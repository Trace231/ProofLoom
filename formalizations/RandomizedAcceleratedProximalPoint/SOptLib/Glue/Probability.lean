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
import Mathlib.Probability.IdentDistribIndep
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import SOptLib.Glue.Algebra
import SOptLib.Glue.Analysis


open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

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

namespace ProbabilityTheory

/-- Disjoint prefix and offset windows of an independent stream are independent vectors.

For a Nat-indexed independent sample stream, the vector of samples over
`0, ..., N - 1` is independent of the vector over `offset, ..., offset + t - 1`
whenever those two finite index sets are disjoint.

Layer: Glue | Gap: Level 1 (finite prefix-offset sample-window independence)
Proof: join the two windows through a Sum-indexed injective map into Nat, pull
  independence back by `iIndepFun.precomp`, and use the existing Sum-tagged
  finite-block independence theorem before composing with coordinate maps.
Source: Mathlib probability independence API for `iIndepFun`, finite products,
  `Fin`, `Finset`, and Sum-indexed random-variable families
Used in: randomized accelerated proximal-point fresh inner-block independence
  from the strict outer sample prefix
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem iIndepFun.indepFun_fin_range_offset_windows_of_disjoint
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (sample : ℕ → Ω → S) (μ : Measure Ω)
    (N offset t : ℕ)
    (h_sample_meas : ∀ n, Measurable (sample n))
    (h_sample_iIndep : iIndepFun sample μ)
    (hdisj :
      Disjoint
        (Finset.range N)
        (Finset.image (fun r : Fin t => offset + r.1) Finset.univ)) :
    IndepFun
      (fun ω : Ω => fun r : Fin N => sample r.1 ω)
      (fun ω : Ω => fun r : Fin t => sample (offset + r.1) ω)
      μ := by
  classical
  let idx : Fin N ⊕ Fin t → ℕ := fun z =>
    match z with
    | Sum.inl r => r.1
    | Sum.inr r => offset + r.1
  have hidx : Function.Injective idx := by
    simpa [idx] using sum_fin_range_offset_injective_of_disjoint N offset t hdisj
  let samplesum : Fin N ⊕ Fin t → Ω → S := fun z ω => sample (idx z) ω
  have hsamplesum_meas : ∀ z, Measurable (samplesum z) := by
    intro z
    exact h_sample_meas (idx z)
  have hsamplesum_iIndep : iIndepFun samplesum μ := by
    simpa [samplesum] using h_sample_iIndep.precomp hidx
  let I : Finset (Fin N) := Finset.univ
  let J : Finset (Fin t) := Finset.univ
  let Xsub : Ω → ({p // p ∈ I} → S) :=
    fun ω p => samplesum (Sum.inl p.1) ω
  let Ysub : Ω → ({q // q ∈ J} → S) :=
    fun ω q => samplesum (Sum.inr q.1) ω
  let leftMap : ({p // p ∈ I} → S) → (Fin N → S) :=
    fun v r => v ⟨r, by simp [I]⟩
  let rightMap : ({q // q ∈ J} → S) → (Fin t → S) :=
    fun v r => v ⟨r, by simp [J]⟩
  have hblocks : IndepFun Xsub Ysub μ := by
    change IndepFun
      (fun ω : Ω => fun p : {p // p ∈ I} => samplesum (Sum.inl p.1) ω)
      (fun ω : Ω => fun q : {q // q ∈ J} => samplesum (Sum.inr q.1) ω)
      μ
    exact iIndepFun.indepFun_finset_sum_inl_inr
      samplesum μ I J hsamplesum_meas hsamplesum_iIndep
  have hleft : Measurable leftMap := by
    refine measurable_pi_lambda _ ?_
    intro r
    exact measurable_pi_apply (⟨r, by simp [I]⟩ : {p // p ∈ I})
  have hright : Measurable rightMap := by
    refine measurable_pi_lambda _ ?_
    intro r
    exact measurable_pi_apply (⟨r, by simp [J]⟩ : {q // q ∈ J})
  have hcomp : IndepFun (leftMap ∘ Xsub) (rightMap ∘ Ysub) μ :=
    hblocks.comp hleft hright
  change IndepFun (leftMap ∘ Xsub) (rightMap ∘ Ysub) μ
  exact hcomp

end ProbabilityTheory

/-- If `Y` has the same pushforward law as a finite-range map `X`, then
`Y` is almost surely supported on the actual range of `X`.

Layer: Glue | Gap: Level 0 (finite-range support transfer under equal laws)
Proof: transfer Mathlib's finite-range support fact for `Measure.map X μ` along
  the equality of pushforward laws, then pull it back through the a.e. measurable
  map `Y`.
Source: Mathlib measure map API and finite measurable-set support facts
Used in: randomized proximal finite block law support recovery
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem ae_mem_range_of_map_eq_of_finite_range
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β]
    {μ : Measure α} {X Y : α → β}
    (hfin : (Set.range X).Finite)
    (hY : AEMeasurable Y μ)
    (hmap : Measure.map Y μ = Measure.map X μ) :
    ∀ᵐ a ∂μ, Y a ∈ Set.range X := by
  have hsupport : ∀ᵐ z ∂Measure.map Y μ, z ∈ Set.range X := by
    rw [hmap]
    exact MeasureTheory.ae_map_mem_range X hfin.measurableSet μ
  exact MeasureTheory.ae_of_ae_map hY hsupport

/-- Equal-length offset windows of an iid sample stream have identical laws.

If every coordinate of a Nat-indexed stream has the same distribution and the
stream is independent, then the `Fin t` sample windows starting at any two
offsets are identically distributed.

Layer: Glue | Gap: Level 1 (iid offset sample-window identical distribution)
Proof: reindex the stream by the two injective offset maps, use
  `iIndepFun.precomp` for the two window processes, and apply Mathlib
  `IdentDistrib.pi` coordinatewise.
Source: Mathlib probability `IdentDistrib.pi`, `iIndepFun.precomp`, and finite
  Pi measurable-space APIs
Used in: randomized accelerated proximal-point fixed inner-run sample-block
  distribution transport
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem sampleWindow_identDistrib_of_identDistrib_iIndep
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    {P : Measure Ω} {sample : ℕ → Ω → S}
    (h_ident : ∀ n m : ℕ, IdentDistrib (sample n) (sample m) P P)
    (h_iIndep : iIndepFun sample P)
    (offset offset' t : ℕ) :
    IdentDistrib (fun ω : Ω => fun r : Fin t => sample (offset + r.1) ω)
      (fun ω : Ω => fun r : Fin t => sample (offset' + r.1) ω) P P := by
  classical
  let X : Fin t → Ω → S := fun r ω => sample (offset + r.1) ω
  let Y : Fin t → Ω → S := fun r ω => sample (offset' + r.1) ω
  have hcoord : ∀ r : Fin t, IdentDistrib (X r) (Y r) P P := by
    intro r
    exact h_ident (offset + r.1) (offset' + r.1)
  have hX_ind : iIndepFun X P := by
    have hinj : Function.Injective (fun r : Fin t => offset + r.1) := by
      intro r q h
      exact Fin.ext (Nat.add_left_cancel h)
    simpa [X] using h_iIndep.precomp hinj
  have hY_ind : iIndepFun Y P := by
    have hinj : Function.Injective (fun r : Fin t => offset' + r.1) := by
      intro r q h
      exact Fin.ext (Nat.add_left_cancel h)
    simpa [Y] using h_iIndep.precomp hinj
  simpa [X, Y] using ProbabilityTheory.IdentDistrib.pi hcoord hX_ind hY_ind

/-- A normed observable determined by a finite-valued sample window is integrable.

For a Nat-indexed stream `ξ` with finite measurable sample alphabet, every
normed observable that is constant on equal `sampleWindow ξ offset t` values is
integrable under any finite measure.

Layer: Glue | Gap: Level 1 (finite sample-window factor integrability)
Proof: prove the `Fin t` sample window is measurable coordinatewise, observe its
  range is finite because the sample alphabet is finite, and apply finite-key
  factor integrability.
Source: Mathlib Pi measurability, finite function spaces, and finite-measure
  integrability APIs
Used in: randomized accelerated proximal point fixed inner-loop finite
  sample-window scalar and normed observable expectation obligations
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal point -/
theorem integrable_of_finiteSampleWindow_factor
    {Ω S E : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [Fintype S]
    [MeasurableSingletonClass S] [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (ξ : ℕ → Ω → S) (offset t : ℕ)
    {Z : Ω → E}
    (hξ_measurable : ∀ n, Measurable (ξ n))
    (hconst :
      ∀ ⦃ω ω' : Ω⦄,
        (fun r : Fin t => ξ (offset + r.1) ω) =
          (fun r : Fin t => ξ (offset + r.1) ω') →
        Z ω = Z ω') :
    Integrable Z μ := by
  classical
  let Y : Ω → Fin t → S := fun ω r => ξ (offset + r.1) ω
  have hwindow_meas : Measurable Y := by
    exact measurable_pi_lambda Y
      (fun r : Fin t => hξ_measurable (offset + r.1))
  have hwindow_fin : (Set.range Y).Finite := Set.toFinite _
  have hZ_meas : Measurable Z := by
    haveI : Fintype {y : (Fin t → S) // y ∈ Set.range Y} := hwindow_fin.fintype
    let Yrange : Ω → {y : (Fin t → S) // y ∈ Set.range Y} :=
      fun ω => ⟨Y ω, ⟨ω, rfl⟩⟩
    let G : {y : (Fin t → S) // y ∈ Set.range Y} → E := fun y =>
      Z (Classical.choose y.2)
    have hYrange : Measurable Yrange := by
      refine measurable_to_countable ?_
      intro ω
      have hset : MeasurableSet (Y ⁻¹' {Y ω}) :=
        hwindow_meas (measurableSet_singleton (Y ω))
      convert hset using 1
      ext ω'
      simp [Yrange]
    have hG : Measurable G := measurable_of_finite G
    have hZG : Z = G ∘ Yrange := by
      funext ω
      dsimp [Function.comp, G, Yrange]
      exact hconst (Classical.choose_spec (show Y ω ∈ Set.range Y from ⟨ω, rfl⟩)).symm
    rw [hZG]
    exact hG.comp hYrange
  have hZ_fin : (Set.range Z).Finite := by
    haveI : Fintype {y : (Fin t → S) // y ∈ Set.range Y} := hwindow_fin.fintype
    let G : {y : (Fin t → S) // y ∈ Set.range Y} → E := fun y =>
      Z (Classical.choose y.2)
    have hsubset : Set.range Z ⊆ Set.range G := by
      rintro z ⟨ω, rfl⟩
      refine ⟨⟨Y ω, ⟨ω, rfl⟩⟩, ?_⟩
      dsimp [G]
      exact hconst (Classical.choose_spec (show Y ω ∈ Set.range Y from ⟨ω, rfl⟩))
    exact (Set.finite_range G).subset hsubset
  let Srange : Finset ℝ := hZ_fin.toFinset.image fun z => ‖z‖
  let C : ℝ := if hS : Srange.Nonempty then Srange.max' hS else 0
  have hC : ∀ ω, ‖Z ω‖ ≤ C := by
    intro ω
    have hmem : ‖Z ω‖ ∈ Srange := by
      simp [Srange, Set.Finite.mem_toFinset]
    have hS : Srange.Nonempty := ⟨‖Z ω‖, hmem⟩
    simpa [C, hS] using Finset.le_max' Srange (‖Z ω‖) hmem
  exact Integrable.of_bound hZ_meas.aestronglyMeasurable C (ae_of_all μ hC)

namespace SOptLib

/-- A finite-uniform independent sample can be replaced by a normalized finite sum
inside a base-space integral.

If a state `Z` is independent of a finite index `idx`, the law of `idx` has
uniform singleton masses, and each fixed-index scalar fiber is integrable, then
the expectation of the selected scalar kernel equals the expectation of the
normalized sum of all fixed-index kernels.

Layer: Glue | Gap: Level 1 (independent finite-uniform average integral bridge)
Proof: identify the joint law of `(Z, idx)` as the product of the marginal laws
  by `IndepFun`, expand the finite-index product integral by singleton real
  masses, and map the state marginal integrals back to the base space.
Source: Mathlib probability independence, product-measure Bochner integration,
  and finite singleton-mass APIs
Used in: randomized accelerated proximal-point fresh component sampling
  replacement by a finite-sum conditional average
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem integral_comp_indep_finite_uniform_eq_integral_inv_card_sum
    {Ω ι W : Type*} [MeasurableSpace Ω] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [Fintype ι] [MeasurableSpace W]
    (P : Measure Ω) [IsFiniteMeasure P] (idx : Ω → ι) (Z : Ω → W)
    (F : W → ι → ℝ)
    (hZ : Measurable Z) (hidx : Measurable idx)
    (hindep : IndepFun Z idx P)
    (hidx_uniform : ∀ i : ι, (Measure.map idx P).real ({i} : Set ι) =
      (Fintype.card ι : ℝ)⁻¹)
    (hF : Measurable (fun q : W × ι => F q.1 q.2))
    (hF_int : ∀ i : ι, Integrable (fun ω : Ω => F (Z ω) i) P) :
    (∫ ω : Ω, F (Z ω) (idx ω) ∂P) =
      ∫ ω : Ω,
        (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ (fun i : ι => F (Z ω) i) ∂P := by
  classical
  let μZ : Measure W := Measure.map Z P
  let ν : Measure ι := Measure.map idx P
  let Fidx : ι → W → ℝ := fun i w => F w i
  have hjoint :
      AEMeasurable (fun ω : Ω => (Z ω, idx ω)) P :=
    (hZ.prodMk hidx).aemeasurable
  have hprod_eq :
      Measure.map (fun ω : Ω => (Z ω, idx ω)) P = μZ.prod ν := by
    dsimp [μZ, ν]
    exact (indepFun_iff_map_prod_eq_prod_map_map
      hZ.aemeasurable hidx.aemeasurable).mp hindep
  have hFidx_int_map : ∀ i : ι, Integrable (Fidx i) μZ := by
    intro i
    have hFi : Measurable (fun w : W => F w i) := by
      simpa [Fidx] using hF.comp (measurable_id.prodMk measurable_const)
    exact (MeasureTheory.integrable_map_measure
      hFi.aestronglyMeasurable hZ.aemeasurable).mpr (hF_int i)
  have hfinite_prod :
      (∫ q : W × ι, F q.1 q.2 ∂(μZ.prod ν)) =
        Finset.sum Finset.univ
          (fun i : ι => (Fintype.card ι : ℝ)⁻¹ * ∫ w : W, F w i ∂μZ) := by
    simpa [Fidx, μZ, ν] using
      (integral_selected_finite_index_prod_eq_sum_weights
        (μ := μZ) (ν := ν)
        (p := fun _i : ι => (Fintype.card ι : ℝ)⁻¹)
        (F := Fidx)
        (by
          intro i
          simpa [ν] using hidx_uniform i)
        hFidx_int_map)
  have hmap_back : ∀ i : ι, (∫ w : W, F w i ∂μZ) =
      ∫ ω : Ω, F (Z ω) i ∂P := by
    intro i
    have hFi : Measurable (fun w : W => F w i) := by
      simpa using hF.comp (measurable_id.prodMk measurable_const)
    dsimp [μZ]
    exact MeasureTheory.integral_map hZ.aemeasurable hFi.aestronglyMeasurable
  have hrhs :
      (∫ ω : Ω,
          (Fintype.card ι : ℝ)⁻¹ *
            Finset.sum Finset.univ (fun i : ι => F (Z ω) i) ∂P) =
        Finset.sum Finset.univ
          (fun i : ι => (Fintype.card ι : ℝ)⁻¹ *
            ∫ ω : Ω, F (Z ω) i ∂P) := by
    rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_finset_sum]
    · rw [Finset.mul_sum]
    · intro i _hi
      exact hF_int i
  calc
    (∫ ω : Ω, F (Z ω) (idx ω) ∂P)
        = ∫ q : W × ι, F q.1 q.2 ∂Measure.map
            (fun ω : Ω => (Z ω, idx ω)) P := by
          exact (MeasureTheory.integral_map hjoint hF.aestronglyMeasurable).symm
    _ = ∫ q : W × ι, F q.1 q.2 ∂(μZ.prod ν) := by
          rw [hprod_eq]
    _ = Finset.sum Finset.univ
          (fun i : ι => (Fintype.card ι : ℝ)⁻¹ * ∫ w : W, F w i ∂μZ) := hfinite_prod
    _ = Finset.sum Finset.univ
          (fun i : ι => (Fintype.card ι : ℝ)⁻¹ *
            ∫ ω : Ω, F (Z ω) i ∂P) := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [hmap_back i]
    _ = ∫ ω : Ω,
          (Fintype.card ι : ℝ)⁻¹ *
            Finset.sum Finset.univ (fun i : ι => F (Z ω) i) ∂P := hrhs.symm

/-- A centered finite-uniform sample term has zero integral after multiplying by a
constant scalar.

If a state `Z` is independent of a finite-uniform index `idx`, then the integral
of `finiteUniformAverage (F (Z ·)) - F (Z ·) (idx ·)` is zero; multiplying by a
deterministic scalar preserves the cancellation.

Layer: Glue | Gap: Level 1 (centered finite-uniform sample cancellation)
Proof: rewrite the sampled integral by the independent finite-uniform average
  bridge, split the integral of the difference using integrability, and cancel
  the two equal integrals after pulling out the constant multiplier.
Source: Mathlib Bochner integral algebra and SOptLib finite-uniform
  independence bridge
Used in: randomized accelerated proximal-point fresh component sampling
  cancellation of centered current-index estimator terms
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem integral_const_mul_finiteUniformAverage_sub_sample_eq_zero
    {Ω ι W : Type*} [MeasurableSpace Ω] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [Fintype ι] [MeasurableSpace W]
    (P : Measure Ω) [IsFiniteMeasure P] (idx : Ω → ι) (Z : Ω → W)
    (F : W → ι → ℝ) (γ : ℝ)
    (hZ : Measurable Z) (hidx : Measurable idx)
    (hindep : IndepFun Z idx P)
    (hidx_uniform : ∀ i : ι, (Measure.map idx P).real ({i} : Set ι) =
      (Fintype.card ι : ℝ)⁻¹)
    (hF : Measurable (fun q : W × ι => F q.1 q.2))
    (hF_int : ∀ i : ι, Integrable (fun ω : Ω => F (Z ω) i) P)
    (hsample_int : Integrable (fun ω : Ω => F (Z ω) (idx ω)) P) :
    (∫ ω : Ω,
        γ * ((Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ (fun i : ι => F (Z ω) i) -
          F (Z ω) (idx ω)) ∂P) = 0 := by
  classical
  have havg_int :
      Integrable (fun ω : Ω =>
        (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ (fun i : ι => F (Z ω) i)) P := by
    exact (MeasureTheory.integrable_finset_sum Finset.univ
      (fun i _hi => hF_int i)).const_mul _
  have hsample_eq_avg :
      (∫ ω : Ω, F (Z ω) (idx ω) ∂P) =
        ∫ ω : Ω, (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ (fun i : ι => F (Z ω) i) ∂P := by
    exact
      (integral_comp_indep_finite_uniform_eq_integral_inv_card_sum
        (P := P) (idx := idx) (Z := Z) (F := F)
        hZ hidx hindep hidx_uniform hF hF_int)
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_sub havg_int hsample_int]
  rw [hsample_eq_avg]
  ring

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

open MeasureTheory
open scoped BigOperators

/-- Integrate a finite-window bound with a realized-minus-averaged residual.

If a pointwise finite-sum inequality is bounded by a reference finite sum plus
an actual residual minus an averaged residual, then the same inequality holds
after integration, with the residual written as the difference of finite sums of
integrals.

Layer: Glue | Gap: Level 1 (finite-window residual integral lift)
Proof: combine the reference and residual terms, apply `integral_mono_ae` to
  the a.e. pointwise bound, then commute the Bochner integral through the finite
  sums and split the integrals by linearity.
Source: Mathlib Bochner integral monotonicity, finite-sum linearity, and
  ordered additive-group algebra
Used in: randomized accelerated proximal-point expected finite-window descent
  after replacing a current-sample residual by its averaged residual
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point -/
theorem integral_finset_sum_residual_lift_le
    {Ω I E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
    [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [ClosedIciTopology E]
    (s : Finset I)
    (left rhs actual avg : I → Ω → E)
    (hleft_int : ∀ i ∈ s, Integrable (left i) μ)
    (hrhs_int : ∀ i ∈ s, Integrable (rhs i) μ)
    (hactual_int : ∀ i ∈ s, Integrable (actual i) μ)
    (havg_int : ∀ i ∈ s, Integrable (avg i) μ)
    (hpoint :
      ∀ᵐ ω ∂μ,
        Finset.sum s (fun i => left i ω) ≤
          Finset.sum s (fun i => rhs i ω) +
            (Finset.sum s (fun i => actual i ω) -
              Finset.sum s (fun i => avg i ω))) :
    (∫ ω, Finset.sum s (fun i => left i ω) ∂μ) ≤
      (∫ ω, Finset.sum s (fun i => rhs i ω) ∂μ) +
        (Finset.sum s (fun i => ∫ ω, actual i ω ∂μ) -
          Finset.sum s (fun i => ∫ ω, avg i ω ∂μ)) := by
  classical
  let combined : I → Ω → E := fun i ω => rhs i ω + (actual i ω - avg i ω)
  have hleft_sum_int :
      Integrable (fun ω => Finset.sum s (fun i => left i ω)) μ := by
    exact MeasureTheory.integrable_finset_sum s hleft_int
  have hcombined_int : ∀ i ∈ s, Integrable (combined i) μ := by
    intro i hi
    exact (hrhs_int i hi).add ((hactual_int i hi).sub (havg_int i hi))
  have hcombined_sum_int :
      Integrable (fun ω => Finset.sum s (fun i => combined i ω)) μ := by
    exact MeasureTheory.integrable_finset_sum s hcombined_int
  have hpoint_combined :
      ∀ᵐ ω ∂μ,
        Finset.sum s (fun i => left i ω) ≤
          Finset.sum s (fun i => combined i ω) := by
    filter_upwards [hpoint] with ω hω
    simpa [combined, Finset.sum_add_distrib, Finset.sum_sub_distrib] using hω
  have hmono :
      (∫ ω, Finset.sum s (fun i => left i ω) ∂μ) ≤
        ∫ ω, Finset.sum s (fun i => combined i ω) ∂μ :=
    MeasureTheory.integral_mono_ae hleft_sum_int hcombined_sum_int hpoint_combined
  calc
    (∫ ω, Finset.sum s (fun i => left i ω) ∂μ)
        ≤ ∫ ω, Finset.sum s (fun i => combined i ω) ∂μ := hmono
    _ = Finset.sum s (fun i => ∫ ω, combined i ω ∂μ) := by
          rw [MeasureTheory.integral_finset_sum]
          exact hcombined_int
    _ = Finset.sum s
          (fun i =>
            (∫ ω, rhs i ω ∂μ) +
              ((∫ ω, actual i ω ∂μ) - (∫ ω, avg i ω ∂μ))) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          dsimp [combined]
          rw [MeasureTheory.integral_add (f := rhs i)
            (g := fun ω => actual i ω - avg i ω)
            (hrhs_int i hi) ((hactual_int i hi).sub (havg_int i hi))]
          rw [MeasureTheory.integral_sub (f := actual i) (g := avg i)
            (hactual_int i hi) (havg_int i hi)]
    _ =
        Finset.sum s (fun i => ∫ ω, rhs i ω ∂μ) +
          (Finset.sum s (fun i => ∫ ω, actual i ω ∂μ) -
            Finset.sum s (fun i => ∫ ω, avg i ω ∂μ)) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ =
        (∫ ω, Finset.sum s (fun i => rhs i ω) ∂μ) +
          (Finset.sum s (fun i => ∫ ω, actual i ω ∂μ) -
            Finset.sum s (fun i => ∫ ω, avg i ω ∂μ)) := by
          rw [MeasureTheory.integral_finset_sum]
          exact hrhs_int

open MeasureTheory
open scoped BigOperators

/-- Integrate a finite-window residual bound while discarding a zero-integral correction.

If a pointwise finite-sum inequality has the usual realized-minus-averaged
residual plus an extra correction whose finite-window integral is zero, then the
integrated bound is the same as if the correction had not appeared.

Layer: Glue | Gap: Level 1 (zero-correction finite-window residual lift)
Proof: absorb the correction into the reference summand, apply the finite-window
  residual integral lift, and use Bochner integral linearity to cancel the
  summed correction by its zero integral.
Source: Mathlib Bochner integral finite-sum linearity, integral addition, and
  ordered integral monotonicity APIs
Used in: randomized accelerated proximal-point expected finite-window descent
  after cancelling a centered current-sample correction
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point -/
theorem integral_finset_sum_residual_lift_le_of_zero_correction
    {Ω I E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
    [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [ClosedIciTopology E]
    (s : Finset I)
    (left rhs actual avg corr : I → Ω → E)
    (hleft_int : ∀ i ∈ s, Integrable (left i) μ)
    (hrhs_int : ∀ i ∈ s, Integrable (rhs i) μ)
    (hactual_int : ∀ i ∈ s, Integrable (actual i) μ)
    (havg_int : ∀ i ∈ s, Integrable (avg i) μ)
    (hcorr_int : ∀ i ∈ s, Integrable (corr i) μ)
    (hcorr_zero :
      (∫ ω, Finset.sum s (fun i => corr i ω) ∂μ) = 0)
    (hpoint :
      ∀ᵐ ω ∂μ,
        Finset.sum s (fun i => left i ω) ≤
          Finset.sum s (fun i => rhs i ω) +
            (Finset.sum s (fun i => actual i ω) -
              Finset.sum s (fun i => avg i ω)) +
            Finset.sum s (fun i => corr i ω)) :
    (∫ ω, Finset.sum s (fun i => left i ω) ∂μ) ≤
      (∫ ω, Finset.sum s (fun i => rhs i ω) ∂μ) +
        (Finset.sum s (fun i => ∫ ω, actual i ω ∂μ) -
          Finset.sum s (fun i => ∫ ω, avg i ω ∂μ)) := by
  classical
  let rhsCorr : I → Ω → E := fun i ω => rhs i ω + corr i ω
  have hrhsCorr_int : ∀ i ∈ s, Integrable (rhsCorr i) μ := by
    intro i hi
    exact (hrhs_int i hi).add (hcorr_int i hi)
  have hpoint' :
      ∀ᵐ ω ∂μ,
        Finset.sum s (fun i => left i ω) ≤
          Finset.sum s (fun i => rhsCorr i ω) +
            (Finset.sum s (fun i => actual i ω) -
              Finset.sum s (fun i => avg i ω)) := by
    filter_upwards [hpoint] with ω hω
    simpa [rhsCorr, Finset.sum_add_distrib, sub_eq_add_neg, add_assoc, add_comm,
      add_left_comm] using hω
  have hbase :=
    integral_finset_sum_residual_lift_le
      (s := s) (left := left) (rhs := rhsCorr) (actual := actual) (avg := avg)
      hleft_int hrhsCorr_int hactual_int havg_int hpoint'
  have hrhsCorr_integral :
      (∫ ω, Finset.sum s (fun i => rhsCorr i ω) ∂μ) =
        ∫ ω, Finset.sum s (fun i => rhs i ω) ∂μ := by
    have hsum :
        (fun ω => Finset.sum s (fun i => rhsCorr i ω)) =
          fun ω => Finset.sum s (fun i => rhs i ω) +
            Finset.sum s (fun i => corr i ω) := by
      funext ω
      simp [rhsCorr, Finset.sum_add_distrib]
    rw [hsum]
    rw [MeasureTheory.integral_add
      (MeasureTheory.integrable_finset_sum s hrhs_int)
      (MeasureTheory.integrable_finset_sum s hcorr_int)]
    rw [hcorr_zero, add_zero]
  simpa [hrhsCorr_integral] using hbase

open MeasureTheory
open scoped BigOperators

/-- A per-component balance gives the a.e. finite-sum residual inequality.

If every component in a finite set satisfies `left + avg = rhs + actual` at each
sample point, then the finite sum of `left` is a.e. bounded by the finite sum of
`rhs` plus the realized-minus-averaged residual.

Layer: Glue | Gap: Level 0 (finite-sum residual pointwise balance)
Proof: sum the component balances over the finite index set, split both sums
  using `Finset.sum_add_distrib`, and finish with additive-group algebra plus
  `le_of_eq`.
Source: Mathlib finite-sum algebra and ordered additive-group arithmetic
Used in: randomized accelerated proximal-point fixed-time descent before
  integrating the current-sample residual
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point -/
theorem ae_finset_sum_residual_le_of_pointwise_balance
    {Ω I E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [AddCommGroup E] [Preorder E]
    (s : Finset I)
    (left rhs actual avg : I → Ω → E)
    (hper :
      ∀ (ω : Ω) (i : I), i ∈ s →
        left i ω + avg i ω = rhs i ω + actual i ω) :
    ∀ᵐ ω ∂μ,
      Finset.sum s (fun i => left i ω) ≤
        Finset.sum s (fun i => rhs i ω) +
          (Finset.sum s (fun i => actual i ω) -
            Finset.sum s (fun i => avg i ω)) := by
  refine Filter.Eventually.of_forall ?_
  intro ω
  have hsum :
      Finset.sum s (fun i => left i ω + avg i ω) =
        Finset.sum s (fun i => rhs i ω + actual i ω) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact hper ω i hi
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  refine le_of_eq ?_
  calc
    Finset.sum s (fun i => left i ω) =
        Finset.sum s (fun i => left i ω) +
            Finset.sum s (fun i => avg i ω) -
          Finset.sum s (fun i => avg i ω) := by
      abel
    _ =
        (Finset.sum s (fun i => rhs i ω) +
            Finset.sum s (fun i => actual i ω)) -
          Finset.sum s (fun i => avg i ω) := by
      rw [hsum]
    _ =
        Finset.sum s (fun i => rhs i ω) +
          (Finset.sum s (fun i => actual i ω) -
            Finset.sum s (fun i => avg i ω)) := by
      abel

/-- An a.e.-strongly measurable function with finite range is integrable on a finite measure.

The finite range gives a global bound on `‖Z ω‖`; bounded a.e.-strongly
measurable observables are integrable on finite measure spaces.

Layer: Glue | Gap: Level 0 (finite-range observable integrability)
Proof: take the maximum of the finite set of norms in the range, then apply
  `MeasureTheory.Integrable.of_bound`.
Source: Mathlib finite-set maxima and finite-measure integrability APIs
Used in: randomized accelerated proximal point finite-prefix scalar observables
  for expectation and selected-output bounds
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal point -/
theorem integrable_of_finite_range
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {Z : Ω → E} (hZ : MeasureTheory.AEStronglyMeasurable Z μ)
    (hfin : (Set.range Z).Finite) :
    MeasureTheory.Integrable Z μ := by
  classical
  let S : Finset ℝ := hfin.toFinset.image fun z => ‖z‖
  let C : ℝ := if hS : S.Nonempty then S.max' hS else 0
  have hC : ∀ ω, ‖Z ω‖ ≤ C := by
    intro ω
    have hmem : ‖Z ω‖ ∈ S := by
      simp [S, Set.Finite.mem_toFinset]
    have hS : S.Nonempty := ⟨‖Z ω‖, hmem⟩
    simpa [C, hS] using Finset.le_max' S (‖Z ω‖) hmem
  exact MeasureTheory.Integrable.of_bound hZ C (MeasureTheory.ae_of_all μ hC)

/-- A normed observable determined by a finite-range measurable key is integrable.

If `Y` is a finite-range measurable key and `Z` is constant on the fibers of
`Y`, then `Z` has finite range and is measurable, hence a.e.-strongly
measurable and integrable under any finite measure.

Layer: Glue | Gap: Level 1 (finite-key normed-observable integrability)
Proof: use the finite-fiber measurability lemma for `Z`, show the range of `Z`
  is contained in the image of the finite range of `Y`, and apply finite-range
  integrability.
Source: Mathlib measurable singleton, finite-range, and finite-measure
  integrability APIs
Used in: randomized accelerated proximal point finite sample-window scalar
  expectation obligations
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal point -/
theorem integrable_of_finiteRange_factor
    {Ω α E : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSingletonClass α] [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {Y : Ω → α} {Z : Ω → E}
    (hY : Measurable Y) (hfin : (Set.range Y).Finite)
    (hconst : ∀ ⦃ω ω' : Ω⦄, Y ω = Y ω' → Z ω = Z ω') :
    MeasureTheory.Integrable Z μ := by
  classical
  have hZ_meas : Measurable Z := by
    haveI : Fintype {y : α // y ∈ Set.range Y} := hfin.fintype
    let Yrange : Ω → {y : α // y ∈ Set.range Y} := fun ω => ⟨Y ω, ⟨ω, rfl⟩⟩
    let G : {y : α // y ∈ Set.range Y} → E := fun y =>
      Z (Classical.choose y.2)
    have hYrange : Measurable Yrange := by
      refine measurable_to_countable ?_
      intro ω
      have hset : MeasurableSet (Y ⁻¹' {Y ω}) :=
        hY (measurableSet_singleton (Y ω))
      convert hset using 1
      ext ω'
      simp [Yrange]
    have hG : Measurable G := measurable_of_finite G
    have hZG : Z = G ∘ Yrange := by
      funext ω
      dsimp [Function.comp, G, Yrange]
      exact hconst (Classical.choose_spec (show Y ω ∈ Set.range Y from ⟨ω, rfl⟩)).symm
    rw [hZG]
    exact hG.comp hYrange
  have hZ_fin : (Set.range Z).Finite := by
    haveI : Fintype {y : α // y ∈ Set.range Y} := hfin.fintype
    let G : {y : α // y ∈ Set.range Y} → E := fun y =>
      Z (Classical.choose y.2)
    have hsubset : Set.range Z ⊆ Set.range G := by
      rintro z ⟨ω, rfl⟩
      refine ⟨⟨Y ω, ⟨ω, rfl⟩⟩, ?_⟩
      dsimp [G]
      exact hconst (Classical.choose_spec (show Y ω ∈ Set.range Y from ⟨ω, rfl⟩))
    exact (Set.finite_range G).subset hsubset
  exact integrable_of_finite_range hZ_meas.aestronglyMeasurable hZ_fin

open MeasureTheory
open scoped BigOperators

/-- The expected normalized component dispersion is bounded by two centered
component errors plus two aggregate centered error.

For a finite family of states `xm i ω`, an aggregate state `x ω`, and a
deterministic center `z`, the normalized integral of
`‖xm i ω - x ω‖ ^ 2` is controlled by inserting `z` into every difference.

Layer: Glue | Gap: Level 1 (integrated normalized finite-dispersion centering)
Proof: apply the squared norm triangle bound pointwise, average over the finite
  index set, use the cardinality normalization to simplify the aggregate-center
  term, then integrate by monotonicity and commute the finite sum through the
  integral.
Source: Mathlib finite sums, Bochner integral linearity, and normed-group
  triangle inequality APIs
Used in: randomized accelerated proximal-point component-memory dispersion
  control and variance-reduced finite-sum memory-table estimates
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem integral_inv_mul_sum_sq_sub_le_two_centered
    {Ω ι E : Type*} [MeasurableSpace Ω] [Fintype ι] [SeminormedAddCommGroup E]
    (μ : Measure Ω) (m : ℝ) (hm_pos : 0 < m)
    (hm_card : m = (Fintype.card ι : ℝ))
    (xm : ι → Ω → E) (x : Ω → E) (z : E)
    (hlhs_int :
      Integrable
        (fun ω =>
          m⁻¹ * Finset.sum Finset.univ (fun i => ‖xm i ω - x ω‖ ^ 2)) μ)
    (hxm_center_int : ∀ i, Integrable (fun ω => ‖xm i ω - z‖ ^ 2) μ)
    (hx_center_int : Integrable (fun ω => ‖z - x ω‖ ^ 2) μ) :
    (∫ ω,
      m⁻¹ * Finset.sum Finset.univ (fun i => ‖xm i ω - x ω‖ ^ 2) ∂μ) ≤
      2 *
          (m⁻¹ *
            Finset.sum Finset.univ (fun i => ∫ ω, ‖xm i ω - z‖ ^ 2 ∂μ)) +
        2 * ∫ ω, ‖z - x ω‖ ^ 2 ∂μ := by
  classical
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  have hcenter_avg_int :
      Integrable
        (fun ω =>
          m⁻¹ * Finset.sum Finset.univ (fun i => ‖xm i ω - z‖ ^ 2)) μ := by
    exact (MeasureTheory.integrable_finset_sum Finset.univ
      (fun i _hi => hxm_center_int i)).const_mul m⁻¹
  have hrhs_int :
      Integrable
        (fun ω =>
          2 *
              (m⁻¹ * Finset.sum Finset.univ (fun i => ‖xm i ω - z‖ ^ 2)) +
            2 * ‖z - x ω‖ ^ 2) μ :=
    (hcenter_avg_int.const_mul 2).add (hx_center_int.const_mul 2)
  have hpointwise :
      ∀ ω,
        m⁻¹ * Finset.sum Finset.univ (fun i => ‖xm i ω - x ω‖ ^ 2) ≤
          2 *
              (m⁻¹ * Finset.sum Finset.univ (fun i => ‖xm i ω - z‖ ^ 2)) +
            2 * ‖z - x ω‖ ^ 2 := by
    intro ω
    have hsum_le :
        Finset.sum Finset.univ (fun i => ‖xm i ω - x ω‖ ^ 2) ≤
          Finset.sum Finset.univ
            (fun i => 2 * ‖xm i ω - z‖ ^ 2 + 2 * ‖z - x ω‖ ^ 2) := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      have htri : ‖xm i ω - x ω‖ ≤ ‖xm i ω - z‖ + ‖z - x ω‖ := by
        calc
          ‖xm i ω - x ω‖ = ‖(xm i ω - z) + (z - x ω)‖ := by
            congr 1
            abel
          _ ≤ ‖xm i ω - z‖ + ‖z - x ω‖ := norm_add_le _ _
      have hsq_le :
          ‖xm i ω - x ω‖ ^ 2 ≤ (‖xm i ω - z‖ + ‖z - x ω‖) ^ 2 := by
        exact sq_le_sq' (by nlinarith [norm_nonneg (xm i ω - x ω)]) htri
      have htwo :
          (‖xm i ω - z‖ + ‖z - x ω‖) ^ 2 ≤
            2 * ‖xm i ω - z‖ ^ 2 + 2 * ‖z - x ω‖ ^ 2 := by
        nlinarith [sq_nonneg (‖xm i ω - z‖ - ‖z - x ω‖)]
      exact hsq_le.trans htwo
    have hscaled :=
      mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr (le_of_lt hm_pos))
    calc
      m⁻¹ * Finset.sum Finset.univ (fun i => ‖xm i ω - x ω‖ ^ 2)
          ≤
        m⁻¹ *
          Finset.sum Finset.univ
            (fun i => 2 * ‖xm i ω - z‖ ^ 2 + 2 * ‖z - x ω‖ ^ 2) := hscaled
      _ =
          2 *
              (m⁻¹ * Finset.sum Finset.univ (fun i => ‖xm i ω - z‖ ^ 2)) +
            2 * ‖z - x ω‖ ^ 2 := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [hm_card]
        simp only [Finset.card_univ]
        have hcard_ne : ((Fintype.card ι : ℕ) : ℝ) ≠ 0 := by
          rw [← hm_card]
          exact hm_ne
        field_simp [hcard_ne]
        rw [mul_add, Finset.mul_sum]
        ring
  have h_integral_le :
      (∫ ω,
        m⁻¹ * Finset.sum Finset.univ (fun i => ‖xm i ω - x ω‖ ^ 2) ∂μ) ≤
        ∫ ω,
          (2 *
              (m⁻¹ * Finset.sum Finset.univ (fun i => ‖xm i ω - z‖ ^ 2)) +
            2 * ‖z - x ω‖ ^ 2) ∂μ := by
    exact MeasureTheory.integral_mono hlhs_int hrhs_int hpointwise
  have hcenter_integral :
      (∫ ω,
        m⁻¹ * Finset.sum Finset.univ (fun i => ‖xm i ω - z‖ ^ 2) ∂μ) =
        m⁻¹ *
          Finset.sum Finset.univ (fun i => ∫ ω, ‖xm i ω - z‖ ^ 2 ∂μ) := by
    rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_finset_sum]
    intro i _hi
    exact hxm_center_int i
  have hrhs_integral :
      (∫ ω,
        (2 *
            (m⁻¹ * Finset.sum Finset.univ (fun i => ‖xm i ω - z‖ ^ 2)) +
          2 * ‖z - x ω‖ ^ 2) ∂μ) =
        2 *
            (m⁻¹ *
              Finset.sum Finset.univ (fun i => ∫ ω, ‖xm i ω - z‖ ^ 2 ∂μ)) +
          2 * ∫ ω, ‖z - x ω‖ ^ 2 ∂μ := by
    rw [MeasureTheory.integral_add (hcenter_avg_int.const_mul 2)
      (hx_center_int.const_mul 2)]
    rw [show
        (∫ ω,
          2 * (m⁻¹ * Finset.sum Finset.univ (fun i => ‖xm i ω - z‖ ^ 2)) ∂μ) =
          2 * (∫ ω,
            m⁻¹ * Finset.sum Finset.univ (fun i => ‖xm i ω - z‖ ^ 2) ∂μ) by
        rw [MeasureTheory.integral_const_mul]]
    rw [show
        (∫ ω, 2 * ‖z - x ω‖ ^ 2 ∂μ) =
          2 * (∫ ω, ‖z - x ω‖ ^ 2 ∂μ) by
        rw [MeasureTheory.integral_const_mul]]
    rw [hcenter_integral]
  exact h_integral_le.trans_eq hrhs_integral

open MeasureTheory
open scoped BigOperators

/-- Integrate an a.e. inequality between two scaled finite sums.

If every left and right summand in a finite index set is integrable and an
a.e. bound `c • sum A <= gap + c • sum C` holds, then the same bound holds after
replacing each summand by its expectation under a probability measure.

Layer: Glue | Gap: Level 1 (finite-sum pointwise expectation lift)
Proof: apply Bochner integral monotonicity to the a.e. inequality, commute the
  integral through both finite sums, and use probability normalization to
  integrate the deterministic gap.
Source: Mathlib Bochner integral monotonicity, finite-sum linearity, and
  probability-measure constant integration APIs
Used in: randomized accelerated proximal-point finite-window displacement
  telescope before scalar absorption
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point -/
theorem integral_finset_sum_le_of_pointwise_finset_sum_le
    {Omega I E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
    [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [ClosedIciTopology E]
    [CompleteSpace E]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (s : Finset I) (A C : I -> Omega -> E) (c : ℝ) (gap : E)
    (hA_int : forall i, i ∈ s -> Integrable (A i) mu)
    (hC_int : forall i, i ∈ s -> Integrable (C i) mu)
    (hpoint :
      ∀ᵐ omega ∂mu,
        c • Finset.sum s (fun i => A i omega) <=
          gap + c • Finset.sum s (fun i => C i omega)) :
    c • Finset.sum s (fun i => ∫ omega, A i omega ∂mu) <=
      gap + c • Finset.sum s (fun i => ∫ omega, C i omega ∂mu) := by
  classical
  have hA_sum_int :
      Integrable (fun omega : Omega => Finset.sum s (fun i => A i omega)) mu := by
    exact MeasureTheory.integrable_finset_sum s hA_int
  have hC_sum_int :
      Integrable (fun omega : Omega => Finset.sum s (fun i => C i omega)) mu := by
    exact MeasureTheory.integrable_finset_sum s hC_int
  have hmono :
      (∫ omega : Omega,
          c • Finset.sum s (fun i => A i omega) ∂mu) <=
        ∫ omega : Omega,
          gap + c • Finset.sum s (fun i => C i omega) ∂mu := by
    exact MeasureTheory.integral_mono_ae
      (hA_sum_int.smul c)
      ((integrable_const gap).add (hC_sum_int.smul c))
      hpoint
  have hleft_eval :
      (∫ omega : Omega,
          c • Finset.sum s (fun i => A i omega) ∂mu) =
        c • Finset.sum s (fun i => ∫ omega, A i omega ∂mu) := by
    rw [MeasureTheory.integral_smul]
    rw [MeasureTheory.integral_finset_sum]
    exact hA_int
  have hright_eval :
      (∫ omega : Omega,
          gap + c • Finset.sum s (fun i => C i omega) ∂mu) =
        gap + c • Finset.sum s (fun i => ∫ omega, C i omega ∂mu) := by
    calc
      (∫ omega : Omega,
          gap + c • Finset.sum s (fun i => C i omega) ∂mu) =
          (∫ omega : Omega, (fun _ : Omega => gap) omega ∂mu) +
            ∫ omega : Omega,
              (fun omega : Omega =>
                c • Finset.sum s (fun i => C i omega)) omega ∂mu := by
        exact MeasureTheory.integral_add (integrable_const gap)
          (hC_sum_int.smul c)
      _ = gap + c • Finset.sum s (fun i => ∫ omega, C i omega ∂mu) := by
        rw [MeasureTheory.integral_const]
        rw [MeasureTheory.integral_smul]
        rw [MeasureTheory.integral_finset_sum]
        · simp
        · exact hC_int
  rw [hleft_eval, hright_eval] at hmono
  exact hmono

open MeasureTheory ProbabilityTheory

/-- A nested integral over a prefix and fresh block equals the generated joint integral.

If the generated pair `(prefix, blockOff)` has joint law equal to the product of
the prefix law and a reference fresh-block law, then integrating a product-law
integrable kernel first over the fresh block and then over the prefix agrees
with integrating that kernel on the generated pair. The coordinate maps are only
required to be a.e. measurable. -/
theorem integral_prefix_fresh_block_eq_generated_of_joint_law
    {Ω A B E : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Measure Ω} [SFinite P]
    {pref : Ω → A} {block0 blockOff : Ω → B}
    (hpref : AEMeasurable pref P)
    (hblock0 : AEMeasurable block0 P)
    (hblockOff : AEMeasurable blockOff P)
    (hjoint :
      Measure.map (fun ω => (pref ω, blockOff ω)) P =
        (Measure.map pref P).prod (Measure.map block0 P))
    (Φ : A → B → E)
    (hΦ_int :
      Integrable (Function.uncurry Φ) ((Measure.map pref P).prod (Measure.map block0 P))) :
    (∫ ω₀ : Ω, ∫ ω₁ : Ω, Φ (pref ω₀) (block0 ω₁) ∂P ∂P) =
      ∫ ω : Ω, Φ (pref ω) (blockOff ω) ∂P := by
  classical
  let μpref : Measure A := Measure.map pref P
  let μblock : Measure B := Measure.map block0 P
  let pairOff : Ω → A × B := fun ω => (pref ω, blockOff ω)
  let pairFresh : Ω × Ω → A × B := fun z => (pref z.1, block0 z.2)
  let F : A × B → E := Function.uncurry Φ
  have hpairOff_aem : AEMeasurable pairOff P := hpref.prodMk hblockOff
  have hpairFresh_aem : AEMeasurable pairFresh (P.prod P) :=
    hpref.comp_fst.prodMk hblock0.comp_snd
  have hpairFresh_map :
      Measure.map pairFresh (P.prod P) = μpref.prod μblock := by
    let pref' : Ω → A := hpref.mk pref
    let block0' : Ω → B := hblock0.mk block0
    let pairFresh' : Ω × Ω → A × B := fun z => (pref' z.1, block0' z.2)
    have hpair_ae : pairFresh =ᵐ[P.prod P] pairFresh' := by
      exact
        ((MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := P) (ν := P)).ae_eq_comp
            hpref.ae_eq_mk).prodMk
          ((MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := P) (ν := P)).ae_eq_comp
            hblock0.ae_eq_mk)
    have hpref_map : Measure.map pref' P = μpref := by
      simpa [pref', μpref] using (Measure.map_congr hpref.ae_eq_mk).symm
    have hblock0_map : Measure.map block0' P = μblock := by
      simpa [block0', μblock] using (Measure.map_congr hblock0.ae_eq_mk).symm
    calc
      Measure.map pairFresh (P.prod P)
          = Measure.map pairFresh' (P.prod P) := Measure.map_congr hpair_ae
      _ = (Measure.map pref' P).prod (Measure.map block0' P) := by
            simpa [pairFresh'] using
              (Measure.map_prod_map P P hpref.measurable_mk hblock0.measurable_mk).symm
      _ = μpref.prod μblock := by rw [hpref_map, hblock0_map]
  have hF_pairOff_aesm : AEStronglyMeasurable F (Measure.map pairOff P) := by
    simpa [F, pairOff, μpref, μblock] using (hjoint ▸ hΦ_int.aestronglyMeasurable)
  have hF_pairFresh_aesm : AEStronglyMeasurable F (Measure.map pairFresh (P.prod P)) := by
    simpa [F, μpref, μblock] using (hpairFresh_map ▸ hΦ_int.aestronglyMeasurable)
  have hF_pairFresh_int : Integrable F (Measure.map pairFresh (P.prod P)) := by
    simpa [F, μpref, μblock] using (hpairFresh_map ▸ hΦ_int)
  have hcomp_int : Integrable (F ∘ pairFresh) (P.prod P) :=
    hF_pairFresh_int.comp_aemeasurable hpairFresh_aem
  have hright :
      (∫ ω : Ω, Φ (pref ω) (blockOff ω) ∂P) =
        ∫ q : A × B, F q ∂(μpref.prod μblock) := by
    calc
      (∫ ω : Ω, Φ (pref ω) (blockOff ω) ∂P)
          = ∫ q : A × B, F q ∂Measure.map pairOff P := by
              exact (MeasureTheory.integral_map hpairOff_aem hF_pairOff_aesm).symm
      _ = ∫ q : A × B, F q ∂(μpref.prod μblock) := by
              have hmap : Measure.map pairOff P = μpref.prod μblock := by
                simpa [pairOff, μpref, μblock] using hjoint
              rw [hmap]
  have hleft :
      (∫ ω₀ : Ω, ∫ ω₁ : Ω, Φ (pref ω₀) (block0 ω₁) ∂P ∂P) =
        ∫ q : A × B, F q ∂(μpref.prod μblock) := by
    calc
      (∫ ω₀ : Ω, ∫ ω₁ : Ω, Φ (pref ω₀) (block0 ω₁) ∂P ∂P)
          = ∫ z : Ω × Ω, F (pairFresh z) ∂(P.prod P) := by
              simpa [F, pairFresh, Function.comp_def] using
                (MeasureTheory.integral_integral (μ := P) (ν := P) (f := fun ω₀ ω₁ =>
                  Φ (pref ω₀) (block0 ω₁)) hcomp_int)
      _ = ∫ q : A × B, F q ∂Measure.map pairFresh (P.prod P) := by
              exact (MeasureTheory.integral_map hpairFresh_aem hF_pairFresh_aesm).symm
      _ = ∫ q : A × B, F q ∂(μpref.prod μblock) := by rw [hpairFresh_map]
  exact hleft.trans hright.symm

open MeasureTheory ProbabilityTheory

/-- The joint law of an independent prefix and offset block is the product of the
prefix law and any equal reference block law.

If `pref` is independent of `blockOff`, and `blockOff` has the same
pushforward law as `block0`, then the pair `(pref, blockOff)` pushes the
source measure forward to the product of the prefix law and the reference block
law.

Layer: Glue | Gap: Level 1 (independent product law with replacement marginal)
Proof: apply Mathlib's `IndepFun` product-law characterization and rewrite the
  second marginal by the supplied equal-law hypothesis.
Source: Mathlib probability independence and product-measure pushforward APIs
Used in: randomized accelerated proximal-point finite prefix/fresh block law
  transport for terminal inner sample windows
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem map_pair_eq_prod_map_of_indepFun_of_map_eq
    {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    {P : Measure Ω} [IsFiniteMeasure P]
    {pref : Ω → A} {blockOff block0 : Ω → B}
    (hprefix : AEMeasurable pref P)
    (hblockOff : AEMeasurable blockOff P)
    (hindep : IndepFun pref blockOff P)
    (hblock : Measure.map blockOff P = Measure.map block0 P) :
    Measure.map (fun ω => (pref ω, blockOff ω)) P =
      (Measure.map pref P).prod (Measure.map block0 P) := by
  rw [(indepFun_iff_map_prod_eq_prod_map_map hprefix hblockOff).mp hindep, hblock]

open MeasureTheory ProbabilityTheory

/-- Equal singleton fiber masses imply identical distributions on a countable target.

For random variables into a countable measurable space with measurable singletons,
it is enough to compare the source-measure mass of every singleton fiber.

Layer: Glue | Gap: Level 0 (singleton-fiber criterion for identical distribution)
Proof: build an `IdentDistrib` proof by `IdentDistrib.mk`; equality of pushforward
  measures follows from `Measure.ext_of_singleton` after rewriting singleton map
  masses by `Measure.map_apply_of_aemeasurable`.
Source: Mathlib probability `IdentDistrib` and countable singleton measure
  extensionality APIs
Used in: finite-uniform stochastic sample-coordinate law matching
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem identDistrib_of_countable_singleton_preimage_eq
    {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [Countable ι]
    {P : Measure Ω} {Q : Measure Ω'} {X : Ω → ι} {Y : Ω' → ι}
    (hX : AEMeasurable X P) (hY : AEMeasurable Y Q)
    (h_singleton : ∀ i : ι, P (X ⁻¹' ({i} : Set ι)) = Q (Y ⁻¹' ({i} : Set ι))) :
    IdentDistrib X Y P Q := by
  refine ⟨hX, hY, ?_⟩
  apply Measure.ext_of_singleton
  intro i
  rw [Measure.map_apply_of_aemeasurable hX (measurableSet_singleton i),
    Measure.map_apply_of_aemeasurable hY (measurableSet_singleton i),
    h_singleton i]


open MeasureTheory
open scoped BigOperators

/-- Normalize a guarded finite sum of scalar-weighted integrals to an attached sum.

Each summand carries an `if h : i in s` guard only to expose the membership
proof needed by the integrand. Summing over the same finite set makes the guard
true, and `integral_smul` pulls the deterministic scalar weight outside the
Bochner integral.

Layer: Glue | Gap: Level 0 (guarded finite-integral attached-sum normalization)
Proof: rewrite the finite sum as a sum over `attach`, discharge each guard by
  the attached membership proof, and apply `MeasureTheory.integral_smul`.
Source: Mathlib finite-sum attachment and Bochner integral scalar-multiplication APIs
Used in: randomized accelerated proximal-point residual-window normalization
  before applying time-local conditional-expectation bounds
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem sum_integral_guarded_smul_eq_sum_attach
    {Ω ι E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ι) (γ : ι → ℝ)
    (F : (i : ι) → i ∈ s → Ω → E) :
    Finset.sum s
        (fun i =>
          ∫ ω, (if hi : i ∈ s then γ i • F i hi ω else 0) ∂μ) =
      Finset.sum s.attach
        (fun i => γ i.1 • ∫ ω, F i.1 i.2 ω ∂μ) := by
  rw [← Finset.sum_attach (s := s)]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  simp only [dif_pos i.2]
  rw [MeasureTheory.integral_smul]

/-- The one-based interval specialization used by the randomized accelerated
proximal-point development. -/
theorem sum_Icc_integral_guarded_const_mul_eq_sum_attach
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (N : ℕ) (γ : ℕ → ℝ)
    (F : (t : ℕ) → t ∈ Finset.Icc 1 N → Ω → ℝ) :
    Finset.sum (Finset.Icc 1 N)
        (fun t =>
          ∫ ω, (if ht : t ∈ Finset.Icc 1 N then γ t * F t ht ω else 0) ∂μ) =
      Finset.sum (Finset.Icc 1 N).attach
        (fun t => γ t.1 * ∫ ω, F t.1 t.2 ω ∂μ) := by
  simpa [smul_eq_mul] using
    (sum_integral_guarded_smul_eq_sum_attach (μ := μ) (s := Finset.Icc 1 N)
      (γ := γ) (F := F))

open MeasureTheory
open scoped BigOperators

/-- Normalize a nested lower/upper guarded interval sum of weighted integrals.

Each summand carries separate `a ≤ t` and `t ≤ b` guards only to expose the
proof arguments needed by the integrand. Summing over `Finset.Icc a b` makes
both guards true, and `integral_const_mul` pulls the deterministic scalar
weight outside the integral.

Layer: Glue | Gap: Level 0 (nested guarded interval-integral attached-sum normalization)
Proof: rewrite the finite interval sum as a sum over `attach`, discharge both
  lower and upper guards using `Finset.mem_Icc.mp`, and apply
  `MeasureTheory.integral_const_mul`.
Source: Mathlib finite-sum attachment and Bochner integral scalar-multiplication APIs
Used in: randomized accelerated proximal-point residual-window normalization before
  applying time-local conditional-expectation bounds
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine
  Learning, randomized accelerated proximal-point method -/
theorem sum_Icc_integral_nested_guarded_const_mul_eq_sum_attach
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (a b : ℕ) (γ : ℕ → ℝ)
    (F : (t : ℕ) → a ≤ t → t ≤ b → Ω → ℝ) :
    Finset.sum (Finset.Icc a b)
        (fun t =>
          ∫ ω,
            (if hta : a ≤ t then
              if htb : t ≤ b then γ t * F t hta htb ω else 0
            else 0) ∂μ) =
      Finset.sum (Finset.Icc a b).attach
        (fun t =>
          γ t.1 *
            ∫ ω,
              F t.1 (Finset.mem_Icc.mp t.2).1 (Finset.mem_Icc.mp t.2).2 ω ∂μ) := by
  rw [← Finset.sum_attach (s := Finset.Icc a b)]
  refine Finset.sum_congr rfl ?_
  intro t _ht
  simp only [dif_pos (Finset.mem_Icc.mp t.2).1,
    dif_pos (Finset.mem_Icc.mp t.2).2]
  rw [MeasureTheory.integral_const_mul]

-- Batch 2 promoted from .sgd_phase3_staging/SOptLib/Glue/integrable_sub_const_of_isCompact_continuousOn_measurable_mem.lean
-- Generalization plan (G0):
-- concept/name: integrability of a constant-shifted compact-carrier observable; orig was `expectedGap_integrable_of_outerStateAdapted`
-- generality used: arbitrary measurable source space, finite measure, Borel topological target, compact carrier, continuous-on real observable, measurable carrier-valued process; no convexity, smoothness, oracle, filtration, probability, or finite-dimensional assumptions
-- portable call pattern: objective-gap or residual integrability for stochastic mirror descent, stochastic conditional-gradient, and proximal algorithms whose output process is measurable and stays in a compact feasible set while the objective/baseline constant changes
-- counterargument checked: not paper-local traceability because the theorem removes all SCGS notation and packages a recurring compact-boundedness plus measurable-composition integrability step; not a pure wrapper since Mathlib/SOptLib provide the ingredients but not this carrier-process conclusion
-- coverage search: checked `integrable sub const continuousOn compact measurable mem`, SOptLib `exists_nonneg_norm_bound_of_isCompact_of_continuousOn`, `integrable_of_measurable_bounded_real`, `integrable_sq_norm_sub_of_measurable_mem_diameter_bound`, and staged `measurable_sub_const_of_continuousOn_comp_measurable_mem`; Mathlib semantic search returned HTTP 502, and no local hit covered this exact scalar observable integrability shape
-- minimal hypotheses: compactness and continuous-on are needed for the uniform bound, finite measure for bounded measurable integrability, and pointwise membership is used only to evaluate the bound along the process

open MeasureTheory

/-- A constant shift of a compact-carrier continuous observable is integrable along a feasible process.

If `f` is continuous on a compact carrier `X`, `y` is measurable, and every
`y ω` lies in `X`, then `ω ↦ f (y ω) - c` is integrable for every finite measure.

Layer: Glue | Gap: Level 1 (compact-carrier observable integrability)
Proof: first compose the continuous-on observable through the carrier subtype to
  get measurability, then use compactness to bound `‖f‖` on the carrier and
  apply finite-measure integrability of bounded real random variables.
Source: Mathlib compact extreme-value, subtype topology, and finite-measure
  integrability APIs
Used in: stochastic conditional-gradient sliding expected objective-gap
  integrability for compact feasible output processes
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem integrable_sub_const_of_isCompact_continuousOn_measurable_mem
    {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Set E) (f : E → ℝ) (y : Ω → E) (c : ℝ)
    (hX : IsCompact X) (hf : ContinuousOn f X)
    (hy : Measurable y) (hy_mem : ∀ ω, y ω ∈ X) :
    Integrable (fun ω => f (y ω) - c) μ := by
  have hmeas : Measurable (fun ω => f (y ω) - c) := by
    have hfCarrier : Continuous (fun x : {x : E // x ∈ X} => f x.1) :=
      continuous_subtype_of_continuousOn_ambient
        (X := X) (fun x : {x : E // x ∈ X} => f x.1) f hf (by
          intro x
          rfl)
    have hySubtype :
        Measurable (fun ω => (⟨y ω, hy_mem ω⟩ : {x : E // x ∈ X})) :=
      Measurable.subtype_mk hy
    exact (hfCarrier.measurable.comp hySubtype).sub measurable_const
  obtain ⟨C, _hC_nonneg, hC⟩ :=
    exists_nonneg_norm_bound_of_isCompact_of_continuousOn f hX hf
  refine integrable_of_measurable_bounded_real hmeas (C := C + ‖c‖) ?_
  intro ω
  calc
    ‖f (y ω) - c‖ ≤ ‖f (y ω)‖ + ‖c‖ := norm_sub_le _ _
    _ ≤ C + ‖c‖ := add_le_add (hC (y ω) (hy_mem ω)) le_rfl


-- Batch 2 promoted from Staging/twoIndexSample_indep_strictPast_current.lean
/-!
-- Generalization plan (G1):
-- concept/name: arbitrary-index sample freshness from a strict-past sigma-algebra; orig was `twoIndexSample_current_indep_strictPast`, renamed to expose the reusable `iIndepFun`/disjoint-singleton bridge
-- generality used: arbitrary sample space `Omega`, sample value type `Sample`, measure `mu`, index type `ι`, family `xi : ι -> Omega -> Sample`, strict-past sigma-algebra, past index set, and current index; no topology, convexity, smoothness, oracle, or finite-dimensional assumptions are used
-- portable call pattern: mini-batch stochastic approximation, stochastic mirror descent, SGD, and variance-reduced proofs can instantiate any independently indexed sample family, strict-past history sigma-algebra, and current coordinate to prove freshness of the current sample while changing only the index set description and history bound
-- counterargument checked: not paper-local traceability because the statement is free of algorithm state, oracle, objective, and theorem-number vocabulary; it is not a pure wrapper around caller expressions because it packages the recurring `iIndepFun` to generated strict-past independence bridge with the necessary left-shrink step
-- coverage search: searched `twoIndexSample strictPast current independence`, catalog entries for `indep_prefixFiltration_future`, `indep_sampleBlock_singleton_of_not_mem`, and `indep_strictPast_sup_coordinate_of_disjoint_current`; those hits cover one-index prefixes, finite blocks, or finite block plus peer-coordinate joins, while this theorem covers an arbitrary past set and an arbitrary strict-past sigma-algebra bounded by its generated coordinates
-- minimal hypotheses: all already minimal; coordinate measurability is required to turn `iIndepFun` into independent comap sigma-algebras, `hxi_iIndep` supplies independence, `hpast_disj` supplies freshness, and `hstrict_le` is the exact caller-side history bound
-/

namespace SOptLib

open MeasureTheory ProbabilityTheory

/-- A strict-past sigma-algebra generated by disjoint independent samples is
independent of the current sample.

For an independent indexed sample family, any sigma-algebra bounded by the
one generated from a past index set is independent of the sigma-algebra
generated by a current coordinate, provided the past set is disjoint from that
coordinate.

Layer: Glue | Gap: Level 1 (strict-past current-sample freshness)
Proof: apply independence of disjoint indexed `iSup`s to the past set and the
  singleton current coordinate, collapse the singleton `iSup`, and shrink the
  left sigma-algebra through the supplied strict-past bound.
Source: Mathlib probability independence API for `iIndepFun`, independent
  generated sigma-algebras, and sub-sigma-algebra monotonicity
Used in: stochastic conditional-gradient sliding martingale cancellation for a
  current mini-batch sample against the generated strict optimization past
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem iIndepFun_indep_strictPast_singleton
    {Omega Sample ι : Type*} [mOmega : MeasurableSpace Omega]
    [mSample : MeasurableSpace Sample]
    (xi : ι -> Omega -> Sample) (mu : Measure Omega)
    (hxi_meas : forall q, Measurable (xi q))
    (hxi_iIndep : ProbabilityTheory.iIndepFun xi mu)
    (strictPast : MeasurableSpace Omega) (pastSet : Set ι)
    (current : ι)
    (hpast_disj : Disjoint pastSet ({current} : Set ι))
    (hstrict_le :
      strictPast ≤
        (⨆ q ∈ pastSet,
          MeasurableSpace.comap (xi q) mSample)) :
    ProbabilityTheory.Indep strictPast
      (MeasurableSpace.comap (xi current) mSample) mu := by
  classical
  let mPair : ι -> MeasurableSpace Omega :=
    fun q => MeasurableSpace.comap (xi q) mSample
  have hiPair : ProbabilityTheory.iIndep mPair mu := by
    simpa [mPair] using hxi_iIndep.iIndep
  have h_le : forall q, mPair q ≤ mOmega := by
    intro q
    simpa [mPair] using (hxi_meas q).comap_le
  have hpast_iSup_indep_current_iSup :
      ProbabilityTheory.Indep
        (⨆ q ∈ pastSet, mPair q)
        (⨆ q ∈ ({current} : Set ι), mPair q) mu :=
    ProbabilityTheory.indep_iSup_of_disjoint (Ω := Omega) (ι := ι)
      (m := mPair) (_mΩ := mOmega) (μ := mu) h_le hiPair hpast_disj
  have hpast_indep_current :
      ProbabilityTheory.Indep
        (⨆ q ∈ pastSet,
          MeasurableSpace.comap (xi q) mSample)
        (MeasurableSpace.comap (xi current) mSample) mu := by
    simpa [mPair] using hpast_iSup_indep_current_iSup
  exact ProbabilityTheory.indep_of_indep_of_le_left hpast_indep_current hstrict_le

/-- A strict-past-measurable random variable is independent of the current
sample.

This is the random-variable form of
`iIndepFun_indep_strictPast_singleton`: once a caller proves its query is
measurable with respect to the strict-past sigma-algebra, independence from the
current sample follows from the same disjointness and history-bound hypotheses.

Layer: Glue | Gap: Level 1 (strict-past measurable query current-sample freshness)
Proof: apply `iIndepFun_indep_strictPast_singleton` to get sigma-algebra
  independence, then shrink the left comap through the query measurability.
Source: Mathlib probability independence API for random variables, independent
  generated sigma-algebras, and sub-sigma-algebra monotonicity
Used in: stochastic conditional-gradient sliding martingale cancellation for a
  strict-past measurable query against the current mini-batch sample
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem iIndepFun_indepFun_strictPast_singleton
    {Omega Sample Query ι : Type*} [mOmega : MeasurableSpace Omega]
    [mSample : MeasurableSpace Sample] [MeasurableSpace Query]
    (xi : ι -> Omega -> Sample) (mu : Measure Omega)
    (hxi_meas : forall q, Measurable (xi q))
    (hxi_iIndep : ProbabilityTheory.iIndepFun xi mu)
    (strictPast : MeasurableSpace Omega) (pastSet : Set ι)
    (current : ι) {X : Omega -> Query}
    (hX : Measurable[strictPast] X)
    (hpast_disj : Disjoint pastSet ({current} : Set ι))
    (hstrict_le :
      strictPast ≤
        (⨆ q ∈ pastSet,
          MeasurableSpace.comap (xi q) mSample)) :
    ProbabilityTheory.IndepFun X (xi current) mu := by
  exact
    @indepFun_of_measurable_left_of_indep_comap Omega Query Sample mOmega
      (by infer_instance) mSample (μ := mu) (m := strictPast)
      (X := X) (Y := xi current) hX
    (iIndepFun_indep_strictPast_singleton
      (mOmega := mOmega) (mSample := mSample) (ι := ι)
      (xi := xi) (mu := mu) (hxi_meas := hxi_meas)
      (hxi_iIndep := hxi_iIndep) (strictPast := strictPast)
      (pastSet := pastSet) (current := current) hpast_disj hstrict_le)

end SOptLib


-- Batch 2 promoted from Staging/twoIndexSample_indep_strictPast_sup_peer_current.lean
/-!
-- Generalization plan (G0):
-- concept/name: `iIndepFun` independence from a strict-past sigma-algebra joined with a peer coordinate; orig was `twoIndexSample_current_indep_strictPast_sup_peer`, renamed to expose the arbitrary-index strict-past/coordinate freshness pattern rather than a local proof-block label
-- generality used: arbitrary probability space carrier `Omega`, sample value type `Sample`, measure `mu`, index type `ι`, indexed family `xi : ι -> Omega -> Sample`, strict-past sigma-algebra, past index set, peer index, and current index; no topology, convexity, smoothness, oracle, or finite-dimensional assumptions are used
-- portable call pattern: mini-batch stochastic approximation, SGD, stochastic mirror descent, and variance-reduced proofs can instantiate current and peer coordinates to prove off-diagonal independence between one fresh sample and a query bundled with another same-batch sample
-- counterargument checked: not paper-local traceability because the statement is free of algorithm state, objective, oracle, theorem-number, and source-field vocabulary; it is not a full duplicate of the current-only strict-past theorem because the left sigma-algebra explicitly includes a peer current coordinate and packages the recurring `sup` bound
-- coverage search: searched `twoIndexSample strictPast current peer independence`, catalog entries for `indepFun_prod_past_current_of_indep_current`, `indep_strictPast_sup_coordinate_of_disjoint_current`, and staged `iIndepFun_indep_strictPast_singleton`; those hits cover product transfer, finite blocks, or strict-past current freshness, while this theorem covers an arbitrary strict-past sigma-algebra joined with a peer coordinate
-- minimal hypotheses: all already minimal; coordinate measurability turns `iIndepFun` into independent comap sigma-algebras, `hxi_iIndep` supplies independence, `hleft_disj` supplies current freshness from both past and peer, and `hstrict_le` is the exact caller-side history bound
-/

namespace SOptLib

open MeasureTheory ProbabilityTheory

/-- A strict-past sigma-algebra joined with a peer coordinate is independent of a
distinct current coordinate.

For an independent indexed sample family, if `pastSet` together with `peer` is
disjoint from `current`, then any strict-past sigma-algebra generated by
`pastSet`, after adjoining the peer sample, is independent of the sample at
`current`.

Layer: Glue | Gap: Level 1 (strict-past plus peer current-sample freshness)
Proof: apply the strict-past singleton independence theorem to the enlarged
  index set `pastSet ∪ {peer}` and shrink the left sigma-algebra using the
  supplied strict-past bound plus the peer coordinate inclusion.
Source: Mathlib probability independence API for `iIndepFun`, independent
  generated sigma-algebras, and sub-sigma-algebra monotonicity
Used in: stochastic conditional-gradient sliding off-diagonal mini-batch
  variance expansion for a query paired with a peer current sample
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem iIndepFun_indep_strictPast_sup_coordinate_singleton
    {Omega Sample ι : Type*} [mOmega : MeasurableSpace Omega]
    [mSample : MeasurableSpace Sample]
    (xi : ι -> Omega -> Sample) (mu : Measure Omega)
    (hxi_meas : forall q, Measurable (xi q))
    (hxi_iIndep : ProbabilityTheory.iIndepFun xi mu)
    (strictPast : MeasurableSpace Omega) (pastSet : Set ι)
    (peer current : ι)
    (hleft_disj : Disjoint (pastSet ∪ ({peer} : Set ι)) ({current} : Set ι))
    (hstrict_le :
      strictPast ≤
        (⨆ q ∈ pastSet,
          MeasurableSpace.comap (xi q) mSample)) :
    ProbabilityTheory.Indep
      (strictPast ⊔ MeasurableSpace.comap (xi peer) mSample)
      (MeasurableSpace.comap (xi current) mSample) mu := by
  classical
  refine
    iIndepFun_indep_strictPast_singleton
      (mOmega := mOmega) (mSample := mSample) (ι := ι)
      (xi := xi) (mu := mu) (hxi_meas := hxi_meas)
      (hxi_iIndep := hxi_iIndep)
      (strictPast := strictPast ⊔ MeasurableSpace.comap (xi peer) mSample)
      (pastSet := pastSet ∪ ({peer} : Set ι)) (current := current)
      hleft_disj ?_
  refine sup_le ?_ ?_
  · exact le_trans hstrict_le <| by
      refine iSup_le ?_
      intro q
      refine iSup_le ?_
      intro hq
      exact le_iSup_of_le q (le_iSup_of_le (Or.inl hq) le_rfl)
  · exact le_iSup_of_le peer (le_iSup_of_le (Or.inr rfl) le_rfl)

end SOptLib

-- Batch 2 promoted from Staging/aestronglyMeasurable_of_finite_key_reconstruction.lean
open MeasureTheory

-- Generalization plan (G0):
-- concept/name: countable-key reconstruction a.e.-strong measurability; orig was
--   aestronglyMeasurable_algorithmSampleLaw_of_prefix_const
-- generality used: arbitrary measurable source space, countable measurable key with
--   measurable singletons, arbitrary measure, a reconstruction map, and
--   topological codomain only
-- portable call pattern: mini-batch and sample-window stochastic proofs where an
--   observable is reconstructed from a countable prefix key; path space, key type,
--   law, reconstruction map, and codomain vary while AEStronglyMeasurable stays
-- counterargument checked: not paper-local traceability because the proof boundary
--   avoids target MeasurableSpace assumptions in any countable-prefix process; not a
--   pure wrapper around Measurable.aestronglyMeasurable_measure, which needs
--   target measurability
-- coverage search: LeanSearch for "a.e. strongly measurable function equal to
--   composition with countable measurable key" returned only composition and
--   discrete-source lemmas; SOptLib catalog hits Measurable.aestronglyMeasurable_measure
--   and aestronglyMeasurable_map_of_measurable_on_ae_support are adjacent but
--   require target measurability/support-extension structure, so coverage is partial
-- minimal hypotheses: Countable Key and MeasurableSingletonClass Key are needed by
--   AEStronglyMeasurable.of_discrete; no finite dimension, norm, or
--   probability assumption is used

/-- An observable reconstructed a.e. from a countable a.e.-measurable key is
a.e.-strongly measurable.

If `Y` is an a.e.-measurable countable key and `Z` agrees a.e. with
`reconstruct ∘ Y`, then `Z` is a.e.-strongly measurable.  The codomain only
needs a topology: the reconstruction map is a.e.-strongly measurable because
its domain is countable and has measurable singletons.

Layer: Glue | Gap: Level 1 (countable-key reconstruction a.e.-strong measurability)
Proof: use `AEStronglyMeasurable.of_discrete` for the countable key
  reconstruction, compose with the a.e.-measurable key map, and transfer across
  the supplied a.e. equality.
Source: Mathlib strongly measurable functions on countable measurable-singleton
  spaces and a.e. congruence APIs
Used in: stochastic finite-prefix mini-batch reconstruction measurability
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic conditional gradient sliding -/
theorem aestronglyMeasurable_of_countable_key_reconstruction
    {Ω Key E : Type*} [MeasurableSpace Ω] [MeasurableSpace Key]
    [Countable Key] [MeasurableSingletonClass Key] [TopologicalSpace E]
    {μ : Measure Ω} {Y : Ω → Key} {Z : Ω → E}
    (hY : AEMeasurable Y μ) (reconstruct : Key → E)
    (hZ : reconstruct ∘ Y =ᵐ[μ] Z) :
    AEStronglyMeasurable Z μ := by
  have hrec : AEStronglyMeasurable reconstruct (Measure.map Y μ) := by
    exact AEStronglyMeasurable.of_discrete
  exact (hrec.comp_aemeasurable hY).congr hZ


-- Batch 2 promoted from Staging/integral_comp_le_integral_comp_bound_of_indep_fixed_integral_bound.lean
open MeasureTheory ProbabilityTheory

-- Generalization plan (G0):
-- concept/name: product-law integral bound transfer with a composed random bound; orig was
--   integral_comp_le_integral_bound_of_indep_fixed_integral_bound.
-- generality used: arbitrary measurable spaces Ω, W, and Smp; finite measure P and measure ν;
--   measurable scalar kernel φ, measurable bound B, measurable random inputs X and Y,
--   independence of X and Y, law identity for Y, integrability of φ(X,Y) and B(X).
-- portable call pattern: random-query and finite-prefix variance proofs vary the prefix
--   variable X, fresh sample Y, scalar kernel φ, law ν, and random bound B while retaining
--   the same composed integral inequality.
-- counterargument checked: not paper-local traceability and not a one-line wrapper; the
--   theorem packages the product-law/Fubini step needed whenever a fixed-fiber bound has a
--   random query-dependent right side.
-- coverage search: SOptLib hits integral_comp_le_of_indep_fixed_integral_bound and
--   integrable_comp_of_indep_fixed_integral_bound cover only uniform constant bounds;
--   LeanSearch hits independence/conditional expectation API but no direct variable-bound
--   composed integral transfer.
-- minimal hypotheses: only finiteness of the source measure P is assumed; finiteness of ν is
--   derived from the law identity. No convexity, normed-space, finite-dimensional, or
--   optimization-specific assumptions.

/-- Transfer fixed-fiber scalar integral bounds through an independent random parameter
when the bound depends on the fixed parameter.

If `Y` has law `ν`, `X` is independent of `Y`, and every fixed-fiber integral
`∫ s, φ w s ∂ν` is bounded above by `B w`, then the composed random integral is
bounded above by the integral of the composed bound `B ∘ X`.

Layer: Glue | Gap: Level 1 (product-law/Fubini integral-bound transfer)
Proof: identify the joint law using independence, rewrite as a product integral,
  apply Fubini, integrate the pointwise fixed-fiber bound, and map the bound
  integral back along `X`.
Source: Mathlib product-measure integration and independence APIs
Used in: stochastic conditional-gradient sliding finite-prefix variance transfer
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
theorem integral_comp_le_integral_comp_bound_of_indep_fixed_integral_bound
    {Ω W Smp : Type*} [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace Smp]
    {P : Measure Ω} {ν : Measure Smp} [IsFiniteMeasure P]
    {φ : W → Smp → ℝ} {B : W → ℝ} {X : Ω → W} {Y : Ω → Smp}
    (hφ : Measurable (Function.uncurry φ))
    (hB : Measurable B) (hX : Measurable X) (hY : Measurable Y)
    (h_indep : IndepFun X Y P)
    (h_dist : Measure.map Y P = ν)
    (h_int : Integrable (fun ω => φ (X ω) (Y ω)) P)
    (hB_int : Integrable (fun ω => B (X ω)) P)
    (hfixed_bound : ∀ w, ∫ s, φ w s ∂ν ≤ B w) :
    ∫ ω, φ (X ω) (Y ω) ∂P ≤ ∫ ω, B (X ω) ∂P := by
  haveI : IsFiniteMeasure ν := by
    rw [← h_dist]
    exact Measure.isFiniteMeasure_map P Y
  have h_joint_meas : AEMeasurable (fun ω => (X ω, Y ω)) P :=
    (hX.prodMk hY).aemeasurable
  have h_f_meas : Measurable (fun p : W × Smp => φ p.1 p.2) := hφ
  have h_prod_eq : P.map (fun ω => (X ω, Y ω)) = (P.map X).prod ν := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).mp
      h_indep, h_dist]
  have h_int_prod : Integrable (fun p : W × Smp => φ p.1 p.2) ((P.map X).prod ν) := by
    have h1 : Integrable (fun p : W × Smp => φ p.1 p.2)
        (P.map (fun ω => (X ω, Y ω))) :=
      (integrable_map_measure h_f_meas.aestronglyMeasurable h_joint_meas).mpr h_int
    rwa [h_prod_eq] at h1
  have hB_map_int : Integrable B (P.map X) := by
    exact (integrable_map_measure hB.aestronglyMeasurable hX.aemeasurable).mpr hB_int
  calc
    ∫ ω, φ (X ω) (Y ω) ∂P
        = ∫ p : W × Smp, φ p.1 p.2 ∂P.map (fun ω => (X ω, Y ω)) :=
          (integral_map h_joint_meas h_f_meas.aestronglyMeasurable).symm
    _ = ∫ p : W × Smp, φ p.1 p.2 ∂(P.map X).prod ν := by rw [h_prod_eq]
    _ = ∫ w : W, ∫ s : Smp, φ w s ∂ν ∂P.map X := integral_prod _ h_int_prod
    _ ≤ ∫ w : W, B w ∂P.map X := by
      exact integral_mono h_int_prod.integral_prod_left hB_map_int
        (fun w => hfixed_bound w)
    _ = ∫ ω, B (X ω) ∂P :=
      integral_map hX.aemeasurable hB.aestronglyMeasurable


-- Batch 2 promoted from Staging/indepFun_prefixKey_current_of_iIndepFun.lean
open MeasureTheory ProbabilityTheory

-- Generalization plan (G0):
-- concept/name: prefix-key/current-coordinate freshness for an `iIndepFun` sample stream; orig was `strict_prefix_key_indep_current_coordinate_of_iIndep_pair_stream`, renamed away from theorem-local strict-prefix bookkeeping toward an arbitrary prefix key measurable from a strict-past sigma-algebra
-- generality used: arbitrary measurable probability carrier `Ω`, index type `I`, sample value type `Sample`, prefix value type `Prefix`, abstract measure `μ`, indexed sample coordinate map, arbitrary strict-past sigma-algebra bounded by a generated past index set, and a prefix key measurable from that sigma-algebra; no topology, convexity, smoothness, oracle, or finite-dimensional assumptions are used
-- portable call pattern: finite-memory stochastic approximation, SGD, stochastic mirror descent, variance-reduced, and mini-batch proofs can instantiate a different sample-coordinate map, current time/index, peer mini-batch coordinate, and prefix reconstruction key while retaining prefix/current and prefix-plus-peer/current independence conclusions
-- counterargument checked: existing SOptLib hits provide the one-coordinate strict-past independence bridge and the strict-past-plus-peer sigma-algebra bridge; this theorem is not a paper-local traceability label because it bundles the random-variable conclusions that recurring martingale and off-diagonal mini-batch cancellations call directly, with no algorithm/objective/oracle vocabulary
-- coverage search: searched `indepFun prefix key current iIndepFun strictPast sup coordinate singleton`, `iIndepFun independent finite set current coordinate strict past`, and catalog entries for `SOptLib.iIndepFun_indepFun_strictPast_singleton`, `SOptLib.iIndepFun_indep_strictPast_sup_coordinate_singleton`, and `indepFun_prod_past_current_of_indep_current`; coverage is partial because those entries expose the lower-level pieces separately rather than the bundled prefix-key/current API used by stochastic finite-memory proofs
-- minimal hypotheses: all already minimal; coordinate measurability is required by the existing finite-family independence API, `iIndepFun` supplies independence, `hstrict_le` and `hprefixKey_meas` are the exact history measurability assumptions, and disjointness hypotheses express freshness of current from the past and from the past joined with a peer

/-- A strict-past prefix key is independent of a current sample coordinate, and
the prefix key paired with a peer coordinate is independent of a distinct
current coordinate.

For an independent indexed sample family, any prefix key measurable from a
strict-past sigma-algebra is fresh from a disjoint current coordinate.  The same
freshness remains true after adjoining one peer coordinate, provided the past
indices together with the peer remain disjoint from the current index.

Layer: Glue | Gap: Level 1 (prefix-key current-sample freshness)
Proof: apply the SOptLib strict-past `iIndepFun` freshness lemmas, then use the
  product random-variable independence bridge for the peer-coordinate bundle.
Source: Mathlib probability independence API for `iIndepFun`, generated
  sigma-algebras, and sub-sigma-algebra monotonicity
Used in: stochastic conditional-gradient sliding mini-batch martingale and
  off-diagonal variance cancellation for strict-prefix reconstructed iterates
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem indepFun_prefixKey_current_of_iIndepFun
    {Ω I Sample Prefix : Type*} [mΩ : MeasurableSpace Ω]
    [mSample : MeasurableSpace Sample] [MeasurableSpace Prefix]
    {μ : Measure Ω} {sampleCoord : I → Ω → Sample}
    (hsampleCoord_meas : ∀ i, @Measurable Ω Sample mΩ mSample (sampleCoord i))
    (hsampleCoord_iIndep : @iIndepFun Ω I mΩ (fun _ : I => Sample)
      (fun _ : I => mSample) sampleCoord μ)
    {pastSet : Set I} {strictPast : MeasurableSpace Ω}
    {prefixKey : Ω → Prefix} {current : I}
    (hprefixKey_meas : Measurable[strictPast] prefixKey)
    (hstrict_le :
      strictPast ≤
        (⨆ i ∈ pastSet, MeasurableSpace.comap (sampleCoord i) mSample))
    (hpast_current_disj : Disjoint pastSet ({current} : Set I)) :
    @IndepFun Ω Prefix Sample mΩ (by infer_instance) mSample
      prefixKey (sampleCoord current) μ ∧
      ∀ peer : I,
        Disjoint (pastSet ∪ ({peer} : Set I)) ({current} : Set I) →
          @IndepFun Ω (Prefix × Sample) Sample mΩ (by infer_instance) mSample
            (fun ω => (prefixKey ω, sampleCoord peer ω)) (sampleCoord current) μ := by
  constructor
  · exact
      SOptLib.iIndepFun_indepFun_strictPast_singleton
        (mOmega := mΩ) (mSample := mSample) (ι := I)
        (xi := sampleCoord) (mu := μ)
        (hxi_meas := hsampleCoord_meas)
        (hxi_iIndep := hsampleCoord_iIndep)
        (strictPast := strictPast) (pastSet := pastSet)
        (current := current) (X := prefixKey)
        hprefixKey_meas hpast_current_disj hstrict_le
  · intro peer hleft_disj
    exact
      @indepFun_prod_past_current_of_indep_current
        Ω Prefix Sample Sample mΩ (by infer_instance) mSample mSample
        μ strictPast prefixKey (sampleCoord peer) (sampleCoord current)
        hprefixKey_meas
        (SOptLib.iIndepFun_indep_strictPast_sup_coordinate_singleton
          (mOmega := mΩ) (mSample := mSample) (ι := I)
          (xi := sampleCoord) (mu := μ)
          (hxi_meas := hsampleCoord_meas)
          (hxi_iIndep := hsampleCoord_iIndep)
          (strictPast := strictPast) (pastSet := pastSet)
          (peer := peer) (current := current)
          hleft_disj hstrict_le)


-- Batch 6 promoted from Staging/integrable_map_of_finite_range.lean
open MeasureTheory

-- Generalization plan (G0):
-- concept/name: finite-range pushforward-law integrability; orig was
--   `integrable_map_of_finite_range_support`, renamed to
--   `integrable_map_of_finite_range`.
-- generality used: arbitrary measurable source and key spaces, measurable
--   singletons on the key space, finite base measure, a.e. measurable
--   finite-range key, and normed-additive observable values.
-- portable call pattern: generated-process proofs with a finite-range state
--   key `W`; the state type, finite range proof, observable `phi`, and base
--   measure vary while integrability under `Measure.map W mu` is unchanged.
-- counterargument checked: not paper-local and not a pure wrapper; it packages
--   the recurring finite-support pushforward-law step that otherwise requires
--   separate support measurability, map transport, and finite-range
--   integrability arguments.
-- coverage search: queried `Integrable Measure.map finite range`,
--   `integrable function under pushforward measure finite range`, and
--   `integrable of finite range finite key`; closest hits were Mathlib
--   `MeasureTheory.integrable_map_measure`,
--   `MeasureTheory.Integrable.of_finite`, SOptLib
--   `integrable_map_measure_of_integrable_comp`, SOptLib
--   `integrable_of_finite_range`, and SOptLib
--   `integrable_of_finiteRange_factor`; all are component or different-shape
--   lemmas, not this finite-range pushforward-law conclusion.
-- minimal hypotheses: no finite-dimensional, inner-product, convexity,
--   smoothness, or probability assumption is used; finite measure and
--   measurable singletons are the measure-theoretic requirements.

/-- A finite-range pushforward law integrates arbitrary normed observables.

If an a.e. measurable key `W` has finite range, then every observable on the
key space is integrable under the pushed-forward law `Measure.map W μ` over a
finite base measure.

Layer: Glue | Gap: Level 1 (finite-range pushforward-law integrability)
Proof: first obtain a.e. strong measurability from finite support of the
  pushed-forward law, then transport integrability through `Measure.map` and
  prove the pulled-back observable integrable by finite-range boundedness.
Source: Mathlib Bochner integrability, map-measure, finite-range, and
  measurable-singleton APIs
Used in: variance-reduced accelerated gradient generated-history observables
  under finite-state pushforward laws
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem integrable_map_of_finite_range
    {Ω A E : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSingletonClass A] [NormedAddCommGroup E]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (W : Ω → A) (hW : AEMeasurable W μ)
    (hfin : (Set.range W).Finite) (φ : A → E) :
    Integrable φ (Measure.map W μ) := by
  classical
  have hφ : AEStronglyMeasurable φ (Measure.map W μ) := by
    haveI : Fintype {a : A // a ∈ Set.range W} := hfin.fintype
    exact
      aestronglyMeasurable_map_of_measurable_on_ae_support
        (P := μ) (wt := W) (A := Set.range W) (φ := φ)
        hfin.measurableSet
        (by exact StronglyMeasurable.of_discrete)
        (MeasureTheory.ae_map_mem_range W hfin.measurableSet μ)
  refine integrable_map_measure_of_integrable_comp hφ hW ?_
  have hcomp_aestrong : AEStronglyMeasurable (φ ∘ W) μ :=
    hφ.comp_aemeasurable hW
  have hcomp_finite : (Set.range (φ ∘ W)).Finite := by
    have hsubset : Set.range (φ ∘ W) ⊆ φ '' Set.range W := by
      rintro y ⟨ω, rfl⟩
      exact ⟨W ω, ⟨ω, rfl⟩, rfl⟩
    exact (hfin.image φ).subset hsubset
  exact integrable_of_finite_range hcomp_aestrong hcomp_finite


-- Batch 6 promoted from Staging/integrable_prod_of_finite_left_map_fintype_right.lean
open MeasureTheory

-- Generalization plan (G0):
-- concept/name: product-law integrability from finite left pushforward support
--   and finite right type; orig was
--   `integrable_prod_right_fintype_of_finite_left_map`, renamed to
--   `integrable_prod_of_finite_left_map_fintype_right`.
-- generality used: arbitrary measurable source, left key, and finite right
--   type; measurable singletons on both coordinate spaces; finite base and
--   right measures; and an arbitrary normed-additive observable value type.
--   No optimization setup, convexity, smoothness, filtration, or probability
--   normalization is used.
-- portable call pattern: adaptive stochastic sampling proofs instantiate the
--   finite generated-history key as `W` and the finite fresh-sample index type
--   as `iota`; the key type, sample law, observable kernel, and base measure
--   change while the product-law integrability conclusion stays the same.
-- counterargument checked: not paper-local traceability and not a one-line
--   wrapper, because callers otherwise must rebuild finite product support,
--   a.e. strong measurability on that support, product-integrability
--   reduction, finite fibers, and the finite-range outer norm integral.
--   Mathlib has `integrable_prod_iff`, and SOptLib has finite-range map
--   integrability and finite-PMF product integrability, but neither proves
--   this automatic product-law conclusion from a finite left map and finite
--   right type.
-- coverage search: searched CATALOG/SOptLib/Staging/Algorithms for
--   `integrable_prod`, `finite_range`, `finite_left`, `Fintype`, and
--   `product integrability`; read full signatures of SOptLib
--   `integrable_of_finite_range`, `integrable_map_of_finite_range`, and
--   `PMF.integrable_prod_of_fiber_integrable`. LeanSearch for "integrable
--   product measure finite support finite type arbitrary function" returned
--   Mathlib `MeasureTheory.integrable_prod_iff` and finite pi-product lemmas,
--   all partial rather than this finite-support product bridge.
-- minimal hypotheses: `NormedAddCommGroup` is enough for Bochner
--   integrability and norm bounds; no `NormedSpace ℝ`, complete space,
--   finite-dimensional, or probability measure assumption is needed.

/-- A product law integrates arbitrary normed observables when the left law is
supported on a finite map range and the right space is finite.

If `W` has finite range under a finite base measure and `iota` is a finite
measurable-singleton type with a finite measure, then every kernel
`F : A -> iota -> E` is integrable over `(Measure.map W mu).prod nu`.

Layer: Glue | Gap: Level 1 (finite-support product-law integrability)
Proof: finite product support gives a.e. strong measurability of the uncurried
  kernel; `integrable_prod_iff` reduces product integrability to finite right
  fibers and a finite-range left pushforward norm integral.
Source: Mathlib product-measure integration, finite measurable-set support, and
  Bochner finite-range integrability APIs
Used in: variance-reduced accelerated gradient generated-history and fresh
  component-sample product kernels for one-step potential expectations
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem integrable_prod_of_finite_left_map_fintype_right
    {Omega A iota E : Type*} [MeasurableSpace Omega] [MeasurableSpace A]
    [MeasurableSingletonClass A] [MeasurableSpace iota] [Fintype iota]
    [MeasurableSingletonClass iota] [NormedAddCommGroup E]
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (W : Omega -> A) (hW : AEMeasurable W mu)
    (hfin : (Set.range W).Finite) (nu : Measure iota)
    [IsFiniteMeasure nu] (F : A -> iota -> E) :
    Integrable (fun z : A × iota => F z.1 z.2)
      ((Measure.map W mu).prod nu) := by
  classical
  let support : Set (A × iota) := Set.range W ×ˢ (Set.univ : Set iota)
  have hsupport_finite : support.Finite := by
    simpa [support] using hfin.prod (Set.finite_univ : (Set.univ : Set iota).Finite)
  have hsupport_meas : MeasurableSet support := hsupport_finite.measurableSet
  have hleft_support :
      ∀ᵐ a ∂Measure.map W mu, a ∈ Set.range W :=
    MeasureTheory.ae_map_mem_range W hfin.measurableSet mu
  have hprod_support :
      ∀ᵐ z ∂(Measure.map W mu).prod nu, z ∈ support := by
    rw [Measure.ae_prod_mem_iff_ae_ae_mem hsupport_meas]
    filter_upwards [hleft_support] with a ha
    exact Filter.Eventually.of_forall (fun i => by simp [support, ha])
  haveI : Fintype {z : A × iota // z ∈ support} := hsupport_finite.fintype
  have hF_aestrong :
      AEStronglyMeasurable (fun z : A × iota => F z.1 z.2)
        ((Measure.map W mu).prod nu) := by
    have htmp :
        AEStronglyMeasurable (fun z : A × iota => F z.1 z.2)
          (Measure.map (fun z : A × iota => z) ((Measure.map W mu).prod nu)) :=
      aestronglyMeasurable_map_of_measurable_on_ae_support
        (P := (Measure.map W mu).prod nu)
        (wt := fun z : A × iota => z) (A := support)
        (φ := fun z : A × iota => F z.1 z.2)
        hsupport_meas
        (by exact StronglyMeasurable.of_discrete)
        (by simpa using hprod_support)
    simpa [Measure.map_id'] using htmp
  rw [MeasureTheory.integrable_prod_iff hF_aestrong]
  constructor
  · exact Filter.Eventually.of_forall (fun a => by
      have hfiber_aestrong :
          AEStronglyMeasurable (fun i : iota => F a i) nu := by
        exact AEStronglyMeasurable.of_discrete
      exact integrable_of_finite_range hfiber_aestrong
        (Set.finite_range (fun i : iota => F a i)))
  · exact
      integrable_map_of_finite_range W hW hfin
        (fun a : A => ∫ i : iota, ‖F a i‖ ∂nu)


-- Batch 6 promoted from Staging/integral_prod_finite_law_eq_integral_weighted_fiber_sum.lean
noncomputable section

open MeasureTheory
open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: finite-law product integral expansion to an outer integral of
--   weighted fiber sums; orig was
--   `integral_prod_componentSampleLaw_eq_componentConditionalExpectation`,
--   renamed away from component/sample/setup-local conditional-expectation
--   language.
-- generality used: arbitrary base measurable type `A`, finite measurable index
--   type `iota` with measurable singletons, sigma-finite base measure `base`,
--   finite index law `nu`, singleton real masses `w`, and Bochner-valued
--   observable `F`; no optimization objective, convexity, smoothness, inner
--   product, filtration, probability normalization, or finite-dimensional
--   assumptions are used.
-- portable call pattern: finite-sample stochastic proofs call this after
--   identifying a fresh finite index law and before replacing a product
--   integral by the history-conditioned finite weighted expectation; the base
--   measure, index law, weights, and observable change while the conclusion
--   shape stays the same.
-- counterargument checked: this is not only paper traceability because it
--   isolates a recurring Fubini-plus-finite-law expansion used by adaptive
--   stochastic algorithms. It is not a full duplicate of existing SOptLib
--   entries: `integral_selected_finite_index_prod_eq_sum_weights` and
--   `SOptLib.integral_finite_index_first_prod_eq_sum_weights` move the outer
--   integral through the finite sum to produce a sum of fiber integrals, while
--   this theorem keeps the weighted fiber sum inside the base integral. A
--   separate weighted-fiber-sum definition was rejected because the standard
--   `Finset.univ.sum` expression is already clear and no named Mathlib object
--   is missing.
-- coverage search: searched CATALOG/SOptLib/Staging/Algorithms for
--   `integral_prod`, `finite index`, `weighted_fiber`, `fiber_sum`,
--   `componentConditionalExpectation`, and `Measure.prod`. Relevant partial
--   hits were `integral_selected_finite_index_prod_eq_sum_weights`,
--   `SOptLib.integral_finite_index_first_prod_eq_sum_weights`,
--   `expectation_sample_eq_expectation_weighted_fiber_sum_of_joint_law`, and
--   `expectation_sample_eq_expectation_weighted_fiber_sum_of_indepFun`.
--   LeanSearch returned Mathlib finite product integral lemmas, not this
--   singleton-mass weighted fiber expansion.
-- minimal hypotheses: `SFinite base` supports product Fubini, `IsFiniteMeasure
--   nu` supports `integral_fintype`, and the only law-specific hypothesis is
--   the pointwise singleton real-mass identity; positivity and total mass one
--   are unnecessary.

/-- A product integral over a finite index law equals the integral of the
corresponding weighted fiber sum.

For a sigma-finite base measure and a finite index law whose singleton real
masses are `w`, integrating `F a i` over `base.prod nu` is the same as first
forming the finite weighted sum over the index fiber and then integrating over
the base.

Layer: Glue | Gap: Level 1 (finite-law product integral fiber expansion)
Proof: apply product-measure Fubini, rewrite each finite index integral by
  `integral_fintype`, and substitute the singleton real-mass weights.
Source: Mathlib product-measure Bochner integration and finite-type integral
  APIs
Used in: variance-reduced accelerated gradient descent replacement of a fresh
  component-law product integral by a history-conditioned finite weighted
  expectation
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem integral_prod_finite_law_eq_integral_weighted_fiber_sum
    {A iota E : Type*} [MeasurableSpace A] [MeasurableSpace iota]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [Fintype iota] [MeasurableSingletonClass iota]
    (base : Measure A) (nu : Measure iota) [SFinite base] [IsFiniteMeasure nu]
    (w : iota -> ℝ) (F : A -> iota -> E)
    (hnu_singleton : forall i : iota, nu.real ({i} : Set iota) = w i)
    (hF_int : Integrable (fun z : A × iota => F z.1 z.2) (base.prod nu)) :
    (∫ z : A × iota, F z.1 z.2 ∂(base.prod nu)) =
      ∫ a : A, Finset.univ.sum (fun i : iota => w i • F a i) ∂base := by
  classical
  have hinner : forall a : A,
      (∫ i : iota, F a i ∂nu) =
        Finset.univ.sum (fun i : iota => w i • F a i) := by
    intro a
    rw [MeasureTheory.integral_fintype .of_finite]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [hnu_singleton i]
  calc
    (∫ z : A × iota, F z.1 z.2 ∂(base.prod nu)) =
        ∫ a : A, ∫ i : iota, F a i ∂nu ∂base := by
          exact MeasureTheory.integral_prod
            (fun z : A × iota => F z.1 z.2) hF_int
    _ = ∫ a : A, Finset.univ.sum (fun i : iota => w i • F a i) ∂base := by
          exact MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall hinner)
-- Batch 6 promoted from Staging/integral_sample_le_integral_bound_of_indep_weighted_fiber_bound.lean
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: independent finite-sample integral comparison from a
--   weighted fiber bound, renamed away from theorem-number, epoch, and
--   printed-algorithm vocabulary.
-- generality used: arbitrary measurable source space `Omega`, history state
--   type `A`, finite measurable sample type `iota` with measurable singletons,
--   finite source measure `P`, finite sample law `nu`, singleton real weights
--   `w`, scalar sampled observable, and scalar upper bound; no convexity,
--   smoothness, normed vector space, inner product, filtration, or finite
--   dimension is used.
-- portable call pattern: stochastic algorithms with a history-dependent state
--   and a fresh finite sample call this after proving independence and a
--   conditional weighted-fiber bound a.e.; the state, sample law, weights,
--   sampled observable, and upper bound change while the unconditional
--   integral comparison conclusion stays the same.
-- counterargument checked: not paper-local traceability because this packages
--   a recurring transport from conditional finite sampling bounds to
--   unconditional integral inequalities. It is not a pure wrapper over Mathlib: Mathlib
--   has product/Fubini/integral-mono primitives but not this combined
--   independent finite-weighted sampled comparison. No separate weighted-fiber
--   definition is introduced because the standard `Finset.univ.sum` expression
--   is clear and no recognized named formula is missing.
-- coverage search: searched SOptLib and staging for `integral_comp_le`,
--   `weighted_fiber`, `joint_law`, `unconditional`, and
--   `expectation_sample_eq_expectation_weighted_fiber_sum_of_joint_law`; the
--   closest hits are `integral_comp_le_of_indep_fixed_integral_bound`, which
--   only bounds by a constant, and
--   `expectation_sample_eq_expectation_weighted_fiber_sum_of_joint_law`, which
--   assumes the product joint law and proves equality, not the independence
--   plus a.e.-bound inequality. LeanSearch returned Mathlib independence
--   integration lemmas, none with this weighted finite-fiber comparison shape.
-- minimal hypotheses: algorithm-specific sample paths, component laws, and
--   conditional expectation notation are replaced by `W`, `Y`, `nu`, and `w`;
--   the only explicit integrability assumptions are the product sampled
--   observable, the weighted-fiber bound function, and the right-hand side
--   needed by Fubini and `integral_mono_ae`.

/-- Transport an a.e. weighted finite-fiber bound through an independent finite
sample to an unconditional integral inequality.

If `Y` is independent of a history state `W`, has law `nu`, and the singleton
real masses of `nu` are the weights `w`, then an a.e. bound on the weighted
fiber sum of an observable `F (W omega)` gives the corresponding sampled
integral bound for `F (W omega) (Y omega)`.

Layer: Glue | Gap: Level 1 (independent finite-sample integral transport)
Proof: identify the joint law of `(W, Y)` by independence and the marginal law,
  use finite weighted-fiber integral transport, then apply `integral_mono_ae`
  to the supplied a.e. bound.
Source: Mathlib probability independence, product-measure integration, finite
  integral expansion, and ordered Bochner integral APIs
Typical use: convert a history-conditional finite-sampling bound into an
  unconditional integral comparison. -/
theorem integral_sample_le_integral_bound_of_indep_weighted_fiber_bound
    {Omega A iota : Type*} [MeasurableSpace Omega] [MeasurableSpace A]
    [MeasurableSpace iota] [Fintype iota] [MeasurableSingletonClass iota]
    {P : Measure Omega} [IsFiniteMeasure P]
    {W : Omega -> A} {Y : Omega -> iota}
    (nu : Measure iota) (w : iota -> Real)
    (F : A -> iota -> Real) (bound : Omega -> Real)
    (hW : AEMeasurable W P) (hY : AEMeasurable Y P)
    (hindep : IndepFun W Y P)
    (hmarg : Measure.map Y P = nu)
    (hnu_singleton : forall i : iota, nu.real ({i} : Set iota) = w i)
    (hF_int :
      Integrable (fun z : A × iota => F z.1 z.2)
        ((Measure.map W P).prod nu))
    (hweighted_aestrong :
      AEStronglyMeasurable
        (fun a : A => Finset.univ.sum (fun i : iota => w i • F a i))
        (Measure.map W P))
    (hweighted_int :
      Integrable
        (fun omega : Omega =>
          Finset.univ.sum (fun i : iota => w i • F (W omega) i)) P)
    (hbound_int : Integrable bound P)
    (hpoint :
      ∀ᵐ omega ∂P,
        Finset.univ.sum (fun i : iota => w i • F (W omega) i) <=
          bound omega) :
    (∫ omega : Omega, F (W omega) (Y omega) ∂P) <=
      ∫ omega : Omega, bound omega ∂P := by
  classical
  haveI : IsFiniteMeasure nu := by
    rw [← hmarg]
    exact Measure.isFiniteMeasure_map P Y
  have hjoint :
      Measure.map (fun omega : Omega => (W omega, Y omega)) P =
        (Measure.map W P).prod nu := by
    have hprod :=
      map_pair_eq_prod_map_of_indepFun_of_map_eq
        (P := P) (pref := W) (blockOff := Y) (block0 := Y)
        hW hY hindep rfl
    simpa [hmarg] using hprod
  have htransport :
      (∫ omega : Omega, F (W omega) (Y omega) ∂P) =
        ∫ omega : Omega,
          Finset.univ.sum (fun i : iota => w i • F (W omega) i) ∂P := by
    let Z : Omega -> A × iota := fun omega => (W omega, Y omega)
    have hZ_aemeas : AEMeasurable Z P := hW.prodMk hY
    have hF_aestrong :
        AEStronglyMeasurable (fun z : A × iota => F z.1 z.2)
          (Measure.map Z P) := by
      rw [hjoint]
      exact hF_int.aestronglyMeasurable
    have hprod_expand :
        (∫ z : A × iota, F z.1 z.2 ∂((Measure.map W P).prod nu)) =
          ∫ a : A, Finset.univ.sum (fun i : iota => w i • F a i)
            ∂Measure.map W P := by
      have hinner : forall a : A,
          (∫ i : iota, F a i ∂nu) =
            Finset.univ.sum (fun i : iota => w i • F a i) := by
        intro a
        rw [MeasureTheory.integral_fintype .of_finite]
        refine Finset.sum_congr rfl ?_
        intro i _hi
        rw [hnu_singleton i]
      calc
        (∫ z : A × iota, F z.1 z.2 ∂((Measure.map W P).prod nu)) =
            ∫ a : A, ∫ i : iota, F a i ∂nu ∂Measure.map W P := by
              exact MeasureTheory.integral_prod
                (fun z : A × iota => F z.1 z.2) hF_int
      _ = ∫ a : A, Finset.univ.sum (fun i : iota => w i • F a i)
            ∂Measure.map W P := by
              exact MeasureTheory.integral_congr_ae
                (Filter.Eventually.of_forall hinner)
    calc
      (∫ omega : Omega, F (W omega) (Y omega) ∂P) =
          ∫ z : A × iota, F z.1 z.2 ∂((Measure.map W P).prod nu) := by
            simpa [Z] using
              integral_comp_eq_integral_of_map_eq hZ_aemeas hF_aestrong hjoint
      _ = ∫ a : A, Finset.univ.sum (fun i : iota => w i • F a i)
            ∂Measure.map W P :=
            hprod_expand
      _ = ∫ omega : Omega,
            Finset.univ.sum (fun i : iota => w i • F (W omega) i) ∂P := by
            exact MeasureTheory.integral_map hW hweighted_aestrong
  calc
    (∫ omega : Omega, F (W omega) (Y omega) ∂P)
        = ∫ omega : Omega,
          Finset.univ.sum (fun i : iota => w i • F (W omega) i) ∂P :=
          htransport
    _ <= ∫ omega : Omega, bound omega ∂P :=
          integral_mono_ae hweighted_int hbound_int hpoint

-- Batch 6 promoted from Staging/expectation_add_const_mul_eq.lean
open MeasureTheory

-- Generalization plan (G0):
-- concept/name: linearity of `SOptLib.expectation` for a deterministic two-term scalar combination; orig was `expectation_add_const_mul_eq` and remains paper-free
-- generality used: arbitrary measurable sample space, arbitrary measure, real coefficients, and integrable random variables valued in any real normed vector space; no probability, independence, convexity, smoothness, or oracle assumptions
-- portable call pattern: expectation-level Lyapunov and potential recurrences split deterministic scalar coefficients from integrable potential terms; coefficients and random potentials change while the linearity conclusion stays the same
-- counterargument checked: this is a short wrapper over Mathlib integral linearity, but future SOptLib proofs are written in terms of the named `SOptLib.expectation`; the wrapper avoids caller-side unfolding and is not paper traceability
-- coverage search: searched `expectation_add_const_mul_eq`, expectation/const/mul/add in SOptLib catalog/project, and LeanSearch for Lebesgue integral scalar linear combination; Mathlib has `MeasureTheory.integral_add` and `MeasureTheory.integral_smul`, SOptLib has no expectation-level equality covering this shape
-- minimal hypotheses: integrability of the two input random variables is exactly what `MeasureTheory.integral_add` needs after scalar multiplication

/-- Split the expectation of a deterministic two-term scalar combination.

For integrable random variables valued in a real normed vector space,
expectation distributes across addition and deterministic real scalar
multiplication in the two-term affine-algebra form commonly used in Lyapunov
recurrences.

Layer: Glue | Gap: Level 0 (expectation linearity wrapper)
Proof: unfold `SOptLib.expectation`, apply Mathlib linearity of the Bochner
  integral for addition and deterministic scalar multiplication.
Source: Mathlib measure theory Bochner integral linearity API
Used in: variance-reduced accelerated gradient Lyapunov expectation splitting
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem expectation_add_const_mul_eq
    {Ω : Type*} [MeasurableSpace Ω]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (a c : ℝ) (F G : Ω → E)
    (hF : Integrable F μ)
    (hG : Integrable G μ) :
    (∫ omega, a • F omega + c • G omega ∂μ) =
      a • (∫ omega, F omega ∂μ) + c • (∫ omega, G omega ∂μ) := by
  rw [integral_add
    (f := fun omega => a • F omega)
    (g := fun omega => c • G omega)
    (by simpa only [Pi.smul_apply] using hF.smul a)
    (by simpa only [Pi.smul_apply] using hG.smul c)]
  simp [integral_smul]

-- Batch 6 promoted from Staging/expectation_le_sum_expectation_of_ae_le_finset_sum.lean
open MeasureTheory
open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: expectation monotonicity through an a.e. finite-sum upper
--   bound; orig was `expectation_le_finset_sum_of_pointwise_le`, renamed to
--   expose the pointwise-to-expectation finite-sum lift.
-- generality used: arbitrary measurable sample space, arbitrary measure,
--   arbitrary finite index type, and ordered real normed-space valued
--   integrable summands; no probability, independence, convexity, smoothness,
--   oracle, finite-dimensional, or completeness assumptions are used.
-- portable call pattern: stochastic descent and Lyapunov proofs instantiate
--   `F` as the target potential and `G` as finitely many budget terms after an
--   a.e. pathwise bound; the potential, budgets, finite index set, and measure
--   change while the expectation inequality stays the same.
-- counterargument checked: this is a short composition of Mathlib integral
--   monotonicity and finite-sum linearity, but it is not merely paper-local
--   traceability and avoids repeated caller-side unfolding of `SOptLib.expectation`.
-- coverage search: searched CATALOG.md/SOptLib/Staging/algorithm sources for
--   `expectation_le`, `finset_sum`, `sum_expectation`, and `ae finset sum
--   integral`; the closest hit is
--   `SOptLib.integral_finset_sum_le_of_pointwise_finset_sum_le`, which handles
--   a scaled finite-sum affine inequality under a probability measure, not a
--   single observable bounded by a finite sum under an arbitrary measure.
--   Mathlib provides `MeasureTheory.integral_mono_ae` and
--   `MeasureTheory.integral_finset_sum`, but no expectation-level theorem with
--   this finite-sum majorant shape.
-- minimal hypotheses: all already minimal at Mathlib's ordered Bochner target
--   generality; the proof needs integrability of `F`, integrability of each
--   active summand `G i`, and the a.e. pointwise inequality so that integral
--   monotonicity and finite-sum integral linearity apply.

/-- An a.e. finite-sum upper bound lifts to an expectation upper bound.

If an integrable random variable valued in an ordered real normed space is
a.e. bounded by a finite sum of integrable random variables, then its
`SOptLib.expectation` is bounded by the finite sum of the corresponding
expectations.

Layer: Glue | Gap: Level 0 (finite-sum expectation monotonicity)
Proof: apply Bochner integral monotonicity to the a.e. bound, then commute the
  Bochner integral through the finite sum and fold back `SOptLib.expectation`.
Source: Mathlib Bochner integral monotonicity and finite-sum linearity APIs
Used in: variance-reduced accelerated-gradient Jensen normalization, where a
  pathwise average-potential bound is converted into a sum of expected budgets
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem expectation_le_sum_expectation_of_ae_le_finset_sum
    {Omega I E : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
    [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [ClosedIciTopology E]
    (s : Finset I) (F : Omega -> E) (G : I -> Omega -> E)
    (hF : Integrable F mu)
    (hG : ∀ i, i ∈ s -> Integrable (G i) mu)
    (hpoint : ∀ᵐ omega ∂mu, F omega <= s.sum fun i => G i omega) :
    (∫ omega, F omega ∂mu) <=
      s.sum fun i => ∫ omega, G i omega ∂mu := by
  have hsum_int :
      Integrable (fun omega : Omega => s.sum fun i => G i omega) mu := by
    exact MeasureTheory.integrable_finset_sum s hG
  have hmono :
      (∫ omega, F omega ∂mu) <=
        ∫ omega, (s.sum fun i => G i omega) ∂mu := by
    exact MeasureTheory.integral_mono_ae hF hsum_int hpoint
  rw [MeasureTheory.integral_finset_sum] at hmono
  · simpa using hmono
  · exact hG

-- Batch 6 promoted from Staging/expectation_finset_sum_const_mul_comp_eq_of_finite_range_key.lean
open MeasureTheory
open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: finite-sum expectation linearity for vector observables composed
--   with a finite-range key; orig was
--   `expectation_add_const_mul_comp_eq_of_finite_range_key`, renamed from the
--   two-term local shape to the reusable finite-index const-smul statement.
-- generality used: arbitrary measurable source and key spaces, measurable
--   singletons on the key space, finite base measure, a.e. measurable
--   finite-range key, arbitrary finite index set, real coefficients, and real
--   normed-vector observables; no probability, independence, convexity,
--   smoothness, or oracle assumptions are used.
-- portable call pattern: generated-history Lyapunov recurrences instantiate a
--   finite state key `W` and finitely many scalar observables on that key; the
--   key, index set, coefficients, and observables change while the expectation
--   split conclusion stays the same.
-- counterargument checked: Mathlib supplies Bochner integral finite-sum
--   linearity and scalar multiplication, and existing SOptLib/Staging entries
--   supply two-term expectation linearity and finite-range map integrability,
--   but no declaration combines finite-key automatic integrability with a
--   finite-index coefficient-weighted expectation split.
-- coverage search: searched catalog/project for `expectation finite sum const
--   mul finite range key`, `integral_finset_sum`, `integrable map finite
--   range`, and LeanSearch for Bochner integral finite sum scalar
--   multiplication; closest hits were `MeasureTheory.integral_finset_sum`,
--   `MeasureTheory.integral_const_mul`, staged
--   `expectation_add_const_mul_eq`, and staged
--   `integrable_map_of_finite_range`, all partial rather than this statement.
-- minimal hypotheses: finite measure is needed for finite-range integrability;
--   measurable singletons and a.e. measurability are needed for the pushforward
--   finite-support step; the observable functions need no separate
--   measurability or integrability hypotheses.

/-- Split the expectation of a finite const-smul-weighted sum through a finite key.

If an a.e. measurable key has finite range under a finite measure, then every
normed-vector observable on the key is integrable after composition.
Consequently, the expectation of a finite sum of deterministic
const-smul-weighted composed observables is the finite sum of the corresponding
const-smul-weighted
expectations.

Layer: Glue | Gap: Level 1 (finite-key finite-sum expectation linearity)
Proof: prove each composed scalar observable integrable using finite-range
  pushforward-law integrability, then commute the Bochner integral through the
  finite sum and through deterministic scalar multiplication.
Source: Mathlib Bochner integral finite-sum and scalar-linearity APIs, plus
  finite-range pushforward-law integrability
Used in: variance-reduced accelerated-gradient generated-history Lyapunov
  recurrence splitting before scalar telescoping
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem expectation_finset_sum_const_smul_comp_eq_of_finite_range_key
    {Ω A I E : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSingletonClass A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (W : Ω → A) (hW : AEMeasurable W μ)
    (hWfin : (Set.range W).Finite)
    (idxs : Finset I) (coeff : I → ℝ) (F : I → A → E) :
    (∫ omega, idxs.sum (fun i => coeff i • F i (W omega)) ∂μ) =
      idxs.sum fun i => coeff i • (∫ omega, F i (W omega) ∂μ) := by
  classical
  have hcomp_int :
      ∀ i, i ∈ idxs → Integrable (fun omega => F i (W omega)) μ := by
    intro i _hi
    have hFmap : Integrable (F i) (Measure.map W μ) :=
      integrable_map_of_finite_range W hW hWfin (F i)
    exact (integrable_map_measure hFmap.aestronglyMeasurable hW).1 hFmap
  have hterm_int :
      ∀ i, i ∈ idxs →
        Integrable (fun omega => coeff i • F i (W omega)) μ := by
    intro i hi
    exact (hcomp_int i hi).smul (coeff i)
  calc
    (∫ omega, idxs.sum (fun i => coeff i • F i (W omega)) ∂μ) =
        idxs.sum (fun i => ∫ omega, coeff i • F i (W omega) ∂μ) := by
      exact MeasureTheory.integral_finset_sum idxs hterm_int
    _ = idxs.sum (fun i => coeff i • ∫ omega, F i (W omega) ∂μ) := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      exact MeasureTheory.integral_smul (coeff i)
        (fun omega => F i (W omega))

-- Batch 6 promoted from Staging/expectation_sample_eq_expectation_weighted_fiber_sum_of_joint_law.lean
noncomputable section

open MeasureTheory
open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: product-joint-law transport from a sampled finite index to a
--   weighted fiber expectation; orig was
--   `adaptive_componentConditionalExpectation_transport_of_joint_law`, renamed
--   away from adaptive/component/setup-local conditional-expectation language.
-- generality used: arbitrary source type `Omega`, history key type `A`, finite
--   index type `iota` with measurable singletons, source measure `P`, finite
--   index law `nu`, singleton real weights `w`, and scalar observable `F`; no
--   optimization objective, convexity, smoothness, norm, inner product,
--   filtration, or finite-dimensional assumptions are used.
-- portable call pattern: adaptive stochastic algorithms call this after a
--   freshness or independence argument identifies the joint law of a history
--   key and a fresh finite sample as `(map W P).prod nu`; the history key,
--   sample law, weights, and observable change while the sampled-expectation
--   to weighted-fiber-expectation conclusion stays the same.
-- counterargument checked: this is not paper-local traceability because it
--   packages a recurring conditional-on-history finite sampling transport. It
--   is not a pure wrapper around `integral_selected_finite_index_prod_eq_sum_weights`,
--   since the caller starts from a base-space sampled expectation and an
--   already-proved joint-law equality, not directly from a product integral.
--   A separate weighted-fiber-sum definition was considered but rejected:
--   `Finset.univ.sum (fun i => w i • F a i)` is already the standard finite
--   weighted-sum expression and no recognized Mathlib gap requires a new def.
-- coverage search: searched CATALOG/SOptLib/Staging/Algorithms for
--   `componentConditionalExpectation`, `weighted_fiber`, `joint_law`,
--   `integral_selected_finite_index_prod_eq_sum_weights`, and finite
--   product-measure sum expansions. Relevant partial hits were
--   `integral_selected_finite_index_prod_eq_sum_weights`,
--   `SOptLib.integral_finite_index_first_prod_eq_sum_weights`,
--   `integral_prefix_fresh_block_eq_generated_of_joint_law`, and
--   `SOptLib.integral_comp_indep_finite_uniform_eq_integral_inv_card_sum`;
--   none combines arbitrary singleton weights, a supplied joint-law equality,
--   and base-space expectation transport. LeanSearch returned Mathlib
--   finite-product integral lemmas, not this transport statement.
-- minimal hypotheses: the algorithm-specific sample map is replaced by an
--   arbitrary a.e.-measurable `Y`; the observable is vector-valued because the
--   proof only uses Bochner integration and real scalar weights; positivity
--   and normalization of weights are unnecessary because the proof uses only
--   singleton real masses `nu.real {i} = w i`; finite-dimensional assumptions
--   are absent.

/-- A sampled finite-index expectation transports to a weighted fiber sum under
a product joint law.

If the joint law of a history key `W` and a fresh finite sample `Y` is
`(map W P).prod nu`, then the expectation of `F (W omega) (Y omega)` equals the
expectation of the finite weighted fiber sum using the singleton real masses of
`nu`.

Layer: Glue | Gap: Level 1 (finite-index joint-law expectation transport)
Proof: map the base-space sampled integral to the joint law, rewrite to the
  product measure, expand the finite second-coordinate integral by singleton
  real masses, and map the weighted fiber sum back along `W`.
Source: Mathlib product-measure Bochner integration, finite-type integral, and
  pushforward integral APIs
Used in: variance-reduced accelerated gradient descent replacement of a fresh
  component sample by the conditional finite weighted expectation given the
  current history
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem expectation_sample_eq_expectation_weighted_fiber_sum_of_joint_law
    {Omega A iota E : Type*} [MeasurableSpace Omega] [MeasurableSpace A]
    [MeasurableSpace iota] [Fintype iota] [MeasurableSingletonClass iota]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Measure Omega} [SFinite P]
    {W : Omega -> A} {Y : Omega -> iota}
    (nu : Measure iota) [IsFiniteMeasure nu]
    (w : iota -> Real) (F : A -> iota -> E)
    (hW : AEMeasurable W P) (hY : AEMeasurable Y P)
    (hjoint :
      Measure.map (fun omega : Omega => (W omega, Y omega)) P =
        (Measure.map W P).prod nu)
    (hnu_singleton : forall i : iota, nu.real ({i} : Set iota) = w i)
    (hF_int :
      Integrable (fun z : A × iota => F z.1 z.2) ((Measure.map W P).prod nu))
    (hsum_aestrong :
      AEStronglyMeasurable
        (fun a : A => Finset.univ.sum (fun i : iota => w i • F a i))
        (Measure.map W P)) :
    (∫ omega : Omega, F (W omega) (Y omega) ∂P) =
      ∫ omega : Omega, Finset.univ.sum (fun i : iota => w i • F (W omega) i) ∂P := by
  classical
  by_cases hE : CompleteSpace E
  · letI : CompleteSpace E := hE
    let Z : Omega -> A × iota := fun omega => (W omega, Y omega)
    have hZ_aemeas : AEMeasurable Z P := hW.prodMk hY
    have hF_aestrong :
        AEStronglyMeasurable (fun z : A × iota => F z.1 z.2) (Measure.map Z P) := by
      rw [hjoint]
      exact hF_int.aestronglyMeasurable
    have hprod_expand :
        (∫ z : A × iota, F z.1 z.2 ∂((Measure.map W P).prod nu)) =
          ∫ a : A, Finset.univ.sum (fun i : iota => w i • F a i) ∂Measure.map W P := by
      have hinner : forall a : A,
          (∫ i : iota, F a i ∂nu) =
            Finset.univ.sum (fun i : iota => w i • F a i) := by
        intro a
        rw [MeasureTheory.integral_fintype .of_finite]
        refine Finset.sum_congr rfl ?_
        intro i _hi
        rw [hnu_singleton i]
      calc
        (∫ z : A × iota, F z.1 z.2 ∂((Measure.map W P).prod nu)) =
            ∫ a : A, ∫ i : iota, F a i ∂nu ∂Measure.map W P := by
              exact MeasureTheory.integral_prod
                (fun z : A × iota => F z.1 z.2) hF_int
      _ = ∫ a : A, Finset.univ.sum (fun i : iota => w i • F a i) ∂Measure.map W P := by
              exact MeasureTheory.integral_congr_ae
                (Filter.Eventually.of_forall hinner)
    calc
      (∫ omega : Omega, F (W omega) (Y omega) ∂P) =
          ∫ z : A × iota, F z.1 z.2 ∂((Measure.map W P).prod nu) := by
              simpa [Z] using
                integral_comp_eq_integral_of_map_eq hZ_aemeas hF_aestrong hjoint
      _ = ∫ a : A, Finset.univ.sum (fun i : iota => w i • F a i) ∂Measure.map W P :=
              hprod_expand
      _ = ∫ omega : Omega, Finset.univ.sum (fun i : iota => w i • F (W omega) i) ∂P := by
              exact MeasureTheory.integral_map hW hsum_aestrong
  · simp [MeasureTheory.integral, hE]

-- Batch 6 promoted from Staging/expectation_sample_eq_expectation_weighted_fiber_sum_of_indepFun.lean
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: independent finite-index expectation transport to a weighted
--   fiber expectation; orig was
--   `adaptive_componentConditionalExpectation_transport_of_indepFun`, renamed
--   away from adaptive/component/setup-local conditional-expectation language.
-- generality used: arbitrary source type `Omega`, history key type `A`, finite
--   index type `iota` with measurable singletons, finite source measure `P`,
--   finite index law `nu`, singleton real weights `w`, and vector-valued
--   observable `F`; no optimization objective, convexity, smoothness, norm
--   bound, filtration, or finite-dimensional assumption is used.
-- portable call pattern: stochastic finite-memory proofs call this after
--   proving a generated history key is independent of a fresh finite sample
--   with known marginal law; the history key, sample law, weights, observable,
--   and sample map change while the sampled-expectation to weighted-fiber
--   expectation conclusion stays the same.
-- counterargument checked: this is more than paper traceability because it
--   packages the recurring `IndepFun` plus marginal-law-to-product-law step
--   with the finite weighted fiber expectation transport. It is not a Mathlib
--   duplicate: Mathlib exposes the product-law characterization of
--   independence but not the subsequent finite singleton-mass weighted
--   expectation expansion. It is a deliberate theorem composition, not a new
--   formula def; `Finset.univ.sum` is the standard finite weighted-fiber
--   expression and no recognized named formula is missing.
-- coverage search: searched CATALOG/SOptLib/Staging/Algorithms for
--   `weighted_fiber`, `componentConditionalExpectation`, `joint_law`,
--   `indepFun`, and `map_pair_eq_prod_map_of_indepFun_of_map_eq`; relevant
--   partial hits were `map_pair_eq_prod_map_of_indepFun_of_map_eq`,
--   `expectation_sample_eq_expectation_weighted_fiber_sum_of_joint_law`, and
--   `integral_sample_le_integral_bound_of_indep_weighted_fiber_bound`.
--   LeanSearch returned Mathlib `IndepFun` product-law and independent-product
--   integration lemmas; none combines independence, a replacement marginal,
--   singleton real masses, and weighted finite-fiber expectation transport.
-- minimal hypotheses: algorithm-specific sample paths and component laws are
--   replaced by `W`, `Y`, `nu`, and `w`; finite source measure is used only to
--   obtain the product joint law, while positivity and normalization of
--   weights are unnecessary because the proof needs only
--   `nu.real {i} = w i`.

/-- A sampled finite-index expectation transports to a weighted fiber sum under
independence and a fixed marginal law.

If a history key `W` is independent of a finite sample `Y`, `Y` has law `nu`,
and the singleton real masses of `nu` are `w`, then the Bochner integral of
`F (W omega) (Y omega)` equals the integral of the corresponding finite
weighted fiber sum.

Layer: Glue | Gap: Level 1 (independent finite-index expectation transport)
Proof: identify the joint law by `IndepFun` and the marginal law, then apply
  the product-joint-law weighted finite-fiber expectation transport.
Source: Mathlib probability independence, product-measure pushforward, finite
  integral expansion, and Bochner integration APIs
Used in: variance-reduced accelerated gradient descent replacement of a fresh
  component sample by the history-conditioned finite weighted expectation
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem expectation_sample_eq_expectation_weighted_fiber_sum_of_indepFun
    {Omega A iota E : Type*} [MeasurableSpace Omega] [MeasurableSpace A]
    [MeasurableSpace iota] [Fintype iota] [MeasurableSingletonClass iota]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Measure Omega} [IsFiniteMeasure P]
    {W : Omega -> A} {Y : Omega -> iota}
    (nu : Measure iota) (w : iota -> Real) (F : A -> iota -> E)
    (hW : AEMeasurable W P) (hY : AEMeasurable Y P)
    (hindep : IndepFun W Y P)
    (hmarg : Measure.map Y P = nu)
    (hnu_singleton : forall i : iota, nu.real ({i} : Set iota) = w i)
    (hF_int :
      Integrable (fun z : A × iota => F z.1 z.2) ((Measure.map W P).prod nu)) :
    (∫ omega : Omega, F (W omega) (Y omega) ∂P) =
      ∫ omega : Omega, Finset.univ.sum (fun i : iota => w i • F (W omega) i) ∂P := by
  classical
  haveI : IsFiniteMeasure nu := by
    rw [← hmarg]
    exact Measure.isFiniteMeasure_map P Y
  by_cases hE : CompleteSpace E
  · letI : CompleteSpace E := hE
    let Z : Omega -> A × iota := fun omega => (W omega, Y omega)
    have hZ_aemeas : AEMeasurable Z P := hW.prodMk hY
    have hjoint :
        Measure.map Z P = (Measure.map W P).prod nu := by
      have hprod :=
        map_pair_eq_prod_map_of_indepFun_of_map_eq
          (P := P) (pref := W) (blockOff := Y) (block0 := Y)
          hW hY hindep rfl
      simpa [Z, hmarg] using hprod
    have hF_aestrong :
        AEStronglyMeasurable (fun z : A × iota => F z.1 z.2) (Measure.map Z P) := by
      rw [hjoint]
      exact hF_int.aestronglyMeasurable
    have hfiber_int :
        Integrable (fun a : A => ∫ i : iota, F a i ∂nu) (Measure.map W P) :=
      hF_int.integral_prod_left
    have hinner : forall a : A,
        (∫ i : iota, F a i ∂nu) =
          Finset.univ.sum (fun i : iota => w i • F a i) := by
      intro a
      rw [MeasureTheory.integral_fintype .of_finite]
      refine Finset.sum_congr rfl ?_
      intro i _hi
      rw [hnu_singleton i]
    have hsum_aestrong :
        AEStronglyMeasurable
          (fun a : A => Finset.univ.sum (fun i : iota => w i • F a i))
          (Measure.map W P) :=
      hfiber_int.aestronglyMeasurable.congr (Filter.Eventually.of_forall hinner)
    have hprod_expand :
        (∫ z : A × iota, F z.1 z.2 ∂((Measure.map W P).prod nu)) =
          ∫ a : A, Finset.univ.sum (fun i : iota => w i • F a i) ∂Measure.map W P := by
      calc
        (∫ z : A × iota, F z.1 z.2 ∂((Measure.map W P).prod nu)) =
            ∫ a : A, ∫ i : iota, F a i ∂nu ∂Measure.map W P := by
              exact MeasureTheory.integral_prod
                (fun z : A × iota => F z.1 z.2) hF_int
      _ = ∫ a : A, Finset.univ.sum (fun i : iota => w i • F a i) ∂Measure.map W P := by
              exact MeasureTheory.integral_congr_ae
                (Filter.Eventually.of_forall hinner)
    calc
      (∫ omega : Omega, F (W omega) (Y omega) ∂P) =
          ∫ z : A × iota, F z.1 z.2 ∂((Measure.map W P).prod nu) := by
            simpa [Z] using
              integral_comp_eq_integral_of_map_eq hZ_aemeas hF_aestrong hjoint
      _ = ∫ a : A, Finset.univ.sum (fun i : iota => w i • F a i) ∂Measure.map W P :=
            hprod_expand
      _ = ∫ omega : Omega, Finset.univ.sum (fun i : iota => w i • F (W omega) i) ∂P := by
            exact MeasureTheory.integral_map hW hsum_aestrong
  · simp [MeasureTheory.integral, hE]


-- Promoted from Staging/integral_eq_of_condExp_ae_eq.lean
open MeasureTheory ProbabilityTheory

-- Generalization plan (G0):
-- concept/name: conditional-expectation integral transfer; orig was condExp_integral_eq_integral_of_ae_eq, renamed to integral_eq_of_condExp_ae_eq.
-- generality used: arbitrary measurable space and real Banach target; arbitrary measure and sub-sigma-algebra with the sigma-finite trim required by conditional expectation.
-- portable call pattern: stochastic algorithm proofs convert an a.e. identity for μ[A | m] into an unconditional integral identity; the measure, filtration sigma-algebra, and random variables change while the conclusion shape stays ∫ A = ∫ B.
-- counterargument checked: not paper-local traceability because it removes a repeated conditional-to-unconditional integration proof; not a pure Mathlib rename because Mathlib provides integral_condExp and integral_congr_ae separately, not their a.e.-target composition.
-- coverage search: searched "condExp integral", "conditional expectation almost everywhere equal implies integrals equal", and "integral of conditional expectation equals integral"; closest hits are MeasureTheory.integral_condExp/setIntegral_condExp and SOptLib.integral_eq_zero_of_condExp_ae_eq_zero, which only covers the zero target.
-- minimal hypotheses: all already minimal for Mathlib condExp integration: hm and SigmaFinite (μ.trim hm), plus Banach-space structure for Bochner conditional expectation.

/-- Integrating an a.e. conditional-expectation identity gives the corresponding
unconditional integral identity.

Layer: Glue | Gap: Level 1 (conditional-expectation integral transfer)
Proof: compose Mathlib's `MeasureTheory.integral_condExp` with
  `integral_congr_ae` for the supplied a.e. identity.
Source: Mathlib conditional expectation and Bochner integral APIs
Used in: randomized primal-dual gradient conditional identity integration
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized primal-dual gradient -/
theorem integral_eq_of_condExp_ae_eq
    {Ω E : Type*} {m0 : MeasurableSpace Ω}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : @Measure Ω m0} {m : MeasurableSpace Ω}
    {A B : Ω → E}
    (hm : m ≤ m0)
    [SigmaFinite (μ.trim hm)]
    (hcond : μ[A | m] =ᵐ[μ] B) :
    ∫ ω, A ω ∂μ = ∫ ω, B ω ∂μ := by
  have htotal : ∫ ω, (μ[A | m]) ω ∂μ = ∫ ω, A ω ∂μ :=
    MeasureTheory.integral_condExp (μ := μ) (m := m) (f := A) hm
  have hcond_int : ∫ ω, (μ[A | m]) ω ∂μ = ∫ ω, B ω ∂μ :=
    integral_congr_ae hcond
  exact htotal.symm.trans hcond_int


-- Promoted from Staging/condExp_mul_eq_const_mul_of_condExp_eq_const.lean
open MeasureTheory ProbabilityTheory

-- Generalization plan (G1):
-- concept/name: conditional-expectation pull-out through a continuous bilinear
--   map after the left factor has constant conditional expectation; orig was
--   condexp_hitIndicator_mul_prefixObservable.
-- generality used: arbitrary real normed vector spaces, arbitrary continuous
--   bilinear map B : F →L[ℝ] E →L[ℝ] G, arbitrary measurable sample space Ω,
--   measure μ, sub-sigma-algebra m, random variables hit and payload, and
--   constant p; no probability-measure or algorithm setup fields are used.
-- portable call pattern: stochastic mirror descent, randomized coordinate
--   descent, and primal-dual proofs first rewrite μ[hit | m] to a hit
--   probability or oracle mean, then apply any continuous bilinear pairing with
--   an adapted payload.
-- counterargument checked: not paper-local traceability because the statement
--   has no setup, block, prefix, iterate, or algorithm vocabulary; not a pure
--   Mathlib rename because Mathlib supplies only the pull-out lemma
--   condExp_bilin_of_aestronglyMeasurable_right and leaves the constant
--   conditional-expectation rewrite to callers.
-- minimal hypotheses: all already minimal for the Mathlib pull-out theorem:
--   m-a.e. strong measurability of payload, integrability of hit and of
--   B hit payload, and the supplied a.e. identity μ[hit | m] = p.

/-- Pull a past-measurable payload through a continuous bilinear conditional
expectation after the left factor has constant conditional expectation.

If `payload` is `m`-measurable a.e. and `μ[hit | m]` is a.e. the constant
`p`, then the conditional expectation of `B hit payload` is `B p payload`.

Layer: Glue | Gap: Level 1 (conditional-expectation pull-out with constant
  left factor)
Proof: apply Mathlib's conditional-expectation pull-out theorem for an
  a.e. strongly measurable right factor, then rewrite the left conditional
  expectation by the supplied a.e. constant identity.
Source: Mathlib conditional expectation pull-out and Bochner integrability APIs
Used in: randomized primal-dual and stochastic mirror-descent conditioning
  steps that multiply a fresh hit or oracle mean by an adapted payload
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized primal-dual gradient -/
theorem condExp_bilin_eq_const_bilin_of_condExp_eq_const
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : @Measure Ω mΩ} {m : MeasurableSpace Ω}
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (B : F →L[ℝ] E →L[ℝ] G)
    {hit : Ω → F} {payload : Ω → E} {p : F}
    (hpayload_aesm : AEStronglyMeasurable[m] payload μ)
    (hbilin_int : Integrable (fun ω : Ω => B (hit ω) (payload ω)) μ)
    (hhit_int : Integrable hit μ)
    (hhit_ce : μ[hit | m] =ᵐ[μ] fun _ : Ω => p) :
    μ[(fun ω : Ω => B (hit ω) (payload ω)) | m] =ᵐ[μ]
      fun ω : Ω => B p (payload ω) := by
  have hpull :
      μ[(fun ω : Ω => B (hit ω) (payload ω)) | m] =ᵐ[μ]
        fun ω : Ω => B (μ[hit | m] ω) (payload ω) := by
    simpa using
      (MeasureTheory.condExp_bilin_of_aestronglyMeasurable_right
        (B := B)
        (μ := μ) (m := m) (f := hit) (g := payload)
        hpayload_aesm hbilin_int hhit_int)
  refine hpull.trans ?_
  filter_upwards [hhit_ce] with ω hω
  rw [hω]


-- Promoted from Staging/condExp_indicator_eq_const_of_indep.lean
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

-- Generalization plan (G0):
-- concept/name: conditional expectation of an independent event indicator as a
--   constant event probability; orig was condexp_hitIndicator_sampledBlock_prefix.
-- generality used: arbitrary measurable sample space Ω, abstract probability
--   measure μ, ambient/past/fresh sigma-algebras mΩ/m/mfresh, an arbitrary
--   fresh-measurable event hit, and a real probability p.
-- portable call pattern: stochastic mirror descent, coordinate SGD, randomized
--   primal-dual, and mini-batch proofs condition on an adapted past sigma-
--   algebra while rewriting the indicator of a fresh sampled coordinate/event
--   to its hit probability; the event, sigma-algebras, and probability change
--   while the conditional-expectation conclusion stays the same.
-- counterargument checked: not paper-local traceability because the statement
--   has no setup, block, prefix, iterate, or algorithm vocabulary; not a pure
--   Mathlib rename because Mathlib condExp_indep_eq gives a constant integral
--   for any fresh-measurable random variable, while this lemma packages the
--   recurring stochastic-optimization event-indicator/probability form.
-- coverage search: searched SOptLib catalog/source for condExp, indicator,
--   independent, probability and LeanSearch for "conditional expectation
--   indicator independent event equals probability constant"; top hits were
--   Mathlib MeasureTheory.condExp_indep_eq and
--   ProbabilityTheory.iIndepSet.condExp_indicator_filtrationOfSet_ae_eq.
--   They are partial: the first is more general but leaves the indicator
--   integral/probability rewrite to callers, and the second is specialized to
--   filtrations generated by independent indexed sets.
-- minimal hypotheses: mfresh ≤ mΩ and m ≤ mΩ are exactly the sub-sigma-algebra
--   hypotheses required by condExp_indep_eq; hhit_fresh supplies strong
--   measurability of the indicator and ambient measurability via mfresh ≤ mΩ;
--   h_indep and hprob_real are the independence and real event-mass facts used.

/-- The conditional expectation of an independent event indicator is its
event probability.

If `hit` is measurable in a fresh sigma-algebra independent of the past
sigma-algebra `m`, then conditioning the real indicator of `hit` on `m` gives
the constant real probability of `hit`.

Layer: Glue | Gap: Level 1 (independent indicator conditional expectation)
Proof: apply Mathlib's `condExp_indep_eq` to the fresh-measurable indicator,
  then rewrite the unconditional integral of the indicator as `μ.real hit`.
Source: Mathlib conditional expectation, indicator integration, and probability
  independence APIs
Used in: stochastic primal-dual and mirror-descent conditioning on a fresh
  sampled coordinate after revealing an adapted prefix sigma-algebra
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem condExp_indicator_eq_const_of_indep
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : @Measure Ω mΩ}
    {m mfresh : MeasurableSpace Ω} {hit : Set Ω} {p : ℝ}
    (hmfresh_le : mfresh ≤ mΩ)
    (hm_le : m ≤ mΩ)
    [SigmaFinite (μ.trim hm_le)]
    (hhit_fresh : @MeasurableSet Ω mfresh hit)
    (h_indep : Indep m mfresh μ)
    (hprob_real : μ.real hit = p) :
    μ[hit.indicator (fun _ : Ω => (1 : ℝ)) | m] =ᵐ[μ] fun _ : Ω => p := by
  classical
  have hhit : @MeasurableSet Ω mΩ hit := hmfresh_le hit hhit_fresh
  have hindicator_sm :
      StronglyMeasurable[mfresh] (hit.indicator (fun _ : Ω => (1 : ℝ))) :=
    stronglyMeasurable_const.indicator hhit_fresh
  have hce :
      μ[hit.indicator (fun _ : Ω => (1 : ℝ)) | m] =ᵐ[μ]
        fun _ : Ω => ∫ ω, hit.indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ := by
    exact MeasureTheory.condExp_indep_eq
      (μ := μ) (m₁ := mfresh) (m₂ := m) (m := mΩ)
      hmfresh_le hm_le hindicator_sm h_indep.symm
  have hintegral :
      (∫ ω, hit.indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ) = μ.real hit := by
    exact integral_indicator_one (μ := μ) (s := hit) hhit
  refine hce.trans ?_
  filter_upwards with ω
  simp [hintegral, hprob_real]


-- Promoted from Staging/condExp_ite_eq_prob_mul_add_one_sub_mul.lean
open MeasureTheory ProbabilityTheory

-- Generalization plan (G1):
-- concept/name: conditional expectation of a two-branch event split as its
--   event-probability affine mixture; orig was
--   condexp_sampledBlock_if_prefix_observable, renamed away from block/prefix
--   paper vocabulary.
-- generality used: arbitrary measurable sample space Ω, abstract finite
--   measure μ, sub-sigma-algebra m, event hit, Banach-valued branch payloads
--   A and B, and a scalar p supplied by the conditional expectation of the
--   event indicator.
-- portable call pattern: coordinate SGD, randomized primal-dual, mirror
--   descent, and mini-batch proofs condition on an adapted past sigma-algebra
--   and replace a fresh two-branch payload by p times the hit branch plus
--   1-p times the miss branch; the event, past sigma-algebra, probability, and
--   branch payloads change while the conclusion keeps this affine-mixture
--   shape.
-- counterargument checked: not paper-local traceability because the statement
--   has no setup, sampled-block, prefix, or iterate names; not a duplicate of
--   the previously staged indicator and indicator-times-payload lemmas because
--   this packages the final two-branch `ite` rewrite and additivity step that
--   callers otherwise repeat.
-- coverage search: searched SOptLib catalog/source and the round registry for
--   condExp, indicator, ite, branch, mixture, and probability; LeanSearch for
--   "conditional expectation of if event then A else B equals probability
--   times A plus one minus probability times B" returned Mathlib
--   MeasureTheory.condExp_add, condExp_indicator_aux, and pull-out lemmas.
--   Those are partial building blocks, not the event-branch affine-mixture
--   statement.
-- minimal hypotheses: B must be a.e. m-measurable so μ[B|m]=B; A-B must be
--   a.e. m-measurable for the pull-out step; integrability of A and B plus
--   finite-measure boundedness make the indicator branch integrable; the only
--   stochastic hypothesis is the supplied event-indicator CE identity.

/-- Conditional expectation of a fresh two-branch event split is the affine
mixture of the two past-measurable branches.

If the real indicator of `hit` has conditional expectation `p` given `m`, and
`A` and `B` are `m`-measurable integrable branch payloads, then conditioning
`if ω ∈ hit then A ω else B ω` on `m` gives
`p • A + (1 - p) • B` a.e.

Layer: Glue | Gap: Level 1 (conditional-expectation event-branch affine mixture)
Proof: rewrite the branch as `B + 1_hit • (A - B)`, use conditional-expectation
  additivity, pull out the past-measurable difference from the indicator
  conditional expectation, and finish with scalar algebra.
Source: Mathlib conditional expectation additivity and pull-out APIs
Used in: randomized coordinate and primal-dual conditioning steps that replace a
  fresh hit/miss branch by its probability-weighted past-measurable payloads
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized primal-dual gradient -/
theorem condExp_ite_eq_prob_smul_add_one_sub_smul
    {Ω E : Type*} [mΩ : MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : @Measure Ω mΩ} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} {hit : Set Ω} {A B : Ω → E} {p : ℝ}
    [DecidablePred (fun ω : Ω => ω ∈ hit)]
    (hm_le : m ≤ mΩ)
    (hhit_meas : @MeasurableSet Ω mΩ hit)
    (hA_aesm : AEStronglyMeasurable[m] A μ)
    (hB_aesm : AEStronglyMeasurable[m] B μ)
    (hA_int : Integrable A μ)
    (hB_int : Integrable B μ)
    (hhit_ce :
      μ[hit.indicator (fun _ : Ω => (1 : ℝ)) | m] =ᵐ[μ] fun _ : Ω => p) :
    μ[(fun ω : Ω => if ω ∈ hit then A ω else B ω) | m] =ᵐ[μ]
      fun ω : Ω => p • A ω + (1 - p) • B ω := by
  classical
  letI : IsFiniteMeasure (μ.trim hm_le) := isFiniteMeasure_trim (μ := μ) hm_le
  let ind : Ω → ℝ := hit.indicator (fun _ : Ω => (1 : ℝ))
  have hB_ce : μ[B | m] =ᵐ[μ] B :=
    MeasureTheory.condExp_of_aestronglyMeasurable' hm_le hB_aesm hB_int
  have hdiff_aesm : AEStronglyMeasurable[m] (fun ω : Ω => A ω - B ω) μ :=
    hA_aesm.sub hB_aesm
  have hdiff_int : Integrable (fun ω : Ω => A ω - B ω) μ :=
    hA_int.sub hB_int
  have hind_aesm : AEStronglyMeasurable[mΩ] ind μ := by
    exact (measurable_const.indicator hhit_meas).aestronglyMeasurable
  have hind_bound : ∀ᵐ ω ∂μ, ‖ind ω‖ ≤ (1 : ℝ) := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    by_cases hω : ω ∈ hit
    · simp [ind, hω]
    · simp [ind, hω]
  have hprod_int : Integrable (fun ω : Ω => ind ω • (A ω - B ω)) μ :=
    hdiff_int.bdd_smul 1 hind_aesm hind_bound
  have hind_int : Integrable ind μ :=
    (integrable_const (1 : ℝ)).indicator hhit_meas
  have hmul_ce :
      μ[(fun ω : Ω => ind ω • (A ω - B ω)) | m] =ᵐ[μ]
        fun ω : Ω => p • (A ω - B ω) := by
    have hpull :
        μ[(fun ω : Ω => ind ω • (A ω - B ω)) | m] =ᵐ[μ]
          fun ω : Ω => μ[ind | m] ω • (A ω - B ω) := by
      simpa [Pi.mul_apply, ind] using
        (MeasureTheory.condExp_smul_of_aestronglyMeasurable_right
          (μ := μ) (m := m) (f := ind)
          (g := fun ω : Ω => A ω - B ω)
          hind_int hprod_int hdiff_aesm)
    refine hpull.trans ?_
    filter_upwards [hhit_ce] with ω hω
    rw [show μ[ind | m] ω = p by simpa [ind] using hω]
  have hadd :
      μ[(fun ω : Ω => B ω + ind ω • (A ω - B ω)) | m] =ᵐ[μ]
        fun ω : Ω =>
          μ[B | m] ω +
            μ[(fun ω : Ω => ind ω • (A ω - B ω)) | m] ω := by
    simpa only [Pi.add_apply] using
      (MeasureTheory.condExp_add
        (μ := μ) (m := m) (f := B)
        (g := fun ω : Ω => ind ω • (A ω - B ω))
        hB_int hprod_int)
  have hbranch :
      (fun ω : Ω => if ω ∈ hit then A ω else B ω) =ᵐ[μ]
        fun ω : Ω => B ω + ind ω • (A ω - B ω) := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    by_cases hω : ω ∈ hit
    · simp [ind, hω]
    · simp [ind, hω]
  calc
    μ[(fun ω : Ω => if ω ∈ hit then A ω else B ω) | m] =ᵐ[μ]
        μ[(fun ω : Ω => B ω + ind ω • (A ω - B ω)) | m] := by
          exact MeasureTheory.condExp_congr_ae hbranch
    _ =ᵐ[μ] (fun ω : Ω =>
        μ[B | m] ω +
          μ[(fun ω : Ω => ind ω • (A ω - B ω)) | m] ω) := hadd
    _ =ᵐ[μ] (fun ω : Ω => B ω + p • (A ω - B ω)) := by
          filter_upwards [hB_ce, hmul_ce] with ω hBω hDω
          rw [hBω, hDω]
    _ =ᵐ[μ] (fun ω : Ω => p • A ω + (1 - p) • B ω) := by
          refine Filter.Eventually.of_forall ?_
          intro ω
          module


-- Promoted from Staging/PMF_sum_toReal_eq_one.lean
-- Generalization plan (G0):
-- concept/name: finite PMF real-mass normalization; orig was pmf_toReal_sum_eq_one.
-- generality used: an arbitrary finite type and a Mathlib `PMF`; no measure,
-- convexity, smoothness, oracle, or algorithm setup assumptions are needed.
-- portable call pattern: finite discrete sampling proofs that convert a
-- PMF-valued law into real block probabilities can reuse the same normalization
-- conclusion while changing only the finite index type and PMF.
-- counterargument checked: this is not paper traceability or a pure rename;
-- Mathlib supplies the ENNReal `PMF.tsum_coe`, but not the finite real-valued
-- atom-sum bridge used by stochastic-optimization coefficient proofs.
-- coverage search: searched `PMF tsum coe toReal sum one Fintype ENNReal`,
-- `finite probability mass function sum toReal equals one`, and catalog tokens
-- `sum_toReal`, `toReal_sum`, `finite PMF sum`; relevant hits were Mathlib
-- `PMF.tsum_coe`, `PMF.hasSum_coe_one`, `PMF.ofFintype`, SOptLib finite PMF
-- product-measure expansions, and real-weight PMF constructors; none state this
-- finite real normalization directly.
-- minimal hypotheses: all already minimal; `[Fintype α]` is exactly what turns
-- the PMF total mass tsum into a finite sum over all atoms.


open scoped BigOperators

namespace PMF

/-- The real-valued atom masses of a finite PMF sum to `1`.

For a probability mass function on a finite type, converting each ENNReal atom
to a real number preserves the total mass because PMF atoms are finite.

Layer: Glue | Gap: Level 0 (finite PMF real normalization)
Proof: convert the finite ENNReal sum with `ENNReal.toReal_sum`, then rewrite the
  ENNReal total mass using `PMF.tsum_coe` and `tsum_fintype`.
Source: Mathlib probability mass functions, ENNReal finite sums, and finite
  tsum APIs
Used in: random primal-dual gradient block-sampling probability normalization
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/steps/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem sum_toReal_eq_one {α : Type*} [Fintype α] (p : PMF α) :
    (∑ a : α, (p a).toReal) = 1 := by
  classical
  have hsum : (∑ a : α, p a) = (1 : ENNReal) := by
    simpa [tsum_fintype] using (PMF.tsum_coe p)
  calc
    (∑ a : α, (p a).toReal) = (∑ a : α, p a).toReal := by
      exact (ENNReal.toReal_sum (s := Finset.univ) (f := fun a => p a)
        (fun a _ => PMF.apply_ne_top p a)).symm
    _ = (1 : ENNReal).toReal := by
      rw [hsum]
    _ = 1 := by
      simp [ENNReal.toReal_one]

end PMF


-- Promoted from Staging/setIntegral_indicator_eq_prob_mul_of_indep.lean
open MeasureTheory ProbabilityTheory

-- Generalization plan (G0):
-- concept/name: restricted set integral of an independent hit indicator; orig was
--   setIntegral_hitIndicator_sampledBlock_prefix.
-- generality used: arbitrary measurable space Ω, arbitrary measure μ, abstract
--   past and fresh sigma-algebras m and mfresh, an arbitrary measurable hit
--   event, and a real event probability p.
-- portable call pattern: stochastic mirror descent, coordinate SGD, and
--   randomized primal-dual proofs condition on a fresh sampled index while
--   testing against an adapted/past-measurable event s; the hit event,
--   probability p, and sigma-algebras change, but the restricted indicator
--   integral identity is unchanged.
-- counterargument checked: not paper-local traceability because the statement
--   has no block, prefix, setup, iterate, or algorithm vocabulary; not a pure
--   wrapper because it combines Mathlib's indicator integral, restricted
--   measure-real API, independence of sigma-algebras, and ENNReal-to-real
--   probability conversion in the exact conditional-expectation set-integral
--   form future stochastic proofs need.
-- coverage search: searched SOptLib catalog/source for setIntegral, indicator,
--   independent, probability and LeanSearch for "integral of indicator over
--   measurable set independent event equals probability times measure"; top
--   hits were Mathlib integral_indicator_one, ProbabilityTheory.IndepSet.
--   measure_inter_eq_mul, and ProbabilityTheory.lintegral_mul_indicator_eq_
--   lintegral_mul_lintegral_indicator, none giving this real-valued restricted
--   set-integral identity against a sub-sigma-algebra measurable set.
-- minimal hypotheses: hhit and hhit_fresh make the hit event ambient-
--   measurable and fresh-measurable; hs and h_indep are used only for the
--   independence product; hprob_real supplies exactly the real-valued event
--   mass needed by the conclusion.

/-- Integrating a fresh hit indicator over a past-measurable set gives its
probability times the set mass.

If the fresh sigma-algebra containing `hit` is independent of the past
sigma-algebra `m`, then the real set integral of that hit indicator over any
`m`-measurable set is the hit probability times `μ.real` of the set.

Layer: Glue | Gap: Level 1 (restricted independent indicator set integral)
Proof: rewrite the set integral as the real measure of `s ∩ hit`, apply
  independence of the past and fresh sigma-algebras, and convert the ENNReal
  event probability to the supplied real probability.
Source: Mathlib measure-theory indicator integration and probability
  independence APIs
Used in: stochastic primal-dual and mirror-descent conditioning on a fresh
  sampled coordinate over an adapted prefix event
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem setIntegral_indicator_eq_prob_mul_of_indep
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : @Measure Ω mΩ} {m mfresh : MeasurableSpace Ω}
    {hit s : Set Ω} {p : ℝ}
    (hhit : @MeasurableSet Ω mΩ hit)
    (hhit_fresh : @MeasurableSet Ω mfresh hit)
    (hs : @MeasurableSet Ω m s)
    (h_indep : Indep m mfresh μ)
    (hprob_real : μ.real hit = p) :
    ∫ ω in s, (hit.indicator (fun _ : Ω => (1 : ℝ)) ω) ∂μ =
      p * μ.real s := by
  classical
  have hinter : μ (s ∩ hit) = μ s * μ hit := by
    have hind := (ProbabilityTheory.Indep_iff m mfresh μ).1 h_indep
    exact hind s hit hs hhit_fresh
  calc
    ∫ ω in s, (hit.indicator (fun _ : Ω => (1 : ℝ)) ω) ∂μ =
        μ.real (s ∩ hit) := by
      change ∫ ω, hit.indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ.restrict s =
        μ.real (s ∩ hit)
      calc
        ∫ ω, hit.indicator (fun _ : Ω => (1 : ℝ)) ω ∂μ.restrict s =
            (μ.restrict s).real hit := by
          exact integral_indicator_one (μ := μ.restrict s) (s := hit) hhit
        _ = μ.real (s ∩ hit) := by
          rw [measureReal_restrict_apply hhit]
          rw [Set.inter_comm]
    _ = p * μ.real s := by
      rw [measureReal_def, hinter]
      rw [ENNReal.toReal_mul]
      have hhit_real : (μ hit).toReal = p := by
        simpa [measureReal_def] using hprob_real
      rw [hhit_real]
      rw [measureReal_def]
      ring


-- Merged from Staging/expectation_finset_sum_sub_sub_const_mul_eq.lean
open MeasureTheory
open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: finite-sum expectation linearity for a subtractive affine
--   scalar-smul expression; orig was `expectation_y_window_split_local`, renamed
--   away from RGEM-local `YWindow` vocabulary.
-- generality used: arbitrary measurable sample space, arbitrary measure,
--   arbitrary finite index set, three real-normed-vector-valued payload
--   families, and one deterministic real coefficient; no probability,
--   independence, filtration, convexity, smoothness, oracle, inner-product,
--   or finite-dimensional assumptions are used.
-- portable call pattern: finite-table stochastic descent proofs split the
--   expectation of a sum of new-minus-current-minus-coefficient-times-lagged
--   payloads into three named expectation sums; the payload families, finite
--   index set, coefficient, and measure change while the conclusion stays the
--   same.
-- counterargument checked: this is a short wrapper over Mathlib Bochner
--   integral finite-sum and subtraction linearity, but it is not paper-local
--   traceability because randomized coordinate, finite-memory, and table-based
--   descent proofs repeatedly need the same expectation-level regrouping.
--   Existing SOptLib helpers cover two-term affine expectation splitting,
--   finite-sum monotonicity, and finite-key const-smul sums, but not this
--   three-family subtractive finite-sum equality.
-- coverage search: searched CATALOG.md/SOptLib/Staging/source for
--   `expectation finite sum sub sub const mul`, `sum_sub_sub`, and
--   `integral_finset_sum`; closest hits were `expectation_add_const_mul_eq`,
--   `expectation_le_sum_expectation_of_ae_le_finset_sum`, and
--   `expectation_finset_sum_const_smul_comp_eq_of_finite_range_key`, all
--   partial. LeanSearch returned Mathlib `MeasureTheory.integral_finset_sum`,
--   `MeasureTheory.integral_sub`, and `MeasureTheory.integral_smul` as
--   proof ingredients rather than a combined expectation-level theorem.
-- minimal hypotheses: integrability of the three active payload families is
--   exactly what the finite-sum, subtraction, and scalar-action integral
--   linearity steps require.

/-- Split a finite sum of subtractive vector payloads into expectation sums.

For integrable vector-valued payload families `YNew`, `YCurr`, and `YDiff`,
the expectation of `∑ i ∈ s, YNew i - YCurr i - c • YDiff i` is the sum of
the `YNew` expectations minus the sum of the `YCurr` expectations minus `c`
smul the sum of the `YDiff` expectations.

Layer: Glue | Gap: Level 0 (subtractive finite-sum expectation linearity)
Proof: commute the Bochner integral through the finite sum, split each
  subtractive summand using `integral_sub`, pull out the deterministic
  coefficient using `integral_smul`, and regroup finite sums.
Source: Mathlib Bochner integral finite-sum, subtraction, and scalar-linearity APIs
Used in: randomized coordinate and finite-memory stochastic descent recurrences
  that separate new, current, and lagged table-difference expectation terms
Book citation: book/FOML/RandomGradientExtrapolation.json#/key_lemmas/3/proof
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem expectation_finset_sum_sub_sub_const_smul_eq
    {Ω ι E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure Ω}
    (s : Finset ι) (YNew YCurr YDiff : ι → Ω → E) (c : ℝ)
    (hYNew_int : ∀ i ∈ s, Integrable (YNew i) μ)
    (hYCurr_int : ∀ i ∈ s, Integrable (YCurr i) μ)
    (hYDiff_int : ∀ i ∈ s, Integrable (YDiff i) μ) :
    (∫ ω, Finset.sum s
          (fun i => YNew i ω - YCurr i ω - c • YDiff i ω) ∂μ) =
      Finset.sum s (fun i => ∫ ω, YNew i ω ∂μ) -
        Finset.sum s (fun i => ∫ ω, YCurr i ω ∂μ) -
        c • Finset.sum s (fun i => ∫ ω, YDiff i ω ∂μ) := by
  classical
  have hterm_int :
      ∀ i ∈ s,
        Integrable (fun ω => YNew i ω - YCurr i ω - c • YDiff i ω) μ := by
    intro i hi
    exact ((hYNew_int i hi).sub (hYCurr_int i hi)).sub
      ((hYDiff_int i hi).smul c)
  calc
    (∫ ω, Finset.sum s
          (fun i => YNew i ω - YCurr i ω - c • YDiff i ω) ∂μ) =
        Finset.sum s
          (fun i => ∫ ω, YNew i ω - YCurr i ω - c • YDiff i ω ∂μ) := by
      exact MeasureTheory.integral_finset_sum s hterm_int
    _ =
        Finset.sum s
          (fun i =>
            (∫ ω, YNew i ω ∂μ) -
              (∫ ω, YCurr i ω ∂μ) -
              c • (∫ ω, YDiff i ω ∂μ)) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [MeasureTheory.integral_sub]
      · rw [MeasureTheory.integral_sub]
        · rw [MeasureTheory.integral_smul]
        · exact hYNew_int i hi
        · exact hYCurr_int i hi
      · exact (hYNew_int i hi).sub (hYCurr_int i hi)
      · exact (hYDiff_int i hi).smul c
    _ =
        Finset.sum s (fun i => ∫ ω, YNew i ω ∂μ) -
          Finset.sum s (fun i => ∫ ω, YCurr i ω ∂μ) -
          c • Finset.sum s (fun i => ∫ ω, YDiff i ω ∂μ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum]


-- Merged from Staging/expectation_inner_finite_average_extrapolated_table_split.lean
open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: expectation split for an inner product against a finite average
--   of extrapolated table entries; orig was
--   `gradient_extrapolation_tableAverage_inner_expectation_split`, renamed away
--   from gradient-extrapolation and table-average paper vocabulary.
-- generality used: arbitrary measurable sample space, arbitrary measure, finite
--   index set, real inner-product space, scalar extrapolation coefficient, and
--   scalar finite-average weight; no probability, independence, filtration,
--   convexity, smoothness, oracle, or update-rule assumptions are used.
-- portable call pattern: finite-memory stochastic optimization proofs split an
--   expected inner product against an extrapolated gradient/value table into
--   the current table contribution and the current-minus-previous displacement
--   contribution; the payload, table families, finite index set, measure, and
--   scalar coefficients vary while the expectation split conclusion stays fixed.
-- counterargument checked: close to Mathlib `inner_sum`, `inner_smul_right`,
--   `MeasureTheory.integral_finset_sum`, and `MeasureTheory.integral_const_mul`,
--   but not a pure rename of any single theorem because it packages the
--   pointwise extrapolated-table algebra together with expectation linearity in
--   the exact finite-memory split used by stochastic optimization recurrences.
-- coverage search: searched CATALOG.md/SOptLib/Staging/algorithm sources for
--   `expectation inner finite average extrapolated table split`,
--   `Finset.sum expectation inner`, `integral_finset_sum`, and `inner_sum`;
--   closest SOptLib hits were `inner_sum_smul_right_eq_sum_mul_inner`,
--   `expectation_add_const_mul_eq`, and
--   `expectation_le_sum_expectation_of_ae_le_finset_sum`, which respectively
--   cover pointwise algebra, two-term expectation linearity, and monotone
--   finite-sum bounds but not this extrapolated-table expectation equality.
--   LeanSearch returned Mathlib `MeasureTheory.integral_finset_sum`,
--   `MeasureTheory.integral_const_mul`, and `MeasureTheory.Integrable.integral_smul`.
-- minimal hypotheses: weakened from setup-level integrability facts to the two
--   finite families of scalar integrability hypotheses exactly needed for
--   `integral_add`, `integral_finset_sum`, and deterministic scalar factors.

/-- Split the expectation of an inner product against a finite extrapolated table average.

For an arbitrary payload `U`, current table `yCurr`, previous table `yPrev`,
and scalar extrapolation coefficient `alpha`, the expected inner product against
`invCard • ∑ i, extrapolatedPoint alpha (yCurr i) (yPrev i)` separates into
the current-table contribution and the current-minus-previous displacement
contribution.

Layer: Model | Gap: Level 0 (finite extrapolated-table expectation split)
Proof: expand the extrapolated table pointwise using `extrapolatedPoint`, commute
  finite sums through the right slot of the real inner product, and then use
  Bochner integral linearity for addition, scalar multiplication, and finite sums.
Source: Mathlib finite sums, real inner-product algebra, and Bochner integral
  linearity APIs
Used in: randomized gradient extrapolation recurrences that split a finite
  memory-table average into current and displacement expectation terms
Book citation: book/FOML/RandomGradientExtrapolation.json#/algorithm_spec/steps/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem expectation_inner_finite_average_extrapolated_table_split
    {Ω ι E : Type*} [MeasurableSpace Ω]
    [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure Ω) (s : Finset ι) (alpha invCard : ℝ)
    (U : Ω → E) (yCurr yPrev : ι → Ω → E)
    (hCurr_int :
      ∀ i ∈ s, Integrable (fun ω => ⟪U ω, yCurr i ω⟫_ℝ) μ)
    (hDiff_int :
      ∀ i ∈ s, Integrable (fun ω => ⟪U ω, yCurr i ω - yPrev i ω⟫_ℝ) μ) :
    (∫ ω,
        (fun ω =>
          ⟪U ω,
            invCard •
              Finset.sum s
                (fun i => yCurr i ω + alpha • (yCurr i ω - yPrev i ω))⟫_ℝ) ω ∂μ) =
      invCard *
          Finset.sum s
            (fun i =>
              ∫ ω, ⟪U ω, yCurr i ω⟫_ℝ ∂μ) +
        (alpha * invCard) *
          Finset.sum s
            (fun i =>
              ∫ ω, ⟪U ω, yCurr i ω - yPrev i ω⟫_ℝ ∂μ) := by
  classical
  let A : ι → Ω → ℝ := fun i ω => ⟪U ω, yCurr i ω⟫_ℝ
  let D : ι → Ω → ℝ := fun i ω => ⟪U ω, yCurr i ω - yPrev i ω⟫_ℝ
  have hpoint :
      (fun ω =>
        ⟪U ω,
          invCard •
            Finset.sum s
              (fun i => yCurr i ω + alpha • (yCurr i ω - yPrev i ω))⟫_ℝ) =
      (fun ω =>
        invCard * Finset.sum s (fun i => A i ω) +
          (alpha * invCard) * Finset.sum s (fun i => D i ω)) := by
    funext ω
    simp [A, D, inner_sum, inner_add_right,
      inner_smul_right, Finset.sum_add_distrib, Finset.mul_sum, add_comm,
      mul_assoc, mul_left_comm]
  calc
    (∫ ω,
        (fun ω =>
          ⟪U ω,
            invCard •
              Finset.sum s
                (fun i => yCurr i ω + alpha • (yCurr i ω - yPrev i ω))⟫_ℝ) ω ∂μ)
        =
      (∫ ω,
        (fun ω =>
          invCard * Finset.sum s (fun i => A i ω) +
            (alpha * invCard) * Finset.sum s (fun i => D i ω)) ω ∂μ) := by
        rw [hpoint]
    _ =
      invCard * Finset.sum s (fun i => ∫ ω, A i ω ∂μ) +
        (alpha * invCard) * Finset.sum s (fun i => ∫ ω, D i ω ∂μ) := by
        rw [MeasureTheory.integral_add]
        · rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
          rw [MeasureTheory.integral_finset_sum s hCurr_int]
          rw [MeasureTheory.integral_finset_sum s hDiff_int]
        · exact (integrable_finset_sum s hCurr_int).const_mul invCard
        · exact (integrable_finset_sum s hDiff_int).const_mul (alpha * invCard)
    _ =
      invCard *
          Finset.sum s
            (fun i =>
              ∫ ω, ⟪U ω, yCurr i ω⟫_ℝ ∂μ) +
        (alpha * invCard) *
          Finset.sum s
            (fun i =>
              ∫ ω, ⟪U ω, yCurr i ω - yPrev i ω⟫_ℝ ∂μ) := by
        simp [A, D]

end SOptLib


-- Merged from Staging/integrable_of_finiteSampleWindow_factor_aestrongly.lean
open MeasureTheory

-- Generalization plan (G0):
-- concept/name: finite sample-window factor integrability via a.e.-strong
--   reconstruction; orig was `integrable_of_finiteSampleWindow_factor_aestrongly`.
-- generality used: arbitrary measurable source space, finite measurable sample
--   alphabet with measurable singletons, arbitrary finite measure, Nat-indexed
--   sample stream, and arbitrary normed additive codomain; no target
--   `MeasurableSpace`, Borel, second-countability, probability, filtration,
--   convexity, smoothness, or oracle assumptions.
-- portable call pattern: finite-sample stochastic proofs where iterates,
--   generated states, weighted outputs, or scalar/normed payloads are determined
--   by a finite sample window; the sample alphabet, offset, window length,
--   measure, payload type, and window-constancy proof vary while integrability
--   is concluded in the same way.
-- counterargument checked: adjacent SOptLib
--   `integrable_of_finiteSampleWindow_factor` covers the same window shape but
--   requires target measurability and Borel/second-countability hypotheses; this
--   theorem strengthens that codomain side by using countable-key
--   reconstruction, so it is not a duplicate or paper-local traceability.
-- coverage search: searched CATALOG/SOptLib for `finiteSampleWindow`,
--   `finiteRange factor`, and `aestrongly key reconstruction`; read full
--   signatures of `SOptLib.integrable_of_finiteSampleWindow_factor`,
--   `SOptLib.integrable_of_finiteRange_factor`,
--   `SOptLib.integrable_of_finite_range`, and
--   `SOptLib.aestronglyMeasurable_of_countable_key_reconstruction`. LeanSearch
--   for finite-range integrability returned lower-level Mathlib boundedness
--   lemmas such as `MeasureTheory.Integrable.of_bound`, not this finite-window
--   factor theorem.
-- minimal hypotheses: the codomain measurability assumptions from the existing
--   finite-window factor lemma are removed; all remaining hypotheses are used
--   for finite-key measurability, finite range, or finite-measure bounded
--   integrability.

/-- A normed observable determined by a finite-valued sample window is integrable.

For a Nat-indexed stream `ξ` with finite measurable sample alphabet, every
normed observable that is constant on equal finite sample-window values is
integrable under any finite measure. The codomain does not need a measurable
space structure: a countable-window reconstruction supplies a.e.-strong
measurability, and finite range supplies boundedness.

Layer: Glue | Gap: Level 1 (finite sample-window factor integrability without codomain measurability)
Proof: build the finite `Fin n` sample-window key, prove the observable has
  finite range from fiber constancy, reconstruct it from the countable key for
  a.e.-strong measurability, and apply finite-range integrability.
Source: Mathlib Pi measurability, finite function spaces, countable-key
  a.e.-strong measurability, and finite-measure integrability APIs
Used in: randomized gradient extrapolation finite sample-window integrability
  for generated-state, strict-past, and weighted-output payloads
Book citation: book/FOML/RandomGradientExtrapolation.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem integrable_of_finiteSampleWindow_factor_aestrongly
    {Ω Sample F : Type*} [MeasurableSpace Ω] [MeasurableSpace Sample]
    [Fintype Sample] [MeasurableSingletonClass Sample] [NormedAddCommGroup F]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (ξ : ℕ → Ω → Sample) (offset n : ℕ) {Z : Ω → F}
    (hξ_measurable : ∀ k, Measurable (ξ k))
    (hconst :
      ∀ ⦃ω ω' : Ω⦄,
        (fun r : Fin n => ξ (offset + r.1) ω) =
          (fun r : Fin n => ξ (offset + r.1) ω') →
        Z ω = Z ω') :
    Integrable Z μ := by
  classical
  let Y : Ω → Fin n → Sample := fun ω r => ξ (offset + r.1) ω
  have hY_meas : Measurable Y := by
    exact measurable_pi_lambda Y (fun r : Fin n => hξ_measurable (offset + r.1))
  have hY_fin : (Set.range Y).Finite := Set.toFinite _
  have hZ_fin : (Set.range Z).Finite := by
    exact Set.Finite.range_of_finite_range_fiber_const hY_fin hconst
  let reconstruct : (Fin n → Sample) → F := fun y =>
    if hy : y ∈ Set.range Y then Z (Classical.choose hy) else 0
  have hZ_reconstruct : reconstruct ∘ Y =ᵐ[μ] Z := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    dsimp [Function.comp, reconstruct]
    have hy : Y ω ∈ Set.range Y := ⟨ω, rfl⟩
    rw [dif_pos hy]
    exact hconst (Classical.choose_spec hy)
  have hZ_aestrong : AEStronglyMeasurable Z μ := by
    have hrec : AEStronglyMeasurable reconstruct (Measure.map Y μ) := by
      exact AEStronglyMeasurable.of_discrete
    exact (hrec.comp_aemeasurable hY_meas.aemeasurable).congr hZ_reconstruct
  let S : Finset ℝ := hZ_fin.toFinset.image fun z => ‖z‖
  let C : ℝ := if hS : S.Nonempty then S.max' hS else 0
  have hC : ∀ ω, ‖Z ω‖ ≤ C := by
    intro ω
    have hmem : ‖Z ω‖ ∈ S := by
      simp [S, Set.Finite.mem_toFinset]
    have hS : S.Nonempty := ⟨‖Z ω‖, hmem⟩
    simpa [C, hS] using Finset.le_max' S (‖Z ω‖) hmem
  exact Integrable.of_bound hZ_aestrong C (ae_of_all μ hC)


-- Merged from Staging/expectation_eq_mul_of_expectation_eq_inv_mul.lean
open MeasureTheory

-- Generalization plan (G0):
-- concept/name: inverse-scaling cancellation for scalar expectations; orig was `lemma59_auxiliary_gradient_gap_expectation_relation`, renamed away from Lemma 5.9 and gradient-gap vocabulary
-- generality used: arbitrary measurable sample space, arbitrary measure, two `RCLike`-valued random variables, and a nonzero deterministic scalar; no probability, independence, integrability, convexity, smoothness, oracle, or finite-dimensional assumptions are used
-- portable call pattern: coordinate-sampling and mini-batch proofs first identify a selected expectation with an inverse-probability scaled payload, then solve for the unscaled payload expectation; the payloads and sampling law change while the scalar cancellation conclusion stays the same
-- counterargument checked: the proof is a short wrapper over `MeasureTheory.integral_const_mul`, but it is not paper-local traceability because it packages the recurring expectation-level inverse-probability solve used after one-branch selected expectation identities; Mathlib has scalar integral linearity, not this expectation-solve shape
-- coverage search: searched SOptLib catalog/project for "expectation inv mul", "mul of expectation", "integral const mul", and LeanSearch for "if integral C equals integral inverse times A then integral A equals scalar times integral C"; closest SOptLib hit was `expectation_add_const_mul_eq` for affine linearity, and Mathlib hits were `MeasureTheory.integral_const_mul`/`integral_smul`, all partial rather than the solved relation
-- minimal hypotheses: `m ≠ 0` is necessary for cancellation; no integrability hypothesis is needed because the Bochner integral scalar-multiplication theorem used by the proof has no integrability premise

/-- Solve an inverse-scaled scalar expectation identity for the unscaled expectation.

If the expectation of `C` is the expectation of `m⁻¹ * A`, then the expectation
of `A` is `m` times the expectation of `C`, provided `m` is nonzero.

Layer: Model | Gap: Level 0 (expectation inverse-scaling cancellation)
Proof: unfold `SOptLib.expectation`, rewrite the inverse-scaled integral using
  Mathlib's deterministic scalar-multiplication rule for Bochner integrals, and
  cancel the nonzero scalar.
Source: Mathlib measure theory Bochner integral scalar-linearity API
Used in: randomized coordinate and mini-batch gradient proofs after selected
  inverse-probability expectation identities
Book citation: book/FOML/RandomGradientExtrapolation.json#/key_lemmas/4/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem expectation_eq_mul_of_expectation_eq_inv_mul
    {Ω : Type*} [MeasurableSpace Ω]
    {L : Type*} [RCLike L]
    (μ : Measure Ω) (A C : Ω → L) {m : L}
    (hm : m ≠ 0)
    (hC : (∫ ω, C ω ∂μ) =
      ∫ ω, m⁻¹ * A ω ∂μ) :
    (∫ ω, A ω ∂μ) = m * ∫ ω, C ω ∂μ := by
  rw [integral_const_mul] at hC
  calc
    ∫ ω, A ω ∂μ = m * (m⁻¹ * ∫ ω, A ω ∂μ) := by
      field_simp [hm]
    _ = m * ∫ ω, C ω ∂μ := by
      rw [← hC]


-- Merged from Staging/expectation_eq_mul_sub_of_expectation_eq_inv_mul_add.lean
open MeasureTheory

-- Generalization plan (G0):
-- concept/name: two-branch inverse-probability expectation solve; orig was `lemma59_component_value_auxiliary_expectation_relation`, renamed away from Lemma 5.9 and component-value vocabulary
-- generality used: arbitrary measurable sample space, arbitrary measure, branch payloads in a real normed vector space, and a nonzero deterministic real scalar; no probability, independence, convexity, smoothness, oracle, or finite-dimensional assumptions are used
-- portable call pattern: randomized coordinate and mini-batch proofs identify a selected observable as a mixture of an auxiliary branch and a stale branch, then solve for the auxiliary expectation; the measure, branch payloads, and nonzero cardinal/probability scalar change while the solved conclusion stays the same
-- counterargument checked: the theorem packages a short affine algebra step over Bochner-integral linearity, but it is not paper-local traceability because the same two-branch mixture solve recurs after conditional block identities in coordinate methods
-- coverage search: searched the SOptLib catalog/project for "expectation inv mul", "expectation add const mul", "mul sub", and "auxiliary expectation"; the closest approved entries are `expectation_add_const_mul_eq` for expectation linearity and `expectation_eq_mul_of_expectation_eq_inv_mul` for the one-branch solve, while Mathlib/LeanSearch only returned integral scalar-linearity and interval-integral scaling lemmas, all partial rather than this solved two-branch relation
-- minimal hypotheses: `m ≠ 0` is necessary for inverse cancellation; integrability of `A` and `B` is exactly what is needed to split the affine mixture expectation, and no integrability hypothesis on `C` is used

/-- Solve a two-branch inverse-scaled Bochner-integral identity for the first branch.

If the expectation of `C` is the expectation of the mixture
`m⁻¹ • A + (1 - m⁻¹) • B`, then the expectation of `A` is
`m • E[C] - (m - 1) • E[B]`, provided `m` is nonzero.

Layer: Glue | Gap: Level 0 (two-branch inverse-probability expectation solve)
Proof: split the mixture expectation using Mathlib's Bochner integral linearity,
  then multiply by the nonzero scalar and simplify the resulting affine identity.
Source: Mathlib measure theory Bochner integral linearity and real field algebra
Used in: randomized coordinate and mini-batch block-mixture expectation solves
Book citation: book/FOML/RandomGradientExtrapolation.json#/key_lemmas/3/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem expectation_eq_mul_sub_of_expectation_eq_inv_mul_add
    {Ω : Type*} [MeasurableSpace Ω]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (A B C : Ω → E) {m : ℝ}
    (hm : m ≠ 0)
    (hA : Integrable A μ)
    (hB : Integrable B μ)
    (hC : (∫ ω, C ω ∂μ) =
      ∫ ω, m⁻¹ • A ω + (1 - m⁻¹) • B ω ∂μ) :
    (∫ ω, A ω ∂μ) =
      m • (∫ ω, C ω ∂μ) - (m - 1) • (∫ ω, B ω ∂μ) := by
  have hmix :
      (∫ ω, m⁻¹ • A ω + (1 - m⁻¹) • B ω ∂μ) =
        m⁻¹ • (∫ ω, A ω ∂μ) +
          (1 - m⁻¹) • (∫ ω, B ω ∂μ) := by
    rw [integral_add
      (f := fun ω => m⁻¹ • A ω)
      (g := fun ω => (1 - m⁻¹) • B ω)
      (by simpa only [Pi.smul_apply] using hA.smul m⁻¹)
      (by simpa only [Pi.smul_apply] using hB.smul (1 - m⁻¹))]
    simp [integral_smul]
  have hrel :
      (∫ ω, C ω ∂μ) =
        m⁻¹ • (∫ ω, A ω ∂μ) +
          (1 - m⁻¹) • (∫ ω, B ω ∂μ) :=
    hC.trans hmix
  have hscaled :
      m • (∫ ω, C ω ∂μ) =
        (∫ ω, A ω ∂μ) + (m - 1) • (∫ ω, B ω ∂μ) := by
    have hleft : m * m⁻¹ = 1 := by
      field_simp [hm]
    have hright : m * (1 - m⁻¹) = m - 1 := by
      field_simp [hm]
    calc
      m • (∫ ω, C ω ∂μ) =
          m • (m⁻¹ • (∫ ω, A ω ∂μ) +
            (1 - m⁻¹) • (∫ ω, B ω ∂μ)) := by
            rw [hrel]
      _ = (∫ ω, A ω ∂μ) + (m - 1) • (∫ ω, B ω ∂μ) := by
            simp [smul_add, smul_smul, hleft, hright]
  calc
    (∫ ω, A ω ∂μ) =
        ((∫ ω, A ω ∂μ) + (m - 1) • (∫ ω, B ω ∂μ)) -
          (m - 1) • (∫ ω, B ω ∂μ) := by
          rw [add_sub_cancel_right]
    _ = m • (∫ ω, C ω ∂μ) - (m - 1) • (∫ ω, B ω ∂μ) := by
          rw [← hscaled]


-- Generalization plan (G0):
-- concept/name: expectation split after a two-branch affine mixture identity; orig was `lemma59_y_inner_auxiliary_expectation_relation_split`, renamed away from Lemma 5.9 and y-table projection vocabulary
-- generality used: arbitrary measurable sample space, arbitrary measure, branch payloads in a real normed vector space, and an arbitrary real branch weight; no probability, independence, filtration, convexity, smoothness, oracle, or finite-dimensional assumptions are used
-- portable call pattern: selected-coordinate, mini-batch, and refresh/stale table proofs first establish that a selected observable has the expectation of a two-branch affine mixture, then split the result into weighted branch expectations; the measure, payloads, and branch probability change while the conclusion keeps the same shape
-- counterargument checked: this is a short composition over Bochner integral linearity, but it is not paper-local traceability because it packages the recurring post-conditioning boundary from a mixture identity to named branch integrals; it is not a duplicate of `expectation_add_const_mul_eq`, which only splits the mixture integral and does not consume a prior expectation equality
-- coverage search: searched SOptLib catalog/source for `expectation_add_const_mul_eq`, `two_branch`, `branch split`, `mixture expectation`, and `expectation_eq`; LeanSearch for "expectation equality mixture integral p f plus one minus p g split" returned Mathlib conditional-expectation and integral-linearity lemmas; all hits were partial building blocks rather than this equality-to-split wrapper
-- minimal hypotheses: integrability of the two branch payloads is exactly what the underlying Bochner integral additivity needs; the selected observable needs no separate integrability hypothesis because the supplied expectation equality is the only fact used about it

/-- Split a selected integral after a two-branch affine mixture identity.

If the integral of `Y` is the integral of the affine mixture
`p • A + (1 - p) • B`, then it is the corresponding affine combination of the
two branch integrals.

Layer: Glue | Gap: Level 0 (two-branch integral split after mixture identity)
Proof: compose the supplied integral equality with the existing Bochner-integral
  linearity wrapper for deterministic scalar combinations.
Source: Mathlib measure theory Bochner integral linearity API
Used in: randomized coordinate and mini-batch selected-refresh expectation
  substitutions after conditional two-branch identities
Book citation: book/FOML/RandomGradientExtrapolation.json#/key_lemmas/4/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem expectation_two_branch_split_of_expectation_eq
    {Ω : Type*} [MeasurableSpace Ω]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (p : ℝ) (Y A B : Ω → E)
    (hA : Integrable A μ)
    (hB : Integrable B μ)
    (hY : (∫ ω, Y ω ∂μ) =
      ∫ ω, p • A ω + (1 - p) • B ω ∂μ) :
    (∫ ω, Y ω ∂μ) =
      p • (∫ ω, A ω ∂μ) + (1 - p) • (∫ ω, B ω ∂μ) := by
  calc
    (∫ ω, Y ω ∂μ) =
        ∫ ω, p • A ω + (1 - p) • B ω ∂μ := hY
    _ = p • (∫ ω, A ω ∂μ) + (1 - p) • (∫ ω, B ω ∂μ) :=
        expectation_add_const_mul_eq
          (μ := μ) (a := p) (c := 1 - p) (F := A) (G := B) hA hB


namespace SOptLib

-- Generalization plan (G0):
-- concept/name: no-hit finite-sample-window cylinder measurability under the
--   sample-window comap; orig was `no_hit_prefix_measurable_paperStrictPast`,
--   renamed away from the paper strict-past conditioning label.
-- generality used: arbitrary source type, arbitrary measurable sample alphabet
--   with measurable singletons, arbitrary Nat-indexed sample stream, arbitrary
--   half-open window `[offset, stop)`, and fixed forbidden value; no probability
--   measure, independence, integrability, convexity, smoothness, topology,
--   vector space, or finite-dimensional assumptions are used.
-- portable call pattern: stochastic finite-memory and table-refresh proofs
--   condition on a finite sample history and need the event that a coordinate
--   has not appeared in that history to be measurable; the alphabet, window
--   map, offset, prefix length, and forbidden value vary while the comap
--   measurability conclusion stays fixed.
-- counterargument checked: not paper-local traceability because the statement
--   is paper-free finite-cylinder measurability reusable before conditional
--   expectation or fresh-sample independence; not a one-line rename of Mathlib,
--   whose cylinder API covers product-space cylinders but not this direct
--   comap-window no-hit event.
-- coverage search: searched SOptLib/project for `no_hit`, `sampleWindow`,
--   `measurableSet`, and `comap`; relevant hits were the existing
--   `sampleWindowMeasurableSpace_eq_comap` equality and iid no-hit probability
--   theorem, neither proving the no-hit event is measurable under the window
--   comap. LeanSearch for finite-coordinate no-hit measurability returned
--   generic `Measurable.const_eq`, simple-function fiber, and cylinder-set
--   lemmas; coverage is partial, not this callable statement.
-- minimal hypotheses: the original finite alphabet assumption is weakened to
--   measurable singletons because finite-index intersections of singleton
--   complements are measurable; all probability and iid hypotheses are removed.

/-- The event that every coordinate of a finite sample window avoids a fixed
value is measurable for the window comap sigma-algebra.

For any Nat-indexed sample stream, the no-hit event on the half-open interval
`[offset, stop)` is the preimage of a measurable finite-coordinate cylinder
under the explicit finite-window map `fun ω r => sample (offset + r.1) ω`.

Layer: Glue | Gap: Level 1 (finite-window no-hit cylinder measurability)
Proof: express the no-hit event as the preimage of the finite intersection of
  coordinate singleton complements in the product measurable space, then use
  the defining measurability of the comap.
Source: Mathlib product measurable-space, finite intersection, singleton
  measurability, and comap APIs
Used in: randomized gradient extrapolation conditioning on a strict finite
  sampled-block history before applying fresh-block independence
Book citation: book/FOML/RandomGradientExtrapolation.json#/proposition_5_6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem measurableSet_noHit_of_sampleWindow_comap
    {Ω A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
    (sample : ℕ → Ω → A) (offset stop : ℕ) (a : A) :
    @MeasurableSet Ω
      (MeasurableSpace.comap
        (fun ω : Ω => fun r : Fin (stop - offset) => sample (offset + r.1) ω)
        (by infer_instance : MeasurableSpace (Fin (stop - offset) → A)))
      {ω : Ω | ∀ t : ℕ, offset ≤ t → t < stop → sample t ω ≠ a} := by
  classical
  let K : Ω → Fin (stop - offset) → A :=
    fun ω r => sample (offset + r.1) ω
  let C : Set (Fin (stop - offset) → A) := {y | ∀ r : Fin (stop - offset), y r ≠ a}
  have hC_meas : MeasurableSet C := by
    have hcoord : ∀ r : Fin (stop - offset),
        MeasurableSet {y : Fin (stop - offset) → A | y r ≠ a} := by
      intro r
      exact ((measurableSet_singleton a).preimage (measurable_pi_apply r)).compl
    have hC_eq :
        C = ⋂ r : Fin (stop - offset),
          {y : Fin (stop - offset) → A | y r ≠ a} := by
      ext y
      simp [C]
    rw [hC_eq]
    exact MeasurableSet.iInter hcoord
  have hK_meas :
      @Measurable Ω (Fin (stop - offset) → A)
        (MeasurableSpace.comap K
          (by infer_instance : MeasurableSpace (Fin (stop - offset) → A)))
        (by infer_instance : MeasurableSpace (Fin (stop - offset) → A)) K :=
    Measurable.of_comap_le le_rfl
  have hnoHit_fin :
      @MeasurableSet Ω
        (MeasurableSpace.comap K
          (by infer_instance : MeasurableSpace (Fin (stop - offset) → A)))
        {ω : Ω | ∀ r : Fin (stop - offset), K ω r ≠ a} := by
    change @MeasurableSet Ω
      (MeasurableSpace.comap K
        (by infer_instance : MeasurableSpace (Fin (stop - offset) → A))) (K ⁻¹' C)
    exact hC_meas.preimage hK_meas
  have hset :
      {ω : Ω | ∀ t : ℕ, offset ≤ t → t < stop → sample t ω ≠ a} =
        {ω : Ω | ∀ r : Fin (stop - offset), K ω r ≠ a} := by
    ext ω
    constructor
    · intro h r
      exact h (offset + r.1) (by omega) (by omega)
    · intro h t ht_offset ht_stop
      let r : Fin (stop - offset) := ⟨t - offset, by omega⟩
      have hidx : offset + (t - offset) = t := by omega
      simpa [K, r, hidx] using h r
  rw [hset]
  exact hnoHit_fin

end SOptLib


namespace SOptLib

-- Generalization plan (G0):
-- concept/name: no-hit probability for a finite prefix of an iid finite-uniform
--   sample stream; orig was `no_hit_prefix_probability_uniform_block_stream`,
--   renamed to expose the reusable real-valued measure formula.
-- generality used: arbitrary measurable probability space, finite nonempty
--   measurable-singleton index type, measurable sample coordinates, `iIndepFun`
--   for the stream, and pointwise finite-uniform singleton masses; no
--   filtration, oracle, iterate, convexity, topology, vector-space, or
--   finite-dimensional assumptions are used.
-- portable call pattern: randomized coordinate descent, block mirror descent,
--   SAGA/SVRG table-refresh, and finite-memory stochastic algorithms can call
--   this after instantiating the sample stream, prefix offset, prefix length,
--   and forbidden coordinate while preserving the same power-law conclusion.
-- counterargument checked: not paper-local traceability because the statement
--   is free of RGEM objects and packages the recurring independence plus
--   finite-uniform complement product; not a one-line wrapper around
--   Mathlib, whose closest binomial zero-success PMF theorem does not apply to
--   arbitrary sample streams and generated no-hit events.
-- coverage search: searched SOptLib catalog/project for `no_hit`, `uniform
--   finite`, `measureReal`, and `iIndepFun`; relevant hits provide singleton
--   complements and finite-block independence only. LeanSearch for
--   "probability no hits in finite independent identically distributed uniform
--   samples power" returned `PMF.binomial_apply_zero`, `PMF.uniformOfFintype`,
--   and uniform-on facts; coverage is partial, not full.
-- minimal hypotheses: all already minimal for this proof shape; measurability
--   is needed for generated events, `iIndepFun` for finite-block freshness,
--   finite nonempty index type for the positive cardinality denominator, and
--   the uniform marginal hypothesis only at singleton atoms.

/-- The real probability that a finite iid uniform prefix avoids a fixed index.

For a measurable iid sample stream on a finite nonempty index type, if every
coordinate has finite-uniform singleton mass, then the event that the block
`offset, ..., offset + n - 1` never samples `i` has real probability
`((card - 1) / card) ^ n`.

Layer: Glue | Gap: Level 1 (iid finite-uniform prefix no-hit probability)
Proof: precompose the iid stream with the injective finite-window map, apply
  `iIndepFun.measure_inter_preimage_eq_mul` to the no-hit intersection, and
  convert the finite ENNReal product to a real power.
Source: Mathlib probability APIs for `iIndepFun`, finite-block independence,
  real-valued measure complements, and finite uniform distributions
Used in: randomized block and coordinate methods bounding stale-table events by
  the probability of no previous selection in a finite iid sample prefix
Book citation: book/FOML/RandomGradientExtrapolation.json#/proposition_5_6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem measureReal_no_hit_prefix_of_iid_uniform_finite
    {Ω I : Type*} [MeasurableSpace Ω] [MeasurableSpace I]
    [MeasurableSingletonClass I] [Fintype I] [Nonempty I]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (sample : ℕ → Ω → I) (offset n : ℕ) (i : I)
    (hsample_measurable : ∀ t, Measurable (sample t))
    (hsample_iIndep : iIndepFun sample P)
    (hsample_uniform :
      ∀ t j, P ((sample t) ⁻¹' ({j} : Set I)) =
        ENNReal.ofReal ((Fintype.card I : ℝ)⁻¹)) :
    P.real {ω : Ω | ∀ r : Fin n, sample (offset + r.1) ω ≠ i} =
      (((Fintype.card I : ℝ) - 1) / (Fintype.card I : ℝ)) ^ n := by
  classical
  let q : ℝ := ((Fintype.card I : ℝ) - 1) / (Fintype.card I : ℝ)
  have hcard_ne : (Fintype.card I : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card I ≠ 0)
  have hsample_ne_real : ∀ t : ℕ,
      P.real {ω : Ω | sample t ω ≠ i} = q := by
    intro t
    have hhit_meas : MeasurableSet {ω : Ω | sample t ω = i} := by
      have hpre : {ω : Ω | sample t ω = i} =
          (sample t) ⁻¹' ({i} : Set I) := by
        ext ω
        simp
      rw [hpre]
      exact (measurableSet_singleton i).preimage (hsample_measurable t)
    have hhit_real :
        P.real {ω : Ω | sample t ω = i} = (Fintype.card I : ℝ)⁻¹ := by
      have hpre : {ω : Ω | sample t ω = i} =
          (sample t) ⁻¹' ({i} : Set I) := by
        ext ω
        simp
      have hp_nonneg : 0 ≤ (Fintype.card I : ℝ)⁻¹ := by
        exact inv_nonneg.mpr (Nat.cast_nonneg _)
      rw [hpre, measureReal_def, hsample_uniform t i, ENNReal.toReal_ofReal hp_nonneg]
    have hmiss :
        {ω : Ω | sample t ω ≠ i} = {ω : Ω | sample t ω = i}ᶜ := by
      ext ω
      simp
    calc
      P.real {ω : Ω | sample t ω ≠ i}
          = P.real ({ω : Ω | sample t ω = i}ᶜ) := by rw [hmiss]
      _ = 1 - P.real {ω : Ω | sample t ω = i} :=
          probReal_compl_eq_one_sub hhit_meas
      _ = q := by
          rw [hhit_real]
          dsimp [q]
          field_simp [hcard_ne]
  let sampleFin : Fin n → Ω → I := fun r ω => sample (offset + r.1) ω
  have hidx_inj : Function.Injective (fun r : Fin n => offset + r.1) := by
    intro a b hab
    ext
    exact Nat.add_left_cancel hab
  have hsampleFin_iIndep : iIndepFun sampleFin P := by
    simpa [sampleFin] using hsample_iIndep.precomp hidx_inj
  let miss : Fin n → Set I := fun _ => ({i} : Set I)ᶜ
  have hsets_meas : ∀ r ∈ (Finset.univ : Finset (Fin n)), MeasurableSet (miss r) := by
    intro r _hr
    exact (measurableSet_singleton i).compl
  have hprod_measure :
      P (⋂ r ∈ (Finset.univ : Finset (Fin n)), sampleFin r ⁻¹' miss r) =
        ∏ r ∈ (Finset.univ : Finset (Fin n)), P (sampleFin r ⁻¹' miss r) :=
    hsampleFin_iIndep.measure_inter_preimage_eq_mul
      (Finset.univ : Finset (Fin n)) hsets_meas
  have hset :
      {ω : Ω | ∀ r : Fin n, sample (offset + r.1) ω ≠ i} =
        ⋂ r ∈ (Finset.univ : Finset (Fin n)), sampleFin r ⁻¹' miss r := by
    ext ω
    simp [sampleFin, miss]
  calc
    P.real {ω : Ω | ∀ r : Fin n, sample (offset + r.1) ω ≠ i}
        = (P (⋂ r ∈ (Finset.univ : Finset (Fin n)), sampleFin r ⁻¹' miss r)).toReal := by
          rw [hset, measureReal_def]
    _ = (∏ r ∈ (Finset.univ : Finset (Fin n)), P (sampleFin r ⁻¹' miss r)).toReal := by
          rw [hprod_measure]
    _ = ∏ r ∈ (Finset.univ : Finset (Fin n)), (P (sampleFin r ⁻¹' miss r)).toReal := by
          rw [ENNReal.toReal_prod]
    _ = ∏ _r ∈ (Finset.univ : Finset (Fin n)), q := by
          refine Finset.prod_congr rfl ?_
          intro r _hr
          change P.real (sampleFin r ⁻¹' miss r) = q
          simpa [sampleFin, miss] using hsample_ne_real (offset + r.1)
    _ = q ^ n := by
          simp

end SOptLib


-- Generalization plan (G0):
-- concept/name: expectation monotonicity for a scalar residual with two subtractive terms; orig was `proposition56_auxiliary_smoothness_gap_expectation_5_2_72_positive_domain`, renamed away from proposition numbers, smoothness-gap vocabulary, and algorithm-local generated-process fields
-- generality used: arbitrary measurable sample space, arbitrary measure, real-valued observables, one deterministic real scalar, integrability of the four observables, and an a.e. pointwise residual bound; no probability, independence, filtration, convexity, smoothness, oracle, or finite-dimensional hypotheses are used
-- portable call pattern: stochastic descent and Lyapunov proofs lift a pathwise three-term residual inequality into an expected residual inequality; the measure, scalar coefficient, leading budget, and three residual payloads change while the conclusion `c * E[A] ≤ E[F] - E[G] - E[H]` stays the same
-- counterargument checked: this is a short wrapper over `integral_mono_ae`, `integral_const_mul`, and `integral_sub`, but it is not paper-local traceability because the same expectation lift recurs whenever a pointwise descent residual has two subtractive terms; it is not a pure Mathlib duplicate because Mathlib exposes the lower-level integral APIs, not this SOptLib expectation-shaped residual conclusion
-- coverage search: searched the SOptLib catalog/source/staging files for `expectation_le`, `ae_le`, `const_mul`, `sub_sub`, `integral_mono_ae`, and `residual`; closest hits were `expectationLe_of_ae_le_add`, `expectation_le_sum_expectation_of_ae_le_finset_sum`, and `integral_finset_sum_residual_lift_le`, all covering additive expectation bounds or finite-sum residuals rather than this single scalar three-term residual lift; LeanSearch returned Mathlib integral monotonicity and subtraction linearity primitives only
-- minimal hypotheses: the original global pointwise bound is weakened to an
-- a.e. bound over the supplied measure; integrability of `A`, `F`, `G`, and
-- `H` is exactly what the monotonicity and subtraction-linearity steps require

/-- Lift an a.e. three-term ordered residual bound to expectations.

If `c • A ≤ F - G - H` holds almost everywhere and all four observables
are integrable, then the corresponding expectation inequality has the same
three-term residual form.

Layer: Glue | Gap: Level 0 (three-term residual expectation monotonicity)
Proof: apply `integral_mono_ae` to the a.e. residual bound, rewrite the left
  integral by deterministic scalar linearity, and split the right integral by
  subtraction linearity.
Source: Mathlib measure theory Bochner integral monotonicity and real-valued
  integral linearity APIs
Used in: randomized gradient extrapolation expected descent, where an auxiliary
  pathwise smoothness residual is converted into a three-term expected residual
Book citation: book/FOML/RandomGradientExtrapolation.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem expectation_const_smul_le_sub_sub_of_ae_le
    {Omega E : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
    [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] [ClosedIciTopology E]
    (A F G H : Omega → E) (c : ℝ)
    (hA : Integrable A P)
    (hF : Integrable F P)
    (hG : Integrable G P)
    (hH : Integrable H P)
    (hpoint : ∀ᵐ omega ∂P, c • A omega ≤ F omega - G omega - H omega) :
    c • (∫ omega, A omega ∂P) ≤
      (∫ omega, F omega ∂P) - (∫ omega, G omega ∂P) -
        (∫ omega, H omega ∂P) := by
  have hright_int : Integrable (fun omega => F omega - G omega - H omega) P :=
    (hF.sub hG).sub hH
  have hmono :
      (∫ omega, c • A omega ∂P) ≤
        ∫ omega, F omega - G omega - H omega ∂P := by
    exact integral_mono_ae (hA.smul c) hright_int hpoint
  have hleft :
      (∫ omega, c • A omega ∂P) = c • ∫ omega, A omega ∂P := by
    rw [integral_smul]
  have hright :
      (∫ omega, F omega - G omega - H omega ∂P) =
        (∫ omega, F omega ∂P) - (∫ omega, G omega ∂P) -
          (∫ omega, H omega ∂P) := by
    calc
      (∫ omega, F omega - G omega - H omega ∂P) =
          (∫ omega, F omega - G omega ∂P) - (∫ omega, H omega ∂P) := by
            rw [integral_sub]
            · exact hF.sub hG
            · exact hH
      _ = (∫ omega, F omega ∂P) - (∫ omega, G omega ∂P) -
            (∫ omega, H omega ∂P) := by
            rw [integral_sub]
            · exact hF
            · exact hG
  rw [← hleft, ← hright]
  exact hmono


-- Generalization plan (G0):
-- concept/name: integral lift of a weighted finite-window telescope; orig
--   was `proposition56_gradient_extrapolation_telescope_expectation_5_2_65_positive_domain`,
--   renamed away from theorem-number and RGEM-local vocabulary.
-- generality used: arbitrary measurable sample space, arbitrary measure, two
--   finite index windows, vector-valued Bochner payloads in any real normed
--   vector space, deterministic scalar coefficient functions on the finite
--   windows, and one terminal scalar; no probability, independence,
--   filtration, convexity, smoothness, oracle, inner-product, or
--   finite-dimensional assumptions are used.
-- portable call pattern: stochastic descent and finite-memory proofs first
--   establish a pathwise terminal-minus-residual finite-window telescope, then
--   need the same equality after replacing payloads by integrals; the
--   windows, weights, payloads, terminal index, and measure change while the
--   conclusion keeps this shape.
-- counterargument checked: this is assembled from Mathlib integral linearity,
--   but it is not paper-local traceability or a pure rename because no existing
--   SOptLib theorem packages a two-window weighted telescope equality with a
--   terminal term and a subtractive residual window at expectation level.
-- coverage search: searched CATALOG.md/SOptLib/Staging/source for
--   `expectation weighted telescope`, `telescope expectation finite sum`,
--   `weighted finite-window expectation`, and `integral_finset_sum`; closest
--   hits were `expectation_finset_sum_sub_sub_const_smul_eq`,
--   `integral_finset_affine_regroup_of_integral_eq`,
--   `integral_finset_sum_residual_lift_le`, and Mathlib
--   `MeasureTheory.integral_finset_sum`, all proof ingredients or adjacent
--   split/bound forms rather than this equality.
-- minimal hypotheses: integrability of each active `A` and `C` payload and of
--   the terminal payload `B` is exactly what finite-sum, subtraction, and
--   scalar-action integral linearity require.

/-- Lift an almost-everywhere weighted finite-window telescope identity through integration.

If an almost-everywhere identity says that a weighted sum over one finite
window is a terminal weighted payload minus a weighted residual sum over
another finite window, then the same identity holds after replacing every
payload by its Bochner integral.

Layer: Glue | Gap: Level 1 (weighted finite-window telescope expectation lift)
Proof: convert the pathwise identity to equality of Bochner integrals, commute
  both finite weighted sums through the integral, and pull out deterministic
  scalar coefficients.
Source: Mathlib Bochner integral finite-sum, subtraction, and scalar-linearity APIs
Used in: finite-memory stochastic descent after a pathwise sampled-memory
  telescope has been proved and the proof switches to expected recurrences
Book citation: book/FOML/RandomGradientExtrapolation.json#/key_lemmas/13/proof/8
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem integral_weighted_telescope_of_ae_eq
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω} {ι κ : Type*} (s : Finset ι) (r : Finset κ)
    (A : ι → Ω → E) (C : κ → Ω → E) (B : Ω → E)
    (a : ι → ℝ) (β : ℝ) (c : κ → ℝ)
    (hA_int : ∀ t ∈ s, Integrable (A t) μ)
    (hB_int : Integrable B μ)
    (hC_int : ∀ t ∈ r, Integrable (C t) μ)
    (hpath :
      ∀ᵐ ω ∂μ,
        Finset.sum s (fun t => a t • A t ω) =
          β • B ω - Finset.sum r (fun t => c t • C t ω)) :
    Finset.sum s (fun t => a t • ∫ ω, A t ω ∂μ) =
      β • (∫ ω, B ω ∂μ) -
        Finset.sum r (fun t => c t • ∫ ω, C t ω ∂μ) := by
  classical
  have hleft_int :
      Integrable (fun ω => Finset.sum s (fun t => a t • A t ω)) μ := by
    refine MeasureTheory.integrable_finset_sum s ?_
    intro t ht
    simpa only [Pi.smul_apply] using (hA_int t ht).smul (a t)
  have hright_sum_int :
      Integrable (fun ω => Finset.sum r (fun t => c t • C t ω)) μ := by
    refine MeasureTheory.integrable_finset_sum r ?_
    intro t ht
    simpa only [Pi.smul_apply] using (hC_int t ht).smul (c t)
  have hintegral_eq :
      (∫ ω, Finset.sum s (fun t => a t • A t ω) ∂μ) =
        ∫ ω,
          (β • B ω - Finset.sum r (fun t => c t • C t ω)) ∂μ := by
    exact MeasureTheory.integral_congr_ae hpath
  have hleft_eq :
      (∫ ω, Finset.sum s (fun t => a t • A t ω) ∂μ) =
        Finset.sum s (fun t => a t • ∫ ω, A t ω ∂μ) := by
    rw [MeasureTheory.integral_finset_sum]
    · refine Finset.sum_congr rfl ?_
      intro t ht
      rw [MeasureTheory.integral_smul]
    · intro t ht
      simpa only [Pi.smul_apply] using (hA_int t ht).smul (a t)
  have hright_eq :
      (∫ ω,
          (β • B ω - Finset.sum r (fun t => c t • C t ω)) ∂μ) =
        β • (∫ ω, B ω ∂μ) -
          Finset.sum r (fun t => c t • ∫ ω, C t ω ∂μ) := by
    have hsum_eq :
        (∫ ω, Finset.sum r (fun t => c t • C t ω) ∂μ) =
          Finset.sum r (fun t => c t • ∫ ω, C t ω ∂μ) := by
      rw [MeasureTheory.integral_finset_sum]
      · refine Finset.sum_congr rfl ?_
        intro t ht
        rw [MeasureTheory.integral_smul]
      · intro t ht
        simpa only [Pi.smul_apply] using (hC_int t ht).smul (c t)
    rw [MeasureTheory.integral_sub]
    · rw [MeasureTheory.integral_smul, hsum_eq]
    · simpa only [Pi.smul_apply] using hB_int.smul β
    · exact hright_sum_int
  calc
      Finset.sum s (fun t => a t • ∫ ω, A t ω ∂μ) =
        (∫ ω, Finset.sum s (fun t => a t • A t ω) ∂μ) := hleft_eq.symm
    _ =
        ∫ ω,
          (β • B ω - Finset.sum r (fun t => c t • C t ω)) ∂μ :=
        hintegral_eq
    _ =
        β • (∫ ω, B ω ∂μ) -
          Finset.sum r (fun t => c t • ∫ ω, C t ω ∂μ) := hright_eq


namespace SOptLib

-- Generalization plan (G0):
-- concept/name: current-hit/no-previous-hit expectation identity for a finite
--   uniform independent sample stream; orig was
--   `selected_current_no_previous_hit_expectation_eq`, renamed away from RGEM
--   selected-block wording.
-- generality used: arbitrary measurable probability space, arbitrary finite
--   measurable index type with decidable equality, an arbitrary Nat-indexed
--   sample stream, coordinate measurability, `iIndepFun`, and pointwise
--   finite-uniform singleton laws; no iterate, objective, oracle, smoothness,
--   convexity, Hilbert, or finite-dimensional assumptions are used.
-- portable call pattern: coordinate SGD, randomized variance reduction, block
--   mirror descent, and randomized primal-dual proofs compute the expectation
--   of a fresh current-coordinate hit multiplied by the event that the same
--   coordinate has not appeared in a strict prefix; the sample space, finite
--   index type, stream law, horizon, target index, and scalar payload change
--   while the formula stays the same.
-- counterargument checked: not paper-local traceability because the statement
--   has no setup, block-update, iterate, or theorem-number vocabulary; not a
--   pure wrapper because it packages the geometric no-hit probability and the
--   independent current-hit factor. Existing finite-uniform integral bridges
--   cover selected finite averages, not this strict-prefix first-hit identity.
-- coverage search: searched CATALOG/SOptLib for current hit, no previous hit,
--   finite uniform, independent sample, geometric no-hit, and read
--   `SOptLib.integral_comp_indep_finite_uniform_eq_integral_inv_card_sum`,
--   `SOptLib.condExp_indicator_eq_const_of_indep`, and
--   `SOptLib.iIndepFun.indep_past_iSup_current`; LeanSearch returned finite
--   uniform `Finset.expect_ite_eq` lemmas and lower-level conditional
--   expectation/indicator APIs. These are partial building blocks, not the
--   combined stream-prefix expectation formula.
-- minimal hypotheses: uniformity is pointwise in time and index, independence
--   is exactly `iIndepFun` for the stream, and probability is needed only to
--   evaluate the empty prefix as mass one; no finite-dimensional or algorithm
--   assumptions remain.

/-- A current finite-uniform hit times a strict-past no-hit indicator has the
geometric first-hit expectation.

For an independent finite-uniform sample stream, the expectation of the scalar
payload `c` on the event that `sample t = i` and no one-based earlier sample
`sample 1, ..., sample (t - 1)` equals `i` is the current hit probability
`1 / card ι` times the geometric no-previous-hit probability.

Layer: Glue | Gap: Level 1 (finite-uniform current-hit/no-previous-hit expectation)
Proof: prove the strict-prefix no-hit probability by induction using
  `iIndepFun.indep_past_iSup_current`, then factor the current hit from the
  strict prefix and integrate the constant indicator.
Source: Mathlib probability independence, finite measurable spaces, real-valued
  measure, and Bochner indicator-integral APIs
Used in: coordinate and block stochastic methods computing the contribution of
  a selected fresh coordinate whose previous occurrence has not appeared in a
  finite prefix
Book citation: book/FOML/RandomGradientExtrapolation.json#/proposition_5_6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem expectation_current_hit_no_previous_hit_const_eq
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [mι : MeasurableSpace ι]
    [Fintype ι] [Nonempty ι] [DecidableEq ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (sample : ℕ → Ω → ι) (t : ℕ) (i : ι) (c : ℝ)
    (hsample_measurable : ∀ n : ℕ, Measurable (sample n))
    (hsample_iIndep : iIndepFun sample μ)
    (hsample_uniform :
      ∀ n : ℕ, ∀ j : ι,
        (Measure.map (sample n) μ).real ({j} : Set ι) =
          (Fintype.card ι : ℝ)⁻¹) :
    (∫ ω : Ω,
        (if sample t ω = i then
          (by
            classical
            exact if ¬ ∃ r, 1 ≤ r ∧ r ≤ t - 1 ∧ sample r ω = i then c else 0)
        else 0) ∂μ) =
      (Fintype.card ι : ℝ)⁻¹ *
        (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) ^ (t - 1) * c := by
  classical
  let p : ℝ := (Fintype.card ι : ℝ)⁻¹
  let q : ℝ := ((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)
  have hcard_ne : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
  have hprefix_meas_past :
      ∀ n : ℕ,
        @MeasurableSet Ω
          (⨆ j : ℕ, ⨆ _hj : j < n + 1,
            MeasurableSpace.comap (sample j)
              mι)
          {ω : Ω | ∀ r, 1 ≤ r → r ≤ n → sample r ω ≠ i} := by
    intro n
    induction n with
    | zero =>
        have hset :
            {ω : Ω | ∀ r, 1 ≤ r → r ≤ 0 → sample r ω ≠ i} = Set.univ := by
          ext ω
          constructor
          · intro _; trivial
          · intro _ r hr_one hr_le
            omega
        rw [hset]
        exact MeasurableSet.univ
    | succ n ih =>
        let A : Set Ω := {ω : Ω | ∀ r, 1 ≤ r → r ≤ n → sample r ω ≠ i}
        let B : Set Ω := {ω : Ω | sample (n + 1) ω ≠ i}
        let pastSigmaN : MeasurableSpace Ω :=
          ⨆ j : ℕ, ⨆ _hj : j < n + 1,
            MeasurableSpace.comap (sample j) mι
        let pastSigmaSucc : MeasurableSpace Ω :=
          ⨆ j : ℕ, ⨆ _hj : j < n + 1 + 1,
            MeasurableSpace.comap (sample j) mι
        have hmono : pastSigmaN ≤ pastSigmaSucc := by
          refine iSup_le ?_
          intro j
          refine iSup_le ?_
          intro hj
          exact le_iSup_of_le j
            (le_iSup_of_le (Nat.lt_trans hj (Nat.lt_succ_self _)) le_rfl)
        have hA_meas : @MeasurableSet Ω pastSigmaSucc A := by
          exact hmono A (by simpa [A, pastSigmaN] using ih)
        have hB_meas : @MeasurableSet Ω pastSigmaSucc B := by
          have hle :
              MeasurableSpace.comap (sample (n + 1)) mι ≤ pastSigmaSucc := by
            exact le_iSup_of_le (n + 1)
              (le_iSup_of_le (Nat.lt_succ_self (n + 1)) le_rfl)
          have hsample_past :
              @Measurable Ω ι pastSigmaSucc mι (sample (n + 1)) :=
            Measurable.of_comap_le hle
          have hpre :
              B = (sample (n + 1)) ⁻¹' (({i} : Set ι)ᶜ) := by
            ext ω
            simp [B]
          rw [hpre]
          exact (measurableSet_singleton i).compl.preimage hsample_past
        have hset :
            {ω : Ω | ∀ r, 1 ≤ r → r ≤ n + 1 → sample r ω ≠ i} = A ∩ B := by
          ext ω
          constructor
          · intro h
            constructor
            · intro r hr_one hr_le
              exact h r hr_one (by omega)
            · exact h (n + 1) (by omega) (by omega)
          · intro h r hr_one hr_le
            rcases h with ⟨hA, hB⟩
            by_cases hr : r ≤ n
            · exact hA r hr_one hr
            · have hr_eq : r = n + 1 := by omega
              simpa [B, hr_eq] using hB
        rw [hset]
        simpa [pastSigmaSucc] using hA_meas.inter hB_meas
  have hprefix_meas_ambient :
      ∀ n : ℕ, MeasurableSet
        {ω : Ω | ∀ r, 1 ≤ r → r ≤ n → sample r ω ≠ i} := by
    intro n
    let pastSigma : MeasurableSpace Ω :=
      ⨆ j : ℕ, ⨆ _hj : j < n + 1,
        MeasurableSpace.comap (sample j)
          mι
    have hpast_le :
        pastSigma ≤ mΩ := by
      refine iSup_le ?_
      intro j
      refine iSup_le ?_
      intro _hj
      exact @Measurable.comap_le Ω ι
        mΩ
        mι
        (sample j) (hsample_measurable j)
    exact hpast_le _
      (by simpa [pastSigma] using hprefix_meas_past n)
  have hsample_ne_real :
      ∀ n : ℕ, μ.real {ω : Ω | sample n ω ≠ i} = q := by
    intro n
    let Hit : Set Ω := (sample n) ⁻¹' ({i} : Set ι)
    have hHit_meas : MeasurableSet Hit :=
      (measurableSet_singleton i).preimage (hsample_measurable n)
    have hHit_prob : μ.real Hit = p := by
      have hmap :
          (Measure.map (sample n) μ).real ({i} : Set ι) = μ.real Hit := by
        simpa [Hit] using
          (MeasureTheory.map_measureReal_apply
            (μ := μ) (f := sample n) (hsample_measurable n)
            (s := ({i} : Set ι)) (measurableSet_singleton i))
      exact hmap.symm.trans (by simpa [p] using hsample_uniform n i)
    have hcompl : μ.real Hitᶜ = 1 - p := by
      rw [measureReal_def, measure_compl hHit_meas (measure_ne_top μ Hit)]
      rw [ENNReal.toReal_sub_of_le (measure_mono (Set.subset_univ Hit))
        (measure_ne_top μ Set.univ)]
      rw [show (μ Hit).toReal = p by simpa [measureReal_def] using hHit_prob]
      simp [p]
    have hset : {ω : Ω | sample n ω ≠ i} = Hitᶜ := by
      ext ω
      simp [Hit]
    rw [hset, hcompl]
    dsimp [p, q]
    field_simp [hcard_ne]
  have hprefix_prob :
      ∀ n : ℕ,
        μ.real {ω : Ω | ∀ r, 1 ≤ r → r ≤ n → sample r ω ≠ i} = q ^ n := by
    intro n
    induction n with
    | zero =>
        have hset :
            {ω : Ω | ∀ r, 1 ≤ r → r ≤ 0 → sample r ω ≠ i} = Set.univ := by
          ext ω
          constructor
          · intro _; trivial
          · intro _ r hr_one hr_le
            omega
        rw [hset]
        simp [q, probReal_univ]
    | succ n ih =>
        let A : Set Ω := {ω : Ω | ∀ r, 1 ≤ r → r ≤ n → sample r ω ≠ i}
        let B : Set Ω := {ω : Ω | sample (n + 1) ω ≠ i}
        let pastSigma : MeasurableSpace Ω :=
          ⨆ j : ℕ, ⨆ _hj : j < n + 1,
            MeasurableSpace.comap (sample j)
              mι
        let currentSigma : MeasurableSpace Ω :=
          MeasurableSpace.comap (sample (n + 1))
            mι
        have hA_meas : @MeasurableSet Ω pastSigma A := by
          simpa [A, pastSigma] using hprefix_meas_past n
        have hB_meas_current : @MeasurableSet Ω currentSigma B := by
          have hsample_current :
              @Measurable Ω ι currentSigma
                mι (sample (n + 1)) :=
            Measurable.of_comap_le le_rfl
          have hpre :
              B = (sample (n + 1)) ⁻¹' (({i} : Set ι)ᶜ) := by
            ext ω
            simp [B]
          rw [hpre]
          exact (measurableSet_singleton i).compl.preimage hsample_current
        have hIndep0 :
            Indep
              (⨆ j : ℕ, ⨆ _hj : j < n + 1,
                MeasurableSpace.comap (sample j) mι)
              (MeasurableSpace.comap (sample (n + 1)) mι) μ := by
          exact
            @ProbabilityTheory.iIndepFun.indep_past_iSup_current
              Ω ι mΩ mι μ sample (n + 1) hsample_measurable hsample_iIndep
        have hIndep : Indep pastSigma currentSigma μ := by
          simpa [pastSigma, currentSigma] using hIndep0
        have hfac : μ (A ∩ B) = μ A * μ B := by
          exact (Indep_iff pastSigma currentSigma μ).1 hIndep
            A B hA_meas hB_meas_current
        have hreal_fac : μ.real (A ∩ B) = μ.real A * μ.real B := by
          rw [measureReal_def, hfac, ENNReal.toReal_mul, ← measureReal_def,
            ← measureReal_def]
        have hsucc_set :
            {ω : Ω | ∀ r, 1 ≤ r → r ≤ n + 1 → sample r ω ≠ i} = A ∩ B := by
          ext ω
          constructor
          · intro h
            constructor
            · intro r hr_one hr_le
              exact h r hr_one (by omega)
            · exact h (n + 1) (by omega) (by omega)
          · intro h r hr_one hr_le
            rcases h with ⟨hA, hB⟩
            by_cases hr : r ≤ n
            · exact hA r hr_one hr
            · have hr_eq : r = n + 1 := by omega
              simpa [B, hr_eq] using hB
        calc
          μ.real {ω : Ω | ∀ r, 1 ≤ r → r ≤ n + 1 → sample r ω ≠ i}
              = μ.real (A ∩ B) := by rw [hsucc_set]
          _ = μ.real A * μ.real B := hreal_fac
          _ = q ^ n * q := by
              have hBprob : μ.real B = q := by
                simpa [B] using hsample_ne_real (n + 1)
              rw [show μ.real A = q ^ n by simpa [A] using ih, hBprob]
          _ = q ^ (n + 1) := by
              rw [pow_succ]
  let Prev : Set Ω :=
    {ω : Ω | ∀ r, 1 ≤ r → r ≤ t - 1 → sample r ω ≠ i}
  let Hit : Set Ω := {ω : Ω | sample t ω = i}
  let Event : Set Ω := Prev ∩ Hit
  have hPrev_meas : MeasurableSet Prev := by
    simpa [Prev] using hprefix_meas_ambient (t - 1)
  have hHit_meas : MeasurableSet Hit := by
    have hpre : Hit = (sample t) ⁻¹' ({i} : Set ι) := by
      ext ω
      simp [Hit]
    rw [hpre]
    exact (measurableSet_singleton i).preimage (hsample_measurable t)
  have hEvent_meas : MeasurableSet Event := hPrev_meas.inter hHit_meas
  have hPrev_prob : μ.real Prev = q ^ (t - 1) := by
    simpa [Prev] using hprefix_prob (t - 1)
  have hHit_prob : μ.real Hit = p := by
    have hmap :
        (Measure.map (sample t) μ).real ({i} : Set ι) = μ.real Hit := by
      simpa [Hit] using
        (MeasureTheory.map_measureReal_apply
          (μ := μ) (f := sample t) (hsample_measurable t)
          (s := ({i} : Set ι)) (measurableSet_singleton i))
    exact hmap.symm.trans (by simpa [p] using hsample_uniform t i)
  have hPrev_past :
      @MeasurableSet Ω
        (⨆ j : ℕ, ⨆ _hj : j < t,
          MeasurableSpace.comap (sample j)
            mι)
        Prev := by
    by_cases ht : 1 ≤ t
    · have hsub : t - 1 + 1 = t := Nat.sub_add_cancel ht
      have h := hprefix_meas_past (t - 1)
      rw [hsub] at h
      simpa [Prev] using h
    · have hPrev_univ : Prev = Set.univ := by
        ext ω
        constructor
        · intro _; trivial
        · intro _ r hr_one hr_le
          omega
      rw [hPrev_univ]
      exact MeasurableSet.univ
  have hHit_current :
      @MeasurableSet Ω
        (MeasurableSpace.comap (sample t)
          mι)
        Hit := by
    have hsample_current :
        @Measurable Ω ι
          (MeasurableSpace.comap (sample t)
            mι)
          mι (sample t) :=
      Measurable.of_comap_le le_rfl
    have hpre : Hit = (sample t) ⁻¹' ({i} : Set ι) := by
      ext ω
      simp [Hit]
    rw [hpre]
    exact (measurableSet_singleton i).preimage hsample_current
  have hIndep_final :
      Indep
        (⨆ j : ℕ, ⨆ _hj : j < t,
          MeasurableSpace.comap (sample j)
            mι)
        (MeasurableSpace.comap (sample t)
          mι) μ := by
    simpa using
      (@ProbabilityTheory.iIndepFun.indep_past_iSup_current
        Ω ι mΩ mι μ sample t hsample_measurable hsample_iIndep)
  have hEvent_prob : μ.real Event = q ^ (t - 1) * p := by
    have hfac : μ (Prev ∩ Hit) = μ Prev * μ Hit := by
      exact (Indep_iff _ _ μ).1 hIndep_final
        Prev Hit hPrev_past hHit_current
    have hreal_fac : μ.real (Prev ∩ Hit) = μ.real Prev * μ.real Hit := by
      rw [measureReal_def, hfac, ENNReal.toReal_mul, ← measureReal_def,
        ← measureReal_def]
    calc
      μ.real Event = μ.real (Prev ∩ Hit) := by rfl
      _ = μ.real Prev * μ.real Hit := hreal_fac
      _ = q ^ (t - 1) * p := by rw [hPrev_prob, hHit_prob]
  have hfun :
      (fun ω : Ω =>
          if sample t ω = i then
            (by
              classical
              exact if ¬ ∃ r, 1 ≤ r ∧ r ≤ t - 1 ∧ sample r ω = i then c else 0)
          else 0) =
        Event.indicator (fun _ : Ω => c) := by
    funext ω
    have hiff :
        (¬ ∃ r, 1 ≤ r ∧ r ≤ t - 1 ∧ sample r ω = i) ↔ ω ∈ Prev := by
      constructor
      · intro hno r hr_one hr_le heq
        exact hno ⟨r, hr_one, hr_le, heq⟩
      · intro hno hex
        rcases hex with ⟨r, hr_one, hr_le, heq⟩
        exact hno r hr_one hr_le heq
    by_cases hhit : sample t ω = i
    · have hmemHit : ω ∈ Hit := by simpa [Hit] using hhit
      by_cases hno : ¬ ∃ r, 1 ≤ r ∧ r ≤ t - 1 ∧ sample r ω = i
      · have hmemPrev : ω ∈ Prev := hiff.mp hno
        have hmemEvent : ω ∈ Event := ⟨hmemPrev, hmemHit⟩
        simp [hhit, hno, Set.indicator_of_mem hmemEvent]
      · have hnotEvent : ω ∉ Event := by
          intro hmem
          exact hno (hiff.mpr hmem.1)
        simp [hhit, hno, Set.indicator_of_notMem hnotEvent]
    · have hnotEvent : ω ∉ Event := by
        intro hmem
        exact hhit (by simpa [Hit] using hmem.2)
      simp [hhit, Set.indicator_of_notMem hnotEvent]
  calc
    (∫ ω : Ω,
        (if sample t ω = i then
          (by
            classical
            exact if ¬ ∃ r, 1 ≤ r ∧ r ≤ t - 1 ∧ sample r ω = i then c else 0)
        else 0) ∂μ)
        = ∫ ω, Event.indicator (fun _ : Ω => c) ω ∂μ := by
          rw [hfun]
    _ = μ.real Event * c := by
          simpa [smul_eq_mul] using
            (integral_indicator_const (μ := μ) (e := c) hEvent_meas)
    _ = p * q ^ (t - 1) * c := by
          rw [hEvent_prob]
          ring
    _ = (Fintype.card ι : ℝ)⁻¹ *
        (((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ)) ^ (t - 1) * c := by
          rfl

end SOptLib


-- Generalization plan (G0):
-- concept/name: countable-key fiber-factor strong measurability; orig was
--   `strictPast_stronglyMeasurable_of_window_const`, renamed away from the
--   paper strict-past window to expose the measurable countable key.
-- generality used: arbitrary source measurable space, arbitrary sub-sigma
--   algebra `m`, countable measurable key with measurable singletons, and
--   topological codomain only; no measure, probability, norm, filtration,
--   convexity, smoothness, or oracle assumptions are used.
-- portable call pattern: SGD, stochastic mirror descent, variance-reduced,
--   mini-batch, and randomized block proofs can show a state/payload is
--   adapted by proving it is constant on equal finite-prefix keys; the sample
--   path type, key, payload, and sub-sigma algebra vary while
--   `StronglyMeasurable[m]` stays the conclusion.
-- counterargument checked: not paper-local traceability because the theorem is
--   a paper-free factorization through a countable key; not covered by the
--   existing `aestronglyMeasurable_of_countable_key_reconstruction`, which is
--   measure-a.e. and does not provide the sub-sigma `StronglyMeasurable` form
--   required by `condExp_of_stronglyMeasurable`.
-- coverage search: searched CATALOG/SOptLib for `countable_key`,
--   `reconstruction`, `fiber_const`, `StronglyMeasurable`, and `comap`; read
--   `SOptLib.aestronglyMeasurable_of_countable_key_reconstruction` and
--   `SOptLib.measurable_of_finite_range_fiber_const`. LeanSearch for
--   "strongly measurable function constant on fibers of countable measurable
--   function" returned Mathlib `StronglyMeasurable.of_discrete` and simple
--   composition lemmas, but no fiber-factor statement.
-- minimal hypotheses: `Countable Key` and `MeasurableSingletonClass Key` make
--   the range-subtype reconstruction strongly measurable and the range key
--   measurable; all other hypotheses are exactly the ambient spaces and
--   pointwise fiber constancy.

/-- A function constant on fibers of a countable measurable key is strongly
measurable with respect to the key's sigma-algebra.

If `Y` is measurable into a countable key space and `Z` depends only on the
value of `Y`, then `Z` factors through the countable range subtype of `Y`.
Every map out of that countable measurable-singleton subtype is strongly
measurable, so composing with the key gives strong measurability for `Z`.

Layer: Glue | Gap: Level 1 (countable-key fiber-factor strong measurability)
Proof: factor through the range subtype of the key, prove the range-valued key
  measurable by singleton fibers, apply `StronglyMeasurable.of_discrete` on the
  countable range subtype, and use fiber constancy to identify the composition.
Source: Mathlib strongly measurable functions on countable
  measurable-singleton spaces, subtype range APIs, and measurable-space
  singleton-fiber criteria
Used in: randomized gradient extrapolation strict-past adaptation for finite
  sample-prefix payloads before conditional expectation pull-out
Book citation: book/FOML/RandomGradientExtrapolation.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem stronglyMeasurable_of_countable_key_const
    {Ω Key F : Type*} [MeasurableSpace Key]
    [Countable Key] [MeasurableSingletonClass Key] [TopologicalSpace F]
    {m : MeasurableSpace Ω} {Y : Ω → Key} {Z : Ω → F}
    (hY : Measurable[m] Y)
    (hZ_const : ∀ ⦃ω ω' : Ω⦄, Y ω = Y ω' → Z ω = Z ω') :
    StronglyMeasurable[m] Z := by
  classical
  let Yrange : Ω → {y : Key // y ∈ Set.range Y} := fun ω => ⟨Y ω, ⟨ω, rfl⟩⟩
  let reconstruct : {y : Key // y ∈ Set.range Y} → F := fun y =>
    Z (Classical.choose y.2)
  have hYrange : Measurable[m] Yrange := by
    refine measurable_to_countable ?_
    intro ω
    have hset : MeasurableSet[m] (Y ⁻¹' {Y ω}) :=
      hY (measurableSet_singleton (Y ω))
    convert hset using 1
    ext ω'
    simp [Yrange]
  have hZ_reconstruct : reconstruct ∘ Yrange = Z := by
    funext ω
    dsimp [Function.comp, reconstruct, Yrange]
    exact hZ_const (Classical.choose_spec
      (show Y ω ∈ Set.range Y from ⟨ω, rfl⟩))
  have hrec : StronglyMeasurable reconstruct := StronglyMeasurable.of_discrete
  have hcomp : StronglyMeasurable[m] (reconstruct ∘ Yrange) :=
    hrec.comp_measurable hYrange
  simpa [hZ_reconstruct] using hcomp


namespace SOptLib

-- Generalization plan (G0):
-- concept/name: real probability of missing a fixed atom from the pushed-forward
--   singleton mass of a random variable.
-- generality used: arbitrary measurable probability space, arbitrary measurable
--   codomain, a measurable random variable, measurability of the selected
--   singleton, and the real mass of that singleton under the push-forward law;
--   no finite, nonempty, uniform, filtration, independence, oracle, iterate,
--   convexity, topology, vector-space, or finite-dimensional assumptions are
--   used.
-- portable call pattern: randomized coordinate descent, block mirror descent,
--   finite-sum variance-reduction, and table-refresh proofs compute the
--   probability that the current sampled index is not a fixed coordinate after
--   a separate law-specific proof of the selected atom mass.

/-- A sample misses a fixed atom with real probability `1 - p`.

If a measurable random variable has pushed-forward real mass `p` at a selected
measurable singleton, then the real probability of not hitting that singleton is
the complementary mass.

Layer: Glue | Gap: Level 0 (pushed-forward singleton complement mass)
Proof: transfer the singleton mass through `Measure.map_measureReal_apply`,
  identify the miss event as the complement of the singleton preimage, and use
  `probReal_compl_eq_one_sub`.
Source: Mathlib real-valued measure, probability-measure complement, measurable
  singleton, and map APIs
Used in: randomized coordinate and block methods replacing the probability of
  not selecting a fixed index by the complementary pushed-forward atom mass
Book citation: book/FOML/RandomGradientExtrapolation.json#/proposition_5_6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem measureReal_preimage_singleton_compl_eq_one_sub
    {Ω I : Type*} [MeasurableSpace Ω] [MeasurableSpace I]
    (P : Measure Ω) [IsProbabilityMeasure P] {Y : Ω → I} (i : I) {p : ℝ}
    (hY : Measurable Y)
    (hi : MeasurableSet ({i} : Set I))
    (hY_singleton :
      (Measure.map Y P).real ({i} : Set I) = p) :
    P.real {ω : Ω | Y ω ≠ i} = 1 - p := by
  let atom : Set Ω := Y ⁻¹' ({i} : Set I)
  have hatom_meas : MeasurableSet atom := hi.preimage hY
  have hatom_real : P.real atom = p := by
    rw [← map_measureReal_apply (μ := P) hY hi]
    exact hY_singleton
  have hmiss : {ω : Ω | Y ω ≠ i} = atomᶜ := by
    ext ω
    simp [atom]
  calc
    P.real {ω : Ω | Y ω ≠ i} = P.real atomᶜ := by rw [hmiss]
    _ = 1 - P.real atom := probReal_compl_eq_one_sub hatom_meas
    _ = 1 - p := by rw [hatom_real]

end SOptLib


-- Generalization plan (G0):
-- concept/name: Bochner-integral finite-sum affine regrouping;
--   orig was `weighted_q_auxiliary_expectation_to_block_inner`, renamed away
--   from Q, auxiliary/current/lagged roles, and RGEM-local vocabulary.
-- generality used: arbitrary measurable sample space, arbitrary source measure,
--   finite coordinate set, vector-valued payloads in any real normed vector
--   space, one deterministic mixture coefficient, one deterministic recurrence
--   coefficient, and one additive source term; no probability, independence,
--   filtration, convexity, smoothness, oracle, inner-product, or
--   finite-dimensional assumptions are used.
-- portable call pattern: finite-coordinate stochastic recurrences call this
--   after a conditional sampling identity proves that each selected-coordinate
--   integral is the integral of a two-branch affine mixture; the payloads,
--   coefficients, measure, and additive source term change while the finite-sum
--   regrouping conclusion stays fixed.
-- counterargument checked: not paper-local traceability because the statement
--   is paper-free Bochner-integral algebra; not a pure Mathlib wrapper because
--   it combines finite-sum integral linearity with a per-coordinate mixture
--   substitution and coefficient regrouping in the exact recurrence skeleton
--   reused by randomized coordinate and finite-memory methods.
-- coverage search: searched CATALOG.md/SOptLib/Staging/source for
--   `weighted auxiliary expectation`, `current lagged`, `expectation finite
--   sum`, and `integral_finset_sum`; closest hits were
--   `expectation_add_const_mul_eq`,
--   `expectation_finset_sum_const_smul_comp_eq_of_finite_range_key`, and
--   finite-sum telescopes in `SOptLib.Glue.Algebra`, all partial but not this
--   finite-coordinate mixture-regrouping theorem. LeanSearch returned Mathlib
--   `MeasureTheory.integral_finset_sum` and related integral-linearity lemmas,
--   which supply the proof ingredients but not the combined statement.
-- minimal hypotheses: integrability of `A`, `B`, and `N` is exactly what is
--   needed for the displayed linearity steps; no integrability hypothesis on
--   `C` is used because `C` appears only through the supplied integral identity.

/-- Regroup a finite-sum Bochner integral after a two-branch affine identity.

If each selected-coordinate integral is the integral of the affine mixture
`c • A i + (1 - c) • B i`, then the integral of the weighted finite sum
regroups into selected-coordinate integrals, adjusted branch integrals, and the
additive source term.

Layer: Glue | Gap: Level 1 (finite-coordinate integral mixture regrouping)
Proof: commute the Bochner integral through the additive source term,
  deterministic scalar factors, and the finite coordinate sum; then split each
  coordinate mixture integral and normalize the scalar coefficients.
Source: Mathlib Bochner integral finite-sum and scalar-linearity APIs
Used in: randomized coordinate and finite-memory stochastic recurrences after
  selected-coordinate integrals are identified as two-branch affine mixtures
Book citation: book/FOML/RandomGradientExtrapolation.json#/key_lemmas/3/proof/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem integral_finset_affine_regroup_of_integral_eq
    {Ω ι : Type*} [MeasurableSpace Ω]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (s : Finset ι) (A B C : ι → Ω → E) (N : Ω → E) (c tau : ℝ)
    (hA_int : ∀ i ∈ s, Integrable (A i) μ)
    (hB_int : ∀ i ∈ s, Integrable (B i) μ)
    (hN_int : Integrable N μ)
    (hC_mix : ∀ i ∈ s,
      (∫ ω, C i ω ∂μ) =
        ∫ ω, c • A i ω + (1 - c) • B i ω ∂μ) :
    (∫ ω,
        c • Finset.sum s
          (fun i => (1 + tau) • A i ω - tau • B i ω) +
          N ω ∂μ) =
      Finset.sum s
        (fun i =>
          (1 + tau) • (∫ ω, C i ω ∂μ) -
            ((1 + tau) - c) • (∫ ω, B i ω ∂μ)) +
        ∫ ω, N ω ∂μ := by
  classical
  have hsum_int :
      Integrable
        (fun ω =>
          Finset.sum s
            (fun i => (1 + tau) • A i ω - tau • B i ω)) μ := by
    refine integrable_finset_sum s ?_
    intro i _hi
    have hAi : Integrable (fun ω => (1 + tau) • A i ω) μ := by
      simpa only [Pi.smul_apply] using (hA_int i _hi).smul (1 + tau)
    have hBi : Integrable (fun ω => tau • B i ω) μ := by
      simpa only [Pi.smul_apply] using (hB_int i _hi).smul tau
    exact hAi.sub hBi
  have hterm_eq : ∀ i ∈ s,
      (∫ ω, ((1 + tau) • A i ω - tau • B i ω) ∂μ) =
        (1 + tau) • (∫ ω, A i ω ∂μ) -
          tau • (∫ ω, B i ω ∂μ) := by
    intro i hi
    rw [integral_sub]
    · rw [integral_smul, integral_smul]
    · exact by simpa only [Pi.smul_apply] using (hA_int i hi).smul (1 + tau)
    · exact by simpa only [Pi.smul_apply] using (hB_int i hi).smul tau
  have hsum_eq :
      (∫ ω,
          Finset.sum s
            (fun i => (1 + tau) • A i ω - tau • B i ω) ∂μ) =
        Finset.sum s
          (fun i =>
            (1 + tau) • (∫ ω, A i ω ∂μ) -
              tau • (∫ ω, B i ω ∂μ)) := by
    rw [integral_finset_sum]
    · exact Finset.sum_congr rfl (fun i hi => hterm_eq i hi)
    · intro i _hi
      have hAi : Integrable (fun ω => (1 + tau) • A i ω) μ := by
        simpa only [Pi.smul_apply] using (hA_int i _hi).smul (1 + tau)
      have hBi : Integrable (fun ω => tau • B i ω) μ := by
        simpa only [Pi.smul_apply] using (hB_int i _hi).smul tau
      exact hAi.sub hBi
  have hlin :
      (∫ ω,
          c • Finset.sum s
            (fun i => (1 + tau) • A i ω - tau • B i ω) +
            N ω ∂μ) =
        c • Finset.sum s
            (fun i =>
              (1 + tau) • (∫ ω, A i ω ∂μ) -
                tau • (∫ ω, B i ω ∂μ)) +
          ∫ ω, N ω ∂μ := by
    rw [integral_add]
    · rw [integral_smul, hsum_eq]
    · exact by simpa only [Pi.smul_apply] using hsum_int.smul c
    · exact hN_int
  have hC_linear : ∀ i ∈ s,
      (∫ ω, C i ω ∂μ) =
        c • (∫ ω, A i ω ∂μ) +
          (1 - c) • (∫ ω, B i ω ∂μ) := by
    intro i hi
    have hlin_i :
        (∫ ω, c • A i ω + (1 - c) • B i ω ∂μ) =
          c • (∫ ω, A i ω ∂μ) +
            (1 - c) • (∫ ω, B i ω ∂μ) := by
      rw [integral_add]
      · rw [integral_smul, integral_smul]
      · exact by simpa only [Pi.smul_apply] using (hA_int i hi).smul c
      · exact by simpa only [Pi.smul_apply] using (hB_int i hi).smul (1 - c)
    rw [hC_mix i hi, hlin_i]
  calc
    (∫ ω,
        c • Finset.sum s
          (fun i => (1 + tau) • A i ω - tau • B i ω) +
          N ω ∂μ) =
      c • Finset.sum s
          (fun i =>
            (1 + tau) • (∫ ω, A i ω ∂μ) -
              tau • (∫ ω, B i ω ∂μ)) +
        ∫ ω, N ω ∂μ := hlin
    _ =
      Finset.sum s
        (fun i =>
          (1 + tau) • (∫ ω, C i ω ∂μ) -
            ((1 + tau) - c) • (∫ ω, B i ω ∂μ)) +
        ∫ ω, N ω ∂μ := by
        rw [Finset.smul_sum]
        congr 1
        refine Finset.sum_congr rfl ?_
        intro i _hi
        rw [hC_linear i _hi]
        module
