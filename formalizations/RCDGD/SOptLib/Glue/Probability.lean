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
