-- Source: Dziugaite_Roy_2017; Gintare Karolina Dziugaite, Daniel M. Roy; Computing Nonvacuous Generalization Bounds for Deep (Stochastic) Neural Networks with Many More Parameters than Training Data; 2017; URL: https://arxiv.org/pdf/1703.11008v2; section: (1); sha256: 4d28d0e2f5f7b841a5c79c0ecfa675cb6357323a008fa048dff9a07594ee6a35
--
-- Closure JSON: Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala.json
-- This file is sub-pipeline-generated. Sub-phase-0 (Lean
-- alignment) iteratively refines theorem statements + adds
-- definitions as needed. This target-specific file may import
-- an older External/<bib>.lean, but that imported file is
-- read-only for this sub-pipeline.

import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import SOptLib.Glue.Probability

namespace ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala

open MeasureTheory ProbabilityTheory InformationTheory Matrix
open scoped ENNReal RealInnerProductSpace MatrixOrder

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The source-facing covariance domain for Dziugaite--Roy Eq. (1).
Source JSON `phase0_compat_source.json#/main_theorem/statement_math`:
`"assume Σ_q and Σ_p are positive definite"`.  Carrying positive definiteness
in the covariance type prevents the paper object `N(μ,Σ)` from exposing
Mathlib's off-domain totalization of `multivariateGaussian` at arbitrary
matrices. -/
abbrev PositiveDefiniteCovariance (ι : Type*) [Fintype ι] : Type _ :=
  { Sigma : Matrix ι ι ℝ // Sigma.PosDef }

/-- The matrix underlying a source-facing positive-definite covariance. -/
def PositiveDefiniteCovariance.matrix (Sigma : PositiveDefiniteCovariance ι) :
    Matrix ι ι ℝ :=
  Sigma.1

@[simp] theorem PositiveDefiniteCovariance.matrix_eq_coe
    (Sigma : PositiveDefiniteCovariance ι) :
    Sigma.matrix = (Sigma : Matrix ι ι ℝ) := rfl

/-- Immediate source-domain projection: covariances in Eq. (1) are positive
definite by construction. -/
private theorem PositiveDefiniteCovariance.posDef (Sigma : PositiveDefiniteCovariance ι) :
    (Sigma : Matrix ι ι ℝ).PosDef :=
  Sigma.2

variable [DecidableEq ι]

/-- Source JSON `phase0_compat_source.json#/main_theorem/statement_math`:
`"Let N_q = N(μ_q, Σ_q) be a multivariate normal with mean μ_q and covariance
matrix Σ_q"` together with `"assume Σ_q and Σ_p are positive definite"`.
This is the Mathlib Gaussian realization restricted to the paper's covariance
domain, so the off-domain `dirac` fallback of `multivariateGaussian` is not
part of the source-facing object. -/
def multivariateNormalLaw
    (mu : EuclideanSpace ℝ ι) (Sigma : PositiveDefiniteCovariance ι) :
    Measure (EuclideanSpace ℝ ι) :=
  ProbabilityTheory.multivariateGaussian mu (Sigma : Matrix ι ι ℝ)

/-- Definitional bridge for the paper notation `N(μ,Σ)`. -/
@[simp] theorem multivariateNormalLaw_def
    (mu : EuclideanSpace ℝ ι) (Sigma : PositiveDefiniteCovariance ι) :
    multivariateNormalLaw mu Sigma =
      ProbabilityTheory.multivariateGaussian mu (Sigma : Matrix ι ι ℝ) := rfl

/-- The source-facing Gaussian law is a probability measure.  This is the mass
normalization used when Mathlib's finite-measure KL formula is specialized to
probability laws. -/
private theorem multivariateNormalLaw_isProbabilityMeasure
    (mu : EuclideanSpace ℝ ι) (Sigma : PositiveDefiniteCovariance ι) :
    IsProbabilityMeasure (multivariateNormalLaw mu Sigma) := by
  rw [multivariateNormalLaw_def]
  infer_instance

/-- Source JSON `phase0_compat_source.json#/main_theorem/statement_math`:
`"with mean μ_q"`, inside the positive-definite covariance boundary of Eq. (1). -/
private theorem multivariateNormalLaw_mean
    (mu : EuclideanSpace ℝ ι) (Sigma : PositiveDefiniteCovariance ι) :
    ∫ x, x ∂(multivariateNormalLaw mu Sigma) = mu := by
  simp [multivariateNormalLaw]

/-- Source JSON `phase0_compat_source.json#/main_theorem/statement_math`:
`"covariance matrix Σ_q"` and `"assume Σ_q and Σ_p are positive definite"`. -/
private theorem multivariateNormalLaw_covariance
    (mu : EuclideanSpace ℝ ι) (Sigma : PositiveDefiniteCovariance ι)
    (x y : EuclideanSpace ℝ ι) :
    covarianceBilin (multivariateNormalLaw mu Sigma) x y =
      x ⬝ᵥ (Sigma : Matrix ι ι ℝ) *ᵥ y := by
  simpa [multivariateNormalLaw] using
    (ProbabilityTheory.covarianceBilin_multivariateGaussian (μ := mu)
      (S := (Sigma : Matrix ι ι ℝ)) Sigma.posDef.posSemidef x y)

/-- Source JSON `phase0_compat_source.json#/main_theorem/statement_math`:
`"KL(N_q||N_p)"`.  This uses Mathlib's measure-level KL divergence rather than
an asserted scalar witness. -/
def multivariateNormalKLDivergence
    (muq mup : EuclideanSpace ℝ ι)
    (Sigmaq Sigmap : PositiveDefiniteCovariance ι) :
    ℝ≥0∞ :=
  InformationTheory.klDiv (multivariateNormalLaw muq Sigmaq)
    (multivariateNormalLaw mup Sigmap)

/-- Definitional bridge for the paper notation `KL(N_q‖N_p)`. -/
@[simp] theorem multivariateNormalKLDivergence_def
    (muq mup : EuclideanSpace ℝ ι)
    (Sigmaq Sigmap : PositiveDefiniteCovariance ι) :
    multivariateNormalKLDivergence muq mup Sigmaq Sigmap =
      InformationTheory.klDiv (multivariateNormalLaw muq Sigmaq)
        (multivariateNormalLaw mup Sigmap) := rfl

/-- Source JSON `phase0_compat_source.json#/main_theorem/statement_math`:
`"tr(Σ_p^{-1}Σ_q)-k+(μ_p-μ_q)^TΣ_p^{-1}(μ_p-μ_q)+ln(det Σ_p / det Σ_q)"`.
This is the displayed right hand side of Eq. (1). -/
def multivariateNormalKLClosedForm
    (muq mup : EuclideanSpace ℝ ι)
    (Sigmaq Sigmap : PositiveDefiniteCovariance ι) :
    ℝ :=
  (1 / 2 : ℝ) *
    ((((Sigmap : Matrix ι ι ℝ)⁻¹ * (Sigmaq : Matrix ι ι ℝ))).trace -
      (Fintype.card ι : ℝ) +
      (mup - muq) ⬝ᵥ ((Sigmap : Matrix ι ι ℝ)⁻¹ *ᵥ (mup - muq)) +
      Real.log ((Sigmap : Matrix ι ι ℝ).det / (Sigmaq : Matrix ι ι ℝ).det))

/-- Definitional bridge for the closed scalar expression in Eq. (1). -/
@[simp] theorem multivariateNormalKLClosedForm_def
    (muq mup : EuclideanSpace ℝ ι)
    (Sigmaq Sigmap : PositiveDefiniteCovariance ι) :
    multivariateNormalKLClosedForm muq mup Sigmaq Sigmap =
      (1 / 2 : ℝ) *
        ((((Sigmap : Matrix ι ι ℝ)⁻¹ * (Sigmaq : Matrix ι ι ℝ))).trace -
          (Fintype.card ι : ℝ) +
          (mup - muq) ⬝ᵥ ((Sigmap : Matrix ι ι ℝ)⁻¹ *ᵥ (mup - muq)) +
          Real.log ((Sigmap : Matrix ι ι ℝ).det / (Sigmaq : Matrix ι ι ℝ).det)) := rfl

/-- Mathlib's `klDiv` is `ℝ≥0∞`-valued, while the paper displays a finite real
closed form.  This is the canonical finite lift of the displayed Eq. (1)
right hand side into Mathlib's codomain. -/
def multivariateNormalKLClosedFormENNReal
    (muq mup : EuclideanSpace ℝ ι)
    (Sigmaq Sigmap : PositiveDefiniteCovariance ι) :
    ℝ≥0∞ :=
  ENNReal.ofReal (multivariateNormalKLClosedForm muq mup Sigmaq Sigmap)

/-- Definitional bridge for the finite `ℝ≥0∞` realization of Eq. (1). -/
@[simp] theorem multivariateNormalKLClosedFormENNReal_def
    (muq mup : EuclideanSpace ℝ ι)
    (Sigmaq Sigmap : PositiveDefiniteCovariance ι) :
    multivariateNormalKLClosedFormENNReal muq mup Sigmaq Sigmap =
      ENNReal.ofReal (multivariateNormalKLClosedForm muq mup Sigmaq Sigmap) := rfl

/-- Positive definiteness supplies the nonzero determinant needed by the displayed
determinant quotient in Eq. (1).  This is a bridge obligation, not a source
assumption. -/
private theorem positiveDefiniteCovariance_det_ne_zero
    {Sigma : Matrix ι ι ℝ} (hSigma : Sigma.PosDef) :
    Sigma.det ≠ 0 := by
  exact (Matrix.isUnit_iff_isUnit_det Sigma).mp hSigma.isUnit |>.ne_zero

/-- Positive definiteness supplies the positive determinant intended by the
source's logarithm of a determinant quotient.  The proof is left for the prover
phase. -/
private theorem positiveDefiniteCovariance_det_pos
    {Sigma : Matrix ι ι ℝ} (hSigma : Sigma.PosDef) :
    0 < Sigma.det := by
  exact hSigma.det_pos

/-- The source-facing covariance subtype gives the determinant nonzero fact
needed by the displayed determinant quotient. -/
private theorem PositiveDefiniteCovariance.det_ne_zero (Sigma : PositiveDefiniteCovariance ι) :
    (Sigma : Matrix ι ι ℝ).det ≠ 0 :=
  positiveDefiniteCovariance_det_ne_zero Sigma.posDef

/-- The source-facing covariance subtype gives the positive determinant intended
by the displayed logarithm of a determinant quotient. -/
private theorem PositiveDefiniteCovariance.det_pos (Sigma : PositiveDefiniteCovariance ι) :
    0 < (Sigma : Matrix ι ι ℝ).det :=
  positiveDefiniteCovariance_det_pos Sigma.posDef

/-- The covariance square-root in Mathlib's multivariate Gaussian construction is
itself nonsingular for positive-definite covariance.  This is the linear
invertibility ingredient needed for a volume-equivalence proof of the Gaussian
law. -/
private theorem positiveDefiniteCovariance_sqrt_det_pos
    (Sigma : PositiveDefiniteCovariance ι) :
    0 < (CFC.sqrt (Sigma : Matrix ι ι ℝ)).det := by
  exact (Matrix.PosDef.posDef_sqrt Sigma.posDef).det_pos

/-- Nonzero determinant form of `positiveDefiniteCovariance_sqrt_det_pos`,
matching the hypotheses of Mathlib's finite-dimensional volume map lemmas. -/
private theorem positiveDefiniteCovariance_sqrt_det_ne_zero
    (Sigma : PositiveDefiniteCovariance ι) :
    (CFC.sqrt (Sigma : Matrix ι ι ℝ)).det ≠ 0 :=
  ne_of_gt (positiveDefiniteCovariance_sqrt_det_pos Sigma)

/-- The Euclidean linear map used in Mathlib's affine Gaussian construction is
injective when the covariance is positive definite. -/
private theorem positiveDefiniteCovariance_sqrt_toEuclideanCLM_injective
    (Sigma : PositiveDefiniteCovariance ι) :
    Function.Injective
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (Sigma : Matrix ι ι ℝ))) := by
  classical
  intro x y hxy
  apply WithLp.ofLp_injective 2
  have hraw :
      Function.Injective fun v : ι → ℝ =>
        (CFC.sqrt (Sigma : Matrix ι ι ℝ)) *ᵥ v := by
    exact Matrix.mulVec_injective_iff_isUnit.mpr
      (Matrix.PosDef.posDef_sqrt Sigma.posDef).isUnit
  apply hraw
  simpa using congrArg (fun z : EuclideanSpace ℝ ι => WithLp.ofLp z) hxy

/-- Measurable-embedding form of the previous injectivity fact, ready for
`MeasurableEmbedding.absolutelyContinuous_map`. -/
private theorem positiveDefiniteCovariance_sqrt_toEuclideanCLM_measurableEmbedding
    (Sigma : PositiveDefiniteCovariance ι) :
    MeasurableEmbedding
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (Sigma : Matrix ι ι ℝ))) := by
  classical
  let L : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (Sigma : Matrix ι ι ℝ))
  let e : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι :=
    LinearEquiv.ofInjectiveEndo (L : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)
      (positiveDefiniteCovariance_sqrt_toEuclideanCLM_injective Sigma)
  have he_cont : Continuous (e : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) := by
    simpa [e, L, LinearEquiv.coe_ofInjectiveEndo] using L.continuous
  let eL : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι :=
    e.toContinuousLinearEquivOfContinuous he_cont
  have he_meas : MeasurableEmbedding (eL : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) :=
    eL.toHomeomorph.measurableEmbedding
  simpa [eL, e, L, LinearEquiv.coe_ofInjectiveEndo] using he_meas

/-- The affine map that realizes `multivariateNormalLaw` as a pushforward of the
standard Gaussian is a measurable embedding under positive-definite covariance. -/
private theorem multivariateNormalLaw_affineMap_measurableEmbedding
    (mu : EuclideanSpace ℝ ι) (Sigma : PositiveDefiniteCovariance ι) :
    MeasurableEmbedding fun x : EuclideanSpace ℝ ι =>
      mu + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (Sigma : Matrix ι ι ℝ)) x := by
  classical
  have hshift : MeasurableEmbedding fun y : EuclideanSpace ℝ ι => mu + y := by
    simpa using (Homeomorph.addLeft mu).measurableEmbedding
  exact hshift.comp (positiveDefiniteCovariance_sqrt_toEuclideanCLM_measurableEmbedding Sigma)

/-- Definitional form of Mathlib's multivariate Gaussian construction. -/
private theorem multivariateNormalLaw_eq_map_stdGaussian
    (mu : EuclideanSpace ℝ ι) (Sigma : PositiveDefiniteCovariance ι) :
    multivariateNormalLaw mu Sigma =
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)).map
        (fun x : EuclideanSpace ℝ ι =>
          mu + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (Sigma : Matrix ι ι ℝ)) x) := by
  rfl

/-- The positive-definite affine construction transports absolute continuity
from the standard Gaussian to the corresponding multivariate normal law.  The
remaining premise is exactly the finite-product standard-Gaussian density
bridge. -/
private theorem multivariateNormalLaw_absolutelyContinuous_affine_volume
    (mu : EuclideanSpace ℝ ι) (Sigma : PositiveDefiniteCovariance ι)
    (hstd : ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι) ≪
      (volume : MeasureTheory.Measure (EuclideanSpace ℝ ι))) :
    multivariateNormalLaw mu Sigma ≪
      (volume : MeasureTheory.Measure (EuclideanSpace ℝ ι)).map
        (fun x : EuclideanSpace ℝ ι =>
          mu + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (Sigma : Matrix ι ι ℝ)) x) := by
  rw [multivariateNormalLaw_eq_map_stdGaussian]
  exact (multivariateNormalLaw_affineMap_measurableEmbedding mu Sigma).absolutelyContinuous_map hstd

/-- The one-dimensional standard Gaussian has the strict positive density needed
for both directions of absolute continuity with Lebesgue measure. -/
private theorem gaussianReal_zero_one_equivalent_volume :
    ProbabilityTheory.gaussianReal 0 (1 : NNReal) ≪
        (volume : MeasureTheory.Measure ℝ) ∧
      (volume : MeasureTheory.Measure ℝ) ≪
        ProbabilityTheory.gaussianReal 0 (1 : NNReal) := by
  constructor
  · exact ProbabilityTheory.gaussianReal_absolutelyContinuous 0 one_ne_zero
  · exact ProbabilityTheory.gaussianReal_absolutelyContinuous' 0 one_ne_zero

universe u v

private theorem map_withDensity_measurableEquiv
    {α : Type u} {β : Type v} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) {f : β → ℝ≥0∞}
    (hf : Measurable f) :
    (μ.withDensity (fun x => f (e x))).map e =
      (μ.map e).withDensity f := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs]
  rw [MeasureTheory.setLIntegral_map hs hf e.measurable]

private theorem absolutelyContinuous_of_map_measurableEquiv
    {α : Type u} {β : Type v} [MeasurableSpace α] [MeasurableSpace β]
    {μ ν : Measure α} (e : α ≃ᵐ β) (hmap : μ.map e ≪ ν.map e) :
    μ ≪ ν := by
  intro s hs
  have hpre : (ν.map e) (e.symm ⁻¹' s) = 0 := by
    rw [e.map_apply]
    simpa [Set.preimage_preimage] using hs
  have hpre_mu : (μ.map e) (e.symm ⁻¹' s) = 0 := hmap hpre
  rw [e.map_apply] at hpre_mu
  simpa [Set.preimage_preimage] using hpre_mu

private theorem measure_pi_fin_withDensity_prod
    {n : ℕ} (f : Fin n → ℝ → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i))
    (hf_ne_top : ∀ i x, f i x ≠ ∞) :
    Measure.pi (fun i => (volume : Measure ℝ).withDensity (f i)) =
      (volume : Measure (Fin n → ℝ)).withDensity
        (fun x => ∏ i, f i (x i)) := by
  induction n with
  | zero =>
      rw [volume_pi, Measure.pi_of_empty, Measure.pi_of_empty]
      simp
  | succ n ih =>
      haveI : ∀ i : Fin (n + 1),
          SigmaFinite ((volume : Measure ℝ).withDensity (f i)) :=
        fun i => SigmaFinite.withDensity_of_ne_top' (fun x => hf_ne_top i x)
      let e : (∀ i : Fin (n + 1), ℝ) ≃ᵐ
          (ℝ × ∀ i : Fin n, ℝ) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
      apply MeasurableEmbedding.map_injective e.measurableEmbedding
      rw [(measurePreserving_piFinSuccAbove
          (fun i : Fin (n + 1) => (volume : Measure ℝ).withDensity (f i)) 0).map_eq]
      rw [ih (fun i : Fin n => f ((0 : Fin (n + 1)).succAbove i))
        (fun i => hf ((0 : Fin (n + 1)).succAbove i))
        (fun i x => hf_ne_top ((0 : Fin (n + 1)).succAbove i) x)]
      have htail_meas :
          Measurable
            (fun x : Fin n → ℝ => ∏ i, f ((0 : Fin (n + 1)).succAbove i) (x i)) := by
        exact Finset.measurable_fun_prod Finset.univ
          (by
            intro i hi
            exact (hf ((0 : Fin (n + 1)).succAbove i)).comp (measurable_pi_apply i))
      rw [MeasureTheory.prod_withDensity (hf 0) htail_meas]
      have hdensity_source :
          (fun x : Fin (n + 1) → ℝ => ∏ i, f i (x i)) =
            fun x => (fun z : ℝ × (Fin n → ℝ) =>
              f 0 z.1 * ∏ i, f ((0 : Fin (n + 1)).succAbove i) (z.2 i)) (e x) := by
        funext x
        simp [e]
        rw [Fin.prod_univ_succ (fun i : Fin (n + 1) => f i (x i))]
        congr 1
      have hsplit_meas : Measurable (fun z : ℝ × (Fin n → ℝ) =>
          f 0 z.1 * ∏ i, f ((0 : Fin (n + 1)).succAbove i) (z.2 i)) := by
        exact ((hf 0).comp measurable_fst).mul (htail_meas.comp measurable_snd)
      rw [hdensity_source]
      calc
        ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))).withDensity
            (fun z : ℝ × (Fin n → ℝ) =>
              f 0 z.1 * ∏ i, f ((0 : Fin (n + 1)).succAbove i) (z.2 i)) =
            ((volume : Measure (Fin (n + 1) → ℝ)).map e).withDensity
              (fun z : ℝ × (Fin n → ℝ) =>
                f 0 z.1 * ∏ i, f ((0 : Fin (n + 1)).succAbove i) (z.2 i)) := by
          rw [(volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).map_eq]
          rw [Measure.volume_eq_prod]
        _ = Measure.map e ((volume : Measure (Fin (n + 1) → ℝ)).withDensity
            fun x => (fun z : ℝ × (Fin n → ℝ) =>
              f 0 z.1 * ∏ i, f ((0 : Fin (n + 1)).succAbove i) (z.2 i)) (e x)) := by
          simpa using
            (map_withDensity_measurableEquiv e
              (volume : Measure (Fin (n + 1) → ℝ)) hsplit_meas).symm

private theorem measure_pi_real_withDensity_prod
    (f : ι → ℝ → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i))
    (hf_ne_top : ∀ i x, f i x ≠ ∞) :
    Measure.pi (fun i => (volume : Measure ℝ).withDensity (f i)) =
      (volume : Measure (ι → ℝ)).withDensity
        (fun x => ∏ i, f i (x i)) := by
  classical
  let eι : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let e : (∀ j : Fin (Fintype.card ι), ℝ) ≃ᵐ (ι → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) eι
  haveI : ∀ i : ι, SigmaFinite ((volume : Measure ℝ).withDensity (f i)) :=
    fun i => SigmaFinite.withDensity_of_ne_top' (fun x => hf_ne_top i x)
  have hfin :
      Measure.pi
          (fun j : Fin (Fintype.card ι) =>
            (volume : Measure ℝ).withDensity (f (eι j))) =
        (volume : Measure (Fin (Fintype.card ι) → ℝ)).withDensity
          (fun x => ∏ j, f (eι j) (x j)) := by
    exact measure_pi_fin_withDensity_prod
      (fun j : Fin (Fintype.card ι) => f (eι j))
      (fun j => hf (eι j))
      (fun j x => hf_ne_top (eι j) x)
  have hmap :
      (Measure.pi
          (fun j : Fin (Fintype.card ι) =>
            (volume : Measure ℝ).withDensity (f (eι j)))).map e =
        ((volume : Measure (Fin (Fintype.card ι) → ℝ)).withDensity
          (fun x => ∏ j, f (eι j) (x j))).map e := by
    simpa using congrArg
      (fun μ : Measure (Fin (Fintype.card ι) → ℝ) => μ.map e) hfin
  rw [(measurePreserving_piCongrLeft
      (fun i : ι => (volume : Measure ℝ).withDensity (f i)) eι).map_eq] at hmap
  have htarget_meas : Measurable (fun x : ι → ℝ => ∏ i, f i (x i)) := by
    exact Finset.measurable_fun_prod Finset.univ
      (by
        intro i hi
        exact (hf i).comp (measurable_pi_apply i))
  have hdensity_fin :
      (fun x : Fin (Fintype.card ι) → ℝ => ∏ j, f (eι j) (x j)) =
        fun x => (fun y : ι → ℝ => ∏ i, f i (y i)) (e x) := by
    funext x
    calc
      (∏ j, f (eι j) (x j)) =
          ∏ j, f (eι j) ((e x) (eι j)) := by
        refine Finset.prod_congr rfl ?_
        intro j hj
        simpa [e] using
          (congrArg (f (eι j))
            (MeasurableEquiv.piCongrLeft_apply_apply
              (β := fun _ : ι => ℝ) eι x j)).symm
      _ = ∏ i, f i ((e x) i) := by
        exact eι.prod_comp (fun i : ι => f i ((e x) i))
  rw [hdensity_fin] at hmap
  rw [map_withDensity_measurableEquiv e
    (volume : Measure (Fin (Fintype.card ι) → ℝ)) htarget_meas] at hmap
  rw [volume_pi] at hmap
  rw [(measurePreserving_piCongrLeft (fun i : ι => (volume : Measure ℝ)) eι).map_eq] at hmap
  rw [← volume_pi] at hmap
  exact hmap

private theorem stdGaussian_pi_eq_volume_withDensity :
    Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 (1 : NNReal)) =
      (volume : Measure (ι → ℝ)).withDensity
        (fun x => ∏ i, ProbabilityTheory.gaussianPDF 0 (1 : NNReal) (x i)) := by
  simp_rw [ProbabilityTheory.gaussianReal_of_var_ne_zero 0 one_ne_zero]
  exact measure_pi_real_withDensity_prod
    (fun _ : ι => ProbabilityTheory.gaussianPDF 0 (1 : NNReal))
    (fun _ => ProbabilityTheory.measurable_gaussianPDF 0 (1 : NNReal))
    (fun _ x => ProbabilityTheory.gaussianPDF_ne_top (x := x))

private theorem stdGaussian_euclidean_eq_volume_withDensity :
    ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι) =
      (volume : Measure (EuclideanSpace ℝ ι)).withDensity
        (fun x => ∏ i, ProbabilityTheory.gaussianPDF 0 (1 : NNReal) (x i)) := by
  let e : (ι → ℝ) ≃ᵐ EuclideanSpace ℝ ι :=
    MeasurableEquiv.toLp 2 (ι → ℝ)
  let dens : EuclideanSpace ℝ ι → ℝ≥0∞ :=
    fun x => ∏ i, ProbabilityTheory.gaussianPDF 0 (1 : NNReal) (x i)
  have htarget_meas : Measurable dens := by
    exact Finset.measurable_fun_prod Finset.univ
      (by
        intro i hi
        exact (ProbabilityTheory.measurable_gaussianPDF 0 (1 : NNReal)).comp
          (PiLp.continuous_apply (p := 2) (β := fun _ : ι => ℝ) i).measurable)
  have hdensity_source :
      (fun x : ι → ℝ =>
          ∏ i, ProbabilityTheory.gaussianPDF 0 (1 : NNReal) (x i)) =
        fun x => dens (e x) := by
    rfl
  have hvol_map : (volume : Measure (ι → ℝ)).map e =
      (volume : Measure (EuclideanSpace ℝ ι)) := by
    simpa [e] using (PiLp.volume_preserving_toLp ι).map_eq
  rw [← ProbabilityTheory.map_pi_eq_stdGaussian]
  rw [stdGaussian_pi_eq_volume_withDensity]
  rw [hdensity_source]
  change Measure.map (WithLp.toLp 2)
      ((volume : Measure (ι → ℝ)).withDensity (fun x => dens (e x))) =
    (volume : Measure (EuclideanSpace ℝ ι)).withDensity dens
  calc
    Measure.map (WithLp.toLp 2)
        ((volume : Measure (ι → ℝ)).withDensity (fun x => dens (e x))) =
        (((volume : Measure (ι → ℝ)).withDensity (fun x => dens (e x))).map e) := by
      rfl
    _ = ((volume : Measure (ι → ℝ)).map e).withDensity dens := by
      exact map_withDensity_measurableEquiv e (volume : Measure (ι → ℝ)) htarget_meas
    _ = (volume : Measure (EuclideanSpace ℝ ι)).withDensity dens := by
      rw [hvol_map]

private theorem stdGaussian_euclidean_rnDeriv_volume_eq_density :
    (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)).rnDeriv
        (volume : Measure (EuclideanSpace ℝ ι)) =ᵐ[
      (volume : Measure (EuclideanSpace ℝ ι))]
        fun x => ∏ i, ProbabilityTheory.gaussianPDF 0 (1 : NNReal) (x i) := by
  have hmeas :
      Measurable
        (fun x : EuclideanSpace ℝ ι =>
          ∏ i, ProbabilityTheory.gaussianPDF 0 (1 : NNReal) (x i)) := by
    exact Finset.measurable_fun_prod Finset.univ
      (by
        intro i hi
        exact (ProbabilityTheory.measurable_gaussianPDF 0 (1 : NNReal)).comp
          (PiLp.continuous_apply (p := 2) (β := fun _ : ι => ℝ) i).measurable)
  rw [stdGaussian_euclidean_eq_volume_withDensity]
  exact Measure.rnDeriv_withDensity _ hmeas

private theorem measure_pi_fin_absolutelyContinuous
    {n : ℕ} (μ ν : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (h : ∀ i, μ i ≪ ν i) :
    Measure.pi μ ≪ Measure.pi ν := by
  induction n with
  | zero =>
      exact Measure.absolutelyContinuous_of_eq
        ((Measure.pi_of_empty μ).trans (Measure.pi_of_empty ν).symm)
  | succ n ih =>
      let e : (∀ i : Fin (n + 1), ℝ) ≃ᵐ
          (ℝ × ∀ i : Fin n, ℝ) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
      apply absolutelyContinuous_of_map_measurableEquiv e
      have htail :
          Measure.pi (fun i : Fin n => μ (Fin.succ i)) ≪
            Measure.pi (fun i : Fin n => ν (Fin.succ i)) := by
        exact ih (fun i : Fin n => μ (Fin.succ i))
          (fun i : Fin n => ν (Fin.succ i))
          (fun i : Fin n => h (Fin.succ i))
      rw [(measurePreserving_piFinSuccAbove μ 0).map_eq,
        (measurePreserving_piFinSuccAbove ν 0).map_eq]
      exact (h 0).prod htail

private theorem measure_pi_real_absolutelyContinuous
    (μ ν : ι → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (h : ∀ i, μ i ≪ ν i) :
    Measure.pi μ ≪ Measure.pi ν := by
  classical
  let eι : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let e : (∀ j : Fin (Fintype.card ι), ℝ) ≃ᵐ (ι → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) eι
  have hfin :
      Measure.pi (fun j : Fin (Fintype.card ι) => μ (eι j)) ≪
        Measure.pi (fun j : Fin (Fintype.card ι) => ν (eι j)) := by
    exact measure_pi_fin_absolutelyContinuous
      (fun j : Fin (Fintype.card ι) => μ (eι j))
      (fun j : Fin (Fintype.card ι) => ν (eι j))
      (fun j : Fin (Fintype.card ι) => h (eι j))
  have hmap := hfin.map e.measurable
  rw [(measurePreserving_piCongrLeft (fun i : ι => μ i) eι).map_eq,
    (measurePreserving_piCongrLeft (fun i : ι => ν i) eι).map_eq] at hmap
  exact hmap

private theorem stdGaussian_euclidean_equivalent_volume :
    ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι) ≪
        (volume : MeasureTheory.Measure (EuclideanSpace ℝ ι)) ∧
      (volume : MeasureTheory.Measure (EuclideanSpace ℝ ι)) ≪
        ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι) := by
  constructor
  · have hpi :
        Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 (1 : NNReal)) ≪
          (volume : Measure (ι → ℝ)) := by
      rw [volume_pi]
      exact measure_pi_real_absolutelyContinuous
        (fun _ : ι => ProbabilityTheory.gaussianReal 0 (1 : NNReal))
        (fun _ : ι => (volume : Measure ℝ))
        (fun _ : ι => gaussianReal_zero_one_equivalent_volume.1)
    rw [← ProbabilityTheory.map_pi_eq_stdGaussian]
    rw [← (PiLp.volume_preserving_toLp ι).map_eq]
    exact hpi.map (PiLp.volume_preserving_toLp ι).measurable
  · have hpi :
        (volume : Measure (ι → ℝ)) ≪
          Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 (1 : NNReal)) := by
      rw [volume_pi]
      exact measure_pi_real_absolutelyContinuous
        (fun _ : ι => (volume : Measure ℝ))
        (fun _ : ι => ProbabilityTheory.gaussianReal 0 (1 : NNReal))
        (fun _ : ι => gaussianReal_zero_one_equivalent_volume.2)
    rw [← ProbabilityTheory.map_pi_eq_stdGaussian]
    rw [← (PiLp.volume_preserving_toLp ι).map_eq]
    exact hpi.map (PiLp.volume_preserving_toLp ι).measurable

private theorem positiveDefiniteCovariance_sqrt_toEuclideanCLM_det_ne_zero
    (Sigma : PositiveDefiniteCovariance ι) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (Sigma : Matrix ι ι ℝ))).det ≠ 0 := by
  intro hzero
  let L : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (Sigma : Matrix ι ι ℝ))
  have hker :
      LinearMap.ker (L : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) ≠ ⊥ :=
    (LinearMap.det_eq_zero_iff_ker_ne_bot).mp hzero
  exact hker (LinearMap.ker_eq_bot.mpr
    (positiveDefiniteCovariance_sqrt_toEuclideanCLM_injective Sigma))

private theorem multivariateNormal_affine_volume_equivalent
    (mu : EuclideanSpace ℝ ι) (Sigma : PositiveDefiniteCovariance ι) :
    (volume : MeasureTheory.Measure (EuclideanSpace ℝ ι)).map
          (fun x : EuclideanSpace ℝ ι =>
            mu + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (Sigma : Matrix ι ι ℝ)) x) ≪
        (volume : MeasureTheory.Measure (EuclideanSpace ℝ ι)) ∧
      (volume : MeasureTheory.Measure (EuclideanSpace ℝ ι)) ≪
        (volume : MeasureTheory.Measure (EuclideanSpace ℝ ι)).map
          (fun x : EuclideanSpace ℝ ι =>
            mu + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (Sigma : Matrix ι ι ℝ)) x) := by
  let L : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (Sigma : Matrix ι ι ℝ))
  let shift : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι := fun x => mu + x
  have hdet : L.det ≠ 0 := by
    simpa [L] using positiveDefiniteCovariance_sqrt_toEuclideanCLM_det_ne_zero Sigma
  have hshift_meas : Measurable shift :=
    Continuous.measurable (continuous_const.add continuous_id)
  constructor
  · have hlin :
        (volume : Measure (EuclideanSpace ℝ ι)).map L ≪
          (volume : Measure (EuclideanSpace ℝ ι)) := by
      exact (MeasureTheory.Measure.ContinuousLinearMap.quasiMeasurePreserving
        (μ := (volume : Measure (EuclideanSpace ℝ ι))) L hdet).absolutelyContinuous
    have hshift :
        ((volume : Measure (EuclideanSpace ℝ ι)).map L).map shift ≪
          (volume : Measure (EuclideanSpace ℝ ι)).map shift := by
      exact hlin.map hshift_meas
    change ((volume : Measure (EuclideanSpace ℝ ι)).map L).map shift ≪
      (volume : Measure (EuclideanSpace ℝ ι)).map shift at hshift
    rw [Measure.map_map hshift_meas L.continuous.measurable] at hshift
    rw [MeasureTheory.Measure.IsAddLeftInvariant.map_add_left_eq_self mu] at hshift
    simpa [Function.comp_def, L, shift] using hshift
  · have hlin :
        (volume : Measure (EuclideanSpace ℝ ι)) ≪
          (volume : Measure (EuclideanSpace ℝ ι)).map L := by
      change (volume : Measure (EuclideanSpace ℝ ι)) ≪
        (volume : Measure (EuclideanSpace ℝ ι)).map
          (L : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)
      rw [MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
        (μ := (volume : Measure (EuclideanSpace ℝ ι))) hdet]
      exact MeasureTheory.Measure.absolutelyContinuous_smul
        (μ := (volume : Measure (EuclideanSpace ℝ ι))) (by
          rw [ENNReal.ofReal_ne_zero_iff]
          exact abs_pos.mpr (inv_ne_zero hdet))
    have hshift :
        (volume : Measure (EuclideanSpace ℝ ι)).map shift ≪
          ((volume : Measure (EuclideanSpace ℝ ι)).map L).map shift := by
      exact hlin.map hshift_meas
    change (volume : Measure (EuclideanSpace ℝ ι)).map shift ≪
      ((volume : Measure (EuclideanSpace ℝ ι)).map L).map shift at hshift
    rw [Measure.map_map hshift_meas L.continuous.measurable] at hshift
    have hshift_volume :
        (volume : Measure (EuclideanSpace ℝ ι)).map shift =
          (volume : Measure (EuclideanSpace ℝ ι)) := by
      exact MeasureTheory.Measure.IsAddLeftInvariant.map_add_left_eq_self mu
    simpa [Function.comp_def, L, shift, hshift_volume] using hshift

private theorem multivariateNormal_affine_volume_eq_smul
    (mu : EuclideanSpace ℝ ι) (Sigma : PositiveDefiniteCovariance ι) :
    (volume : MeasureTheory.Measure (EuclideanSpace ℝ ι)).map
        (fun x : EuclideanSpace ℝ ι =>
          mu + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (Sigma : Matrix ι ι ℝ)) x) =
      ENNReal.ofReal
          |(Matrix.toEuclideanCLM (𝕜 := ℝ)
              (CFC.sqrt (Sigma : Matrix ι ι ℝ))).det⁻¹| •
        (volume : MeasureTheory.Measure (EuclideanSpace ℝ ι)) := by
  let L : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (Sigma : Matrix ι ι ℝ))
  let shift : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι := fun x => mu + x
  have hdet : L.det ≠ 0 := by
    simpa [L] using positiveDefiniteCovariance_sqrt_toEuclideanCLM_det_ne_zero Sigma
  have hshift_meas : Measurable shift :=
    Continuous.measurable (continuous_const.add continuous_id)
  calc
    (volume : Measure (EuclideanSpace ℝ ι)).map
        (fun x : EuclideanSpace ℝ ι =>
          mu + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (Sigma : Matrix ι ι ℝ)) x) =
        ((volume : Measure (EuclideanSpace ℝ ι)).map L).map shift := by
      rw [Measure.map_map hshift_meas L.continuous.measurable]
      rfl
    _ = (ENNReal.ofReal |L.det⁻¹| •
          (volume : Measure (EuclideanSpace ℝ ι))).map shift := by
      change Measure.map shift
          (Measure.map
            (L : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)
            (volume : Measure (EuclideanSpace ℝ ι))) =
        Measure.map shift
          (ENNReal.ofReal
            |(LinearMap.det
              (L : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι))⁻¹| •
            (volume : Measure (EuclideanSpace ℝ ι)))
      rw [MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
        (μ := (volume : Measure (EuclideanSpace ℝ ι))) hdet]
    _ = ENNReal.ofReal |L.det⁻¹| •
          (volume : Measure (EuclideanSpace ℝ ι)).map shift := by
      rw [Measure.map_smul]
    _ = ENNReal.ofReal |L.det⁻¹| •
          (volume : Measure (EuclideanSpace ℝ ι)) := by
      rw [MeasureTheory.Measure.IsAddLeftInvariant.map_add_left_eq_self mu]
    _ = ENNReal.ofReal
          |(Matrix.toEuclideanCLM (𝕜 := ℝ)
              (CFC.sqrt (Sigma : Matrix ι ι ℝ))).det⁻¹| •
        (volume : MeasureTheory.Measure (EuclideanSpace ℝ ι)) := by
      rfl

private theorem multivariateNormalLaw_volume_density_affine
    (mu : EuclideanSpace ℝ ι) (Sigma : PositiveDefiniteCovariance ι) :
    ∃ e : EuclideanSpace ℝ ι ≃ᵐ EuclideanSpace ℝ ι,
      (∀ x : EuclideanSpace ℝ ι,
        e x =
          mu + Matrix.toEuclideanCLM (𝕜 := ℝ)
            (CFC.sqrt (Sigma : Matrix ι ι ℝ)) x) ∧
      multivariateNormalLaw mu Sigma =
        (volume : MeasureTheory.Measure (EuclideanSpace ℝ ι)).withDensity
          (fun y : EuclideanSpace ℝ ι =>
            ENNReal.ofReal
                |(Matrix.toEuclideanCLM (𝕜 := ℝ)
                    (CFC.sqrt (Sigma : Matrix ι ι ℝ))).det⁻¹| *
              ∏ i, ProbabilityTheory.gaussianPDF 0 (1 : NNReal) ((e.symm y) i)) := by
  classical
  let L : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (Sigma : Matrix ι ι ℝ))
  let linEquiv : EuclideanSpace ℝ ι ≃ₗ[ℝ] EuclideanSpace ℝ ι :=
    LinearEquiv.ofInjectiveEndo (L : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)
      (positiveDefiniteCovariance_sqrt_toEuclideanCLM_injective Sigma)
  have hlin_cont : Continuous
      (linEquiv : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) := by
    simpa [linEquiv, L, LinearEquiv.coe_ofInjectiveEndo] using L.continuous
  let linCLE : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι :=
    linEquiv.toContinuousLinearEquivOfContinuous hlin_cont
  let affHome : EuclideanSpace ℝ ι ≃ₜ EuclideanSpace ℝ ι :=
    linCLE.toHomeomorph.trans (Homeomorph.addLeft mu)
  let e : EuclideanSpace ℝ ι ≃ᵐ EuclideanSpace ℝ ι :=
    affHome.toMeasurableEquiv
  let phi : EuclideanSpace ℝ ι → ℝ≥0∞ :=
    fun x => ∏ i, ProbabilityTheory.gaussianPDF 0 (1 : NNReal) (x i)
  have he_apply : ∀ x : EuclideanSpace ℝ ι, e x = mu + L x := by
    intro x
    simp [e, affHome, linCLE, linEquiv, L, LinearEquiv.coe_ofInjectiveEndo]
  refine ⟨e, ?_, ?_⟩
  · intro x
    simpa [L] using he_apply x
  · have hphi_meas : Measurable phi := by
      exact Finset.measurable_fun_prod Finset.univ
        (by
          intro i hi
          exact (ProbabilityTheory.measurable_gaussianPDF 0 (1 : NNReal)).comp
            (PiLp.continuous_apply (p := 2) (β := fun _ : ι => ℝ) i).measurable)
    have hpull_meas : Measurable (fun y : EuclideanSpace ℝ ι => phi (e.symm y)) :=
      hphi_meas.comp e.symm.measurable
    have hmap_density :
        ((volume : Measure (EuclideanSpace ℝ ι)).withDensity phi).map e =
          ((volume : Measure (EuclideanSpace ℝ ι)).map e).withDensity
            (fun y : EuclideanSpace ℝ ι => phi (e.symm y)) := by
      have h :=
        map_withDensity_measurableEquiv e
          (volume : Measure (EuclideanSpace ℝ ι)) hpull_meas
      simpa [phi] using h
    have hvol_e :
        (volume : Measure (EuclideanSpace ℝ ι)).map e =
          ENNReal.ofReal |L.det⁻¹| •
            (volume : Measure (EuclideanSpace ℝ ι)) := by
      calc
        (volume : Measure (EuclideanSpace ℝ ι)).map e =
            (volume : Measure (EuclideanSpace ℝ ι)).map
              (fun x : EuclideanSpace ℝ ι => mu + L x) := by
          congr
        _ = ENNReal.ofReal |L.det⁻¹| •
            (volume : Measure (EuclideanSpace ℝ ι)) := by
          simpa [L] using multivariateNormal_affine_volume_eq_smul mu Sigma
    calc
      multivariateNormalLaw mu Sigma =
          ((volume : Measure (EuclideanSpace ℝ ι)).withDensity phi).map e := by
        rw [multivariateNormalLaw_eq_map_stdGaussian,
          stdGaussian_euclidean_eq_volume_withDensity]
        congr
      _ = ((volume : Measure (EuclideanSpace ℝ ι)).map e).withDensity
            (fun y : EuclideanSpace ℝ ι => phi (e.symm y)) := hmap_density
      _ = (ENNReal.ofReal |L.det⁻¹| •
            (volume : Measure (EuclideanSpace ℝ ι))).withDensity
            (fun y : EuclideanSpace ℝ ι => phi (e.symm y)) := by
        rw [hvol_e]
      _ = ENNReal.ofReal |L.det⁻¹| •
            (volume : Measure (EuclideanSpace ℝ ι)).withDensity
              (fun y : EuclideanSpace ℝ ι => phi (e.symm y)) := by
        rw [MeasureTheory.withDensity_smul_measure]
      _ = (volume : Measure (EuclideanSpace ℝ ι)).withDensity
            (fun y : EuclideanSpace ℝ ι =>
              ENNReal.ofReal |L.det⁻¹| *
                ∏ i, ProbabilityTheory.gaussianPDF 0 (1 : NNReal) ((e.symm y) i)) := by
        rw [← MeasureTheory.withDensity_smul
          (μ := (volume : Measure (EuclideanSpace ℝ ι)))
          (r := ENNReal.ofReal |L.det⁻¹|) hpull_meas]
        apply congrArg
          (fun f : EuclideanSpace ℝ ι → ℝ≥0∞ =>
            (volume : Measure (EuclideanSpace ℝ ι)).withDensity f)
        funext y
        simp [Pi.smul_apply, ENNReal.smul_def, phi]
      _ = (volume : MeasureTheory.Measure (EuclideanSpace ℝ ι)).withDensity
          (fun y : EuclideanSpace ℝ ι =>
            ENNReal.ofReal
                |(Matrix.toEuclideanCLM (𝕜 := ℝ)
                    (CFC.sqrt (Sigma : Matrix ι ι ℝ))).det⁻¹| *
              ∏ i, ProbabilityTheory.gaussianPDF 0 (1 : NNReal) ((e.symm y) i)) := by
        rfl

private theorem multivariateNormalLaw_rnDeriv_volume_eq_density_affine
    (mu : EuclideanSpace ℝ ι) (Sigma : PositiveDefiniteCovariance ι) :
    ∃ e : EuclideanSpace ℝ ι ≃ᵐ EuclideanSpace ℝ ι,
      (∀ x : EuclideanSpace ℝ ι,
        e x =
          mu + Matrix.toEuclideanCLM (𝕜 := ℝ)
            (CFC.sqrt (Sigma : Matrix ι ι ℝ)) x) ∧
      (multivariateNormalLaw mu Sigma).rnDeriv
          (volume : MeasureTheory.Measure (EuclideanSpace ℝ ι)) =ᵐ[
            (volume : MeasureTheory.Measure (EuclideanSpace ℝ ι))]
        (fun y : EuclideanSpace ℝ ι =>
          ENNReal.ofReal
              |(Matrix.toEuclideanCLM (𝕜 := ℝ)
                  (CFC.sqrt (Sigma : Matrix ι ι ℝ))).det⁻¹| *
            ∏ i, ProbabilityTheory.gaussianPDF 0 (1 : NNReal) ((e.symm y) i)) := by
  classical
  rcases multivariateNormalLaw_volume_density_affine mu Sigma with ⟨e, he_apply, hlaw⟩
  refine ⟨e, he_apply, ?_⟩
  let phi : EuclideanSpace ℝ ι → ℝ≥0∞ :=
    fun x => ∏ i, ProbabilityTheory.gaussianPDF 0 (1 : NNReal) (x i)
  have hphi_meas : Measurable phi := by
    exact Finset.measurable_fun_prod Finset.univ
      (by
        intro i hi
        exact (ProbabilityTheory.measurable_gaussianPDF 0 (1 : NNReal)).comp
          (PiLp.continuous_apply (p := 2) (β := fun _ : ι => ℝ) i).measurable)
  have hpull_meas : Measurable (fun y : EuclideanSpace ℝ ι => phi (e.symm y)) :=
    hphi_meas.comp e.symm.measurable
  have hdensity_meas :
      Measurable
        (fun y : EuclideanSpace ℝ ι =>
          ENNReal.ofReal
              |(Matrix.toEuclideanCLM (𝕜 := ℝ)
                  (CFC.sqrt (Sigma : Matrix ι ι ℝ))).det⁻¹| *
            ∏ i, ProbabilityTheory.gaussianPDF 0 (1 : NNReal) ((e.symm y) i)) := by
    simpa [phi] using
      (measurable_const.mul hpull_meas)
  rw [hlaw]
  exact Measure.rnDeriv_withDensity
    (volume : Measure (EuclideanSpace ℝ ι)) hdensity_meas

private theorem log_standardGaussianPDF_zero_one (z : ℝ) :
    Real.log (ProbabilityTheory.gaussianPDF 0 (1 : NNReal) z).toReal =
      -z ^ 2 / 2 - Real.log (Real.sqrt (2 * Real.pi)) := by
  have harg_pos : 0 < 2 * Real.pi * ((1 : NNReal) : ℝ) := by
    exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos) (by norm_num)
  have hsqrt_ne : Real.sqrt (2 * Real.pi * ((1 : NNReal) : ℝ)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 harg_pos)
  rw [ProbabilityTheory.toReal_gaussianPDF]
  unfold ProbabilityTheory.gaussianPDFReal
  rw [Real.log_mul (inv_ne_zero hsqrt_ne) (Real.exp_ne_zero _)]
  rw [Real.log_inv (Real.sqrt (2 * Real.pi * ((1 : NNReal) : ℝ)))]
  rw [Real.log_exp]
  simp
  ring

private theorem euclidean_sum_sq_eq_norm_sq (x : EuclideanSpace ℝ ι) :
    (∑ i, (x i) ^ 2) = ‖x‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_congr rfl (fun i hi => by
    rw [Real.norm_eq_abs, sq_abs])

private theorem integrable_inner_const_clm_stdGaussian
    (a : EuclideanSpace ℝ ι)
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :
    Integrable (fun u : EuclideanSpace ℝ ι => inner ℝ a (A u))
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) := by
  have h_id_l2 : MemLp (fun u : EuclideanSpace ℝ ι => u) 2
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) :=
    IsGaussian.memLp_two_id
  have h_id_int : Integrable (fun u : EuclideanSpace ℝ ι => u)
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) :=
    h_id_l2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hA_l2 : MemLp (fun u : EuclideanSpace ℝ ι => A u) 2
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) := by
    simpa [Function.comp_def] using h_id_l2.continuousLinearMap_comp A
  have hA_sq_int : Integrable (fun u : EuclideanSpace ℝ ι => ‖A u‖ ^ 2)
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hA_l2.aestronglyMeasurable).1 hA_l2
  have hconst_sq_int : Integrable (fun _ : EuclideanSpace ℝ ι => ‖a‖ ^ 2)
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) :=
    integrable_const _
  exact integrable_inner_of_integrable_sq_norm
    (P := ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι))
    (u := fun _ : EuclideanSpace ℝ ι => a)
    (v := fun u : EuclideanSpace ℝ ι => A u)
    MeasureTheory.aestronglyMeasurable_const hA_l2.aestronglyMeasurable
    hconst_sq_int hA_sq_int

private theorem integral_norm_sq_add_clm_stdGaussian_split
    (a : EuclideanSpace ℝ ι)
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :
    (∫ u : EuclideanSpace ℝ ι, ‖a + A u‖ ^ 2
        ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι))) =
      ‖a‖ ^ 2 +
        ∫ u : EuclideanSpace ℝ ι, ‖A u‖ ^ 2
          ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) := by
  have h_id_l2 : MemLp (fun u : EuclideanSpace ℝ ι => u) 2
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) :=
    IsGaussian.memLp_two_id
  have h_id_int : Integrable (fun u : EuclideanSpace ℝ ι => u)
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) :=
    h_id_l2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hA_l2 : MemLp (fun u : EuclideanSpace ℝ ι => A u) 2
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) := by
    simpa [Function.comp_def] using h_id_l2.continuousLinearMap_comp A
  have hA_sq_int : Integrable (fun u : EuclideanSpace ℝ ι => ‖A u‖ ^ 2)
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hA_l2.aestronglyMeasurable).1 hA_l2
  have hconst_sq_int : Integrable (fun _ : EuclideanSpace ℝ ι => ‖a‖ ^ 2)
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) :=
    integrable_const _
  have hcross0_int : Integrable (fun u : EuclideanSpace ℝ ι => inner ℝ a (A u))
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) :=
    integrable_inner_const_clm_stdGaussian a A
  have hcross_int : Integrable
      (fun u : EuclideanSpace ℝ ι => 2 * inner ℝ a (A u))
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) :=
    hcross0_int.const_mul 2
  have hpoint : ∀ u : EuclideanSpace ℝ ι,
      ‖a + A u‖ ^ 2 = ‖a‖ ^ 2 + 2 * inner ℝ a (A u) + ‖A u‖ ^ 2 := by
    intro u
    exact norm_add_sq_real a (A u)
  have hcross_zero :
      (∫ u : EuclideanSpace ℝ ι, inner ℝ a (A u)
        ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι))) = 0 := by
    calc
      (∫ u : EuclideanSpace ℝ ι, inner ℝ a (A u)
        ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι))) =
          ∫ u : EuclideanSpace ℝ ι, (inner ℝ (A.adjoint a) u)
            ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) := by
        exact MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun u => by
            rw [ContinuousLinearMap.adjoint_inner_left])
      _ =
          inner ℝ (A.adjoint a)
            (∫ u : EuclideanSpace ℝ ι, u
              ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι))) := by
        simpa [innerSL_apply_apply] using
          (ContinuousLinearMap.integral_comp_comm (innerSL ℝ (A.adjoint a))
            h_id_int)
      _ = 0 := by
        rw [ProbabilityTheory.integral_id_stdGaussian]
        simp
  calc
    (∫ u : EuclideanSpace ℝ ι, ‖a + A u‖ ^ 2
        ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι))) =
        ∫ u : EuclideanSpace ℝ ι,
          (‖a‖ ^ 2 + 2 * inner ℝ a (A u) + ‖A u‖ ^ 2)
          ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) := by
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ =
        (∫ _ : EuclideanSpace ℝ ι, ‖a‖ ^ 2
          ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι))) +
        (∫ u : EuclideanSpace ℝ ι, 2 * inner ℝ a (A u)
          ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι))) +
        (∫ u : EuclideanSpace ℝ ι, ‖A u‖ ^ 2
          ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι))) := by
      calc
        (∫ u : EuclideanSpace ℝ ι,
            (‖a‖ ^ 2 + 2 * inner ℝ a (A u) + ‖A u‖ ^ 2)
            ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι))) =
            (∫ u : EuclideanSpace ℝ ι,
              (‖a‖ ^ 2 + 2 * inner ℝ a (A u))
              ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι))) +
            (∫ u : EuclideanSpace ℝ ι, ‖A u‖ ^ 2
              ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι))) := by
          simpa only [Pi.add_apply] using
            (MeasureTheory.integral_add
              (μ := ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι))
              (f := fun u : EuclideanSpace ℝ ι =>
                ‖a‖ ^ 2 + 2 * inner ℝ a (A u))
              (g := fun u : EuclideanSpace ℝ ι => ‖A u‖ ^ 2)
              (hconst_sq_int.add hcross_int) hA_sq_int)
        _ =
            ((∫ _ : EuclideanSpace ℝ ι, ‖a‖ ^ 2
              ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι))) +
            (∫ u : EuclideanSpace ℝ ι, 2 * inner ℝ a (A u)
              ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)))) +
            (∫ u : EuclideanSpace ℝ ι, ‖A u‖ ^ 2
              ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι))) := by
          simpa only [Pi.add_apply] using
            congrArg (fun t : ℝ =>
              t + ∫ u : EuclideanSpace ℝ ι, ‖A u‖ ^ 2
                ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)))
              (MeasureTheory.integral_add
                (μ := ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι))
                (f := fun _ : EuclideanSpace ℝ ι => ‖a‖ ^ 2)
                (g := fun u : EuclideanSpace ℝ ι => 2 * inner ℝ a (A u))
                hconst_sq_int hcross_int)
        _ =
            (∫ _ : EuclideanSpace ℝ ι, ‖a‖ ^ 2
              ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι))) +
            (∫ u : EuclideanSpace ℝ ι, 2 * inner ℝ a (A u)
              ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι))) +
            (∫ u : EuclideanSpace ℝ ι, ‖A u‖ ^ 2
              ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι))) := by
          ring
    _ =
        ‖a‖ ^ 2 + 0 +
        (∫ u : EuclideanSpace ℝ ι, ‖A u‖ ^ 2
          ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι))) := by
      rw [MeasureTheory.integral_const, MeasureTheory.integral_const_mul, hcross_zero]
      simp
    _ =
        ‖a‖ ^ 2 +
        (∫ u : EuclideanSpace ℝ ι, ‖A u‖ ^ 2
          ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι))) := by
      ring

private theorem integral_norm_sq_clm_stdGaussian_eq_sum_adjoint_basisFun
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :
    (∫ u : EuclideanSpace ℝ ι, ‖A u‖ ^ 2
        ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι))) =
      ∑ i, ‖A.adjoint (EuclideanSpace.basisFun ι ℝ i)‖ ^ 2 := by
  classical
  let b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι) := EuclideanSpace.basisFun ι ℝ
  have h_id_l2 : MemLp (fun u : EuclideanSpace ℝ ι => u) 2
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) :=
    IsGaussian.memLp_two_id
  have hcoord_int :
      ∀ i, Integrable
        (fun u : EuclideanSpace ℝ ι =>
          inner ℝ (b i) (A u) * inner ℝ (b i) (A u))
        (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) := by
    intro i
    have hlin_l2 : MemLp
        (fun u : EuclideanSpace ℝ ι => inner ℝ (A.adjoint (b i)) u) 2
        (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) := by
      simpa [innerSL_apply_apply] using
        h_id_l2.continuousLinearMap_comp (innerSL ℝ (A.adjoint (b i)))
    have hlin_int :
        Integrable
          (fun u : EuclideanSpace ℝ ι =>
            inner ℝ (A.adjoint (b i)) u * inner ℝ (A.adjoint (b i)) u)
          (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) :=
      hlin_l2.integrable_mul hlin_l2
    exact hlin_int.congr (Filter.Eventually.of_forall fun u => by
      simp [ContinuousLinearMap.adjoint_inner_left])
  have hnorm : ∀ u : EuclideanSpace ℝ ι,
      ‖A u‖ ^ 2 =
        ∑ i, inner ℝ (b i) (A u) * inner ℝ (b i) (A u) := by
    intro u
    rw [← real_inner_self_eq_norm_sq]
    simpa [real_inner_comm (A u)] using
      (b.sum_inner_mul_inner (A u) (A u)).symm
  calc
    (∫ u : EuclideanSpace ℝ ι, ‖A u‖ ^ 2
        ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι))) =
        ∫ u : EuclideanSpace ℝ ι,
          ∑ i, inner ℝ (b i) (A u) * inner ℝ (b i) (A u)
          ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) := by
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hnorm)
    _ =
        ∑ i, ∫ u : EuclideanSpace ℝ ι,
          inner ℝ (b i) (A u) * inner ℝ (b i) (A u)
          ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) := by
      rw [MeasureTheory.integral_finset_sum]
      intro i _
      exact hcoord_int i
    _ =
        ∑ i, inner ℝ (A.adjoint (b i)) (A.adjoint (b i)) := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        (∫ u : EuclideanSpace ℝ ι,
          inner ℝ (b i) (A u) * inner ℝ (b i) (A u)
          ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι))) =
            ∫ u : EuclideanSpace ℝ ι,
              inner ℝ (A.adjoint (b i)) u * inner ℝ (A.adjoint (b i)) u
              ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) := by
          exact MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall fun u => by
              simp [ContinuousLinearMap.adjoint_inner_left])
        _ = inner ℝ (A.adjoint (b i)) (A.adjoint (b i)) := by
          exact integral_inner_mul_inner_stdGaussian _ _
    _ = ∑ i, ‖A.adjoint (EuclideanSpace.basisFun ι ℝ i)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [real_inner_self_eq_norm_sq]
      rfl

private theorem sum_norm_sq_toEuclideanCLM_adjoint_basisFun_eq_trace_mul_conjTranspose
    (A : Matrix ι ι ℝ) :
    (∑ i, ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) A).adjoint
        (EuclideanSpace.basisFun ι ℝ i)‖ ^ 2) =
      (A * Aᴴ).trace := by
  classical
  have hadj :
      (Matrix.toEuclideanCLM (𝕜 := ℝ) A).adjoint =
        Matrix.toEuclideanCLM (𝕜 := ℝ) Aᴴ := by
    change (Matrix.toEuclideanLin A).toContinuousLinearMap.adjoint =
      (Matrix.toEuclideanLin Aᴴ).toContinuousLinearMap
    rw [← LinearMap.adjoint_toContinuousLinearMap]
    exact congrArg LinearMap.toContinuousLinearMap
      (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (𝕜 := ℝ) A).symm
  rw [hadj]
  calc
    (∑ i, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Aᴴ
        (EuclideanSpace.basisFun ι ℝ i)‖ ^ 2) =
        ∑ i, ∑ j,
          (Matrix.toEuclideanCLM (𝕜 := ℝ) Aᴴ
            (EuclideanSpace.basisFun ι ℝ i) j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact (euclidean_sum_sq_eq_norm_sq
        (Matrix.toEuclideanCLM (𝕜 := ℝ) Aᴴ
          (EuclideanSpace.basisFun ι ℝ i))).symm
    _ = ∑ i, ∑ j, A i j * A i j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose, pow_two]
    _ = (A * Aᴴ).trace := by
      simp [Matrix.mul_apply, Matrix.trace, Matrix.conjTranspose, dotProduct]

private theorem toEuclideanCLM_comp
    (A B : Matrix ι ι ℝ) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) A).comp
        (Matrix.toEuclideanCLM (𝕜 := ℝ) B) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (A * B) := by
  ext x
  simp [ContinuousLinearMap.comp_apply, Matrix.mulVec_mulVec]

private theorem norm_sq_toEuclideanCLM_eq_dotProduct_mulVec_of_transpose_mul_self
    (B M : Matrix ι ι ℝ)
    (hBt : Bᵀ = B) (hBsq : B * B = M)
    (x : EuclideanSpace ℝ ι) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) B x‖ ^ 2 =
      x ⬝ᵥ (M *ᵥ x) := by
  rw [← real_inner_self_eq_norm_sq]
  rw [Matrix.inner_toEuclideanCLM]
  simp only [Matrix.ofLp_toEuclideanCLM]
  rw [Matrix.dotProduct_mulVec]
  rw [Matrix.vecMul_mulVec]
  rw [hBt, hBsq]
  rw [← Matrix.dotProduct_mulVec]

private theorem sqrt_inv_mean_quadratic_term
    (muq mup : EuclideanSpace ℝ ι)
    (Sigmap : PositiveDefiniteCovariance ι) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
        ((CFC.sqrt (Sigmap : Matrix ι ι ℝ))⁻¹) (muq - mup)‖ ^ 2 =
      (mup - muq) ⬝ᵥ
        ((Sigmap : Matrix ι ι ℝ)⁻¹ *ᵥ (mup - muq)) := by
  classical
  let B : Matrix ι ι ℝ := (CFC.sqrt (Sigmap : Matrix ι ι ℝ))⁻¹
  have hBt : Bᵀ = B := by
    have hB_herm : B.IsHermitian := by
      exact (Matrix.PosDef.posDef_sqrt Sigmap.posDef).isHermitian.inv
    simpa [B, Matrix.conjTranspose] using hB_herm.eq
  have hB_sq : B * B = (Sigmap : Matrix ι ι ℝ)⁻¹ := by
    dsimp [B]
    rw [← Matrix.mul_inv_rev (CFC.sqrt (Sigmap : Matrix ι ι ℝ))
      (CFC.sqrt (Sigmap : Matrix ι ι ℝ))]
    rw [show CFC.sqrt (Sigmap : Matrix ι ι ℝ) *
        CFC.sqrt (Sigmap : Matrix ι ι ℝ) = (Sigmap : Matrix ι ι ℝ) by
      simpa [pow_two] using
        (CFC.sqrt_mul_sqrt_self (Sigmap : Matrix ι ι ℝ)
          Sigmap.posDef.posSemidef.nonneg)]
  calc
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
        ((CFC.sqrt (Sigmap : Matrix ι ι ℝ))⁻¹) (muq - mup)‖ ^ 2 =
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) B (-(mup - muq))‖ ^ 2 := by
      simp [B]
    _ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) B (mup - muq)‖ ^ 2 := by
      rw [map_neg, norm_neg]
    _ = (mup - muq) ⬝ᵥ
        ((Sigmap : Matrix ι ι ℝ)⁻¹ *ᵥ (mup - muq)) := by
      simpa using
        norm_sq_toEuclideanCLM_eq_dotProduct_mulVec_of_transpose_mul_self
          B ((Sigmap : Matrix ι ι ℝ)⁻¹) hBt hB_sq (mup - muq)

private theorem sqrt_inv_covariance_trace_term
    (Sigmaq Sigmap : PositiveDefiniteCovariance ι) :
    (∑ i,
        ‖((Matrix.toEuclideanCLM (𝕜 := ℝ)
            ((CFC.sqrt (Sigmap : Matrix ι ι ℝ))⁻¹)).comp
            (Matrix.toEuclideanCLM (𝕜 := ℝ)
              (CFC.sqrt (Sigmaq : Matrix ι ι ℝ)))).adjoint
          (EuclideanSpace.basisFun ι ℝ i)‖ ^ 2) =
      ((Sigmap : Matrix ι ι ℝ)⁻¹ * (Sigmaq : Matrix ι ι ℝ)).trace := by
  classical
  let B : Matrix ι ι ℝ := (CFC.sqrt (Sigmap : Matrix ι ι ℝ))⁻¹
  let C : Matrix ι ι ℝ := CFC.sqrt (Sigmaq : Matrix ι ι ℝ)
  have hcomp :
      (Matrix.toEuclideanCLM (𝕜 := ℝ)
          ((CFC.sqrt (Sigmap : Matrix ι ι ℝ))⁻¹)).comp
          (Matrix.toEuclideanCLM (𝕜 := ℝ)
            (CFC.sqrt (Sigmaq : Matrix ι ι ℝ))) =
        Matrix.toEuclideanCLM (𝕜 := ℝ) (B * C) := by
    simpa [B, C] using toEuclideanCLM_comp B C
  rw [hcomp]
  rw [sum_norm_sq_toEuclideanCLM_adjoint_basisFun_eq_trace_mul_conjTranspose]
  have hB_herm : Bᴴ = B := by
    have h : B.IsHermitian := by
      exact (Matrix.PosDef.posDef_sqrt Sigmap.posDef).isHermitian.inv
    exact h.eq
  have hC_herm : Cᴴ = C := by
    have h : C.IsHermitian := by
      exact (Matrix.PosDef.posDef_sqrt Sigmaq.posDef).isHermitian
    exact h.eq
  have hC_sq : C * C = (Sigmaq : Matrix ι ι ℝ) := by
    simpa [C, pow_two] using
      (CFC.sqrt_mul_sqrt_self (Sigmaq : Matrix ι ι ℝ)
        Sigmaq.posDef.posSemidef.nonneg)
  have hB_sq : B * B = (Sigmap : Matrix ι ι ℝ)⁻¹ := by
    dsimp [B]
    rw [← Matrix.mul_inv_rev (CFC.sqrt (Sigmap : Matrix ι ι ℝ))
      (CFC.sqrt (Sigmap : Matrix ι ι ℝ))]
    rw [show CFC.sqrt (Sigmap : Matrix ι ι ℝ) *
        CFC.sqrt (Sigmap : Matrix ι ι ℝ) = (Sigmap : Matrix ι ι ℝ) by
      simpa [pow_two] using
        (CFC.sqrt_mul_sqrt_self (Sigmap : Matrix ι ι ℝ)
          Sigmap.posDef.posSemidef.nonneg)]
  calc
    ((B * C) * (B * C)ᴴ).trace = (B * (C * C) * B).trace := by
      rw [Matrix.conjTranspose_mul, hB_herm, hC_herm]
      simp [Matrix.mul_assoc]
    _ = (B * B * (C * C)).trace := by
      simpa [Matrix.mul_assoc] using (Matrix.trace_mul_cycle B (C * C) B)
    _ = ((Sigmap : Matrix ι ι ℝ)⁻¹ * (Sigmaq : Matrix ι ι ℝ)).trace := by
      rw [hB_sq, hC_sq]

private theorem toEuclideanCLM_det_eq_matrix_det (A : Matrix ι ι ℝ) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) A).det = A.det := by
  change LinearMap.det
      ((Matrix.toEuclideanCLM (𝕜 := ℝ) A :
          EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :
        EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) = A.det
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  rw [LinearMap.det_toLin]

private theorem positiveDefiniteCovariance_sqrt_det_sq_eq_det
    (Sigma : PositiveDefiniteCovariance ι) :
    (CFC.sqrt (Sigma : Matrix ι ι ℝ)).det ^ 2 =
      (Sigma : Matrix ι ι ℝ).det := by
  have hsqrt :
      (CFC.sqrt (Sigma : Matrix ι ι ℝ)).det =
        Real.sqrt (Sigma : Matrix ι ι ℝ).det := by
    simpa using
      (Matrix.PosSemidef.det_sqrt (A := (Sigma : Matrix ι ι ℝ)) Sigma.posDef.posSemidef)
  rw [hsqrt]
  exact Real.sq_sqrt (le_of_lt (PositiveDefiniteCovariance.det_pos Sigma))

private theorem log_jacobian_const_eq_neg_log_sqrt_det
    (Sigma : PositiveDefiniteCovariance ι) :
    Real.log
        (ENNReal.ofReal
          |(Matrix.toEuclideanCLM (𝕜 := ℝ)
              (CFC.sqrt (Sigma : Matrix ι ι ℝ))).det⁻¹|).toReal =
      -Real.log (CFC.sqrt (Sigma : Matrix ι ι ℝ)).det := by
  let L : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (Sigma : Matrix ι ι ℝ))
  have hL_pos : 0 < L.det := by
    simpa [L] using
      (by
        rw [toEuclideanCLM_det_eq_matrix_det
          (A := CFC.sqrt (Sigma : Matrix ι ι ℝ))]
        exact positiveDefiniteCovariance_sqrt_det_pos Sigma)
  calc
    Real.log
        (ENNReal.ofReal
          |(Matrix.toEuclideanCLM (𝕜 := ℝ)
              (CFC.sqrt (Sigma : Matrix ι ι ℝ))).det⁻¹|).toReal =
        Real.log |L.det⁻¹| := by
      simp [L, ENNReal.toReal_ofReal, abs_nonneg]
    _ = Real.log L.det⁻¹ := by
      rw [abs_of_pos (inv_pos.mpr hL_pos)]
    _ = -Real.log L.det := by
      rw [Real.log_inv]
    _ = -Real.log (CFC.sqrt (Sigma : Matrix ι ι ℝ)).det := by
      have hdet := toEuclideanCLM_det_eq_matrix_det
        (A := CFC.sqrt (Sigma : Matrix ι ι ℝ))
      simpa [L] using congrArg (fun t : ℝ => -Real.log t) hdet

private theorem log_jacobian_const_sub_eq_half_log_det_ratio
    (Sigmaq Sigmap : PositiveDefiniteCovariance ι) :
    Real.log
        (ENNReal.ofReal
          |(Matrix.toEuclideanCLM (𝕜 := ℝ)
              (CFC.sqrt (Sigmaq : Matrix ι ι ℝ))).det⁻¹|).toReal -
      Real.log
        (ENNReal.ofReal
          |(Matrix.toEuclideanCLM (𝕜 := ℝ)
              (CFC.sqrt (Sigmap : Matrix ι ι ℝ))).det⁻¹|).toReal =
      (1 / 2 : ℝ) *
        Real.log ((Sigmap : Matrix ι ι ℝ).det / (Sigmaq : Matrix ι ι ℝ).det) := by
  rw [log_jacobian_const_eq_neg_log_sqrt_det Sigmaq,
    log_jacobian_const_eq_neg_log_sqrt_det Sigmap]
  have hqdet_pos : 0 < (Sigmaq : Matrix ι ι ℝ).det :=
    PositiveDefiniteCovariance.det_pos Sigmaq
  have hpdet_pos : 0 < (Sigmap : Matrix ι ι ℝ).det :=
    PositiveDefiniteCovariance.det_pos Sigmap
  have hqlog :
      Real.log (Sigmaq : Matrix ι ι ℝ).det =
        2 * Real.log (CFC.sqrt (Sigmaq : Matrix ι ι ℝ)).det := by
    rw [← positiveDefiniteCovariance_sqrt_det_sq_eq_det Sigmaq, Real.log_pow]
    norm_num
  have hplog :
      Real.log (Sigmap : Matrix ι ι ℝ).det =
        2 * Real.log (CFC.sqrt (Sigmap : Matrix ι ι ℝ)).det := by
    rw [← positiveDefiniteCovariance_sqrt_det_sq_eq_det Sigmap, Real.log_pow]
    norm_num
  rw [Real.log_div (ne_of_gt hpdet_pos) (ne_of_gt hqdet_pos), hplog, hqlog]
  ring

private theorem multivariateNormalLaw_equivalent_volume
    (mu : EuclideanSpace ℝ ι) (Sigma : PositiveDefiniteCovariance ι) :
    multivariateNormalLaw mu Sigma ≪
        (volume : MeasureTheory.Measure (EuclideanSpace ℝ ι)) ∧
      (volume : MeasureTheory.Measure (EuclideanSpace ℝ ι)) ≪
        multivariateNormalLaw mu Sigma := by
  constructor
  · exact (multivariateNormalLaw_absolutelyContinuous_affine_volume mu Sigma
      stdGaussian_euclidean_equivalent_volume.1).trans
      (multivariateNormal_affine_volume_equivalent mu Sigma).1
  · have h_affine_law :
        (volume : Measure (EuclideanSpace ℝ ι)).map
            (fun x : EuclideanSpace ℝ ι =>
              mu + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (Sigma : Matrix ι ι ℝ)) x) ≪
          multivariateNormalLaw mu Sigma := by
      rw [multivariateNormalLaw_eq_map_stdGaussian]
      exact stdGaussian_euclidean_equivalent_volume.2.map
        (Continuous.measurable (continuous_const.add
            (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (Sigma : Matrix ι ι ℝ))).continuous))
    exact (multivariateNormal_affine_volume_equivalent mu Sigma).2.trans h_affine_law

private theorem llr_eq_log_rnDeriv_div_common_dominating_ae
    {α : Type*} [MeasurableSpace α] {μ ν κ : Measure α}
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite κ]
    (hμν : μ ≪ ν) (hμκ : μ ≪ κ) (hνκ : ν ≪ κ) :
    MeasureTheory.llr μ ν =ᵐ[μ]
      fun x => Real.log ((μ.rnDeriv κ x / ν.rnDeriv κ x).toReal) := by
  have hdiv :
      μ.rnDeriv ν =ᵐ[ν] fun x => μ.rnDeriv κ x / ν.rnDeriv κ x :=
    Measure.rnDeriv_eq_div hμκ hνκ
  filter_upwards [hμν.ae_eq hdiv] with x hx
  rw [MeasureTheory.llr, hx]

set_option maxHeartbeats 800000

/-- Analytic Gaussian-density bridge for Dziugaite--Roy Eq. (1).
The source paper cites the positive-definite multivariate normal KL formula as
standard.  On the Mathlib side, the remaining content is exactly that the
measure-level log-likelihood ratio is integrable under the `q` law and that
its real integral is the displayed determinant/trace/quadratic expression. -/
private theorem multivariateNormalLaw_llr_integrable_and_integral_eq_closedForm
    (muq mup : EuclideanSpace ℝ ι)
    (Sigmaq Sigmap : PositiveDefiniteCovariance ι) :
    Integrable
        (MeasureTheory.llr (multivariateNormalLaw muq Sigmaq)
          (multivariateNormalLaw mup Sigmap))
        (multivariateNormalLaw muq Sigmaq) ∧
      ∫ x, MeasureTheory.llr (multivariateNormalLaw muq Sigmaq)
            (multivariateNormalLaw mup Sigmap) x ∂(multivariateNormalLaw muq Sigmaq) =
        multivariateNormalKLClosedForm muq mup Sigmaq Sigmap := by
  classical
  let μ := multivariateNormalLaw muq Sigmaq
  let ν := multivariateNormalLaw mup Sigmap
  have hq_vol := multivariateNormalLaw_equivalent_volume muq Sigmaq
  have hp_vol := multivariateNormalLaw_equivalent_volume mup Sigmap
  have hac : μ ≪ ν := by
    simpa [μ, ν] using hq_vol.1.trans hp_vol.2
  have hμprob : IsProbabilityMeasure μ := by
    simpa [μ] using multivariateNormalLaw_isProbabilityMeasure muq Sigmaq
  have hνprob : IsProbabilityMeasure ν := by
    simpa [ν] using multivariateNormalLaw_isProbabilityMeasure mup Sigmap
  have hllr_volume :
      MeasureTheory.llr μ ν =ᵐ[μ]
        fun x => Real.log ((μ.rnDeriv
          (volume : Measure (EuclideanSpace ℝ ι)) x /
            ν.rnDeriv (volume : Measure (EuclideanSpace ℝ ι)) x).toReal) := by
    exact llr_eq_log_rnDeriv_div_common_dominating_ae
      (μ := μ) (ν := ν) (κ := (volume : Measure (EuclideanSpace ℝ ι)))
      hac (by simpa [μ] using hq_vol.1) (by simpa [ν] using hp_vol.1)
  have hllr_of_volume_densities :
      ∀ f g : EuclideanSpace ℝ ι → ℝ≥0∞,
        μ.rnDeriv (volume : Measure (EuclideanSpace ℝ ι)) =ᵐ[
            (volume : Measure (EuclideanSpace ℝ ι))] f →
        ν.rnDeriv (volume : Measure (EuclideanSpace ℝ ι)) =ᵐ[
            (volume : Measure (EuclideanSpace ℝ ι))] g →
        MeasureTheory.llr μ ν =ᵐ[μ]
          fun x => Real.log ((f x / g x).toReal) := by
    intro f g hf hg
    refine hllr_volume.trans ?_
    have hμ_vol : μ ≪ (volume : Measure (EuclideanSpace ℝ ι)) := by
      simpa [μ] using hq_vol.1
    filter_upwards [hμ_vol.ae_eq hf, hμ_vol.ae_eq hg] with x hfx hgx
    rw [hfx, hgx]
  rcases multivariateNormalLaw_rnDeriv_volume_eq_density_affine muq Sigmaq with
    ⟨eq, heq_apply, hfq_rn⟩
  rcases multivariateNormalLaw_rnDeriv_volume_eq_density_affine mup Sigmap with
    ⟨ep, hep_apply, hfp_rn⟩
  let fq : EuclideanSpace ℝ ι → ℝ≥0∞ :=
    fun y =>
      ENNReal.ofReal
          |(Matrix.toEuclideanCLM (𝕜 := ℝ)
              (CFC.sqrt (Sigmaq : Matrix ι ι ℝ))).det⁻¹| *
        ∏ i, ProbabilityTheory.gaussianPDF 0 (1 : NNReal) ((eq.symm y) i)
  let fp : EuclideanSpace ℝ ι → ℝ≥0∞ :=
    fun y =>
      ENNReal.ofReal
          |(Matrix.toEuclideanCLM (𝕜 := ℝ)
              (CFC.sqrt (Sigmap : Matrix ι ι ℝ))).det⁻¹| *
        ∏ i, ProbabilityTheory.gaussianPDF 0 (1 : NNReal) ((ep.symm y) i)
  have hllr_density :
      MeasureTheory.llr μ ν =ᵐ[μ]
        fun x => Real.log ((fq x / fp x).toReal) := by
    exact hllr_of_volume_densities fq fp
      (by simpa [μ, fq] using hfq_rn)
      (by simpa [ν, fp] using hfp_rn)
  have hfq_pos : ∀ x : EuclideanSpace ℝ ι, 0 < fq x := by
    intro x
    have hdet_factor :
        0 < ENNReal.ofReal
          |(Matrix.toEuclideanCLM (𝕜 := ℝ)
              (CFC.sqrt (Sigmaq : Matrix ι ι ℝ))).det⁻¹| := by
      exact ENNReal.ofReal_pos.mpr
        (abs_pos.mpr
          (inv_ne_zero
            (positiveDefiniteCovariance_sqrt_toEuclideanCLM_det_ne_zero Sigmaq)))
    have hprod :
        0 < ∏ i, ProbabilityTheory.gaussianPDF 0 (1 : NNReal) ((eq.symm x) i) := by
      exact pos_iff_ne_zero.mpr
        (Finset.prod_ne_zero_iff.mpr (fun i hi =>
          ne_of_gt
            (ProbabilityTheory.gaussianPDF_pos 0
              (one_ne_zero : (1 : NNReal) ≠ 0) ((eq.symm x) i))))
    simpa [fq] using (ENNReal.mul_pos_iff.2 ⟨hdet_factor, hprod⟩)
  have hfq_ne_top : ∀ x : EuclideanSpace ℝ ι, fq x ≠ ∞ := by
    intro x
    have hprod :
        (∏ i, ProbabilityTheory.gaussianPDF 0 (1 : NNReal) ((eq.symm x) i)) ≠ ∞ := by
      simpa using
        (WithTop.prod_ne_top (s := (Finset.univ : Finset ι))
          (f := fun i => ProbabilityTheory.gaussianPDF 0 (1 : NNReal) ((eq.symm x) i))
          (fun i hi => ProbabilityTheory.gaussianPDF_ne_top (x := ((eq.symm x) i))))
    simpa [fq] using
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hprod)
  have hfp_pos : ∀ x : EuclideanSpace ℝ ι, 0 < fp x := by
    intro x
    have hdet_factor :
        0 < ENNReal.ofReal
          |(Matrix.toEuclideanCLM (𝕜 := ℝ)
              (CFC.sqrt (Sigmap : Matrix ι ι ℝ))).det⁻¹| := by
      exact ENNReal.ofReal_pos.mpr
        (abs_pos.mpr
          (inv_ne_zero
            (positiveDefiniteCovariance_sqrt_toEuclideanCLM_det_ne_zero Sigmap)))
    have hprod :
        0 < ∏ i, ProbabilityTheory.gaussianPDF 0 (1 : NNReal) ((ep.symm x) i) := by
      exact pos_iff_ne_zero.mpr
        (Finset.prod_ne_zero_iff.mpr (fun i hi =>
          ne_of_gt
            (ProbabilityTheory.gaussianPDF_pos 0
              (one_ne_zero : (1 : NNReal) ≠ 0) ((ep.symm x) i))))
    simpa [fp] using (ENNReal.mul_pos_iff.2 ⟨hdet_factor, hprod⟩)
  have hfp_ne_top : ∀ x : EuclideanSpace ℝ ι, fp x ≠ ∞ := by
    intro x
    have hprod :
        (∏ i, ProbabilityTheory.gaussianPDF 0 (1 : NNReal) ((ep.symm x) i)) ≠ ∞ := by
      simpa using
        (WithTop.prod_ne_top (s := (Finset.univ : Finset ι))
          (f := fun i => ProbabilityTheory.gaussianPDF 0 (1 : NNReal) ((ep.symm x) i))
          (fun i hi => ProbabilityTheory.gaussianPDF_ne_top (x := ((ep.symm x) i))))
    simpa [fp] using
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hprod)
  have hfq_toReal_pos : ∀ x : EuclideanSpace ℝ ι, 0 < (fq x).toReal := by
    intro x
    exact ENNReal.toReal_pos (ne_of_gt (hfq_pos x)) (hfq_ne_top x)
  have hfp_toReal_pos : ∀ x : EuclideanSpace ℝ ι, 0 < (fp x).toReal := by
    intro x
    exact ENNReal.toReal_pos (ne_of_gt (hfp_pos x)) (hfp_ne_top x)
  have hllr_density_real :
      MeasureTheory.llr μ ν =ᵐ[μ]
        fun x => Real.log ((fq x).toReal / (fp x).toReal) := by
    refine hllr_density.trans ?_
    filter_upwards [] with x
    rw [ENNReal.toReal_div]
  have hllr_density_log_sub :
      MeasureTheory.llr μ ν =ᵐ[μ]
        fun x => Real.log (fq x).toReal - Real.log (fp x).toReal := by
    refine hllr_density_real.trans ?_
    filter_upwards [] with x
    rw [Real.log_div (ne_of_gt (hfq_toReal_pos x)) (ne_of_gt (hfp_toReal_pos x))]
  have hfq_log_expand : ∀ x : EuclideanSpace ℝ ι,
      Real.log (fq x).toReal =
        Real.log
            (ENNReal.ofReal
              |(Matrix.toEuclideanCLM (𝕜 := ℝ)
                  (CFC.sqrt (Sigmaq : Matrix ι ι ℝ))).det⁻¹|).toReal +
          ∑ i, Real.log
            (ProbabilityTheory.gaussianPDF 0 (1 : NNReal) ((eq.symm x) i)).toReal := by
    intro x
    let cq : ℝ≥0∞ :=
      ENNReal.ofReal
        |(Matrix.toEuclideanCLM (𝕜 := ℝ)
            (CFC.sqrt (Sigmaq : Matrix ι ι ℝ))).det⁻¹|
    let pq : ι → ℝ≥0∞ :=
      fun i => ProbabilityTheory.gaussianPDF 0 (1 : NNReal) ((eq.symm x) i)
    have hcq_pos : 0 < cq.toReal := by
      have hcq0 : cq ≠ 0 := by
        exact ne_of_gt
          (ENNReal.ofReal_pos.mpr
            (abs_pos.mpr
              (inv_ne_zero
                (positiveDefiniteCovariance_sqrt_toEuclideanCLM_det_ne_zero Sigmaq))))
      exact ENNReal.toReal_pos hcq0 ENNReal.ofReal_ne_top
    have hprod_ne_top : (∏ i, pq i) ≠ ∞ := by
      simpa [pq] using
        (WithTop.prod_ne_top (s := (Finset.univ : Finset ι))
          (f := pq)
          (fun i hi => ProbabilityTheory.gaussianPDF_ne_top (x := ((eq.symm x) i))))
    have hprod_pos : 0 < (∏ i, pq i) := by
      exact pos_iff_ne_zero.mpr
        (Finset.prod_ne_zero_iff.mpr (fun i hi =>
          ne_of_gt
            (ProbabilityTheory.gaussianPDF_pos 0
              (one_ne_zero : (1 : NNReal) ≠ 0) ((eq.symm x) i))))
    have hprod_toReal_pos : 0 < (∏ i, pq i).toReal :=
      ENNReal.toReal_pos (ne_of_gt hprod_pos) hprod_ne_top
    have hpq_toReal_ne : ∀ i ∈ (Finset.univ : Finset ι), (pq i).toReal ≠ 0 := by
      intro i hi
      exact ne_of_gt
        (ENNReal.toReal_pos
          (ne_of_gt
            (ProbabilityTheory.gaussianPDF_pos 0
              (one_ne_zero : (1 : NNReal) ≠ 0) ((eq.symm x) i)))
          (ProbabilityTheory.gaussianPDF_ne_top (x := ((eq.symm x) i))))
    calc
      Real.log (fq x).toReal =
          Real.log (cq.toReal * (∏ i, pq i).toReal) := by
        simp [fq, cq, pq, ENNReal.toReal_mul]
      _ = Real.log cq.toReal + Real.log (∏ i, pq i).toReal := by
        exact Real.log_mul (ne_of_gt hcq_pos) (ne_of_gt hprod_toReal_pos)
      _ = Real.log cq.toReal + ∑ i, Real.log (pq i).toReal := by
        rw [ENNReal.toReal_prod]
        rw [Real.log_prod hpq_toReal_ne]
      _ = Real.log
            (ENNReal.ofReal
              |(Matrix.toEuclideanCLM (𝕜 := ℝ)
                  (CFC.sqrt (Sigmaq : Matrix ι ι ℝ))).det⁻¹|).toReal +
          ∑ i, Real.log
            (ProbabilityTheory.gaussianPDF 0 (1 : NNReal) ((eq.symm x) i)).toReal := by
        rfl
  have hfp_log_expand : ∀ x : EuclideanSpace ℝ ι,
      Real.log (fp x).toReal =
        Real.log
            (ENNReal.ofReal
              |(Matrix.toEuclideanCLM (𝕜 := ℝ)
                  (CFC.sqrt (Sigmap : Matrix ι ι ℝ))).det⁻¹|).toReal +
          ∑ i, Real.log
            (ProbabilityTheory.gaussianPDF 0 (1 : NNReal) ((ep.symm x) i)).toReal := by
    intro x
    let cp : ℝ≥0∞ :=
      ENNReal.ofReal
        |(Matrix.toEuclideanCLM (𝕜 := ℝ)
            (CFC.sqrt (Sigmap : Matrix ι ι ℝ))).det⁻¹|
    let pp : ι → ℝ≥0∞ :=
      fun i => ProbabilityTheory.gaussianPDF 0 (1 : NNReal) ((ep.symm x) i)
    have hcp_pos : 0 < cp.toReal := by
      have hcp0 : cp ≠ 0 := by
        exact ne_of_gt
          (ENNReal.ofReal_pos.mpr
            (abs_pos.mpr
              (inv_ne_zero
                (positiveDefiniteCovariance_sqrt_toEuclideanCLM_det_ne_zero Sigmap))))
      exact ENNReal.toReal_pos hcp0 ENNReal.ofReal_ne_top
    have hprod_ne_top : (∏ i, pp i) ≠ ∞ := by
      simpa [pp] using
        (WithTop.prod_ne_top (s := (Finset.univ : Finset ι))
          (f := pp)
          (fun i hi => ProbabilityTheory.gaussianPDF_ne_top (x := ((ep.symm x) i))))
    have hprod_pos : 0 < (∏ i, pp i) := by
      exact pos_iff_ne_zero.mpr
        (Finset.prod_ne_zero_iff.mpr (fun i hi =>
          ne_of_gt
            (ProbabilityTheory.gaussianPDF_pos 0
              (one_ne_zero : (1 : NNReal) ≠ 0) ((ep.symm x) i))))
    have hprod_toReal_pos : 0 < (∏ i, pp i).toReal :=
      ENNReal.toReal_pos (ne_of_gt hprod_pos) hprod_ne_top
    have hpp_toReal_ne : ∀ i ∈ (Finset.univ : Finset ι), (pp i).toReal ≠ 0 := by
      intro i hi
      exact ne_of_gt
        (ENNReal.toReal_pos
          (ne_of_gt
            (ProbabilityTheory.gaussianPDF_pos 0
              (one_ne_zero : (1 : NNReal) ≠ 0) ((ep.symm x) i)))
          (ProbabilityTheory.gaussianPDF_ne_top (x := ((ep.symm x) i))))
    calc
      Real.log (fp x).toReal =
          Real.log (cp.toReal * (∏ i, pp i).toReal) := by
        simp [fp, cp, pp, ENNReal.toReal_mul]
      _ = Real.log cp.toReal + Real.log (∏ i, pp i).toReal := by
        exact Real.log_mul (ne_of_gt hcp_pos) (ne_of_gt hprod_toReal_pos)
      _ = Real.log cp.toReal + ∑ i, Real.log (pp i).toReal := by
        rw [ENNReal.toReal_prod]
        rw [Real.log_prod hpp_toReal_ne]
      _ = Real.log
            (ENNReal.ofReal
              |(Matrix.toEuclideanCLM (𝕜 := ℝ)
                  (CFC.sqrt (Sigmap : Matrix ι ι ℝ))).det⁻¹|).toReal +
          ∑ i, Real.log
            (ProbabilityTheory.gaussianPDF 0 (1 : NNReal) ((ep.symm x) i)).toReal := by
        rfl
  have hfq_log_expand_sq : ∀ x : EuclideanSpace ℝ ι,
      Real.log (fq x).toReal =
        Real.log
            (ENNReal.ofReal
              |(Matrix.toEuclideanCLM (𝕜 := ℝ)
                  (CFC.sqrt (Sigmaq : Matrix ι ι ℝ))).det⁻¹|).toReal +
          ∑ i,
            (-((eq.symm x) i) ^ 2 / 2 - Real.log (Real.sqrt (2 * Real.pi))) := by
    intro x
    calc
      Real.log (fq x).toReal =
          Real.log
              (ENNReal.ofReal
                |(Matrix.toEuclideanCLM (𝕜 := ℝ)
                    (CFC.sqrt (Sigmaq : Matrix ι ι ℝ))).det⁻¹|).toReal +
            ∑ i, Real.log
              (ProbabilityTheory.gaussianPDF 0 (1 : NNReal) ((eq.symm x) i)).toReal := by
        exact hfq_log_expand x
      _ =
          Real.log
              (ENNReal.ofReal
                |(Matrix.toEuclideanCLM (𝕜 := ℝ)
                    (CFC.sqrt (Sigmaq : Matrix ι ι ℝ))).det⁻¹|).toReal +
            ∑ i,
              (-((eq.symm x) i) ^ 2 / 2 - Real.log (Real.sqrt (2 * Real.pi))) := by
        congr 1
        exact Finset.sum_congr rfl (fun i hi => log_standardGaussianPDF_zero_one ((eq.symm x) i))
  have hfp_log_expand_sq : ∀ x : EuclideanSpace ℝ ι,
      Real.log (fp x).toReal =
        Real.log
            (ENNReal.ofReal
              |(Matrix.toEuclideanCLM (𝕜 := ℝ)
                  (CFC.sqrt (Sigmap : Matrix ι ι ℝ))).det⁻¹|).toReal +
          ∑ i,
            (-((ep.symm x) i) ^ 2 / 2 - Real.log (Real.sqrt (2 * Real.pi))) := by
    intro x
    calc
      Real.log (fp x).toReal =
          Real.log
              (ENNReal.ofReal
                |(Matrix.toEuclideanCLM (𝕜 := ℝ)
                    (CFC.sqrt (Sigmap : Matrix ι ι ℝ))).det⁻¹|).toReal +
            ∑ i, Real.log
              (ProbabilityTheory.gaussianPDF 0 (1 : NNReal) ((ep.symm x) i)).toReal := by
        exact hfp_log_expand x
      _ =
          Real.log
              (ENNReal.ofReal
                |(Matrix.toEuclideanCLM (𝕜 := ℝ)
                    (CFC.sqrt (Sigmap : Matrix ι ι ℝ))).det⁻¹|).toReal +
            ∑ i,
              (-((ep.symm x) i) ^ 2 / 2 - Real.log (Real.sqrt (2 * Real.pi))) := by
        congr 1
        exact Finset.sum_congr rfl (fun i hi => log_standardGaussianPDF_zero_one ((ep.symm x) i))
  have hllr_density_affine_squares :
      MeasureTheory.llr μ ν =ᵐ[μ]
        fun x =>
          (Real.log
              (ENNReal.ofReal
                |(Matrix.toEuclideanCLM (𝕜 := ℝ)
                    (CFC.sqrt (Sigmaq : Matrix ι ι ℝ))).det⁻¹|).toReal +
            ∑ i,
              (-((eq.symm x) i) ^ 2 / 2 - Real.log (Real.sqrt (2 * Real.pi)))) -
          (Real.log
              (ENNReal.ofReal
                |(Matrix.toEuclideanCLM (𝕜 := ℝ)
                    (CFC.sqrt (Sigmap : Matrix ι ι ℝ))).det⁻¹|).toReal +
            ∑ i,
              (-((ep.symm x) i) ^ 2 / 2 - Real.log (Real.sqrt (2 * Real.pi)))) := by
    refine hllr_density_log_sub.trans ?_
    filter_upwards [] with x
    rw [hfq_log_expand_sq x, hfp_log_expand_sq x]
  have hsum_log_standard :
      ∀ u : EuclideanSpace ℝ ι,
        (∑ i, (- (u i) ^ 2 / 2 - Real.log (Real.sqrt (2 * Real.pi)))) =
          -(1 / 2 : ℝ) * ∑ i, (u i) ^ 2 -
            (Fintype.card ι : ℝ) * Real.log (Real.sqrt (2 * Real.pi)) := by
    intro u
    have hsquares :
        (∑ i, - (u i) ^ 2 / 2) =
          -(1 / 2 : ℝ) * ∑ i, (u i) ^ 2 := by
      calc
        (∑ i, - (u i) ^ 2 / 2) =
            ∑ i, -(1 / 2 : ℝ) * (u i) ^ 2 := by
          exact Finset.sum_congr rfl (fun i hi => by ring)
        _ = -(1 / 2 : ℝ) * ∑ i, (u i) ^ 2 := by
          rw [Finset.mul_sum]
    rw [Finset.sum_sub_distrib, hsquares, Finset.sum_const]
    simp [nsmul_eq_mul]
  have hllr_density_affine_quadratic :
      MeasureTheory.llr μ ν =ᵐ[μ]
        fun x =>
          (Real.log
              (ENNReal.ofReal
                |(Matrix.toEuclideanCLM (𝕜 := ℝ)
                    (CFC.sqrt (Sigmaq : Matrix ι ι ℝ))).det⁻¹|).toReal -
            Real.log
              (ENNReal.ofReal
                |(Matrix.toEuclideanCLM (𝕜 := ℝ)
                    (CFC.sqrt (Sigmap : Matrix ι ι ℝ))).det⁻¹|).toReal) +
          (1 / 2 : ℝ) *
            ((∑ i, ((ep.symm x) i) ^ 2) - ∑ i, ((eq.symm x) i) ^ 2) := by
    refine hllr_density_affine_squares.trans ?_
    filter_upwards [] with x
    rw [hsum_log_standard (eq.symm x), hsum_log_standard (ep.symm x)]
    ring
  have hllr_density_affine_norms :
      MeasureTheory.llr μ ν =ᵐ[μ]
        fun x =>
          (Real.log
              (ENNReal.ofReal
                |(Matrix.toEuclideanCLM (𝕜 := ℝ)
                    (CFC.sqrt (Sigmaq : Matrix ι ι ℝ))).det⁻¹|).toReal -
            Real.log
              (ENNReal.ofReal
                |(Matrix.toEuclideanCLM (𝕜 := ℝ)
                    (CFC.sqrt (Sigmap : Matrix ι ι ℝ))).det⁻¹|).toReal) +
          (1 / 2 : ℝ) * (‖ep.symm x‖ ^ 2 - ‖eq.symm x‖ ^ 2) := by
    refine hllr_density_affine_quadratic.trans ?_
    filter_upwards [] with x
    rw [euclidean_sum_sq_eq_norm_sq (ep.symm x), euclidean_sum_sq_eq_norm_sq (eq.symm x)]
  have hμ_eq_map_eq :
      μ = (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)).map eq := by
    have heq_fun :
        (eq : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) =
          fun x : EuclideanSpace ℝ ι =>
            muq + Matrix.toEuclideanCLM (𝕜 := ℝ)
              (CFC.sqrt (Sigmaq : Matrix ι ι ℝ)) x := by
      funext x
      exact heq_apply x
    change multivariateNormalLaw muq Sigmaq =
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)).map eq
    rw [multivariateNormalLaw_eq_map_stdGaussian, ← heq_fun]
  have hμ_pullback_eq_std :
      μ.map eq.symm =
        ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι) := by
    rw [hμ_eq_map_eq]
    rw [Measure.map_map eq.symm.measurable eq.measurable]
    simp
  have heq_symm_affine : ∀ x : EuclideanSpace ℝ ι,
      muq + Matrix.toEuclideanCLM (𝕜 := ℝ)
        (CFC.sqrt (Sigmaq : Matrix ι ι ℝ)) (eq.symm x) = x := by
    intro x
    simpa [heq_apply (eq.symm x)] using (eq.apply_symm_apply x)
  have hep_symm_affine : ∀ x : EuclideanSpace ℝ ι,
      mup + Matrix.toEuclideanCLM (𝕜 := ℝ)
        (CFC.sqrt (Sigmap : Matrix ι ι ℝ)) (ep.symm x) = x := by
    intro x
    simpa [hep_apply (ep.symm x)] using (ep.apply_symm_apply x)
  have heq_symm_linear : ∀ x : EuclideanSpace ℝ ι,
      Matrix.toEuclideanCLM (𝕜 := ℝ)
        (CFC.sqrt (Sigmaq : Matrix ι ι ℝ)) (eq.symm x) = x - muq := by
    intro x
    have h := heq_symm_affine x
    calc
      Matrix.toEuclideanCLM (𝕜 := ℝ)
          (CFC.sqrt (Sigmaq : Matrix ι ι ℝ)) (eq.symm x) =
          (muq + Matrix.toEuclideanCLM (𝕜 := ℝ)
            (CFC.sqrt (Sigmaq : Matrix ι ι ℝ)) (eq.symm x)) - muq := by
        abel
      _ = x - muq := by
        rw [h]
  have hep_symm_linear : ∀ x : EuclideanSpace ℝ ι,
      Matrix.toEuclideanCLM (𝕜 := ℝ)
        (CFC.sqrt (Sigmap : Matrix ι ι ℝ)) (ep.symm x) = x - mup := by
    intro x
    have h := hep_symm_affine x
    calc
      Matrix.toEuclideanCLM (𝕜 := ℝ)
          (CFC.sqrt (Sigmap : Matrix ι ι ℝ)) (ep.symm x) =
          (mup + Matrix.toEuclideanCLM (𝕜 := ℝ)
            (CFC.sqrt (Sigmap : Matrix ι ι ℝ)) (ep.symm x)) - mup := by
        abel
      _ = x - mup := by
        rw [h]
  have hstd_norm_sq_integral :
      ∫ u : EuclideanSpace ℝ ι, ‖u‖ ^ 2
          ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι) =
        (Fintype.card ι : ℝ) := by
    simpa [Real.rpow_two, finrank_euclideanSpace] using
      (stdGaussianMoment_two (E := EuclideanSpace ℝ ι))
  have hq_centered_norm_sq_integral :
      ∫ x, ‖eq.symm x‖ ^ 2 ∂μ = (Fintype.card ι : ℝ) := by
    calc
      ∫ x, ‖eq.symm x‖ ^ 2 ∂μ =
          ∫ u, ‖u‖ ^ 2 ∂μ.map eq.symm := by
        rw [MeasureTheory.integral_map]
        · exact eq.symm.measurable.aemeasurable
        · have hcont :
              Continuous (fun u : EuclideanSpace ℝ ι => ‖u‖ ^ 2) := by
            exact (continuous_norm : Continuous (fun u : EuclideanSpace ℝ ι => ‖u‖)).pow 2
          exact hcont.aestronglyMeasurable
      _ = ∫ u : EuclideanSpace ℝ ι, ‖u‖ ^ 2
            ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι) := by
        rw [hμ_pullback_eq_std]
      _ = (Fintype.card ι : ℝ) := hstd_norm_sq_integral
  have hstd_norm_sq_integrable :
      Integrable (fun u : EuclideanSpace ℝ ι => ‖u‖ ^ 2)
        (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) := by
    have hL2 : MemLp (fun u : EuclideanSpace ℝ ι => u) 2
        (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) :=
      IsGaussian.memLp_two_id
    exact (MeasureTheory.memLp_two_iff_integrable_sq_norm hL2.aestronglyMeasurable).1 hL2
  have hq_centered_norm_sq_integrable :
      Integrable (fun x => ‖eq.symm x‖ ^ 2) μ := by
    rw [hμ_eq_map_eq]
    have hmeas :
        AEStronglyMeasurable (fun x : EuclideanSpace ℝ ι => ‖eq.symm x‖ ^ 2)
          ((ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)).map eq) := by
      exact ((eq.symm.measurable.norm.pow_const (2 : ℕ)).aestronglyMeasurable)
    have hbase :
        Integrable ((fun x : EuclideanSpace ℝ ι => ‖eq.symm x‖ ^ 2) ∘ eq)
          (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) := by
      simpa [Function.comp_def] using hstd_norm_sq_integrable
    exact
      (MeasureTheory.integrable_map_measure hmeas eq.measurable.aemeasurable).2 hbase
  let Lq : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (Sigmaq : Matrix ι ι ℝ))
  let Lp : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (Sigmap : Matrix ι ι ℝ))
  let Lpinv : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt (Sigmap : Matrix ι ι ℝ))⁻¹)
  have hLp_Lpinv : ∀ y : EuclideanSpace ℝ ι, Lp (Lpinv y) = y := by
    intro y
    apply WithLp.ofLp_injective 2
    have hunit : IsUnit (CFC.sqrt (Sigmap : Matrix ι ι ℝ)).det := by
      exact isUnit_iff_ne_zero.mpr (positiveDefiniteCovariance_sqrt_det_ne_zero Sigmap)
    simp [Lp, Lpinv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit]
  have hp_comp_apply : ∀ u : EuclideanSpace ℝ ι,
      ep.symm (eq u) = Lpinv ((muq - mup) + Lq u) := by
    intro u
    apply positiveDefiniteCovariance_sqrt_toEuclideanCLM_injective Sigmap
    calc
      Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (Sigmap : Matrix ι ι ℝ))
          (ep.symm (eq u)) =
          eq u - mup := hep_symm_linear (eq u)
      _ = (muq - mup) + Lq u := by
        rw [heq_apply u]
        simp [Lq]
        abel
      _ =
          Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (Sigmap : Matrix ι ι ℝ))
            (Lpinv ((muq - mup) + Lq u)) := by
        simpa [Lp] using (hLp_Lpinv ((muq - mup) + Lq u)).symm
  have hstd_id_l2 : MemLp (fun u : EuclideanSpace ℝ ι => u) 2
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) :=
    IsGaussian.memLp_two_id
  have hp_base_integrable :
      Integrable (fun u : EuclideanSpace ℝ ι => ‖ep.symm (eq u)‖ ^ 2)
        (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) := by
    have hmean_l2 : MemLp (fun _ : EuclideanSpace ℝ ι => (muq - mup)) (2 : ℝ≥0∞)
        (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) := by
      exact MeasureTheory.memLp_const (muq - mup)
    have hLq_l2 : MemLp (fun u : EuclideanSpace ℝ ι => Lq u) 2
        (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) := by
      simpa [Function.comp_def] using hstd_id_l2.continuousLinearMap_comp Lq
    have hsum_l2 : MemLp (fun u : EuclideanSpace ℝ ι => (muq - mup) + Lq u) 2
        (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) :=
      hmean_l2.add hLq_l2
    have hinv_l2 :
        MemLp (fun u : EuclideanSpace ℝ ι => Lpinv ((muq - mup) + Lq u)) 2
          (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) := by
      simpa [Function.comp_def] using hsum_l2.continuousLinearMap_comp Lpinv
    have hinv_int :
        Integrable (fun u : EuclideanSpace ℝ ι =>
          ‖Lpinv ((muq - mup) + Lq u)‖ ^ 2)
          (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) :=
      (MeasureTheory.memLp_two_iff_integrable_sq_norm hinv_l2.aestronglyMeasurable).1
        hinv_l2
    exact hinv_int.congr (Filter.Eventually.of_forall fun u => by simp [hp_comp_apply u])
  have hp_centered_norm_sq_integrable :
      Integrable (fun x => ‖ep.symm x‖ ^ 2) μ := by
    rw [hμ_eq_map_eq]
    have hmeas :
        AEStronglyMeasurable (fun x : EuclideanSpace ℝ ι => ‖ep.symm x‖ ^ 2)
          ((ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)).map eq) := by
      exact ((ep.symm.measurable.norm.pow_const (2 : ℕ)).aestronglyMeasurable)
    exact
      (MeasureTheory.integrable_map_measure hmeas eq.measurable.aemeasurable).2
        hp_base_integrable
  have hlog_const :
      (Real.log
          (ENNReal.ofReal
            |(Matrix.toEuclideanCLM (𝕜 := ℝ)
                (CFC.sqrt (Sigmaq : Matrix ι ι ℝ))).det⁻¹|).toReal -
        Real.log
          (ENNReal.ofReal
            |(Matrix.toEuclideanCLM (𝕜 := ℝ)
                (CFC.sqrt (Sigmap : Matrix ι ι ℝ))).det⁻¹|).toReal) =
        (1 / 2 : ℝ) *
          Real.log ((Sigmap : Matrix ι ι ℝ).det / (Sigmaq : Matrix ι ι ℝ).det) :=
    log_jacobian_const_sub_eq_half_log_det_ratio Sigmaq Sigmap
  have hquadratic_integrable :
      Integrable
        (fun x =>
          (1 / 2 : ℝ) * (‖ep.symm x‖ ^ 2 - ‖eq.symm x‖ ^ 2)) μ :=
    (hp_centered_norm_sq_integrable.sub hq_centered_norm_sq_integrable).const_mul (1 / 2 : ℝ)
  have hrhs_integrable :
      Integrable
        (fun x =>
          (Real.log
              (ENNReal.ofReal
                |(Matrix.toEuclideanCLM (𝕜 := ℝ)
                    (CFC.sqrt (Sigmaq : Matrix ι ι ℝ))).det⁻¹|).toReal -
            Real.log
              (ENNReal.ofReal
                |(Matrix.toEuclideanCLM (𝕜 := ℝ)
                    (CFC.sqrt (Sigmap : Matrix ι ι ℝ))).det⁻¹|).toReal) +
          (1 / 2 : ℝ) * (‖ep.symm x‖ ^ 2 - ‖eq.symm x‖ ^ 2)) μ := by
    exact (integrable_const _).add hquadratic_integrable
  constructor
  · exact hrhs_integrable.congr hllr_density_affine_norms.symm
  · have hp_centered_norm_sq_integral :
        ∫ x, ‖ep.symm x‖ ^ 2 ∂μ =
          ((Sigmap : Matrix ι ι ℝ)⁻¹ * (Sigmaq : Matrix ι ι ℝ)).trace +
            (mup - muq) ⬝ᵥ ((Sigmap : Matrix ι ι ℝ)⁻¹ *ᵥ (mup - muq)) := by
      calc
        ∫ x, ‖ep.symm x‖ ^ 2 ∂μ =
            ∫ u, ‖ep.symm (eq u)‖ ^ 2
              ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι) := by
          rw [hμ_eq_map_eq]
          rw [MeasureTheory.integral_map]
          · exact eq.measurable.aemeasurable
          · exact ((ep.symm.measurable.norm.pow_const (2 : ℕ)).aestronglyMeasurable)
        _ = ∫ u, ‖Lpinv ((muq - mup) + Lq u)‖ ^ 2
              ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι) := by
          exact MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall fun u => by simp [hp_comp_apply u])
        _ = ((Sigmap : Matrix ι ι ℝ)⁻¹ * (Sigmaq : Matrix ι ι ℝ)).trace +
              (mup - muq) ⬝ᵥ ((Sigmap : Matrix ι ι ℝ)⁻¹ *ᵥ (mup - muq)) := by
          have hdet :
              ‖Lpinv (muq - mup)‖ ^ 2 +
                  ∑ i,
                    ‖(Lpinv.comp Lq).adjoint
                      (EuclideanSpace.basisFun ι ℝ i)‖ ^ 2 =
                ((Sigmap : Matrix ι ι ℝ)⁻¹ * (Sigmaq : Matrix ι ι ℝ)).trace +
                  (mup - muq) ⬝ᵥ
                    ((Sigmap : Matrix ι ι ℝ)⁻¹ *ᵥ (mup - muq)) := by
            have hmean :
                ‖Lpinv (muq - mup)‖ ^ 2 =
                  (mup - muq) ⬝ᵥ
                    ((Sigmap : Matrix ι ι ℝ)⁻¹ *ᵥ (mup - muq)) := by
              simpa [Lpinv] using
                sqrt_inv_mean_quadratic_term muq mup Sigmap
            have htrace :
                ∑ i,
                    ‖(Lpinv.comp Lq).adjoint
                      (EuclideanSpace.basisFun ι ℝ i)‖ ^ 2 =
                  ((Sigmap : Matrix ι ι ℝ)⁻¹ * (Sigmaq : Matrix ι ι ℝ)).trace := by
              simpa [Lpinv, Lq] using
                sqrt_inv_covariance_trace_term Sigmaq Sigmap
            rw [hmean, htrace]
            ring
          calc
            (∫ u, ‖Lpinv ((muq - mup) + Lq u)‖ ^ 2
                ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)) =
                ∫ u, ‖Lpinv (muq - mup) + (Lpinv.comp Lq) u‖ ^ 2
                  ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι) := by
              exact MeasureTheory.integral_congr_ae
                (Filter.Eventually.of_forall fun u => by
                  change ‖Lpinv (muq - mup + Lq u)‖ ^ 2 =
                    ‖Lpinv (muq - mup) + (Lpinv.comp Lq) u‖ ^ 2
                  have hmap :
                      Lpinv (muq - mup + Lq u) =
                        Lpinv (muq - mup) + Lpinv (Lq u) :=
                    map_add Lpinv (muq - mup) (Lq u)
                  simpa [ContinuousLinearMap.comp_apply] using
                    congrArg (fun z => ‖z‖ ^ 2) hmap)
            _ =
                ‖Lpinv (muq - mup)‖ ^ 2 +
                  ∫ u, ‖(Lpinv.comp Lq) u‖ ^ 2
                    ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι) := by
              exact integral_norm_sq_add_clm_stdGaussian_split
                (Lpinv (muq - mup)) (Lpinv.comp Lq)
            _ =
                ‖Lpinv (muq - mup)‖ ^ 2 +
                  ∑ i,
                    ‖(Lpinv.comp Lq).adjoint
                      (EuclideanSpace.basisFun ι ℝ i)‖ ^ 2 := by
              rw [integral_norm_sq_clm_stdGaussian_eq_sum_adjoint_basisFun]
            _ =
                ((Sigmap : Matrix ι ι ℝ)⁻¹ * (Sigmaq : Matrix ι ι ℝ)).trace +
                  (mup - muq) ⬝ᵥ
                    ((Sigmap : Matrix ι ι ℝ)⁻¹ *ᵥ (mup - muq)) := hdet
    change ∫ x, MeasureTheory.llr μ ν x ∂μ =
      multivariateNormalKLClosedForm muq mup Sigmaq Sigmap
    calc
      ∫ x, MeasureTheory.llr μ ν x ∂μ =
          ∫ x,
            (Real.log
                (ENNReal.ofReal
                  |(Matrix.toEuclideanCLM (𝕜 := ℝ)
                      (CFC.sqrt (Sigmaq : Matrix ι ι ℝ))).det⁻¹|).toReal -
              Real.log
                (ENNReal.ofReal
                  |(Matrix.toEuclideanCLM (𝕜 := ℝ)
                      (CFC.sqrt (Sigmap : Matrix ι ι ℝ))).det⁻¹|).toReal) +
            (1 / 2 : ℝ) * (‖ep.symm x‖ ^ 2 - ‖eq.symm x‖ ^ 2) ∂μ :=
        MeasureTheory.integral_congr_ae hllr_density_affine_norms
      _ = (Real.log
              (ENNReal.ofReal
                |(Matrix.toEuclideanCLM (𝕜 := ℝ)
                    (CFC.sqrt (Sigmaq : Matrix ι ι ℝ))).det⁻¹|).toReal -
            Real.log
              (ENNReal.ofReal
                |(Matrix.toEuclideanCLM (𝕜 := ℝ)
                    (CFC.sqrt (Sigmap : Matrix ι ι ℝ))).det⁻¹|).toReal) +
          (1 / 2 : ℝ) *
            (((Sigmap : Matrix ι ι ℝ)⁻¹ * (Sigmaq : Matrix ι ι ℝ)).trace +
              (mup - muq) ⬝ᵥ ((Sigmap : Matrix ι ι ℝ)⁻¹ *ᵥ (mup - muq)) -
              (Fintype.card ι : ℝ)) := by
        rw [MeasureTheory.integral_add (integrable_const _) hquadratic_integrable]
        rw [MeasureTheory.integral_const_mul]
        rw [MeasureTheory.integral_sub hp_centered_norm_sq_integrable
          hq_centered_norm_sq_integrable]
        rw [hp_centered_norm_sq_integral, hq_centered_norm_sq_integral]
        simp [measureReal_def]
      _ = multivariateNormalKLClosedForm muq mup Sigmaq Sigmap := by
        refine Eq.trans ?_
          (multivariateNormalKLClosedForm_def muq mup Sigmaq Sigmap).symm
        rw [hlog_const]
        ring

/-- Source JSON `phase0_compat_source.json#/main_theorem`: Eq. (1), quoted as
`"assume Σ_q and Σ_p are positive definite. Then KL(N_q||N_p) is ..."`; source
PDF lines 195--212 contain the same displayed formula.  The equality is stated
in Mathlib's `ℝ≥0∞` KL codomain, with the paper's finite real expression lifted
by `ENNReal.ofReal`.  The nonnegativity conjunct records that this lift denotes
the displayed finite real value, rather than clipping a negative real. -/
theorem dziugaite_roy_2017_multivariateNormal_kl_closedForm_positiveDefinite
    (muq mup : EuclideanSpace ℝ ι)
    (Sigmaq Sigmap : PositiveDefiniteCovariance ι) :
    0 ≤ multivariateNormalKLClosedForm muq mup Sigmaq Sigmap ∧
      multivariateNormalKLDivergence muq mup Sigmaq Sigmap =
        multivariateNormalKLClosedFormENNReal muq mup Sigmaq Sigmap := by
  have hq_vol := multivariateNormalLaw_equivalent_volume muq Sigmaq
  have hp_vol := multivariateNormalLaw_equivalent_volume mup Sigmap
  have hac : multivariateNormalLaw muq Sigmaq ≪ multivariateNormalLaw mup Sigmap :=
    hq_vol.1.trans hp_vol.2
  let μ := multivariateNormalLaw muq Sigmaq
  let ν := multivariateNormalLaw mup Sigmap
  have hμprob : IsProbabilityMeasure μ := by
    simpa [μ] using multivariateNormalLaw_isProbabilityMeasure muq Sigmaq
  have hνprob : IsProbabilityMeasure ν := by
    simpa [ν] using multivariateNormalLaw_isProbabilityMeasure mup Sigmap
  have hllr :
      Integrable (MeasureTheory.llr μ ν) μ ∧
        ∫ x, MeasureTheory.llr μ ν x ∂μ =
          multivariateNormalKLClosedForm muq mup Sigmaq Sigmap := by
    simpa [μ, ν] using
      multivariateNormalLaw_llr_integrable_and_integral_eq_closedForm muq mup Sigmaq Sigmap
  constructor
  · have hnonneg := InformationTheory.integral_llr_add_sub_measure_univ_nonneg
      (μ := μ) (ν := ν) hac hllr.1
    have hμmass : μ.real Set.univ = 1 := by
      simp [measureReal_def]
    have hνmass : ν.real Set.univ = 1 := by
      simp [measureReal_def]
    nlinarith [hllr.2, hnonneg, hμmass, hνmass]
  · have hkl := InformationTheory.klDiv_of_ac_of_integrable
      (μ := μ) (ν := ν) hac hllr.1
    have hμmass : μ.real Set.univ = 1 := by
      simp [measureReal_def]
    have hνmass : ν.real Set.univ = 1 := by
      simp [measureReal_def]
    rw [multivariateNormalKLDivergence_def]
    rw [hkl]
    rw [hllr.2, hνmass, hμmass]
    norm_num

/-- Positive-definite Gaussian covariances put the paper KL value in the finite
part of Mathlib's `ℝ≥0∞` codomain. -/
theorem dziugaite_roy_2017_multivariateNormal_kl_closedForm_positiveDefinite_ne_top
    (muq mup : EuclideanSpace ℝ ι)
    (Sigmaq Sigmap : PositiveDefiniteCovariance ι) :
    multivariateNormalKLDivergence muq mup Sigmaq Sigmap ≠ ∞ := by
  rw [(dziugaite_roy_2017_multivariateNormal_kl_closedForm_positiveDefinite
    muq mup Sigmaq Sigmap).2]
  rw [multivariateNormalKLClosedFormENNReal_def]
  exact ENNReal.ofReal_ne_top

/-- Source JSON `phase0_compat_source.json#/main_theorem/measure`: the scalar
Gaussian KL leaf is obtained by specializing Eq. (1) to covariance matrices
`σ_Q^2 I` and `σ_P^2 I`. -/
def isotropicCovariance (sigma : ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal fun _ : ι => sigma ^ 2

/-- A positive scalar standard deviation gives the positive-definite isotropic
covariance used by the scalar specialization. -/
private theorem isotropicCovariance_posDef {ι : Type*} [DecidableEq ι] {sigma : ℝ} (hsigma : 0 < sigma) :
    (isotropicCovariance (ι := ι) sigma).PosDef := by
  rw [isotropicCovariance]
  exact Matrix.PosDef.diagonal (fun _ => sq_pos_of_pos hsigma)

/-- The canonical positive-definite covariance object for an isotropic Gaussian
with positive scalar standard deviation. -/
def isotropicPositiveDefiniteCovariance
    {ι : Type*} [Fintype ι] [DecidableEq ι] (sigma : ℝ) (hsigma : 0 < sigma) :
    PositiveDefiniteCovariance ι :=
  ⟨isotropicCovariance (ι := ι) sigma, isotropicCovariance_posDef hsigma⟩

/-- Source JSON `phase0_compat_source.json#/main_theorem/measure`: scalar
specialization with covariance matrices `σ_Q^2 I` and `σ_P^2 I`. -/
def isotropicGaussianKLClosedForm
    (muq mup : EuclideanSpace ℝ ι) (sigmaq sigmap : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ((Fintype.card ι : ℝ) *
        (sigmaq ^ 2 / sigmap ^ 2 - 1 +
          Real.log (sigmap ^ 2 / sigmaq ^ 2)) +
      ‖mup - muq‖ ^ 2 / sigmap ^ 2)

private theorem isotropicCovariance_det (sigma : ℝ) :
    (isotropicCovariance (ι := ι) sigma).det =
      (sigma ^ 2) ^ Fintype.card ι := by
  unfold isotropicCovariance
  rw [Matrix.det_diagonal, Finset.prod_const, Finset.card_univ]

private theorem ringInverse_const_fun_sq
    {sigma : ℝ} (hsigma : 0 < sigma) :
    Ring.inverse (fun _ : ι => sigma ^ 2) =
      fun _ : ι => (sigma ^ 2)⁻¹ := by
  have hsigma_sq_ne : sigma ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hsigma)
  have hunit : IsUnit (fun _ : ι => sigma ^ 2) := by
    rw [Pi.isUnit_iff]
    intro i
    exact isUnit_iff_ne_zero.mpr hsigma_sq_ne
  ext i
  rw [Ring.inverse_of_isUnit hunit]
  have hi := hunit.val_inv_apply i
  simpa using hi

private theorem isotropicCovariance_inv_mul_trace
    (sigmaq sigmap : ℝ) (hsigmap : 0 < sigmap) :
    (((isotropicCovariance (ι := ι) sigmap)⁻¹ *
        isotropicCovariance (ι := ι) sigmaq).trace) =
      (Fintype.card ι : ℝ) * (sigmaq ^ 2 / sigmap ^ 2) := by
  have hinv := ringInverse_const_fun_sq (ι := ι) hsigmap
  calc
    (((isotropicCovariance (ι := ι) sigmap)⁻¹ *
        isotropicCovariance (ι := ι) sigmaq).trace) =
        (Matrix.diagonal fun _ : ι => (sigmap ^ 2)⁻¹ * sigmaq ^ 2).trace := by
      simp [isotropicCovariance, Matrix.inv_diagonal, Matrix.diagonal_mul_diagonal,
        hinv]
    _ = ∑ _ : ι, (sigmap ^ 2)⁻¹ * sigmaq ^ 2 := by
      rw [Matrix.trace_diagonal]
    _ = (Fintype.card ι : ℝ) * ((sigmap ^ 2)⁻¹ * sigmaq ^ 2) := by
      rw [Finset.sum_const]
      simp [nsmul_eq_mul]
    _ = (Fintype.card ι : ℝ) * (sigmaq ^ 2 / sigmap ^ 2) := by
      ring

private theorem isotropicCovariance_inv_quadratic
    (x : EuclideanSpace ℝ ι) {sigma : ℝ} (hsigma : 0 < sigma) :
    x ⬝ᵥ (((isotropicCovariance (ι := ι) sigma)⁻¹) *ᵥ x) =
      ‖x‖ ^ 2 / sigma ^ 2 := by
  have hinv := ringInverse_const_fun_sq (ι := ι) hsigma
  calc
    x ⬝ᵥ (((isotropicCovariance (ι := ι) sigma)⁻¹) *ᵥ x) =
        ∑ i, x i * ((sigma ^ 2)⁻¹ * x i) := by
      simp [isotropicCovariance, Matrix.inv_diagonal, dotProduct,
        Matrix.mulVec_diagonal, hinv]
    _ = (sigma ^ 2)⁻¹ * ∑ i, (x i) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ‖x‖ ^ 2 / sigma ^ 2 := by
      rw [euclidean_sum_sq_eq_norm_sq]
      ring

private theorem isotropicCovariance_log_det_div
    {sigmaq sigmap : ℝ} (hsigmaq : 0 < sigmaq) (hsigmap : 0 < sigmap) :
    Real.log ((isotropicCovariance (ι := ι) sigmap).det /
        (isotropicCovariance (ι := ι) sigmaq).det) =
      (Fintype.card ι : ℝ) * Real.log (sigmap ^ 2 / sigmaq ^ 2) := by
  calc
    Real.log ((isotropicCovariance (ι := ι) sigmap).det /
        (isotropicCovariance (ι := ι) sigmaq).det) =
        Real.log (((sigmap ^ 2) ^ Fintype.card ι) /
          ((sigmaq ^ 2) ^ Fintype.card ι)) := by
      rw [isotropicCovariance_det, isotropicCovariance_det]
    _ = Real.log ((sigmap ^ 2 / sigmaq ^ 2) ^ Fintype.card ι) := by
      rw [← div_pow]
    _ = (Fintype.card ι : ℝ) * Real.log (sigmap ^ 2 / sigmaq ^ 2) := by
      rw [Real.log_pow]

/-- The scalar Gaussian KL formula is the matrix Eq. (1) specialized to
`σ_Q^2 I` and `σ_P^2 I`.  The matrix algebra is left for the prover phase. -/
private theorem isotropicGaussianKLClosedForm_eq_matrixClosedForm
    (muq mup : EuclideanSpace ℝ ι) {sigmaq sigmap : ℝ}
    (hsigmaq : 0 < sigmaq) (hsigmap : 0 < sigmap) :
    multivariateNormalKLClosedForm muq mup
        (isotropicPositiveDefiniteCovariance (ι := ι) sigmaq hsigmaq)
        (isotropicPositiveDefiniteCovariance (ι := ι) sigmap hsigmap) =
      isotropicGaussianKLClosedForm muq mup sigmaq sigmap := by
  change
    (1 / 2 : ℝ) *
      ((((isotropicCovariance (ι := ι) sigmap)⁻¹ *
            isotropicCovariance (ι := ι) sigmaq).trace) -
        (Fintype.card ι : ℝ) +
        (mup - muq) ⬝ᵥ
          (((isotropicCovariance (ι := ι) sigmap)⁻¹) *ᵥ (mup - muq)) +
        Real.log ((isotropicCovariance (ι := ι) sigmap).det /
          (isotropicCovariance (ι := ι) sigmaq).det)) =
      (1 / 2 : ℝ) *
        ((Fintype.card ι : ℝ) *
            (sigmaq ^ 2 / sigmap ^ 2 - 1 +
              Real.log (sigmap ^ 2 / sigmaq ^ 2)) +
          ‖mup - muq‖ ^ 2 / sigmap ^ 2)
  have hquad :
      (mup - muq).ofLp ⬝ᵥ
          ((isotropicCovariance (ι := ι) sigmap)⁻¹ *ᵥ
            (mup.ofLp - muq.ofLp)) =
        ‖mup - muq‖ ^ 2 / sigmap ^ 2 := by
    simpa using isotropicCovariance_inv_quadratic (mup - muq) hsigmap
  rw [isotropicCovariance_inv_mul_trace sigmaq sigmap hsigmap, hquad,
    isotropicCovariance_log_det_div hsigmaq hsigmap]
  ring

/-- Scalar form used downstream, exposed as a source-facing specialization of
Dziugaite--Roy Eq. (1) rather than as an independent witness formula. -/
theorem dziugaite_roy_2017_isotropicGaussian_kl_closedForm_positiveStd
    (muq mup : EuclideanSpace ℝ ι) {sigmaq sigmap : ℝ}
    (hsigmaq : 0 < sigmaq) (hsigmap : 0 < sigmap) :
    0 ≤ isotropicGaussianKLClosedForm muq mup sigmaq sigmap ∧
      multivariateNormalKLDivergence muq mup
          (isotropicPositiveDefiniteCovariance (ι := ι) sigmaq hsigmaq)
          (isotropicPositiveDefiniteCovariance (ι := ι) sigmap hsigmap) =
        ENNReal.ofReal (isotropicGaussianKLClosedForm muq mup sigmaq sigmap) := by
  let hmatrix :=
    dziugaite_roy_2017_multivariateNormal_kl_closedForm_positiveDefinite
      muq mup
      (isotropicPositiveDefiniteCovariance (ι := ι) sigmaq hsigmaq)
      (isotropicPositiveDefiniteCovariance (ι := ι) sigmap hsigmap)
  constructor
  · rw [← isotropicGaussianKLClosedForm_eq_matrixClosedForm muq mup hsigmaq hsigmap]
    exact hmatrix.1
  · rw [← isotropicGaussianKLClosedForm_eq_matrixClosedForm muq mup hsigmaq hsigmap,
      ← multivariateNormalKLClosedFormENNReal_def]
    exact hmatrix.2

end

end ExternalAdapter.Dziugaite_Roy_2017__theorem2AppendixA1GaussianKLFormulaScala
