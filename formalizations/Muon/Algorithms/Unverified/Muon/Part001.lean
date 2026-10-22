import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import SOptLib.Model.Objective
import SOptLib.Model.StochasticOracle
import SOptLib.Layer0.Objective
import SOptLib.Layer0.Oracle
import SOptLib.Glue.Probability

/-!
Complete-paper Muon task. See TASK.md and paper/Muon/source_manifest.json.

This Phase 0 file exposes the paper's object layer: matrix objectives, the
SVD/polar update direction used by Muon, Algorithm 1 stochastic iterates, and
Algorithm 2 deterministic iterates. Endpoint proofs are intentionally left to
later prover phases.
-/

noncomputable section

namespace SGD.Muon

open Matrix MeasureTheory Filter
open scoped BigOperators InnerProductSpace Matrix.Norms.Frobenius

abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

instance matMeasurableSpace (m n : ℕ) : MeasurableSpace (Mat m n) :=
  MeasurableSpace.pi

instance matBorelSpace (m n : ℕ) : BorelSpace (Mat m n) :=
  inferInstanceAs (BorelSpace (Fin m → Fin n → ℝ))

def matrixRankBound (m n : ℕ) : ℕ :=
  Nat.min m n

def frobeniusNorm {m n : ℕ} (A : Mat m n) : ℝ :=
  ‖A‖

def matrixToEuclidean {m n : ℕ} (A : Mat m n) :
    EuclideanSpace ℝ (Fin m × Fin n) :=
  WithLp.toLp 2 (fun p => A p.1 p.2)

theorem matrixToEuclidean_sub {m n : ℕ} (A B : Mat m n) :
    matrixToEuclidean (A - B) = matrixToEuclidean A - matrixToEuclidean B :=
  rfl

theorem norm_matrixToEuclidean {m n : ℕ} (A : Mat m n) :
    ‖matrixToEuclidean A‖ = frobeniusNorm A := by
  rw [frobeniusNorm, Matrix.frobenius_norm_def, PiLp.norm_eq_of_L2]
  simp only [matrixToEuclidean, WithLp.ofLp_toLp, Real.norm_eq_abs]
  rw [← Finset.sum_product']
  simp [Finset.univ_product_univ, Real.sqrt_eq_rpow, Real.rpow_two, pow_two]

noncomputable def matrixToEuclideanCLM {m n : ℕ} :
    Mat m n →L[ℝ] EuclideanSpace ℝ (Fin m × Fin n) :=
  LinearMap.mkContinuous
    { toFun := matrixToEuclidean
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun A => by
      change ‖matrixToEuclidean A‖ ≤ 1 * ‖A‖
      rw [norm_matrixToEuclidean]
      simp [frobeniusNorm])

@[simp] theorem matrixToEuclideanCLM_apply {m n : ℕ} (A : Mat m n) :
    matrixToEuclideanCLM A = matrixToEuclidean A :=
  rfl

theorem matrixToEuclidean_measurable {m n : ℕ} :
    Measurable (matrixToEuclidean : Mat m n → EuclideanSpace ℝ (Fin m × Fin n)) :=
  matrixToEuclideanCLM.continuous.measurable

def euclideanToMatrix {m n : ℕ}
    (x : EuclideanSpace ℝ (Fin m × Fin n)) : Mat m n :=
  fun i j => x (i, j)

noncomputable def matrixEuclideanLinearIsometryEquiv {m n : ℕ} :
    Mat m n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m × Fin n) :=
  { toLinearEquiv :=
      { toFun := matrixToEuclidean
        invFun := euclideanToMatrix
        left_inv := by intro A; rfl
        right_inv := by intro x; ext p; rfl
        map_add' := by intro A B; rfl
        map_smul' := by intro c A; rfl }
    norm_map' := norm_matrixToEuclidean }

@[simp] theorem matrixEuclideanLinearIsometryEquiv_apply {m n : ℕ} (A : Mat m n) :
    matrixEuclideanLinearIsometryEquiv A = matrixToEuclidean A :=
  rfl

def spectralNorm {m n : ℕ} (A : Mat m n) : ℝ :=
  ‖(Matrix.toEuclideanLin (𝕜 := ℝ) A).toContinuousLinearMap‖

def nuclearNorm {m n : ℕ} (A : Mat m n) : ℝ :=
  ∑ i : Fin n, (Matrix.toEuclideanLin (𝕜 := ℝ) A).singularValues i

def frobeniusInner {m n : ℕ} (A B : Mat m n) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, A i j * B i j

theorem inner_matrixToEuclidean {m n : ℕ} (A B : Mat m n) :
    ⟪matrixToEuclidean A, matrixToEuclidean B⟫_ℝ = frobeniusInner A B := by
  calc
    ⟪matrixToEuclidean A, matrixToEuclidean B⟫_ℝ =
        dotProduct (fun p : Fin m × Fin n => B p.1 p.2)
          (star (fun p : Fin m × Fin n => A p.1 p.2)) := by
            exact EuclideanSpace.inner_toLp_toLp _ _
    _ = frobeniusInner A B := by
      simp only [dotProduct, frobeniusInner, Pi.star_apply, star_trivial]
      rw [← Finset.sum_product']
      apply Finset.sum_congr rfl
      intro p _hp
      ring

structure Objective (m n : ℕ) where
  f : Mat m n → ℝ

def coordinateMatrix {m n : ℕ} (i : Fin m) (j : Fin n) : Mat m n :=
  Matrix.single i j (1 : ℝ)

noncomputable def objectiveGradient {m n : ℕ} (f : Mat m n → ℝ)
    (W : Mat m n) : Mat m n :=
  fun i j => fderiv ℝ f W (coordinateMatrix i j)

noncomputable def Objective.grad {m n : ℕ} (P : Objective m n) : Mat m n → Mat m n :=
  objectiveGradient P.f

noncomputable def Objective.fStar {m n : ℕ} (P : Objective m n) : ℝ :=
  sInf (Set.range P.f)

def Objective.HasFiniteInfimum {m n : ℕ} (P : Objective m n) : Prop :=
  BddBelow (Set.range P.f)

noncomputable def Objective.sourceFStar {m n : ℕ} (P : Objective m n)
    (_hfinite : P.HasFiniteInfimum) : ℝ :=
  P.fStar

def Objective.IsMinimizer {m n : ℕ} (P : Objective m n) (Wstar : Mat m n) : Prop :=
  P.f Wstar = P.fStar

theorem Objective.grad_eq_coordinate_fderiv {m n : ℕ} (P : Objective m n) (W : Mat m n) :
    P.grad W = fun i j => fderiv ℝ P.f W (coordinateMatrix i j) :=
  rfl

theorem objectiveGradient_measurable {m n : ℕ} (f : Mat m n → ℝ) :
    Measurable (objectiveGradient f) := by
  unfold objectiveGradient
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact measurable_fderiv_apply_const ℝ f (coordinateMatrix i j)

theorem Objective.grad_measurable {m n : ℕ} (P : Objective m n) :
    Measurable P.grad := by
  exact objectiveGradient_measurable P.f

def vectorizedObjective {m n : ℕ} (P : Objective m n) : Mat m n → ℝ :=
  P.f

theorem matrix_eq_sum_entries_smul_coordinateMatrix {m n : ℕ} (H : Mat m n) :
    H = ∑ i : Fin m, ∑ j : Fin n, H i j • coordinateMatrix i j := by
  classical
  ext i j
  change H i j =
    (∑ a : Fin m, ∑ b : Fin n, H a b • coordinateMatrix a b) i j
  simp only [Matrix.sum_apply]
  simp only [Pi.smul_apply, coordinateMatrix, Matrix.single_apply, Pi.single_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hbj
      simp [hbj]
    · simp
  · intro a _ hai
    simp [hai]
  · simp

theorem objective_fderiv_apply_eq_frobeniusInner_grad {m n : ℕ}
    (P : Objective m n) (W H : Mat m n) :
    fderiv ℝ (vectorizedObjective P) W H = frobeniusInner (P.grad W) H := by
  classical
  let L := fderiv ℝ (vectorizedObjective P) W
  have hH : H = ∑ i : Fin m, ∑ j : Fin n, H i j • coordinateMatrix i j :=
    matrix_eq_sum_entries_smul_coordinateMatrix H
  calc
    fderiv ℝ (vectorizedObjective P) W H =
        L (∑ i : Fin m, ∑ j : Fin n, H i j • coordinateMatrix i j) := by
          simpa [L] using congrArg L hH
    _ = ∑ i : Fin m, ∑ j : Fin n,
        H i j * fderiv ℝ (vectorizedObjective P) W (coordinateMatrix i j) := by
          simp [L, smul_eq_mul]
    _ = frobeniusInner (P.grad W) H := by
          simp [frobeniusInner, Objective.grad, objectiveGradient, vectorizedObjective,
            mul_comm, mul_left_comm, mul_assoc]

theorem Objective.fStar_eq_infimum {m n : ℕ} (P : Objective m n) :
    P.fStar = sInf (Set.range P.f) :=
  rfl

theorem Objective.sourceFStar_eq_infimum {m n : ℕ} (P : Objective m n)
    (hfinite : P.HasFiniteInfimum) :
    P.sourceFStar hfinite = sInf (Set.range P.f) :=
  rfl

theorem Objective.sourceFStar_eq_fStar {m n : ℕ} (P : Objective m n)
    (hfinite : P.HasFiniteInfimum) :
    P.sourceFStar hfinite = P.fStar :=
  rfl

def vectorizedMatrix {m n : ℕ} (W : Mat m n) : Mat m n :=
  W

theorem vectorizedObjective_apply {m n : ℕ} (P : Objective m n) (W : Mat m n) :
    vectorizedObjective P (vectorizedMatrix W) = P.f W :=
  rfl

noncomputable def realizedExpectation
    {Ω R : Type*} [MeasurableSpace Ω] [NormedAddCommGroup R] [NormedSpace ℝ R]
    (μ : Measure Ω) (Z : Ω → R) (_hwd : SOptLib.expectationWellDefined μ Z) : R :=
  ∫ ω, Z ω ∂μ

theorem realizedExpectation_eq_integral
    {Ω R : Type*} [MeasurableSpace Ω] [NormedAddCommGroup R] [NormedSpace ℝ R]
    (μ : Measure Ω) (Z : Ω → R) (hwd : SOptLib.expectationWellDefined μ Z) :
    realizedExpectation μ Z hwd = ∫ ω, Z ω ∂μ :=
  rfl

structure StochasticProblem (ξ : Type*) [MeasurableSpace ξ] (m n : ℕ) where
  sampleLoss : Mat m n → ξ → ℝ
  sampleLaw : Measure ξ
  isProbability_sampleLaw : IsProbabilityMeasure sampleLaw
  /- This single proof field is the source-unstated measure-theoretic
     well-formedness boundary needed to evaluate Algorithm 1's literal sampled
     loss gradient at an adapted random iterate.  It is not Assumption 3.3 and
     carries no independent oracle datum. -/
  sampleGrad_jointly_measurable :
    Measurable (fun p : Mat m n × ξ =>
      objectiveGradient (fun W' : Mat m n => sampleLoss W' p.2) p.1)

def StochasticProblem.objectiveWellDefinedAt {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (W : Mat m n) : Prop :=
  SOptLib.objectiveWellDefined P.sampleLaw P.sampleLoss id W

noncomputable def StochasticProblem.objectiveValue {ξ : Type*} [MeasurableSpace ξ]
    {m n : ℕ} (P : StochasticProblem ξ m n) (W : Mat m n)
    (_hwd : P.objectiveWellDefinedAt W) : ℝ :=
  SOptLib.objectiveExpectation P.sampleLaw P.sampleLoss id W

noncomputable def StochasticProblem.objective {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) : Objective m n where
  f := fun W => SOptLib.objectiveExpectation P.sampleLaw P.sampleLoss id W

theorem StochasticProblem.objectiveValue_eq_objective {ξ : Type*} [MeasurableSpace ξ]
    {m n : ℕ} (P : StochasticProblem ξ m n) (W : Mat m n)
    (hwd : P.objectiveWellDefinedAt W) :
    P.objectiveValue W hwd = P.objective.f W :=
  rfl

theorem StochasticProblem.objective_eq_expected_loss {ξ : Type*} [MeasurableSpace ξ]
    {m n : ℕ} (P : StochasticProblem ξ m n) (W : Mat m n) :
    P.objective.f W = ∫ z, P.sampleLoss W z ∂P.sampleLaw :=
  rfl

noncomputable def StochasticProblem.sampleGrad {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (W : Mat m n) (z : ξ) : Mat m n :=
  objectiveGradient (fun W' : Mat m n => P.sampleLoss W' z) W

theorem StochasticProblem.sampleGrad_eq_sample_loss_gradient {ξ : Type*} [MeasurableSpace ξ]
    {m n : ℕ} (P : StochasticProblem ξ m n) (W : Mat m n) (z : ξ) :
    P.sampleGrad W z = objectiveGradient (fun W' : Mat m n => P.sampleLoss W' z) W :=
  rfl

def StochasticProblem.sampleGradKernel {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) :
    {f : (Mat m n × ξ) → Mat m n // Measurable f} :=
  ⟨fun p => P.sampleGrad p.1 p.2, by
    simpa [StochasticProblem.sampleGrad] using P.sampleGrad_jointly_measurable⟩

@[simp] theorem StochasticProblem.sampleGradKernel_apply
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (p : Mat m n × ξ) :
    P.sampleGradKernel.val p = P.sampleGrad p.1 p.2 :=
  rfl

structure BatchSize where
  val : ℕ
  positive : 0 < val

abbrev BatchSamples (ξ : Type*) (B : BatchSize) := Fin B.val → ξ

abbrev SamplePath (ξ : Type*) (B : BatchSize) := ℕ → BatchSamples ξ B

noncomputable def batchSampleLaw {ξ : Type*} [MeasurableSpace ξ]
    (μ : Measure ξ) (B : BatchSize) : Measure (BatchSamples ξ B) :=
  Measure.pi (fun _ : Fin B.val => μ)

noncomputable def samplePathLaw {ξ : Type*} [MeasurableSpace ξ]
    (P : StochasticProblem ξ m n) (B : BatchSize) : Measure (SamplePath ξ B) :=
  SOptLib.iidMiniBatchSampleLaw B.val P.sampleLaw

theorem samplePathLaw_eq_iidMiniBatchSampleLaw
    {ξ : Type*} [MeasurableSpace ξ] (P : StochasticProblem ξ m n) (B : BatchSize) :
    samplePathLaw P B = SOptLib.iidMiniBatchSampleLaw B.val P.sampleLaw :=
  rfl

structure FrobeniusSmooth {m n : ℕ} (P : Objective m n) (L : ℝ) : Prop where
  contDiff : ContDiff ℝ 1 (vectorizedObjective P)
  lipschitz_grad :
    ∀ W W' : Mat m n,
      frobeniusNorm (P.grad W - P.grad W') ≤ L * frobeniusNorm (W - W')

structure SpectralSmooth {m n : ℕ} (P : Objective m n) (Lstar : ℝ) : Prop where
  /- `Lstar` is the Lipschitz-smoothness constant of Assumption 3.2.
     Recording its intrinsic nonnegativity here rules out the degenerate
     negative-constant witnesses admitted by the bare norm inequality. -/
  nonneg : 0 ≤ Lstar
  contDiff : ContDiff ℝ 1 (vectorizedObjective P)
  lipschitz_grad :
    ∀ W W' : Mat m n,
      nuclearNorm (P.grad W - P.grad W') ≤ Lstar * spectralNorm (W - W')

/- The exact pre-correction Assumption 3.2 bundle, retained only to certify the
   model defect that forced `SpectralSmooth.nonneg`.  This is not an active
   source interface: all theorem consumers use the corrected structure above. -/
private structure PreCorrectionSpectralSmooth {m n : ℕ}
    (P : Objective m n) (Lstar : ℝ) : Prop where
  contDiff : ContDiff ℝ 1 (vectorizedObjective P)
  lipschitz_grad :
    ∀ W W' : Mat m n,
      nuclearNorm (P.grad W - P.grad W') ≤ Lstar * spectralNorm (W - W')

theorem FrobeniusSmooth.objective_continuous {m n : ℕ} {P : Objective m n} {L : ℝ}
    (h : FrobeniusSmooth P L) : Continuous P.f := by
  simpa [vectorizedObjective] using h.contDiff.continuous

theorem SpectralSmooth.objective_continuous {m n : ℕ} {P : Objective m n} {Lstar : ℝ}
    (h : SpectralSmooth P Lstar) : Continuous P.f := by
  simpa [vectorizedObjective] using h.contDiff.continuous

structure BoundedVariance {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (σ : ℝ) : Prop where
  /- The paper uses `σ` as a standard-deviation/noise scale (in particular,
     Equation (14) simplifies `sqrt (σ ^ 2)` to `σ`).  Assumption 3.3 omits
     this domain convention from its display, so we record the approved
     correction once at the assumption boundary. -/
  nonneg : 0 ≤ σ
  unbiased :
    ∀ W : Mat m n,
      ∃ hwd : SOptLib.expectationWellDefined P.sampleLaw (fun z => P.sampleGrad W z),
        realizedExpectation P.sampleLaw (fun z => P.sampleGrad W z) hwd = P.objective.grad W
  variance :
    ∀ W : Mat m n,
      ∃ hwd : SOptLib.expectationWellDefined P.sampleLaw
          (fun z => frobeniusNorm (P.sampleGrad W z - P.objective.grad W) ^ 2),
        realizedExpectation P.sampleLaw
          (fun z => frobeniusNorm (P.sampleGrad W z - P.objective.grad W) ^ 2) hwd ≤ σ ^ 2

theorem BoundedVariance.sqrt_sq_noiseScale
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    {P : StochasticProblem ξ m n} {σ : ℝ} (hvariance : BoundedVariance P σ) :
    Real.sqrt (σ ^ 2) = σ := by
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hvariance.nonneg]

/- Source: book/Muon/Muon.json#/assumptions/Assumption_3_3_bounded_variance
   and paper/Muon/main.pdf, Assumption 3.3.  The paper states the expectations
   but not Lean regularity side conditions, so this is an internal bridge
   obligation rather than a Setup or theorem-head assumption. -/
def BoundedVarianceWellDefined {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) : Prop :=
  ∀ W : Mat m n,
    SOptLib.expectationWellDefined P.sampleLaw (fun z => P.sampleGrad W z) ∧
      SOptLib.expectationWellDefined P.sampleLaw
        (fun z => frobeniusNorm (P.sampleGrad W z - P.objective.grad W) ^ 2)

theorem boundedVariance_wellDefined_of_source_assumption
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (σ : ℝ) (hvariance : BoundedVariance P σ) :
    BoundedVarianceWellDefined P := by
  intro W
  exact ⟨(hvariance.unbiased W).choose, (hvariance.variance W).choose⟩

def IsFrobeniusStationary {m n : ℕ} (P : Objective m n) (ε : ℝ) (W : Mat m n) : Prop :=
  frobeniusNorm (P.grad W) ≤ ε

def IsNuclearStationary {m n : ℕ} (P : Objective m n) (ε : ℝ) (W : Mat m n) : Prop :=
  nuclearNorm (P.grad W) ≤ ε

def OrthonormalColumns {rows cols : ℕ} (Q : Matrix (Fin rows) (Fin cols) ℝ) : Prop :=
  ∀ i j : Fin cols, (∑ a : Fin rows, Q a i * Q a j) = if i = j then 1 else 0

def NonnegativeDiagonal {k : ℕ} (s : Fin k → ℝ) : Prop :=
  ∀ i, 0 ≤ s i

theorem orthonormalColumns_of_orthonormal_euclidean {rows cols : ℕ}
    (q : Fin cols → EuclideanSpace ℝ (Fin rows)) (hq : Orthonormal ℝ q) :
    OrthonormalColumns (fun a i => q i a) := by
  intro i j
  have hij := (orthonormal_iff_ite.mp hq) i j
  have hsum :
      (∑ a : Fin rows, inner ℝ ((q i).ofLp a) ((q j).ofLp a)) =
        ∑ a : Fin rows, (q i).ofLp a * (q j).ofLp a := by
    apply Finset.sum_congr rfl
    intro a _ha
    calc
      inner ℝ ((q i).ofLp a) ((q j).ofLp a)
          = (q j).ofLp a * (q i).ofLp a := by
            exact RCLike.inner_apply ((q i).ofLp a) ((q j).ofLp a)
      _ = (q i).ofLp a * (q j).ofLp a := by ring
  rw [PiLp.inner_apply, hsum] at hij
  simpa using hij

def IsThinSVDWithPolar {m n : ℕ} (M P : Mat m n) : Prop :=
  ∃ (U : Matrix (Fin m) (Fin M.rank) ℝ)
    (V : Matrix (Fin n) (Fin M.rank) ℝ)
    (s : Fin M.rank → ℝ),
      OrthonormalColumns U ∧
      OrthonormalColumns V ∧
      NonnegativeDiagonal s ∧
      M = U * Matrix.diagonal s * Vᵀ ∧
      P = U * Vᵀ

theorem thin_svd_data_exists_of_rank_zero {m n : ℕ} (M : Mat m n)
    (hzero : M.rank = 0) :
    ∃ (U : Matrix (Fin m) (Fin M.rank) ℝ)
      (V : Matrix (Fin n) (Fin M.rank) ℝ)
      (s : Fin M.rank → ℝ),
        OrthonormalColumns U ∧
        OrthonormalColumns V ∧
        NonnegativeDiagonal s ∧
        M = U * Matrix.diagonal s * Vᵀ := by
  classical
  let L := Matrix.toLin (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m)) M
  have hrank_toLin :
      M.rank =
        Module.finrank ℝ
          (LinearMap.range
            (Matrix.toLin (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m)) M)) := by
    simpa using
      Matrix.rank_eq_finrank_range_toLin M (Pi.basisFun ℝ (Fin m)) (Pi.basisFun ℝ (Fin n))
  have hrange0 : Module.finrank ℝ (LinearMap.range L) = 0 := by
    rw [← hrank_toLin, hzero]
  haveI : Subsingleton (LinearMap.range L) := (Module.finrank_zero_iff).mp hrange0
  have hrange_bot : LinearMap.range L = ⊥ := Submodule.eq_bot_of_subsingleton
  have hLzero : L = 0 := (LinearMap.range_eq_bot).mp hrange_bot
  have hMzero : M = 0 := by
    have hmatrix :
        Matrix.toLin (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m)) M =
          Matrix.toLin (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m)) (0 : Mat m n) := by
      simpa [L] using hLzero
    exact (Matrix.toLin (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))).injective hmatrix
  have hempty : ∀ i : Fin M.rank, False := by
    intro i
    have hi : (i : ℕ) < 0 := by simpa [hzero] using i.isLt
    exact Nat.not_lt_zero _ hi
  refine ⟨0, 0, 0, ?_, ?_, ?_, ?_⟩
  · intro i _j
    exact False.elim (hempty i)
  · intro i _j
    exact False.elim (hempty i)
  · intro i
    exact False.elim (hempty i)
  · rw [hMzero]
    simp

theorem matrix_eq_zero_of_rank_eq_zero {m n : ℕ} (M : Mat m n)
    (hzero : M.rank = 0) :
    M = 0 := by
  let L := Matrix.toLin (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m)) M
  have hrank_toLin :
      M.rank =
        Module.finrank ℝ
          (LinearMap.range
            (Matrix.toLin (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m)) M)) := by
    simpa using
      Matrix.rank_eq_finrank_range_toLin M (Pi.basisFun ℝ (Fin m)) (Pi.basisFun ℝ (Fin n))
  have hrange0 : Module.finrank ℝ (LinearMap.range L) = 0 := by
    rw [← hrank_toLin, hzero]
  haveI : Subsingleton (LinearMap.range L) := (Module.finrank_zero_iff).mp hrange0
  have hrange_bot : LinearMap.range L = ⊥ := Submodule.eq_bot_of_subsingleton
  have hLzero : L = 0 := (LinearMap.range_eq_bot).mp hrange_bot
  have hmatrix :
      Matrix.toLin (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m)) M =
        Matrix.toLin (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m)) (0 : Mat m n) := by
    simpa [L] using hLzero
  exact (Matrix.toLin (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))).injective hmatrix

theorem matrix_rank_eq_finrank_range_toEuclideanLin {m n : ℕ} (M : Mat m n) :
    M.rank =
      Module.finrank ℝ
        (LinearMap.range (Matrix.toEuclideanLin (𝕜 := ℝ) M)) := by
  simpa [Matrix.toEuclideanLin_eq_toLin_orthonormal] using
      Matrix.rank_eq_finrank_range_toLin M
      (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis

def rankToDomainIndex {m n : ℕ} (M : Mat m n) (i : Fin M.rank) : Fin n :=
  ⟨i, by
    have hrank_le : M.rank ≤ n := by
      rw [matrix_rank_eq_finrank_range_toEuclideanLin M]
      simpa using LinearMap.finrank_range_le (Matrix.toEuclideanLin (𝕜 := ℝ) M)
    exact lt_of_lt_of_le i.isLt hrank_le⟩

noncomputable def thinSVDRightFactor {m n : ℕ} (M : Mat m n) :
    Matrix (Fin n) (Fin M.rank) ℝ :=
  fun a i =>
    ((Matrix.toEuclideanLin (𝕜 := ℝ) M).isSymmetric_adjoint_comp_self.eigenvectorBasis
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)))
      (rankToDomainIndex (m := m) (n := n) M i) a

noncomputable def thinSVDLeftFactor {m n : ℕ} (M : Mat m n) :
    Matrix (Fin m) (Fin M.rank) ℝ :=
  fun a i =>
    (((Matrix.toEuclideanLin (𝕜 := ℝ) M).singularValues i)⁻¹ •
      (Matrix.toEuclideanLin (𝕜 := ℝ) M)
        (((Matrix.toEuclideanLin (𝕜 := ℝ) M).isSymmetric_adjoint_comp_self.eigenvectorBasis
          (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)))
          (rankToDomainIndex (m := m) (n := n) M i))) a

theorem matrix_mulVec_eq_toEuclideanLin_apply {m n : ℕ}
    (M : Mat m n) (v : EuclideanSpace ℝ (Fin n)) (a : Fin m) :
    (M *ᵥ v.ofLp) a =
      ((Matrix.toEuclideanLin (𝕜 := ℝ) M) v).ofLp a := by
  have h :=
    Matrix.toEuclideanLin_apply_piLp_toLp (𝕜 := ℝ) M v.ofLp
  have h' := congrArg (fun z : EuclideanSpace ℝ (Fin m) => z.ofLp a) h
  simpa using h'.symm

set_option maxHeartbeats 800000 in
theorem rightSingularVectorFamily_orthonormal {m n : ℕ} (M : Mat m n) :
    Orthonormal ℝ
      (fun i : Fin M.rank =>
        ((Matrix.toEuclideanLin (𝕜 := ℝ) M).isSymmetric_adjoint_comp_self.eigenvectorBasis
          (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)))
          (rankToDomainIndex (m := m) (n := n) M i)) := by
  classical
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
    Matrix.toEuclideanLin (𝕜 := ℝ) M
  let b := T.isSymmetric_adjoint_comp_self.eigenvectorBasis
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n))
  rw [orthonormal_iff_ite]
  intro i j
  have h := b.inner_eq_ite (rankToDomainIndex (m := m) (n := n) M i)
    (rankToDomainIndex (m := m) (n := n) M j)
  have hidx :
      rankToDomainIndex (m := m) (n := n) M i =
        rankToDomainIndex (m := m) (n := n) M j ↔ i = j := by
    constructor
    · intro hij
      exact Fin.ext (by simpa [rankToDomainIndex] using congrArg Fin.val hij)
    · intro hij
      simpa [hij]
  by_cases hij : i = j
  · simpa [T, b, hij, hidx] using h
  · have hidx_ne :
        rankToDomainIndex (m := m) (n := n) M i ≠
          rankToDomainIndex (m := m) (n := n) M j := fun h_eq =>
      hij (hidx.mp h_eq)
    simpa [T, b, hij, hidx_ne] using h

theorem rightSingularVectors_rank_orthonormalColumns {m n : ℕ} (M : Mat m n) :
    OrthonormalColumns
      (fun a i =>
        ((Matrix.toEuclideanLin (𝕜 := ℝ) M).isSymmetric_adjoint_comp_self.eigenvectorBasis
          (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)))
          (rankToDomainIndex (m := m) (n := n) M i) a) :=
  orthonormalColumns_of_orthonormal_euclidean
    (fun i : Fin M.rank =>
      ((Matrix.toEuclideanLin (𝕜 := ℝ) M).isSymmetric_adjoint_comp_self.eigenvectorBasis
        (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)))
        (rankToDomainIndex (m := m) (n := n) M i))
    (rightSingularVectorFamily_orthonormal M)

theorem singularValues_pos_of_fin_rank {m n : ℕ} (M : Mat m n)
    (i : Fin M.rank) :
    0 < (Matrix.toEuclideanLin (𝕜 := ℝ) M).singularValues i := by
  classical
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
    Matrix.toEuclideanLin (𝕜 := ℝ) M
  have hrank : M.rank = Module.finrank ℝ T.range := by
    simpa [T] using matrix_rank_eq_finrank_range_toEuclideanLin M
  have hi : (i : ℕ) < Module.finrank ℝ T.range := by
    rw [← hrank]
    exact i.isLt
  simpa [T] using (T.singularValues_pos_iff_lt_finrank_range).2 hi

theorem singularValues_rank_diagonal_nonnegative {m n : ℕ} (M : Mat m n) :
    NonnegativeDiagonal
      (fun i : Fin M.rank => (Matrix.toEuclideanLin (𝕜 := ℝ) M).singularValues i) := by
  intro i
  exact le_of_lt (singularValues_pos_of_fin_rank M i)

theorem leftSingularVectorFamily_orthonormal {m n : ℕ} (M : Mat m n) :
    Orthonormal ℝ
      (fun i : Fin M.rank =>
        ((Matrix.toEuclideanLin (𝕜 := ℝ) M).singularValues i)⁻¹ •
          (Matrix.toEuclideanLin (𝕜 := ℝ) M)
            (((Matrix.toEuclideanLin (𝕜 := ℝ) M).isSymmetric_adjoint_comp_self.eigenvectorBasis
              (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)))
              (rankToDomainIndex (m := m) (n := n) M i))) := by
  classical
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
    Matrix.toEuclideanLin (𝕜 := ℝ) M
  let b := T.isSymmetric_adjoint_comp_self.eigenvectorBasis
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n))
  rw [orthonormal_iff_ite]
  intro i j
  let ii := rankToDomainIndex (m := m) (n := n) M i
  let jj := rankToDomainIndex (m := m) (n := n) M j
  have hidx_eq : ii = jj ↔ i = j := by
    constructor
    · intro hij
      exact Fin.ext (by simpa [ii, jj, rankToDomainIndex] using congrArg Fin.val hij)
    · intro hij
      simpa [ii, jj, hij]
  have hi_sq :
      T.singularValues i ^ 2 =
        T.isSymmetric_adjoint_comp_self.eigenvalues
          (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)) ii := by
    simpa [ii, rankToDomainIndex] using
      T.sq_singularValues_fin (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)) ii
  have hj_eigen :
      (T.adjoint.comp T) (b jj) =
        (T.isSymmetric_adjoint_comp_self.eigenvalues
          (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)) jj : ℝ) • b jj := by
    simpa [b] using
      T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis
        (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)) jj
  have hinnerT :
      inner ℝ (T (b ii)) (T (b jj)) =
        (if i = j then T.singularValues i ^ 2 else 0) := by
    calc
      inner ℝ (T (b ii)) (T (b jj)) =
          inner ℝ (b ii) (T.adjoint (T (b jj))) := by
            simpa using (LinearMap.adjoint_inner_right T (b ii) (T (b jj))).symm
      _ = inner ℝ (b ii) ((T.adjoint.comp T) (b jj)) := by
            rfl
      _ = inner ℝ (b ii)
          ((T.isSymmetric_adjoint_comp_self.eigenvalues
            (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)) jj : ℝ) • b jj) := by
            rw [hj_eigen]
      _ =
          (T.isSymmetric_adjoint_comp_self.eigenvalues
            (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)) jj : ℝ) *
            inner ℝ (b ii) (b jj) := by
            rw [inner_smul_right]
      _ = (if i = j then T.singularValues i ^ 2 else 0) := by
            by_cases hij : i = j
            · subst j
              have hji : jj = ii := by rfl
              have hb : inner ℝ (b ii) (b jj) = 1 := by
                simpa [hji] using b.inner_eq_ite ii ii
              calc
                (T.isSymmetric_adjoint_comp_self.eigenvalues
                    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)) jj : ℝ) *
                    inner ℝ (b ii) (b jj)
                    = T.isSymmetric_adjoint_comp_self.eigenvalues
                        (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)) ii := by
                        simp [hji, hb]
                _ = T.singularValues i ^ 2 := hi_sq.symm
                _ = (if i = i then T.singularValues i ^ 2 else 0) := by simp
            · have hneq : ii ≠ jj := fun h => hij (hidx_eq.mp h)
              have hb : inner ℝ (b ii) (b jj) = 0 := by
                simpa [hneq] using b.inner_eq_ite ii jj
              simp [hij, hb]
  have hspos_i : 0 < T.singularValues i := by
    simpa [T] using singularValues_pos_of_fin_rank M i
  have hspos_j : 0 < T.singularValues j := by
    simpa [T] using singularValues_pos_of_fin_rank M j
  have hsne_i : T.singularValues i ≠ 0 := ne_of_gt hspos_i
  have hsne_j : T.singularValues j ≠ 0 := ne_of_gt hspos_j
  by_cases hij : i = j
  · subst j
    have hmain :
        inner ℝ ((T.singularValues i)⁻¹ • T (b ii))
          ((T.singularValues i)⁻¹ • T (b ii)) = 1 := by
      calc
        inner ℝ ((T.singularValues i)⁻¹ • T (b ii))
            ((T.singularValues i)⁻¹ • T (b ii))
            = (T.singularValues i)⁻¹ *
                ((T.singularValues i)⁻¹ * inner ℝ (T (b ii)) (T (b ii))) := by
                rw [inner_smul_left, inner_smul_right]
                simp [starRingEnd_apply, pow_two, mul_assoc, mul_comm, mul_left_comm]
        _ = (T.singularValues i)⁻¹ *
                ((T.singularValues i)⁻¹ * (T.singularValues i ^ 2)) := by
                rw [hinnerT]
                simp
        _ = 1 := by
                field_simp [hsne_i]
    simpa [T, b, ii] using hmain
  · have hmain :
        inner ℝ ((T.singularValues i)⁻¹ • T (b ii))
          ((T.singularValues j)⁻¹ • T (b jj)) = 0 := by
      calc
        inner ℝ ((T.singularValues i)⁻¹ • T (b ii))
            ((T.singularValues j)⁻¹ • T (b jj))
            = (starRingEnd ℝ) ((T.singularValues i)⁻¹) *
                ((T.singularValues j)⁻¹ * inner ℝ (T (b ii)) (T (b jj))) := by
                rw [inner_smul_left, inner_smul_right]
        _ = 0 := by
                have hzero : inner ℝ (T (b ii)) (T (b jj)) = 0 := by
                  simpa [hij] using hinnerT
                rw [hzero]
                simp
    simpa [T, b, ii, jj, hij] using hmain

theorem leftSingularVectors_rank_orthonormalColumns {m n : ℕ} (M : Mat m n) :
    OrthonormalColumns
      (fun a i =>
        (((Matrix.toEuclideanLin (𝕜 := ℝ) M).singularValues i)⁻¹ •
          (Matrix.toEuclideanLin (𝕜 := ℝ) M)
            (((Matrix.toEuclideanLin (𝕜 := ℝ) M).isSymmetric_adjoint_comp_self.eigenvectorBasis
              (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)))
              (rankToDomainIndex (m := m) (n := n) M i))) a) :=
  orthonormalColumns_of_orthonormal_euclidean
    (fun i : Fin M.rank =>
      ((Matrix.toEuclideanLin (𝕜 := ℝ) M).singularValues i)⁻¹ •
        (Matrix.toEuclideanLin (𝕜 := ℝ) M)
          (((Matrix.toEuclideanLin (𝕜 := ℝ) M).isSymmetric_adjoint_comp_self.eigenvectorBasis
            (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)))
            (rankToDomainIndex (m := m) (n := n) M i)))
    (leftSingularVectorFamily_orthonormal M)

theorem map_eigenvectorBasis_eq_zero_of_singularValue_zero {m n : ℕ}
    (M : Mat m n) (j : Fin n)
    (hσ : (Matrix.toEuclideanLin (𝕜 := ℝ) M).singularValues j = 0) :
    (Matrix.toEuclideanLin (𝕜 := ℝ) M)
      (((Matrix.toEuclideanLin (𝕜 := ℝ) M).isSymmetric_adjoint_comp_self.eigenvectorBasis
        (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n))) j) = 0 := by
  classical
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
    Matrix.toEuclideanLin (𝕜 := ℝ) M
  let b := T.isSymmetric_adjoint_comp_self.eigenvectorBasis
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n))
  have hsq :
      T.singularValues (j : ℕ) ^ 2 =
        T.isSymmetric_adjoint_comp_self.eigenvalues
          (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)) j := by
    simpa using
      T.sq_singularValues_fin (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)) j
  have heig :
      (T.adjoint.comp T) (b j) =
        (T.isSymmetric_adjoint_comp_self.eigenvalues
          (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)) j : ℝ) • b j := by
    simpa [b] using
      T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis
        (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)) j
  have heigen_zero :
      T.isSymmetric_adjoint_comp_self.eigenvalues
          (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)) j = 0 := by
    rw [← hsq, hσ]
    simp
  have hinner : inner ℝ (T (b j)) (T (b j)) = 0 := by
    calc
      inner ℝ (T (b j)) (T (b j))
          = inner ℝ (b j) (T.adjoint (T (b j))) := by
            simpa using (LinearMap.adjoint_inner_right T (b j) (T (b j))).symm
      _ = inner ℝ (b j) ((T.adjoint.comp T) (b j)) := by
            rfl
      _ = inner ℝ (b j)
          ((T.isSymmetric_adjoint_comp_self.eigenvalues
            (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)) j : ℝ) • b j) := by
            rw [heig]
      _ = 0 := by
            simp [heigen_zero]
  simpa [T, b] using (inner_self_eq_zero.mp hinner)

theorem rank_singularValue_entry_sum_cancel {m n : ℕ} (M : Mat m n)
    (a : Fin m) (bcol : Fin n) :
    (∑ x : Fin M.rank,
      ((Matrix.toEuclideanLin (𝕜 := ℝ) M).singularValues x)⁻¹ *
        ((Matrix.toEuclideanLin (𝕜 := ℝ) M)
          (((Matrix.toEuclideanLin (𝕜 := ℝ) M).isSymmetric_adjoint_comp_self.eigenvectorBasis
            (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)))
            (rankToDomainIndex (m := m) (n := n) M x))) a *
        (Matrix.toEuclideanLin (𝕜 := ℝ) M).singularValues x *
        (((Matrix.toEuclideanLin (𝕜 := ℝ) M).isSymmetric_adjoint_comp_self.eigenvectorBasis
          (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)))
          (rankToDomainIndex (m := m) (n := n) M x)) bcol)
      =
      ∑ x : Fin M.rank,
        ((Matrix.toEuclideanLin (𝕜 := ℝ) M)
          (((Matrix.toEuclideanLin (𝕜 := ℝ) M).isSymmetric_adjoint_comp_self.eigenvectorBasis
            (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)))
            (rankToDomainIndex (m := m) (n := n) M x))) a *
        (((Matrix.toEuclideanLin (𝕜 := ℝ) M).isSymmetric_adjoint_comp_self.eigenvectorBasis
          (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)))
          (rankToDomainIndex (m := m) (n := n) M x)) bcol := by
  classical
  apply Finset.sum_congr rfl
  intro x _hx
  have hsne :
      (Matrix.toEuclideanLin (𝕜 := ℝ) M).singularValues (x : ℕ) ≠ 0 :=
    ne_of_gt (singularValues_pos_of_fin_rank M x)
  field_simp [hsne]

theorem matrix_entry_eq_sum_eigenvectorBasis_image_mul_entry {m n : ℕ}
    (M : Mat m n) (a : Fin m) (bcol : Fin n) :
    M a bcol =
      ∑ j : Fin n,
        ((Matrix.toEuclideanLin (𝕜 := ℝ) M)
          (((Matrix.toEuclideanLin (𝕜 := ℝ) M).isSymmetric_adjoint_comp_self.eigenvectorBasis
            (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n))) j)) a *
        (((Matrix.toEuclideanLin (𝕜 := ℝ) M).isSymmetric_adjoint_comp_self.eigenvectorBasis
          (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n))) j) bcol := by
  classical
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
    Matrix.toEuclideanLin (𝕜 := ℝ) M
  let b := T.isSymmetric_adjoint_comp_self.eigenvectorBasis
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n))
  let e : EuclideanSpace ℝ (Fin n) := PiLp.single 2 bcol (1 : ℝ)
  have hentry : M a bcol = (T e) a := by
    simp [T, e, Matrix.ofLp_toEuclideanLin_apply, Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single bcol]
    · simp
    · intro x _hx hx
      simp [hx]
    · simp
  have hexpand :
      T e = ∑ j : Fin n, (b j) bcol • T (b j) := by
    calc
      T e = T (∑ j : Fin n, b.repr e j • b j) := by
        rw [b.sum_repr]
      _ = ∑ j : Fin n, b.repr e j • T (b j) := by
        simp [map_sum, map_smul]
      _ = ∑ j : Fin n, (b j) bcol • T (b j) := by
        apply Finset.sum_congr rfl
        intro j _hj
        have hrepr : b.repr e j = (b j) bcol := by
          rw [OrthonormalBasis.repr_apply_apply]
          rw [PiLp.inner_apply]
          rw [Finset.sum_eq_single bcol]
          · norm_num [e, inner]
          · intro x _hx hx
            simp [e, hx, RCLike.inner_apply]
          · simp
        rw [hrepr]
  calc
    M a bcol = (T e) a := hentry
    _ = (∑ j : Fin n, (b j) bcol • T (b j)) a := by rw [hexpand]
    _ = ∑ j : Fin n, ((T (b j)) a * (b j) bcol) := by
      have hcoord :
          ((∑ j : Fin n, (b j) bcol • T (b j))).ofLp a =
            ∑ j : Fin n, (((b j) bcol • T (b j) :
              EuclideanSpace ℝ (Fin m))).ofLp a := by
        simp
      rw [hcoord]
      apply Finset.sum_congr rfl
      intro j _hj
      simp [PiLp.smul_apply, mul_comm]
    _ = ∑ j : Fin n, (T (b j)) a * (b j) bcol := rfl

theorem nuclearNorm_eq_sum_rank_singularValues {m n : ℕ} (M : Mat m n) :
    nuclearNorm M =
      ∑ i : Fin M.rank, (Matrix.toEuclideanLin (𝕜 := ℝ) M).singularValues i := by
  classical
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
    Matrix.toEuclideanLin (𝕜 := ℝ) M
  have hrank : M.rank = Module.finrank ℝ T.range := by
    simpa [T] using matrix_rank_eq_finrank_range_toEuclideanLin M
  have hsupport : T.singularValues.support = Finset.range M.rank := by
    simpa [hrank] using T.support_singularValues
  have hsupport_subset : T.singularValues.support ⊆ Finset.range n := by
    intro i hi
    rw [T.support_singularValues, Finset.mem_range] at hi
    have hle : Module.finrank ℝ T.range ≤ n := by
      simpa using (LinearMap.finrank_range_le T)
    simpa [Finset.mem_range] using hi.trans_le hle
  have hsum_range :
      (∑ i ∈ Finset.range n, T.singularValues i) =
        ∑ i ∈ T.singularValues.support, T.singularValues i := by
    refine (Finset.sum_subset hsupport_subset ?_).symm
    intro i _hi_range hi_not_support
    exact Finsupp.notMem_support_iff.mp hi_not_support
  have hsum_fin :
      (∑ i : Fin n, T.singularValues i) = ∑ i ∈ Finset.range n, T.singularValues i := by
    simpa using (Finset.sum_range (f := fun i => T.singularValues i) (n := n)).symm
  calc
    nuclearNorm M = ∑ i : Fin n, T.singularValues i := by
      rfl
    _ = ∑ i ∈ Finset.range n, T.singularValues i := hsum_fin
    _ = ∑ i ∈ T.singularValues.support, T.singularValues i := hsum_range
    _ = ∑ i ∈ Finset.range M.rank, T.singularValues i := by
      rw [hsupport]
    _ = ∑ i : Fin M.rank, T.singularValues i := by
      simpa using (Finset.sum_range (f := fun i => T.singularValues i) (n := M.rank))

theorem thin_svd_singular_values_data_exists {m n : ℕ} (M : Mat m n) :
    ∃ (U : Matrix (Fin m) (Fin M.rank) ℝ)
      (V : Matrix (Fin n) (Fin M.rank) ℝ),
        OrthonormalColumns U ∧
        OrthonormalColumns V ∧
        NonnegativeDiagonal
          (fun i : Fin M.rank => (Matrix.toEuclideanLin (𝕜 := ℝ) M).singularValues i) ∧
        M =
          U * Matrix.diagonal
            (fun i : Fin M.rank => (Matrix.toEuclideanLin (𝕜 := ℝ) M).singularValues i) *
              Vᵀ := by
  classical
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
    Matrix.toEuclideanLin (𝕜 := ℝ) M
  have hsing_nonneg : ∀ i : ℕ, 0 ≤ T.singularValues i := fun i =>
    T.singularValues_nonneg i
  have hsing_support :
      T.singularValues.support = Finset.range (Module.finrank ℝ T.range) :=
    T.support_singularValues
  have hrank_toLin :
      M.rank =
        Module.finrank ℝ
          (LinearMap.range
            (Matrix.toLin (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m)) M)) := by
    simpa using
      Matrix.rank_eq_finrank_range_toLin M (Pi.basisFun ℝ (Fin m)) (Pi.basisFun ℝ (Fin n))
  have hrank_toEuclidean :
      M.rank = Module.finrank ℝ T.range := by
    simpa [T] using matrix_rank_eq_finrank_range_toEuclideanLin M
  have hsing_rank_pos :
      ∀ i : Fin M.rank, 0 < T.singularValues i := by
    intro i
    simpa [T] using singularValues_pos_of_fin_rank M i
  have hsing_rank_nonneg :
      NonnegativeDiagonal (fun i : Fin M.rank => T.singularValues i) := by
    intro i
    exact le_of_lt (hsing_rank_pos i)
  -- Remaining bridge: use the spectral theorem for `T.adjoint.comp T` to build
  -- right singular vectors, transport the positive singular-vector span through
  -- `T / σᵢ` to left singular vectors, then convert the resulting orthonormal
  -- families back to matrix columns indexed by `Fin M.rank`.
  by_cases hzero : M.rank = 0
  · rcases thin_svd_data_exists_of_rank_zero M hzero with
      ⟨U, V, s, hU, hV, _hs, hM⟩
    refine ⟨U, V, hU, hV, ?_, ?_⟩
    · simpa using hsing_rank_nonneg
    · have hMzero : M = 0 := matrix_eq_zero_of_rank_eq_zero M hzero
      have hempty : ∀ i : Fin M.rank, False := by
        intro i
        have hi : (i : ℕ) < 0 := by simpa [hzero] using i.isLt
        exact Nat.not_lt_zero _ hi
      ext a b
      calc
        M a b = 0 := by simp [hMzero]
        _ =
            (U * Matrix.diagonal
              (fun i : Fin M.rank => (Matrix.toEuclideanLin (𝕜 := ℝ) M).singularValues i) *
                Vᵀ) a b := by
              simp only [Matrix.mul_apply]
              symm
              refine Finset.sum_eq_zero ?_
              intro x _hx
              exact False.elim (hempty x)
  · let U : Matrix (Fin m) (Fin M.rank) ℝ :=
      fun a i =>
        ((T.singularValues i)⁻¹ •
          T ((T.isSymmetric_adjoint_comp_self.eigenvectorBasis
            (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)))
            (rankToDomainIndex (m := m) (n := n) M i))) a
    let V : Matrix (Fin n) (Fin M.rank) ℝ :=
      fun a i =>
        (T.isSymmetric_adjoint_comp_self.eigenvectorBasis
          (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)))
          (rankToDomainIndex (m := m) (n := n) M i) a
    refine ⟨U, V, ?_, ?_, ?_, ?_⟩
    · simpa [U, T] using leftSingularVectors_rank_orthonormalColumns M
    · simpa [V, T] using rightSingularVectors_rank_orthonormalColumns M
    · simpa [T] using hsing_rank_nonneg
    ·
      ext a b
      simp [U, V, Matrix.mul_apply, Matrix.diagonal, Matrix.transpose_apply]
      rw [rank_singularValue_entry_sum_cancel M a b]
      rw [matrix_entry_eq_sum_eigenvectorBasis_image_mul_entry M a b]
      have hrank_le_n : M.rank ≤ n := by
        rw [hrank_toEuclidean]
        simpa using LinearMap.finrank_range_le T
      have hsub : Finset.range M.rank ⊆ Finset.range n := by
        intro i hi
        rw [Finset.mem_range] at hi ⊢
        exact lt_of_lt_of_le hi hrank_le_n
      rw [Finset.sum_fin_eq_sum_range, Finset.sum_fin_eq_sum_range]
      have hdrop :
          (∑ i ∈ Finset.range n,
            if h : i < n then
              ((Matrix.toEuclideanLin (𝕜 := ℝ) M)
                (((Matrix.toEuclideanLin (𝕜 := ℝ) M).isSymmetric_adjoint_comp_self.eigenvectorBasis
                  (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n))) ⟨i, h⟩)) a *
                (((Matrix.toEuclideanLin (𝕜 := ℝ) M).isSymmetric_adjoint_comp_self.eigenvectorBasis
                  (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n))) ⟨i, h⟩) b
            else 0) =
          ∑ i ∈ Finset.range M.rank,
            if h : i < n then
              ((Matrix.toEuclideanLin (𝕜 := ℝ) M)
                (((Matrix.toEuclideanLin (𝕜 := ℝ) M).isSymmetric_adjoint_comp_self.eigenvectorBasis
                  (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n))) ⟨i, h⟩)) a *
                (((Matrix.toEuclideanLin (𝕜 := ℝ) M).isSymmetric_adjoint_comp_self.eigenvectorBasis
                  (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n))) ⟨i, h⟩) b
            else 0 := by
        refine (Finset.sum_subset hsub ?_).symm
        intro x hx_n hx_not_rank
        rw [Finset.mem_range] at hx_n
        have hx_ge_rank : M.rank ≤ x := by
          exact Nat.le_of_not_gt (by simpa [Finset.mem_range] using hx_not_rank)
        have hx_ge_range : Module.finrank ℝ T.range ≤ x := by
          simpa [hrank_toEuclidean] using hx_ge_rank
        have hσT : T.singularValues x = 0 := by
          exact (T.singularValues_eq_zero_iff_le_finrank_range (n := x)).2 hx_ge_range
        have hσ : (Matrix.toEuclideanLin (𝕜 := ℝ) M).singularValues x = 0 := by
          simpa [T] using hσT
        have hmap := map_eigenvectorBasis_eq_zero_of_singularValue_zero M ⟨x, hx_n⟩ hσ
        simp [hx_n, hmap]
      rw [hdrop]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mem_range] at hx
      have hx_n : x < n := lt_of_lt_of_le hx hrank_le_n
      simp [hx, hx_n, rankToDomainIndex]

theorem thin_svd_data_exists {m n : ℕ} (M : Mat m n) :
    ∃ (U : Matrix (Fin m) (Fin M.rank) ℝ)
      (V : Matrix (Fin n) (Fin M.rank) ℝ)
      (s : Fin M.rank → ℝ),
        OrthonormalColumns U ∧
        OrthonormalColumns V ∧
        NonnegativeDiagonal s ∧
        M = U * Matrix.diagonal s * Vᵀ := by
  rcases thin_svd_singular_values_data_exists M with ⟨U, V, hU, hV, hs, hM⟩
  exact ⟨U, V,
    (fun i : Fin M.rank => (Matrix.toEuclideanLin (𝕜 := ℝ) M).singularValues i),
    hU, hV, hs, hM⟩

theorem thin_svd_canonical_data {m n : ℕ} (M : Mat m n) :
    OrthonormalColumns (thinSVDLeftFactor M) ∧
      OrthonormalColumns (thinSVDRightFactor M) ∧
      NonnegativeDiagonal
        (fun i : Fin M.rank => (Matrix.toEuclideanLin (𝕜 := ℝ) M).singularValues i) ∧
      M =
        thinSVDLeftFactor M *
          Matrix.diagonal
            (fun i : Fin M.rank => (Matrix.toEuclideanLin (𝕜 := ℝ) M).singularValues i) *
          (thinSVDRightFactor M)ᵀ := by
  classical
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
    Matrix.toEuclideanLin (𝕜 := ℝ) M
  have hrank_toEuclidean :
      M.rank = Module.finrank ℝ T.range := by
    simpa [T] using matrix_rank_eq_finrank_range_toEuclideanLin M
  by_cases hzero : M.rank = 0
  · have hMzero : M = 0 := matrix_eq_zero_of_rank_eq_zero M hzero
    have hempty : ∀ i : Fin M.rank, False := by
      intro i
      have hi : (i : ℕ) < 0 := by simpa [hzero] using i.isLt
      exact Nat.not_lt_zero _ hi
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i _j
      exact False.elim (hempty i)
    · intro i _j
      exact False.elim (hempty i)
    · intro i
      exact False.elim (hempty i)
    · rw [hMzero]
      have hfactor_zero :
          thinSVDLeftFactor M *
              Matrix.diagonal
                (fun i : Fin M.rank =>
                  (Matrix.toEuclideanLin (𝕜 := ℝ) M).singularValues i) *
              (thinSVDRightFactor M)ᵀ = 0 := by
        ext a b
        simp only [Matrix.mul_apply]
        refine Finset.sum_eq_zero ?_
        intro x _hx
        exact False.elim (hempty x)
      simpa [hMzero] using hfactor_zero.symm
  · have hsing_rank_nonneg :
        NonnegativeDiagonal
          (fun i : Fin M.rank => T.singularValues i) := by
      intro i
      simpa [T] using
        (le_of_lt (singularValues_pos_of_fin_rank M i))
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [thinSVDLeftFactor, T] using
        leftSingularVectors_rank_orthonormalColumns M
    · simpa [thinSVDRightFactor, T] using
        rightSingularVectors_rank_orthonormalColumns M
    · simpa [T] using hsing_rank_nonneg
    ·
      ext a b
      simp [thinSVDLeftFactor, thinSVDRightFactor, Matrix.mul_apply,
        Matrix.diagonal, Matrix.transpose_apply]
      simp_rw [matrix_mulVec_eq_toEuclideanLin_apply]
      rw [rank_singularValue_entry_sum_cancel M a b]
      rw [matrix_entry_eq_sum_eigenvectorBasis_image_mul_entry M a b]
      have hrank_le_n : M.rank ≤ n := by
        rw [hrank_toEuclidean]
        simpa using LinearMap.finrank_range_le T
      have hsub : Finset.range M.rank ⊆ Finset.range n := by
        intro i hi
        rw [Finset.mem_range] at hi ⊢
        exact lt_of_lt_of_le hi hrank_le_n
      rw [Finset.sum_fin_eq_sum_range, Finset.sum_fin_eq_sum_range]
      have hdrop :
          (∑ i ∈ Finset.range n,
            if h : i < n then
              ((Matrix.toEuclideanLin (𝕜 := ℝ) M)
                (((Matrix.toEuclideanLin (𝕜 := ℝ) M).isSymmetric_adjoint_comp_self.eigenvectorBasis
                  (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n))) ⟨i, h⟩)) a *
                (((Matrix.toEuclideanLin (𝕜 := ℝ) M).isSymmetric_adjoint_comp_self.eigenvectorBasis
                  (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n))) ⟨i, h⟩) b
            else 0) =
          ∑ i ∈ Finset.range M.rank,
            if h : i < n then
              ((Matrix.toEuclideanLin (𝕜 := ℝ) M)
                (((Matrix.toEuclideanLin (𝕜 := ℝ) M).isSymmetric_adjoint_comp_self.eigenvectorBasis
                  (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n))) ⟨i, h⟩)) a *
                (((Matrix.toEuclideanLin (𝕜 := ℝ) M).isSymmetric_adjoint_comp_self.eigenvectorBasis
                  (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n))) ⟨i, h⟩) b
            else 0 := by
        refine (Finset.sum_subset hsub ?_).symm
        intro x hx_n hx_not_rank
        rw [Finset.mem_range] at hx_n
        have hx_ge_rank : M.rank ≤ x := by
          exact Nat.le_of_not_gt (by simpa [Finset.mem_range] using hx_not_rank)
        have hx_ge_range : Module.finrank ℝ T.range ≤ x := by
          simpa [hrank_toEuclidean] using hx_ge_rank
        have hσT : T.singularValues x = 0 := by
          exact (T.singularValues_eq_zero_iff_le_finrank_range (n := x)).2 hx_ge_range
        have hσ : (Matrix.toEuclideanLin (𝕜 := ℝ) M).singularValues x = 0 := by
          simpa [T] using hσT
        have hmap := map_eigenvectorBasis_eq_zero_of_singularValue_zero M ⟨x, hx_n⟩ hσ
        simp [hx_n, hmap]
      rw [hdrop]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mem_range] at hx
      have hx_n : x < n := lt_of_lt_of_le hx hrank_le_n
      simp [hx, hx_n, rankToDomainIndex]

theorem exists_thinSVDWithPolar {m n : ℕ} (M : Mat m n) :
    ∃ P : Mat m n, IsThinSVDWithPolar M P := by
  rcases thin_svd_data_exists M with ⟨U, V, s, hU, hV, hs, hM⟩
  refine ⟨U * Vᵀ, ?_⟩
  exact ⟨U, V, s, hU, hV, hs, hM, rfl⟩

theorem transpose_mul_self_eq_one_of_orthonormalColumns {rows cols : ℕ}
    (Q : Matrix (Fin rows) (Fin cols) ℝ) (hQ : OrthonormalColumns Q) :
    Qᵀ * Q = 1 := by
  classical
  ext i j
  simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hQ i j

theorem frobeniusInner_eq_trace_transpose_mul {m n : ℕ} (A B : Mat m n) :
    frobeniusInner A B = Matrix.trace (Aᵀ * B) := by
  classical
  calc
    frobeniusInner A B = ∑ i : Fin m, ∑ j : Fin n, A i j * B i j := rfl
    _ = ∑ j : Fin n, ∑ i : Fin m, A i j * B i j := Finset.sum_comm
    _ = Matrix.trace (Aᵀ * B) := by
          simp [Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply]

theorem frobeniusInner_factor_polar_eq_sum_diagonal_of_orthonormalColumns
    {m n k : ℕ} (U : Matrix (Fin m) (Fin k) ℝ) (V : Matrix (Fin n) (Fin k) ℝ)
    (s : Fin k → ℝ) (hU : OrthonormalColumns U) (hV : OrthonormalColumns V) :
    frobeniusInner (U * Matrix.diagonal s * Vᵀ) (U * Vᵀ) = ∑ i : Fin k, s i := by
  classical
  have hUtU : Uᵀ * U = 1 := transpose_mul_self_eq_one_of_orthonormalColumns U hU
  have hVtV : Vᵀ * V = 1 := transpose_mul_self_eq_one_of_orthonormalColumns V hV
  rw [frobeniusInner_eq_trace_transpose_mul]
  calc
    Matrix.trace ((U * Matrix.diagonal s * Vᵀ)ᵀ * (U * Vᵀ))
        = Matrix.trace ((V * Matrix.diagonal s * Uᵀ) * (U * Vᵀ)) := by
            simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = Matrix.trace (V * Matrix.diagonal s * (Uᵀ * U) * Vᵀ) := by
            simp [Matrix.mul_assoc]
    _ = Matrix.trace (V * Matrix.diagonal s * Vᵀ) := by
            simp [hUtU, Matrix.mul_assoc]
    _ = Matrix.trace (Vᵀ * (V * Matrix.diagonal s)) := by
            exact Matrix.trace_mul_comm (V * Matrix.diagonal s) Vᵀ
    _ = Matrix.trace ((Vᵀ * V) * Matrix.diagonal s) := by
            simp [Matrix.mul_assoc]
    _ = Matrix.trace (Matrix.diagonal s) := by
            simp [hVtV]
    _ = ∑ i : Fin k, s i := by
            simp [Matrix.trace]

theorem frobeniusInner_factorization_eq_sum_diagonal
    {m n k : ℕ} {M P : Mat m n}
    (U : Matrix (Fin m) (Fin k) ℝ) (V : Matrix (Fin n) (Fin k) ℝ)
    (s : Fin k → ℝ) (hU : OrthonormalColumns U) (hV : OrthonormalColumns V)
    (hM : M = U * Matrix.diagonal s * Vᵀ) (hP : P = U * Vᵀ) :
    frobeniusInner M P = ∑ i : Fin k, s i := by
  rw [hM, hP]
  exact frobeniusInner_factor_polar_eq_sum_diagonal_of_orthonormalColumns U V s hU hV

theorem frobeniusInner_rank_singularValues_factor_polar_eq_nuclearNorm
    {m n : ℕ} (M : Mat m n)
    (U : Matrix (Fin m) (Fin M.rank) ℝ) (V : Matrix (Fin n) (Fin M.rank) ℝ)
    (hU : OrthonormalColumns U) (hV : OrthonormalColumns V)
    (hM : M =
      U * Matrix.diagonal
        (fun i : Fin M.rank => (Matrix.toEuclideanLin (𝕜 := ℝ) M).singularValues i) * Vᵀ) :
    frobeniusInner M (U * Vᵀ) = nuclearNorm M := by
  calc
    frobeniusInner M (U * Vᵀ) =
        ∑ i : Fin M.rank, (Matrix.toEuclideanLin (𝕜 := ℝ) M).singularValues i := by
      exact frobeniusInner_factorization_eq_sum_diagonal U V
        (fun i : Fin M.rank => (Matrix.toEuclideanLin (𝕜 := ℝ) M).singularValues i)
        hU hV hM rfl
    _ = nuclearNorm M := (nuclearNorm_eq_sum_rank_singularValues M).symm

theorem exists_thinSVDWithPolar_frobeniusInner_eq_nuclearNorm
    {m n : ℕ} (M : Mat m n) :
    ∃ P : Mat m n,
      IsThinSVDWithPolar M P ∧ frobeniusInner M P = nuclearNorm M := by
  classical
  rcases thin_svd_singular_values_data_exists M with ⟨U, V, hU, hV, hs, hM⟩
  refine ⟨U * Vᵀ, ?_, ?_⟩
  · exact ⟨U, V,
      (fun i : Fin M.rank => (Matrix.toEuclideanLin (𝕜 := ℝ) M).singularValues i),
      hU, hV, hs, hM, rfl⟩
  · exact frobeniusInner_rank_singularValues_factor_polar_eq_nuclearNorm M U V hU hV hM

theorem orthonormalColumns_column_norm
    {rows cols : ℕ} (Q : Matrix (Fin rows) (Fin cols) ℝ)
    (hQ : OrthonormalColumns Q) (i : Fin cols) :
    ‖(WithLp.toLp 2 (fun a : Fin rows => Q a i) :
        EuclideanSpace ℝ (Fin rows))‖ = 1 := by
  have hsq := EuclideanSpace.norm_sq_eq
    (WithLp.toLp 2 (fun a : Fin rows => Q a i) :
      EuclideanSpace ℝ (Fin rows))
  have hcol : (∑ a : Fin rows, Q a i * Q a i) = 1 := by
    simpa using hQ i i
  have hnormsq :
      ‖(WithLp.toLp 2 (fun a : Fin rows => Q a i) :
          EuclideanSpace ℝ (Fin rows))‖ ^ 2 = 1 := by
    rw [hsq]
    simpa [Real.norm_eq_abs, sq_abs, pow_two] using hcol
  nlinarith [norm_nonneg
    (WithLp.toLp 2 (fun a : Fin rows => Q a i) :
      EuclideanSpace ℝ (Fin rows))]

theorem abs_orthonormal_column_matrix_bilinear_le_spectralNorm
    {m n k : ℕ} (B : Mat m n)
    (U : Matrix (Fin m) (Fin k) ℝ) (V : Matrix (Fin n) (Fin k) ℝ)
    (hU : OrthonormalColumns U) (hV : OrthonormalColumns V) (i : Fin k) :
    |(Uᵀ * B * V) i i| ≤ spectralNorm B := by
  let u : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun a => U a i)
  let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun b => V b i)
  let L := (Matrix.toEuclideanLin (𝕜 := ℝ) B).toContinuousLinearMap
  have hu : ‖u‖ = 1 := by
    simpa [u] using orthonormalColumns_column_norm U hU i
  have hv : ‖v‖ = 1 := by
    simpa [v] using orthonormalColumns_column_norm V hV i
  have hentry : (Uᵀ * B * V) i i = ⟪u, L v⟫_ℝ := by
    simp [u, v, L, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.toEuclideanLin_apply_piLp_toLp, PiLp.inner_apply, dotProduct,
      real_inner_eq_re_inner, RCLike.inner_apply]
    change
      (∑ b : Fin n, (∑ a : Fin m, U a i * B a b) * V b i) =
        ∑ a : Fin m, (∑ b : Fin n, B a b * V b i) * U a i
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _ha
    apply Finset.sum_congr rfl
    intro b _hb
    ring
  rw [hentry]
  calc
    |⟪u, L v⟫_ℝ| ≤ ‖u‖ * ‖L v‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖u‖ * (‖L‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left (L.le_opNorm v) (norm_nonneg u)
    _ = spectralNorm B := by simp [hu, hv, L, spectralNorm]

/- The paper's nuclear/spectral pairing is realized by the canonical Mathlib
   operator norm and the thin SVD above.  This is the duality estimate used in
   Appendix C.5, Eq. (20). -/
theorem abs_frobeniusInner_le_nuclearNorm_mul_spectralNorm
    {m n : ℕ} (A B : Mat m n) :
    |frobeniusInner A B| ≤ nuclearNorm A * spectralNorm B := by
  classical
  rcases thin_svd_singular_values_data_exists A with
    ⟨U, V, hU, hV, hs, hA⟩
  let s : Fin A.rank → ℝ := fun i =>
    (Matrix.toEuclideanLin (𝕜 := ℝ) A).singularValues i
  have hs_nonneg (i : Fin A.rank) : 0 ≤ s i := hs i
  have hformula :
      frobeniusInner A B = ∑ i : Fin A.rank, s i * (Uᵀ * B * V) i i := by
    calc
      frobeniusInner A B =
          frobeniusInner (U * Matrix.diagonal s * Vᵀ) B := by rw [← hA]
      _ = Matrix.trace ((U * Matrix.diagonal s * Vᵀ)ᵀ * B) :=
        frobeniusInner_eq_trace_transpose_mul _ _
      _ =
          Matrix.trace (V * Matrix.diagonal s * Uᵀ * B) := by
            simp [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Matrix.trace ((Matrix.diagonal s * Uᵀ * B) * V) := by
            simpa [Matrix.mul_assoc] using
              Matrix.trace_mul_comm V (Matrix.diagonal s * Uᵀ * B)
      _ = Matrix.trace (Matrix.diagonal s * (Uᵀ * B * V)) := by
            simp [Matrix.mul_assoc]
      _ = ∑ i : Fin A.rank, s i * (Uᵀ * B * V) i i := by
            simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal]
  rw [hformula]
  calc
    |∑ i : Fin A.rank, s i * (Uᵀ * B * V) i i| ≤
        ∑ i : Fin A.rank, |s i * (Uᵀ * B * V) i i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin A.rank, s i * spectralNorm B := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [abs_mul, abs_of_nonneg (hs_nonneg i)]
      exact mul_le_mul_of_nonneg_left
        (abs_orthonormal_column_matrix_bilinear_le_spectralNorm B U V hU hV i)
        (hs_nonneg i)
    _ = nuclearNorm A * spectralNorm B := by
      rw [← Finset.sum_mul, ← nuclearNorm_eq_sum_rank_singularValues]

noncomputable def orthogonalizedDirection {m n : ℕ} (M : Mat m n) : Mat m n :=
  thinSVDLeftFactor M * (thinSVDRightFactor M)ᵀ

/- The scalar series `∑ choose (2j) j / 4^j * x^j` is `(1-x)⁻¹/²`
   for `|x| < 1`.  Applied to `x = I - XᵀX`, with
   `X = M / (1 + ‖M‖)`, its finite sums are continuous matrix polynomials.
   Their pointwise limit is the exact partial polar: nonzero singular values
   are sent to one and the kernel stays zero. -/
def inverseSqrtSeriesCoefficient (j : ℕ) : ℝ :=
  Ring.choose ((1 / 2 : ℝ) + j - 1) j

theorem inverseSqrtSeries_hasSum {x : ℝ} (hx : |x| < 1) :
    HasSum (fun j => inverseSqrtSeriesCoefficient j * x ^ j)
      (1 / (1 - x) ^ (1 / 2 : ℝ)) := by
  have hxball : x ∈ Metric.eball (0 : ℝ) 1 := by
    simpa [enorm_eq_nnnorm] using hx
  simpa [inverseSqrtSeriesCoefficient, mul_comm] using
    (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (1 / 2 : ℝ)).hasSum_sub hxball

theorem inverseSqrtSeries_partialSums_tendsto {x : ℝ} (hx : |x| < 1) :
    Tendsto
      (fun k => ∑ j ∈ Finset.range (k + 1), inverseSqrtSeriesCoefficient j * x ^ j)
      atTop (nhds (1 / (1 - x) ^ (1 / 2 : ℝ))) := by
  exact (inverseSqrtSeries_hasSum hx).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

theorem polarSingularMode_partialSums_tendsto_one {q : ℝ}
    (hq : 0 < q) (hq_one : q < 1) :
    Tendsto
      (fun k => q * ∑ j ∈ Finset.range (k + 1),
        inverseSqrtSeriesCoefficient j * (1 - q ^ 2) ^ j)
      atTop (nhds 1) := by
  have hx : |1 - q ^ 2| < 1 := by
    rw [abs_of_nonneg]
    · nlinarith [sq_nonneg q]
    · nlinarith [sq_nonneg q]
  have hlim := (inverseSqrtSeries_partialSums_tendsto hx).const_mul q
  convert hlim using 1
  rw [sub_sub_cancel, ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_pos hq]
  field_simp

def polarNormalized {m n : ℕ} (M : Mat m n) : Mat m n :=
  (1 + ‖M‖)⁻¹ • M

theorem polarNormalized_continuous {m n : ℕ} :
    Continuous (polarNormalized : Mat m n → Mat m n) := by
  apply Continuous.smul
  · apply Continuous.inv₀
    · exact continuous_const.add continuous_norm
    · intro M h
      have : 0 < 1 + ‖M‖ := by positivity
      exact this.ne' h
  · exact continuous_id

def partialPolarPolynomial {m n : ℕ} (k : ℕ) (M : Mat m n) : Mat m n :=
  let X := polarNormalized M
  X * ∑ j ∈ Finset.range (k + 1),
    inverseSqrtSeriesCoefficient j •
      ((1 : Mat n n) - Xᵀ * X) ^ j

theorem partialPolarPolynomial_continuous {m n : ℕ} (k : ℕ) :
    Continuous (partialPolarPolynomial (m := m) (n := n) k) := by
  unfold partialPolarPolynomial
  have hX : Continuous (polarNormalized : Mat m n → Mat m n) :=
    polarNormalized_continuous
  have hbase : Continuous (fun M : Mat m n =>
      (1 : Mat n n) - (polarNormalized M)ᵀ * polarNormalized M) :=
    continuous_const.sub (hX.matrix_transpose.matrix_mul hX)
  apply hX.matrix_mul
  exact continuous_finset_sum (Finset.range (k + 1)) fun j _ =>
    (hbase.pow j).const_smul (inverseSqrtSeriesCoefficient j)

theorem partialPolarPolynomial_measurable {m n : ℕ} (k : ℕ) :
    Measurable (partialPolarPolynomial (m := m) (n := n) k) :=
  (partialPolarPolynomial_continuous k).measurable

/- The canonical measurable exact-partial-polar candidate is the pointwise
   limit of the continuous polynomial approximants.  `limUnder` totalizes
   only the nonconvergent branch; the SVD identification below is responsible
   for showing that this branch is never used. -/
noncomputable def measurablePartialPolar {m n : ℕ} (M : Mat m n) : Mat m n :=
  limUnder atTop (fun k => partialPolarPolynomial k M)

theorem measurablePartialPolar_measurable {m n : ℕ} :
    Measurable (measurablePartialPolar : Mat m n → Mat m n) := by
  have h := StronglyMeasurable.limUnder
    (l := atTop)
    (fun k =>
      (partialPolarPolynomial_measurable (m := m) (n := n) k).stronglyMeasurable)
  exact h.measurable

theorem measurablePartialPolar_zero {m n : ℕ} :
    measurablePartialPolar (0 : Mat m n) = 0 := by
  simp only [measurablePartialPolar, partialPolarPolynomial, polarNormalized,
    norm_zero, add_zero, inv_one, one_smul, transpose_zero, zero_mul, sub_zero,
    zero_pow, Finset.sum_const_zero, Matrix.zero_mul]
  exact (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (0 : Mat m n)) atTop (nhds 0)).limUnder_eq

theorem orthogonalizedDirection_isThinSVDWithPolar {m n : ℕ} (M : Mat m n) :
    IsThinSVDWithPolar M (orthogonalizedDirection M) := by
  rcases thin_svd_canonical_data M with ⟨hU, hV, hs, hM⟩
  exact ⟨thinSVDLeftFactor M, thinSVDRightFactor M,
    (fun i : Fin M.rank => (Matrix.toEuclideanLin (𝕜 := ℝ) M).singularValues i),
    hU, hV, hs, hM, rfl⟩

theorem orthogonalizedDirection_frobeniusInner_eq_nuclearNorm {m n : ℕ} (M : Mat m n) :
    frobeniusInner M (orthogonalizedDirection M) = nuclearNorm M := by
  rcases thin_svd_canonical_data M with ⟨hU, hV, _hs, hM⟩
  calc
    frobeniusInner M (orthogonalizedDirection M) =
        ∑ i : Fin M.rank,
          (Matrix.toEuclideanLin (𝕜 := ℝ) M).singularValues i := by
      rw [orthogonalizedDirection]
      exact frobeniusInner_factorization_eq_sum_diagonal
        (thinSVDLeftFactor M) (thinSVDRightFactor M)
        (fun i : Fin M.rank =>
          (Matrix.toEuclideanLin (𝕜 := ℝ) M).singularValues i)
        hU hV hM rfl
    _ = nuclearNorm M := (nuclearNorm_eq_sum_rank_singularValues M).symm

def muonUpdate {m n : ℕ} (W : Mat m n) (η : ℝ) (D : Mat m n) : Mat m n :=
  W - η • D

def stochasticBatchGradient {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (B : BatchSize) (W : Mat m n)
    (samples : BatchSamples ξ B) : Mat m n :=
  ((B.val : ℝ)⁻¹) • ∑ i : Fin B.val, P.sampleGrad W (samples i)

theorem stochasticBatchGradient_eq_source_formula {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (B : BatchSize) (W : Mat m n)
    (samples : BatchSamples ξ B) :
    stochasticBatchGradient P B W samples =
      ((B.val : ℝ)⁻¹) • ∑ i : Fin B.val, P.sampleGrad W (samples i) :=
  rfl

theorem stochasticBatchGradient_measurable_of_measurable
    {Ω ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (B : BatchSize)
    (query : Ω → Mat m n) (samples : Ω → BatchSamples ξ B)
    (hquery : Measurable query) (hsamples : Measurable samples) :
    Measurable (fun ω => stochasticBatchGradient P B (query ω) (samples ω)) := by
  unfold stochasticBatchGradient
  exact (Finset.measurable_sum Finset.univ (fun i _hi =>
    SOptLib.sampledOracle_measurable
      (oracle := P.sampleGrad) (x := query) (ξ := fun ω => samples ω i)
      P.sampleGradKernel.property hquery
      ((measurable_pi_apply i).comp hsamples))).const_smul ((B.val : ℝ)⁻¹)

theorem stochasticBatchGradient_measurable_from
    {Ω ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace ξ] {m n : ℕ}
    (source : MeasurableSpace Ω) (P : StochasticProblem ξ m n) (B : BatchSize)
    (query : Ω → Mat m n) (samples : Ω → BatchSamples ξ B)
    (hquery : Measurable[source] query) (hsamples : Measurable[source] samples) :
    Measurable[source]
      (fun ω => stochasticBatchGradient P B (query ω) (samples ω)) := by
  letI : MeasurableSpace Ω := source
  exact stochasticBatchGradient_measurable_of_measurable
    P B query samples hquery hsamples

/- The strict sample past before time `t` contains every mini-batch coordinate
   with time index strictly below `t`.  It is the source filtration used to
   state that Algorithm 1's `W_t` is adapted and its time-`t` batch is fresh. -/
def stochasticSampleStrictPast {ξ : Type*} [MeasurableSpace ξ]
    (B : BatchSize) (t : ℕ) : MeasurableSpace (SamplePath ξ B) :=
  ⨆ q ∈ {q : ℕ × Fin B.val | q.1 < t},
    MeasurableSpace.comap (fun ω : SamplePath ξ B => ω q.1 q.2)
      (by infer_instance : MeasurableSpace ξ)

theorem stochasticSampleStrictPast_mono {ξ : Type*} [MeasurableSpace ξ]
    (B : BatchSize) {s t : ℕ} (hst : s ≤ t) :
    stochasticSampleStrictPast (ξ := ξ) B s ≤ stochasticSampleStrictPast B t := by
  unfold stochasticSampleStrictPast
  refine iSup_le fun q => iSup_le fun hq => ?_
  exact le_iSup_of_le q (le_iSup_of_le (lt_of_lt_of_le hq hst) le_rfl)

theorem stochasticSample_miniBatch_measurable_strictPast
    {ξ : Type*} [MeasurableSpace ξ] (B : BatchSize) {s t : ℕ} (hst : s < t) :
    Measurable[stochasticSampleStrictPast (ξ := ξ) B t]
      (fun ω : SamplePath ξ B => ω s) := by
  refine @measurable_pi_lambda (SamplePath ξ B) (Fin B.val) (fun _ => ξ)
    (stochasticSampleStrictPast B t) (fun _ => inferInstance)
    (fun ω _i => ω s _i) ?_
  intro i
  exact Measurable.of_comap_le
    (le_iSup_of_le (s, i) (le_iSup_of_le hst le_rfl))

structure MuonState (m n : ℕ) where
  W : Mat m n
  M : Mat m n

structure StochasticMuonConfig (m n : ℕ) where
  W0 : Mat m n
  eta : ℕ → ℝ
  beta : ℝ
  beta_mem : beta ∈ Set.Ico (0 : ℝ) 1
  batchSize : BatchSize

def stochasticMuonBaseState {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (ω : SamplePath ξ cfg.batchSize) : MuonState m n :=
  let G0 := stochasticBatchGradient P cfg.batchSize cfg.W0 (ω 0)
  { W := cfg.W0, M := G0 }

def stochasticMuonStep {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (ω : SamplePath ξ cfg.batchSize) (t : ℕ) (state : MuonState m n) : MuonState m n :=
  let Wnext := muonUpdate state.W (cfg.eta t) (orthogonalizedDirection state.M)
  let Gnext := stochasticBatchGradient P cfg.batchSize Wnext (ω (t + 1))
  let Mnext := cfg.beta • state.M + (1 - cfg.beta) • Gnext
  { W := Wnext, M := Mnext }

def stochasticMuonState {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (ω : SamplePath ξ cfg.batchSize) : ℕ → MuonState m n :=
  fun t => Nat.rec (stochasticMuonBaseState P cfg ω)
    (fun k state => stochasticMuonStep P cfg ω k state) t

theorem stochasticMuon_M_zero_eq_G_zero {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (ω : SamplePath ξ cfg.batchSize) :
    (stochasticMuonState P cfg ω 0).M =
      stochasticBatchGradient P cfg.batchSize cfg.W0 (ω 0) :=
  rfl

theorem stochasticMuon_W_succ_eq_source_update {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (ω : SamplePath ξ cfg.batchSize) (t : ℕ) :
    (stochasticMuonState P cfg ω (t + 1)).W =
      (stochasticMuonState P cfg ω t).W -
        cfg.eta t • orthogonalizedDirection ((stochasticMuonState P cfg ω t).M) := by
  cases t <;> rfl

theorem stochasticMuon_M_succ_eq_source_update {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (ω : SamplePath ξ cfg.batchSize) (t : ℕ) :
    (stochasticMuonState P cfg ω (t + 1)).M =
      cfg.beta • (stochasticMuonState P cfg ω t).M +
        (1 - cfg.beta) •
          stochasticBatchGradient P cfg.batchSize
            (stochasticMuonState P cfg ω (t + 1)).W (ω (t + 1)) := by
  cases t <;> rfl

/- The stochastic-state induction is independent of how the exact partial
   polar is realized.  Its only analytic input is measurability of that map;
   all sample-coordinate measurability is derived from the strict-past
   generators above. -/
set_option maxHeartbeats 1200000 in
theorem stochasticMuon_state_strictPast_measurable_of_direction
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (hdir : Measurable (orthogonalizedDirection : Mat m n → Mat m n)) :
    ∀ t : ℕ,
      Measurable[stochasticSampleStrictPast cfg.batchSize t]
          (fun ω : SamplePath ξ cfg.batchSize => (stochasticMuonState P cfg ω t).W) ∧
      Measurable[stochasticSampleStrictPast cfg.batchSize (t + 1)]
          (fun ω : SamplePath ξ cfg.batchSize => (stochasticMuonState P cfg ω t).M) := by
  intro t
  induction t with
  | zero =>
      constructor
      · exact measurable_const
      · rw [show (fun ω : SamplePath ξ cfg.batchSize =>
            (stochasticMuonState P cfg ω 0).M) =
            fun ω => stochasticBatchGradient P cfg.batchSize cfg.W0 (ω 0) by
              funext ω
              exact stochasticMuon_M_zero_eq_G_zero P cfg ω]
        exact stochasticBatchGradient_measurable_from
          (stochasticSampleStrictPast cfg.batchSize 1)
          P cfg.batchSize
          (fun _ω : SamplePath ξ cfg.batchSize => cfg.W0)
          (fun ω : SamplePath ξ cfg.batchSize => ω 0)
          measurable_const
          (stochasticSample_miniBatch_measurable_strictPast cfg.batchSize (Nat.zero_lt_succ 0))
  | succ t ih =>
      rcases ih with ⟨hW, hM⟩
      have hW_up :
          Measurable[stochasticSampleStrictPast cfg.batchSize (t + 1)]
            (fun ω : SamplePath ξ cfg.batchSize => (stochasticMuonState P cfg ω t).W) :=
        hW.mono (stochasticSampleStrictPast_mono cfg.batchSize (Nat.le_succ t)) le_rfl
      have hWnext :
          Measurable[stochasticSampleStrictPast cfg.batchSize (t + 1)]
            (fun ω : SamplePath ξ cfg.batchSize =>
              (stochasticMuonState P cfg ω (t + 1)).W) := by
        rw [show (fun ω : SamplePath ξ cfg.batchSize =>
              (stochasticMuonState P cfg ω (t + 1)).W) =
              fun ω => (stochasticMuonState P cfg ω t).W -
                cfg.eta t • orthogonalizedDirection
                  ((stochasticMuonState P cfg ω t).M) by
            funext ω
            exact stochasticMuon_W_succ_eq_source_update P cfg ω t]
        exact hW_up.sub ((hdir.comp hM).const_smul (cfg.eta t))
      constructor
      · simpa [Nat.succ_eq_add_one] using hWnext
      · have hM_up :
            Measurable[stochasticSampleStrictPast cfg.batchSize (t + 2)]
              (fun ω : SamplePath ξ cfg.batchSize => (stochasticMuonState P cfg ω t).M) :=
          hM.mono
            (stochasticSampleStrictPast_mono cfg.batchSize (Nat.le_succ (t + 1))) le_rfl
        have hWnext_up :
            Measurable[stochasticSampleStrictPast cfg.batchSize (t + 2)]
              (fun ω : SamplePath ξ cfg.batchSize =>
                (stochasticMuonState P cfg ω (t + 1)).W) :=
          hWnext.mono
            (stochasticSampleStrictPast_mono cfg.batchSize (Nat.le_succ (t + 1))) le_rfl
        have hbatch :
            Measurable[stochasticSampleStrictPast cfg.batchSize (t + 2)]
              (fun ω : SamplePath ξ cfg.batchSize =>
                stochasticBatchGradient P cfg.batchSize
                  (stochasticMuonState P cfg ω (t + 1)).W (ω (t + 1))) :=
          stochasticBatchGradient_measurable_from
            (stochasticSampleStrictPast cfg.batchSize (t + 2))
            P cfg.batchSize
            (fun ω : SamplePath ξ cfg.batchSize =>
              (stochasticMuonState P cfg ω (t + 1)).W)
            (fun ω : SamplePath ξ cfg.batchSize => ω (t + 1)) hWnext_up
            (stochasticSample_miniBatch_measurable_strictPast cfg.batchSize
              (Nat.lt_succ_self (t + 1)))
        rw [show (fun ω : SamplePath ξ cfg.batchSize =>
              (stochasticMuonState P cfg ω (t + 1)).M) =
              fun ω => cfg.beta • (stochasticMuonState P cfg ω t).M +
                (1 - cfg.beta) •
                  stochasticBatchGradient P cfg.batchSize
                    (stochasticMuonState P cfg ω (t + 1)).W (ω (t + 1)) by
            funext ω
            exact stochasticMuon_M_succ_eq_source_update P cfg ω t]
        exact hM_up.const_smul cfg.beta |>.add (hbatch.const_smul (1 - cfg.beta))

theorem stochasticMuon_W_strictPast_measurable_of_direction
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (hdir : Measurable (orthogonalizedDirection : Mat m n → Mat m n)) (t : ℕ) :
    Measurable[stochasticSampleStrictPast cfg.batchSize t]
      (fun ω : SamplePath ξ cfg.batchSize => (stochasticMuonState P cfg ω t).W) :=
  (stochasticMuon_state_strictPast_measurable_of_direction P cfg hdir t).1

theorem sqrt_sum_sq_le_sum_of_nonneg {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    Real.sqrt (∑ i, a i ^ 2) ≤ ∑ i, a i := by
  classical
  have hsum_nonneg : 0 ≤ ∑ i, a i := by
    exact Finset.sum_nonneg (fun i _hi => ha i)
  rw [Real.sqrt_le_left hsum_nonneg]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := a)
    (fun i _hi => ha i)

theorem sum_sq_singularValues_eq_trace_adjoint_comp_self {m n : ℕ}
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    (∑ i : Fin n, T.singularValues i ^ 2) =
      (T.adjoint.comp T).trace ℝ (EuclideanSpace ℝ (Fin n)) := by
  classical
  let hsym := T.isSymmetric_adjoint_comp_self
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
    simp [finrank_euclideanSpace]
  calc
    (∑ i : Fin n, T.singularValues i ^ 2)
        = ∑ i : Fin n, hsym.eigenvalues hn i := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          exact T.sq_singularValues_fin hn i
    _ = (T.adjoint.comp T).trace ℝ (EuclideanSpace ℝ (Fin n)) := by
          simpa [hsym] using (hsym.trace_eq_sum_eigenvalues hn).symm

theorem trace_adjoint_comp_toEuclideanLin_eq_sum_entries_sq {m n : ℕ}
    (A : Mat m n) :
    ((Matrix.toEuclideanLin (𝕜 := ℝ) A).adjoint.comp
        (Matrix.toEuclideanLin (𝕜 := ℝ) A)).trace ℝ (EuclideanSpace ℝ (Fin n)) =
      ∑ i : Fin n, ∑ j : Fin m, A j i ^ 2 := by
  classical
  let T := Matrix.toEuclideanLin (𝕜 := ℝ) A
  change (T.adjoint.comp T).trace ℝ (EuclideanSpace ℝ (Fin n)) =
    ∑ i : Fin n, ∑ j : Fin m, A j i ^ 2
  calc
    (T.adjoint.comp T).trace ℝ (EuclideanSpace ℝ (Fin n))
        = ∑ i : Fin n, ‖T (EuclideanSpace.single i 1)‖ ^ 2 := by
          rw [LinearMap.trace_eq_sum_inner (T.adjoint.comp T)
            (EuclideanSpace.basisFun (Fin n) ℝ)]
          refine Finset.sum_congr rfl ?_
          intro i _hi
          have hb :
              ((EuclideanSpace.basisFun (Fin n) ℝ) i : EuclideanSpace ℝ (Fin n)) =
                EuclideanSpace.single i (1 : ℝ) := by
            simp only [EuclideanSpace.basisFun_apply]
          have hnrm : ‖T ((EuclideanSpace.basisFun (Fin n) ℝ) i)‖ =
              ‖T (EuclideanSpace.single i (1 : ℝ))‖ :=
            congrArg (fun x => ‖T x‖) hb
          simp [LinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
          exact hnrm
    _ = ∑ i : Fin n, ∑ j : Fin m, A j i ^ 2 := by
          simp [T, Matrix.toEuclideanLin_apply, EuclideanSpace.real_norm_sq_eq]

theorem frobeniusNorm_sq_eq_sum_entries_sq {m n : ℕ} (A : Mat m n) :
    frobeniusNorm A ^ 2 = ∑ i : Fin n, ∑ j : Fin m, A j i ^ 2 := by
  classical
  have hnorm :
      frobeniusNorm A = Real.sqrt (∑ j : Fin m, ∑ i : Fin n, A j i ^ 2) := by
    rw [frobeniusNorm, Matrix.frobenius_norm_def]
    simp [Real.sqrt_eq_rpow, Real.norm_eq_abs, sq_abs]
  have hsum_nonneg : 0 ≤ ∑ j : Fin m, ∑ i : Fin n, A j i ^ 2 := by
    exact Finset.sum_nonneg (fun j _hj =>
      Finset.sum_nonneg (fun i _hi => sq_nonneg (A j i)))
  calc
    frobeniusNorm A ^ 2 = (∑ j : Fin m, ∑ i : Fin n, A j i ^ 2) := by
      rw [hnorm, Real.sq_sqrt hsum_nonneg]
    _ = ∑ i : Fin n, ∑ j : Fin m, A j i ^ 2 := by
      exact Finset.sum_comm

theorem trace_adjoint_comp_toEuclideanLin_eq_frobeniusNorm_sq {m n : ℕ}
    (A : Mat m n) :
    ((Matrix.toEuclideanLin (𝕜 := ℝ) A).adjoint.comp
        (Matrix.toEuclideanLin (𝕜 := ℝ) A)).trace ℝ (EuclideanSpace ℝ (Fin n)) =
      frobeniusNorm A ^ 2 := by
  rw [trace_adjoint_comp_toEuclideanLin_eq_sum_entries_sq,
    ← frobeniusNorm_sq_eq_sum_entries_sq]

theorem frobeniusNorm_eq_sqrt_sum_singularValues_sq {m n : ℕ} (A : Mat m n) :
    frobeniusNorm A =
      Real.sqrt (∑ i : Fin n,
        (Matrix.toEuclideanLin (𝕜 := ℝ) A).singularValues i ^ 2) := by
  classical
  let T := Matrix.toEuclideanLin (𝕜 := ℝ) A
  change frobeniusNorm A = Real.sqrt (∑ i : Fin n, T.singularValues i ^ 2)
  have hsq :
      (∑ i : Fin n, T.singularValues i ^ 2) = frobeniusNorm A ^ 2 := by
    exact (sum_sq_singularValues_eq_trace_adjoint_comp_self T).trans
      (by simpa [T] using trace_adjoint_comp_toEuclideanLin_eq_frobeniusNorm_sq A)
  rw [hsq, Real.sqrt_sq_eq_abs]
  have hnonneg : 0 ≤ frobeniusNorm A := by
    simp [frobeniusNorm]
  exact (abs_of_nonneg hnonneg).symm

theorem singularValue_rank_le_frobeniusNorm {m n : ℕ} (M : Mat m n)
    (i : Fin M.rank) :
    (Matrix.toEuclideanLin (𝕜 := ℝ) M).singularValues i ≤ frobeniusNorm M := by
  classical
  let T := Matrix.toEuclideanLin (𝕜 := ℝ) M
  let ii : Fin n := rankToDomainIndex (m := m) (n := n) M i
  have hterm : T.singularValues i ^ 2 ≤ ∑ j : Fin n, T.singularValues j ^ 2 := by
    have hsingle := Finset.single_le_sum
      (fun j (_hj : j ∈ (Finset.univ : Finset (Fin n))) => sq_nonneg (T.singularValues j))
      (Finset.mem_univ ii)
    simpa [ii, rankToDomainIndex] using hsingle
  calc
    T.singularValues i = Real.sqrt (T.singularValues i ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (T.singularValues_nonneg i)]
    _ ≤ Real.sqrt (∑ j : Fin n, T.singularValues j ^ 2) := Real.sqrt_le_sqrt hterm
    _ = frobeniusNorm M := by
      simpa [T] using (frobeniusNorm_eq_sqrt_sum_singularValues_sq M).symm

theorem matrix_mul_diagonal_mul_transpose_apply
    {m n k : ℕ} (U : Matrix (Fin m) (Fin k) ℝ)
    (V : Matrix (Fin n) (Fin k) ℝ) (d : Fin k → ℝ)
    (a : Fin m) (b : Fin n) :
    (U * Matrix.diagonal d * Vᵀ) a b = ∑ i : Fin k, U a i * d i * V b i := by
  classical
  simp [Matrix.mul_apply, Matrix.diagonal]

theorem partialPolarPolynomial_factorization {m n : ℕ} (M : Mat m n) (k : ℕ) :
    let c := (1 + ‖M‖)⁻¹
    let s := fun i : Fin M.rank =>
      (Matrix.toEuclideanLin (𝕜 := ℝ) M).singularValues i
    let q := fun i : Fin M.rank => c * s i
    partialPolarPolynomial k M =
      thinSVDLeftFactor M *
        Matrix.diagonal (fun i => q i *
          ∑ j ∈ Finset.range (k + 1),
            inverseSqrtSeriesCoefficient j * (1 - q i ^ 2) ^ j) *
        (thinSVDRightFactor M)ᵀ := by
  classical
  dsimp only
  rcases thin_svd_canonical_data M with ⟨hU, hV, _hs, hM⟩
  let U := thinSVDLeftFactor M
  let V := thinSVDRightFactor M
  let s := fun i : Fin M.rank =>
    (Matrix.toEuclideanLin (𝕜 := ℝ) M).singularValues i
  let c : ℝ := (1 + ‖M‖)⁻¹
  let q := fun i : Fin M.rank => c * s i
  have hUtU : Uᵀ * U = 1 :=
    transpose_mul_self_eq_one_of_orthonormalColumns U hU
  have hVtV : Vᵀ * V = 1 :=
    transpose_mul_self_eq_one_of_orthonormalColumns V hV
  have hX : polarNormalized M = U * Matrix.diagonal q * Vᵀ := by
    calc
      polarNormalized M = c • M := by rfl
      _ = c • (U * Matrix.diagonal s * Vᵀ) :=
        congrArg (fun A : Mat m n => c • A) hM
      _ = U * Matrix.diagonal q * Vᵀ := by
        ext a b
        change c * (U * Matrix.diagonal s * Vᵀ) a b = _
        rw [matrix_mul_diagonal_mul_transpose_apply,
          matrix_mul_diagonal_mul_transpose_apply, Finset.mul_sum]
        simp [U, V, q, s, c]
        ring
  have hdiagSquare : (Matrix.diagonal q)ᵀ * Matrix.diagonal q =
      Matrix.diagonal (fun i => q i ^ 2) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.mul_apply, Matrix.diagonal, pow_two]
    · simp [Matrix.mul_apply, Matrix.diagonal, hij, Ne.symm hij]
  have hXtX : (polarNormalized M)ᵀ * polarNormalized M =
      V * Matrix.diagonal (fun i => q i ^ 2) * Vᵀ := by
    rw [hX]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᵀ U]
    rw [hUtU, Matrix.one_mul]
    rw [← Matrix.mul_assoc (Matrix.diagonal q)ᵀ (Matrix.diagonal q)]
    rw [hdiagSquare]
  have hpower : ∀ j : ℕ,
      (U * Matrix.diagonal q * Vᵀ) *
          ((1 : Mat n n) - V * Matrix.diagonal (fun i => q i ^ 2) * Vᵀ) ^ j =
        U * Matrix.diagonal (fun i => q i * (1 - q i ^ 2) ^ j) * Vᵀ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ]
        calc
          (U * Matrix.diagonal q * Vᵀ) *
                (((1 : Mat n n) - V * Matrix.diagonal (fun i => q i ^ 2) * Vᵀ) ^ j *
                  ((1 : Mat n n) - V * Matrix.diagonal (fun i => q i ^ 2) * Vᵀ)) =
              ((U * Matrix.diagonal q * Vᵀ) *
                  ((1 : Mat n n) - V * Matrix.diagonal (fun i => q i ^ 2) * Vᵀ) ^ j) *
                ((1 : Mat n n) - V * Matrix.diagonal (fun i => q i ^ 2) * Vᵀ) := by
                  simp [Matrix.mul_assoc]
          _ = (U * Matrix.diagonal (fun i => q i * (1 - q i ^ 2) ^ j) * Vᵀ) *
                ((1 : Mat n n) - V * Matrix.diagonal (fun i => q i ^ 2) * Vᵀ) := by
                  rw [ih]
          _ = U * Matrix.diagonal (fun i => q i * (1 - q i ^ 2) ^ (j + 1)) * Vᵀ := by
                rw [Matrix.mul_sub, Matrix.mul_one]
                calc
                  U * Matrix.diagonal (fun i => q i * (1 - q i ^ 2) ^ j) * Vᵀ -
                      (U * Matrix.diagonal (fun i => q i * (1 - q i ^ 2) ^ j) * Vᵀ) *
                        (V * Matrix.diagonal (fun i => q i ^ 2) * Vᵀ) =
                    U * (Matrix.diagonal (fun i => q i * (1 - q i ^ 2) ^ j) -
                      Matrix.diagonal (fun i => q i * (1 - q i ^ 2) ^ j) *
                        (Vᵀ * V) * Matrix.diagonal (fun i => q i ^ 2)) * Vᵀ := by
                          simp only [Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul]
                  _ = U * (Matrix.diagonal (fun i => q i * (1 - q i ^ 2) ^ j) -
                      Matrix.diagonal (fun i => q i * (1 - q i ^ 2) ^ j) *
                        Matrix.diagonal (fun i => q i ^ 2)) * Vᵀ := by
                          rw [hVtV]
                          simp
                  _ = U * Matrix.diagonal
                      (fun i => q i * (1 - q i ^ 2) ^ (j + 1)) * Vᵀ := by
                          congr 2
                          ext i l
                          by_cases hil : i = l <;>
                            simp [Matrix.mul_apply, Matrix.diagonal, hil, pow_succ] <;> ring
  change polarNormalized M *
      (∑ j ∈ Finset.range (k + 1), inverseSqrtSeriesCoefficient j •
        ((1 : Mat n n) - (polarNormalized M)ᵀ * polarNormalized M) ^ j) = _
  rw [hXtX, hX]
  rw [Matrix.mul_sum]
  simp_rw [Matrix.mul_smul, hpower]
  ext a b
  rw [matrix_mul_diagonal_mul_transpose_apply]
  change
    ((∑ j ∈ Finset.range (k + 1),
      inverseSqrtSeriesCoefficient j •
        (U * Matrix.diagonal (fun i => q i * (1 - q i ^ 2) ^ j) * Vᵀ)) : Mat m n) a b =
      ∑ i : Fin M.rank, U a i *
        (q i * ∑ j ∈ Finset.range (k + 1),
          inverseSqrtSeriesCoefficient j * (1 - q i ^ 2) ^ j) * V b i
  simp only [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul]
  simp_rw [matrix_mul_diagonal_mul_transpose_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

theorem partialPolarPolynomial_tendsto_orthogonalizedDirection {m n : ℕ}
    (M : Mat m n) :
    Tendsto (fun k => partialPolarPolynomial k M) atTop
      (nhds (orthogonalizedDirection M)) := by
  classical
  let U := thinSVDLeftFactor M
  let V := thinSVDRightFactor M
  let s := fun i : Fin M.rank =>
    (Matrix.toEuclideanLin (𝕜 := ℝ) M).singularValues i
  let c : ℝ := (1 + ‖M‖)⁻¹
  let q := fun i : Fin M.rank => c * s i
  have hq_pos : ∀ i, 0 < q i := by
    intro i
    exact mul_pos (inv_pos.mpr (by positivity)) (singularValues_pos_of_fin_rank M i)
  have hq_lt_one : ∀ i, q i < 1 := by
    intro i
    have hsle : s i ≤ ‖M‖ := by
      simpa [s, frobeniusNorm] using singularValue_rank_le_frobeniusNorm M i
    have hden : 0 < 1 + ‖M‖ := by positivity
    simp only [q, c, inv_mul_eq_div]
    exact (div_lt_one hden).2 (lt_of_le_of_lt hsle (by linarith))
  change Tendsto (fun k => partialPolarPolynomial k M) atTop
    (nhds (fun a b => orthogonalizedDirection M a b))
  apply tendsto_pi_nhds.2
  intro a
  apply tendsto_pi_nhds.2
  intro b
  simp_rw [partialPolarPolynomial_factorization M]
  rw [show orthogonalizedDirection M = U * Matrix.diagonal (fun _ => (1 : ℝ)) * Vᵀ by
    ext x y
    rw [matrix_mul_diagonal_mul_transpose_apply]
    simp [orthogonalizedDirection, U, V, Matrix.mul_apply]]
  simp_rw [matrix_mul_diagonal_mul_transpose_apply]
  apply tendsto_finset_sum
  intro i _hi
  have hi := polarSingularMode_partialSums_tendsto_one (hq_pos i) (hq_lt_one i)
  change Tendsto
    (fun k => U a i *
      (q i * ∑ j ∈ Finset.range (k + 1),
        inverseSqrtSeriesCoefficient j * (1 - q i ^ 2) ^ j) * V b i)
    atTop (nhds (U a i * 1 * V b i))
  simpa [mul_assoc] using (hi.const_mul (U a i) |>.mul_const (V b i))

theorem measurablePartialPolar_eq_orthogonalizedDirection {m n : ℕ}
    (M : Mat m n) :
    measurablePartialPolar M = orthogonalizedDirection M := by
  exact (partialPolarPolynomial_tendsto_orthogonalizedDirection M).limUnder_eq

theorem orthogonalizedDirection_measurable {m n : ℕ} :
    Measurable (orthogonalizedDirection : Mat m n → Mat m n) := by
  have hEq : (orthogonalizedDirection : Mat m n → Mat m n) = measurablePartialPolar := by
    funext M
    exact (measurablePartialPolar_eq_orthogonalizedDirection M).symm
  rw [hEq]
  exact measurablePartialPolar_measurable

theorem trace_mul_transpose_eq_card_of_orthonormalColumns {rows cols : ℕ}
    (Q : Matrix (Fin rows) (Fin cols) ℝ) (hQ : OrthonormalColumns Q) :
    Matrix.trace (Qᵀ * Q) = (cols : ℝ) := by
  rw [transpose_mul_self_eq_one_of_orthonormalColumns Q hQ]
  simp

theorem frobeniusNorm_sq_mul_transpose_of_orthonormalColumns {m n k : ℕ}
    (U : Matrix (Fin m) (Fin k) ℝ) (V : Matrix (Fin n) (Fin k) ℝ)
    (hU : OrthonormalColumns U) (hV : OrthonormalColumns V) :
    frobeniusNorm (U * Vᵀ) ^ 2 = (k : ℝ) := by
  classical
  have hUtU : Uᵀ * U = 1 := transpose_mul_self_eq_one_of_orthonormalColumns U hU
  have hVtV : Vᵀ * V = 1 := transpose_mul_self_eq_one_of_orthonormalColumns V hV
  rw [frobeniusNorm_sq_eq_sum_entries_sq]
  calc
    (∑ i : Fin n, ∑ j : Fin m, (U * Vᵀ) j i ^ 2)
        = Matrix.trace ((U * Vᵀ)ᵀ * (U * Vᵀ)) := by
          simp only [Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply, pow_two]
          apply Finset.sum_congr rfl
          intro i _hi
          apply Finset.sum_congr rfl
          intro j _hj
          simp [Matrix.mul_apply, Matrix.transpose_apply, pow_two]
    _ = Matrix.trace (V * (Uᵀ * U) * Vᵀ) := by
          simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = Matrix.trace (V * Vᵀ) := by
          simp [hUtU, Matrix.mul_assoc]
    _ = Matrix.trace (Vᵀ * V) := by
          exact Matrix.trace_mul_comm V Vᵀ
    _ = (k : ℝ) := by
          rw [hVtV]
          simp

theorem frobeniusNorm_mul_transpose_le_sqrt_rankBound_of_orthonormalColumns
    {m n k : ℕ} (U : Matrix (Fin m) (Fin k) ℝ) (V : Matrix (Fin n) (Fin k) ℝ)
    (hU : OrthonormalColumns U) (hV : OrthonormalColumns V)
    (hk : k ≤ matrixRankBound m n) :
    frobeniusNorm (U * Vᵀ) ≤ Real.sqrt (matrixRankBound m n : ℝ) := by
  classical
  have hsq := frobeniusNorm_sq_mul_transpose_of_orthonormalColumns U V hU hV
  have hnorm_nonneg : 0 ≤ frobeniusNorm (U * Vᵀ) := by simp [frobeniusNorm]
  have hsqrt :
      frobeniusNorm (U * Vᵀ) = Real.sqrt (k : ℝ) := by
    rw [← hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg hnorm_nonneg]
  rw [hsqrt]
  exact Real.sqrt_le_sqrt (by exact_mod_cast hk)

theorem frobeniusNorm_sq_of_isThinSVDWithPolar {m n : ℕ} {M P : Mat m n}
    (h : IsThinSVDWithPolar M P) :
    frobeniusNorm P ^ 2 = (M.rank : ℝ) := by
  classical
  rcases h with ⟨U, V, s, hU, hV, _hs, _hM, hP⟩
  rw [hP]
  exact frobeniusNorm_sq_mul_transpose_of_orthonormalColumns U V hU hV

theorem frobeniusNorm_le_sqrt_rankBound_of_isThinSVDWithPolar
    {m n : ℕ} {M P : Mat m n} (h : IsThinSVDWithPolar M P) :
    frobeniusNorm P ≤ Real.sqrt (matrixRankBound m n : ℝ) := by
  classical
  rcases h with ⟨U, V, s, hU, hV, _hs, _hM, hP⟩
  have hrank_m : M.rank ≤ m := Matrix.rank_le_height M
  have hrank_n : M.rank ≤ n := Matrix.rank_le_width M
  have hrank : M.rank ≤ matrixRankBound m n := by
    exact le_min hrank_m hrank_n
  rw [hP]
  exact frobeniusNorm_mul_transpose_le_sqrt_rankBound_of_orthonormalColumns
    U V hU hV hrank

theorem frobeniusNorm_le_nuclearNorm {m n : ℕ} (A : Mat m n) :
    frobeniusNorm A ≤ nuclearNorm A := by
  rw [frobeniusNorm_eq_sqrt_sum_singularValues_sq, nuclearNorm]
  exact sqrt_sum_sq_le_sum_of_nonneg
    (fun i : Fin n => (Matrix.toEuclideanLin (𝕜 := ℝ) A).singularValues i)
    (fun i => (Matrix.toEuclideanLin (𝕜 := ℝ) A).singularValues_nonneg i)

theorem finset_sum_le_sqrt_card_mul_sqrt_sum_sq {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) :
    ∑ i ∈ s, a i ≤ Real.sqrt (s.card : ℝ) * Real.sqrt (∑ i ∈ s, a i ^ 2) := by
  simpa [Finset.sum_const, nsmul_eq_mul, pow_two] using
    (Real.sum_mul_le_sqrt_mul_sqrt (s := s) (f := fun _ => (1 : ℝ)) (g := a))

theorem fin_card_filter_lt_nat_le {n k : ℕ} :
    (Finset.univ.filter (fun i : Fin n => (i : ℕ) < k)).card ≤ k := by
  classical
  calc
    (Finset.univ.filter (fun i : Fin n => (i : ℕ) < k)).card
        ≤ (Finset.range k).card := by
          refine Finset.card_le_card_of_injOn (fun i : Fin n => (i : ℕ)) ?_ ?_
          · intro i hi
            exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
          · intro i hi j hj hij
            exact Fin.ext hij
    _ = k := by simp

theorem singularValues_l1_le_sqrt_rankBound_mul_l2 {m n : ℕ} (A : Mat m n) :
    (∑ i : Fin n, (Matrix.toEuclideanLin (𝕜 := ℝ) A).singularValues i) ≤
      Real.sqrt (matrixRankBound m n : ℝ) *
        Real.sqrt (∑ i : Fin n,
          (Matrix.toEuclideanLin (𝕜 := ℝ) A).singularValues i ^ 2) := by
  let T := Matrix.toEuclideanLin (𝕜 := ℝ) A
  have hrank : Module.finrank ℝ T.range ≤ matrixRankBound m n := by
    have hm0 : Module.finrank ℝ T.range ≤
        Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) := by
      exact Submodule.finrank_le T.range
    have hm : Module.finrank ℝ T.range ≤ m := by
      simpa [finrank_euclideanSpace] using hm0
    have hn0 : Module.finrank ℝ T.range ≤
        Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
      exact T.finrank_range_le
    have hn : Module.finrank ℝ T.range ≤ n := by
      simpa [finrank_euclideanSpace] using hn0
    exact le_min hm hn
  have hzero :
      ∀ i : Fin n, matrixRankBound m n ≤ (i : ℕ) → T.singularValues i = 0 := by
    intro i hi
    rw [LinearMap.singularValues_eq_zero_iff_le_finrank_range]
    exact le_trans hrank hi
  let s : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => (i : ℕ) < matrixRankBound m n)
  have hsum_support :
      (∑ i : Fin n, T.singularValues i) = (∑ i ∈ s, T.singularValues i) := by
    calc
      (∑ i : Fin n, T.singularValues i)
          = ∑ i : Fin n,
              if (i : ℕ) < matrixRankBound m n then T.singularValues i else 0 := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            by_cases hi : (i : ℕ) < matrixRankBound m n
            · simp [hi]
            · simp [hi, hzero i (not_lt.mp hi)]
      _ = ∑ i ∈ s, T.singularValues i := by
            rw [Finset.sum_filter]
  have hcard_nat : s.card ≤ matrixRankBound m n := by
    simpa [s] using fin_card_filter_lt_nat_le (n := n) (k := matrixRankBound m n)
  have hcard : (s.card : ℝ) ≤ (matrixRankBound m n : ℝ) := by
    exact_mod_cast hcard_nat
  have hcauchy :
      (∑ i ∈ s, T.singularValues i) ≤
        Real.sqrt (s.card : ℝ) * Real.sqrt (∑ i ∈ s, T.singularValues i ^ 2) :=
    finset_sum_le_sqrt_card_mul_sqrt_sum_sq s (fun i => T.singularValues i)
  have hsumsq_le :
      (∑ i ∈ s, T.singularValues i ^ 2) ≤ ∑ i : Fin n, T.singularValues i ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro i hi
      exact Finset.mem_univ i
    · intro i _hi_univ hi_not
      exact sq_nonneg (T.singularValues i)
  have hcard_factor :
      Real.sqrt (s.card : ℝ) * Real.sqrt (∑ i ∈ s, T.singularValues i ^ 2) ≤
        Real.sqrt (matrixRankBound m n : ℝ) *
          Real.sqrt (∑ i ∈ s, T.singularValues i ^ 2) := by
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hcard) (Real.sqrt_nonneg _)
  have hsum_factor :
      Real.sqrt (matrixRankBound m n : ℝ) *
          Real.sqrt (∑ i ∈ s, T.singularValues i ^ 2) ≤
        Real.sqrt (matrixRankBound m n : ℝ) *
          Real.sqrt (∑ i : Fin n, T.singularValues i ^ 2) := by
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsumsq_le) (Real.sqrt_nonneg _)
  calc
    (∑ i : Fin n, (Matrix.toEuclideanLin (𝕜 := ℝ) A).singularValues i)
        = ∑ i ∈ s, T.singularValues i := by simpa [T] using hsum_support
    _ ≤ Real.sqrt (s.card : ℝ) * Real.sqrt (∑ i ∈ s, T.singularValues i ^ 2) := hcauchy
    _ ≤ Real.sqrt (matrixRankBound m n : ℝ) *
          Real.sqrt (∑ i ∈ s, T.singularValues i ^ 2) := hcard_factor
    _ ≤ Real.sqrt (matrixRankBound m n : ℝ) *
          Real.sqrt (∑ i : Fin n, T.singularValues i ^ 2) := hsum_factor
    _ = Real.sqrt (matrixRankBound m n : ℝ) *
          Real.sqrt (∑ i : Fin n,
            (Matrix.toEuclideanLin (𝕜 := ℝ) A).singularValues i ^ 2) := by simp [T]

theorem nuclearNorm_le_sqrt_rankBound_mul_frobeniusNorm {m n : ℕ} (A : Mat m n) :
    nuclearNorm A ≤ Real.sqrt (matrixRankBound m n : ℝ) * frobeniusNorm A := by
  rw [nuclearNorm, frobeniusNorm_eq_sqrt_sum_singularValues_sq]
  exact singularValues_l1_le_sqrt_rankBound_mul_l2 A

theorem nuclearNorm_nonneg_early {m n : ℕ} (A : Mat m n) :
    0 ≤ nuclearNorm A := by
  unfold nuclearNorm
  exact Finset.sum_nonneg fun i _hi =>
    (Matrix.toEuclideanLin (𝕜 := ℝ) A).singularValues_nonneg i

theorem nuclearNorm_measurable {m n : ℕ} :
    Measurable (nuclearNorm : Mat m n → ℝ) := by
  have hEq : (nuclearNorm : Mat m n → ℝ) =
      fun A => frobeniusInner A (orthogonalizedDirection A) := by
    funext A
    exact (orthogonalizedDirection_frobeniusInner_eq_nuclearNorm A).symm
  rw [hEq]
  unfold frobeniusInner
  apply Finset.measurable_sum
  intro i _hi
  apply Finset.measurable_sum
  intro j _hj
  exact ((measurable_pi_apply j).comp (measurable_pi_apply i)).mul
    (((measurable_pi_apply j).comp (measurable_pi_apply i)).comp
      orthogonalizedDirection_measurable)

theorem stochasticMuon_W_strictPast_measurable
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n) (t : ℕ) :
    Measurable[stochasticSampleStrictPast cfg.batchSize t]
      (fun ω : SamplePath ξ cfg.batchSize => (stochasticMuonState P cfg ω t).W) :=
  stochasticMuon_W_strictPast_measurable_of_direction P cfg
    orthogonalizedDirection_measurable t

/- Every finite Algorithm 1 path stays in a deterministic Frobenius ball.
   This is the compact-path input for the source theorems' expectation
   observables; it uses only the exact partial-polar rank bound. -/
theorem stochasticMuon_W_frobeniusNorm_le_prefix
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (ω : SamplePath ξ cfg.batchSize) (t : ℕ) :
    frobeniusNorm (stochasticMuonState P cfg ω t).W ≤
      frobeniusNorm cfg.W0 +
        ∑ k ∈ Finset.range t,
          |cfg.eta k| * Real.sqrt (matrixRankBound m n : ℝ) := by
  induction t with
  | zero => simp [stochasticMuonState, stochasticMuonBaseState]
  | succ t ih =>
      rw [stochasticMuon_W_succ_eq_source_update P cfg ω t]
      rw [Finset.sum_range_succ]
      have hdir :
          frobeniusNorm
              (orthogonalizedDirection (stochasticMuonState P cfg ω t).M) ≤
            Real.sqrt (matrixRankBound m n : ℝ) :=
        frobeniusNorm_le_sqrt_rankBound_of_isThinSVDWithPolar
          (orthogonalizedDirection_isThinSVDWithPolar
            (stochasticMuonState P cfg ω t).M)
      calc
        frobeniusNorm
            ((stochasticMuonState P cfg ω t).W -
              cfg.eta t • orthogonalizedDirection
                (stochasticMuonState P cfg ω t).M) ≤
            frobeniusNorm (stochasticMuonState P cfg ω t).W +
              frobeniusNorm
                (cfg.eta t • orthogonalizedDirection
                  (stochasticMuonState P cfg ω t).M) := by
            simpa [frobeniusNorm] using
              norm_sub_le
                (stochasticMuonState P cfg ω t).W
                (cfg.eta t • orthogonalizedDirection
                  (stochasticMuonState P cfg ω t).M)
        _ = frobeniusNorm (stochasticMuonState P cfg ω t).W +
              |cfg.eta t| * frobeniusNorm
                (orthogonalizedDirection (stochasticMuonState P cfg ω t).M) := by
            rw [show frobeniusNorm
                (cfg.eta t • orthogonalizedDirection
                  (stochasticMuonState P cfg ω t).M) =
                ‖cfg.eta t • orthogonalizedDirection
                  (stochasticMuonState P cfg ω t).M‖ by rfl,
              norm_smul, Real.norm_eq_abs]
            rfl
        _ ≤ (frobeniusNorm cfg.W0 +
              ∑ k ∈ Finset.range t,
                |cfg.eta k| * Real.sqrt (matrixRankBound m n : ℝ)) +
              |cfg.eta t| * Real.sqrt (matrixRankBound m n : ℝ) :=
            add_le_add ih (mul_le_mul_of_nonneg_left hdir (abs_nonneg _))
        _ = frobeniusNorm cfg.W0 +
              (∑ k ∈ Finset.range t,
                |cfg.eta k| * Real.sqrt (matrixRankBound m n : ℝ) +
                |cfg.eta t| * Real.sqrt (matrixRankBound m n : ℝ)) := by ring

theorem stochasticMuon_W_measurable
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n) (t : ℕ) :
    Measurable
      (fun ω : SamplePath ξ cfg.batchSize => (stochasticMuonState P cfg ω t).W) := by
  apply (stochasticMuon_W_strictPast_measurable P cfg t).mono
  · unfold stochasticSampleStrictPast
    refine iSup_le fun q => iSup_le fun _hq => ?_
    have hcoord : Measurable
        (fun ω : SamplePath ξ cfg.batchSize => ω q.1 q.2) :=
      (measurable_pi_apply q.2).comp (measurable_pi_apply q.1)
    exact hcoord.comap_le
  · exact le_rfl

theorem stochasticMuon_M_measurable
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n) (t : ℕ) :
    Measurable
      (fun ω : SamplePath ξ cfg.batchSize => (stochasticMuonState P cfg ω t).M) := by
  apply (stochasticMuon_state_strictPast_measurable_of_direction P cfg
    orthogonalizedDirection_measurable t).2.mono
  · unfold stochasticSampleStrictPast
    refine iSup_le fun q => iSup_le fun _hq => ?_
    have hcoord : Measurable
        (fun ω : SamplePath ξ cfg.batchSize => ω q.1 q.2) :=
      (measurable_pi_apply q.2).comp (measurable_pi_apply q.1)
    exact hcoord.comap_le
  · exact le_rfl

/- Equation (13) in Appendix A.4, specialized to the actual random query and
   time-`t` mini-batch used by `stochasticMuonState`.  The sole local premise is
   the source-stage adaptedness fact for `W_t`; freshness and the `σ² / B`
   reduction are derived here from the canonical iid path law. -/
theorem stochasticMuon_equation_13
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (t : ℕ) (sigma : ℝ) (hvariance : BoundedVariance P sigma)
    (hW : Measurable[stochasticSampleStrictPast cfg.batchSize t]
      (fun ω : SamplePath ξ cfg.batchSize => (stochasticMuonState P cfg ω t).W)) :
    ∫ ω,
        frobeniusNorm
          (stochasticBatchGradient P cfg.batchSize
              (stochasticMuonState P cfg ω t).W (ω t) -
            P.objective.grad (stochasticMuonState P cfg ω t).W) ^ 2
      ∂(samplePathLaw P cfg.batchSize) ≤
        sigma ^ 2 / (cfg.batchSize.val : ℝ) := by
  classical
  letI : IsProbabilityMeasure P.sampleLaw := P.isProbability_sampleLaw
  let pathLaw := samplePathLaw P cfg.batchSize
  letI : IsProbabilityMeasure pathLaw := by
    dsimp [pathLaw, samplePathLaw]
    infer_instance
  let query : SamplePath ξ cfg.batchSize → Mat m n :=
    fun ω => (stochasticMuonState P cfg ω t).W
  let sampleCoord : (ℕ × Fin cfg.batchSize.val) → SamplePath ξ cfg.batchSize → ξ :=
    fun q ω => ω q.1 q.2
  let pastSet : Set (ℕ × Fin cfg.batchSize.val) := {q | q.1 < t}
  have hcoord_meas : ∀ q, Measurable (sampleCoord q) := by
    intro q
    exact (measurable_pi_apply q.2).comp (measurable_pi_apply q.1)
  have hcoord_iIndep : ProbabilityTheory.iIndepFun sampleCoord pathLaw := by
    simpa [sampleCoord, pathLaw, samplePathLaw] using
      (SOptLib.iidMiniBatchSampleLaw_iIndepFun_eval
        cfg.batchSize.val P.sampleLaw)
  have hstrict_eq :
      stochasticSampleStrictPast cfg.batchSize t =
        (⨆ q ∈ pastSet,
          MeasurableSpace.comap (sampleCoord q)
            (by infer_instance : MeasurableSpace ξ)) := by
    rfl
  have hquery_past :
      Measurable[stochasticSampleStrictPast cfg.batchSize t] query := by
    simpa [query] using hW
  have hstrict_ambient :
      stochasticSampleStrictPast cfg.batchSize t ≤
        (by infer_instance : MeasurableSpace (SamplePath ξ cfg.batchSize)) := by
    rw [hstrict_eq]
    refine iSup_le ?_
    intro q
    refine iSup_le ?_
    intro _hq
    exact (hcoord_meas q).comap_le
  have hquery_meas : Measurable query := hquery_past.mono hstrict_ambient le_rfl
  have hpast_current (i : Fin cfg.batchSize.val) :
      Disjoint pastSet ({(t, i)} : Set (ℕ × Fin cfg.batchSize.val)) := by
    rw [Set.disjoint_singleton_right]
    intro hmem
    exact (Nat.lt_irrefl t) hmem
  have hfresh (i : Fin cfg.batchSize.val) :=
    indepFun_prefixKey_current_of_iIndepFun
      (μ := pathLaw) (sampleCoord := sampleCoord)
      hcoord_meas hcoord_iIndep
      (prefixKey := query)
      (pastSet := pastSet)
      (strictPast := stochasticSampleStrictPast cfg.batchSize t)
      hquery_past (by simpa [hstrict_eq]) (hpast_current i)
  have hindep_query : ∀ i ∈ (Finset.univ : Finset (Fin cfg.batchSize.val)),
      ProbabilityTheory.IndepFun query (fun ω => ω t i) pathLaw := by
    intro i _hi
    simpa [sampleCoord] using (hfresh i).1
  have hindep_query_peer :
      ∀ i ∈ (Finset.univ : Finset (Fin cfg.batchSize.val)),
        ∀ j ∈ (Finset.univ : Finset (Fin cfg.batchSize.val)), i ≠ j →
          ProbabilityTheory.IndepFun (fun ω => (query ω, ω t j))
            (fun ω => ω t i) pathLaw := by
    intro i _hi j _hj hij
    have hdisj :
        Disjoint (pastSet ∪ ({(t, j)} : Set (ℕ × Fin cfg.batchSize.val)))
          ({(t, i)} : Set (ℕ × Fin cfg.batchSize.val)) := by
      rw [Set.disjoint_singleton_right]
      intro hmem
      rcases hmem with hmem | hmem
      · exact (Nat.lt_irrefl t) hmem
      · exact hij (Prod.mk.inj hmem).2
    simpa [sampleCoord] using (hfresh i).2 (t, j) hdisj
  have hres_mat_meas :
      Measurable (fun p : Mat m n × ξ =>
        P.sampleGrad p.1 p.2 - P.objective.grad p.1) :=
    P.sampleGradKernel.property.sub
      (P.objective.grad_measurable.comp measurable_fst)
  have hres_meas :
      Measurable (fun p : Mat m n × ξ =>
        matrixToEuclidean (P.sampleGrad p.1 p.2) -
          matrixToEuclidean (P.objective.grad p.1)) := by
    simpa [matrixToEuclidean_sub] using
      matrixToEuclidean_measurable.comp hres_mat_meas
  have hY_meas : ∀ i ∈ (Finset.univ : Finset (Fin cfg.batchSize.val)),
      Measurable (fun ω : SamplePath ξ cfg.batchSize => ω t i) := by
    intro i _hi
    exact (measurable_pi_apply i).comp (measurable_pi_apply t)
  have hmap (i : Fin cfg.batchSize.val) :
      Measure.map (fun ω : SamplePath ξ cfg.batchSize => ω t i) pathLaw =
        P.sampleLaw := by
    simpa [pathLaw, samplePathLaw] using
      (SOptLib.iidMiniBatchSampleLaw_map_eval
        cfg.batchSize.val P.sampleLaw t i)
  have hfixed_int :
      ∀ i ∈ (Finset.univ : Finset (Fin cfg.batchSize.val)), ∀ z : Mat m n,
        Integrable
          (fun ω : SamplePath ξ cfg.batchSize =>
            ‖P.sampleGrad z (ω t i) - P.objective.grad z‖ ^ 2) pathLaw := by
    intro i hi z
    let phi : ξ → ℝ := fun s => ‖P.sampleGrad z s - P.objective.grad z‖ ^ 2
    have hphi : Measurable phi := by
      simpa [phi] using
        (hres_mat_meas.comp
          ((measurable_const : Measurable fun _ : ξ => z).prodMk measurable_id)).norm.pow_const 2
    have hmapped : Integrable phi
        (Measure.map (fun ω : SamplePath ξ cfg.batchSize => ω t i) pathLaw) := by
      rw [hmap i]
      simpa [phi, frobeniusNorm, SOptLib.expectationWellDefined] using
        (hvariance.variance z).choose
    exact (integrable_map_measure hphi.aestronglyMeasurable
      (hY_meas i hi).aemeasurable).mp hmapped
  have hfixed_bound :
      ∀ i ∈ (Finset.univ : Finset (Fin cfg.batchSize.val)), ∀ z : Mat m n,
        ∫ ω : SamplePath ξ cfg.batchSize,
            ‖P.sampleGrad z (ω t i) - P.objective.grad z‖ ^ 2 ∂pathLaw ≤ sigma ^ 2 := by
    intro i hi z
    let phi : ξ → ℝ := fun s => ‖P.sampleGrad z s - P.objective.grad z‖ ^ 2
    have hphi : AEStronglyMeasurable phi P.sampleLaw := by
      have hm : Measurable phi := by
        simpa [phi] using
          (hres_mat_meas.comp
            ((measurable_const : Measurable fun _ : ξ => z).prodMk measurable_id)).norm.pow_const 2
      exact hm.aestronglyMeasurable
    calc
      ∫ ω : SamplePath ξ cfg.batchSize,
          ‖P.sampleGrad z (ω t i) - P.objective.grad z‖ ^ 2 ∂pathLaw =
          ∫ s, phi s ∂P.sampleLaw := by
            rw [← hmap i]
            exact (integral_map (hY_meas i hi).aemeasurable
              (hphi.mono_measure (by rw [hmap i]))).symm
      _ ≤ sigma ^ 2 := by
        simpa [phi, frobeniusNorm, realizedExpectation] using
          (hvariance.variance z).choose_spec
  have hfixed_zero_mat :
      ∀ i ∈ (Finset.univ : Finset (Fin cfg.batchSize.val)), ∀ z : Mat m n,
        ∫ s, P.sampleGrad z s - P.objective.grad z
          ∂Measure.map (fun ω : SamplePath ξ cfg.batchSize => ω t i) pathLaw = 0 := by
    intro i _hi z
    rw [hmap i]
    have hGint : Integrable (fun s => P.sampleGrad z s) P.sampleLaw := by
      simpa [SOptLib.expectationWellDefined] using (hvariance.unbiased z).choose
    rw [integral_sub hGint (integrable_const _)]
    have hmean : ∫ s, P.sampleGrad z s ∂P.sampleLaw = P.objective.grad z := by
      simpa [realizedExpectation] using (hvariance.unbiased z).choose_spec
    rw [hmean]
    simp
  have hfixed_int_euclidean :
      ∀ i ∈ (Finset.univ : Finset (Fin cfg.batchSize.val)), ∀ z : Mat m n,
        Integrable
          (fun ω : SamplePath ξ cfg.batchSize =>
            ‖matrixToEuclidean (P.sampleGrad z (ω t i)) -
              matrixToEuclidean (P.objective.grad z)‖ ^ 2) pathLaw := by
    intro i hi z
    simpa [← matrixToEuclidean_sub, norm_matrixToEuclidean] using
      hfixed_int i hi z
  have hfixed_bound_euclidean :
      ∀ i ∈ (Finset.univ : Finset (Fin cfg.batchSize.val)), ∀ z : Mat m n,
        ∫ ω : SamplePath ξ cfg.batchSize,
            ‖matrixToEuclidean (P.sampleGrad z (ω t i)) -
              matrixToEuclidean (P.objective.grad z)‖ ^ 2 ∂pathLaw ≤ sigma ^ 2 := by
    intro i hi z
    simpa [← matrixToEuclidean_sub, norm_matrixToEuclidean] using
      hfixed_bound i hi z
  have hfixed_zero :
      ∀ i ∈ (Finset.univ : Finset (Fin cfg.batchSize.val)), ∀ z : Mat m n,
        ∫ s,
            matrixToEuclidean (P.sampleGrad z s) -
              matrixToEuclidean (P.objective.grad z)
          ∂Measure.map (fun ω : SamplePath ξ cfg.batchSize => ω t i) pathLaw = 0 := by
    intro i hi z
    let mu := Measure.map (fun ω : SamplePath ξ cfg.batchSize => ω t i) pathLaw
    have hGint : Integrable (fun s => P.sampleGrad z s) mu := by
      rw [show mu = P.sampleLaw from hmap i]
      simpa [SOptLib.expectationWellDefined] using (hvariance.unbiased z).choose
    have hresint : Integrable (fun s => P.sampleGrad z s - P.objective.grad z) mu :=
      hGint.sub (integrable_const _)
    have hlin := ContinuousLinearMap.integral_comp_comm
      (L := matrixToEuclideanCLM (m := m) (n := n)) hresint
    calc
      ∫ s, matrixToEuclidean (P.sampleGrad z s) -
          matrixToEuclidean (P.objective.grad z) ∂mu =
          matrixToEuclideanCLM
            (∫ s, P.sampleGrad z s - P.objective.grad z ∂mu) := by
              simpa [matrixToEuclidean_sub] using hlin
      _ = 0 := by rw [hfixed_zero_mat i hi z]; rfl
  have hbound :=
    randomQuery_centeredMiniBatchAverage_secondMoment_le_variance_div_card
      (P := pathLaw) (I := (Finset.univ : Finset (Fin cfg.batchSize.val)))
      (m := cfg.batchSize.val)
      (G := fun W z => matrixToEuclidean (P.sampleGrad W z))
      (target := fun W => matrixToEuclidean (P.objective.grad W))
      (xq := query) (Y := fun i ω => ω t i) (sigma ^ 2)
      cfg.batchSize.positive (by simp) hres_meas hquery_meas hY_meas
      hindep_query hindep_query_peer (sq_nonneg sigma)
      hfixed_int_euclidean hfixed_bound_euclidean hfixed_zero
  have hcenter : ∀ ω : SamplePath ξ cfg.batchSize,
      stochasticBatchGradient P cfg.batchSize (query ω) (ω t) -
          P.objective.grad (query ω) =
        ((cfg.batchSize.val : ℝ)⁻¹) •
          ∑ i : Fin cfg.batchSize.val,
            (P.sampleGrad (query ω) (ω t i) - P.objective.grad (query ω)) := by
    intro ω
    exact miniBatchAverage_sub_target_eq_average_residual
      Finset.univ cfg.batchSize.val (by simp) cfg.batchSize.positive
      (fun i => P.sampleGrad (query ω) (ω t i)) (P.objective.grad (query ω))
  have hcenter_euclidean : ∀ ω : SamplePath ξ cfg.batchSize,
      ((cfg.batchSize.val : ℝ)⁻¹) •
          ∑ i : Fin cfg.batchSize.val,
            (matrixToEuclidean (P.sampleGrad (query ω) (ω t i)) -
              matrixToEuclidean (P.objective.grad (query ω))) =
        matrixToEuclidean
          (stochasticBatchGradient P cfg.batchSize (query ω) (ω t) -
            P.objective.grad (query ω)) := by
    intro ω
    rw [hcenter]
    symm
    change matrixToEuclideanCLM
        (((cfg.batchSize.val : ℝ)⁻¹) •
          ∑ i : Fin cfg.batchSize.val,
            (P.sampleGrad (query ω) (ω t i) - P.objective.grad (query ω))) = _
    rw [map_smul, map_sum]
    simp [matrixToEuclidean_sub]
  change
    (∫ ω,
        frobeniusNorm
          (stochasticBatchGradient P cfg.batchSize (query ω) (ω t) -
            P.objective.grad (query ω)) ^ 2 ∂pathLaw) ≤
      sigma ^ 2 / (cfg.batchSize.val : ℝ)
  calc
    ∫ ω,
        frobeniusNorm
          (stochasticBatchGradient P cfg.batchSize (query ω) (ω t) -
            P.objective.grad (query ω)) ^ 2 ∂pathLaw =
      ∫ ω,
        ‖((cfg.batchSize.val : ℝ)⁻¹) •
          ∑ i : Fin cfg.batchSize.val,
            (matrixToEuclidean (P.sampleGrad (query ω) (ω t i)) -
              matrixToEuclidean (P.objective.grad (query ω)))‖ ^ 2 ∂pathLaw := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [← norm_matrixToEuclidean, ← hcenter_euclidean ω]
    _ ≤ sigma ^ 2 / (cfg.batchSize.val : ℝ) := hbound

/- Equation (13) with an explicit direction-measurability premise.  The
   unconditional source-assumption version below instantiates this premise
   from the exact polynomial-limit realization of the partial polar. -/
theorem stochasticMuon_equation_13_of_direction_measurable
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (t : ℕ) (sigma : ℝ) (hvariance : BoundedVariance P sigma)
    (hdir : Measurable (orthogonalizedDirection : Mat m n → Mat m n)) :
    ∫ ω,
        frobeniusNorm
          (stochasticBatchGradient P cfg.batchSize
              (stochasticMuonState P cfg ω t).W (ω t) -
            P.objective.grad (stochasticMuonState P cfg ω t).W) ^ 2
      ∂(samplePathLaw P cfg.batchSize) ≤
        sigma ^ 2 / (cfg.batchSize.val : ℝ) :=
  stochasticMuon_equation_13 P cfg t sigma hvariance
    (stochasticMuon_W_strictPast_measurable_of_direction P cfg hdir t)

/- The deterministic `C_t` process in Lemma A.4: it follows the same random
   iterates as Algorithm 1, but replaces every mini-batch gradient by the true
   gradient. -/
def stochasticMuonComparator {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (ω : SamplePath ξ cfg.batchSize) : ℕ → Mat m n :=
  fun t => Nat.rec (P.objective.grad cfg.W0)
    (fun k C =>
      cfg.beta • C +
        (1 - cfg.beta) • P.objective.grad (stochasticMuonState P cfg ω (k + 1)).W) t

/- The exact printed conclusion of Lemma A.4 for the canonical `C_t-M_t`
   process.  Naming it separately makes the source-stage constant/domain issue
   visible without changing any registered theorem head. -/
def stochasticMuonLemmaA4Bound {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (t : ℕ) (sigma : ℝ) : Prop :=
  (∫ ω,
      frobeniusNorm
        (stochasticMuonComparator P cfg ω t - (stochasticMuonState P cfg ω t).M)
      ∂(samplePathLaw P cfg.batchSize)) ≤
    Real.sqrt ((1 - cfg.beta) / (1 + cfg.beta)) * sigma /
        Real.sqrt (cfg.batchSize.val : ℝ) +
      cfg.beta ^ t * sigma / Real.sqrt (cfg.batchSize.val : ℝ)

/- A typed same-interface obstruction for the direct Lemma A.4 route.  At
   `t = 0` its printed right-hand side is strictly negative whenever `σ < 0`,
   whereas its left-hand side is an integral of a nonnegative norm. -/
theorem stochasticMuon_lemma_A4_bound_impossible_of_sigma_neg
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    {sigma : ℝ} (hsigma : sigma < 0) :
    ¬ stochasticMuonLemmaA4Bound P cfg 0 sigma := by
  intro hbound
  have hB : 0 < Real.sqrt (cfg.batchSize.val : ℝ) := by
    exact Real.sqrt_pos.2 (by exact_mod_cast cfg.batchSize.positive)
  have hcoef :
      0 < Real.sqrt ((1 - cfg.beta) / (1 + cfg.beta)) + 1 := by
    have hsqrt : 0 ≤ Real.sqrt ((1 - cfg.beta) / (1 + cfg.beta)) :=
      Real.sqrt_nonneg _
    linarith
  have hrhs :
      Real.sqrt ((1 - cfg.beta) / (1 + cfg.beta)) * sigma /
          Real.sqrt (cfg.batchSize.val : ℝ) +
        cfg.beta ^ (0 : ℕ) * sigma / Real.sqrt (cfg.batchSize.val : ℝ) < 0 := by
    rw [pow_zero, one_mul, ← add_div]
    have hnum :
        (Real.sqrt ((1 - cfg.beta) / (1 + cfg.beta)) + 1) * sigma < 0 :=
      mul_neg_of_pos_of_neg hcoef hsigma
    convert div_neg_of_neg_of_pos hnum hB using 1 <;> ring
  have hlhs :
      0 ≤ ∫ ω,
        frobeniusNorm
          (stochasticMuonComparator P cfg ω 0 - (stochasticMuonState P cfg ω 0).M)
        ∂(samplePathLaw P cfg.batchSize) := by
    have hpoint : ∀ ω : SamplePath ξ cfg.batchSize,
        (0 : ℝ) ≤ frobeniusNorm
          (stochasticMuonComparator P cfg ω 0 - (stochasticMuonState P cfg ω 0).M) := by
      intro ω
      simp only [frobeniusNorm]
      exact norm_nonneg _
    exact MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall hpoint)
  exact (not_le_of_gt hrhs) (hlhs.trans hbound)

structure DeterministicMuonConfig (m n : ℕ) where
  W0 : Mat m n
  eta : ℕ → ℝ

structure DeterministicMomentumMuonConfig (m n : ℕ) where
  W0 : Mat m n
  eta : ℕ → ℝ
  beta : ℝ
  beta_mem : beta ∈ Set.Ico (0 : ℝ) 1

def deterministicGradient {m n : ℕ} (P : Objective m n) (W : Mat m n) : Mat m n :=
  P.grad W

structure DeterministicMuonState (m n : ℕ) where
  W : Mat m n
  G : Mat m n

def deterministicMuonBaseState {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) : DeterministicMuonState m n :=
  { W := cfg.W0, G := deterministicGradient P cfg.W0 }

def deterministicMuonStep {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (t : ℕ)
    (state : DeterministicMuonState m n) : DeterministicMuonState m n :=
  let Wnext := muonUpdate state.W (cfg.eta t) (orthogonalizedDirection state.G)
  { W := Wnext, G := deterministicGradient P Wnext }

def deterministicMuonState {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) : ℕ → DeterministicMuonState m n :=
  fun t => Nat.rec (deterministicMuonBaseState P cfg)
    (fun k state => deterministicMuonStep P cfg k state) t

theorem deterministicMuon_G_eq_gradient {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (t : ℕ) :
    (deterministicMuonState P cfg t).G =
      deterministicGradient P ((deterministicMuonState P cfg t).W) := by
  cases t <;> rfl

theorem deterministicMuon_W_succ_eq_source_update {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (t : ℕ) :
    (deterministicMuonState P cfg (t + 1)).W =
      (deterministicMuonState P cfg t).W -
        cfg.eta t • orthogonalizedDirection ((deterministicMuonState P cfg t).G) := by
  cases t <;> rfl

def deterministicMomentumMuonBaseState {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMomentumMuonConfig m n) : MuonState m n :=
  { W := cfg.W0, M := deterministicGradient P cfg.W0 }

def deterministicMomentumMuonStep {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMomentumMuonConfig m n) (t : ℕ)
    (state : MuonState m n) : MuonState m n :=
  let Wnext := muonUpdate state.W (cfg.eta t) (orthogonalizedDirection state.M)
  let Gnext := deterministicGradient P Wnext
  let Mnext := cfg.beta • state.M + (1 - cfg.beta) • Gnext
  { W := Wnext, M := Mnext }

def deterministicMomentumMuonState {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMomentumMuonConfig m n) : ℕ → MuonState m n :=
  fun t => Nat.rec (deterministicMomentumMuonBaseState P cfg)
    (fun k state => deterministicMomentumMuonStep P cfg k state) t

theorem deterministicMomentumMuon_M_zero_eq_gradient {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMomentumMuonConfig m n) :
    (deterministicMomentumMuonState P cfg 0).M = deterministicGradient P cfg.W0 :=
  rfl

theorem deterministicMomentumMuon_W_succ_eq_source_update {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMomentumMuonConfig m n) (t : ℕ) :
    (deterministicMomentumMuonState P cfg (t + 1)).W =
      (deterministicMomentumMuonState P cfg t).W -
        cfg.eta t • orthogonalizedDirection
          ((deterministicMomentumMuonState P cfg t).M) := by
  cases t <;> rfl

/- The deterministic clause of Corollaries 4.2 and 4.8 is a specialization of
   Algorithm 1 at the singleton, zero-noise oracle.  Keeping this realization
   private makes the source-facing stochastic API the sole supplier of the
   deterministic momentum estimate. -/
noncomputable def deterministicOracleProblem {m n : ℕ}
    (P : Objective m n) : StochasticProblem Unit m n where
  sampleLoss := fun W _ => P.f W
  sampleLaw := Measure.dirac ()
  isProbability_sampleLaw := inferInstance
  sampleGrad_jointly_measurable := by
    simpa using
      (objectiveGradient_measurable P.f).comp measurable_fst

theorem deterministicOracleProblem_objective {m n : ℕ}
    (P : Objective m n) :
    (deterministicOracleProblem P).objective = P := by
  cases P with
  | mk f =>
      change Objective.mk _ = Objective.mk f
      apply congrArg Objective.mk
      funext W
      simp [deterministicOracleProblem, StochasticProblem.objective,
        SOptLib.objectiveExpectation_def]

theorem deterministicOracleProblem_sampleGrad {m n : ℕ}
    (P : Objective m n) (W : Mat m n) (z : Unit) :
    (deterministicOracleProblem P).sampleGrad W z = P.grad W := by
  rfl

theorem deterministicOracleProblem_boundedVariance_zero {m n : ℕ}
    (P : Objective m n) : BoundedVariance (deterministicOracleProblem P) 0 := by
  constructor
  · exact le_rfl
  · intro W
    rw [deterministicOracleProblem_objective P]
    have hsample :
        (fun z => (deterministicOracleProblem P).sampleGrad W z) =
          (fun _ : Unit => P.grad W) := by
      funext z
      exact deterministicOracleProblem_sampleGrad P W z
    rw [hsample]
    refine ⟨?_, ?_⟩
    · unfold SOptLib.expectationWellDefined
      exact MeasureTheory.integrable_dirac (by simp)
    · simp [realizedExpectation, deterministicOracleProblem]
  · intro W
    rw [deterministicOracleProblem_objective P]
    have hnoise :
        (fun z => frobeniusNorm
          ((deterministicOracleProblem P).sampleGrad W z - P.grad W) ^ 2) =
          (fun _ : Unit => (0 : ℝ)) := by
      funext z
      rw [deterministicOracleProblem_sampleGrad]
      simp [frobeniusNorm]
    rw [hnoise]
    refine ⟨?_, ?_⟩
    · unfold SOptLib.expectationWellDefined
      exact MeasureTheory.integrable_dirac (by simp)
    · simp [realizedExpectation, deterministicOracleProblem, frobeniusNorm]

def deterministicOracleBatchSize : BatchSize :=
  { val := 1, positive := by norm_num }

def deterministicOracleConfig {m n : ℕ}
    (cfg : DeterministicMomentumMuonConfig m n) : StochasticMuonConfig m n :=
  { W0 := cfg.W0
    eta := cfg.eta
    beta := cfg.beta
    beta_mem := cfg.beta_mem
    batchSize := deterministicOracleBatchSize }

theorem deterministicOracle_batchGradient {m n : ℕ}
    (P : Objective m n) (W : Mat m n)
    (samples : BatchSamples Unit deterministicOracleBatchSize) :
    stochasticBatchGradient (deterministicOracleProblem P)
      deterministicOracleBatchSize W samples = P.grad W := by
  simp [stochasticBatchGradient, deterministicOracleBatchSize,
    deterministicOracleProblem_sampleGrad]

theorem deterministicOracle_state_eq {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMomentumMuonConfig m n)
    (omega : SamplePath Unit (deterministicOracleConfig cfg).batchSize) :
    ∀ t : ℕ,
      stochasticMuonState (deterministicOracleProblem P)
          (deterministicOracleConfig cfg) omega t =
        deterministicMomentumMuonState P cfg t := by
  intro t
  induction t with
  | zero =>
      change stochasticMuonBaseState (deterministicOracleProblem P)
          (deterministicOracleConfig cfg) omega =
        deterministicMomentumMuonBaseState P cfg
      simp [stochasticMuonBaseState, deterministicMomentumMuonBaseState,
        deterministicOracleConfig, deterministicOracle_batchGradient,
        deterministicGradient]
  | succ t ih =>
      change stochasticMuonStep (deterministicOracleProblem P)
          (deterministicOracleConfig cfg) omega t
          (stochasticMuonState (deterministicOracleProblem P)
            (deterministicOracleConfig cfg) omega t) =
        deterministicMomentumMuonStep P cfg t
          (deterministicMomentumMuonState P cfg t)
      rw [ih]
      simp [stochasticMuonStep, deterministicMomentumMuonStep,
        deterministicOracleConfig, deterministicOracle_batchGradient,
        deterministicGradient]

def StarConvex {m n : ℕ} (P : Objective m n) (Wstar : Mat m n) : Prop :=
  P.IsMinimizer Wstar ∧
    ∀ W : Mat m n, frobeniusInner (P.grad W) (W - Wstar) ≥ P.f W - P.fStar

theorem StarConvex.isMinimizer {m n : ℕ} {P : Objective m n} {Wstar : Mat m n}
    (h : StarConvex P Wstar) :
    P.IsMinimizer Wstar :=
  h.1

theorem StarConvex.gradient_lower_bound {m n : ℕ} {P : Objective m n} {Wstar : Mat m n}
    (h : StarConvex P Wstar) (W : Mat m n) :
    frobeniusInner (P.grad W) (W - Wstar) ≥ P.f W - P.fStar :=
  h.2 W

def BoundedOperatorDistance {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (T : ℕ)
    (Wstar : Mat m n) (Dop : ℝ) : Prop :=
  ∀ t ∈ Finset.range (T + 1),
    spectralNorm ((deterministicMuonState P cfg t).W - Wstar) ≤ Dop

structure ThirdDerivativeBounded {m n : ℕ} (P : Objective m n) (s : ℝ) : Prop where
  contDiff : ContDiff ℝ 3 (vectorizedObjective P)
  bound : ∀ w : Mat m n, ‖iteratedFDeriv ℝ 3 (vectorizedObjective P) w‖ ≤ s

theorem ThirdDerivativeBounded.contDiff' {m n : ℕ} {P : Objective m n} {s : ℝ}
    (h : ThirdDerivativeBounded P s) :
    ContDiff ℝ 3 (vectorizedObjective P) :=
  h.contDiff

theorem ThirdDerivativeBounded.objective_continuous {m n : ℕ}
    {P : Objective m n} {s : ℝ} (h : ThirdDerivativeBounded P s) :
    Continuous P.f := by
  simpa [vectorizedObjective] using h.contDiff.continuous

theorem ThirdDerivativeBounded.gradient_continuous {m n : ℕ}
    {P : Objective m n} {s : ℝ} (h : ThirdDerivativeBounded P s) :
    Continuous P.grad := by
  unfold Objective.grad objectiveGradient
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (h.contDiff.continuous_fderiv_apply (by norm_num)).comp
    (continuous_id.prodMk continuous_const)

/- The stochastic source theorems use exactly one of Assumptions 3.1, 3.2,
   or 4.13.  This internal disjunction prevents well-definedness from being
   (incorrectly) attributed to Assumption 3.3 alone. -/
def StochasticObjectiveRegularity {m n : ℕ} (P : Objective m n) : Prop :=
  (∃ L : ℝ, FrobeniusSmooth P L) ∨
    (∃ Lstar : ℝ, SpectralSmooth P Lstar) ∨
      ∃ s : ℝ, ThirdDerivativeBounded P s

theorem objective_gradient_continuous_of_contDiff_one
    {m n : ℕ} (P : Objective m n)
    (h : ContDiff ℝ 1 (vectorizedObjective P)) :
    Continuous P.grad := by
  unfold Objective.grad objectiveGradient
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (h.continuous_fderiv_apply (by norm_num)).comp
    (continuous_id.prodMk continuous_const)

theorem StochasticObjectiveRegularity.objective_continuous
    {m n : ℕ} {P : Objective m n} (h : StochasticObjectiveRegularity P) :
    Continuous P.f := by
  rcases h with ⟨L, hL⟩ | ⟨Lstar, hLstar⟩ | ⟨s, hs⟩
  · exact hL.objective_continuous
  · exact hLstar.objective_continuous
  · exact hs.objective_continuous

theorem StochasticObjectiveRegularity.gradient_continuous
    {m n : ℕ} {P : Objective m n} (h : StochasticObjectiveRegularity P) :
    Continuous P.grad := by
  rcases h with ⟨L, hL⟩ | ⟨Lstar, hLstar⟩ | ⟨s, hs⟩
  · exact objective_gradient_continuous_of_contDiff_one P hL.contDiff
  · exact objective_gradient_continuous_of_contDiff_one P hLstar.contDiff
  · exact hs.gradient_continuous

theorem objective_grad_contDiff_two_of_vectorized_contDiff_three
    {m n : ℕ} (P : Objective m n)
    (hcont : ContDiff ℝ 3 (vectorizedObjective P)) :
    ContDiff ℝ 2 P.grad := by
  classical
  let H : (Mat m n →L[ℝ] ℝ) →ₗ[ℝ] Mat m n :=
    { toFun := fun L => fun i j => L (coordinateMatrix i j)
      map_add' := by
        intro L L'
        ext i j
        simp
      map_smul' := by
        intro c L
        ext i j
        simp }
  let Hc : (Mat m n →L[ℝ] ℝ) →L[ℝ] Mat m n :=
    H.toContinuousLinearMap
  have hcont' : ContDiff ℝ (2 + 1) (vectorizedObjective P) := by
    simpa using hcont
  have hfd :
      ContDiff ℝ 2 (fderiv ℝ (vectorizedObjective P)) :=
    (contDiff_succ_iff_fderiv.mp hcont').2.2
  have hc := hfd.continuousLinearMap_comp Hc
  simpa [Objective.grad, objectiveGradient, H, Hc, Function.comp_def] using hc

def SymmetricMatrix {n : ℕ} (Λ : Mat n n) : Prop :=
  Λᵀ = Λ

def MatrixPositiveDefinite {n : ℕ} (Λ : Mat n n) : Prop :=
  Λ.PosDef

theorem MatrixPositiveDefinite_eq_mathlib_PosDef {n : ℕ} (Λ : Mat n n) :
    MatrixPositiveDefinite Λ = Λ.PosDef :=
  rfl

noncomputable def lambdaNorm {m n : ℕ} (Λ : Mat n n) (A : Mat m n) : ℝ :=
  Real.sqrt (frobeniusInner (A * Λ) A)

noncomputable def lambdaInvNorm {m n : ℕ} (Λ : Mat n n) (A : Mat m n) : ℝ :=
  lambdaNorm Λ⁻¹ A

def LambdaSmooth {m n : ℕ} (P : Objective m n) (Λ : Mat n n) : Prop :=
  MatrixPositiveDefinite Λ ∧ ContDiff ℝ 1 (vectorizedObjective P) ∧
    ∀ W W' : Mat m n,
      lambdaInvNorm Λ (P.grad W - P.grad W') ≤ lambdaNorm Λ (W - W')

theorem LambdaSmooth.positiveDefinite {m n : ℕ} {P : Objective m n} {Λ : Mat n n}
    (h : LambdaSmooth P Λ) :
    MatrixPositiveDefinite Λ :=
  h.1

theorem LambdaSmooth.contDiff {m n : ℕ} {P : Objective m n} {Λ : Mat n n}
    (h : LambdaSmooth P Λ) :
    ContDiff ℝ 1 (vectorizedObjective P) :=
  h.2.1

theorem LambdaSmooth.lipschitz_grad {m n : ℕ} {P : Objective m n} {Λ : Mat n n}
    (h : LambdaSmooth P Λ) (W W' : Mat m n) :
    lambdaInvNorm Λ (P.grad W - P.grad W') ≤ lambdaNorm Λ (W - W') :=
  h.2.2 W W'

/-- Source-facing bookkeeping for asymptotic constants.

The paper's `O`, `\tilde O`, and `\gtrsim` clauses are not scalar inequalities at
a single horizon.  This record names which paper parameters a hidden constant
may depend on and which asymptotic variables it must be independent of.  The
predicate below is intentionally proof-light in Phase 0; later phases prove the
actual bounds from the displayed theorem inequalities. -/
structure AsymptoticScope where
  mayDependOn : List String
  independentOf : List String
  constantPredicate : ℝ → Prop := fun C => 0 < C

def ConstantRespectsScope (scope : AsymptoticScope) (C : ℝ) : Prop :=
  0 < C ∧ scope.constantPredicate C

def horizonDomain (T : ℕ) : Prop :=
  0 < T

def epsilonDomain (ε : ℝ) : Prop :=
  0 < ε

def AsymptoticUpperNat
    (domain : ℕ → Prop) (lhs rate : ℕ → ℝ) (scope : AsymptoticScope) : Prop :=
  ∃ C : ℝ, ∃ T₀ : ℕ,
    0 < C ∧ ConstantRespectsScope scope C ∧
      ∀ T : ℕ, domain T → T₀ ≤ T → lhs T ≤ C * rate T

def AsymptoticUpperNatOn
    (domain : ℕ → Prop) (lhs : ∀ T : ℕ, domain T → ℝ)
    (rate : ℕ → ℝ) (scope : AsymptoticScope) : Prop :=
  ∃ C : ℝ, ∃ T₀ : ℕ,
    0 < C ∧ ConstantRespectsScope scope C ∧
      ∀ T : ℕ, ∀ hT : domain T, T₀ ≤ T → lhs T hT ≤ C * rate T

def DomainAsymptoticUpperNatOn
    (domain : ℕ → Prop) (lhs rate : ∀ T : ℕ, domain T → ℝ)
    (scope : AsymptoticScope) : Prop :=
  ∃ C : ℝ, ∃ T₀ : ℕ,
    0 < C ∧ ConstantRespectsScope scope C ∧
      ∀ T : ℕ, ∀ hT : domain T, T₀ ≤ T → lhs T hT ≤ C * rate T hT

def DomainAsymptoticLowerNatOn
    (domain : ℕ → Prop) (lhs rate : ∀ T : ℕ, domain T → ℝ)
    (scope : AsymptoticScope) : Prop :=
  ∃ c : ℝ, ∃ T₀ : ℕ,
    0 < c ∧ ConstantRespectsScope scope c ∧
      ∀ T : ℕ, ∀ hT : domain T, T₀ ≤ T → c * rate T hT ≤ lhs T hT

def DomainAsymptoticThetaNatOn
    (domain : ℕ → Prop) (lhs rate : ∀ T : ℕ, domain T → ℝ)
    (scope : AsymptoticScope) : Prop :=
  DomainAsymptoticUpperNatOn domain lhs rate scope ∧
    DomainAsymptoticLowerNatOn domain lhs rate scope

def AsymptoticLowerNat
    (domain : ℕ → Prop) (lhs rate : ℕ → ℝ) (scope : AsymptoticScope) : Prop :=
  ∃ c : ℝ, ∃ T₀ : ℕ,
    0 < c ∧ ConstantRespectsScope scope c ∧
      ∀ T : ℕ, domain T → T₀ ≤ T → c * rate T ≤ lhs T

def AsymptoticThetaNat
    (domain : ℕ → Prop) (lhs rate : ℕ → ℝ) (scope : AsymptoticScope) : Prop :=
  AsymptoticUpperNat domain lhs rate scope ∧ AsymptoticLowerNat domain lhs rate scope

def AsymptoticUpperReal
    (domain : ℝ → Prop) (lhs rate : ℝ → ℝ) (scope : AsymptoticScope) : Prop :=
  ∃ C : ℝ, ∃ ε₀ : ℝ,
    0 < C ∧ 0 < ε₀ ∧ ConstantRespectsScope scope C ∧
      ∀ ε : ℝ, domain ε → 0 < ε → ε ≤ ε₀ → lhs ε ≤ C * rate ε

def AsymptoticUpperRealOn
    (domain : ℝ → Prop) (lhs rate : ∀ ε : ℝ, domain ε → ℝ)
    (scope : AsymptoticScope) : Prop :=
  ∃ C : ℝ, ∃ ε₀ : ℝ,
    0 < C ∧ 0 < ε₀ ∧ ConstantRespectsScope scope C ∧
      ∀ ε : ℝ, ∀ hε : domain ε, 0 < ε → ε ≤ ε₀ →
        lhs ε hε ≤ C * rate ε hε

def AsymptoticLowerReal
    (domain : ℝ → Prop) (lhs rate : ℝ → ℝ) (scope : AsymptoticScope) : Prop :=
  ∃ c : ℝ, ∃ ε₀ : ℝ,
    0 < c ∧ 0 < ε₀ ∧ ConstantRespectsScope scope c ∧
      ∀ ε : ℝ, domain ε → 0 < ε → ε ≤ ε₀ → c * rate ε ≤ lhs ε

/- A tilde-O bound permits a fixed power of a logarithm, but its multiplicative
   constant is still independent of the asymptotic variable.  Encoding the
   logarithm in the inequality (rather than only in `AsymptoticScope` metadata)
   is essential: for example, `(log T)^2 / T` is tilde-O of `1 / T` but is not
   ordinary O of `1 / T`. -/
def natPolylogEnvelope (k T : ℕ) : ℝ :=
  (max 1 (Real.log (T : ℝ))) ^ k

def accuracyPolylogEnvelope (k : ℕ) (ε : ℝ) : ℝ :=
  (max 1 (Real.log ε⁻¹)) ^ k

def TildeAsymptoticUpperReal
    (domain : ℝ → Prop) (lhs rate : ℝ → ℝ) (scope : AsymptoticScope) : Prop :=
  ∃ k : ℕ,
    AsymptoticUpperReal domain lhs
      (fun ε => accuracyPolylogEnvelope k ε * rate ε) scope

def TildeAsymptoticUpperNat
    (domain : ℕ → Prop) (lhs rate : ℕ → ℝ) (scope : AsymptoticScope) : Prop :=
  ∃ k : ℕ,
    AsymptoticUpperNat domain lhs
      (fun T => natPolylogEnvelope k T * rate T) scope

def TildeAsymptoticUpperNatOn
    (domain : ℕ → Prop) (lhs rate : ∀ T : ℕ, domain T → ℝ)
    (scope : AsymptoticScope) : Prop :=
  ∃ k : ℕ,
    DomainAsymptoticUpperNatOn domain lhs
      (fun T hT => natPolylogEnvelope k T * rate T hT) scope

def objectiveGapAt {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (T : ℕ) : ℝ :=
  P.f ((deterministicMuonState P cfg T).W) - P.fStar

def sourceObjectiveGapAt {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (T : ℕ)
    (hfinite : P.HasFiniteInfimum) : ℝ :=
  P.f ((deterministicMuonState P cfg T).W) - P.sourceFStar hfinite

theorem sourceObjectiveGapAt_eq_objectiveGapAt {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (T : ℕ)
    (hfinite : P.HasFiniteInfimum) :
    sourceObjectiveGapAt P cfg T hfinite = objectiveGapAt P cfg T :=
  rfl

def ObjectivePrecisionComplexity {m n : ℕ}
    (P : Objective m n) (cfgFor : ℝ → DeterministicMuonConfig m n)
    (rate : ℝ → ℝ) (scope : AsymptoticScope) : Prop :=
  ∃ horizonBound : ℝ → ℝ,
    AsymptoticUpperReal epsilonDomain horizonBound rate scope ∧
      ∀ ε : ℝ, epsilonDomain ε →
        ∃ T : ℕ, (T : ℝ) ≤ horizonBound ε ∧ objectiveGapAt P (cfgFor ε) T ≤ ε

def ObjectivePrecisionComplexityUnder {m n : ℕ}
    (P : Objective m n) (cfgFor : ℝ → DeterministicMuonConfig m n)
    (runAssumptions : ℝ → ℕ → Prop)
    (rate : ℝ → ℝ) (scope : AsymptoticScope) : Prop :=
  ∃ horizonBound : ℝ → ℝ,
    AsymptoticUpperReal epsilonDomain horizonBound rate scope ∧
      ∀ ε : ℝ, epsilonDomain ε →
        ∃ T : ℕ, (T : ℝ) ≤ horizonBound ε ∧
          runAssumptions ε T ∧ objectiveGapAt P (cfgFor ε) T ≤ ε

def SourceObjectivePrecisionComplexityUnder {m n : ℕ}
    (P : Objective m n) (hfinite : P.HasFiniteInfimum)
    (cfgFor : ℝ → DeterministicMuonConfig m n)
    (runAssumptions : ℝ → ℕ → Prop)
    (rate : ℝ → ℝ) (scope : AsymptoticScope) : Prop :=
  ∃ horizonBound : ℝ → ℝ,
    AsymptoticUpperReal epsilonDomain horizonBound rate scope ∧
      ∀ ε : ℝ, epsilonDomain ε →
        ∃ T : ℕ, (T : ℝ) ≤ horizonBound ε ∧
          runAssumptions ε T ∧ sourceObjectiveGapAt P (cfgFor ε) T hfinite ≤ ε

def SourceObjectivePrecisionComplexityUnderOn {m n : ℕ}
    (P : Objective m n) (hfinite : P.HasFiniteInfimum)
    (accuracyDomain : ℝ → Prop)
    (cfgFor : ∀ ε : ℝ, accuracyDomain ε → DeterministicMuonConfig m n)
    (runAssumptions : ∀ ε : ℝ, accuracyDomain ε → ℕ → Prop)
    (rate : ∀ ε : ℝ, accuracyDomain ε → ℝ) (scope : AsymptoticScope) : Prop :=
  ∃ horizonBound : ∀ ε : ℝ, accuracyDomain ε → ℝ,
    AsymptoticUpperRealOn accuracyDomain horizonBound rate scope ∧
      ∀ ε : ℝ, ∀ hε : accuracyDomain ε, epsilonDomain ε →
        ∃ T : ℕ, (T : ℝ) ≤ horizonBound ε hε ∧
          runAssumptions ε hε T ∧
            sourceObjectiveGapAt P (cfgFor ε hε) T hfinite ≤ ε

def ObjectiveRunPrecisionComplexity {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (rate : ℝ → ℝ) (scope : AsymptoticScope) : Prop :=
  ∃ horizonBound : ℝ → ℝ,
    AsymptoticUpperReal epsilonDomain horizonBound rate scope ∧
      ∀ ε : ℝ, epsilonDomain ε →
        ∃ T : ℕ, (T : ℝ) ≤ horizonBound ε ∧ objectiveGapAt P cfg T ≤ ε

def ObjectiveRunPrecisionComplexityUnder {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (runAssumptions : ℝ → ℕ → Prop)
    (rate : ℝ → ℝ) (scope : AsymptoticScope) : Prop :=
  ∃ horizonBound : ℝ → ℝ,
    AsymptoticUpperReal epsilonDomain horizonBound rate scope ∧
      ∀ ε : ℝ, epsilonDomain ε →
        ∃ T : ℕ, (T : ℝ) ≤ horizonBound ε ∧
          runAssumptions ε T ∧ objectiveGapAt P cfg T ≤ ε

def SourceObjectiveRunPrecisionComplexityUnder {m n : ℕ}
    (P : Objective m n) (hfinite : P.HasFiniteInfimum)
    (cfg : DeterministicMuonConfig m n)
    (runAssumptions : ℝ → ℕ → Prop)
    (rate : ℝ → ℝ) (scope : AsymptoticScope) : Prop :=
  ∃ horizonBound : ℝ → ℝ,
    AsymptoticUpperReal epsilonDomain horizonBound rate scope ∧
      ∀ ε : ℝ, epsilonDomain ε →
        ∃ T : ℕ, (T : ℝ) ≤ horizonBound ε ∧
          runAssumptions ε T ∧ sourceObjectiveGapAt P cfg T hfinite ≤ ε

def HorizonObjectivePrecisionComplexity {m n : ℕ}
    (P : Objective m n) (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (runAssumptions : ℕ → Prop)
    (rate : ℝ → ℝ) (scope : AsymptoticScope) : Prop :=
  ∃ horizonBound : ℝ → ℝ,
    AsymptoticUpperReal epsilonDomain horizonBound rate scope ∧
      ∀ ε : ℝ, epsilonDomain ε →
        ∃ T : ℕ, (T : ℝ) ≤ horizonBound ε ∧
          runAssumptions T ∧ objectiveGapAt P (cfgForHorizon T) T ≤ ε

def HorizonObjectivePrecisionComplexityWithHorizonRate {m n : ℕ}
    (P : Objective m n) (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (runAssumptions : ℕ → Prop)
    (rateAt : ℕ → ℝ → ℝ) (scope : AsymptoticScope) : Prop :=
  ∃ C : ℝ, ∃ ε₀ : ℝ,
    0 < C ∧ 0 < ε₀ ∧ ConstantRespectsScope scope C ∧
      ∀ ε : ℝ, epsilonDomain ε → ε ≤ ε₀ →
        ∃ T : ℕ, runAssumptions T ∧ objectiveGapAt P (cfgForHorizon T) T ≤ ε ∧
          (T : ℝ) ≤ C * rateAt T ε

def SourceHorizonObjectivePrecisionComplexityWithHorizonRate {m n : ℕ}
    (P : Objective m n) (hfinite : P.HasFiniteInfimum)
    (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (runAssumptions : ℕ → Prop)
    (rateAt : ℕ → ℝ → ℝ) (scope : AsymptoticScope) : Prop :=
  ∃ C : ℝ, ∃ ε₀ : ℝ,
    0 < C ∧ 0 < ε₀ ∧ ConstantRespectsScope scope C ∧
      ∀ ε : ℝ, epsilonDomain ε → ε ≤ ε₀ →
        ∃ T : ℕ, runAssumptions T ∧ sourceObjectiveGapAt P (cfgForHorizon T) T hfinite ≤ ε ∧
          (T : ℝ) ≤ C * rateAt T ε

def TildeSourceHorizonObjectivePrecisionComplexityWithHorizonRate {m n : ℕ}
    (P : Objective m n) (hfinite : P.HasFiniteInfimum)
    (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (runAssumptions : ℕ → Prop)
    (rateAt : ℕ → ℝ → ℝ) (scope : AsymptoticScope) : Prop :=
  ∃ k : ℕ, ∃ C : ℝ, ∃ ε₀ : ℝ,
    0 < C ∧ 0 < ε₀ ∧ ConstantRespectsScope scope C ∧
      ∀ ε : ℝ, epsilonDomain ε → ε ≤ ε₀ →
        ∃ T : ℕ, runAssumptions T ∧
          sourceObjectiveGapAt P (cfgForHorizon T) T hfinite ≤ ε ∧
          (T : ℝ) ≤ C * (accuracyPolylogEnvelope k ε * rateAt T ε)

def NuclearStationarityComplexity
    (averageForHorizon : ℕ → ℝ) (rate : ℝ → ℝ) (scope : AsymptoticScope) : Prop :=
  ∃ horizonBound : ℝ → ℝ,
    AsymptoticUpperReal epsilonDomain horizonBound rate scope ∧
      ∀ ε : ℝ, epsilonDomain ε →
        ∃ T : ℕ, (T : ℝ) ≤ horizonBound ε ∧ averageForHorizon T ≤ ε

def NuclearStationarityComplexityOn
    (domain : ℕ → Prop) (averageForHorizon : ∀ T : ℕ, domain T → ℝ)
    (rate : ℝ → ℝ) (scope : AsymptoticScope) : Prop :=
  ∃ horizonBound : ℝ → ℝ,
    AsymptoticUpperReal epsilonDomain horizonBound rate scope ∧
      ∀ ε : ℝ, epsilonDomain ε →
        ∃ T : ℕ, ∃ hT : domain T,
          (T : ℝ) ≤ horizonBound ε ∧ averageForHorizon T hT ≤ ε

def RealizedAsymptoticUpperNat {α : Type*}
    (domain : ℕ → Prop) (realizes : ℕ → α → Prop)
    (lhs : ℕ → α → ℝ) (rate : ℕ → ℝ) (scope : AsymptoticScope) : Prop :=
  ∃ C : ℝ, ∃ T₀ : ℕ,
    0 < C ∧ ConstantRespectsScope scope C ∧
      ∀ T : ℕ, domain T → T₀ ≤ T →
        (∃ a : α, realizes T a) ∧
          ∀ a : α, realizes T a → lhs T a ≤ C * rate T

def RealizedAsymptoticUpperNatOn {α : Type*}
    (domain : ℕ → Prop) (realizes : ∀ T : ℕ, domain T → α → Prop)
    (lhs : ∀ T : ℕ, domain T → α → ℝ)
    (rate : ∀ T : ℕ, domain T → ℝ) (scope : AsymptoticScope) : Prop :=
  ∃ C : ℝ, ∃ T₀ : ℕ,
    0 < C ∧ ConstantRespectsScope scope C ∧
      ∀ T : ℕ, ∀ hT : domain T, T₀ ≤ T →
        (∃ a : α, realizes T hT a) ∧
          ∀ a : α, realizes T hT a → lhs T hT a ≤ C * rate T hT

def RealizedNuclearStationarityComplexity {α : Type*}
    (realizes : ℕ → α → Prop) (averageForHorizon : ℕ → α → ℝ)
    (rate : ℝ → ℝ) (scope : AsymptoticScope) : Prop :=
  ∃ horizonBound : ℝ → ℝ,
    AsymptoticUpperReal epsilonDomain horizonBound rate scope ∧
      ∀ ε : ℝ, epsilonDomain ε →
        ∃ T : ℕ, ∃ a : α,
          (T : ℝ) ≤ horizonBound ε ∧ realizes T a ∧ averageForHorizon T a ≤ ε

def RealizedNuclearStationarityComplexityOn {α : Type*}
    (domain : ℕ → Prop) (realizes : ∀ T : ℕ, domain T → α → Prop)
    (averageForHorizon : ∀ T : ℕ, domain T → α → ℝ)
    (rate : ℝ → ℝ) (scope : AsymptoticScope) : Prop :=
  ∃ horizonBound : ℝ → ℝ,
    AsymptoticUpperReal epsilonDomain horizonBound rate scope ∧
      ∀ ε : ℝ, epsilonDomain ε →
        ∃ T : ℕ, ∃ hT : domain T, ∃ a : α,
          (T : ℝ) ≤ horizonBound ε ∧ realizes T hT a ∧
            averageForHorizon T hT a ≤ ε

def HorizonNuclearStationarityComplexityWithHorizonRate
    (averageForHorizon : ℕ → ℝ) (runAssumptions : ℕ → Prop)
    (rateAt : ℕ → ℝ → ℝ) (scope : AsymptoticScope) : Prop :=
  ∃ C : ℝ, ∃ ε₀ : ℝ,
    0 < C ∧ 0 < ε₀ ∧ ConstantRespectsScope scope C ∧
      ∀ ε : ℝ, epsilonDomain ε → ε ≤ ε₀ →
        ∃ T : ℕ, runAssumptions T ∧ averageForHorizon T ≤ ε ∧
          (T : ℝ) ≤ C * rateAt T ε

def HorizonNuclearStationarityComplexityWithHorizonRateOn
    (domain : ℕ → Prop) (averageForHorizon : ∀ T : ℕ, domain T → ℝ)
    (rateAt : ∀ T : ℕ, domain T → ℝ → ℝ) (scope : AsymptoticScope) : Prop :=
  ∃ C : ℝ, ∃ ε₀ : ℝ,
    0 < C ∧ 0 < ε₀ ∧ ConstantRespectsScope scope C ∧
      ∀ ε : ℝ, epsilonDomain ε → ε ≤ ε₀ →
        ∃ T : ℕ, ∃ hT : domain T,
          averageForHorizon T hT ≤ ε ∧ (T : ℝ) ≤ C * rateAt T hT ε

def EpsilonHorizonNuclearStationarityComplexityWithHorizonRate
    (averageForAccuracyHorizon : ℝ → ℕ → ℝ)
    (runAssumptions : ℝ → ℕ → Prop)
    (rateAt : ℕ → ℝ → ℝ) (scope : AsymptoticScope) : Prop :=
  ∃ C : ℝ, ∃ ε₀ : ℝ,
    0 < C ∧ 0 < ε₀ ∧ ConstantRespectsScope scope C ∧
      ∀ ε : ℝ, epsilonDomain ε → ε ≤ ε₀ →
        ∃ T : ℕ, runAssumptions ε T ∧
          averageForAccuracyHorizon ε T ≤ ε ∧
          (T : ℝ) ≤ C * rateAt T ε

def EpsilonHorizonNuclearStationarityComplexityWithHorizonRateOn
    (domain : ℝ → ℕ → Prop)
    (averageForAccuracyHorizon : ∀ ε : ℝ, ∀ T : ℕ, domain ε T → ℝ)
    (rateAt : ℕ → ℝ → ℝ) (scope : AsymptoticScope) : Prop :=
  ∃ C : ℝ, ∃ ε₀ : ℝ,
    0 < C ∧ 0 < ε₀ ∧ ConstantRespectsScope scope C ∧
      ∀ ε : ℝ, epsilonDomain ε → ε ≤ ε₀ →
        ∃ T : ℕ, ∃ hT : domain ε T,
          averageForAccuracyHorizon ε T hT ≤ ε ∧
          (T : ℝ) ≤ C * rateAt T ε

def StepSizeScale (ηChoice rate : ℝ → ℝ) (scope : AsymptoticScope) : Prop :=
  AsymptoticUpperReal epsilonDomain ηChoice rate scope

def ConstantStepsizeFamily {m n : ℕ}
    (base : DeterministicMuonConfig m n) (cfgFor : ℝ → DeterministicMuonConfig m n)
    (ηChoice : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, (cfgFor ε).W0 = base.W0 ∧ ∀ t : ℕ, (cfgFor ε).eta t = ηChoice ε

def stochasticAverageNuclearGradient {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n) (T : ℕ) : ℝ :=
  ((T : ℝ)⁻¹) *
    ∫ ω, (Finset.sum (Finset.range T)
      (fun t => nuclearNorm (P.objective.grad ((stochasticMuonState P cfg ω t).W))))
      ∂(samplePathLaw P cfg.batchSize)

def stochasticAverageNuclearGradientWellDefined {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n) (T : ℕ) : Prop :=
  SOptLib.expectationWellDefined (samplePathLaw P cfg.batchSize)
    (fun ω => Finset.sum (Finset.range T)
      (fun t => nuclearNorm (P.objective.grad ((stochasticMuonState P cfg ω t).W))))

noncomputable def stochasticAverageNuclearGradientRealized {ξ : Type*} [MeasurableSpace ξ]
    {m n : ℕ} (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (hwd : stochasticAverageNuclearGradientWellDefined P cfg T) : ℝ :=
  ((T : ℝ)⁻¹) *
    realizedExpectation (samplePathLaw P cfg.batchSize)
      (fun ω => Finset.sum (Finset.range T)
        (fun t => nuclearNorm (P.objective.grad ((stochasticMuonState P cfg ω t).W)))) hwd

theorem stochasticAverageNuclearGradientRealized_eq_integral {ξ : Type*}
    [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (hwd : stochasticAverageNuclearGradientWellDefined P cfg T) :
    stochasticAverageNuclearGradientRealized P cfg T hwd = stochasticAverageNuclearGradient P cfg T :=
  rfl

noncomputable def uniformHorizonIndexLaw (T : ℕ) (hT : horizonDomain T) :
    Measure (Fin T) := by
  letI : Nonempty (Fin T) := Fin.pos_iff_nonempty.mp hT
  exact (PMF.uniformOfFintype (Fin T)).toMeasure

noncomputable def stochasticGeneratedOutputJointLaw {ξ : Type*} [MeasurableSpace ξ]
    {m n : ℕ} (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (hT : horizonDomain T) :
    Measure (Fin T × SamplePath ξ cfg.batchSize) :=
  (uniformHorizonIndexLaw T hT).prod (samplePathLaw P cfg.batchSize)

def stochasticGeneratedOutputMap {ξ : Type*} [MeasurableSpace ξ]
    {m n : ℕ} (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) : Fin T × SamplePath ξ cfg.batchSize → Mat m n :=
  fun q => (stochasticMuonState P cfg q.2 q.1).W

theorem stochasticGeneratedOutputMap_measurable {ξ : Type*} [MeasurableSpace ξ]
    {m n : ℕ} (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) : Measurable (stochasticGeneratedOutputMap P cfg T) := by
  classical
  let piece : Fin T → Fin T × SamplePath ξ cfg.batchSize → Mat m n :=
    fun i q => if q.1 = i then (stochasticMuonState P cfg q.2 i).W else 0
  have hpiece : ∀ i : Fin T, Measurable (piece i) := by
    intro i
    exact Measurable.ite
      (measurable_fst (measurableSet_singleton i))
      ((stochasticMuon_W_measurable P cfg i).comp measurable_snd)
      measurable_const
  have hsum : Measurable (fun q => ∑ i : Fin T, piece i q) :=
    Finset.measurable_sum Finset.univ (fun i _hi => hpiece i)
  have heq : stochasticGeneratedOutputMap P cfg T =
      (fun q => ∑ i : Fin T, piece i q) := by
    funext q
    unfold stochasticGeneratedOutputMap piece
    symm
    rw [Finset.sum_eq_single q.1]
    · simp
    · intro i _hi hne
      simp [hne.symm]
    · simp
  rw [heq]
  exact hsum

noncomputable def stochasticGeneratedOutputLaw {ξ : Type*} [MeasurableSpace ξ]
    {m n : ℕ} (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (hT : horizonDomain T) : Measure (Mat m n) :=
  Measure.map (stochasticGeneratedOutputMap P cfg T)
    (stochasticGeneratedOutputJointLaw P cfg T hT)

theorem stochasticGeneratedOutputJointLaw_isProbability {ξ : Type*}
    [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (hT : horizonDomain T) :
    IsProbabilityMeasure (stochasticGeneratedOutputJointLaw P cfg T hT) := by
  letI : Nonempty (Fin T) := Fin.pos_iff_nonempty.mp hT
  letI : IsProbabilityMeasure P.sampleLaw := P.isProbability_sampleLaw
  letI : IsProbabilityMeasure (samplePathLaw P cfg.batchSize) := by
    dsimp [samplePathLaw]
    infer_instance
  unfold stochasticGeneratedOutputJointLaw uniformHorizonIndexLaw
  infer_instance

theorem stochasticGeneratedOutputLaw_isProbability {ξ : Type*}
    [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (hT : horizonDomain T) :
    IsProbabilityMeasure (stochasticGeneratedOutputLaw P cfg T hT) := by
  letI : IsProbabilityMeasure (stochasticGeneratedOutputJointLaw P cfg T hT) :=
    stochasticGeneratedOutputJointLaw_isProbability P cfg T hT
  exact Measure.isProbabilityMeasure_map
    (stochasticGeneratedOutputMap_measurable P cfg T).aemeasurable

set_option maxHeartbeats 800000 in
theorem stochasticGeneratedOutput_nuclearGradient_integrable {ξ : Type*}
    [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (hT : horizonDomain T)
    (hwd : stochasticAverageNuclearGradientWellDefined P cfg T) :
    Integrable (fun W => nuclearNorm (P.objective.grad W))
      (stochasticGeneratedOutputLaw P cfg T hT) := by
  letI : Nonempty (Fin T) := Fin.pos_iff_nonempty.mp hT
  letI : IsProbabilityMeasure P.sampleLaw := P.isProbability_sampleLaw
  letI : IsProbabilityMeasure (samplePathLaw P cfg.batchSize) := by
    dsimp [samplePathLaw]
    infer_instance
  let μ := samplePathLaw P cfg.batchSize
  let F : Fin T → SamplePath ξ cfg.batchSize → ℝ := fun i ω =>
    nuclearNorm (P.objective.grad (stochasticMuonState P cfg ω i).W)
  have hF_meas : ∀ i : Fin T, Measurable (F i) := by
    intro i
    simpa [F, Objective.grad] using
      (nuclearNorm_measurable.comp
        ((objectiveGradient_measurable P.objective.f).comp
          (stochasticMuon_W_measurable P cfg i)))
  have hsum : Integrable
      (fun ω => Finset.sum (Finset.range T)
        (fun t => nuclearNorm (P.objective.grad (stochasticMuonState P cfg ω t).W))) μ :=
    hwd
  have hF_int : ∀ i : Fin T, Integrable (F i) μ := by
    intro i
    apply hsum.mono' (hF_meas i).aestronglyMeasurable
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (nuclearNorm_nonneg_early _)]
    exact Finset.single_le_sum
      (fun t _ht => nuclearNorm_nonneg_early
        (P.objective.grad (stochasticMuonState P cfg ω t).W))
      (Finset.mem_range.mpr i.isLt)
  have hjoint : Integrable
      (fun q : Fin T × SamplePath ξ cfg.batchSize => F q.1 q.2)
      (stochasticGeneratedOutputJointLaw P cfg T hT) := by
    unfold stochasticGeneratedOutputJointLaw uniformHorizonIndexLaw
    apply PMF.integrable_prod_of_fiber_integrable
      (PMF.uniformOfFintype (Fin T)) μ F
    · simpa [F, Objective.grad, stochasticGeneratedOutputMap] using
        ((nuclearNorm_measurable.comp
          ((objectiveGradient_measurable P.objective.f).comp
            (stochasticGeneratedOutputMap_measurable P cfg T))).aestronglyMeasurable)
    · exact hF_int
  unfold stochasticGeneratedOutputLaw
  exact (integrable_map_measure
    (nuclearNorm_measurable.comp
      (objectiveGradient_measurable P.objective.f)).aestronglyMeasurable
    (stochasticGeneratedOutputMap_measurable P cfg T).aemeasurable).2 hjoint

set_option maxHeartbeats 800000 in
theorem stochasticGeneratedOutput_expectedNuclearGradient_eq_average {ξ : Type*}
    [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (hT : horizonDomain T)
    (hwd : stochasticAverageNuclearGradientWellDefined P cfg T) :
    (∫ W, nuclearNorm (P.objective.grad W)
        ∂(stochasticGeneratedOutputLaw P cfg T hT)) =
      stochasticAverageNuclearGradientRealized P cfg T hwd := by
  letI : Nonempty (Fin T) := Fin.pos_iff_nonempty.mp hT
  letI : IsProbabilityMeasure P.sampleLaw := P.isProbability_sampleLaw
  letI : IsProbabilityMeasure (samplePathLaw P cfg.batchSize) := by
    dsimp [samplePathLaw]
    infer_instance
  let μ := samplePathLaw P cfg.batchSize
  let F : Fin T → SamplePath ξ cfg.batchSize → ℝ := fun i ω =>
    nuclearNorm (P.objective.grad (stochasticMuonState P cfg ω i).W)
  have hF_meas : ∀ i : Fin T, Measurable (F i) := by
    intro i
    simpa [F, Objective.grad] using
      (nuclearNorm_measurable.comp
        ((objectiveGradient_measurable P.objective.f).comp
          (stochasticMuon_W_measurable P cfg i)))
  have hsum : Integrable
      (fun ω => Finset.sum (Finset.range T)
        (fun t => nuclearNorm (P.objective.grad (stochasticMuonState P cfg ω t).W))) μ :=
    hwd
  have hF_int : ∀ i : Fin T, Integrable (F i) μ := by
    intro i
    apply hsum.mono' (hF_meas i).aestronglyMeasurable
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (nuclearNorm_nonneg_early _)]
    exact Finset.single_le_sum
      (fun t _ht => nuclearNorm_nonneg_early
        (P.objective.grad (stochasticMuonState P cfg ω t).W))
      (Finset.mem_range.mpr i.isLt)
  have huniform : ∀ i : Fin T,
      (PMF.uniformOfFintype (Fin T)).toMeasure.real ({i} : Set (Fin T)) =
        (T : ℝ)⁻¹ := by
    intro i
    rw [Measure.real_def,
      PMF.toMeasure_apply_singleton _ i (measurableSet_singleton i),
      PMF.uniformOfFintype_apply, Fintype.card_fin]
    simp [ENNReal.toReal_inv]
  have hjoint := stochasticGeneratedOutput_nuclearGradient_integrable
    P cfg T hT hwd
  rw [show (∫ W, nuclearNorm (P.objective.grad W)
      ∂(stochasticGeneratedOutputLaw P cfg T hT)) =
      ∫ q, nuclearNorm (P.objective.grad (stochasticGeneratedOutputMap P cfg T q))
        ∂(stochasticGeneratedOutputJointLaw P cfg T hT) by
    simpa [stochasticGeneratedOutputLaw, Objective.grad] using
      (integral_map
        (stochasticGeneratedOutputMap_measurable P cfg T).aemeasurable
        (nuclearNorm_measurable.comp
          (objectiveGradient_measurable P.objective.f)).aestronglyMeasurable)]
  unfold stochasticGeneratedOutputJointLaw uniformHorizonIndexLaw
  rw [MeasureTheory.integral_prod]
  · rw [MeasureTheory.integral_fintype]
    · unfold stochasticAverageNuclearGradientRealized realizedExpectation
      simp_rw [huniform]
      simp only [smul_eq_mul, stochasticGeneratedOutputMap]
      rw [← Finset.mul_sum]
      congr 1
      calc
        (∑ i : Fin T, ∫ y, nuclearNorm
            (P.objective.grad (stochasticMuonState P cfg y i).W) ∂μ) =
            ∑ t ∈ Finset.range T, ∫ y, nuclearNorm
              (P.objective.grad (stochasticMuonState P cfg y t).W) ∂μ :=
          Fin.sum_univ_eq_sum_range
            (fun t => ∫ y, nuclearNorm
              (P.objective.grad (stochasticMuonState P cfg y t).W) ∂μ) T
        _ = ∫ ω, Finset.sum (Finset.range T)
              (fun t => nuclearNorm
                (P.objective.grad (stochasticMuonState P cfg ω t).W)) ∂μ := by
          rw [integral_finset_sum _ (fun t ht => by
            simpa [F, μ] using hF_int ⟨t, Finset.mem_range.mp ht⟩)]
    · exact Integrable.of_finite
  · simpa [F, μ, stochasticGeneratedOutputMap] using
      (integrable_map_measure
        (nuclearNorm_measurable.comp
          (objectiveGradient_measurable P.objective.f)).aestronglyMeasurable
        (stochasticGeneratedOutputMap_measurable P cfg T).aemeasurable).1 hjoint

def StochasticGeneratedOutputGuarantee {ξ : Type*} [MeasurableSpace ξ]
    {m n : ℕ} (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (hT : horizonDomain T)
    (hwd : stochasticAverageNuclearGradientWellDefined P cfg T) (ε : ℝ) : Prop :=
  IsProbabilityMeasure (stochasticGeneratedOutputLaw P cfg T hT) ∧
    Integrable (fun W => nuclearNorm (P.objective.grad W))
      (stochasticGeneratedOutputLaw P cfg T hT) ∧
    (∫ W, nuclearNorm (P.objective.grad W)
        ∂(stochasticGeneratedOutputLaw P cfg T hT)) =
      stochasticAverageNuclearGradientRealized P cfg T hwd ∧
    (∫ W, nuclearNorm (P.objective.grad W)
        ∂(stochasticGeneratedOutputLaw P cfg T hT)) ≤ ε

theorem stochasticGeneratedOutputGuarantee_of_average_le {ξ : Type*}
    [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (hT : horizonDomain T)
    (hwd : stochasticAverageNuclearGradientWellDefined P cfg T) (ε : ℝ)
    (havg : stochasticAverageNuclearGradientRealized P cfg T hwd ≤ ε) :
    StochasticGeneratedOutputGuarantee P cfg T hT hwd ε := by
  refine ⟨stochasticGeneratedOutputLaw_isProbability P cfg T hT,
    stochasticGeneratedOutput_nuclearGradient_integrable P cfg T hT hwd, ?_, ?_⟩
  · exact stochasticGeneratedOutput_expectedNuclearGradient_eq_average P cfg T hT hwd
  · rw [stochasticGeneratedOutput_expectedNuclearGradient_eq_average P cfg T hT hwd]
    exact havg

def StochasticGeneratedOutputTransferOn {ξ : Type*} [MeasurableSpace ξ]
    {m n : ℕ} (P : StochasticProblem ξ m n) (domain : ℕ → Prop)
    (horizon : ∀ T : ℕ, domain T → horizonDomain T)
    (cfgForHorizon : ℕ → StochasticMuonConfig m n)
    (wellDefined : ∀ T : ℕ, ∀ hT : domain T,
      stochasticAverageNuclearGradientWellDefined P (cfgForHorizon T) T)
    (averageForHorizon : ∀ T : ℕ, ∀ hT : domain T, ℝ) : Prop :=
  ∀ T : ℕ, ∀ hT : domain T, ∀ ε : ℝ,
    averageForHorizon T hT ≤ ε →
      StochasticGeneratedOutputGuarantee P (cfgForHorizon T) T
        (horizon T hT) (wellDefined T hT) ε

theorem stochasticAverageNuclearGradient_wellDefined_of_source_assumptions
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n) (T : ℕ) (σ : ℝ)
    (_hregularity : StochasticObjectiveRegularity P.objective)
    (_hvariance : BoundedVariance P σ) :
    stochasticAverageNuclearGradientWellDefined P cfg T := by
  letI : IsProbabilityMeasure P.sampleLaw := P.isProbability_sampleLaw
  letI : IsProbabilityMeasure (samplePathLaw P cfg.batchSize) := by
    dsimp [samplePathLaw]
    infer_instance
  unfold stochasticAverageNuclearGradientWellDefined SOptLib.expectationWellDefined
  apply MeasureTheory.integrable_finset_sum (Finset.range T)
  intro t _ht
  let R : ℝ := frobeniusNorm cfg.W0 +
    ∑ k ∈ Finset.range t,
      |cfg.eta k| * Real.sqrt (matrixRankBound m n : ℝ)
  let X : Set (Mat m n) := Metric.closedBall 0 R
  have hW : Measurable
      (fun ω : SamplePath ξ cfg.batchSize => (stochasticMuonState P cfg ω t).W) :=
    stochasticMuon_W_measurable P cfg t
  have hW_mem : ∀ ω : SamplePath ξ cfg.batchSize,
      (stochasticMuonState P cfg ω t).W ∈ X := by
    intro ω
    have hb := stochasticMuon_W_frobeniusNorm_le_prefix P cfg ω t
    simpa [X, R, Metric.mem_closedBall, frobeniusNorm, dist_eq_norm] using hb
  have hgrad_cont : Continuous P.objective.grad := _hregularity.gradient_continuous
  have hgrad_norm_cont : Continuous
      (fun W : Mat m n => frobeniusNorm (P.objective.grad W)) := by
    simpa [frobeniusNorm] using continuous_norm.comp hgrad_cont
  obtain ⟨C, hC, hgrad_bound⟩ :=
    exists_nonneg_norm_bound_of_isCompact_of_continuousOn
      (fun W : Mat m n => frobeniusNorm (P.objective.grad W))
      (isCompact_closedBall (0 : Mat m n) R) hgrad_norm_cont.continuousOn
  apply integrable_of_measurable_bounded_real
  · exact nuclearNorm_measurable.comp (hgrad_cont.measurable.comp hW)
  · intro ω
    have hF : frobeniusNorm (P.objective.grad (stochasticMuonState P cfg ω t).W) ≤ C := by
      have hb := hgrad_bound (stochasticMuonState P cfg ω t).W (hW_mem ω)
      simpa [Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ frobeniusNorm
          (P.objective.grad (stochasticMuonState P cfg ω t).W) by
            simp [frobeniusNorm])] using hb
    rw [Real.norm_eq_abs,
      abs_of_nonneg (nuclearNorm_nonneg_early
        (P.objective.grad (stochasticMuonState P cfg ω t).W))]
    exact le_trans
      (nuclearNorm_le_sqrt_rankBound_mul_frobeniusNorm
        (P.objective.grad (stochasticMuonState P cfg ω t).W))
      (mul_le_mul_of_nonneg_left hF (Real.sqrt_nonneg _))

def stochasticExpectedObjectiveDrop {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n) (T : ℕ) : ℝ :=
  ∫ ω, (P.objective.f cfg.W0 - P.objective.f ((stochasticMuonState P cfg ω T).W))
    ∂(samplePathLaw P cfg.batchSize)

def stochasticExpectedObjectiveDropWellDefined {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n) (T : ℕ) : Prop :=
  SOptLib.expectationWellDefined (samplePathLaw P cfg.batchSize)
    (fun ω => P.objective.f cfg.W0 - P.objective.f ((stochasticMuonState P cfg ω T).W))

noncomputable def stochasticExpectedObjectiveDropRealized {ξ : Type*} [MeasurableSpace ξ]
    {m n : ℕ} (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (hwd : stochasticExpectedObjectiveDropWellDefined P cfg T) : ℝ :=
  realizedExpectation (samplePathLaw P cfg.batchSize)
    (fun ω => P.objective.f cfg.W0 - P.objective.f ((stochasticMuonState P cfg ω T).W)) hwd

theorem stochasticExpectedObjectiveDropRealized_eq_integral {ξ : Type*}
    [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (hwd : stochasticExpectedObjectiveDropWellDefined P cfg T) :
    stochasticExpectedObjectiveDropRealized P cfg T hwd = stochasticExpectedObjectiveDrop P cfg T :=
  rfl

theorem stochasticExpectedObjectiveDrop_wellDefined_of_source_assumptions
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n) (T : ℕ) (σ : ℝ)
    (_hregularity : StochasticObjectiveRegularity P.objective)
    (_hvariance : BoundedVariance P σ) :
    stochasticExpectedObjectiveDropWellDefined P cfg T := by
  letI : IsProbabilityMeasure P.sampleLaw := P.isProbability_sampleLaw
  letI : IsProbabilityMeasure (samplePathLaw P cfg.batchSize) := by
    dsimp [samplePathLaw]
    infer_instance
  unfold stochasticExpectedObjectiveDropWellDefined SOptLib.expectationWellDefined
  let R : ℝ := frobeniusNorm cfg.W0 +
    ∑ k ∈ Finset.range T,
      |cfg.eta k| * Real.sqrt (matrixRankBound m n : ℝ)
  let X : Set (Mat m n) := Metric.closedBall 0 R
  have hW : Measurable
      (fun ω : SamplePath ξ cfg.batchSize => (stochasticMuonState P cfg ω T).W) :=
    stochasticMuon_W_measurable P cfg T
  have hW_mem : ∀ ω : SamplePath ξ cfg.batchSize,
      (stochasticMuonState P cfg ω T).W ∈ X := by
    intro ω
    have hb := stochasticMuon_W_frobeniusNorm_le_prefix P cfg ω T
    simpa [X, R, Metric.mem_closedBall, frobeniusNorm, dist_eq_norm] using hb
  have hf_cont : Continuous P.objective.f := _hregularity.objective_continuous
  obtain ⟨C, hC, hf_bound⟩ :=
    exists_nonneg_norm_bound_of_isCompact_of_continuousOn
      P.objective.f (isCompact_closedBall (0 : Mat m n) R) hf_cont.continuousOn
  apply integrable_of_measurable_bounded_real
  · exact measurable_const.sub (hf_cont.measurable.comp hW)
  · intro ω
    calc
      ‖P.objective.f cfg.W0 - P.objective.f (stochasticMuonState P cfg ω T).W‖ ≤
          ‖P.objective.f cfg.W0‖ +
            ‖P.objective.f (stochasticMuonState P cfg ω T).W‖ := norm_sub_le _ _
      _ ≤ ‖P.objective.f cfg.W0‖ + C :=
        add_le_add le_rfl (hf_bound _ (hW_mem ω))

/- Source: book/Muon/Muon.json#/key_lemmas/theorem_4_1 and
   #/key_lemmas/theorem_4_7.  These theorems print expectations of the
   averaged gradient norm and objective drop.  Their Bochner well-definedness
   bridges consume the theorem-specific smoothness assumption together with
   Assumption 3.3; fixed-query variance alone does not control a random iterate. -/
def stochasticBasicExpectationsWellDefined {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n) (T : ℕ) : Prop :=
  stochasticAverageNuclearGradientWellDefined P cfg T ∧
    stochasticExpectedObjectiveDropWellDefined P cfg T

def deterministicAverageNuclearGradient {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (T : ℕ) : ℝ :=
  ((T : ℝ)⁻¹) *
    Finset.sum (Finset.range T)
      (fun t => nuclearNorm (P.grad ((deterministicMuonState P cfg t).W)))

def deterministicMomentumAverageNuclearGradient {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMomentumMuonConfig m n) (T : ℕ) : ℝ :=
  ((T : ℝ)⁻¹) *
    Finset.sum (Finset.range T)
      (fun t => nuclearNorm (P.grad ((deterministicMomentumMuonState P cfg t).W)))

/- A positive finite average of nonnegative quantities controls one of its
   actual summands.  This is the reusable bridge from the paper's averaged
   bounds to a generated iterate; it has no algorithm-, schedule-, or
   dimension-specific premises. -/
theorem exists_index_le_of_positive_finite_average
    (T : ℕ) (hT : horizonDomain T) (a : ℕ → ℝ) (ε : ℝ)
    (_ha : ∀ t ∈ Finset.range T, 0 ≤ a t)
    (havg : ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) a ≤ ε) :
    ∃ t ∈ Finset.range T, a t ≤ ε := by
  have hTr : 0 < (T : ℝ) := by exact_mod_cast hT
  have hsum : Finset.sum (Finset.range T) a ≤ Finset.sum (Finset.range T) (fun _ => ε) := by
    have hdiv : Finset.sum (Finset.range T) a / (T : ℝ) ≤ ε := by
      simpa [div_eq_inv_mul] using havg
    have hmul := (div_le_iff₀ hTr).mp hdiv
    simpa [mul_comm] using hmul
  have hrange : (Finset.range T).Nonempty := by
    refine ⟨0, ?_⟩
    simpa [horizonDomain] using hT
  exact Finset.exists_le_of_sum_le hrange hsum

def GeneratedNuclearStationarityTransfer {m n : ℕ}
    (P : Objective m n) (domain : ℕ → Prop)
    (averageForHorizon : ∀ T : ℕ, domain T → ℝ)
    (outputForHorizon : ∀ T : ℕ, domain T → ℕ → Mat m n) : Prop :=
  ∀ T : ℕ, ∀ hT : domain T, ∀ ε : ℝ,
    averageForHorizon T hT ≤ ε →
      ∃ t ∈ Finset.range T,
        IsNuclearStationary P ε (outputForHorizon T hT t)

theorem generatedNuclearStationarityTransfer_of_finite_average
    {m n : ℕ} (P : Objective m n) (domain : ℕ → Prop)
    (horizon : ∀ T : ℕ, domain T → horizonDomain T)
    (outputForHorizon : ∀ T : ℕ, domain T → ℕ → Mat m n) :
    GeneratedNuclearStationarityTransfer P domain
      (fun T hT => ((T : ℝ)⁻¹) * Finset.sum (Finset.range T)
        (fun t => nuclearNorm (P.grad (outputForHorizon T hT t))))
      outputForHorizon := by
  intro T hT ε havg
  obtain ⟨t, ht, hle⟩ := exists_index_le_of_positive_finite_average
    T (horizon T hT)
    (fun k => nuclearNorm (P.grad (outputForHorizon T hT k))) ε
    (fun k _hk => nuclearNorm_nonneg_early _) havg
  exact ⟨t, ht, hle⟩

theorem deterministicOracle_average_wellDefined {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMomentumMuonConfig m n) (T : ℕ) :
    stochasticAverageNuclearGradientWellDefined (deterministicOracleProblem P)
      (deterministicOracleConfig cfg) T := by
  letI : IsProbabilityMeasure (deterministicOracleProblem P).sampleLaw :=
    (deterministicOracleProblem P).isProbability_sampleLaw
  letI : IsProbabilityMeasure
      (samplePathLaw (deterministicOracleProblem P)
        (deterministicOracleConfig cfg).batchSize) := by
    dsimp [samplePathLaw]
    infer_instance
  unfold stochasticAverageNuclearGradientWellDefined SOptLib.expectationWellDefined
  have hconstant :
      (fun omega : SamplePath Unit (deterministicOracleConfig cfg).batchSize =>
        Finset.sum (Finset.range T) (fun t =>
          nuclearNorm ((deterministicOracleProblem P).objective.grad
            ((stochasticMuonState (deterministicOracleProblem P)
              (deterministicOracleConfig cfg) omega t).W)))) =
      (fun _ => Finset.sum (Finset.range T) (fun t =>
        nuclearNorm (P.grad ((deterministicMomentumMuonState P cfg t).W)))) := by
    funext omega
    apply Finset.sum_congr rfl
    intro t _ht
    rw [deterministicOracleProblem_objective]
    rw [deterministicOracle_state_eq]
  rw [hconstant]
  exact MeasureTheory.integrable_const _

theorem deterministicOracle_average_eq {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMomentumMuonConfig m n) (T : ℕ)
    (hwd : stochasticAverageNuclearGradientWellDefined
      (deterministicOracleProblem P) (deterministicOracleConfig cfg) T) :
    stochasticAverageNuclearGradientRealized (deterministicOracleProblem P)
        (deterministicOracleConfig cfg) T hwd =
      deterministicMomentumAverageNuclearGradient P cfg T := by
  letI : IsProbabilityMeasure (deterministicOracleProblem P).sampleLaw :=
    (deterministicOracleProblem P).isProbability_sampleLaw
  letI : IsProbabilityMeasure
      (samplePathLaw (deterministicOracleProblem P)
        (deterministicOracleConfig cfg).batchSize) := by
    dsimp [samplePathLaw]
    infer_instance
  unfold stochasticAverageNuclearGradientRealized
    deterministicMomentumAverageNuclearGradient realizedExpectation
  have hconstant :
      (fun omega : SamplePath Unit (deterministicOracleConfig cfg).batchSize =>
        Finset.sum (Finset.range T) (fun t =>
          nuclearNorm ((deterministicOracleProblem P).objective.grad
            ((stochasticMuonState (deterministicOracleProblem P)
              (deterministicOracleConfig cfg) omega t).W)))) =
      (fun _ => Finset.sum (Finset.range T) (fun t =>
        nuclearNorm (P.grad ((deterministicMomentumMuonState P cfg t).W)))) := by
    funext omega
    apply Finset.sum_congr rfl
    intro t _ht
    rw [deterministicOracleProblem_objective]
    rw [deterministicOracle_state_eq]
  rw [hconstant, integral_const, measureReal_univ_eq_one, one_smul]

def objectiveInitialGap {m n : ℕ} (P : Objective m n) (W0 : Mat m n) : ℝ :=
  P.f W0 - P.fStar

def sourceObjectiveInitialGap {m n : ℕ}
    (P : Objective m n) (W0 : Mat m n) (hfinite : P.HasFiniteInfimum) : ℝ :=
  P.f W0 - P.sourceFStar hfinite

theorem sourceObjectiveInitialGap_eq_objectiveInitialGap {m n : ℕ}
    (P : Objective m n) (W0 : Mat m n) (hfinite : P.HasFiniteInfimum) :
    sourceObjectiveInitialGap P W0 hfinite = objectiveInitialGap P W0 :=
  rfl

def hessianBilinear {m n : ℕ} (P : Objective m n)
    (W A B : Mat m n) : ℝ :=
  frobeniusInner A ((fderiv ℝ P.grad W) B)

theorem hessianBilinear_eq_fderiv_grad_pairing {m n : ℕ} (P : Objective m n)
    (W A B : Mat m n) :
    hessianBilinear P W A B = frobeniusInner A ((fderiv ℝ P.grad W) B) :=
  rfl

theorem hessianBilinear_joint_continuous_of_thirdDerivativeBounded
    {m n : ℕ} {P : Objective m n} {s : ℝ}
    (hthird : ThirdDerivativeBounded P s) :
    Continuous (fun q : Mat m n × (Mat m n × Mat m n) =>
      hessianBilinear P q.1 q.2.1 q.2.2) := by
  have hgrad : ContDiff ℝ 2 P.grad :=
    objective_grad_contDiff_two_of_vectorized_contDiff_three P hthird.contDiff
  have happ : Continuous (fun p : Mat m n × Mat m n =>
      (fderiv ℝ P.grad p.1) p.2) :=
    hgrad.continuous_fderiv_apply (by norm_num)
  have hA : Continuous (fun q : Mat m n × (Mat m n × Mat m n) => q.2.1) :=
    continuous_fst.comp continuous_snd
  have hFB : Continuous (fun q : Mat m n × (Mat m n × Mat m n) =>
      (fderiv ℝ P.grad q.1) q.2.2) :=
    happ.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  unfold hessianBilinear frobeniusInner
  apply continuous_finset_sum
  intro i _hi
  apply continuous_finset_sum
  intro j _hj
  exact ((continuous_apply j).comp ((continuous_apply i).comp hA)).mul
    ((continuous_apply j).comp ((continuous_apply i).comp hFB))

def deterministicMuonDirection {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (t : ℕ) : Mat m n :=
  orthogonalizedDirection ((deterministicMuonState P cfg t).G)

theorem deterministicMuonDirection_eq_source_UVt {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (t : ℕ) :
    deterministicMuonDirection P cfg t =
      orthogonalizedDirection ((deterministicMuonState P cfg t).G) :=
  rfl

theorem deterministicMuonDirection_isThinSVDWithPolar {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (t : ℕ) :
    IsThinSVDWithPolar ((deterministicMuonState P cfg t).G)
      (deterministicMuonDirection P cfg t) := by
  unfold deterministicMuonDirection
  exact orthogonalizedDirection_isThinSVDWithPolar _

theorem deterministicMuonDirection_frobeniusInner_eq_nuclearNorm {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (t : ℕ) :
    frobeniusInner (P.grad ((deterministicMuonState P cfg t).W))
        (deterministicMuonDirection P cfg t) =
      nuclearNorm (P.grad ((deterministicMuonState P cfg t).W)) := by
  unfold deterministicMuonDirection
  have hG :
      (deterministicMuonState P cfg t).G =
        P.grad ((deterministicMuonState P cfg t).W) := by
    simpa [deterministicGradient] using deterministicMuon_G_eq_gradient P cfg t
  rw [← hG]
  exact orthogonalizedDirection_frobeniusInner_eq_nuclearNorm _

def deterministicGradientDifferenceDirection {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (t : ℕ) : Mat m n :=
  orthogonalizedDirection
    (P.grad ((deterministicMuonState P cfg t).W) -
      P.grad ((deterministicMuonState P cfg (t + 1)).W))

def hessianDirectionalTerm {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (t : ℕ) : ℝ :=
  let Wt := (deterministicMuonState P cfg t).W
  let Dt := deterministicMuonDirection P cfg t
  hessianBilinear P Wt Dt Dt

theorem hessianDirectionalTerm_eq_source_Jt {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (t : ℕ) :
    hessianDirectionalTerm P cfg t =
      hessianBilinear P ((deterministicMuonState P cfg t).W)
        (deterministicMuonDirection P cfg t) (deterministicMuonDirection P cfg t) :=
  rfl

theorem deterministicMuonDirection_source_pairing_contract {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (t : ℕ) :
    IsThinSVDWithPolar ((deterministicMuonState P cfg t).G)
        (deterministicMuonDirection P cfg t) ∧
      frobeniusInner (P.grad ((deterministicMuonState P cfg t).W))
          (deterministicMuonDirection P cfg t) =
        nuclearNorm (P.grad ((deterministicMuonState P cfg t).W)) := by
  exact ⟨
    deterministicMuonDirection_isThinSVDWithPolar P cfg t,
    deterministicMuonDirection_frobeniusInner_eq_nuclearNorm P cfg t⟩

theorem equation_15_first_order_term_eq_neg_eta_nuclearNorm
    {m n : ℕ} (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    {T t : ℕ} {η : ℝ}
    (ht : t ∈ Finset.range T)
    (hη : ∀ t ∈ Finset.range T, cfg.eta t = η) :
    frobeniusInner (P.grad ((deterministicMuonState P cfg t).W))
        (((deterministicMuonState P cfg (t + 1)).W) -
          ((deterministicMuonState P cfg t).W)) =
      -η * nuclearNorm (P.grad ((deterministicMuonState P cfg t).W)) := by
  classical
  let Wt := (deterministicMuonState P cfg t).W
  let Gt := (deterministicMuonState P cfg t).G
  let Dt := orthogonalizedDirection Gt
  have hG : Gt = P.grad Wt := by
    simpa [Wt, Gt, deterministicGradient] using deterministicMuon_G_eq_gradient P cfg t
  have hupdate :
      (deterministicMuonState P cfg (t + 1)).W =
        Wt - cfg.eta t • Dt := by
    simpa [Wt, Gt, Dt] using deterministicMuon_W_succ_eq_source_update P cfg t
  have heta : cfg.eta t = η := hη t ht
  have hdir :
      frobeniusInner (P.grad Wt) Dt = nuclearNorm (P.grad Wt) := by
    simpa [Dt, Wt, deterministicMuonDirection] using
      (deterministicMuonDirection_source_pairing_contract P cfg t).2
  rw [hupdate, heta]
  change
    frobeniusInner (P.grad Wt) ((Wt - η • Dt) - Wt) =
      -η * nuclearNorm (P.grad Wt)
  have hdiff : (Wt - η • Dt) - Wt = (-η) • Dt := by
    ext i j
    simp
  rw [hdiff]
  calc
    frobeniusInner (P.grad Wt) ((-η) • Dt) =
        (-η) * frobeniusInner (P.grad Wt) Dt := by
      unfold frobeniusInner
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      simp
      ring
    _ = -η * nuclearNorm (P.grad Wt) := by
      rw [hdir]

theorem equation_15_third_order_descent
    {m n : ℕ} (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    {T t : ℕ} {s η : ℝ}
    (ht : t ∈ Finset.range T)
    (hthird : ThirdDerivativeBounded P s)
    (hη : ∀ t ∈ Finset.range T, cfg.eta t = η)
    (_hη_nonneg : 0 ≤ η)
    (hTaylor :
      ‖iteratedFDeriv ℝ 3 (vectorizedObjective P)
          ((deterministicMuonState P cfg t).W)‖ ≤ s →
        P.f ((deterministicMuonState P cfg (t + 1)).W) -
            P.f ((deterministicMuonState P cfg t).W) ≤
          frobeniusInner (P.grad ((deterministicMuonState P cfg t).W))
            (((deterministicMuonState P cfg (t + 1)).W) -
              ((deterministicMuonState P cfg t).W)) +
            η ^ 2 *
              hessianBilinear P ((deterministicMuonState P cfg t).W)
                (deterministicMuonDirection P cfg t)
                (deterministicMuonDirection P cfg t) / 2 +
            s * η ^ 3 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6) :
    P.f ((deterministicMuonState P cfg (t + 1)).W) -
        P.f ((deterministicMuonState P cfg t).W) ≤
      -η * nuclearNorm (P.grad ((deterministicMuonState P cfg t).W)) +
        η ^ 2 * hessianDirectionalTerm P cfg t / 2 +
        s * η ^ 3 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6 := by
  classical
  have hfirst :=
    equation_15_first_order_term_eq_neg_eta_nuclearNorm
      (P := P) (cfg := cfg) (T := T) (t := t) (η := η) ht hη
  have hJ := hessianDirectionalTerm_eq_source_Jt P cfg t
  have hthird_at :
      ‖iteratedFDeriv ℝ 3 (vectorizedObjective P)
          ((deterministicMuonState P cfg t).W)‖ ≤ s :=
    ThirdDerivativeBounded.bound hthird ((deterministicMuonState P cfg t).W)
  calc
    P.f ((deterministicMuonState P cfg (t + 1)).W) -
        P.f ((deterministicMuonState P cfg t).W)
        ≤
          frobeniusInner (P.grad ((deterministicMuonState P cfg t).W))
            (((deterministicMuonState P cfg (t + 1)).W) -
              ((deterministicMuonState P cfg t).W)) +
            η ^ 2 *
              hessianBilinear P ((deterministicMuonState P cfg t).W)
                (deterministicMuonDirection P cfg t)
                (deterministicMuonDirection P cfg t) / 2 +
            s * η ^ 3 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6 :=
          hTaylor hthird_at
    _ =
      -η * nuclearNorm (P.grad ((deterministicMuonState P cfg t).W)) +
        η ^ 2 * hessianDirectionalTerm P cfg t / 2 +
        s * η ^ 3 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6 := by
          rw [hfirst, hJ]

def hessianDirectionalAverage {m n : ℕ} (P : Objective m n)
    (cfg : DeterministicMuonConfig m n) (T : ℕ) : ℝ :=
  ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) (fun t => hessianDirectionalTerm P cfg t)

theorem hessianDirectionalAverage_eq_source_J {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (T : ℕ) :
    hessianDirectionalAverage P cfg T =
      ((T : ℝ)⁻¹) * Finset.sum (Finset.range T) (fun t => hessianDirectionalTerm P cfg t) :=
  rfl

def hessianDirectionalWeightedAverage {m n : ℕ} (P : Objective m n)
    (cfg : DeterministicMuonConfig m n) (T : ℕ) (η Dop : ℝ) : ℝ :=
  ((T : ℝ)⁻¹) *
    Finset.sum (Finset.range T)
      (fun t => (1 - η / Dop) ^ (T - 1 - t) * hessianDirectionalTerm P cfg t)

theorem hessianDirectionalWeightedAverage_eq_source_Jtilde {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (T : ℕ) (η Dop : ℝ) :
    hessianDirectionalWeightedAverage P cfg T η Dop =
      ((T : ℝ)⁻¹) *
        Finset.sum (Finset.range T)
          (fun t => (1 - η / Dop) ^ (T - 1 - t) * hessianDirectionalTerm P cfg t) :=
  rfl

def stochasticMuonDirection {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (ω : SamplePath ξ cfg.batchSize) (t : ℕ) : Mat m n :=
  orthogonalizedDirection ((stochasticMuonState P cfg ω t).M)

def stochasticGradientDifferenceDirection {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (ω : SamplePath ξ cfg.batchSize) (t : ℕ) : Mat m n :=
  orthogonalizedDirection
    (P.objective.grad ((stochasticMuonState P cfg ω t).W) -
      P.objective.grad ((stochasticMuonState P cfg ω (t + 1)).W))

def stochasticHessianDirectionalTerm {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (ω : SamplePath ξ cfg.batchSize) (t : ℕ) : ℝ :=
  let Wt := (stochasticMuonState P cfg ω t).W
  let Dt := stochasticMuonDirection P cfg ω t
  hessianBilinear P.objective Wt Dt Dt

def stochasticHessianCrossTerm {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (ω : SamplePath ξ cfg.batchSize) (t : ℕ) : ℝ :=
  let Wt := (stochasticMuonState P cfg ω t).W
  let Dg := stochasticGradientDifferenceDirection P cfg ω t
  let Dt := stochasticMuonDirection P cfg ω t
  hessianBilinear P.objective Wt Dg Dt

theorem stochasticHessianBilinearTerm_integrable_of_source_regularity
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (t : ℕ) {s : ℝ} (hthird : ThirdDerivativeBounded P.objective s)
    (D₁ D₂ : SamplePath ξ cfg.batchSize → Mat m n)
    (hD₁ : Measurable D₁) (hD₂ : Measurable D₂)
    (hD₁_bound : ∀ ω, frobeniusNorm (D₁ ω) ≤
      Real.sqrt (matrixRankBound m n : ℝ))
    (hD₂_bound : ∀ ω, frobeniusNorm (D₂ ω) ≤
      Real.sqrt (matrixRankBound m n : ℝ)) :
    Integrable (fun ω => hessianBilinear P.objective
      (stochasticMuonState P cfg ω t).W (D₁ ω) (D₂ ω))
      (samplePathLaw P cfg.batchSize) := by
  letI : IsProbabilityMeasure P.sampleLaw := P.isProbability_sampleLaw
  letI : IsProbabilityMeasure (samplePathLaw P cfg.batchSize) := by
    dsimp [samplePathLaw]
    infer_instance
  let R : ℝ := frobeniusNorm cfg.W0 +
    ∑ k ∈ Finset.range t,
      |cfg.eta k| * Real.sqrt (matrixRankBound m n : ℝ)
  let D : ℝ := Real.sqrt (matrixRankBound m n : ℝ)
  let X : Set (Mat m n × (Mat m n × Mat m n)) :=
    Metric.closedBall 0 R ×ˢ (Metric.closedBall 0 D ×ˢ Metric.closedBall 0 D)
  have hW : Measurable
      (fun ω : SamplePath ξ cfg.batchSize => (stochasticMuonState P cfg ω t).W) :=
    stochasticMuon_W_measurable P cfg t
  have hq : Measurable (fun ω : SamplePath ξ cfg.batchSize =>
      ((stochasticMuonState P cfg ω t).W, (D₁ ω, D₂ ω))) :=
    hW.prodMk (hD₁.prodMk hD₂)
  have hq_mem : ∀ ω : SamplePath ξ cfg.batchSize,
      ((stochasticMuonState P cfg ω t).W, (D₁ ω, D₂ ω)) ∈ X := by
    intro ω
    constructor
    · have hb := stochasticMuon_W_frobeniusNorm_le_prefix P cfg ω t
      simpa [X, R, Metric.mem_closedBall, frobeniusNorm, dist_eq_norm] using hb
    · constructor
      · simpa [D, Metric.mem_closedBall, frobeniusNorm, dist_eq_norm] using hD₁_bound ω
      · simpa [D, Metric.mem_closedBall, frobeniusNorm, dist_eq_norm] using hD₂_bound ω
  have hH := hessianBilinear_joint_continuous_of_thirdDerivativeBounded hthird
  have hcompact : IsCompact X :=
    (isCompact_closedBall (0 : Mat m n) R).prod
      ((isCompact_closedBall (0 : Mat m n) D).prod
        (isCompact_closedBall (0 : Mat m n) D))
  obtain ⟨C, hC, hbound⟩ :=
    exists_nonneg_norm_bound_of_isCompact_of_continuousOn
      (fun q : Mat m n × (Mat m n × Mat m n) =>
        hessianBilinear P.objective q.1 q.2.1 q.2.2)
      hcompact hH.continuousOn
  apply integrable_of_measurable_bounded_real
  · exact hH.measurable.comp hq
  · intro ω
    exact hbound _ (hq_mem ω)

def stochasticHessianDirectionalAverage {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n) (T : ℕ) : ℝ :=
  ((T : ℝ)⁻¹) *
    ∫ ω, Finset.sum (Finset.range T)
      (fun t => stochasticHessianDirectionalTerm P cfg ω t)
      ∂(samplePathLaw P cfg.batchSize)

def stochasticHessianDirectionalAverageWellDefined {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n) (T : ℕ) : Prop :=
  SOptLib.expectationWellDefined (samplePathLaw P cfg.batchSize)
    (fun ω => Finset.sum (Finset.range T)
      (fun t => stochasticHessianDirectionalTerm P cfg ω t))

noncomputable def stochasticHessianDirectionalAverageRealized {ξ : Type*}
    [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (hwd : stochasticHessianDirectionalAverageWellDefined P cfg T) : ℝ :=
  ((T : ℝ)⁻¹) *
    realizedExpectation (samplePathLaw P cfg.batchSize)
      (fun ω => Finset.sum (Finset.range T)
        (fun t => stochasticHessianDirectionalTerm P cfg ω t)) hwd

theorem stochasticHessianDirectionalAverageRealized_eq_integral {ξ : Type*}
    [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (hwd : stochasticHessianDirectionalAverageWellDefined P cfg T) :
    stochasticHessianDirectionalAverageRealized P cfg T hwd =
      stochasticHessianDirectionalAverage P cfg T :=
  rfl

def stochasticHessianCrossAverage {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n) (T : ℕ) : ℝ :=
  ((T : ℝ)⁻¹) *
    ∫ ω, Finset.sum (Finset.range (T - 1))
      (fun t => stochasticHessianCrossTerm P cfg ω t)
      ∂(samplePathLaw P cfg.batchSize)

def stochasticHessianCrossAverageWellDefined {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n) (T : ℕ) : Prop :=
  SOptLib.expectationWellDefined (samplePathLaw P cfg.batchSize)
    (fun ω => Finset.sum (Finset.range (T - 1))
      (fun t => stochasticHessianCrossTerm P cfg ω t))

noncomputable def stochasticHessianCrossAverageRealized {ξ : Type*}
    [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (hwd : stochasticHessianCrossAverageWellDefined P cfg T) : ℝ :=
  ((T : ℝ)⁻¹) *
    realizedExpectation (samplePathLaw P cfg.batchSize)
      (fun ω => Finset.sum (Finset.range (T - 1))
        (fun t => stochasticHessianCrossTerm P cfg ω t)) hwd

theorem stochasticHessianCrossAverageRealized_eq_integral {ξ : Type*}
    [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (hwd : stochasticHessianCrossAverageWellDefined P cfg T) :
    stochasticHessianCrossAverageRealized P cfg T hwd =
      stochasticHessianCrossAverage P cfg T :=
  rfl

def stochasticHessianJstarWellDefined {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n) (T : ℕ) : Prop :=
  stochasticHessianDirectionalAverageWellDefined P cfg T ∧
    stochasticHessianCrossAverageWellDefined P cfg T

theorem stochasticHessianJstar_wellDefined_of_source_assumptions
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n) (T : ℕ) (s σ : ℝ)
    (_hthird : ThirdDerivativeBounded P.objective s)
    (_hvariance : BoundedVariance P σ) :
    stochasticHessianJstarWellDefined P cfg T := by
  letI : IsProbabilityMeasure P.sampleLaw := P.isProbability_sampleLaw
  letI : IsProbabilityMeasure (samplePathLaw P cfg.batchSize) := by
    dsimp [samplePathLaw]
    infer_instance
  have hgrad : Continuous P.objective.grad := _hthird.gradient_continuous
  have hDt_meas (t : ℕ) : Measurable
      (fun ω : SamplePath ξ cfg.batchSize => stochasticMuonDirection P cfg ω t) := by
    exact orthogonalizedDirection_measurable.comp (stochasticMuon_M_measurable P cfg t)
  have hDt_bound (t : ℕ) (ω : SamplePath ξ cfg.batchSize) :
      frobeniusNorm (stochasticMuonDirection P cfg ω t) ≤
        Real.sqrt (matrixRankBound m n : ℝ) := by
    exact frobeniusNorm_le_sqrt_rankBound_of_isThinSVDWithPolar
      (orthogonalizedDirection_isThinSVDWithPolar
        (stochasticMuonState P cfg ω t).M)
  have hDg_meas (t : ℕ) : Measurable
      (fun ω : SamplePath ξ cfg.batchSize =>
        stochasticGradientDifferenceDirection P cfg ω t) := by
    unfold stochasticGradientDifferenceDirection
    exact orthogonalizedDirection_measurable.comp
      ((hgrad.measurable.comp (stochasticMuon_W_measurable P cfg t)).sub
        (hgrad.measurable.comp (stochasticMuon_W_measurable P cfg (t + 1))))
  have hDg_bound (t : ℕ) (ω : SamplePath ξ cfg.batchSize) :
      frobeniusNorm (stochasticGradientDifferenceDirection P cfg ω t) ≤
        Real.sqrt (matrixRankBound m n : ℝ) := by
    unfold stochasticGradientDifferenceDirection
    exact frobeniusNorm_le_sqrt_rankBound_of_isThinSVDWithPolar
      (orthogonalizedDirection_isThinSVDWithPolar _)
  constructor
  · unfold stochasticHessianDirectionalAverageWellDefined
      SOptLib.expectationWellDefined
    apply MeasureTheory.integrable_finset_sum (Finset.range T)
    intro t _ht
    simpa [stochasticHessianDirectionalTerm] using
      stochasticHessianBilinearTerm_integrable_of_source_regularity
        P cfg t _hthird
        (fun ω => stochasticMuonDirection P cfg ω t)
        (fun ω => stochasticMuonDirection P cfg ω t)
        (hDt_meas t) (hDt_meas t) (hDt_bound t) (hDt_bound t)
  · unfold stochasticHessianCrossAverageWellDefined
      SOptLib.expectationWellDefined
    apply MeasureTheory.integrable_finset_sum (Finset.range (T - 1))
    intro t _ht
    simpa [stochasticHessianCrossTerm] using
      stochasticHessianBilinearTerm_integrable_of_source_regularity
        P cfg t _hthird
        (fun ω => stochasticGradientDifferenceDirection P cfg ω t)
        (fun ω => stochasticMuonDirection P cfg ω t)
        (hDg_meas t) (hDt_meas t) (hDg_bound t) (hDt_bound t)

/- Source: book/Muon/Muon.json#/assumptions/Assumption_4_13_bounded_third_derivative,
   #/assumptions/Assumption_3_3_bounded_variance, and #/key_lemmas/theorem_4_15.
   The stochastic theorem prints raw
   expectations of gradient norms, objective drops, and J/Jhat averages; this
   bridge therefore consumes both of its stated source assumptions while
   keeping the Lean Bochner-integral side conditions internal. -/
def stochasticMuonExpectationsWellDefined {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n) (T : ℕ) : Prop :=
  stochasticAverageNuclearGradientWellDefined P cfg T ∧
    stochasticExpectedObjectiveDropWellDefined P cfg T ∧
    stochasticHessianJstarWellDefined P cfg T

def stochasticHessianJstar {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n) (T : ℕ) : ℝ :=
  max (stochasticHessianCrossAverage P cfg T) (stochasticHessianDirectionalAverage P cfg T)

noncomputable def stochasticHessianJstarRealized {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n) (T : ℕ)
    (hwd : stochasticHessianJstarWellDefined P cfg T) : ℝ :=
  max (stochasticHessianCrossAverageRealized P cfg T hwd.2)
    (stochasticHessianDirectionalAverageRealized P cfg T hwd.1)

theorem stochasticHessianJstarRealized_eq_source_max {ξ : Type*} [MeasurableSpace ξ]
    {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n) (T : ℕ)
    (hwd : stochasticHessianJstarWellDefined P cfg T) :
    stochasticHessianJstarRealized P cfg T hwd =
      max (stochasticHessianCrossAverageRealized P cfg T hwd.2)
        (stochasticHessianDirectionalAverageRealized P cfg T hwd.1) :=
  rfl

theorem stochasticHessianJstar_eq_source_max {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n) (T : ℕ) :
    stochasticHessianJstar P cfg T =
      max (stochasticHessianCrossAverage P cfg T) (stochasticHessianDirectionalAverage P cfg T) :=
  rfl

/- Lean totalizes the paper's quotients and logarithms.  These wrappers mark
   that convention at the object boundary; source-domain proofs are separate
   obligations, not extra public assumptions. -/
def sourceQuot (a b : ℝ) : ℝ := a / b

def sourceSqrt (a : ℝ) : ℝ := Real.sqrt a

def sourceLogQuot (a b : ℝ) : ℝ := Real.log (sourceQuot a b)

def sourceInv (a : ℝ) : ℝ := a⁻¹

def sourceRpow (a p : ℝ) : ℝ := Real.rpow a p

def sourceQuotDomain (_a b : ℝ) : Prop := b ≠ 0

def sourceHorizonEtaQuotDomain (T : ℕ) (η : ℝ) : Prop :=
  horizonDomain T ∧ sourceQuotDomain 0 ((T : ℝ) * η)

def sourceInvDomain (a : ℝ) : Prop := a ≠ 0

def sourceRpowDomain (a _p : ℝ) : Prop := 0 < a

def sourceSqrtDomain (a : ℝ) : Prop := 0 ≤ a

def sourceSqrtQuotDomain (a b : ℝ) : Prop :=
  sourceQuotDomain a b ∧ sourceSqrtDomain (sourceQuot a b)

def sourceLogQuotDomain (a b : ℝ) : Prop :=
  sourceQuotDomain a b ∧ 0 < sourceQuot a b

/- Source-boundary bookkeeping for printed expressions whose paper meaning is
   partial although Lean's `/`, `sqrt`, and `log` are total.  These are not
   assumptions for paper-facing theorems; they record whether a printed source
   expression is semantically realized or has a Phase 2 boundary correction. -/
def SourceNatDomainBoundary
    (sourceDomain semanticDomain correctionNeeded : ℕ → Prop) : Prop :=
  (∀ T : ℕ, semanticDomain T → sourceDomain T) ∧
    ∀ T : ℕ, sourceDomain T → semanticDomain T ∨ correctionNeeded T

def SourceScalarDomainBoundary
    (sourceDomain semanticDomain correctionNeeded : Prop) : Prop :=
  (semanticDomain → sourceDomain) ∧ (sourceDomain → semanticDomain ∨ correctionNeeded)

def realizedSourceQuot (a b : ℝ) (_h : sourceQuotDomain a b) : ℝ :=
  sourceQuot a b

def realizedSourceSqrt (a : ℝ) (_h : sourceSqrtDomain a) : ℝ :=
  sourceSqrt a

def realizedSourceSqrtQuot (a b : ℝ) (h : sourceSqrtQuotDomain a b) : ℝ :=
  realizedSourceSqrt (realizedSourceQuot a b h.1) h.2

def realizedSourceLogQuot (a b : ℝ) (_h : sourceLogQuotDomain a b) : ℝ :=
  sourceLogQuot a b

def realizedSourceInv (a : ℝ) (_h : sourceInvDomain a) : ℝ :=
  sourceInv a

def realizedSourceRpow (a p : ℝ) (_h : sourceRpowDomain a p) : ℝ :=
  sourceRpow a p

theorem realizedSourceQuot_eq_sourceQuot (a b : ℝ) (h : sourceQuotDomain a b) :
    realizedSourceQuot a b h = sourceQuot a b :=
  rfl

theorem realizedSourceSqrt_eq_sourceSqrt (a : ℝ) (h : sourceSqrtDomain a) :
    realizedSourceSqrt a h = sourceSqrt a :=
  rfl

theorem realizedSourceSqrtQuot_eq_sourceSqrt_sourceQuot
    (a b : ℝ) (h : sourceSqrtQuotDomain a b) :
    realizedSourceSqrtQuot a b h = sourceSqrt (sourceQuot a b) :=
  rfl

theorem realizedSourceLogQuot_eq_sourceLogQuot
    (a b : ℝ) (h : sourceLogQuotDomain a b) :
    realizedSourceLogQuot a b h = sourceLogQuot a b :=
  rfl

theorem realizedSourceInv_eq_sourceInv (a : ℝ) (h : sourceInvDomain a) :
    realizedSourceInv a h = sourceInv a :=
  rfl

theorem realizedSourceRpow_eq_sourceRpow (a p : ℝ) (h : sourceRpowDomain a p) :
    realizedSourceRpow a p h = sourceRpow a p :=
  rfl

theorem rankCube_sourceSqrtDomain (m n : ℕ) :
    sourceSqrtDomain ((matrixRankBound m n : ℝ) ^ 3) := by
  unfold sourceSqrtDomain
  positivity

theorem stochasticMuonConfig_one_sub_beta_sourceQuotDomain {m n : ℕ}
    (cfg : StochasticMuonConfig m n) (a : ℝ) :
    sourceQuotDomain a (1 - cfg.beta) := by
  unfold sourceQuotDomain
  exact ne_of_gt (sub_pos.mpr cfg.beta_mem.2)

def theorem_4_1_rhsDomain {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (L σ η : ℝ) (hdropWD : stochasticExpectedObjectiveDropWellDefined P cfg T) :
    Prop :=
  let r : ℝ := matrixRankBound m n
  let B : ℝ := cfg.batchSize.val
  horizonDomain T ∧
    sourceQuotDomain (stochasticExpectedObjectiveDropRealized P cfg T hdropWD)
      ((T : ℝ) * η) ∧
    sourceSqrtDomain (r * (1 - cfg.beta)) ∧
    sourceSqrtDomain (B * (1 + cfg.beta)) ∧
    sourceQuotDomain (2 * σ * sourceSqrt (r * (1 - cfg.beta)))
      (sourceSqrt (B * (1 + cfg.beta))) ∧
    sourceSqrtDomain r ∧
    sourceSqrtDomain B ∧
    sourceQuotDomain (2 * σ * sourceSqrt r)
      ((1 - cfg.beta) * (T : ℝ) * sourceSqrt B) ∧
    sourceQuotDomain (2 * r * η * cfg.beta * L) (1 - cfg.beta)

def theorem_4_1_rhs {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (L σ η : ℝ) (hdropWD : stochasticExpectedObjectiveDropWellDefined P cfg T)
    (hdom : theorem_4_1_rhsDomain P cfg T L σ η hdropWD) : ℝ :=
  let r : ℝ := matrixRankBound m n
  let B : ℝ := cfg.batchSize.val
  let ⟨_hT, hdrop, hsNoise, hsBatchNoise, hqBatchNoise, hsRank, hsBatch, hqTail, hqMomentum⟩ :=
    hdom
  realizedSourceQuot (stochasticExpectedObjectiveDropRealized P cfg T hdropWD)
      ((T : ℝ) * η) hdrop +
    L * (matrixRankBound m n : ℝ) * η / 2 +
    realizedSourceQuot
      (2 * σ * realizedSourceSqrt (r * (1 - cfg.beta)) hsNoise)
      (realizedSourceSqrt (B * (1 + cfg.beta)) hsBatchNoise) hqBatchNoise +
    realizedSourceQuot
      (2 * σ * realizedSourceSqrt r hsRank)
      ((1 - cfg.beta) * (T : ℝ) * realizedSourceSqrt B hsBatch) hqTail +
    realizedSourceQuot (2 * r * η * cfg.beta * L) (1 - cfg.beta) hqMomentum

def theorem_4_1_sourceRhs {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (L σ η : ℝ) : ℝ :=
  let r : ℝ := matrixRankBound m n
  let B : ℝ := cfg.batchSize.val
  stochasticExpectedObjectiveDrop P cfg T / ((T : ℝ) * η) +
    L * r * η / 2 +
    (2 * σ * Real.sqrt (r * (1 - cfg.beta))) / Real.sqrt (B * (1 + cfg.beta)) +
    (2 * σ * Real.sqrt r) / ((1 - cfg.beta) * (T : ℝ) * Real.sqrt B) +
    (2 * r * η * cfg.beta * L) / (1 - cfg.beta)

def theorem_4_7_rhsDomain {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (Lstar σ η : ℝ)
    (hdropWD : stochasticExpectedObjectiveDropWellDefined P cfg T) : Prop :=
  let r : ℝ := matrixRankBound m n
  let B : ℝ := cfg.batchSize.val
  horizonDomain T ∧
    sourceQuotDomain (stochasticExpectedObjectiveDropRealized P cfg T hdropWD)
      ((T : ℝ) * η) ∧
    sourceSqrtDomain (r * (1 - cfg.beta)) ∧
    sourceSqrtDomain ((1 + cfg.beta) * B) ∧
    sourceQuotDomain (2 * σ * sourceSqrt (r * (1 - cfg.beta)))
      (sourceSqrt ((1 + cfg.beta) * B)) ∧
    sourceSqrtDomain r ∧
    sourceSqrtDomain B ∧
    sourceQuotDomain (2 * σ * sourceSqrt r)
      ((1 - cfg.beta) * (T : ℝ) * sourceSqrt B) ∧
    sourceQuotDomain (2 * η * cfg.beta * Lstar) (1 - cfg.beta)

def theorem_4_7_rhs {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (Lstar σ η : ℝ)
    (hdropWD : stochasticExpectedObjectiveDropWellDefined P cfg T)
    (hdom : theorem_4_7_rhsDomain P cfg T Lstar σ η hdropWD) : ℝ :=
  let r : ℝ := matrixRankBound m n
  let B : ℝ := cfg.batchSize.val
  let ⟨_hT, hdrop, hsNoise, hsBatchNoise, hqBatchNoise, hsRank, hsBatch, hqTail, hqMomentum⟩ :=
    hdom
  realizedSourceQuot (stochasticExpectedObjectiveDropRealized P cfg T hdropWD)
      ((T : ℝ) * η) hdrop +
    Lstar * η / 2 +
    realizedSourceQuot
      (2 * σ * realizedSourceSqrt (r * (1 - cfg.beta)) hsNoise)
      (realizedSourceSqrt ((1 + cfg.beta) * B) hsBatchNoise) hqBatchNoise +
    realizedSourceQuot
      (2 * σ * realizedSourceSqrt r hsRank)
      ((1 - cfg.beta) * (T : ℝ) * realizedSourceSqrt B hsBatch) hqTail +
    realizedSourceQuot (2 * η * cfg.beta * Lstar) (1 - cfg.beta) hqMomentum

def theorem_4_7_sourceRhs {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (Lstar σ η : ℝ) : ℝ :=
  let r : ℝ := matrixRankBound m n
  let B : ℝ := cfg.batchSize.val
  stochasticExpectedObjectiveDrop P cfg T / ((T : ℝ) * η) +
    Lstar * η / 2 +
    (2 * σ * Real.sqrt (r * (1 - cfg.beta))) / Real.sqrt ((1 + cfg.beta) * B) +
    (2 * σ * Real.sqrt r) / ((1 - cfg.beta) * (T : ℝ) * Real.sqrt B) +
    (2 * η * cfg.beta * Lstar) / (1 - cfg.beta)

/- Appendices B.1, B.2, and B.4 use order-preserving multiplication and
   division by the constant learning rate.  The printed theorem statements do
   not spell out `0 < η`; these three internal source boundaries record that
   implicit proof convention without strengthening any registered theorem
   head or changing the globally shared quotient domain. -/
def theorem_4_1_sourceDomain (T : ℕ) (η : ℝ) : Prop :=
  sourceHorizonEtaQuotDomain T η ∧ 0 < η

def theorem_4_7_sourceDomain (T : ℕ) (η : ℝ) : Prop :=
  sourceHorizonEtaQuotDomain T η ∧ 0 < η

theorem theorem_4_1_eta_pos_of_sourceDomain {T : ℕ} {η : ℝ}
    (h : theorem_4_1_sourceDomain T η) : 0 < η :=
  h.2

theorem theorem_4_7_eta_pos_of_sourceDomain {T : ℕ} {η : ℝ}
    (h : theorem_4_7_sourceDomain T η) : 0 < η :=
  h.2

theorem theorem_4_1_sourceDomain_rejects_negative_eta :
    ¬ theorem_4_1_sourceDomain 1 (-1) := by
  norm_num [theorem_4_1_sourceDomain]

theorem theorem_4_7_sourceDomain_rejects_negative_eta :
    ¬ theorem_4_7_sourceDomain 1 (-1) := by
  norm_num [theorem_4_7_sourceDomain]

def theorem_4_1_downstream_phase2_boundary {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (L σ η : ℝ) : Prop :=
  ∃ hbasic : stochasticBasicExpectationsWellDefined P cfg T,
    theorem_4_1_rhsDomain P cfg T L σ η hbasic.2 ∧ 0 < η

def theorem_4_1_sourceDomainCorrectionNeeded {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (L σ η : ℝ) : Prop :=
  theorem_4_1_sourceDomain T η ∧
    ¬ theorem_4_1_downstream_phase2_boundary P cfg T L σ η

def theorem_4_1_source_boundary_corrected_statement {ξ : Type*}
    [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (L σ η : ℝ) : Prop :=
  theorem_4_1_sourceDomain T η →
    ∃ hbasic : stochasticBasicExpectationsWellDefined P cfg T,
    ∃ hdom : theorem_4_1_rhsDomain P cfg T L σ η hbasic.2,
      stochasticAverageNuclearGradientRealized P cfg T hbasic.1 ≤
        theorem_4_1_rhs P cfg T L σ η hbasic.2 hdom

def theorem_4_1_statement {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (L σ η : ℝ) : Prop :=
  SourceScalarDomainBoundary (theorem_4_1_sourceDomain T η)
    (theorem_4_1_downstream_phase2_boundary P cfg T L σ η)
    (theorem_4_1_sourceDomainCorrectionNeeded P cfg T L σ η) ∧
    theorem_4_1_source_boundary_corrected_statement P cfg T L σ η

def theorem_4_7_downstream_phase2_boundary {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (Lstar σ η : ℝ) : Prop :=
  ∃ hbasic : stochasticBasicExpectationsWellDefined P cfg T,
    theorem_4_7_rhsDomain P cfg T Lstar σ η hbasic.2 ∧ 0 < η

def theorem_4_7_sourceDomainCorrectionNeeded {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (Lstar σ η : ℝ) : Prop :=
  theorem_4_7_sourceDomain T η ∧
    ¬ theorem_4_7_downstream_phase2_boundary P cfg T Lstar σ η

def theorem_4_7_source_boundary_corrected_statement {ξ : Type*}
    [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (Lstar σ η : ℝ) : Prop :=
  theorem_4_7_sourceDomain T η →
    ∃ hbasic : stochasticBasicExpectationsWellDefined P cfg T,
    ∃ hdom : theorem_4_7_rhsDomain P cfg T Lstar σ η hbasic.2,
      stochasticAverageNuclearGradientRealized P cfg T hbasic.1 ≤
        theorem_4_7_rhs P cfg T Lstar σ η hbasic.2 hdom

def theorem_4_7_statement {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (Lstar σ η : ℝ) : Prop :=
  SourceScalarDomainBoundary (theorem_4_7_sourceDomain T η)
    (theorem_4_7_downstream_phase2_boundary P cfg T Lstar σ η)
    (theorem_4_7_sourceDomainCorrectionNeeded P cfg T Lstar σ η) ∧
    theorem_4_7_source_boundary_corrected_statement P cfg T Lstar σ η

theorem theorem_4_1_sourceDomain_of_downstream {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    {P : StochasticProblem ξ m n} {cfg : StochasticMuonConfig m n}
    {T : ℕ} {L σ η : ℝ} :
    theorem_4_1_downstream_phase2_boundary P cfg T L σ η →
      theorem_4_1_sourceDomain T η := by
  intro h
  rcases h with ⟨hbasic, hdom, hηpos⟩
  unfold theorem_4_1_sourceDomain theorem_4_1_rhsDomain at *
  exact ⟨⟨hdom.1, hdom.2.1⟩, hηpos⟩

theorem theorem_4_7_sourceDomain_of_downstream {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    {P : StochasticProblem ξ m n} {cfg : StochasticMuonConfig m n}
    {T : ℕ} {Lstar σ η : ℝ} :
    theorem_4_7_downstream_phase2_boundary P cfg T Lstar σ η →
      theorem_4_7_sourceDomain T η := by
  intro h
  rcases h with ⟨hbasic, hdom, hηpos⟩
  unfold theorem_4_7_sourceDomain theorem_4_7_rhsDomain at *
  exact ⟨⟨hdom.1, hdom.2.1⟩, hηpos⟩

theorem theorem_4_1_downstream_phase2_boundary_of_sourceDomain {ξ : Type*}
    [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (L σ η : ℝ)
    (hsrc : theorem_4_1_sourceDomain T η)
    (_hη : ∀ t ∈ Finset.range T, cfg.eta t = η)
    (_hsmooth : FrobeniusSmooth P.objective L)
    (_hvariance : BoundedVariance P σ) :
    theorem_4_1_downstream_phase2_boundary P cfg T L σ η := by
  let hregularity : StochasticObjectiveRegularity P.objective := Or.inl ⟨L, _hsmooth⟩
  let hbasic : stochasticBasicExpectationsWellDefined P cfg T := ⟨
    stochasticAverageNuclearGradient_wellDefined_of_source_assumptions
      P cfg T σ hregularity _hvariance,
    stochasticExpectedObjectiveDrop_wellDefined_of_source_assumptions
      P cfg T σ hregularity _hvariance⟩
  have hβ_nonneg : 0 ≤ cfg.beta := cfg.beta_mem.1
  have hβ_lt_one : cfg.beta < 1 := cfg.beta_mem.2
  have h_one_sub_beta_pos : 0 < 1 - cfg.beta := sub_pos.mpr hβ_lt_one
  have h_one_plus_beta_pos : 0 < 1 + cfg.beta := by linarith
  have hB_pos : 0 < (cfg.batchSize.val : ℝ) := by exact_mod_cast cfg.batchSize.positive
  have hr_nonneg : 0 ≤ (matrixRankBound m n : ℝ) := by exact_mod_cast Nat.zero_le (matrixRankBound m n)
  refine ⟨hbasic, ?_, hsrc.2⟩
  unfold theorem_4_1_rhsDomain
  dsimp
  refine ⟨hsrc.1.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold sourceQuotDomain
    exact hsrc.1.2
  · unfold sourceSqrtDomain
    exact mul_nonneg hr_nonneg (le_of_lt h_one_sub_beta_pos)
  · unfold sourceSqrtDomain
    exact mul_nonneg (le_of_lt hB_pos) (le_of_lt h_one_plus_beta_pos)
  · unfold sourceQuotDomain
    exact ne_of_gt (by
      unfold sourceSqrt
      exact Real.sqrt_pos.2 (mul_pos hB_pos h_one_plus_beta_pos))
  · unfold sourceSqrtDomain
    exact hr_nonneg
  · unfold sourceSqrtDomain
    exact le_of_lt hB_pos
  · unfold sourceQuotDomain
    exact mul_ne_zero (mul_ne_zero
      (stochasticMuonConfig_one_sub_beta_sourceQuotDomain cfg
        (2 * σ * sourceSqrt (matrixRankBound m n : ℝ)))
      (by exact_mod_cast ne_of_gt hsrc.1.1))
      (ne_of_gt (by
        unfold sourceSqrt
        exact Real.sqrt_pos.2 hB_pos))
  · exact stochasticMuonConfig_one_sub_beta_sourceQuotDomain cfg
      (2 * (matrixRankBound m n : ℝ) * η * cfg.beta * L)

theorem theorem_4_7_downstream_phase2_boundary_of_sourceDomain {ξ : Type*}
    [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (Lstar σ η : ℝ)
    (hsrc : theorem_4_7_sourceDomain T η)
    (_hη : ∀ t ∈ Finset.range T, cfg.eta t = η)
    (_hsmooth : SpectralSmooth P.objective Lstar)
    (_hvariance : BoundedVariance P σ) :
    theorem_4_7_downstream_phase2_boundary P cfg T Lstar σ η := by
  let hregularity : StochasticObjectiveRegularity P.objective :=
    Or.inr (Or.inl ⟨Lstar, _hsmooth⟩)
  let hbasic : stochasticBasicExpectationsWellDefined P cfg T := ⟨
    stochasticAverageNuclearGradient_wellDefined_of_source_assumptions
      P cfg T σ hregularity _hvariance,
    stochasticExpectedObjectiveDrop_wellDefined_of_source_assumptions
      P cfg T σ hregularity _hvariance⟩
  have hβ_nonneg : 0 ≤ cfg.beta := cfg.beta_mem.1
  have hβ_lt_one : cfg.beta < 1 := cfg.beta_mem.2
  have h_one_sub_beta_pos : 0 < 1 - cfg.beta := sub_pos.mpr hβ_lt_one
  have h_one_plus_beta_pos : 0 < 1 + cfg.beta := by linarith
  have hB_pos : 0 < (cfg.batchSize.val : ℝ) := by exact_mod_cast cfg.batchSize.positive
  have hr_nonneg : 0 ≤ (matrixRankBound m n : ℝ) := by exact_mod_cast Nat.zero_le (matrixRankBound m n)
  refine ⟨hbasic, ?_, hsrc.2⟩
  unfold theorem_4_7_rhsDomain
  dsimp
  refine ⟨hsrc.1.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold sourceQuotDomain
    exact hsrc.1.2
  · unfold sourceSqrtDomain
    exact mul_nonneg hr_nonneg (le_of_lt h_one_sub_beta_pos)
  · unfold sourceSqrtDomain
    exact mul_nonneg (le_of_lt h_one_plus_beta_pos) (le_of_lt hB_pos)
  · unfold sourceQuotDomain
    exact ne_of_gt (by
      unfold sourceSqrt
      exact Real.sqrt_pos.2 (mul_pos h_one_plus_beta_pos hB_pos))
  · unfold sourceSqrtDomain
    exact hr_nonneg
  · unfold sourceSqrtDomain
    exact le_of_lt hB_pos
  · unfold sourceQuotDomain
    exact mul_ne_zero (mul_ne_zero
      (stochasticMuonConfig_one_sub_beta_sourceQuotDomain cfg
        (2 * σ * sourceSqrt (matrixRankBound m n : ℝ)))
      (by exact_mod_cast ne_of_gt hsrc.1.1))
      (ne_of_gt (by
        unfold sourceSqrt
        exact Real.sqrt_pos.2 hB_pos))
  · exact stochasticMuonConfig_one_sub_beta_sourceQuotDomain cfg
      (2 * η * cfg.beta * Lstar)

theorem theorem_4_1_source_domain_obligation {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (L σ η : ℝ)
    (_hη : ∀ t ∈ Finset.range T, cfg.eta t = η)
    (_hsmooth : FrobeniusSmooth P.objective L)
    (_hvariance : BoundedVariance P σ) :
    SourceScalarDomainBoundary (theorem_4_1_sourceDomain T η)
      (theorem_4_1_downstream_phase2_boundary P cfg T L σ η)
      (theorem_4_1_sourceDomainCorrectionNeeded P cfg T L σ η) := by
  constructor
  · exact theorem_4_1_sourceDomain_of_downstream
  · intro hsrc
    exact Or.inl
      (theorem_4_1_downstream_phase2_boundary_of_sourceDomain P cfg T L σ η
        hsrc _hη _hsmooth _hvariance)

theorem theorem_4_7_source_domain_obligation {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (Lstar σ η : ℝ)
    (_hη : ∀ t ∈ Finset.range T, cfg.eta t = η)
    (_hsmooth : SpectralSmooth P.objective Lstar)
    (_hvariance : BoundedVariance P σ) :
    SourceScalarDomainBoundary (theorem_4_7_sourceDomain T η)
      (theorem_4_7_downstream_phase2_boundary P cfg T Lstar σ η)
      (theorem_4_7_sourceDomainCorrectionNeeded P cfg T Lstar σ η) := by
  constructor
  · exact theorem_4_7_sourceDomain_of_downstream
  · intro hsrc
    exact Or.inl
      (theorem_4_7_downstream_phase2_boundary_of_sourceDomain P cfg T Lstar σ η
        hsrc _hη _hsmooth _hvariance)

def theorem_4_5_rhsDomain {m n : ℕ}
    (_P : Objective m n) (_cfg : DeterministicMuonConfig m n) (_T : ℕ)
    (_L : ℝ) (Dop η : ℝ) : Prop :=
  sourceQuotDomain η Dop ∧ 0 ≤ η ∧ η ≤ Dop

def theorem_4_5_rhs {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (T : ℕ)
    (L Dop η : ℝ) (hdom : theorem_4_5_rhsDomain P cfg T L Dop η) : ℝ :=
  (1 - realizedSourceQuot η Dop hdom.1) ^ T * (P.f cfg.W0 - P.fStar) +
    realizedSourceQuot ((matrixRankBound m n : ℝ) * L * Dop * η) 2
      (by norm_num [sourceQuotDomain])

def theorem_4_5_sourceRhs {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (T : ℕ)
    (L Dop η : ℝ) : ℝ :=
  (1 - η / Dop) ^ T * (P.f cfg.W0 - P.fStar) +
    ((matrixRankBound m n : ℝ) * L * Dop * η) / 2

/- The pre-correction formula guard recorded only that the printed quotient
   was defined.  It did not record the nonnegative contraction used in
   Appendix C.1. -/
private def theorem_4_5_preCorrectionRhsDomain {m n : ℕ}
    (_P : Objective m n) (_cfg : DeterministicMuonConfig m n) (_T : ℕ)
    (_L : ℝ) (Dop η : ℝ) : Prop :=
  sourceQuotDomain η Dop

def theorem_4_5_counterexampleEntry : Mat 1 1 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.proj 0 : Mat 1 1 →L[ℝ] (Fin 1 → ℝ))

@[simp] theorem theorem_4_5_counterexampleEntry_apply (W : Mat 1 1) :
    theorem_4_5_counterexampleEntry W = W 0 0 :=
  rfl

/- Compiled Step-0 certificate for the missing stepsize domain.  This uses the
   one-dimensional quadratic `w |-> w^2/2`, initialized at its minimizer.  At
   horizon zero all source assumptions hold, while `eta = -1` makes the old
   quotient-only version of the printed right-hand side equal `-1/2`. -/
private theorem theorem_4_5_preCorrection_negative_eta_counterexample :
    ∃ (P : Objective 1 1) (cfg : DeterministicMuonConfig 1 1)
      (Wstar : Mat 1 1) (hfinite : P.HasFiniteInfimum),
      StarConvex P Wstar ∧
      FrobeniusSmooth P 1 ∧
      BoundedOperatorDistance P cfg 0 Wstar 1 ∧
      (∀ t ∈ Finset.range 0, cfg.eta t = (-1 : ℝ)) ∧
      theorem_4_5_preCorrectionRhsDomain P cfg 0 1 1 (-1) ∧
      sourceObjectiveGapAt P cfg 0 hfinite = 0 ∧
      theorem_4_5_sourceRhs P cfg 0 1 1 (-1) = -(1 : ℝ) / 2 ∧
      ¬ sourceObjectiveGapAt P cfg 0 hfinite ≤
        theorem_4_5_sourceRhs P cfg 0 1 1 (-1) := by
  let P : Objective 1 1 :=
    ⟨fun W => (1 / 2 : ℝ) * theorem_4_5_counterexampleEntry W ^ 2⟩
  let cfg : DeterministicMuonConfig 1 1 :=
    { W0 := 0
      eta := fun _ => -1 }
  have hfinite : P.HasFiniteInfimum := by
    refine ⟨0, ?_⟩
    rintro y ⟨W, rfl⟩
    dsimp [P]
    positivity
  have hfstar : P.fStar = 0 := by
    apply le_antisymm
    · exact csInf_le hfinite ⟨0, by simp [P]⟩
    · apply le_csInf
      · exact Set.range_nonempty _
      · rintro y ⟨W, rfl⟩
        dsimp [P]
        positivity
  have hgrad (W : Mat 1 1) : P.grad W = W := by
    ext i j
    fin_cases i
    fin_cases j
    have hentry : HasFDerivAt theorem_4_5_counterexampleEntry
        theorem_4_5_counterexampleEntry W :=
      theorem_4_5_counterexampleEntry.hasFDerivAt
    have hderiv := (hentry.pow 2).const_mul (1 / 2 : ℝ)
    rw [Objective.grad_eq_coordinate_fderiv]
    change fderiv ℝ
      (fun W : Mat 1 1 =>
        (1 / 2 : ℝ) * theorem_4_5_counterexampleEntry W ^ 2) W
          (coordinateMatrix 0 0) = W 0 0
    rw [hderiv.fderiv]
    simp [coordinateMatrix]
  have hstar : StarConvex P 0 := by
    constructor
    · change P.f 0 = P.fStar
      rw [hfstar]
      simp [P, theorem_4_5_counterexampleEntry]
    · intro W
      rw [hfstar]
      rw [hgrad]
      simp [frobeniusInner, P]
      nlinarith [sq_nonneg (W 0 0)]
  have hsmooth : FrobeniusSmooth P 1 := by
    constructor
    · dsimp [vectorizedObjective, P]
      exact contDiff_const.mul (theorem_4_5_counterexampleEntry.contDiff.pow 2)
    · intro W W'
      rw [hgrad, hgrad]
      simp
  have hbounded : BoundedOperatorDistance P cfg 0 0 1 := by
    intro t ht
    have ht0 : t = 0 := by simpa using ht
    subst t
    change spectralNorm (cfg.W0 - 0) ≤ 1
    simp [cfg, spectralNorm]
  have hgap : sourceObjectiveGapAt P cfg 0 hfinite = 0 := by
    change P.f cfg.W0 - P.sourceFStar hfinite = 0
    rw [P.sourceFStar_eq_fStar, hfstar]
    simp [P, cfg, theorem_4_5_counterexampleEntry]
  have hrhs : theorem_4_5_sourceRhs P cfg 0 1 1 (-1) = -(1 : ℝ) / 2 := by
    unfold theorem_4_5_sourceRhs
    rw [hfstar]
    norm_num [matrixRankBound, P, cfg, theorem_4_5_counterexampleEntry]
  refine ⟨P, cfg, 0, hfinite, hstar, hsmooth, hbounded, ?_, ?_, hgap, hrhs, ?_⟩
  · simp
  · norm_num [theorem_4_5_preCorrectionRhsDomain, sourceQuotDomain]
  · rw [hgap, hrhs]
    norm_num

def theorem_4_6_rhsDomain {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (t : ℕ)
    (L Dop : ℝ) : Prop :=
  sourceQuotDomain
    (2 * (matrixRankBound m n : ℝ) * L * (P.f cfg.W0 - P.fStar) * Dop ^ 2)
    (2 * (matrixRankBound m n : ℝ) * L * Dop ^ 2 +
      (t : ℝ) * (P.f cfg.W0 - P.fStar))

def theorem_4_6_rhs {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (t : ℕ)
    (L Dop : ℝ) (hdom : theorem_4_6_rhsDomain P cfg t L Dop) : ℝ :=
  realizedSourceQuot
    (2 * (matrixRankBound m n : ℝ) * L * (P.f cfg.W0 - P.fStar) * Dop ^ 2)
    (2 * (matrixRankBound m n : ℝ) * L * Dop ^ 2 +
      (t : ℝ) * (P.f cfg.W0 - P.fStar)) hdom

def theorem_4_6_sourceRhs {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (t : ℕ)
    (L Dop : ℝ) : ℝ :=
  (2 * (matrixRankBound m n : ℝ) * L * (P.f cfg.W0 - P.fStar) * Dop ^ 2) /
    (2 * (matrixRankBound m n : ℝ) * L * Dop ^ 2 +
      (t : ℝ) * (P.f cfg.W0 - P.fStar))

def theorem_4_9_rhsDomain {m n : ℕ}
    (_P : Objective m n) (_cfg : DeterministicMuonConfig m n) (_T : ℕ)
    (_Lstar : ℝ) (Dop η : ℝ) : Prop :=
  sourceQuotDomain η Dop ∧ 0 ≤ η ∧ η ≤ Dop

def theorem_4_9_rhs {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (T : ℕ)
    (Lstar Dop η : ℝ) (hdom : theorem_4_9_rhsDomain P cfg T Lstar Dop η) : ℝ :=
  (1 - realizedSourceQuot η Dop hdom.1) ^ T * (P.f cfg.W0 - P.fStar) +
    realizedSourceQuot (Lstar * Dop * η) 2 (by norm_num [sourceQuotDomain])

def theorem_4_9_sourceRhs {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (T : ℕ)
    (Lstar Dop η : ℝ) : ℝ :=
  (1 - η / Dop) ^ T * (P.f cfg.W0 - P.fStar) + Lstar * Dop * η / 2

/- Compiled Step-0 certificate for the former object model.  On the
   zero-dimensional constant objective, the old two-field smoothness contract
   accepts `Lstar = -1`, while Theorem 4.9's finite-horizon source inequality
   specializes to the false statement `0 ≤ -1/2`.  The corrected
   `SpectralSmooth` cannot inhabit this witness because of its `nonneg` field. -/
private theorem spectralSmooth_preCorrection_negative_constant_counterexample :
    ∃ (P : Objective 0 0) (cfg : DeterministicMuonConfig 0 0)
      (hfinite : P.HasFiniteInfimum),
      PreCorrectionSpectralSmooth P (-1) ∧
        sourceObjectiveGapAt P cfg 1 hfinite = 0 ∧
        theorem_4_9_sourceRhs P cfg 1 (-1) 1 1 = -(1 : ℝ) / 2 ∧
        ¬ sourceObjectiveGapAt P cfg 1 hfinite ≤
          theorem_4_9_sourceRhs P cfg 1 (-1) 1 1 := by
  let P : Objective 0 0 := ⟨fun _ => 0⟩
  let cfg : DeterministicMuonConfig 0 0 :=
    { W0 := 0
      eta := fun _ => 1 }
  have hfinite : P.HasFiniteInfimum := by
    refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨W, rfl⟩
    simp [P]
  have hold : PreCorrectionSpectralSmooth P (-1) := by
    refine ⟨?_, ?_⟩
    · simpa [P, vectorizedObjective] using
        (contDiff_const : ContDiff ℝ 1 (fun _ : Mat 0 0 => (0 : ℝ)))
    · intro W W'
      have hW : W = 0 := Subsingleton.elim _ _
      have hW' : W' = 0 := Subsingleton.elim _ _
      subst W
      subst W'
      simp [P, Objective.grad, objectiveGradient, nuclearNorm, spectralNorm]
  have hgap : sourceObjectiveGapAt P cfg 1 hfinite = 0 := by
    simp [sourceObjectiveGapAt, Objective.sourceFStar, Objective.fStar, P]
  have hrhs : theorem_4_9_sourceRhs P cfg 1 (-1) 1 1 = -(1 : ℝ) / 2 := by
    norm_num [theorem_4_9_sourceRhs, Objective.fStar, P, cfg]
  refine ⟨P, cfg, hfinite, hold, hgap, hrhs, ?_⟩
  rw [hgap, hrhs]
  norm_num

def theorem_4_10_rhsDomain {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (t : ℕ)
    (Lstar Dop : ℝ) : Prop :=
  sourceQuotDomain
    (2 * Lstar * (P.f cfg.W0 - P.fStar) * Dop ^ 2)
    (2 * Lstar * Dop ^ 2 + (t : ℝ) * (P.f cfg.W0 - P.fStar))

def theorem_4_10_rhs {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (t : ℕ)
    (Lstar Dop : ℝ) (hdom : theorem_4_10_rhsDomain P cfg t Lstar Dop) : ℝ :=
  realizedSourceQuot
    (2 * Lstar * (P.f cfg.W0 - P.fStar) * Dop ^ 2)
    (2 * Lstar * Dop ^ 2 + (t : ℝ) * (P.f cfg.W0 - P.fStar)) hdom

def theorem_4_10_sourceRhs {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (t : ℕ)
    (Lstar Dop : ℝ) : ℝ :=
  (2 * Lstar * (P.f cfg.W0 - P.fStar) * Dop ^ 2) /
    (2 * Lstar * Dop ^ 2 + (t : ℝ) * (P.f cfg.W0 - P.fStar))

def theorem_4_14_rhsDomain {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (T : ℕ) (_J _s η : ℝ) : Prop :=
  horizonDomain T ∧
    0 < η ∧
    sourceQuotDomain
      (P.f cfg.W0 - P.f ((deterministicMuonState P cfg T).W)) ((T : ℝ) * η) ∧
    sourceSqrtDomain ((matrixRankBound m n : ℝ) ^ 3)

theorem theorem_4_14_rhsDomain_eta_pos {m n : ℕ}
    {P : Objective m n} {cfg : DeterministicMuonConfig m n}
    {T : ℕ} {J s η : ℝ}
    (hdom : theorem_4_14_rhsDomain P cfg T J s η) :
    0 < η :=
  hdom.2.1

def theorem_4_14_rhs {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (T : ℕ) (J s η : ℝ)
    (hdom : theorem_4_14_rhsDomain P cfg T J s η) : ℝ :=
  let ⟨_hT, _hηpos, hdrop, hsRankCube⟩ := hdom
  realizedSourceQuot
      (P.f cfg.W0 - P.f ((deterministicMuonState P cfg T).W)) ((T : ℝ) * η) hdrop +
    η * J / 2 +
      s * η ^ 2 * realizedSourceSqrt ((matrixRankBound m n : ℝ) ^ 3) hsRankCube / 6

def theorem_4_14_sourceRhs {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (T : ℕ) (J s η : ℝ) : ℝ :=
  (P.f cfg.W0 - P.f ((deterministicMuonState P cfg T).W)) / ((T : ℝ) * η) +
    η * J / 2 + s * η ^ 2 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6

theorem theorem_4_14_rhs_eq_sourceRhs {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T : ℕ) (J s η : ℝ)
    (hdom : theorem_4_14_rhsDomain P cfg T J s η) :
    theorem_4_14_rhs P cfg T J s η hdom =
      theorem_4_14_sourceRhs P cfg T J s η := by
  rcases hdom with ⟨_hT, _hηpos, hdrop, hsRankCube⟩
  simp [theorem_4_14_rhs, theorem_4_14_sourceRhs, sourceQuot, sourceSqrt,
    realizedSourceQuot_eq_sourceQuot, realizedSourceSqrt_eq_sourceSqrt]

def theorem_4_16_rhsDomain (m n : ℕ)
    (T : ℕ) (_Δ _Jtilde _s η Dop : ℝ) : Prop :=
  horizonDomain T ∧ sourceQuotDomain η Dop ∧
    sourceSqrtDomain ((matrixRankBound m n : ℝ) ^ 3)

def theorem_4_16_rhs {m n : ℕ}
    (_P : Objective m n) (_cfg : DeterministicMuonConfig m n) (T : ℕ)
    (Δ Jtilde s η Dop : ℝ) (hdom : theorem_4_16_rhsDomain m n T Δ Jtilde s η Dop) : ℝ :=
  let ⟨_hT, hstep, hsRankCube⟩ := hdom
  (1 - realizedSourceQuot η Dop hstep) ^ T * Δ + η ^ 2 * Jtilde * (T : ℝ) / 2 +
    s * η ^ 2 * Dop *
      realizedSourceSqrt ((matrixRankBound m n : ℝ) ^ 3) hsRankCube / 6

def theorem_4_16_sourceRhs {m n : ℕ}
    (_P : Objective m n) (_cfg : DeterministicMuonConfig m n) (T : ℕ)
    (Δ Jtilde s η Dop : ℝ) : ℝ :=
  (1 - η / Dop) ^ T * Δ + η ^ 2 * Jtilde * (T : ℝ) / 2 +
    s * η ^ 2 * Dop * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) / 6

theorem theorem_4_16_rhs_eq_sourceRhs {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (T : ℕ)
    (Δ Jtilde s η Dop : ℝ)
    (hdom : theorem_4_16_rhsDomain m n T Δ Jtilde s η Dop) :
    theorem_4_16_rhs P cfg T Δ Jtilde s η Dop hdom =
      theorem_4_16_sourceRhs P cfg T Δ Jtilde s η Dop := by
  rcases hdom with ⟨_hT, hstep, hsRankCube⟩
  simp [theorem_4_16_rhs, theorem_4_16_sourceRhs, sourceQuot, sourceSqrt,
    realizedSourceQuot_eq_sourceQuot, realizedSourceSqrt_eq_sourceSqrt]

def theoremScope (label : String) (independent : List String) : AsymptoticScope :=
  { mayDependOn := [label, "fixed paper parameters"],
    independentOf := independent,
    constantPredicate := fun C => 0 < C }

def internalBetaFromOneMinusSource (q : ℝ) : ℝ :=
  if _h : 1 - q ∈ Set.Ico (0 : ℝ) 1 then 1 - q else 0

theorem internalBetaFromOneMinusSource_mem_Ico (q : ℝ) :
    internalBetaFromOneMinusSource q ∈ Set.Ico (0 : ℝ) 1 := by
  unfold internalBetaFromOneMinusSource
  by_cases h : 1 - q ∈ Set.Ico (0 : ℝ) 1
  · simp [h]
  · simp [h, Set.mem_Ico]

theorem internalBetaFromOneMinusSource_realizes
    {q : ℝ} (h : 1 - q ∈ Set.Ico (0 : ℝ) 1) :
    1 - internalBetaFromOneMinusSource q = q := by
  simp [internalBetaFromOneMinusSource, h]

def deterministicConstantConfig {m n : ℕ}
    (W0 : Mat m n) (η : ℝ) : DeterministicMuonConfig m n :=
  { W0 := W0, eta := fun _ => η }

def stochasticConstantConfig {m n : ℕ}
    (W0 : Mat m n) (η β : ℝ) (hβ : β ∈ Set.Ico (0 : ℝ) 1)
    (B : BatchSize) : StochasticMuonConfig m n :=
  { W0 := W0, eta := fun _ => η, beta := β, beta_mem := hβ, batchSize := B }

def deterministicMomentumConstantConfig {m n : ℕ}
    (W0 : Mat m n) (η β : ℝ) (hβ : β ∈ Set.Ico (0 : ℝ) 1) :
    DeterministicMomentumMuonConfig m n :=
  { W0 := W0, eta := fun _ => η, beta := β, beta_mem := hβ }

def unitBatchSize : BatchSize :=
  { val := 1, positive := by norm_num }

def constantMomentumO1 (β : ℝ) : Prop :=
  AsymptoticUpperNat (fun _ => True) (fun _ => β) (fun _ => 1)
    (theoremScope "fixed beta=O(1)" ["T"])

/- Source: book/Muon/Muon.json#/key_lemmas/corollary_4_2 and
   #/key_lemmas/corollary_4_8.  These definitions keep the printed
   stochastic schedules, sigma=0 deterministic branches, and epsilon-complexity
   clauses as endpoint payloads rather than scalar pointwise Big-O inequalities. -/
def corollary_4_2_stochasticRate (m n : ℕ) (L σ Δ : ℝ) (T : ℕ) : ℝ :=
  Real.sqrt (Real.sqrt (((matrixRankBound m n : ℝ) ^ 2 * L * Δ * σ ^ 2) / (T : ℝ))) +
    Real.sqrt (((matrixRankBound m n : ℝ) * L * Δ) / (T : ℝ)) +
      Real.sqrt (matrixRankBound m n : ℝ) * σ ^ 2 / Real.sqrt (L * Δ * (T : ℝ))

def corollary_4_8_stochasticRate (m n : ℕ) (Lstar σ Δ : ℝ) (T : ℕ) : ℝ :=
  Real.sqrt (Real.sqrt (((matrixRankBound m n : ℝ) * Lstar * Δ * σ ^ 2) / (T : ℝ))) +
    Real.sqrt ((Lstar * Δ) / (T : ℝ)) +
      (matrixRankBound m n : ℝ) * σ ^ 2 / Real.sqrt (Lstar * Δ * (T : ℝ))

def corollary_4_2_stochasticRateDomain
    (m n : ℕ) (T : ℕ) (L σ Δ : ℝ) : Prop :=
  horizonDomain T ∧
    sourceSqrtQuotDomain ((matrixRankBound m n : ℝ) ^ 2 * L * Δ * σ ^ 2) (T : ℝ) ∧
    sourceSqrtQuotDomain ((matrixRankBound m n : ℝ) * L * Δ) (T : ℝ) ∧
    sourceSqrtDomain (L * Δ * (T : ℝ)) ∧
    sourceQuotDomain (Real.sqrt (matrixRankBound m n : ℝ) * σ ^ 2)
      (Real.sqrt (L * Δ * (T : ℝ)))

def corollary_4_2_deterministicRateDomain
    (m n : ℕ) (T : ℕ) (L Δ : ℝ) : Prop :=
  horizonDomain T ∧
    sourceSqrtQuotDomain ((matrixRankBound m n : ℝ) * L * Δ) (T : ℝ)

def corollary_4_8_stochasticRateDomain
    (m n : ℕ) (T : ℕ) (Lstar σ Δ : ℝ) : Prop :=
  horizonDomain T ∧
    sourceSqrtQuotDomain ((matrixRankBound m n : ℝ) * Lstar * Δ * σ ^ 2) (T : ℝ) ∧
    sourceSqrtQuotDomain (Lstar * Δ) (T : ℝ) ∧
    sourceSqrtDomain (Lstar * Δ * (T : ℝ)) ∧
    sourceQuotDomain ((matrixRankBound m n : ℝ) * σ ^ 2)
      (Real.sqrt (Lstar * Δ * (T : ℝ)))

def corollary_4_8_deterministicRateDomain
    (_m _n : ℕ) (T : ℕ) (Lstar Δ : ℝ) : Prop :=
  horizonDomain T ∧ sourceSqrtQuotDomain (Lstar * Δ) (T : ℝ)

def corollary_4_2_stochasticRateRealized
    (m n : ℕ) (T : ℕ) (L σ Δ : ℝ)
    (h : corollary_4_2_stochasticRateDomain m n T L σ Δ) : ℝ :=
  let hFirst := h.2.1
  let hSecond := h.2.2.1
  let hThirdSqrt := h.2.2.2.1
  let hThirdQuot := h.2.2.2.2
  realizedSourceSqrt (realizedSourceSqrtQuot
    ((matrixRankBound m n : ℝ) ^ 2 * L * Δ * σ ^ 2) (T : ℝ) hFirst)
    (Real.sqrt_nonneg _) +
    realizedSourceSqrtQuot ((matrixRankBound m n : ℝ) * L * Δ) (T : ℝ) hSecond +
      realizedSourceQuot (Real.sqrt (matrixRankBound m n : ℝ) * σ ^ 2)
        (realizedSourceSqrt (L * Δ * (T : ℝ)) hThirdSqrt) hThirdQuot

def corollary_4_2_deterministicRateRealized
    (m n : ℕ) (T : ℕ) (L Δ : ℝ)
    (h : corollary_4_2_deterministicRateDomain m n T L Δ) : ℝ :=
  realizedSourceSqrtQuot ((matrixRankBound m n : ℝ) * L * Δ) (T : ℝ) h.2

def corollary_4_8_stochasticRateRealized
    (m n : ℕ) (T : ℕ) (Lstar σ Δ : ℝ)
    (h : corollary_4_8_stochasticRateDomain m n T Lstar σ Δ) : ℝ :=
  let hFirst := h.2.1
  let hSecond := h.2.2.1
  let hThirdSqrt := h.2.2.2.1
  let hThirdQuot := h.2.2.2.2
  realizedSourceSqrt (realizedSourceSqrtQuot
    ((matrixRankBound m n : ℝ) * Lstar * Δ * σ ^ 2) (T : ℝ) hFirst)
    (Real.sqrt_nonneg _) +
    realizedSourceSqrtQuot (Lstar * Δ) (T : ℝ) hSecond +
      realizedSourceQuot ((matrixRankBound m n : ℝ) * σ ^ 2)
        (realizedSourceSqrt (Lstar * Δ * (T : ℝ)) hThirdSqrt) hThirdQuot

def corollary_4_8_deterministicRateRealized
    (m n : ℕ) (T : ℕ) (Lstar Δ : ℝ)
    (h : corollary_4_8_deterministicRateDomain m n T Lstar Δ) : ℝ :=
  realizedSourceSqrtQuot (Lstar * Δ) (T : ℝ) h.2

def corollary_4_2_stochasticComplexityRate (m n : ℕ) (L σ Δ ε : ℝ) : ℝ :=
  (matrixRankBound m n : ℝ) ^ 2 * L * σ ^ 2 * Δ * ε⁻¹ ^ 4

def corollary_4_2_deterministicComplexityRate (m n : ℕ) (L Δ ε : ℝ) : ℝ :=
  (matrixRankBound m n : ℝ) * L * Δ * ε⁻¹ ^ 2

def corollary_4_8_stochasticComplexityRate (m n : ℕ) (Lstar σ Δ ε : ℝ) : ℝ :=
  (matrixRankBound m n : ℝ) * Lstar * σ ^ 2 * Δ * ε⁻¹ ^ 4

def corollary_4_8_deterministicComplexityRate (_m _n : ℕ) (Lstar Δ ε : ℝ) : ℝ :=
  Lstar * Δ * ε⁻¹ ^ 2

def corollary_4_2_stochasticOneMinusBeta (T : ℕ) (L σ Δ : ℝ) : ℝ :=
  min (sourceQuot (Real.sqrt (L * Δ)) (σ * Real.sqrt (T : ℝ))) 1

def corollary_4_2_stochasticEta (m n T : ℕ) (L σ Δ : ℝ) : ℝ :=
  Real.sqrt
    (sourceQuot (corollary_4_2_stochasticOneMinusBeta T L σ Δ * Δ)
      ((matrixRankBound m n : ℝ) * (T : ℝ) * L))

def internalCorollary_4_2_stochasticBetaDomain (T : ℕ) (L σ Δ : ℝ) : Prop :=
  1 - corollary_4_2_stochasticOneMinusBeta T L σ Δ ∈ Set.Ico (0 : ℝ) 1

def corollary_4_2_stochasticSourceHorizonDomain
    (T : ℕ) (_L _σ _Δ : ℝ) : Prop :=
  horizonDomain T

def corollary_4_2_stochasticScheduleDomain
    (m n : ℕ)
    (T : ℕ) (L σ Δ : ℝ) : Prop :=
  horizonDomain T ∧
    sourceSqrtDomain (L * Δ) ∧
    sourceSqrtDomain (T : ℝ) ∧
    sourceQuotDomain (Real.sqrt (L * Δ)) (σ * Real.sqrt (T : ℝ)) ∧
    sourceSqrtQuotDomain
      (corollary_4_2_stochasticOneMinusBeta T L σ Δ * Δ)
      ((matrixRankBound m n : ℝ) * (T : ℝ) * L) ∧
    sourceQuotDomain
      (corollary_4_2_stochasticOneMinusBeta T L σ Δ * Δ)
      ((matrixRankBound m n : ℝ) * (T : ℝ) * L)

def corollary_4_2_stochasticRealizableHorizonDomain
    (m n T : ℕ) (L σ Δ : ℝ) : Prop :=
  corollary_4_2_stochasticScheduleDomain m n T L σ Δ ∧
    corollary_4_2_stochasticRateDomain m n T L σ Δ ∧
    internalCorollary_4_2_stochasticBetaDomain T L σ Δ

def corollary_4_2_stochasticSemanticHorizonDomain
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (W0 : Mat m n)
    (T : ℕ) (L σ Δ : ℝ) : Prop :=
  corollary_4_2_stochasticRealizableHorizonDomain m n T L σ Δ ∧
    ∀ cfg : StochasticMuonConfig m n,
      (horizonDomain T ∧
        cfg.W0 = W0 ∧
        cfg.batchSize.val = 1 ∧
        (∀ t ∈ Finset.range T,
          cfg.eta t = corollary_4_2_stochasticEta m n T L σ Δ) ∧
        1 - cfg.beta = corollary_4_2_stochasticOneMinusBeta T L σ Δ) →
        stochasticAverageNuclearGradientWellDefined P cfg T

def corollary_4_2_stochasticAdmissibleHorizonDomain
    (m n T : ℕ) (L σ Δ : ℝ) : Prop :=
  corollary_4_2_stochasticRealizableHorizonDomain m n T L σ Δ

def corollary_4_2_stochasticBetaDomainCorrectionNeeded
    (m n T : ℕ) (L σ Δ : ℝ) : Prop :=
  corollary_4_2_stochasticSourceHorizonDomain T L σ Δ ∧
    ¬ corollary_4_2_stochasticRealizableHorizonDomain m n T L σ Δ

def corollary_4_2_stochasticSemanticCorrectionNeeded
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (W0 : Mat m n)
    (T : ℕ) (L σ Δ : ℝ) : Prop :=
  corollary_4_2_stochasticSourceHorizonDomain T L σ Δ ∧
    ¬ corollary_4_2_stochasticSemanticHorizonDomain P W0 T L σ Δ

def corollary_4_2_stochasticSourceBoundary
    (m n : ℕ) (L σ Δ : ℝ) : Prop :=
  SourceNatDomainBoundary
    (fun T => corollary_4_2_stochasticSourceHorizonDomain T L σ Δ)
    (fun T => corollary_4_2_stochasticRealizableHorizonDomain m n T L σ Δ)
    (fun T => corollary_4_2_stochasticBetaDomainCorrectionNeeded m n T L σ Δ)

def corollary_4_2_stochasticSemanticSourceBoundary
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (W0 : Mat m n) (L σ Δ : ℝ) : Prop :=
  SourceNatDomainBoundary
    (fun T => corollary_4_2_stochasticSourceHorizonDomain T L σ Δ)
    (fun T => corollary_4_2_stochasticSemanticHorizonDomain P W0 T L σ Δ)
    (fun T => corollary_4_2_stochasticSemanticCorrectionNeeded P W0 T L σ Δ)

def corollary_4_2_deterministicEta (m n T : ℕ) (L Δ : ℝ) : ℝ :=
  Real.sqrt (sourceQuot Δ ((matrixRankBound m n : ℝ) * (T : ℝ) * L))

def corollary_4_8_stochasticOneMinusBeta (m n T : ℕ) (Lstar σ Δ : ℝ) : ℝ :=
  min (sourceQuot (Real.sqrt (Lstar * Δ))
    (σ * Real.sqrt ((matrixRankBound m n : ℝ) * (T : ℝ)))) 1

def corollary_4_8_stochasticEta (m n T : ℕ) (Lstar σ Δ : ℝ) : ℝ :=
  Real.sqrt
    (sourceQuot (corollary_4_8_stochasticOneMinusBeta m n T Lstar σ Δ * Δ)
      ((T : ℝ) * Lstar))

def internalCorollary_4_8_stochasticBetaDomain (m n T : ℕ) (Lstar σ Δ : ℝ) : Prop :=
  1 - corollary_4_8_stochasticOneMinusBeta m n T Lstar σ Δ ∈ Set.Ico (0 : ℝ) 1

def corollary_4_8_stochasticSourceHorizonDomain
    (_m _n T : ℕ) (_Lstar _σ _Δ : ℝ) : Prop :=
  horizonDomain T

def corollary_4_8_stochasticScheduleDomain
    (m n T : ℕ) (Lstar σ Δ : ℝ) : Prop :=
  horizonDomain T ∧
    sourceSqrtDomain (Lstar * Δ) ∧
    sourceSqrtDomain ((matrixRankBound m n : ℝ) * (T : ℝ)) ∧
    sourceQuotDomain (Real.sqrt (Lstar * Δ))
      (σ * Real.sqrt ((matrixRankBound m n : ℝ) * (T : ℝ))) ∧
    sourceSqrtQuotDomain
      (corollary_4_8_stochasticOneMinusBeta m n T Lstar σ Δ * Δ)
      ((T : ℝ) * Lstar) ∧
    sourceQuotDomain
      (corollary_4_8_stochasticOneMinusBeta m n T Lstar σ Δ * Δ)
      ((T : ℝ) * Lstar)

def corollary_4_8_stochasticRealizableHorizonDomain
    (m n T : ℕ) (Lstar σ Δ : ℝ) : Prop :=
  corollary_4_8_stochasticScheduleDomain m n T Lstar σ Δ ∧
    corollary_4_8_stochasticRateDomain m n T Lstar σ Δ ∧
    internalCorollary_4_8_stochasticBetaDomain m n T Lstar σ Δ

def corollary_4_8_stochasticSemanticHorizonDomain
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (W0 : Mat m n)
    (T : ℕ) (Lstar σ Δ : ℝ) : Prop :=
  corollary_4_8_stochasticRealizableHorizonDomain m n T Lstar σ Δ ∧
    ∀ cfg : StochasticMuonConfig m n,
      (horizonDomain T ∧
        cfg.W0 = W0 ∧
        cfg.batchSize.val = 1 ∧
        (∀ t ∈ Finset.range T,
          cfg.eta t = corollary_4_8_stochasticEta m n T Lstar σ Δ) ∧
        1 - cfg.beta = corollary_4_8_stochasticOneMinusBeta m n T Lstar σ Δ) →
        stochasticAverageNuclearGradientWellDefined P cfg T

def corollary_4_8_stochasticAdmissibleHorizonDomain
    (m n T : ℕ) (Lstar σ Δ : ℝ) : Prop :=
  corollary_4_8_stochasticRealizableHorizonDomain m n T Lstar σ Δ

def corollary_4_8_stochasticBetaDomainCorrectionNeeded
    (m n T : ℕ) (Lstar σ Δ : ℝ) : Prop :=
  corollary_4_8_stochasticSourceHorizonDomain m n T Lstar σ Δ ∧
    ¬ corollary_4_8_stochasticRealizableHorizonDomain m n T Lstar σ Δ

def corollary_4_8_stochasticSemanticCorrectionNeeded
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (W0 : Mat m n)
    (T : ℕ) (Lstar σ Δ : ℝ) : Prop :=
  corollary_4_8_stochasticSourceHorizonDomain m n T Lstar σ Δ ∧
    ¬ corollary_4_8_stochasticSemanticHorizonDomain P W0 T Lstar σ Δ

def corollary_4_8_stochasticSourceBoundary
    (m n : ℕ) (Lstar σ Δ : ℝ) : Prop :=
  SourceNatDomainBoundary
    (fun T => corollary_4_8_stochasticSourceHorizonDomain m n T Lstar σ Δ)
    (fun T => corollary_4_8_stochasticRealizableHorizonDomain m n T Lstar σ Δ)
    (fun T => corollary_4_8_stochasticBetaDomainCorrectionNeeded m n T Lstar σ Δ)

def corollary_4_8_stochasticSemanticSourceBoundary
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (W0 : Mat m n) (Lstar σ Δ : ℝ) : Prop :=
  SourceNatDomainBoundary
    (fun T => corollary_4_8_stochasticSourceHorizonDomain m n T Lstar σ Δ)
    (fun T => corollary_4_8_stochasticSemanticHorizonDomain P W0 T Lstar σ Δ)
    (fun T => corollary_4_8_stochasticSemanticCorrectionNeeded P W0 T Lstar σ Δ)

def corollary_4_8_deterministicEta (_m _n T : ℕ) (Lstar Δ : ℝ) : ℝ :=
  Real.sqrt (sourceQuot Δ ((T : ℝ) * Lstar))

def internalCorollary_4_2_stochasticConfig {m n : ℕ}
    (W0 : Mat m n) (T : ℕ) (L σ Δ : ℝ)
    (hβ : internalCorollary_4_2_stochasticBetaDomain T L σ Δ) :
    StochasticMuonConfig m n :=
  let q := corollary_4_2_stochasticOneMinusBeta T L σ Δ
  stochasticConstantConfig W0 (corollary_4_2_stochasticEta m n T L σ Δ)
    (1 - q) hβ unitBatchSize

def corollary_4_2_deterministicConfig {m n : ℕ}
    (W0 : Mat m n) (T : ℕ) (L Δ β : ℝ) (hβ : β ∈ Set.Ico (0 : ℝ) 1) :
    DeterministicMomentumMuonConfig m n :=
  deterministicMomentumConstantConfig W0 (corollary_4_2_deterministicEta m n T L Δ) β hβ

def internalCorollary_4_8_stochasticConfig {m n : ℕ}
    (W0 : Mat m n) (T : ℕ) (Lstar σ Δ : ℝ)
    (hβ : internalCorollary_4_8_stochasticBetaDomain m n T Lstar σ Δ) :
    StochasticMuonConfig m n :=
  let q := corollary_4_8_stochasticOneMinusBeta m n T Lstar σ Δ
  stochasticConstantConfig W0 (corollary_4_8_stochasticEta m n T Lstar σ Δ)
    (1 - q) hβ unitBatchSize

def corollary_4_2_stochasticRealization {m n : ℕ}
    (W0 : Mat m n) (T : ℕ) (L σ Δ : ℝ)
    (cfg : StochasticMuonConfig m n) : Prop :=
  horizonDomain T ∧
    cfg.W0 = W0 ∧
    cfg.batchSize.val = 1 ∧
    (∀ t ∈ Finset.range T, cfg.eta t = corollary_4_2_stochasticEta m n T L σ Δ) ∧
    1 - cfg.beta = corollary_4_2_stochasticOneMinusBeta T L σ Δ

theorem internalCorollary_4_2_stochasticConfig_realizes {m n : ℕ}
    (W0 : Mat m n) (T : ℕ) (L σ Δ : ℝ)
    (hT : corollary_4_2_stochasticAdmissibleHorizonDomain m n T L σ Δ) :
    corollary_4_2_stochasticRealization W0 T L σ Δ
      (internalCorollary_4_2_stochasticConfig W0 T L σ Δ hT.2.2) := by
  unfold corollary_4_2_stochasticRealization
  unfold internalCorollary_4_2_stochasticConfig stochasticConstantConfig unitBatchSize
  simp [hT.1.1]

theorem corollary_4_2_stochasticRealization_exists_of_admissible {m n : ℕ}
    (W0 : Mat m n) (T : ℕ) (L σ Δ : ℝ)
    (hT : corollary_4_2_stochasticAdmissibleHorizonDomain m n T L σ Δ) :
    ∃ cfg : StochasticMuonConfig m n,
      corollary_4_2_stochasticRealization W0 T L σ Δ cfg :=
  ⟨internalCorollary_4_2_stochasticConfig W0 T L σ Δ hT.2.2,
    internalCorollary_4_2_stochasticConfig_realizes W0 T L σ Δ hT⟩

def corollary_4_8_stochasticRealization {m n : ℕ}
    (W0 : Mat m n) (T : ℕ) (Lstar σ Δ : ℝ)
    (cfg : StochasticMuonConfig m n) : Prop :=
  horizonDomain T ∧
    cfg.W0 = W0 ∧
    cfg.batchSize.val = 1 ∧
    (∀ t ∈ Finset.range T,
      cfg.eta t = corollary_4_8_stochasticEta m n T Lstar σ Δ) ∧
    1 - cfg.beta = corollary_4_8_stochasticOneMinusBeta m n T Lstar σ Δ

theorem internalCorollary_4_8_stochasticConfig_realizes {m n : ℕ}
    (W0 : Mat m n) (T : ℕ) (Lstar σ Δ : ℝ)
    (hT : corollary_4_8_stochasticAdmissibleHorizonDomain m n T Lstar σ Δ) :
    corollary_4_8_stochasticRealization W0 T Lstar σ Δ
      (internalCorollary_4_8_stochasticConfig W0 T Lstar σ Δ hT.2.2) := by
  unfold corollary_4_8_stochasticRealization
  unfold internalCorollary_4_8_stochasticConfig stochasticConstantConfig unitBatchSize
  simp [hT.1.1]

theorem corollary_4_8_stochasticRealization_exists_of_admissible {m n : ℕ}
    (W0 : Mat m n) (T : ℕ) (Lstar σ Δ : ℝ)
    (hT : corollary_4_8_stochasticAdmissibleHorizonDomain m n T Lstar σ Δ) :
    ∃ cfg : StochasticMuonConfig m n,
      corollary_4_8_stochasticRealization W0 T Lstar σ Δ cfg :=
  ⟨internalCorollary_4_8_stochasticConfig W0 T Lstar σ Δ hT.2.2,
    internalCorollary_4_8_stochasticConfig_realizes W0 T Lstar σ Δ hT⟩

def corollary_4_8_deterministicConfig {m n : ℕ}
    (W0 : Mat m n) (T : ℕ) (Lstar Δ β : ℝ) (hβ : β ∈ Set.Ico (0 : ℝ) 1) :
    DeterministicMomentumMuonConfig m n :=
  deterministicMomentumConstantConfig W0 (corollary_4_8_deterministicEta m n T Lstar Δ) β hβ


/- Source-boundary record for the printed stochastic branch of Corollary 4.2.
   The source prints the beta schedule, while Algorithm 1 requires beta in
   [0,1).  The corrected statement below is therefore deliberately named as an
   admissible-domain result, and this declaration records the Phase 2 boundary
   that remains between the printed horizon domain and the realizable runs. -/
def corollary_4_2_stochastic_downstream_phase2_boundary {ξ : Type*}
    [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (W0 : Mat m n) (L σ : ℝ)
    (hfinite : P.objective.HasFiniteInfimum) : Prop :=
  let Δ := sourceObjectiveInitialGap P.objective W0 hfinite
  corollary_4_2_stochasticSemanticSourceBoundary P W0 L σ Δ

def corollary_4_2_stochastic_corrected_admissible_domain_statement
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (W0 : Mat m n) (L σ : ℝ)
    (hfinite : P.objective.HasFiniteInfimum) : Prop :=
  let Δ := sourceObjectiveInitialGap P.objective W0 hfinite
  let realizes := fun T cfg => corollary_4_2_stochasticRealization W0 T L σ Δ cfg
  RealizedAsymptoticUpperNatOn
    (fun T => corollary_4_2_stochasticSemanticHorizonDomain P W0 T L σ Δ)
    (fun T _hT cfg => realizes T cfg)
    (fun T hT cfg =>
      by
        classical
        exact
          if hr : realizes T cfg then
            stochasticAverageNuclearGradientRealized P cfg T (hT.2 cfg hr)
          else 0)
    (fun T hT => corollary_4_2_stochasticRateRealized m n T L σ Δ hT.1.2.1)
    (theoremScope "Corollary 4.2 corrected stochastic rate on admissible horizons" ["T"]) ∧
  RealizedNuclearStationarityComplexityOn
    (fun T => corollary_4_2_stochasticSemanticHorizonDomain P W0 T L σ Δ)
    (fun T _hT cfg => realizes T cfg)
    (fun T hT cfg =>
      by
        classical
        exact
          if hr : realizes T cfg then
            stochasticAverageNuclearGradientRealized P cfg T (hT.2 cfg hr)
          else 0)
    (corollary_4_2_stochasticComplexityRate m n L σ Δ)
    (theoremScope
      "Corollary 4.2 corrected stochastic epsilon complexity on admissible horizons"
      ["epsilon"]) ∧
  ∀ T : ℕ,
    ∀ hT : corollary_4_2_stochasticSemanticHorizonDomain P W0 T L σ Δ,
    ∀ cfg : StochasticMuonConfig m n,
    ∀ hcfg : corollary_4_2_stochasticRealization W0 T L σ Δ cfg,
    ∀ ε : ℝ,
    stochasticAverageNuclearGradientRealized P cfg T (hT.2 cfg hcfg) ≤ ε →
      StochasticGeneratedOutputGuarantee P cfg T hT.1.1.1 (hT.2 cfg hcfg) ε

/- Source-boundary record for the printed stochastic branch of Corollary 4.8.
   It has the same beta-domain issue as Corollary 4.2, but with the spectral
   smoothness scale Lstar and the additional rank factor in the denominator. -/
def corollary_4_8_stochastic_downstream_phase2_boundary {ξ : Type*}
    [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (W0 : Mat m n) (Lstar σ : ℝ)
    (hfinite : P.objective.HasFiniteInfimum) : Prop :=
  let Δ := sourceObjectiveInitialGap P.objective W0 hfinite
  corollary_4_8_stochasticSemanticSourceBoundary P W0 Lstar σ Δ

def corollary_4_8_stochastic_corrected_admissible_domain_statement
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (W0 : Mat m n) (Lstar σ : ℝ)
    (hfinite : P.objective.HasFiniteInfimum) : Prop :=
  let Δ := sourceObjectiveInitialGap P.objective W0 hfinite
  let realizes := fun T cfg => corollary_4_8_stochasticRealization W0 T Lstar σ Δ cfg
  RealizedAsymptoticUpperNatOn
    (fun T => corollary_4_8_stochasticSemanticHorizonDomain P W0 T Lstar σ Δ)
    (fun T _hT cfg => realizes T cfg)
    (fun T hT cfg =>
      by
        classical
        exact
          if hr : realizes T cfg then
            stochasticAverageNuclearGradientRealized P cfg T (hT.2 cfg hr)
          else 0)
    (fun T hT => corollary_4_8_stochasticRateRealized m n T Lstar σ Δ hT.1.2.1)
    (theoremScope "Corollary 4.8 corrected stochastic rate on admissible horizons" ["T"]) ∧
  RealizedNuclearStationarityComplexityOn
    (fun T => corollary_4_8_stochasticSemanticHorizonDomain P W0 T Lstar σ Δ)
    (fun T _hT cfg => realizes T cfg)
    (fun T hT cfg =>
      by
        classical
        exact
          if hr : realizes T cfg then
            stochasticAverageNuclearGradientRealized P cfg T (hT.2 cfg hr)
          else 0)
    (corollary_4_8_stochasticComplexityRate m n Lstar σ Δ)
    (theoremScope
      "Corollary 4.8 corrected stochastic epsilon complexity on admissible horizons"
      ["epsilon"]) ∧
  ∀ T : ℕ,
    ∀ hT : corollary_4_8_stochasticSemanticHorizonDomain P W0 T Lstar σ Δ,
    ∀ cfg : StochasticMuonConfig m n,
    ∀ hcfg : corollary_4_8_stochasticRealization W0 T Lstar σ Δ cfg,
    ∀ ε : ℝ,
    stochasticAverageNuclearGradientRealized P cfg T (hT.2 cfg hcfg) ≤ ε →
      StochasticGeneratedOutputGuarantee P cfg T hT.1.1.1 (hT.2 cfg hcfg) ε

def corollary_4_2_stochasticRegime
    (m n : ℕ) (L sigma Delta : ℝ) : Prop :=
  0 < matrixRankBound m n ∧ 0 < L ∧ 0 < sigma ∧ 0 < Delta

def corollary_4_8_stochasticRegime
    (m n : ℕ) (Lstar sigma Delta : ℝ) : Prop :=
  0 < matrixRankBound m n ∧ 0 < Lstar ∧ 0 < sigma ∧ 0 < Delta

theorem corollary_4_2_stochasticRegime_realizable
    {m n T : ℕ} {L sigma Delta : ℝ}
    (hreg : corollary_4_2_stochasticRegime m n L sigma Delta)
    (hT : horizonDomain T) :
    corollary_4_2_stochasticRealizableHorizonDomain m n T L sigma Delta := by
  rcases hreg with ⟨hrNat, hL, hsigma, hDelta⟩
  have hr : 0 < (matrixRankBound m n : ℝ) := by exact_mod_cast hrNat
  have hTr : 0 < (T : ℝ) := by exact_mod_cast hT
  have hratio :
      0 < sourceQuot (Real.sqrt (L * Delta)) (sigma * Real.sqrt (T : ℝ)) := by
    unfold sourceQuot
    positivity
  have hq : 0 < corollary_4_2_stochasticOneMinusBeta T L sigma Delta := by
    unfold corollary_4_2_stochasticOneMinusBeta
    exact lt_min hratio zero_lt_one
  have hqle : corollary_4_2_stochasticOneMinusBeta T L sigma Delta ≤ 1 := by
    unfold corollary_4_2_stochasticOneMinusBeta
    exact min_le_right _ _
  refine ⟨?_, ?_, ?_⟩
  · unfold corollary_4_2_stochasticScheduleDomain sourceSqrtDomain
      sourceQuotDomain sourceSqrtQuotDomain sourceQuot
    dsimp
    constructor
    · exact hT
    constructor
    · positivity
    constructor
    · positivity
    constructor
    · positivity
    constructor
    · constructor <;>
        (simp only [sourceQuotDomain, sourceSqrtDomain, sourceQuot]; positivity)
    · positivity
  · unfold corollary_4_2_stochasticRateDomain sourceSqrtDomain
      sourceQuotDomain sourceSqrtQuotDomain sourceQuot
    dsimp
    constructor
    · exact hT
    constructor
    · constructor <;>
        (simp only [sourceQuotDomain, sourceSqrtDomain, sourceQuot]; positivity)
    constructor
    · constructor <;>
        (simp only [sourceQuotDomain, sourceSqrtDomain, sourceQuot]; positivity)
    constructor
    · positivity
    · positivity
  · unfold internalCorollary_4_2_stochasticBetaDomain
    constructor <;> linarith

theorem corollary_4_8_stochasticRegime_realizable
    {m n T : ℕ} {Lstar sigma Delta : ℝ}
    (hreg : corollary_4_8_stochasticRegime m n Lstar sigma Delta)
    (hT : horizonDomain T) :
    corollary_4_8_stochasticRealizableHorizonDomain m n T Lstar sigma Delta := by
  rcases hreg with ⟨hrNat, hLstar, hsigma, hDelta⟩
  have hr : 0 < (matrixRankBound m n : ℝ) := by exact_mod_cast hrNat
  have hTr : 0 < (T : ℝ) := by exact_mod_cast hT
  have hratio : 0 < sourceQuot (Real.sqrt (Lstar * Delta))
      (sigma * Real.sqrt ((matrixRankBound m n : ℝ) * (T : ℝ))) := by
    unfold sourceQuot
    positivity
  have hq : 0 < corollary_4_8_stochasticOneMinusBeta m n T Lstar sigma Delta := by
    unfold corollary_4_8_stochasticOneMinusBeta
    exact lt_min hratio zero_lt_one
  have hqle : corollary_4_8_stochasticOneMinusBeta m n T Lstar sigma Delta ≤ 1 := by
    unfold corollary_4_8_stochasticOneMinusBeta
    exact min_le_right _ _
  refine ⟨?_, ?_, ?_⟩
  · unfold corollary_4_8_stochasticScheduleDomain sourceSqrtDomain
      sourceQuotDomain sourceSqrtQuotDomain sourceQuot
    dsimp
    constructor
    · exact hT
    constructor
    · positivity
    constructor
    · positivity
    constructor
    · positivity
    constructor
    · constructor <;>
        (simp only [sourceQuotDomain, sourceSqrtDomain, sourceQuot]; positivity)
    · positivity
  · unfold corollary_4_8_stochasticRateDomain sourceSqrtDomain
      sourceQuotDomain sourceSqrtQuotDomain sourceQuot
    dsimp
    constructor
    · exact hT
    constructor
    · constructor <;>
        (simp only [sourceQuotDomain, sourceSqrtDomain, sourceQuot]; positivity)
    constructor
    · constructor <;>
        (simp only [sourceQuotDomain, sourceSqrtDomain, sourceQuot]; positivity)
    constructor
    · positivity
    · positivity
  · unfold internalCorollary_4_8_stochasticBetaDomain
    constructor <;> linarith

theorem corollary_4_2_stochasticRegime_semantic
    {xi : Type*} [MeasurableSpace xi] {m n T : ℕ}
    (P : StochasticProblem xi m n) (W0 : Mat m n) {L sigma Delta : ℝ}
    (hreg : corollary_4_2_stochasticRegime m n L sigma Delta)
    (hT : horizonDomain T) (hSmooth : FrobeniusSmooth P.objective L)
    (hVariance : BoundedVariance P sigma) :
    corollary_4_2_stochasticSemanticHorizonDomain P W0 T L sigma Delta := by
  refine ⟨corollary_4_2_stochasticRegime_realizable hreg hT, ?_⟩
  intro cfg _hrun
  exact stochasticAverageNuclearGradient_wellDefined_of_source_assumptions
    P cfg T sigma (Or.inl ⟨L, hSmooth⟩) hVariance

theorem corollary_4_8_stochasticRegime_semantic
    {xi : Type*} [MeasurableSpace xi] {m n T : ℕ}
    (P : StochasticProblem xi m n) (W0 : Mat m n) {Lstar sigma Delta : ℝ}
    (hreg : corollary_4_8_stochasticRegime m n Lstar sigma Delta)
    (hT : horizonDomain T) (hSmooth : SpectralSmooth P.objective Lstar)
    (hVariance : BoundedVariance P sigma) :
    corollary_4_8_stochasticSemanticHorizonDomain P W0 T Lstar sigma Delta := by
  refine ⟨corollary_4_8_stochasticRegime_realizable hreg hT, ?_⟩
  intro cfg _hrun
  exact stochasticAverageNuclearGradient_wellDefined_of_source_assumptions
    P cfg T sigma (Or.inr (Or.inl ⟨Lstar, hSmooth⟩)) hVariance

/- A zero deterministic rate coefficient cannot support the paper's usual
   positive-horizon `O(coefficient * epsilon⁻²)` packaging.  The meaningful
   endpoint is instead stationarity of the initial point and hence literal
   zero motion of the deterministic Algorithm 1 realization. -/
def deterministicMomentumZeroMotion {m n : ℕ}
    (P : Objective m n) (W0 : Mat m n)
    (cfgForHorizon : ℕ → DeterministicMomentumMuonConfig m n) : Prop :=
  P.grad W0 = 0 ∧
    ∀ T t : ℕ,
      (deterministicMomentumMuonState P (cfgForHorizon T) t).W = W0 ∧
      (deterministicMomentumMuonState P (cfgForHorizon T) t).M = 0

theorem deterministicMomentum_zeroMotion_of_grad_eq_zero {m n : ℕ}
    (P : Objective m n) (W0 : Mat m n)
    (cfgForHorizon : ℕ → DeterministicMomentumMuonConfig m n)
    (hW0 : ∀ T : ℕ, (cfgForHorizon T).W0 = W0)
    (hgrad : P.grad W0 = 0) :
    deterministicMomentumZeroMotion P W0 cfgForHorizon := by
  refine ⟨hgrad, ?_⟩
  intro T t
  induction t with
  | zero =>
      simp [deterministicMomentumMuonState, deterministicMomentumMuonBaseState,
        deterministicGradient, hW0 T, hgrad]
  | succ t ih =>
      rcases ih with ⟨hWt, hMt⟩
      have hdir : orthogonalizedDirection (0 : Mat m n) = 0 := by
        unfold orthogonalizedDirection
        ext i j
        rw [Matrix.mul_apply]
        have hrank : (0 : Mat m n).rank = 0 := by simp
        apply Finset.sum_eq_zero
        intro k _hk
        have hklt : (k : ℕ) < 0 := by simpa [hrank] using k.isLt
        exact (Nat.not_lt_zero _ hklt).elim
      change
        (deterministicMomentumMuonStep P (cfgForHorizon T) t
          (deterministicMomentumMuonState P (cfgForHorizon T) t)).W = W0 ∧
        (deterministicMomentumMuonStep P (cfgForHorizon T) t
          (deterministicMomentumMuonState P (cfgForHorizon T) t)).M = 0
      simp [deterministicMomentumMuonStep, muonUpdate, deterministicGradient,
        hWt, hMt, hdir, hgrad]

def corollary_4_2_deterministicZeroMotion {m n : ℕ}
    (P : Objective m n) (W0 : Mat m n) (L Delta beta : ℝ)
    (hbeta : beta ∈ Set.Ico (0 : ℝ) 1) : Prop :=
  deterministicMomentumZeroMotion P W0
    (fun T => corollary_4_2_deterministicConfig W0 T L Delta beta hbeta)

def corollary_4_8_deterministicZeroMotion {m n : ℕ}
    (P : Objective m n) (W0 : Mat m n) (Lstar Delta beta : ℝ)
    (hbeta : beta ∈ Set.Ico (0 : ℝ) 1) : Prop :=
  deterministicMomentumZeroMotion P W0
    (fun T => corollary_4_8_deterministicConfig W0 T Lstar Delta beta hbeta)

private def corollary_4_2_preCorrection_deterministicClause
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (W0 : Mat m n) (L sigma Delta : ℝ) : Prop :=
  sigma = 0 →
    ∀ beta : ℝ, ∀ hbeta : beta ∈ Set.Ico (0 : ℝ) 1, constantMomentumO1 beta →
    DomainAsymptoticUpperNatOn
      (fun T => corollary_4_2_deterministicRateDomain m n T L Delta)
      (fun T _hT => deterministicMomentumAverageNuclearGradient P.objective
        (corollary_4_2_deterministicConfig W0 T L Delta beta hbeta) T)
      (fun T hT => corollary_4_2_deterministicRateRealized m n T L Delta hT)
      (theoremScope "Corollary 4.2 deterministic rate" ["T"]) ∧
    NuclearStationarityComplexityOn
      (fun T => corollary_4_2_deterministicRateDomain m n T L Delta)
      (fun T _hT => deterministicMomentumAverageNuclearGradient P.objective
        (corollary_4_2_deterministicConfig W0 T L Delta beta hbeta) T)
      (corollary_4_2_deterministicComplexityRate m n L Delta)
      (theoremScope "Corollary 4.2 deterministic epsilon complexity" ["epsilon"])

private def corollary_4_8_preCorrection_deterministicClause
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (W0 : Mat m n)
    (Lstar sigma Delta : ℝ) : Prop :=
  sigma = 0 →
    ∀ beta : ℝ, ∀ hbeta : beta ∈ Set.Ico (0 : ℝ) 1, constantMomentumO1 beta →
    DomainAsymptoticUpperNatOn
      (fun T => corollary_4_8_deterministicRateDomain m n T Lstar Delta)
      (fun T _hT => deterministicMomentumAverageNuclearGradient P.objective
        (corollary_4_8_deterministicConfig W0 T Lstar Delta beta hbeta) T)
      (fun T hT => corollary_4_8_deterministicRateRealized m n T Lstar Delta hT)
      (theoremScope "Corollary 4.8 deterministic rate" ["T"]) ∧
    NuclearStationarityComplexityOn
      (fun T => corollary_4_8_deterministicRateDomain m n T Lstar Delta)
      (fun T _hT => deterministicMomentumAverageNuclearGradient P.objective
        (corollary_4_8_deterministicConfig W0 T Lstar Delta beta hbeta) T)
      (corollary_4_8_deterministicComplexityRate m n Lstar Delta)
      (theoremScope "Corollary 4.8 deterministic epsilon complexity" ["epsilon"])

def corollary_4_2_statement {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (W0 : Mat m n) (L σ : ℝ)
    (hfinite : P.objective.HasFiniteInfimum) : Prop :=
  let Δ := sourceObjectiveInitialGap P.objective W0 hfinite
  corollary_4_2_stochastic_downstream_phase2_boundary P W0 L σ hfinite ∧
    (corollary_4_2_stochasticRegime m n L σ Δ →
      corollary_4_2_stochastic_corrected_admissible_domain_statement P W0 L σ hfinite) ∧
    (σ = 0 →
      ∀ β : ℝ, ∀ hβ : β ∈ Set.Ico (0 : ℝ) 1, constantMomentumO1 β →
      DomainAsymptoticUpperNatOn
        (fun T => corollary_4_2_deterministicRateDomain m n T L Δ)
        (fun T _hT => deterministicMomentumAverageNuclearGradient P.objective
          (corollary_4_2_deterministicConfig W0 T L Δ β hβ) T)
        (fun T hT => corollary_4_2_deterministicRateRealized m n T L Δ hT)
        (theoremScope "Corollary 4.2 deterministic rate" ["T"]) ∧
      ((0 < (matrixRankBound m n : ℝ) * L * Δ →
        NuclearStationarityComplexityOn
          (fun T => corollary_4_2_deterministicRateDomain m n T L Δ)
          (fun T _hT => deterministicMomentumAverageNuclearGradient P.objective
            (corollary_4_2_deterministicConfig W0 T L Δ β hβ) T)
          (corollary_4_2_deterministicComplexityRate m n L Δ)
          (theoremScope "Corollary 4.2 deterministic epsilon complexity" ["epsilon"]) ∧
        GeneratedNuclearStationarityTransfer P.objective
          (fun T => corollary_4_2_deterministicRateDomain m n T L Δ)
          (fun T _hT => deterministicMomentumAverageNuclearGradient P.objective
            (corollary_4_2_deterministicConfig W0 T L Δ β hβ) T)
          (fun T _hT t =>
            (deterministicMomentumMuonState P.objective
              (corollary_4_2_deterministicConfig W0 T L Δ β hβ) t).W)) ∧
       ((matrixRankBound m n : ℝ) * L * Δ = 0 →
        corollary_4_2_deterministicZeroMotion P.objective W0 L Δ β hβ ∧
          IsNuclearStationary P.objective 0
            ((deterministicMomentumMuonState P.objective
              (corollary_4_2_deterministicConfig W0 1 L Δ β hβ) 0).W))))

def corollary_4_8_statement {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (W0 : Mat m n) (Lstar σ : ℝ)
    (hfinite : P.objective.HasFiniteInfimum) : Prop :=
  let Δ := sourceObjectiveInitialGap P.objective W0 hfinite
  corollary_4_8_stochastic_downstream_phase2_boundary P W0 Lstar σ hfinite ∧
    (corollary_4_8_stochasticRegime m n Lstar σ Δ →
      corollary_4_8_stochastic_corrected_admissible_domain_statement
        P W0 Lstar σ hfinite) ∧
    (σ = 0 →
      ∀ β : ℝ, ∀ hβ : β ∈ Set.Ico (0 : ℝ) 1, constantMomentumO1 β →
      DomainAsymptoticUpperNatOn
        (fun T => corollary_4_8_deterministicRateDomain m n T Lstar Δ)
        (fun T _hT => deterministicMomentumAverageNuclearGradient P.objective
          (corollary_4_8_deterministicConfig W0 T Lstar Δ β hβ) T)
        (fun T hT => corollary_4_8_deterministicRateRealized m n T Lstar Δ hT)
        (theoremScope "Corollary 4.8 deterministic rate" ["T"]) ∧
      ((0 < Lstar * Δ →
        NuclearStationarityComplexityOn
          (fun T => corollary_4_8_deterministicRateDomain m n T Lstar Δ)
          (fun T _hT => deterministicMomentumAverageNuclearGradient P.objective
            (corollary_4_8_deterministicConfig W0 T Lstar Δ β hβ) T)
          (corollary_4_8_deterministicComplexityRate m n Lstar Δ)
          (theoremScope "Corollary 4.8 deterministic epsilon complexity" ["epsilon"]) ∧
        GeneratedNuclearStationarityTransfer P.objective
          (fun T => corollary_4_8_deterministicRateDomain m n T Lstar Δ)
          (fun T _hT => deterministicMomentumAverageNuclearGradient P.objective
            (corollary_4_8_deterministicConfig W0 T Lstar Δ β hβ) T)
          (fun T _hT t =>
            (deterministicMomentumMuonState P.objective
              (corollary_4_8_deterministicConfig W0 T Lstar Δ β hβ) t).W)) ∧
       (Lstar * Δ = 0 →
        corollary_4_8_deterministicZeroMotion P.objective W0 Lstar Δ β hβ ∧
          IsNuclearStationary P.objective 0
            ((deterministicMomentumMuonState P.objective
              (corollary_4_8_deterministicConfig W0 1 Lstar Δ β hβ) 0).W))))

theorem corollary_4_2_sigma_zero_stochastic_clause_false
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (W0 : Mat m n) (L : ℝ)
    (hfinite : P.objective.HasFiniteInfimum) :
    ¬ corollary_4_2_stochastic_corrected_admissible_domain_statement
      P W0 L 0 hfinite := by
  intro h
  rcases h.2.1 with ⟨_horizonBound, _hAsymptotic, hAccuracy⟩
  rcases hAccuracy 1 (by norm_num [epsilonDomain]) with
    ⟨T, hT, _cfg, _horizon, _hrealizes, _haverage⟩
  have hquot := hT.1.1.2.2.2.1
  simp [corollary_4_2_stochasticScheduleDomain, sourceQuotDomain] at hquot

theorem corollary_4_8_sigma_zero_stochastic_clause_false
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (W0 : Mat m n) (Lstar : ℝ)
    (hfinite : P.objective.HasFiniteInfimum) :
    ¬ corollary_4_8_stochastic_corrected_admissible_domain_statement
      P W0 Lstar 0 hfinite := by
  intro h
  rcases h.2.1 with ⟨_horizonBound, _hAsymptotic, hAccuracy⟩
  rcases hAccuracy 1 (by norm_num [epsilonDomain]) with
    ⟨T, hT, _cfg, _horizon, _hrealizes, _haverage⟩
  have hquot := hT.1.1.2.2.2.1
  simp [corollary_4_8_stochasticScheduleDomain, sourceQuotDomain] at hquot

def corollaryDeterministicOracleZeroObjective : Objective 1 1 :=
  { f := fun _ => 0 }

theorem corollaryDeterministicOracleZeroObjective_hasFiniteInfimum :
    corollaryDeterministicOracleZeroObjective.HasFiniteInfimum := by
  refine ⟨0, ?_⟩
  intro y hy
  rcases hy with ⟨W, rfl⟩
  simp [corollaryDeterministicOracleZeroObjective]

theorem corollaryDeterministicOracleZeroObjective_frobeniusSmooth :
    FrobeniusSmooth corollaryDeterministicOracleZeroObjective 0 := by
  constructor
  · simpa [vectorizedObjective, corollaryDeterministicOracleZeroObjective] using
      (contDiff_const : ContDiff ℝ 1 (fun _ : Mat 1 1 => (0 : ℝ)))
  · intro W W'
    have hzero (X : Mat 1 1) : objectiveGradient (fun _ : Mat 1 1 => (0 : ℝ)) X = 0 := by
      ext i j
      simp [objectiveGradient]
    rw [show corollaryDeterministicOracleZeroObjective.grad W = 0 by
      exact hzero W]
    rw [show corollaryDeterministicOracleZeroObjective.grad W' = 0 by
      exact hzero W']
    simp [frobeniusNorm]

theorem corollaryDeterministicOracleZeroObjective_spectralSmooth :
    SpectralSmooth corollaryDeterministicOracleZeroObjective 0 := by
  constructor
  · exact le_rfl
  · simpa [vectorizedObjective, corollaryDeterministicOracleZeroObjective] using
      (contDiff_const : ContDiff ℝ 1 (fun _ : Mat 1 1 => (0 : ℝ)))
  · intro W W'
    have hzero (X : Mat 1 1) : objectiveGradient (fun _ : Mat 1 1 => (0 : ℝ)) X = 0 := by
      ext i j
      simp [objectiveGradient]
    rw [show corollaryDeterministicOracleZeroObjective.grad W = 0 by
      exact hzero W]
    rw [show corollaryDeterministicOracleZeroObjective.grad W' = 0 by
      exact hzero W']
    simp [nuclearNorm]

private theorem corollary_4_2_preCorrection_sigma_zero_counterexample :
    let P := deterministicOracleProblem corollaryDeterministicOracleZeroObjective
    ∃ hfinite : P.objective.HasFiniteInfimum,
      FrobeniusSmooth P.objective 0 ∧ BoundedVariance P 0 ∧
        ¬ corollary_4_2_stochastic_corrected_admissible_domain_statement
          P 0 0 0 hfinite := by
  dsimp
  have hfinite :
      (deterministicOracleProblem corollaryDeterministicOracleZeroObjective).objective.HasFiniteInfimum := by
    simpa only [deterministicOracleProblem_objective] using
      corollaryDeterministicOracleZeroObjective_hasFiniteInfimum
  refine ⟨hfinite, ?_, deterministicOracleProblem_boundedVariance_zero _, ?_⟩
  · simpa only [deterministicOracleProblem_objective] using
      corollaryDeterministicOracleZeroObjective_frobeniusSmooth
  · exact corollary_4_2_sigma_zero_stochastic_clause_false _ _ _ _

private theorem corollary_4_8_preCorrection_sigma_zero_counterexample :
    let P := deterministicOracleProblem corollaryDeterministicOracleZeroObjective
    ∃ hfinite : P.objective.HasFiniteInfimum,
      SpectralSmooth P.objective 0 ∧ BoundedVariance P 0 ∧
        ¬ corollary_4_8_stochastic_corrected_admissible_domain_statement
          P 0 0 0 hfinite := by
  dsimp
  have hfinite :
      (deterministicOracleProblem corollaryDeterministicOracleZeroObjective).objective.HasFiniteInfimum := by
    simpa only [deterministicOracleProblem_objective] using
      corollaryDeterministicOracleZeroObjective_hasFiniteInfimum
  refine ⟨hfinite, ?_, deterministicOracleProblem_boundedVariance_zero _, ?_⟩
  · simpa only [deterministicOracleProblem_objective] using
      corollaryDeterministicOracleZeroObjective_spectralSmooth
  · exact corollary_4_8_sigma_zero_stochastic_clause_false _ _ _ _

theorem nuclearStationarityComplexityOn_zero_rate_false
    {domain : ℕ → Prop} {average : ∀ T : ℕ, domain T → ℝ}
    (scope : AsymptoticScope)
    (hdomain : ∀ T : ℕ, domain T → horizonDomain T) :
    ¬ NuclearStationarityComplexityOn domain average (fun _ => 0) scope := by
  rintro ⟨horizonBound,
    ⟨C, ε₀, hC, hε₀, _hscope, hbound⟩, haccuracy⟩
  let ε : ℝ := min (ε₀ / 2) (1 / 2)
  have hε : epsilonDomain ε := by
    dsimp [epsilonDomain, ε]
    exact lt_min (half_pos hε₀) (by norm_num)
  have hεle : ε ≤ ε₀ := by
    dsimp [ε]
    exact le_trans (min_le_left _ _) (by linarith)
  have hhorizon_nonpos : horizonBound ε ≤ 0 := by
    simpa using hbound ε hε hε hεle
  rcases haccuracy ε hε with ⟨T, hT, hTbound, _haverage⟩
  have hTpos : 0 < (T : ℝ) := by
    exact_mod_cast hdomain T hT
  linarith

/- The first correction (above) records that the stochastic schedule is
   undefined at sigma = 0.  These two certificates record the independent
   deterministic defect in the still-unchanged statement bodies: at zero
   smoothness/gap scale the printed complexity rate is identically zero, while
   `NuclearStationarityComplexityOn` insists on a positive horizon bounded by
   that zero rate. -/
private theorem corollary_4_2_preCorrection_deterministic_zero_rate_counterexample :
    let P := deterministicOracleProblem corollaryDeterministicOracleZeroObjective
    ∃ hfinite : P.objective.HasFiniteInfimum,
      FrobeniusSmooth P.objective 0 ∧ BoundedVariance P 0 ∧
        ¬ corollary_4_2_preCorrection_deterministicClause P 0 0 0 0 := by
  dsimp
  have hfinite :
      (deterministicOracleProblem corollaryDeterministicOracleZeroObjective).objective.HasFiniteInfimum := by
    simpa only [deterministicOracleProblem_objective] using
      corollaryDeterministicOracleZeroObjective_hasFiniteInfimum
  refine ⟨hfinite, ?_, deterministicOracleProblem_boundedVariance_zero _, ?_⟩
  · simpa only [deterministicOracleProblem_objective] using
      corollaryDeterministicOracleZeroObjective_frobeniusSmooth
  · intro hstatement
    have hbeta : (0 : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by norm_num
    have hbetaO : constantMomentumO1 0 := by
      refine ⟨1, 0, by norm_num, ?_, ?_⟩
      · simp [ConstantRespectsScope, theoremScope]
      · intro T _htrue _hT
        norm_num
    have hcomplexity := (hstatement rfl 0 hbeta hbetaO).2
    have hrate : corollary_4_2_deterministicComplexityRate 1 1 0 0 =
        (fun _ => 0) := by
      funext ε
      simp [corollary_4_2_deterministicComplexityRate]
    rw [hrate] at hcomplexity
    have hfalse := nuclearStationarityComplexityOn_zero_rate_false
      (domain := fun T => corollary_4_2_deterministicRateDomain 1 1 T 0 0)
      (average := fun T hT => deterministicMomentumAverageNuclearGradient
        (deterministicOracleProblem corollaryDeterministicOracleZeroObjective).objective
        (corollary_4_2_deterministicConfig 0 T 0 0 0 hbeta) T)
      (theoremScope "Corollary 4.2 deterministic epsilon complexity" ["epsilon"])
      (fun T hT => hT.1)
    exact hfalse hcomplexity

private theorem corollary_4_8_preCorrection_deterministic_zero_rate_counterexample :
    let P := deterministicOracleProblem corollaryDeterministicOracleZeroObjective
    ∃ hfinite : P.objective.HasFiniteInfimum,
      SpectralSmooth P.objective 0 ∧ BoundedVariance P 0 ∧
        ¬ corollary_4_8_preCorrection_deterministicClause P 0 0 0 0 := by
  dsimp
  have hfinite :
      (deterministicOracleProblem corollaryDeterministicOracleZeroObjective).objective.HasFiniteInfimum := by
    simpa only [deterministicOracleProblem_objective] using
      corollaryDeterministicOracleZeroObjective_hasFiniteInfimum
  refine ⟨hfinite, ?_, deterministicOracleProblem_boundedVariance_zero _, ?_⟩
  · simpa only [deterministicOracleProblem_objective] using
      corollaryDeterministicOracleZeroObjective_spectralSmooth
  · intro hstatement
    have hbeta : (0 : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by norm_num
    have hbetaO : constantMomentumO1 0 := by
      refine ⟨1, 0, by norm_num, ?_, ?_⟩
      · simp [ConstantRespectsScope, theoremScope]
      · intro T _htrue _hT
        norm_num
    have hcomplexity := (hstatement rfl 0 hbeta hbetaO).2
    have hrate : corollary_4_8_deterministicComplexityRate 1 1 0 0 =
        (fun _ => 0) := by
      funext ε
      simp [corollary_4_8_deterministicComplexityRate]
    rw [hrate] at hcomplexity
    have hfalse := nuclearStationarityComplexityOn_zero_rate_false
      (domain := fun T => corollary_4_8_deterministicRateDomain 1 1 T 0 0)
      (average := fun T hT => deterministicMomentumAverageNuclearGradient
        (deterministicOracleProblem corollaryDeterministicOracleZeroObjective).objective
        (corollary_4_8_deterministicConfig 0 T 0 0 0 hbeta) T)
      (theoremScope "Corollary 4.8 deterministic epsilon complexity" ["epsilon"])
      (fun T hT => hT.1)
    exact hfalse hcomplexity

/- Source: book/Muon/Muon.json#/key_lemmas/theorem_4_5,
   #/key_lemmas/theorem_4_6, #/key_lemmas/theorem_4_9, and
   #/key_lemmas/theorem_4_10.  The displayed inequality and the printed
   precision/complexity clause are both part of the public endpoint contract. -/
def theorem_4_5_precisionDomain (m n : ℕ) (L Dop Δ ε : ℝ) : Prop :=
  epsilonDomain ε ∧
    sourceQuotDomain ε ((matrixRankBound m n : ℝ) * L * Dop) ∧
    sourceInvDomain ε ∧
    sourceLogQuotDomain Δ ε ∧
    let η := sourceQuot ε ((matrixRankBound m n : ℝ) * L * Dop)
    0 ≤ η ∧ η ≤ Dop

def theorem_4_5_etaRateRealized (m n : ℕ) (L Dop ε : ℝ)
    (hdom : sourceQuotDomain ε ((matrixRankBound m n : ℝ) * L * Dop)) : ℝ :=
  realizedSourceQuot ε ((matrixRankBound m n : ℝ) * L * Dop) hdom

def theorem_4_5_complexityRateRealized (m n : ℕ) (L Dop Δ ε : ℝ)
    (hdom : theorem_4_5_precisionDomain m n L Dop Δ ε) : ℝ :=
  (matrixRankBound m n : ℝ) * L * Dop ^ 2 *
    realizedSourceInv ε hdom.2.2.1 *
    realizedSourceLogQuot Δ ε hdom.2.2.2.1

def theorem_4_6_complexityRateRealized (m n : ℕ) (L Dop ε : ℝ)
    (hε : epsilonDomain ε) : ℝ :=
  (matrixRankBound m n : ℝ) * L * Dop ^ 2 *
    realizedSourceInv ε (ne_of_gt hε)

def theorem_4_9_precisionDomain (_m _n : ℕ) (Lstar Dop Δ ε : ℝ) : Prop :=
  epsilonDomain ε ∧
    sourceQuotDomain ε (Lstar * Dop) ∧
    sourceInvDomain ε ∧
    sourceLogQuotDomain Δ ε ∧
    let η := sourceQuot ε (Lstar * Dop)
    0 ≤ η ∧ η ≤ Dop

def theorem_4_9_etaRateRealized (_m _n : ℕ) (Lstar Dop ε : ℝ)
    (hdom : sourceQuotDomain ε (Lstar * Dop)) : ℝ :=
  realizedSourceQuot ε (Lstar * Dop) hdom

def theorem_4_9_complexityRateRealized (m n : ℕ) (Lstar Dop Δ ε : ℝ)
    (hdom : theorem_4_9_precisionDomain m n Lstar Dop Δ ε) : ℝ :=
  Lstar * Dop ^ 2 *
    realizedSourceInv ε hdom.2.2.1 *
    realizedSourceLogQuot Δ ε hdom.2.2.2.1

def theorem_4_10_complexityRateRealized (_m _n : ℕ) (Lstar Dop ε : ℝ)
    (hε : epsilonDomain ε) : ℝ :=
  Lstar * Dop ^ 2 * realizedSourceInv ε (ne_of_gt hε)

def theorem_4_5_precisionConfig {m n : ℕ}
    (base : DeterministicMuonConfig m n) (L Dop Δ ε : ℝ)
    (hdom : theorem_4_5_precisionDomain m n L Dop Δ ε) :
    DeterministicMuonConfig m n :=
  deterministicConstantConfig base.W0 (theorem_4_5_etaRateRealized m n L Dop ε hdom.2.1)

/- Appendix C.1's explicit logarithmic/ceiling horizon.  This is scalar
   schedule algebra only; it contains no run or objective-gap assumption. -/
noncomputable def theorem_4_5_logHorizon
    (m n : ℕ) (L Dop Δ ε : ℝ)
    (_hε : theorem_4_5_precisionDomain m n L Dop Δ ε) : ℕ :=
  Nat.ceil
    (((matrixRankBound m n : ℝ) * L * Dop ^ 2 / ε) *
      Real.log (2 * Δ / ε))

/- Assumption 4.4 belongs to the rescheduled Algorithm 2 run at the horizon
   selected for a particular accuracy.  This pointwise predicate is the
   narrowest source-faithful interface for that instance of the assumption. -/
def theorem_4_5_precisionRunAt {m n : ℕ}
    (P : Objective m n) (base : DeterministicMuonConfig m n)
    (Wstar : Mat m n) (L Dop Δ ε : ℝ)
    (hε : theorem_4_5_precisionDomain m n L Dop Δ ε) (N : ℕ) : Prop :=
  BoundedOperatorDistance P
    (theorem_4_5_precisionConfig base L Dop Δ ε hε) N Wstar Dop

/- The source's precision read-off needs a selected rescheduled run.  The
   crossing contract contains only the horizon bound, Assumption 4.4 at that
   selected horizon, and the scalar Appendix C.1 right-hand side.  It does not
   assume the desired objective-gap conclusion and does not quantify bounded
   distance over every horizon. -/
def theorem_4_9_precisionConfig {m n : ℕ}
    (base : DeterministicMuonConfig m n) (Lstar Dop Δ ε : ℝ)
    (hdom : theorem_4_9_precisionDomain m n Lstar Dop Δ ε) :
    DeterministicMuonConfig m n :=
  deterministicConstantConfig base.W0
    (theorem_4_9_etaRateRealized m n Lstar Dop ε hdom.2.1)

/- Appendix C.2 selects the accuracy horizon before invoking Assumption 4.4.
   The selector is scalar: it contains no run, objective-gap, or desired
   complexity premise. -/
noncomputable def theorem_4_6_selectedHorizon
    (m n : ℕ) (L Dop ε : ℝ) (_hε : epsilonDomain ε) : ℕ :=
  Nat.ceil (2 * (matrixRankBound m n : ℝ) * L * Dop ^ 2 / ε)

/- Appendix C.3 uses the same formula-first logarithmic selection pattern as
   Appendix C.1, with the rank factor absent from the spectral scale. -/
noncomputable def theorem_4_9_logHorizon
    (m n : ℕ) (Lstar Dop Δ ε : ℝ)
    (_hε : theorem_4_9_precisionDomain m n Lstar Dop Δ ε) : ℕ :=
  Nat.ceil ((Lstar * Dop ^ 2 / ε) * Real.log (2 * Δ / ε))

/- Assumption 4.4 is consumed only for the rescheduled precision run at the
   selected C.3 horizon. -/
def theorem_4_9_precisionRunAt {m n : ℕ}
    (P : Objective m n) (base : DeterministicMuonConfig m n)
    (Wstar : Mat m n) (Lstar Dop Δ ε : ℝ)
    (hε : theorem_4_9_precisionDomain m n Lstar Dop Δ ε) (N : ℕ) : Prop :=
  BoundedOperatorDistance P
    (theorem_4_9_precisionConfig base Lstar Dop Δ ε hε) N Wstar Dop

def theorem_4_6_adaptiveSchedule {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (t : ℕ) (L : ℝ) : Prop :=
  ∀ k ∈ Finset.range t,
    ∃ hdom : sourceQuotDomain
        (nuclearNorm (P.grad ((deterministicMuonState P cfg k).W)))
        ((matrixRankBound m n : ℝ) * L),
      cfg.eta k =
        realizedSourceQuot
          (nuclearNorm (P.grad ((deterministicMuonState P cfg k).W)))
          ((matrixRankBound m n : ℝ) * L) hdom

def theorem_4_10_adaptiveSchedule {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (t : ℕ) (Lstar : ℝ) : Prop :=
  ∀ k ∈ Finset.range t,
    ∃ hdom : sourceQuotDomain
        (nuclearNorm (P.grad ((deterministicMuonState P cfg k).W))) Lstar,
      cfg.eta k =
        realizedSourceQuot
          (nuclearNorm (P.grad ((deterministicMuonState P cfg k).W))) Lstar hdom

/- Pointwise realization of the C.2 selected horizon.  This is intentionally
   not an all-horizon family. -/
def theorem_4_6_precisionRunAt {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (Wstar : Mat m n) (L Dop : ℝ) (N : ℕ) : Prop :=
  BoundedOperatorDistance P cfg N Wstar Dop ∧
    theorem_4_6_adaptiveSchedule P cfg N L

/- Appendix C.4's scalar-selected accuracy horizon and its pointwise run
   realization. -/
noncomputable def theorem_4_10_selectedHorizon
    (_m _n : ℕ) (Lstar Dop ε : ℝ) (_hε : epsilonDomain ε) : ℕ :=
  Nat.ceil (2 * Lstar * Dop ^ 2 / ε)

def theorem_4_10_precisionRunAt {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (Wstar : Mat m n) (Lstar Dop : ℝ) (N : ℕ) : Prop :=
  BoundedOperatorDistance P cfg N Wstar Dop ∧
    theorem_4_10_adaptiveSchedule P cfg N Lstar

/- Route tombstone `muon_c2_c3_c4_universal_run_families_v1`:
   `theorem_4_6_adaptiveRunFamily`, `theorem_4_9_precisionRunFamily`, and
   `theorem_4_10_adaptiveRunFamily` were non-source all-horizon wrappers.
   They are deliberately absent from the compiled surface; formula selection
   now precedes the pointwise run assumptions above. -/

theorem theorem_4_6_adaptiveSchedule_domain_obligation {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (t : ℕ) (L : ℝ)
    (_hη : theorem_4_6_adaptiveSchedule P cfg t L) :
    ∀ k ∈ Finset.range t,
      sourceQuotDomain
        (nuclearNorm (P.grad ((deterministicMuonState P cfg k).W)))
        ((matrixRankBound m n : ℝ) * L) := by
  intro k hk
  rcases _hη k hk with ⟨hdom, _heta⟩
  exact hdom

theorem theorem_4_10_adaptiveSchedule_domain_obligation {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (t : ℕ) (Lstar : ℝ)
    (_hη : theorem_4_10_adaptiveSchedule P cfg t Lstar) :
    ∀ k ∈ Finset.range t,
      sourceQuotDomain (nuclearNorm (P.grad ((deterministicMuonState P cfg k).W))) Lstar := by
  intro k hk
  rcases _hη k hk with ⟨hdom, _heta⟩
  exact hdom

/- Appendix C.1 uses a nonnegative contraction.  Its source-level scalar
   domain is `0 <= eta <= Dop`; the downstream literal quotient additionally
   needs `Dop != 0`.  The boundary below discloses the degenerate
   `eta = Dop = 0` correction without asserting a quotient witness. -/
def theorem_4_5_sourceDomain (Dop η : ℝ) : Prop :=
  0 ≤ η ∧ η ≤ Dop

def theorem_4_5_formulaCorrectionNeeded {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T : ℕ) (L Dop η : ℝ) : Prop :=
  theorem_4_5_sourceDomain Dop η ∧
    ¬ theorem_4_5_rhsDomain P cfg T L Dop η

def theorem_4_5_formulaSourceBoundary {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T : ℕ) (L Dop η : ℝ) : Prop :=
  SourceScalarDomainBoundary (theorem_4_5_sourceDomain Dop η)
    (theorem_4_5_rhsDomain P cfg T L Dop η)
    (theorem_4_5_formulaCorrectionNeeded P cfg T L Dop η)

theorem theorem_4_5_formula_source_boundary {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T : ℕ) (L Dop η : ℝ) :
    theorem_4_5_formulaSourceBoundary P cfg T L Dop η := by
  constructor
  · exact fun hdom => hdom.2
  · intro hsource
    by_cases hdom : theorem_4_5_rhsDomain P cfg T L Dop η
    · exact Or.inl hdom
    · exact Or.inr ⟨hsource, hdom⟩

/- Appendix C.3 uses a nonnegative constant stepsize bounded by the operator
   radius.  The literal quotient additionally needs `Dop != 0`; the boundary
   records the zero-radius correction rather than inventing that witness. -/
def theorem_4_9_sourceDomain (Dop η : ℝ) : Prop :=
  0 ≤ η ∧ η ≤ Dop

def theorem_4_9_formulaCorrectionNeeded {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T : ℕ) (Lstar Dop η : ℝ) : Prop :=
  theorem_4_9_sourceDomain Dop η ∧
    ¬ theorem_4_9_rhsDomain P cfg T Lstar Dop η

def theorem_4_9_formulaSourceBoundary {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T : ℕ) (Lstar Dop η : ℝ) : Prop :=
  SourceScalarDomainBoundary (theorem_4_9_sourceDomain Dop η)
    (theorem_4_9_rhsDomain P cfg T Lstar Dop η)
    (theorem_4_9_formulaCorrectionNeeded P cfg T Lstar Dop η)

theorem theorem_4_9_formula_source_boundary {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T : ℕ) (Lstar Dop η : ℝ) :
    theorem_4_9_formulaSourceBoundary P cfg T Lstar Dop η := by
  constructor
  · exact fun hdom => hdom.2
  · intro hsource
    by_cases hdom : theorem_4_9_rhsDomain P cfg T Lstar Dop η
    · exact Or.inl hdom
    · exact Or.inr ⟨hsource, hdom⟩

private def theorem_4_9_preCorrectionRhsDomain (Dop η : ℝ) : Prop :=
  sourceQuotDomain η Dop

/- One-dimensional certificate for the C.3 formula boundary, distinct from
   the old negative-smoothness object-model certificate above.  The former
   quotient-only guard accepts `eta = -1`, even for a valid nonnegative
   spectral smoothness constant, and makes the printed bound false at T = 0. -/
private theorem theorem_4_9_preCorrection_negative_eta_counterexample :
    ∃ (P : Objective 1 1) (cfg : DeterministicMuonConfig 1 1)
      (Wstar : Mat 1 1) (hfinite : P.HasFiniteInfimum),
      StarConvex P Wstar ∧
      SpectralSmooth P 1 ∧
      BoundedOperatorDistance P cfg 0 Wstar 1 ∧
      (∀ t ∈ Finset.range 0, cfg.eta t = (-1 : ℝ)) ∧
      theorem_4_9_preCorrectionRhsDomain 1 (-1) ∧
      sourceObjectiveGapAt P cfg 0 hfinite = 0 ∧
      theorem_4_9_sourceRhs P cfg 0 1 1 (-1) = -(1 : ℝ) / 2 ∧
      ¬ sourceObjectiveGapAt P cfg 0 hfinite ≤
        theorem_4_9_sourceRhs P cfg 0 1 1 (-1) := by
  let P : Objective 1 1 := ⟨fun _ => 0⟩
  let cfg : DeterministicMuonConfig 1 1 :=
    { W0 := 0
      eta := fun _ => -1 }
  have hfinite : P.HasFiniteInfimum := by
    refine ⟨0, ?_⟩
    rintro y ⟨W, rfl⟩
    simp [P]
  have hfstar : P.fStar = 0 := by
    apply le_antisymm
    · exact csInf_le hfinite ⟨0, by simp [P]⟩
    · apply le_csInf
      · exact Set.range_nonempty _
      · rintro y ⟨W, rfl⟩
        simp [P]
  have hgrad (W : Mat 1 1) : P.grad W = 0 := by
    ext i j
    rw [Objective.grad_eq_coordinate_fderiv]
    change fderiv ℝ (fun _ : Mat 1 1 => (0 : ℝ)) W (coordinateMatrix i j) = 0
    simp
  have hstar : StarConvex P 0 := by
    constructor
    · change P.f 0 = P.fStar
      rw [hfstar]
    · intro W
      rw [hfstar]
      rw [hgrad]
      simp [P, frobeniusInner]
  have hsmooth : SpectralSmooth P 1 := by
    refine ⟨by norm_num, ?_, ?_⟩
    · dsimp [vectorizedObjective, P]
      exact contDiff_const
    · intro W W'
      rw [hgrad, hgrad]
      rw [sub_self]
      have hzero : nuclearNorm (0 : Mat 1 1) = 0 := by
        simp [nuclearNorm]
      rw [hzero, one_mul]
      exact (show 0 ≤ spectralNorm (W - W') by
        unfold spectralNorm
        exact norm_nonneg _)
  have hbounded : BoundedOperatorDistance P cfg 0 0 1 := by
    intro k hk
    have hk0 : k = 0 := by simpa using hk
    subst k
    change spectralNorm (cfg.W0 - 0) ≤ 1
    simp [cfg, spectralNorm]
  have hgap : sourceObjectiveGapAt P cfg 0 hfinite = 0 := by
    simp [sourceObjectiveGapAt, Objective.sourceFStar, hfstar, P, cfg]
  have hrhs : theorem_4_9_sourceRhs P cfg 0 1 1 (-1) = -(1 : ℝ) / 2 := by
    norm_num [theorem_4_9_sourceRhs, hfstar, P, cfg]
  refine ⟨P, cfg, 0, hfinite, hstar, hsmooth, hbounded, ?_, ?_, hgap, hrhs, ?_⟩
  · simp
  · norm_num [theorem_4_9_preCorrectionRhsDomain, sourceQuotDomain]
  · rw [hgap, hrhs]
    norm_num

def theorem_4_5_precisionConclusion {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (Wstar : Mat m n) (L Dop Δ : ℝ) (hfinite : P.HasFiniteInfimum) : Prop :=
  SourceObjectivePrecisionComplexityUnderOn P hfinite
    (theorem_4_5_precisionDomain m n L Dop Δ)
    (fun ε hε => theorem_4_5_precisionConfig cfg L Dop Δ ε hε)
    (fun ε hε N =>
      StarConvex P Wstar ∧ FrobeniusSmooth P L ∧
        theorem_4_5_precisionRunAt P cfg Wstar L Dop Δ ε hε N)
    (fun ε hε => theorem_4_5_complexityRateRealized m n L Dop Δ ε hε)
    (theoremScope "Theorem 4.5 precision complexity" ["epsilon"])

def theorem_4_6_precisionConclusion {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (Wstar : Mat m n) (L Dop : ℝ) (hfinite : P.HasFiniteInfimum) : Prop :=
  SourceObjectivePrecisionComplexityUnderOn P hfinite epsilonDomain
    (fun _ε _hε => cfg)
    (fun _ε _hε N =>
      StarConvex P Wstar ∧ FrobeniusSmooth P L ∧
        theorem_4_6_precisionRunAt P cfg Wstar L Dop N)
    (fun ε hε => theorem_4_6_complexityRateRealized m n L Dop ε hε)
    (theoremScope "Theorem 4.6 precision complexity" ["epsilon"])

def theorem_4_9_precisionConclusion {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (Wstar : Mat m n) (Lstar Dop Δ : ℝ)
    (hfinite : P.HasFiniteInfimum) : Prop :=
  SourceObjectivePrecisionComplexityUnderOn P hfinite
    (theorem_4_9_precisionDomain m n Lstar Dop Δ)
    (fun ε hε => theorem_4_9_precisionConfig cfg Lstar Dop Δ ε hε)
    (fun ε hε N =>
      StarConvex P Wstar ∧ SpectralSmooth P Lstar ∧
        theorem_4_9_precisionRunAt P cfg Wstar Lstar Dop Δ ε hε N)
    (fun ε hε => theorem_4_9_complexityRateRealized m n Lstar Dop Δ ε hε)
    (theoremScope "Theorem 4.9 precision complexity" ["epsilon"])

def theorem_4_10_precisionConclusion {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (Wstar : Mat m n) (Lstar Dop : ℝ) (hfinite : P.HasFiniteInfimum) : Prop :=
  SourceObjectivePrecisionComplexityUnderOn P hfinite epsilonDomain
    (fun _ε _hε => cfg)
    (fun _ε _hε N =>
      StarConvex P Wstar ∧ SpectralSmooth P Lstar ∧
        theorem_4_10_precisionRunAt P cfg Wstar Lstar Dop N)
    (fun ε hε => theorem_4_10_complexityRateRealized m n Lstar Dop ε hε)
    (theoremScope "Theorem 4.10 precision complexity" ["epsilon"])

def theorem_4_5_statement {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T : ℕ) (Wstar : Mat m n) (L Dop η : ℝ)
    (hfinite : P.HasFiniteInfimum) : Prop :=
  let Δ := sourceObjectiveInitialGap P cfg.W0 hfinite
  theorem_4_5_formulaSourceBoundary P cfg T L Dop η ∧
    (theorem_4_5_rhsDomain P cfg T L Dop η →
      sourceObjectiveGapAt P cfg T hfinite ≤
        theorem_4_5_sourceRhs P cfg T L Dop η) ∧
    AsymptoticUpperRealOn (theorem_4_5_precisionDomain m n L Dop Δ)
      (fun ε hε => theorem_4_5_etaRateRealized m n L Dop ε hε.2.1)
      (fun ε hε => theorem_4_5_etaRateRealized m n L Dop ε hε.2.1)
      (theoremScope "Theorem 4.5 eta=O(epsilon/(rLDop))" ["epsilon"]) ∧
    ((∀ ε : ℝ, ∀ hε : theorem_4_5_precisionDomain m n L Dop Δ ε,
        theorem_4_5_precisionRunAt P cfg Wstar L Dop Δ ε hε
          (theorem_4_5_logHorizon m n L Dop Δ ε hε)) →
      theorem_4_5_precisionConclusion P cfg Wstar L Dop Δ hfinite)

def theorem_4_6_statement {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (t : ℕ) (Wstar : Mat m n) (L Dop : ℝ)
    (hfinite : P.HasFiniteInfimum) : Prop :=
  (∀ hdom : theorem_4_6_rhsDomain P cfg t L Dop,
    sourceObjectiveGapAt P cfg t hfinite ≤ theorem_4_6_rhs P cfg t L Dop hdom) ∧
    ((∀ ε : ℝ, ∀ hε : epsilonDomain ε,
        theorem_4_6_precisionRunAt P cfg Wstar L Dop
          (theorem_4_6_selectedHorizon m n L Dop ε hε)) →
      theorem_4_6_precisionConclusion P cfg Wstar L Dop hfinite)

def theorem_4_9_statement {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T : ℕ) (Wstar : Mat m n) (Lstar Dop η : ℝ)
    (hfinite : P.HasFiniteInfimum) : Prop :=
  let Δ := sourceObjectiveInitialGap P cfg.W0 hfinite
  theorem_4_9_formulaSourceBoundary P cfg T Lstar Dop η ∧
    (theorem_4_9_rhsDomain P cfg T Lstar Dop η →
      sourceObjectiveGapAt P cfg T hfinite ≤
        theorem_4_9_sourceRhs P cfg T Lstar Dop η) ∧
    AsymptoticUpperRealOn (theorem_4_9_precisionDomain m n Lstar Dop Δ)
      (fun ε hε => theorem_4_9_etaRateRealized m n Lstar Dop ε hε.2.1)
      (fun ε hε => theorem_4_9_etaRateRealized m n Lstar Dop ε hε.2.1)
      (theoremScope "Theorem 4.9 eta=O(epsilon/(Lstar Dop))" ["epsilon"]) ∧
    ((∀ ε : ℝ, ∀ hε : theorem_4_9_precisionDomain m n Lstar Dop Δ ε,
        theorem_4_9_precisionRunAt P cfg Wstar Lstar Dop Δ ε hε
          (theorem_4_9_logHorizon m n Lstar Dop Δ ε hε)) →
      theorem_4_9_precisionConclusion P cfg Wstar Lstar Dop Δ hfinite)

def theorem_4_10_statement {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (t : ℕ) (Wstar : Mat m n) (Lstar Dop : ℝ)
    (hfinite : P.HasFiniteInfimum) : Prop :=
  (∀ hdom : theorem_4_10_rhsDomain P cfg t Lstar Dop,
    sourceObjectiveGapAt P cfg t hfinite ≤ theorem_4_10_rhs P cfg t Lstar Dop hdom) ∧
    ((∀ ε : ℝ, ∀ hε : epsilonDomain ε,
        theorem_4_10_precisionRunAt P cfg Wstar Lstar Dop
          (theorem_4_10_selectedHorizon m n Lstar Dop ε hε)) →
      theorem_4_10_precisionConclusion P cfg Wstar Lstar Dop hfinite)

/- Source-derived rate payloads for the Appendix B.3 discussion.  The
   registered Theorem 4.14 statement is the finite-horizon inequality below;
   the two displayed rate/complexity discussions are separate source-facing
   conditional propositions.  Their pointwise and horizon-family premises are
   kept explicit rather than being promoted to Assumption 4.13 or the
   finite-horizon theorem head. -/
def theorem_4_14_branchRateDomain (m n T : ℕ) (J s Δ : ℝ) : Prop :=
  horizonDomain T ∧
    sourceSqrtQuotDomain (J * Δ) (T : ℝ) ∧
    sourceQuotDomain
      (s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Δ) (J * (T : ℝ))

def theorem_4_14_branchRate {m n : ℕ}
    (_P : Objective m n) (_cfg : DeterministicMuonConfig m n) (J s Δ : ℝ) (T : ℕ)
    (hdom : theorem_4_14_branchRateDomain m n T J s Δ) : ℝ :=
  realizedSourceSqrtQuot (J * Δ) (T : ℝ) hdom.2.1 +
    realizedSourceQuot
      (s * realizedSourceSqrt ((matrixRankBound m n : ℝ) ^ 3)
        (rankCube_sourceSqrtDomain m n) * Δ)
      (J * (T : ℝ)) hdom.2.2

def theorem_4_14_sourceBranchRate (m n : ℕ) (J s Δ : ℝ) (T : ℕ) : ℝ :=
  Real.sqrt ((J * Δ) / (T : ℝ)) +
    s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Δ / (J * (T : ℝ))

def theorem_4_14_otherwiseBranchRateDomain
    (m n : ℕ) (s Δ : ℝ) (T : ℕ) : Prop :=
  horizonDomain T ∧
    sourceRpowDomain Δ ((2 : ℝ) / 3) ∧
    sourceRpowDomain s ((1 : ℝ) / 3) ∧
    sourceSqrtDomain (matrixRankBound m n : ℝ) ∧
    sourceRpowDomain (T : ℝ) ((2 : ℝ) / 3) ∧
    sourceQuotDomain
      (sourceRpow Δ ((2 : ℝ) / 3) * sourceRpow s ((1 : ℝ) / 3) *
        sourceSqrt (matrixRankBound m n : ℝ))
      (sourceRpow (T : ℝ) ((2 : ℝ) / 3))

def theorem_4_14_otherwiseBranchRate (m n : ℕ) (s Δ : ℝ) (T : ℕ)
    (hdom : theorem_4_14_otherwiseBranchRateDomain m n s Δ T) : ℝ :=
  let ⟨_hT, hΔ, hs, hr, hTpow, hq⟩ := hdom
  realizedSourceQuot
    (realizedSourceRpow Δ ((2 : ℝ) / 3) hΔ *
      realizedSourceRpow s ((1 : ℝ) / 3) hs *
        realizedSourceSqrt (matrixRankBound m n : ℝ) hr)
    (realizedSourceRpow (T : ℝ) ((2 : ℝ) / 3) hTpow)
    hq

def theorem_4_16_branchRate (_m _n : ℕ) (Jtilde Dop : ℝ) (T : ℕ) : ℝ :=
  Dop ^ 2 * Jtilde / (T : ℝ)

def theorem_4_16_branchRateDomain (_m _n : ℕ) (_Jtilde _Dop : ℝ) (T : ℕ) : Prop :=
  horizonDomain T

def theorem_4_16_branchRateRealized (m n : ℕ) (Jtilde Dop : ℝ) (T : ℕ)
    (hdom : theorem_4_16_branchRateDomain m n Jtilde Dop T) : ℝ :=
  realizedSourceQuot (Dop ^ 2 * Jtilde) (T : ℝ)
    (by
      unfold theorem_4_16_branchRateDomain horizonDomain at hdom
      unfold sourceQuotDomain
      exact_mod_cast (Nat.ne_of_gt hdom))

def theorem_4_16_otherwiseBranchRate (m n : ℕ) (s Dop : ℝ) (T : ℕ) : ℝ :=
  s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Dop ^ 3 / (T : ℝ) ^ 2

def theorem_4_16_otherwiseBranchRateDomain (_m _n : ℕ) (_s _Dop : ℝ) (T : ℕ) : Prop :=
  horizonDomain T

def theorem_4_16_otherwiseBranchRateRealized (m n : ℕ) (s Dop : ℝ) (T : ℕ)
    (hdom : theorem_4_16_otherwiseBranchRateDomain m n s Dop T) : ℝ :=
  realizedSourceQuot
    (s * realizedSourceSqrt ((matrixRankBound m n : ℝ) ^ 3)
      (rankCube_sourceSqrtDomain m n) * Dop ^ 3)
    ((T : ℝ) ^ 2)
    (by
      unfold theorem_4_16_otherwiseBranchRateDomain horizonDomain at hdom
      unfold sourceQuotDomain
      have hT : (T : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hdom)
      exact pow_ne_zero 2 hT)

def theorem_4_14_complexityRate (_m _n : ℕ) (J Δ ε : ℝ) : ℝ :=
  J * Δ * ε⁻¹ ^ 2

def theorem_4_15_complexityRate (m n : ℕ) (Jstar σ Δ ε : ℝ) : ℝ :=
  (matrixRankBound m n : ℝ) * Jstar * σ ^ 2 * Δ * ε⁻¹ ^ 4

def theorem_4_14_otherwiseComplexityRate (m n : ℕ) (s Δ ε : ℝ) : ℝ :=
  Real.sqrt s * Real.sqrt (Real.sqrt ((matrixRankBound m n : ℝ) ^ 3)) *
    Δ * Real.rpow ε (-(3 : ℝ) / 2)

def theorem_4_15_otherwiseComplexityRate (m n : ℕ) (σ ε : ℝ) : ℝ :=
  σ ^ 3 * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * ε⁻¹ ^ 3

def theorem_4_16_complexityRate (_m _n : ℕ) (Jtilde Dop ε : ℝ) : ℝ :=
  Jtilde * Dop ^ 2 * ε⁻¹

def theorem_4_16_otherwiseComplexityRate (m n : ℕ) (s Dop ε : ℝ) : ℝ :=
  Real.sqrt s * Real.sqrt (Real.sqrt ((matrixRankBound m n : ℝ) ^ 3)) *
    Real.sqrt (Dop ^ 3) * Real.sqrt ε⁻¹

def theorem_4_15_remainderRate (m n : ℕ) (cfg : StochasticMuonConfig m n)
    (s η : ℝ) : ℝ :=
  realizedSourceQuot
    (s * realizedSourceSqrt ((matrixRankBound m n : ℝ) ^ 3)
      (rankCube_sourceSqrtDomain m n) * η ^ 2)
    (1 - cfg.beta)
    (stochasticMuonConfig_one_sub_beta_sourceQuotDomain cfg
      (s * realizedSourceSqrt ((matrixRankBound m n : ℝ) ^ 3)
        (rankCube_sourceSqrtDomain m n) * η ^ 2))

def theorem_4_15_positiveBranchRateDomain
    (m n T : ℕ) (Jstar σ Δ s : ℝ) : Prop :=
  horizonDomain T ∧
    sourceSqrtQuotDomain ((matrixRankBound m n : ℝ) * Jstar * Δ * σ ^ 2) (T : ℝ) ∧
    sourceSqrtQuotDomain (Jstar * Δ) (T : ℝ) ∧
    sourceSqrtDomain (Jstar * Δ * (T : ℝ)) ∧
    sourceQuotDomain ((matrixRankBound m n : ℝ) * σ ^ 2)
      (Real.sqrt (Jstar * Δ * (T : ℝ))) ∧
    sourceSqrtDomain ((matrixRankBound m n : ℝ) ^ 3) ∧
    sourceQuotDomain (s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Δ)
      (Jstar * (T : ℝ))

def theorem_4_15_branchRate (m n : ℕ) (Jstar σ Δ s : ℝ) (T : ℕ)
    (hdom : theorem_4_15_positiveBranchRateDomain m n T Jstar σ Δ s) : ℝ :=
  let r : ℝ := matrixRankBound m n
  let ⟨_hT, hFirst, hSecond, hThirdSqrt, hThirdQuot, hRankCube, hCurvature⟩ := hdom
  realizedSourceSqrt (realizedSourceSqrtQuot (r * Jstar * Δ * σ ^ 2) (T : ℝ) hFirst)
      (Real.sqrt_nonneg _) +
    realizedSourceSqrtQuot (Jstar * Δ) (T : ℝ) hSecond +
      realizedSourceQuot (r * σ ^ 2)
        (realizedSourceSqrt (Jstar * Δ * (T : ℝ)) hThirdSqrt) hThirdQuot +
        realizedSourceQuot (s * realizedSourceSqrt (r ^ 3) hRankCube * Δ)
          (Jstar * (T : ℝ)) hCurvature

def theorem_4_15_sourceBranchRate (m n : ℕ) (Jstar σ Δ s : ℝ) (T : ℕ) : ℝ :=
  let r : ℝ := matrixRankBound m n
  Real.sqrt (Real.sqrt ((r * Jstar * Δ * σ ^ 2) / (T : ℝ))) +
    Real.sqrt ((Jstar * Δ) / (T : ℝ)) +
      r * σ ^ 2 / Real.sqrt (Jstar * Δ * (T : ℝ)) +
        s * Real.sqrt (r ^ 3) * Δ / (Jstar * (T : ℝ))

def theorem_4_15_positiveBranchScheduleDomain
    (m n T : ℕ) (Jstar σ Δ s : ℝ) : Prop :=
  horizonDomain T ∧
    sourceSqrtDomain (Jstar * Δ) ∧
    sourceSqrtDomain ((matrixRankBound m n : ℝ) * (T : ℝ)) ∧
    sourceQuotDomain (Real.sqrt (Jstar * Δ))
      (σ * Real.sqrt ((matrixRankBound m n : ℝ) * (T : ℝ))) ∧
    sourceSqrtQuotDomain
      (min (sourceQuot (Real.sqrt (Jstar * Δ))
        (σ * Real.sqrt ((matrixRankBound m n : ℝ) * (T : ℝ)))) 1 * Δ)
      ((T : ℝ) * Jstar) ∧
    theorem_4_15_positiveBranchRateDomain m n T Jstar σ Δ s

def theorem_4_15_otherwiseBranchScheduleDomain
    (m n T : ℕ) (σ Δ ε : ℝ) : Prop :=
  horizonDomain T ∧
    sourceQuotDomain (ε ^ 2) ((matrixRankBound m n : ℝ) * σ ^ 2) ∧
    sourceSqrtDomain ((matrixRankBound m n : ℝ) ^ 3) ∧
    sourceQuotDomain
      (Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Δ * ε ^ 2)
      (σ ^ 3)

def theorem_4_14_positiveBranchEtaRate (J Δ : ℝ) (T : ℕ) : ℝ :=
  Real.sqrt (sourceQuot Δ (J * (T : ℝ)))

def theorem_4_14_otherwiseBranchEtaDomain
    (m n : ℕ) (s Δ : ℝ) (T : ℕ) : Prop :=
  horizonDomain T ∧
    sourceSqrtDomain ((matrixRankBound m n : ℝ) ^ 3) ∧
    sourceQuotDomain Δ
      (s * sourceSqrt ((matrixRankBound m n : ℝ) ^ 3) * (T : ℝ)) ∧
    sourceRpowDomain
      (sourceQuot Δ
        (s * sourceSqrt ((matrixRankBound m n : ℝ) ^ 3) * (T : ℝ)))
      ((1 : ℝ) / 3)

def theorem_4_14_otherwiseBranchEtaRate (m n : ℕ) (s Δ : ℝ) (T : ℕ)
    (hdom : theorem_4_14_otherwiseBranchEtaDomain m n s Δ T) : ℝ :=
  let ⟨_hT, hsRankCube, hq, hp⟩ := hdom
  realizedSourceRpow
    (realizedSourceQuot Δ
      (s * realizedSourceSqrt ((matrixRankBound m n : ℝ) ^ 3) hsRankCube * (T : ℝ))
      hq)
    ((1 : ℝ) / 3)
    hp

def theorem_4_14_positiveBranchSchedule {m n : ℕ}
    (cfg : DeterministicMuonConfig m n) (J Δ : ℝ) : Prop :=
  AsymptoticThetaNat horizonDomain
    (fun T => cfg.eta T) (theorem_4_14_positiveBranchEtaRate J Δ)
    (theoremScope "Theorem 4.14 eta=Theta(sqrt(Delta/(J T)))" ["T"])

def theorem_4_14_otherwiseBranchSchedule {m n : ℕ}
    (cfg : DeterministicMuonConfig m n) (s Δ : ℝ) : Prop :=
  DomainAsymptoticThetaNatOn
    (fun T => theorem_4_14_otherwiseBranchEtaDomain m n s Δ T)
    (fun T _hT => cfg.eta T)
    (fun T hT => theorem_4_14_otherwiseBranchEtaRate m n s Δ T hT)
    (theoremScope "Theorem 4.14 otherwise eta=Theta((Delta/(s r^(3/2) T))^(1/3))" ["T"])

def theorem_4_14_positiveHorizonSchedule {m n : ℕ}
    (P : Objective m n) (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (W0 : Mat m n) (Δ : ℝ) : Prop :=
  ∀ N : ℕ, horizonDomain N →
    let cfgN := cfgForHorizon N
    cfgN.W0 = W0 ∧
      ∀ t ∈ Finset.range N,
        cfgN.eta t =
          theorem_4_14_positiveBranchEtaRate (hessianDirectionalAverage P cfgN N) Δ N

/- The source complexity discussion uses one displayed run-average J.  A
   horizon family needs an explicit envelope before that scalar can be used
   uniformly in a rate. -/
def theorem_4_14_fixedJ_positiveBranchRegime
    {m n : ℕ} (J s : ℝ) : Prop :=
  let fixedJ := J
  let rankTerm :=
    Real.sqrt (Real.sqrt ((matrixRankBound m n : ℝ) ^ 3))
  AsymptoticLowerReal epsilonDomain
    (fun _ => fixedJ)
    (fun ε => Real.sqrt (s * ε) * rankTerm)
    (theoremScope "Theorem 4.14 fixed-J lower branch" ["epsilon"])

def theorem_4_14_fixedJ_positiveHorizonSchedule {m n : ℕ}
    (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (W0 : Mat m n) (J Δ : ℝ) : Prop :=
  ∀ N : ℕ, horizonDomain N →
    let cfgN := cfgForHorizon N
    let etaJ := theorem_4_14_positiveBranchEtaRate J Δ N
    cfgN.W0 = W0 ∧
      ∀ t ∈ Finset.range N,
        cfgN.eta t = etaJ

def theorem_4_14_fixedJ_positiveRunForHorizon {m n : ℕ}
    (P : Objective m n)
    (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (W0 : Mat m n) (J s Δ : ℝ) (N : ℕ) : Prop :=
  horizonDomain N ∧
    let cfgN := cfgForHorizon N
    let etaJ := theorem_4_14_positiveBranchEtaRate J Δ N
    let hRegime :=
      theorem_4_14_fixedJ_positiveBranchRegime (m := m) (n := n) J s
    cfgN.W0 = W0 ∧
    hessianDirectionalAverage P cfgN N ≤ J ∧
    theorem_4_14_branchRateDomain m n N J s Δ ∧
    theorem_4_14_rhsDomain P cfgN N
      (hessianDirectionalAverage P cfgN N) s etaJ ∧
    (∀ t ∈ Finset.range N,
      cfgN.eta t = etaJ) ∧
    hRegime

theorem theorem_4_14_fixedJ_positive_branch_domain_obligation
    {m n : ℕ}
    (P : Objective m n)
    (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (W0 : Mat m n) (J s Δ : ℝ) (N : ℕ)
    (_hrun : theorem_4_14_fixedJ_positiveRunForHorizon
      P cfgForHorizon W0 J s Δ N) :
    theorem_4_14_branchRateDomain m n N J s Δ := by
  unfold theorem_4_14_fixedJ_positiveRunForHorizon at _hrun
  dsimp at _hrun
  rcases _hrun with
    ⟨_hN, _hW0, _hEnvelope, hBranchDomain, _hRhsDomain, _hSchedule, _hRegime⟩
  exact hBranchDomain

theorem theorem_4_14_fixedJ_positive_rhs_domain_obligation
    {m n : ℕ}
    (P : Objective m n)
    (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (W0 : Mat m n) (J s Δ : ℝ) (N : ℕ)
    (_hrun : theorem_4_14_fixedJ_positiveRunForHorizon
      P cfgForHorizon W0 J s Δ N) :
    theorem_4_14_rhsDomain P (cfgForHorizon N) N
      (hessianDirectionalAverage P (cfgForHorizon N) N) s
        (theorem_4_14_positiveBranchEtaRate J Δ N) := by
  unfold theorem_4_14_fixedJ_positiveRunForHorizon at _hrun
  dsimp at _hrun
  rcases _hrun with
    ⟨_hN, _hW0, _hEnvelope, _hBranchDomain, hRhsDomain, _hSchedule, _hRegime⟩
  exact hRhsDomain

def theorem_4_14_positiveBranchRegime {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (T : ℕ) (s : ℝ) : Prop :=
  AsymptoticLowerReal epsilonDomain
    (fun _ => hessianDirectionalAverage P cfg T)
    (fun ε => Real.sqrt (s * ε) * Real.sqrt (Real.sqrt ((matrixRankBound m n : ℝ) ^ 3)))
    (theoremScope "Theorem 4.14 J lower branch" ["epsilon"])

def theorem_4_14_positiveRunForHorizon {m n : ℕ}
    (P : Objective m n) (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (W0 : Mat m n) (s Δ : ℝ) (N : ℕ) : Prop :=
  horizonDomain N ∧
    let cfgN := cfgForHorizon N
    cfgN.W0 = W0 ∧
      theorem_4_14_branchRateDomain m n N
        (hessianDirectionalAverage P cfgN N) s Δ ∧
      (∀ t ∈ Finset.range N,
        cfgN.eta t =
          theorem_4_14_positiveBranchEtaRate (hessianDirectionalAverage P cfgN N) Δ N) ∧
      theorem_4_14_positiveBranchRegime P cfgN N s

def theorem_4_14_otherwiseHorizonSchedule {m n : ℕ}
    (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (W0 : Mat m n) (s Δ : ℝ) : Prop :=
  ∀ N : ℕ, horizonDomain N →
    let cfgN := cfgForHorizon N
    cfgN.W0 = W0 ∧
      ∃ hetaDom : theorem_4_14_otherwiseBranchEtaDomain m n s Δ N,
      ∀ t ∈ Finset.range N,
        cfgN.eta t = theorem_4_14_otherwiseBranchEtaRate m n s Δ N hetaDom

def theorem_4_14_otherwiseBranchRegime {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n) (T : ℕ)
    (s ε C : ℝ) : Prop :=
  epsilonDomain ε ∧
    0 < C ∧
      hessianDirectionalAverage P cfg T ≤
        C * (Real.sqrt (s * ε) *
          Real.sqrt (Real.sqrt ((matrixRankBound m n : ℝ) ^ 3)))

def theorem_4_14_otherwiseRunForHorizon {m n : ℕ}
    (P : Objective m n) (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (W0 : Mat m n) (s Δ ε C : ℝ) (N : ℕ) : Prop :=
  horizonDomain N ∧
    let cfgN := cfgForHorizon N
    cfgN.W0 = W0 ∧
      (∃ hetaDom : theorem_4_14_otherwiseBranchEtaDomain m n s Δ N,
      (∀ t ∈ Finset.range N,
        cfgN.eta t = theorem_4_14_otherwiseBranchEtaRate m n s Δ N hetaDom)) ∧
      theorem_4_14_otherwiseBranchRateDomain m n s Δ N ∧
      theorem_4_14_otherwiseBranchRegime P cfgN N s ε C

def theorem_4_14_otherwiseHorizonScheduleForAccuracy {m n : ℕ}
    (cfgForAccuracyHorizon : ℝ → ℕ → DeterministicMuonConfig m n)
    (W0 : Mat m n) (s Δ : ℝ) : Prop :=
  ∀ ε : ℝ, epsilonDomain ε →
    theorem_4_14_otherwiseHorizonSchedule
      (fun N => cfgForAccuracyHorizon ε N) W0 s Δ

def theorem_4_14_otherwiseRunForAccuracyHorizon {m n : ℕ}
    (P : Objective m n)
    (cfgForAccuracyHorizon : ℝ → ℕ → DeterministicMuonConfig m n)
    (W0 : Mat m n) (s Δ ε C : ℝ) (N : ℕ) : Prop :=
  horizonDomain N ∧
    let cfgN := cfgForAccuracyHorizon ε N
    cfgN.W0 = W0 ∧
      (∃ hetaDom : theorem_4_14_otherwiseBranchEtaDomain m n s Δ N,
      (∀ t ∈ Finset.range N,
        cfgN.eta t = theorem_4_14_otherwiseBranchEtaRate m n s Δ N hetaDom)) ∧
      theorem_4_14_otherwiseBranchRateDomain m n s Δ N ∧
      theorem_4_14_otherwiseBranchRegime P cfgN N s ε C

def theorem_4_14_otherwiseSourceRunForAccuracyHorizon {m n : ℕ}
    (P : Objective m n)
    (cfgForAccuracyHorizon : ℝ → ℕ → DeterministicMuonConfig m n)
    (W0 : Mat m n) (s Δ ε C : ℝ) (N : ℕ) : Prop :=
  theorem_4_14_otherwiseRunForAccuracyHorizon
      P cfgForAccuracyHorizon W0 s Δ ε C N

theorem theorem_4_14_otherwiseBranchEta_sourceDomain
    {m n : ℕ} {s Δ : ℝ} {N : ℕ}
    (hetaDom : theorem_4_14_otherwiseBranchEtaDomain m n s Δ N) :
    sourceHorizonEtaQuotDomain N
        (theorem_4_14_otherwiseBranchEtaRate m n s Δ N hetaDom) ∧
      0 < theorem_4_14_otherwiseBranchEtaRate m n s Δ N hetaDom := by
  rcases hetaDom with ⟨hN, hsRankCube, hq, hp⟩
  have hbase :
      0 <
        realizedSourceQuot Δ
          (s * realizedSourceSqrt ((matrixRankBound m n : ℝ) ^ 3) hsRankCube *
            (N : ℝ)) hq := by
    simpa [sourceRpowDomain, sourceQuot, sourceSqrt,
      realizedSourceQuot, realizedSourceSqrt] using hp
  have hηpos :
      0 <
        realizedSourceRpow
          (realizedSourceQuot Δ
            (s * realizedSourceSqrt ((matrixRankBound m n : ℝ) ^ 3) hsRankCube *
              (N : ℝ)) hq)
          ((1 : ℝ) / 3) hp :=
    Real.rpow_pos_of_pos hbase _
  have hηpos' :
      0 < theorem_4_14_otherwiseBranchEtaRate m n s Δ N
        ⟨hN, hsRankCube, hq, hp⟩ := by
    simpa [theorem_4_14_otherwiseBranchEtaRate] using hηpos
  refine ⟨⟨hN, ?_⟩, ?_⟩
  · exact mul_ne_zero (by exact_mod_cast (Nat.ne_of_gt hN)) (ne_of_gt hηpos')
  · simpa using hηpos'

def theorem_4_14_positiveBranchPointwiseCondition
    (m n : ℕ) (J s ε : ℝ) : Prop :=
  epsilonDomain ε ∧
    sourceSqrtDomain (s * ε) ∧
    sourceSqrtDomain ((matrixRankBound m n : ℝ) ^ 3) ∧
    ∃ c : ℝ, 0 < c ∧
      c * (Real.sqrt (s * ε) *
        Real.sqrt (Real.sqrt ((matrixRankBound m n : ℝ) ^ 3))) ≤ J

def theorem_4_14_positiveBranchPointwisePremise
    (m n : ℕ) (J s : ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ ε : ℝ, epsilonDomain ε → ε ≤ ε₀ →
      theorem_4_14_positiveBranchPointwiseCondition m n J s ε

def theorem_4_14_positivePointwiseRunForHorizon {m n : ℕ}
    (P : Objective m n)
    (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (W0 : Mat m n) (J s Δ : ℝ) (N : ℕ) : Prop :=
  horizonDomain N ∧
    let cfgN := cfgForHorizon N
    let etaJ := theorem_4_14_positiveBranchEtaRate J Δ N
    cfgN.W0 = W0 ∧
    hessianDirectionalAverage P cfgN N ≤ J ∧
    theorem_4_14_branchRateDomain m n N J s Δ ∧
    theorem_4_14_rhsDomain P cfgN N
      (hessianDirectionalAverage P cfgN N) s etaJ ∧
    (∀ t ∈ Finset.range N, cfgN.eta t = etaJ)

def theorem_4_14_positive_branch_rate_and_complexity {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (s Δ J : ℝ)
    (cfgForHorizon : ℕ → DeterministicMuonConfig m n) : Prop :=
  DomainAsymptoticUpperNatOn
      (fun N => theorem_4_14_branchRateDomain m n N J s Δ)
      (fun N _hN => deterministicAverageNuclearGradient P (cfgForHorizon N) N)
      (fun N hN => theorem_4_14_branchRate P (cfgForHorizon N)
        J s Δ N hN)
      (theoremScope "Theorem 4.14 positive-J branch rate" ["T"]) ∧
    HorizonNuclearStationarityComplexityWithHorizonRate
      (fun N => deterministicAverageNuclearGradient P (cfgForHorizon N) N)
      (fun N => theorem_4_14_positivePointwiseRunForHorizon
        P cfgForHorizon cfg.W0 J s Δ N)
      (fun _N ε => theorem_4_14_complexityRate m n J Δ ε)
      (theoremScope "Theorem 4.14 positive-J epsilon complexity" ["epsilon"]) ∧
    GeneratedNuclearStationarityTransfer P
      (fun N => theorem_4_14_positivePointwiseRunForHorizon
        P cfgForHorizon cfg.W0 J s Δ N)
      (fun N _hN => deterministicAverageNuclearGradient P (cfgForHorizon N) N)
      (fun N _hN t => (deterministicMuonState P (cfgForHorizon N) t).W)

def theorem_4_14_otherwise_selected_horizon_relation
    (m n : ℕ) (s Δ ε : ℝ) (N : ℕ) : Prop :=
  Real.sqrt ε ≤
    Real.rpow Δ ((1 : ℝ) / 3) *
      Real.rpow s ((1 : ℝ) / 6) *
        Real.rpow (matrixRankBound m n : ℝ) ((1 : ℝ) / 4) /
      Real.rpow (N : ℝ) ((1 : ℝ) / 3)

def theorem_4_14_otherwise_branch_rate_and_complexity {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (s Δ C : ℝ)
    (cfgForAccuracyHorizon : ℝ → ℕ → DeterministicMuonConfig m n) : Prop :=
  ∃ K : ℝ, 0 < K ∧
    ((∃ ε₀ : ℝ, 0 < ε₀ ∧
        ∀ ε : ℝ, epsilonDomain ε → ε ≤ ε₀ →
          ∀ N : ℕ, horizonDomain N →
            theorem_4_14_otherwise_selected_horizon_relation
              m n s Δ ε N →
            theorem_4_14_otherwiseRunForAccuracyHorizon
              P cfgForAccuracyHorizon cfg.W0 s Δ ε C N →
              ∃ hdom : theorem_4_14_otherwiseBranchRateDomain m n s Δ N,
                deterministicAverageNuclearGradient
                    P (cfgForAccuracyHorizon ε N) N ≤
                  K * theorem_4_14_otherwiseBranchRate m n s Δ N hdom) ∧
      EpsilonHorizonNuclearStationarityComplexityWithHorizonRate
        (fun ε N => deterministicAverageNuclearGradient
          P (cfgForAccuracyHorizon ε N) N)
        (fun ε N => theorem_4_14_otherwiseRunForAccuracyHorizon
          P cfgForAccuracyHorizon cfg.W0 s Δ ε C N)
        (fun _N ε => K * theorem_4_14_otherwiseComplexityRate m n s Δ ε)
        (theoremScope "Theorem 4.14 otherwise epsilon complexity" ["epsilon"]) ∧
      ∀ ε : ℝ,
        GeneratedNuclearStationarityTransfer P
          (fun N => theorem_4_14_otherwiseRunForAccuracyHorizon
            P cfgForAccuracyHorizon cfg.W0 s Δ ε C N)
          (fun N _hN => deterministicAverageNuclearGradient
            P (cfgForAccuracyHorizon ε N) N)
          (fun N _hN t =>
            (deterministicMuonState P (cfgForAccuracyHorizon ε N) t).W))

/- The B.3 consequences are a separate horizon-family interface.  They are
   deliberately not indexed by the finite-horizon theorem's current `T` or
   `η`: the source discussion supplies its own schedules and admissible runs,
   while the public theorem above supplies only the fixed-horizon inequality. -/
def theorem_4_14_source_rate_consequences {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (s : ℝ) (hfinite : P.HasFiniteInfimum) : Prop :=
  let Δ := sourceObjectiveInitialGap P cfg.W0 hfinite
  (∀ hthird : ThirdDerivativeBounded P s,
    ∀ J : ℝ,
    theorem_4_14_positiveBranchPointwisePremise m n J s →
    ∀ cfgForHorizon : ℕ → DeterministicMuonConfig m n,
    (∀ N : ℕ, horizonDomain N →
      theorem_4_14_positivePointwiseRunForHorizon
        P cfgForHorizon cfg.W0 J s Δ N) →
    theorem_4_14_positive_branch_rate_and_complexity
      P cfg s Δ J cfgForHorizon) ∧
  (∀ hthird : ThirdDerivativeBounded P s,
    ∀ C : ℝ, 0 < C →
    ∀ cfgForAccuracyHorizon : ℝ → ℕ → DeterministicMuonConfig m n,
    theorem_4_14_otherwiseHorizonScheduleForAccuracy
      cfgForAccuracyHorizon cfg.W0 s Δ →
    (∀ ε : ℝ, epsilonDomain ε →
      ∀ N : ℕ, horizonDomain N →
        theorem_4_14_otherwiseSourceRunForAccuracyHorizon
        P cfgForAccuracyHorizon cfg.W0 s Δ ε C N) →
    theorem_4_14_otherwise_branch_rate_and_complexity
      P cfg s Δ C cfgForAccuracyHorizon)

def theorem_4_15_positiveBranchSchedule {m n : ℕ}
    (cfg : StochasticMuonConfig m n) (T : ℕ) (Jstar σ Δ s : ℝ) : Prop :=
  theorem_4_15_positiveBranchScheduleDomain m n T Jstar σ Δ s ∧
    cfg.batchSize.val = 1 ∧
    (∀ t ∈ Finset.range T,
      cfg.eta t =
        Real.sqrt (sourceQuot ((1 - cfg.beta) * Δ) ((T : ℝ) * Jstar))) ∧
    1 - cfg.beta =
      min (sourceQuot (Real.sqrt (Jstar * Δ))
        (σ * Real.sqrt ((matrixRankBound m n : ℝ) * (T : ℝ)))) 1

def theorem_4_15_otherwiseOneMinusBetaScale (m n : ℕ) (σ ε : ℝ) : ℝ :=
  sourceQuot (ε ^ 2) ((matrixRankBound m n : ℝ) * σ ^ 2)

def theorem_4_15_otherwiseEtaRate (m n : ℕ) (σ Δ ε : ℝ) (T : ℕ) : ℝ :=
  sourceQuot
    (Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Δ * ε ^ 2)
    (σ ^ 3)

theorem theorem_4_15_otherwiseEtaRate_eq_source_scale
    (m n : ℕ) (σ Δ ε : ℝ) (T : ℕ) :
    theorem_4_15_otherwiseEtaRate m n σ Δ ε T =
      sourceQuot
        (Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Δ * ε ^ 2)
        (σ ^ 3) :=
  rfl

/- At the selected Appendix B.4 horizon, `T * eta` retains a factor of `T`.
   This identity is the scalar substitution that was lost when the previous
   encoding incorrectly divided `eta` by the horizon. -/
theorem theorem_4_15_otherwise_horizon_eta_product
    (m n : ℕ) (σ Δ ε : ℝ) (T : ℕ)
    (hσ : σ ≠ 0) (hε : ε ≠ 0) :
    theorem_4_15_otherwiseComplexityRate m n σ ε *
        theorem_4_15_otherwiseEtaRate m n σ Δ ε T =
      Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) ^ 2 * Δ / ε := by
  unfold theorem_4_15_otherwiseComplexityRate theorem_4_15_otherwiseEtaRate sourceQuot
  field_simp [hσ, hε]

def theorem_4_15_uniformThetaAt
    (lower upper target actual : ℝ) : Prop :=
  0 < lower ∧ lower ≤ upper ∧
    lower * target ≤ actual ∧ actual ≤ upper * target

def theorem_4_15_otherwiseBranchSchedule {m n : ℕ}
    (cfg : StochasticMuonConfig m n) (T : ℕ) (σ Δ ε : ℝ)
    (betaLower betaUpper etaLower etaUpper : ℝ) : Prop :=
  theorem_4_15_otherwiseBranchScheduleDomain m n T σ Δ ε ∧
    cfg.batchSize.val = 1 ∧
    theorem_4_15_uniformThetaAt betaLower betaUpper
      (theorem_4_15_otherwiseOneMinusBetaScale m n σ ε) (1 - cfg.beta) ∧
    theorem_4_15_uniformThetaAt etaLower etaUpper
      (theorem_4_15_otherwiseEtaRate m n σ Δ ε T) (cfg.eta 0) ∧
    (∀ t ∈ Finset.range T,
      cfg.eta t = cfg.eta 0)

def theorem_4_15_branchRegimeThresholdDomain
    (_m _n : ℕ) (_σ : ℝ) (Δ : ℝ) : Prop :=
  sourceInvDomain Δ

def theorem_4_15_branchRegimeThreshold
    (m n : ℕ) (σ Δ ε : ℝ)
    (hdom : theorem_4_15_branchRegimeThresholdDomain m n σ Δ) : ℝ :=
  realizedSourceSqrt (matrixRankBound m n : ℝ)
    (by
      unfold sourceSqrtDomain
      positivity) *
    σ * realizedSourceInv Δ hdom * ε

def theorem_4_15_positiveHorizonSchedule {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfgForHorizon : ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (σ Δ s : ℝ) : Prop :=
  ∀ N : ℕ, horizonDomain N →
    let cfgN := cfgForHorizon N
    let JN := stochasticHessianJstar P cfgN N
    cfgN.W0 = W0 ∧ theorem_4_15_positiveBranchSchedule cfgN N JN σ Δ s

def theorem_4_15_positiveBranchRegime {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (σ Δ : ℝ)
    (hdom : theorem_4_15_branchRegimeThresholdDomain m n σ Δ) : Prop :=
  AsymptoticLowerReal epsilonDomain
    (fun _ => stochasticHessianJstar P cfg T)
    (fun ε => theorem_4_15_branchRegimeThreshold m n σ Δ ε hdom)
    (theoremScope "Theorem 4.15 Jstar lower branch" ["epsilon"])

def theorem_4_15_positiveRunForHorizon {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfgForHorizon : ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (σ Δ s : ℝ) (N : ℕ) : Prop :=
  horizonDomain N ∧
    let cfgN := cfgForHorizon N
    let JN := stochasticHessianJstar P cfgN N
    cfgN.W0 = W0 ∧
      theorem_4_15_positiveBranchSchedule cfgN N JN σ Δ s ∧
      ∃ hregDom : theorem_4_15_branchRegimeThresholdDomain m n σ Δ,
        theorem_4_15_positiveBranchRegime P cfgN N σ Δ hregDom

def theorem_4_15_otherwiseHorizonSchedule {m n : ℕ}
    (cfgForHorizon : ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (σ Δ ε : ℝ)
    (betaLower betaUpper etaLower etaUpper : ℝ) : Prop :=
  ∀ N : ℕ, horizonDomain N →
    let cfgN := cfgForHorizon N
    cfgN.W0 = W0 ∧ theorem_4_15_otherwiseBranchSchedule cfgN N σ Δ ε
      betaLower betaUpper etaLower etaUpper

def theorem_4_15_otherwiseBranchRegime {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (σ Δ ε C : ℝ)
    (hdom : theorem_4_15_branchRegimeThresholdDomain m n σ Δ) : Prop :=
  epsilonDomain ε ∧ 0 < C ∧
    stochasticHessianDirectionalAverage P cfg T ≤
      C * theorem_4_15_branchRegimeThreshold m n σ Δ ε hdom

/- Appendix B.4 prints the directional quantity `J` in its otherwise
   antecedent, although the fixed-horizon formula immediately preceding it
   depends on `Jstar = max (E[Jhat]) (E[J])`.  The non-realized predicate above
   records that source text for discrepancy tracking.  The internal formula
   helper below uses `Jstar`; the released rate contract later exposes the
   equivalent corrected boundary as source directional control plus the
   omitted cross-average control. -/

def theorem_4_15_otherwiseRunForHorizon {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfgForHorizon : ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (σ Δ ε C : ℝ)
    (betaLower betaUpper etaLower etaUpper : ℝ) (N : ℕ) : Prop :=
  horizonDomain N ∧
    let cfgN := cfgForHorizon N
    cfgN.W0 = W0 ∧
      theorem_4_15_otherwiseBranchSchedule cfgN N σ Δ ε
        betaLower betaUpper etaLower etaUpper ∧
      ∃ hregDom : theorem_4_15_branchRegimeThresholdDomain m n σ Δ,
        theorem_4_15_otherwiseBranchRegime P cfgN N σ Δ ε C hregDom

def theorem_4_15_otherwiseRunForAccuracyHorizon
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (σ Δ ε C : ℝ)
    (betaLower betaUpper etaLower etaUpper : ℝ) (N : ℕ) : Prop :=
  horizonDomain N ∧
    let cfgN := cfgForAccuracyHorizon ε N
    cfgN.W0 = W0 ∧
      theorem_4_15_otherwiseBranchSchedule cfgN N σ Δ ε
        betaLower betaUpper etaLower etaUpper ∧
      ∃ hregDom : theorem_4_15_branchRegimeThresholdDomain m n σ Δ,
        theorem_4_15_otherwiseBranchRegime P cfgN N σ Δ ε C hregDom

def theorem_4_15_positiveBranchRegimeRealized
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (σ Δ : ℝ)
    (hwd : stochasticHessianJstarWellDefined P cfg T)
    (hdom : theorem_4_15_branchRegimeThresholdDomain m n σ Δ) : Prop :=
  AsymptoticLowerReal epsilonDomain
    (fun _ => stochasticHessianJstarRealized P cfg T hwd)
    (fun ε => theorem_4_15_branchRegimeThreshold m n σ Δ ε hdom)
    (theoremScope "Theorem 4.15 realized Jstar lower branch" ["epsilon"])

def theorem_4_15_otherwiseBranchRegimeRealized
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (σ Δ ε C : ℝ)
    (hwd : stochasticHessianJstarWellDefined P cfg T)
    (hdom : theorem_4_15_branchRegimeThresholdDomain m n σ Δ) : Prop :=
  epsilonDomain ε ∧ 0 < C ∧
    stochasticHessianJstarRealized P cfg T hwd ≤
      C * theorem_4_15_branchRegimeThreshold m n σ Δ ε hdom

/- Appendix B.4's printed otherwise antecedent controls the realized
   directional average `J`, not `Jstar`.  Keep that source boundary as a
   separate generated-process predicate: it uses the same Algorithm 1 state,
   schedule parameters, and expectation witness as the corrected route, but
   contains no cross/Jstar or stationarity premise. -/
def theorem_4_15_otherwiseSourceBranchRegimeRealized
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (σ Δ ε C : ℝ)
    (hwd : stochasticHessianJstarWellDefined P cfg T)
    (hdom : theorem_4_15_branchRegimeThresholdDomain m n σ Δ) : Prop :=
  epsilonDomain ε ∧ 0 < C ∧
    stochasticHessianDirectionalAverageRealized P cfg T hwd.1 ≤
      C * theorem_4_15_branchRegimeThreshold m n σ Δ ε hdom

/- This is the exact missing mathematical bridge at the source boundary.  The
   source directional regime becomes the existing corrected Jstar regime iff
   the cross half needed by the momentum-lag estimate is also controlled at
   the same threshold.  This theorem does not assert or assume that the source
   hypotheses provide that cross control. -/
theorem theorem_4_15_otherwise_source_regime_and_cross_iff_jstar_regime
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (σ Δ ε C : ℝ)
    (hwd : stochasticHessianJstarWellDefined P cfg T)
    (hdom : theorem_4_15_branchRegimeThresholdDomain m n σ Δ) :
    (theorem_4_15_otherwiseSourceBranchRegimeRealized
        P cfg T σ Δ ε C hwd hdom ∧
      stochasticHessianCrossAverageRealized P cfg T hwd.2 ≤
        C * theorem_4_15_branchRegimeThreshold m n σ Δ ε hdom) ↔
      theorem_4_15_otherwiseBranchRegimeRealized
        P cfg T σ Δ ε C hwd hdom := by
  unfold theorem_4_15_otherwiseSourceBranchRegimeRealized
    theorem_4_15_otherwiseBranchRegimeRealized
  constructor
  · rintro ⟨⟨hε, hC, hdir⟩, hcross⟩
    refine ⟨hε, hC, ?_⟩
    rw [stochasticHessianJstarRealized_eq_source_max, max_le_iff]
    exact ⟨hcross, hdir⟩
  · rintro ⟨hε, hC, hmax⟩
    rw [stochasticHessianJstarRealized_eq_source_max, max_le_iff] at hmax
    exact ⟨⟨hε, hC, hmax.2⟩, hmax.1⟩

def theorem_4_15_sourceDomain (T : ℕ) (η : ℝ) : Prop :=
  sourceHorizonEtaQuotDomain T η ∧ 0 < η

def theorem_4_15_positiveBranchPointwiseCondition
    (m n : ℕ) (Jstar σ Δ ε : ℝ) : Prop :=
  epsilonDomain ε ∧
    ∃ hregDom : theorem_4_15_branchRegimeThresholdDomain m n σ Δ,
      ∃ c : ℝ, 0 < c ∧
        c * theorem_4_15_branchRegimeThreshold m n σ Δ ε hregDom ≤ Jstar

def theorem_4_15_positiveBranchPointwisePremise
    (m n : ℕ) (Jstar σ Δ : ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ ε : ℝ, epsilonDomain ε → ε ≤ ε₀ →
      theorem_4_15_positiveBranchPointwiseCondition m n Jstar σ Δ ε

def theorem_4_15_positiveRunRealizedForHorizon
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfgForHorizon : ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (Jstar σ Δ s : ℝ) (N : ℕ) : Prop :=
  horizonDomain N ∧
    ∃ hwd : stochasticMuonExpectationsWellDefined P (cfgForHorizon N) N,
      let JN := stochasticHessianJstarRealized P (cfgForHorizon N) N hwd.2.2
      (cfgForHorizon N).W0 = W0 ∧
        JN = Jstar ∧
        theorem_4_15_positiveBranchSchedule (cfgForHorizon N) N Jstar σ Δ s ∧
        theorem_4_15_sourceDomain N
          (Real.sqrt (sourceQuot
            ((1 - (cfgForHorizon N).beta) * Δ) ((N : ℝ) * Jstar)))

noncomputable def theorem_4_15_positiveRunAverageRealized
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfgForHorizon : ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (Jstar σ Δ s : ℝ) (N : ℕ)
    (hN : theorem_4_15_positiveRunRealizedForHorizon
      P cfgForHorizon W0 Jstar σ Δ s N) :
    ℝ :=
  stochasticAverageNuclearGradientRealized P (cfgForHorizon N) N
    (Classical.choose hN.2).1

noncomputable def theorem_4_15_positiveRunBranchRateRealized
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfgForHorizon : ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (Jstar σ Δ s : ℝ) (N : ℕ)
    (hN : theorem_4_15_positiveRunRealizedForHorizon
      P cfgForHorizon W0 Jstar σ Δ s N) :
    ℝ :=
  let hwd := Classical.choose hN.2
  let hspec := Classical.choose_spec hN.2
  theorem_4_15_branchRate m n Jstar σ Δ s N hspec.2.2.1.1.2.2.2.2.2

def theorem_4_15_otherwiseRunRealizedForAccuracyHorizon
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (σ Δ ε C : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (N : ℕ) : Prop :=
  horizonDomain N ∧
    ∃ hwd : stochasticMuonExpectationsWellDefined P (cfgForAccuracyHorizon ε N) N,
      let cfgN := cfgForAccuracyHorizon ε N
      cfgN.W0 = W0 ∧
        theorem_4_15_otherwiseBranchSchedule cfgN N σ Δ ε
          betaLower betaUpper etaLower etaUpper ∧
        theorem_4_15_sourceDomain N (cfgN.eta 0) ∧
        theorem_4_15_uniformThetaAt horizonLower horizonUpper
          (theorem_4_15_otherwiseComplexityRate m n σ ε) (N : ℝ) ∧
        ∃ hregDom : theorem_4_15_branchRegimeThresholdDomain m n σ Δ,
          theorem_4_15_otherwiseBranchRegimeRealized
            P cfgN N σ Δ ε C hwd.2.2 hregDom

/- Source-faithful generated-run boundary for Appendix B.4 step 27.  Unlike
   `theorem_4_15_otherwiseRunRealizedForAccuracyHorizon`, its curvature
   antecedent is exactly the directional realized average.  Assumptions 4.13
   and 3.3 are recorded here together with the printed constant-step,
   accuracy, and selected-horizon scales so that a future Track-A proof (or a
   genuine source counterexample) cannot silently replace the source objects. -/
def theorem_4_15_otherwiseSourceSmallJGeneratedRunForAccuracyHorizon
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (σ Δ ε C s : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (N : ℕ) : Prop :=
  horizonDomain N ∧
    ∃ hfinite : P.objective.HasFiniteInfimum,
      sourceObjectiveInitialGap P.objective W0 hfinite = Δ ∧
      ThirdDerivativeBounded P.objective s ∧
      BoundedVariance P σ ∧
      ∃ hwd : stochasticMuonExpectationsWellDefined P
          (cfgForAccuracyHorizon ε N) N,
        let cfgN := cfgForAccuracyHorizon ε N
        cfgN.W0 = W0 ∧
          theorem_4_15_otherwiseBranchSchedule cfgN N σ Δ ε
            betaLower betaUpper etaLower etaUpper ∧
          theorem_4_15_sourceDomain N (cfgN.eta 0) ∧
          theorem_4_15_uniformThetaAt horizonLower horizonUpper
            (theorem_4_15_otherwiseComplexityRate m n σ ε) (N : ℝ) ∧
          ∃ hregDom : theorem_4_15_branchRegimeThresholdDomain m n σ Δ,
            theorem_4_15_otherwiseSourceBranchRegimeRealized
              P cfgN N σ Δ ε C hwd.2.2 hregDom

/- The original source-small-`J` branch is false (the checked generated
   counterexample is in Part003).  The finite-horizon proof needs exactly the
   omitted cross half at this boundary.  This corrected run therefore retains
   every source assumption and schedule and adds only the realized cross
   average bound at the same threshold; it does not assume `Jstar`, descent,
   stationarity, or the desired output guarantee. -/
def theorem_4_15_otherwiseCorrectedSourceSmallJGeneratedRunForAccuracyHorizon
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (σ Δ ε C s : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (N : ℕ) : Prop :=
  horizonDomain N ∧
    ∃ hfinite : P.objective.HasFiniteInfimum,
      sourceObjectiveInitialGap P.objective W0 hfinite = Δ ∧
      ThirdDerivativeBounded P.objective s ∧
      BoundedVariance P σ ∧
      ∃ hwd : stochasticMuonExpectationsWellDefined P
          (cfgForAccuracyHorizon ε N) N,
        let cfgN := cfgForAccuracyHorizon ε N
        cfgN.W0 = W0 ∧
          theorem_4_15_otherwiseBranchSchedule cfgN N σ Δ ε
            betaLower betaUpper etaLower etaUpper ∧
          theorem_4_15_sourceDomain N (cfgN.eta 0) ∧
          theorem_4_15_uniformThetaAt horizonLower horizonUpper
            (theorem_4_15_otherwiseComplexityRate m n σ ε) (N : ℝ) ∧
          ∃ hregDom : theorem_4_15_branchRegimeThresholdDomain m n σ Δ,
            theorem_4_15_otherwiseSourceBranchRegimeRealized
                P cfgN N σ Δ ε C hwd.2.2 hregDom ∧
              stochasticHessianCrossAverageRealized
                  P cfgN N hwd.2.2.2 ≤
                C * theorem_4_15_branchRegimeThreshold
                  m n σ Δ ε hregDom

theorem theorem_4_15_otherwise_corrected_source_run_to_source_run
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (σ Δ ε C s : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (N : ℕ)
    (hN : theorem_4_15_otherwiseCorrectedSourceSmallJGeneratedRunForAccuracyHorizon
      P cfgForAccuracyHorizon W0 σ Δ ε C s
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N) :
    theorem_4_15_otherwiseSourceSmallJGeneratedRunForAccuracyHorizon
      P cfgForAccuracyHorizon W0 σ Δ ε C s
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N := by
  rcases hN with
    ⟨horizon, hfinite, hDelta, hthird, hvariance, hwd, hW0, hSchedule,
      hsource, hHorizon, hregDom, hregime, _hcross⟩
  exact ⟨horizon, hfinite, hDelta, hthird, hvariance, hwd, hW0, hSchedule,
    hsource, hHorizon, hregDom, hregime⟩

theorem theorem_4_15_otherwise_corrected_source_run_to_jstar_run
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (σ Δ ε C s : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (N : ℕ)
    (hN : theorem_4_15_otherwiseCorrectedSourceSmallJGeneratedRunForAccuracyHorizon
      P cfgForAccuracyHorizon W0 σ Δ ε C s
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N) :
    theorem_4_15_otherwiseRunRealizedForAccuracyHorizon
      P cfgForAccuracyHorizon W0 σ Δ ε C
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N := by
  rcases hN with
    ⟨horizon, _hfinite, _hDelta, _hthird, _hvariance, hwd, hW0, hSchedule,
      hsource, hHorizon, hregDom, hregime, hcross⟩
  refine ⟨horizon, hwd, hW0, hSchedule, hsource, hHorizon, hregDom, ?_⟩
  exact (theorem_4_15_otherwise_source_regime_and_cross_iff_jstar_regime
    P (cfgForAccuracyHorizon ε N) N σ Δ ε C hwd.2.2 hregDom).mp
      ⟨hregime, hcross⟩

/- At the allowed zero-noise specialization, the printed otherwise schedule
   cannot be realized for any positive accuracy: its `1 - beta` scale contains
   the partial quotient `epsilon^2 / (r * sigma^2)`.  This records the concrete
   counterexample to the former unconditional schedule existential. -/
theorem theorem_4_15_otherwise_run_impossible_at_zero_variance
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (Δ ε C : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (N : ℕ)
    (_hε : epsilonDomain ε) :
    ¬ theorem_4_15_otherwiseRunRealizedForAccuracyHorizon P
        cfgForAccuracyHorizon W0 0 Δ ε C
        betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N := by
  intro hrun
  unfold theorem_4_15_otherwiseRunRealizedForAccuracyHorizon at hrun
  dsimp at hrun
  rcases hrun with
    ⟨_hN, _hwd, _hW0, hSchedule, _hsource, _hHorizonScale, _hRegime⟩
  rcases hSchedule with
    ⟨hScheduleDomain, _hBatch, _hBetaScale, _hEtaScale, _hEta⟩
  rcases hScheduleDomain with ⟨_horizon, hquot, _hrank, _hetaQuot⟩
  have hzero : (0 : ℝ) ≠ 0 := by
    simpa [sourceQuotDomain] using hquot
  exact hzero rfl

noncomputable def theorem_4_15_otherwiseRunAverageRealized
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (σ Δ ε C : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (N : ℕ)
    (hN : theorem_4_15_otherwiseRunRealizedForAccuracyHorizon P
      cfgForAccuracyHorizon W0 σ Δ ε C
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N) : ℝ :=
  stochasticAverageNuclearGradientRealized P (cfgForAccuracyHorizon ε N) N
    (Classical.choose hN.2).1

/- The Appendix B.4 complexity claim asks for accuracy `ε`, but the
   fixed-horizon `O(δ)` estimate must generally be run at a smaller internal
   schedule accuracy `δ = ε / K`, where `K` absorbs the uniform constants
   in the displayed `O(δ)` bound.  Keeping these two accuracies separate is
   essential: using `ε` for both would require the hidden constant to be at
   most one. -/
def theorem_4_15_otherwiseScheduleAccuracy (accuracyScale ε : ℝ) : ℝ :=
  sourceQuot ε accuracyScale

def theorem_4_15_otherwiseReindexedRunRealizedForAccuracyHorizon
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (σ Δ C : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (accuracyScale ε : ℝ) (N : ℕ) : Prop :=
  theorem_4_15_otherwiseRunRealizedForAccuracyHorizon P
    cfgForAccuracyHorizon W0 σ Δ
    (theorem_4_15_otherwiseScheduleAccuracy accuracyScale ε) C
    betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N

def theorem_4_15_otherwiseCorrectedSourceSmallJReindexedRunForAccuracyHorizon
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (σ Δ C s : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (accuracyScale ε : ℝ) (N : ℕ) : Prop :=
  theorem_4_15_otherwiseCorrectedSourceSmallJGeneratedRunForAccuracyHorizon
    P cfgForAccuracyHorizon W0 σ Δ
    (theorem_4_15_otherwiseScheduleAccuracy accuracyScale ε) C s
    betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N

theorem theorem_4_15_otherwise_corrected_source_reindexed_run_to_jstar_run
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (σ Δ C s : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (accuracyScale ε : ℝ) (N : ℕ)
    (hN : theorem_4_15_otherwiseCorrectedSourceSmallJReindexedRunForAccuracyHorizon
      P cfgForAccuracyHorizon W0 σ Δ C s
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper
      accuracyScale ε N) :
    theorem_4_15_otherwiseReindexedRunRealizedForAccuracyHorizon P
      cfgForAccuracyHorizon W0 σ Δ C
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper
      accuracyScale ε N := by
  exact theorem_4_15_otherwise_corrected_source_run_to_jstar_run
    P cfgForAccuracyHorizon W0 σ Δ
    (theorem_4_15_otherwiseScheduleAccuracy accuracyScale ε) C s
    betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N hN

noncomputable def theorem_4_15_otherwiseReindexedRunAverageRealized
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (σ Δ C : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (accuracyScale ε : ℝ) (N : ℕ)
    (hN : theorem_4_15_otherwiseReindexedRunRealizedForAccuracyHorizon P
      cfgForAccuracyHorizon W0 σ Δ C
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper
      accuracyScale ε N) : ℝ :=
  theorem_4_15_otherwiseRunAverageRealized P cfgForAccuracyHorizon W0 σ Δ
    (theorem_4_15_otherwiseScheduleAccuracy accuracyScale ε) C
    betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N hN

theorem theorem_4_15_otherwiseScheduleAccuracy_pos
    {accuracyScale ε : ℝ} (hscale : 0 < accuracyScale)
    (hε : epsilonDomain ε) :
    epsilonDomain (theorem_4_15_otherwiseScheduleAccuracy accuracyScale ε) := by
  exact div_pos hε hscale

theorem theorem_4_15_otherwiseComplexityRate_reindex
    (m n : ℕ) (σ accuracyScale ε : ℝ)
    (hscale : accuracyScale ≠ 0) (hε : ε ≠ 0) :
    theorem_4_15_otherwiseComplexityRate m n σ
        (theorem_4_15_otherwiseScheduleAccuracy accuracyScale ε) =
      accuracyScale ^ 3 * theorem_4_15_otherwiseComplexityRate m n σ ε := by
  unfold theorem_4_15_otherwiseComplexityRate
    theorem_4_15_otherwiseScheduleAccuracy sourceQuot
  field_simp [hscale, hε]

def theorem_4_15_base_rhsDomain {m n : ℕ}
    (cfg : StochasticMuonConfig m n) (T : ℕ) (Δ Jstar σ η : ℝ) : Prop :=
  let r : ℝ := matrixRankBound m n
  let B : ℝ := cfg.batchSize.val
  horizonDomain T ∧
    sourceQuotDomain Δ ((T : ℝ) * η) ∧
    sourceSqrtDomain (r * (1 - cfg.beta)) ∧
    sourceSqrtDomain ((1 + cfg.beta) * B) ∧
    sourceQuotDomain (2 * σ * sourceSqrt (r * (1 - cfg.beta)))
      (sourceSqrt ((1 + cfg.beta) * B)) ∧
    sourceSqrtDomain r ∧
    sourceSqrtDomain B ∧
    sourceQuotDomain (2 * σ * sourceSqrt r)
      ((1 - cfg.beta) * (T : ℝ) * sourceSqrt B) ∧
    sourceQuotDomain (2 * η * cfg.beta * Jstar) (1 - cfg.beta)

def theorem_4_15_base_rhs {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (_P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (Δ Jstar σ η : ℝ)
    (hdom : theorem_4_15_base_rhsDomain cfg T Δ Jstar σ η) : ℝ :=
  let r : ℝ := matrixRankBound m n
  let B : ℝ := cfg.batchSize.val
  let ⟨_hT, hdrop, hsNoise, hsBatchNoise, hqBatchNoise, hsRank, hsBatch, hqTail, hqMomentum⟩ :=
    hdom
  realizedSourceQuot Δ ((T : ℝ) * η) hdrop +
    Jstar * η / 2 +
    realizedSourceQuot
      (2 * σ * realizedSourceSqrt (r * (1 - cfg.beta)) hsNoise)
      (realizedSourceSqrt ((1 + cfg.beta) * B) hsBatchNoise) hqBatchNoise +
    realizedSourceQuot
      (2 * σ * realizedSourceSqrt r hsRank)
      ((1 - cfg.beta) * (T : ℝ) * realizedSourceSqrt B hsBatch) hqTail +
    realizedSourceQuot (2 * η * cfg.beta * Jstar) (1 - cfg.beta) hqMomentum

def theorem_4_15_sourceBaseRhs {m n : ℕ}
    (cfg : StochasticMuonConfig m n) (T : ℕ) (Δ Jstar σ η : ℝ) : ℝ :=
  let r : ℝ := matrixRankBound m n
  let B : ℝ := cfg.batchSize.val
  Δ / ((T : ℝ) * η) +
    Jstar * η / 2 +
    (2 * σ * Real.sqrt (r * (1 - cfg.beta))) / Real.sqrt ((1 + cfg.beta) * B) +
    (2 * σ * Real.sqrt r) / ((1 - cfg.beta) * (T : ℝ) * Real.sqrt B) +
    (2 * η * cfg.beta * Jstar) / (1 - cfg.beta)

def theorem_4_14_sourceDomain (T : ℕ) (η : ℝ) : Prop :=
  sourceHorizonEtaQuotDomain T η ∧ 0 < η

theorem theorem_4_14_eta_pos_of_sourceDomain {T : ℕ} {η : ℝ}
    (hsrc : theorem_4_14_sourceDomain T η) :
    0 < η :=
  hsrc.2

theorem theorem_4_14_eta_nonneg_of_sourceDomain {T : ℕ} {η : ℝ}
    (hsrc : theorem_4_14_sourceDomain T η) :
    0 ≤ η :=
  le_of_lt (theorem_4_14_eta_pos_of_sourceDomain hsrc)

theorem theorem_4_14_fixedJ_positive_source_domain_obligation
    {m n : ℕ}
    (P : Objective m n)
    (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (W0 : Mat m n) (J s Δ : ℝ) (N : ℕ)
    (_hrun : theorem_4_14_fixedJ_positiveRunForHorizon
      P cfgForHorizon W0 J s Δ N) :
    theorem_4_14_sourceDomain N
      (theorem_4_14_positiveBranchEtaRate J Δ N) := by
  have hRhsDomain :=
    theorem_4_14_fixedJ_positive_rhs_domain_obligation
      P cfgForHorizon W0 J s Δ N _hrun
  unfold theorem_4_14_sourceDomain sourceHorizonEtaQuotDomain
  refine ⟨⟨hRhsDomain.1, ?_⟩, hRhsDomain.2.1⟩
  simpa [sourceQuotDomain] using hRhsDomain.2.2.1

theorem theorem_4_15_eta_pos_of_sourceDomain {T : ℕ} {η : ℝ}
    (h : theorem_4_15_sourceDomain T η) : 0 < η :=
  h.2

theorem theorem_4_15_sourceDomain_rejects_negative_eta :
    ¬ theorem_4_15_sourceDomain 1 (-1) := by
  norm_num [theorem_4_15_sourceDomain]

def theorem_4_15_downstream_phase2_boundary {ξ : Type*}
    [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (σ η _s : ℝ) (hfinite : P.objective.HasFiniteInfimum) : Prop :=
  let Δ := sourceObjectiveInitialGap P.objective cfg.W0 hfinite
  ∃ hwd : stochasticMuonExpectationsWellDefined P cfg T,
    theorem_4_15_base_rhsDomain cfg T Δ
      (stochasticHessianJstarRealized P cfg T hwd.2.2) σ η ∧ 0 < η

def theorem_4_14_downstream_phase2_boundary {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T : ℕ) (s η : ℝ) : Prop :=
  let J := hessianDirectionalAverage P cfg T
  ∃ hdom : theorem_4_14_rhsDomain P cfg T J s η,
    True

def theorem_4_14_sourceDomainCorrectionNeeded {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T : ℕ) (s η : ℝ) : Prop :=
  let hsrc := theorem_4_14_sourceDomain T η
  hsrc ∧
    ¬ theorem_4_14_downstream_phase2_boundary P cfg T s η

theorem theorem_4_14_sourceDomain_of_downstream {m n : ℕ}
    {P : Objective m n} {cfg : DeterministicMuonConfig m n}
    {T : ℕ} {s η : ℝ} :
    theorem_4_14_downstream_phase2_boundary P cfg T s η →
      theorem_4_14_sourceDomain T η := by
  intro h
  rcases h with ⟨hdom, _⟩
  unfold theorem_4_14_sourceDomain theorem_4_14_rhsDomain at *
  rcases hdom with ⟨hT, hηpos, hdrop, _hsRankCube⟩
  exact ⟨⟨hT, hdrop⟩, hηpos⟩

def theorem_4_15_sourceDomainCorrectionNeeded {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (σ η s : ℝ) (hfinite : P.objective.HasFiniteInfimum) : Prop :=
  let hsrc := theorem_4_15_sourceDomain T η
  hsrc ∧
    ¬ theorem_4_15_downstream_phase2_boundary P cfg T σ η s hfinite

theorem theorem_4_15_sourceDomain_of_downstream {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    {P : StochasticProblem ξ m n} {cfg : StochasticMuonConfig m n}
    {T : ℕ} {σ η s : ℝ} {hfinite : P.objective.HasFiniteInfimum} :
    theorem_4_15_downstream_phase2_boundary P cfg T σ η s hfinite →
      theorem_4_15_sourceDomain T η := by
  intro h
  rcases h with ⟨hwd, hdom, hηpos⟩
  unfold theorem_4_15_sourceDomain theorem_4_15_base_rhsDomain at *
  exact ⟨⟨hdom.1, hdom.2.1⟩, hηpos⟩

theorem theorem_4_15_downstream_phase2_boundary_of_sourceDomain
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (σ η s : ℝ) (hfinite : P.objective.HasFiniteInfimum)
    (hsrc : theorem_4_15_sourceDomain T η)
    (_hthird : ThirdDerivativeBounded P.objective s)
    (_hvariance : BoundedVariance P σ)
    (_hη : ∀ t ∈ Finset.range T, cfg.eta t = η) :
    theorem_4_15_downstream_phase2_boundary P cfg T σ η s hfinite := by
  let hregularity : StochasticObjectiveRegularity P.objective :=
    Or.inr (Or.inr ⟨s, _hthird⟩)
  let hwd : stochasticMuonExpectationsWellDefined P cfg T := ⟨
    stochasticAverageNuclearGradient_wellDefined_of_source_assumptions
      P cfg T σ hregularity _hvariance,
    stochasticExpectedObjectiveDrop_wellDefined_of_source_assumptions
      P cfg T σ hregularity _hvariance,
    stochasticHessianJstar_wellDefined_of_source_assumptions
      P cfg T s σ _hthird _hvariance⟩
  have hβ_nonneg : 0 ≤ cfg.beta := cfg.beta_mem.1
  have hβ_lt_one : cfg.beta < 1 := cfg.beta_mem.2
  have h_one_sub_beta_pos : 0 < 1 - cfg.beta := sub_pos.mpr hβ_lt_one
  have h_one_plus_beta_pos : 0 < 1 + cfg.beta := by linarith
  have hB_pos : 0 < (cfg.batchSize.val : ℝ) := by exact_mod_cast cfg.batchSize.positive
  have hr_nonneg : 0 ≤ (matrixRankBound m n : ℝ) := by exact_mod_cast Nat.zero_le (matrixRankBound m n)
  refine ⟨hwd, ?_, hsrc.2⟩
  unfold theorem_4_15_base_rhsDomain
  dsimp
  refine ⟨hsrc.1.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold sourceQuotDomain
    exact hsrc.1.2
  · unfold sourceSqrtDomain
    exact mul_nonneg hr_nonneg (le_of_lt h_one_sub_beta_pos)
  · unfold sourceSqrtDomain
    exact mul_nonneg (le_of_lt h_one_plus_beta_pos) (le_of_lt hB_pos)
  · unfold sourceQuotDomain
    exact ne_of_gt (by
      unfold sourceSqrt
      exact Real.sqrt_pos.2 (mul_pos h_one_plus_beta_pos hB_pos))
  · unfold sourceSqrtDomain
    exact hr_nonneg
  · unfold sourceSqrtDomain
    exact le_of_lt hB_pos
  · unfold sourceQuotDomain
    exact mul_ne_zero (mul_ne_zero
      (stochasticMuonConfig_one_sub_beta_sourceQuotDomain cfg
        (2 * σ * sourceSqrt (matrixRankBound m n : ℝ)))
      (by exact_mod_cast ne_of_gt hsrc.1.1))
      (ne_of_gt (by
        unfold sourceSqrt
        exact Real.sqrt_pos.2 hB_pos))
  · exact stochasticMuonConfig_one_sub_beta_sourceQuotDomain cfg
      (2 * η * cfg.beta * stochasticHessianJstarRealized P cfg T hwd.2.2)

theorem theorem_4_14_downstream_phase2_boundary_of_sourceDomain {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T : ℕ) (s η : ℝ)
    (hsrc : theorem_4_14_sourceDomain T η)
    (_hthird : ThirdDerivativeBounded P s)
    (_hη : ∀ t ∈ Finset.range T, cfg.eta t = η) :
    theorem_4_14_downstream_phase2_boundary P cfg T s η := by
  refine ⟨?_, trivial⟩
  unfold theorem_4_14_rhsDomain
  refine ⟨hsrc.1.1, hsrc.2, ?_, rankCube_sourceSqrtDomain m n⟩
  unfold sourceQuotDomain
  exact hsrc.1.2

theorem theorem_4_15_source_domain_obligation {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (σ η s : ℝ) (hfinite : P.objective.HasFiniteInfimum)
    (_hthird : ThirdDerivativeBounded P.objective s)
    (_hvariance : BoundedVariance P σ)
    (_hη : ∀ t ∈ Finset.range T, cfg.eta t = η) :
    SourceScalarDomainBoundary (theorem_4_15_sourceDomain T η)
      (theorem_4_15_downstream_phase2_boundary P cfg T σ η s hfinite)
      (theorem_4_15_sourceDomainCorrectionNeeded P cfg T σ η s hfinite) := by
  constructor
  · exact theorem_4_15_sourceDomain_of_downstream
  · intro hsrc
    exact Or.inl
      (theorem_4_15_downstream_phase2_boundary_of_sourceDomain P cfg T σ η s hfinite
        hsrc _hthird _hvariance _hη)

theorem theorem_4_14_source_domain_obligation {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T : ℕ) (s η : ℝ)
    (_hthird : ThirdDerivativeBounded P s)
    (_hη : ∀ t ∈ Finset.range T, cfg.eta t = η) :
    SourceScalarDomainBoundary (theorem_4_14_sourceDomain T η)
      (theorem_4_14_downstream_phase2_boundary P cfg T s η)
      (theorem_4_14_sourceDomainCorrectionNeeded P cfg T s η) := by
  constructor
  · exact theorem_4_14_sourceDomain_of_downstream
  · intro hsrc
    exact Or.inl
      (theorem_4_14_downstream_phase2_boundary_of_sourceDomain P cfg T s η
        hsrc _hthird _hη)

theorem theorem_4_14_positive_branch_domain_obligation {m n : ℕ}
    (P : Objective m n) (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (W0 : Mat m n) (s Δ : ℝ) (N : ℕ)
    (_hrun : theorem_4_14_positiveRunForHorizon P cfgForHorizon W0 s Δ N) :
    theorem_4_14_branchRateDomain m n N
      (hessianDirectionalAverage P (cfgForHorizon N) N) s Δ := by
  unfold theorem_4_14_positiveRunForHorizon at _hrun
  dsimp at _hrun
  rcases _hrun with ⟨_hN, _hW0, hBranchDomain, _hSchedule, _hRegime⟩
  exact hBranchDomain

theorem theorem_4_15_positive_branch_domain_obligation
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfgForHorizon : ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (σ Δ s : ℝ) (N : ℕ)
    (_hrun : theorem_4_15_positiveRunForHorizon P cfgForHorizon W0 σ Δ s N) :
    theorem_4_15_positiveBranchRateDomain m n N
      (stochasticHessianJstar P (cfgForHorizon N) N) σ Δ s := by
  unfold theorem_4_15_positiveRunForHorizon at _hrun
  dsimp at _hrun
  rcases _hrun with ⟨_hN, _hW0, hSchedule, _hRegime⟩
  unfold theorem_4_15_positiveBranchSchedule at hSchedule
  rcases hSchedule with ⟨hScheduleDomain, _hBatch, _hEta, _hBeta⟩
  unfold theorem_4_15_positiveBranchScheduleDomain at hScheduleDomain
  rcases hScheduleDomain with
    ⟨_hHorizon, _hSqrtJDelta, _hSqrtRT, _hBetaQuot, _hEtaDom, hRateDomain⟩
  simpa using hRateDomain

/- The printed otherwise schedule is a conditional branch datum.  It cannot
   be required unconditionally at the degenerate source point s = Δ = 0:
   already at the positive horizon N = 1 its eta quotient has denominator
   zero.  This is the typed counterexample for the pre-refactor packaging. -/
theorem theorem_4_14_otherwise_schedule_impossible_at_zero
    {m n : ℕ} (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (W0 : Mat m n) :
    ¬ theorem_4_14_otherwiseHorizonSchedule cfgForHorizon W0 0 0 := by
  intro hschedule
  have hN := hschedule 1 (by norm_num [horizonDomain])
  rcases hN with ⟨_hW0, hEta⟩
  rcases hEta with ⟨hEtaDomain, _hEtaSchedule⟩
  rcases hEtaDomain with ⟨_hN, _hRank, hquot, _hRpow⟩
  have hzero : (0 : ℝ) ≠ 0 := by
    simpa [sourceQuotDomain] using hquot
  exact hzero rfl

theorem theorem_4_14_unconditional_otherwise_schedule_is_false
    {m n : ℕ} (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (hfinite : P.HasFiniteInfimum)
    (hzero : sourceObjectiveInitialGap P cfg.W0 hfinite = 0) :
    ¬ (∃ C : ℝ, 0 < C ∧
      ∃ cfgForAccuracyHorizon : ℝ → ℕ → DeterministicMuonConfig m n,
        theorem_4_14_otherwiseHorizonScheduleForAccuracy
          cfgForAccuracyHorizon cfg.W0 0
            (sourceObjectiveInitialGap P cfg.W0 hfinite)) := by
  rintro ⟨_C, _hC, cfgForAccuracyHorizon, hschedule⟩
  have hscheduleZero :
      theorem_4_14_otherwiseHorizonScheduleForAccuracy
        cfgForAccuracyHorizon cfg.W0 0 0 := by
    simpa [hzero] using hschedule
  have hscheduleAtEpsilonOne :=
    hscheduleZero 1 (by norm_num [epsilonDomain])
  exact theorem_4_14_otherwise_schedule_impossible_at_zero
    (fun N => cfgForAccuracyHorizon 1 N) cfg.W0 hscheduleAtEpsilonOne

def theorem_4_14_zeroObjective : Objective 1 1 :=
  { f := fun _ => 0 }

theorem theorem_4_14_zeroObjective_hasFiniteInfimum :
    theorem_4_14_zeroObjective.HasFiniteInfimum := by
  refine ⟨0, ?_⟩
  intro y hy
  rcases hy with ⟨W, rfl⟩
  simp [theorem_4_14_zeroObjective]

theorem theorem_4_14_zeroObjective_gap_zero
    (cfg : DeterministicMuonConfig 1 1) :
    sourceObjectiveInitialGap theorem_4_14_zeroObjective cfg.W0
        theorem_4_14_zeroObjective_hasFiniteInfimum = 0 := by
  have hrange :
      Set.range (fun _ : Mat 1 1 => (0 : ℝ)) = ({0} : Set ℝ) := by
    ext y
    constructor
    · rintro ⟨W, rfl⟩
      simp
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      exact ⟨0, hy.symm⟩
  simp [sourceObjectiveInitialGap, theorem_4_14_zeroObjective,
    Objective.sourceFStar, Objective.fStar, hrange]

theorem theorem_4_14_zeroObjective_counterexample
    (cfg : DeterministicMuonConfig 1 1) :
    ¬ (∃ C : ℝ, 0 < C ∧
      ∃ cfgForAccuracyHorizon : ℝ → ℕ → DeterministicMuonConfig 1 1,
        theorem_4_14_otherwiseHorizonScheduleForAccuracy
          cfgForAccuracyHorizon cfg.W0 0
            (sourceObjectiveInitialGap theorem_4_14_zeroObjective cfg.W0
              theorem_4_14_zeroObjective_hasFiniteInfimum)) := by
  exact theorem_4_14_unconditional_otherwise_schedule_is_false
    theorem_4_14_zeroObjective cfg
    theorem_4_14_zeroObjective_hasFiniteInfimum
    (theorem_4_14_zeroObjective_gap_zero cfg)

/- The registered Theorem 4.14 contains the fixed-horizon inequality and the
   Appendix B.3 rate/complexity read-offs.  The read-offs are conditional on
   explicit pointwise and horizon-family premises in
   `theorem_4_14_source_rate_consequences`, rather than promoted to Assumption
   4.13 or encoded as unconditional schedule existence. -/
def theorem_4_14_statement {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T : ℕ) (s η : ℝ) (hfinite : P.HasFiniteInfimum) : Prop :=
  SourceScalarDomainBoundary (theorem_4_14_sourceDomain T η)
    (theorem_4_14_downstream_phase2_boundary P cfg T s η)
    (theorem_4_14_sourceDomainCorrectionNeeded P cfg T s η) ∧
    (theorem_4_14_sourceDomain T η →
      ∃ hdom : theorem_4_14_rhsDomain P cfg T
          (hessianDirectionalAverage P cfg T) s η,
        deterministicAverageNuclearGradient P cfg T ≤
          theorem_4_14_rhs P cfg T
            (hessianDirectionalAverage P cfg T) s η hdom) ∧
    theorem_4_14_source_rate_consequences P cfg s hfinite

def theorem_4_15_positive_branch_rate_and_complexity
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (Jstar σ Δ s : ℝ)
    (cfgForHorizon : ℕ → StochasticMuonConfig m n) : Prop :=
  DomainAsymptoticUpperNatOn
      (fun N => theorem_4_15_positiveRunRealizedForHorizon
        P cfgForHorizon cfg.W0 Jstar σ Δ s N)
      (fun N hN => theorem_4_15_positiveRunAverageRealized
        P cfgForHorizon cfg.W0 Jstar σ Δ s N hN)
      (fun N hN => theorem_4_15_positiveRunBranchRateRealized
        P cfgForHorizon cfg.W0 Jstar σ Δ s N hN)
      (theoremScope "Theorem 4.15 fixed-Jstar positive branch rate" ["T"]) ∧
    HorizonNuclearStationarityComplexityWithHorizonRateOn
      (fun N => theorem_4_15_positiveRunRealizedForHorizon
        P cfgForHorizon cfg.W0 Jstar σ Δ s N)
      (fun N hN => theorem_4_15_positiveRunAverageRealized
        P cfgForHorizon cfg.W0 Jstar σ Δ s N hN)
      (fun _N _hN ε => theorem_4_15_complexityRate m n Jstar σ Δ ε)
      (theoremScope "Theorem 4.15 fixed-Jstar epsilon complexity" ["epsilon"]) ∧
    StochasticGeneratedOutputTransferOn P
      (fun N => theorem_4_15_positiveRunRealizedForHorizon
        P cfgForHorizon cfg.W0 Jstar σ Δ s N)
      (fun _N hN => hN.1)
      cfgForHorizon
      (fun _N hN => (Classical.choose hN.2).1)
      (fun N hN => theorem_4_15_positiveRunAverageRealized
        P cfgForHorizon cfg.W0 Jstar σ Δ s N hN)

def theorem_4_15_otherwise_branch_rate_and_complexity
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (σ Δ C betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (accuracyScale : ℝ)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig m n) : Prop :=
  EpsilonHorizonNuclearStationarityComplexityWithHorizonRateOn
    (fun ε N => theorem_4_15_otherwiseReindexedRunRealizedForAccuracyHorizon P
      cfgForAccuracyHorizon cfg.W0 σ Δ C
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper
      accuracyScale ε N)
    (fun ε N hN => theorem_4_15_otherwiseReindexedRunAverageRealized P
      cfgForAccuracyHorizon cfg.W0 σ Δ C
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper
      accuracyScale ε N hN)
    (fun _N ε => theorem_4_15_otherwiseComplexityRate m n σ ε)
    (theoremScope "Theorem 4.15 otherwise epsilon complexity" ["epsilon"]) ∧
  ∀ ε : ℝ,
    StochasticGeneratedOutputTransferOn P
      (fun N => theorem_4_15_otherwiseReindexedRunRealizedForAccuracyHorizon P
        cfgForAccuracyHorizon cfg.W0 σ Δ C
        betaLower betaUpper etaLower etaUpper horizonLower horizonUpper
        accuracyScale ε N)
      (fun _N hN => hN.1)
      (fun N => cfgForAccuracyHorizon
        (theorem_4_15_otherwiseScheduleAccuracy accuracyScale ε) N)
      (fun _N hN => (Classical.choose hN.2).1)
      (fun N hN => theorem_4_15_otherwiseReindexedRunAverageRealized P
        cfgForAccuracyHorizon cfg.W0 σ Δ C
        betaLower betaUpper etaLower etaUpper horizonLower horizonUpper
        accuracyScale ε N hN)

theorem theorem_4_15_positive_run_curvature_control
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n)
    (cfgForHorizon : ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (Jstar σ Δ s : ℝ) (N : ℕ)
    (hN : theorem_4_15_positiveRunRealizedForHorizon
      P cfgForHorizon W0 Jstar σ Δ s N) :
    let hwd := Classical.choose hN.2
    stochasticHessianJstarRealized P (cfgForHorizon N) N hwd.2.2 = Jstar := by
  dsimp
  exact (Classical.choose_spec hN.2).2.1

theorem theorem_4_15_otherwise_selected_horizon_upper_bound
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (σ Δ ε C : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (N : ℕ)
    (hN : theorem_4_15_otherwiseRunRealizedForAccuracyHorizon P
      cfgForAccuracyHorizon W0 σ Δ ε C
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N) :
    (N : ℝ) ≤ horizonUpper * theorem_4_15_otherwiseComplexityRate m n σ ε := by
  rcases hN with
    ⟨_horizon, _hwd, _hW0, _hSchedule, _hsource, hHorizonScale, _hRegime⟩
  exact hHorizonScale.2.2.2

/- A checked consumer for the requested-accuracy/internal-accuracy split.  A
   run scheduled at `δ = ε / accuracyScale` has the source-selected horizon
   bounded by the requested-`ε` complexity rate after the cubic rescaling is
   absorbed into the asymptotic constant. -/
theorem theorem_4_15_otherwise_reindexed_selected_horizon_upper_bound
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (σ Δ C : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (accuracyScale ε : ℝ) (N : ℕ)
    (hscale : 0 < accuracyScale) (hε : epsilonDomain ε)
    (hN : theorem_4_15_otherwiseReindexedRunRealizedForAccuracyHorizon P
      cfgForAccuracyHorizon W0 σ Δ C
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper
      accuracyScale ε N) :
    (N : ℝ) ≤
      (horizonUpper * accuracyScale ^ 3) *
        theorem_4_15_otherwiseComplexityRate m n σ ε := by
  have hselected := theorem_4_15_otherwise_selected_horizon_upper_bound
    P cfgForAccuracyHorizon W0 σ Δ
    (theorem_4_15_otherwiseScheduleAccuracy accuracyScale ε) C
    betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N hN
  rw [theorem_4_15_otherwiseComplexityRate_reindex m n σ accuracyScale ε
    (ne_of_gt hscale) (ne_of_gt hε)] at hselected
  simpa [mul_assoc] using hselected

/- Discrepancy evidence retained for the conditional `Jstar` helper.  Once
   directional control is known, its maximum bound is equivalent to precisely
   the cross-average bound exposed by the corrected source-facing run. -/
theorem theorem_4_15_otherwise_jstar_control_iff_cross_control
    {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n)
    (cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig m n)
    (W0 : Mat m n) (σ Δ ε C s : ℝ)
    (betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ)
    (N : ℕ)
    (_hthird : ThirdDerivativeBounded P.objective s)
    (_hvariance : BoundedVariance P σ)
    (hN : theorem_4_15_otherwiseRunRealizedForAccuracyHorizon P
      cfgForAccuracyHorizon W0 σ Δ ε C
      betaLower betaUpper etaLower etaUpper horizonLower horizonUpper N) :
    ∃ (hwd : stochasticMuonExpectationsWellDefined P
        (cfgForAccuracyHorizon ε N) N)
      (hregDom : theorem_4_15_branchRegimeThresholdDomain m n σ Δ),
      theorem_4_15_otherwiseBranchRegimeRealized P
          (cfgForAccuracyHorizon ε N) N σ Δ ε C hwd.2.2 hregDom ∧
        (stochasticHessianJstarRealized P (cfgForAccuracyHorizon ε N) N hwd.2.2 ≤
            C * theorem_4_15_branchRegimeThreshold m n σ Δ ε hregDom ↔
          stochasticHessianCrossAverageRealized P (cfgForAccuracyHorizon ε N) N
              hwd.2.2.2 ≤
            C * theorem_4_15_branchRegimeThreshold m n σ Δ ε hregDom) := by
  rcases hN with
    ⟨_horizon, hwd, _hW0, _hSchedule, _hsource, _hHorizonScale,
      hregDom, hreg⟩
  refine ⟨hwd, hregDom, hreg, ?_⟩
  rw [stochasticHessianJstarRealized_eq_source_max, max_le_iff]
  have hmax := hreg.2.2
  rw [stochasticHessianJstarRealized_eq_source_max, max_le_iff] at hmax
  exact and_iff_left hmax.2

theorem theorem_4_15_directional_control_does_not_control_source_max :
    ∃ (Jhat J bound : ℝ), J ≤ bound ∧ ¬ max Jhat J ≤ bound := by
  exact ⟨1, 0, 0, le_rfl, by norm_num⟩

/- Source-boundary note: Theorem 4.15 prints expectations defining J*, J,
   and Jhat plus partial quotients/square roots and a big-O remainder.  The
   rate clauses below are conditional on a fixed curvature envelope in the
   positive branch and on one epsilon-indexed family with uniform theta
   constants in the otherwise branch.  Thus neither clause manufactures runs,
   and the otherwise eta scale is the Appendix B.4 scale (without `/ T`). -/
def theorem_4_15_source_rate_consequences {ξ : Type*}
    [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (σ s : ℝ) (hfinite : P.objective.HasFiniteInfimum) : Prop :=
  let Δ := sourceObjectiveInitialGap P.objective cfg.W0 hfinite
  (∀ _hthird : ThirdDerivativeBounded P.objective s,
    ∀ _hvariance : BoundedVariance P σ,
    ∀ Jstar : ℝ,
    theorem_4_15_positiveBranchPointwisePremise m n Jstar σ Δ →
    ∀ cfgForHorizon : ℕ → StochasticMuonConfig m n,
    (∀ N : ℕ, horizonDomain N →
      theorem_4_15_positiveRunRealizedForHorizon
        P cfgForHorizon cfg.W0 Jstar σ Δ s N) →
    theorem_4_15_positive_branch_rate_and_complexity
      P cfg Jstar σ Δ s cfgForHorizon) ∧
  (∀ _hthird : ThirdDerivativeBounded P.objective s,
    ∀ _hvariance : BoundedVariance P σ,
    ∀ C betaLower betaUpper etaLower etaUpper horizonLower horizonUpper : ℝ,
    ∃ accuracyScale : ℝ, 0 < accuracyScale ∧
      ∀ cfgForAccuracyHorizon : ℝ → ℕ → StochasticMuonConfig m n,
      (∃ ε₀ : ℝ, 0 < ε₀ ∧
        ∀ ε : ℝ, epsilonDomain ε → ε ≤ ε₀ →
        ∃ N : ℕ,
          theorem_4_15_otherwiseCorrectedSourceSmallJReindexedRunForAccuracyHorizon P
            cfgForAccuracyHorizon cfg.W0 σ Δ C s
            betaLower betaUpper etaLower etaUpper horizonLower horizonUpper
            accuracyScale ε N) →
      theorem_4_15_otherwise_branch_rate_and_complexity
        P cfg σ Δ C betaLower betaUpper etaLower etaUpper
          horizonLower horizonUpper accuracyScale cfgForAccuracyHorizon)

def theorem_4_15_source_boundary_corrected_statement {ξ : Type*}
    [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (σ η s : ℝ) (hfinite : P.objective.HasFiniteInfimum) : Prop :=
  let Δ := sourceObjectiveInitialGap P.objective cfg.W0 hfinite
  let hsrc := theorem_4_15_sourceDomain T η
  let rateConsequences := theorem_4_15_source_rate_consequences P cfg σ s hfinite
  hsrc →
  ∃ hwd : stochasticMuonExpectationsWellDefined P cfg T,
  ∃ hdom : theorem_4_15_base_rhsDomain cfg T Δ
      (stochasticHessianJstarRealized P cfg T hwd.2.2) σ η,
  (∃ R : ℝ → ℝ,
    AsymptoticUpperReal (fun _ => True) R
      (fun η' => theorem_4_15_remainderRate m n cfg s η')
      (theoremScope "Theorem 4.15 printed O(sr^(3/2)eta^2/(1-beta))" ["eta"]) ∧
    stochasticAverageNuclearGradientRealized P cfg T hwd.1 ≤
      theorem_4_15_base_rhs P cfg T Δ
        (stochasticHessianJstarRealized P cfg T hwd.2.2) σ η hdom +
        R η) ∧
    rateConsequences

def theorem_4_15_statement {ξ : Type*} [MeasurableSpace ξ] {m n : ℕ}
    (P : StochasticProblem ξ m n) (cfg : StochasticMuonConfig m n)
    (T : ℕ) (σ η s : ℝ) (hfinite : P.objective.HasFiniteInfimum) : Prop :=
  let hboundary := SourceScalarDomainBoundary (theorem_4_15_sourceDomain T η)
    (theorem_4_15_downstream_phase2_boundary P cfg T σ η s hfinite)
    (theorem_4_15_sourceDomainCorrectionNeeded P cfg T σ η s hfinite)
  hboundary ∧
    theorem_4_15_source_boundary_corrected_statement P cfg T σ η s hfinite

/- Appendix C.5 divides by `T` and `Dop` and unrolls an affine recurrence
   with contraction factor `1 - eta / Dop`.  These are partial source
   semantics, not additional assumptions on the objective. -/
def theorem_4_16_sourceDomain (T : ℕ) (η Dop : ℝ) : Prop :=
  horizonDomain T ∧ 0 < η ∧ η ≤ Dop

theorem theorem_4_16_sourceDomain_zero_false (η Dop : ℝ) :
    ¬ theorem_4_16_sourceDomain 0 η Dop := by
  simp [theorem_4_16_sourceDomain, horizonDomain]

/- Exact fixed-horizon fragment of the pre-correction statement.  Keeping it
   private records the falsified interface without leaving it on the active
   source/public route. -/
private def theorem_4_16_preCorrectionFixedHorizonObligation {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T : ℕ) (s η Dop : ℝ) (hfinite : P.HasFiniteInfimum) : Prop :=
  let Δ := sourceObjectiveInitialGap P cfg.W0 hfinite
  let Jtilde := hessianDirectionalWeightedAverage P cfg T η Dop
  (∃ hdom : theorem_4_16_rhsDomain m n T Δ Jtilde s η Dop,
    sourceObjectiveGapAt P cfg T hfinite ≤
      theorem_4_16_rhs P cfg T Δ Jtilde s η Dop hdom) ∧
  Jtilde ≤ ((T : ℝ)⁻¹) *
    Finset.sum (Finset.range T) (fun t => |hessianDirectionalTerm P cfg t|)

/- A compiled counterexample to the exact former obligation, with every
   public Theorem 4.16 hypothesis inhabited.  The constant zero objective and
   zero run satisfy star convexity, third-derivative boundedness, distance
   boundedness, and the vacuous constant-step premise at `T = 0`; nevertheless
   the former conclusion would contain `horizonDomain 0`. -/
private theorem theorem_4_16_preCorrection_zero_horizon_counterexample :
    ∃ (P : Objective 0 0) (cfg : DeterministicMuonConfig 0 0)
      (Wstar : Mat 0 0) (s η Dop : ℝ) (hfinite : P.HasFiniteInfimum),
      StarConvex P Wstar ∧
      ThirdDerivativeBounded P s ∧
      BoundedOperatorDistance P cfg 0 Wstar Dop ∧
      (∀ t ∈ Finset.range 0, cfg.eta t = η) ∧
      ¬ theorem_4_16_preCorrectionFixedHorizonObligation
        P cfg 0 s η Dop hfinite := by
  let P : Objective 0 0 := ⟨fun _ => 0⟩
  let cfg : DeterministicMuonConfig 0 0 := { W0 := 0, eta := fun _ => 0 }
  have hfinite : P.HasFiniteInfimum := by
    refine ⟨0, ?_⟩
    rintro y ⟨W, rfl⟩
    simp [P]
  have hstar : StarConvex P 0 := by
    constructor
    · simp [Objective.IsMinimizer, Objective.fStar, P]
    · intro W
      have hW : W = 0 := Subsingleton.elim _ _
      subst W
      simp [P, Objective.grad, objectiveGradient, Objective.fStar,
        frobeniusInner]
  have hthird : ThirdDerivativeBounded P 0 := by
    constructor
    · simpa [P, vectorizedObjective] using
        (contDiff_const : ContDiff ℝ 3 (fun _ : Mat 0 0 => (0 : ℝ)))
    · intro W
      simp [P, vectorizedObjective]
  have hbounded : BoundedOperatorDistance P cfg 0 0 0 := by
    intro t ht
    have ht0 : t = 0 := by simpa using ht
    subst t
    simp [P, cfg, spectralNorm]
  refine ⟨P, cfg, 0, 0, 0, 0, hfinite, hstar, hthird, hbounded, ?_, ?_⟩
  · simp
  · rintro ⟨⟨hdom, _hbound⟩, _haverage⟩
    exact (Nat.not_lt_zero 0) hdom.1

/- `sourceLogQuotDomain` alone permits a logarithm argument in `(0, 1]`.
   Values below one make the printed step negative, while equality to one
   makes it zero and leaves contraction factor one.  The strict lower bound
   below is therefore the exact schedule-side condition that realizes the
   positive contracting step used in Appendix C.5. -/
def theorem_4_16_logScheduleDomain (T : ℕ) (Δ Jtilde Dop : ℝ) : Prop :=
  horizonDomain T ∧ 0 < Dop ∧
    sourceLogQuotDomain ((T : ℝ) * Δ) (Dop ^ 2 * Jtilde) ∧
    1 < sourceQuot ((T : ℝ) * Δ) (Dop ^ 2 * Jtilde)

def theorem_4_16_logEtaRealized (T : ℕ) (Δ Jtilde Dop : ℝ)
    (hlog : theorem_4_16_logScheduleDomain T Δ Jtilde Dop) : ℝ :=
  min (Dop / (T : ℝ) *
    realizedSourceLogQuot ((T : ℝ) * Δ) (Dop ^ 2 * Jtilde) hlog.2.2.1) Dop

theorem theorem_4_16_logEtaRealized_pos
    (T : ℕ) (Δ Jtilde Dop : ℝ)
    (hlog : theorem_4_16_logScheduleDomain T Δ Jtilde Dop) :
    0 < theorem_4_16_logEtaRealized T Δ Jtilde Dop hlog := by
  have hT : 0 < (T : ℝ) := by exact_mod_cast hlog.1
  have hlogPos :
      0 < realizedSourceLogQuot ((T : ℝ) * Δ) (Dop ^ 2 * Jtilde) hlog.2.2.1 := by
    simpa [realizedSourceLogQuot, sourceLogQuot] using Real.log_pos hlog.2.2.2
  unfold theorem_4_16_logEtaRealized
  exact lt_min (mul_pos (div_pos hlog.2.1 hT) hlogPos) hlog.2.1

theorem theorem_4_16_logEtaRealized_le
    (T : ℕ) (Δ Jtilde Dop : ℝ)
    (hlog : theorem_4_16_logScheduleDomain T Δ Jtilde Dop) :
    theorem_4_16_logEtaRealized T Δ Jtilde Dop hlog ≤ Dop := by
  unfold theorem_4_16_logEtaRealized
  exact min_le_right _ _

theorem theorem_4_16_logEtaRealized_sourceDomain
    (T : ℕ) (Δ Jtilde Dop : ℝ)
    (hlog : theorem_4_16_logScheduleDomain T Δ Jtilde Dop) :
    theorem_4_16_sourceDomain T
      (theorem_4_16_logEtaRealized T Δ Jtilde Dop hlog) Dop :=
  ⟨hlog.1, theorem_4_16_logEtaRealized_pos T Δ Jtilde Dop hlog,
    theorem_4_16_logEtaRealized_le T Δ Jtilde Dop hlog⟩

def theorem_4_16_logScheduleCorrectionNeeded (T : ℕ) (Δ Jtilde Dop : ℝ) : Prop :=
  horizonDomain T ∧ ¬ theorem_4_16_logScheduleDomain T Δ Jtilde Dop

def theorem_4_16_logScheduleSourceBoundary (T : ℕ) (Δ Jtilde Dop : ℝ) : Prop :=
  SourceScalarDomainBoundary (horizonDomain T)
    (theorem_4_16_logScheduleDomain T Δ Jtilde Dop)
    (theorem_4_16_logScheduleCorrectionNeeded T Δ Jtilde Dop)

def theorem_4_16_otherwiseLogScheduleDomain
    (m n T : ℕ) (Δ s Dop : ℝ) : Prop :=
  horizonDomain T ∧ 0 < Dop ∧
    sourceLogQuotDomain ((T : ℝ) ^ 2 * Δ)
      (Dop ^ 3 * s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3)) ∧
    1 < sourceQuot ((T : ℝ) ^ 2 * Δ)
      (Dop ^ 3 * s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3))

def theorem_4_16_otherwiseLogEtaRealized (m n : ℕ) (T : ℕ) (Δ s Dop : ℝ)
    (hlog : theorem_4_16_otherwiseLogScheduleDomain m n T Δ s Dop) : ℝ :=
  min (Dop / (T : ℝ) *
    realizedSourceLogQuot ((T : ℝ) ^ 2 * Δ)
      (Dop ^ 3 * s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3)) hlog.2.2.1) Dop

theorem theorem_4_16_otherwiseLogEtaRealized_pos
    (m n T : ℕ) (Δ s Dop : ℝ)
    (hlog : theorem_4_16_otherwiseLogScheduleDomain m n T Δ s Dop) :
    0 < theorem_4_16_otherwiseLogEtaRealized m n T Δ s Dop hlog := by
  have hT : 0 < (T : ℝ) := by exact_mod_cast hlog.1
  have hlogPos :
      0 < realizedSourceLogQuot ((T : ℝ) ^ 2 * Δ)
        (Dop ^ 3 * s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3)) hlog.2.2.1 := by
    simpa [realizedSourceLogQuot, sourceLogQuot] using Real.log_pos hlog.2.2.2
  unfold theorem_4_16_otherwiseLogEtaRealized
  exact lt_min (mul_pos (div_pos hlog.2.1 hT) hlogPos) hlog.2.1

theorem theorem_4_16_otherwiseLogEtaRealized_le
    (m n T : ℕ) (Δ s Dop : ℝ)
    (hlog : theorem_4_16_otherwiseLogScheduleDomain m n T Δ s Dop) :
    theorem_4_16_otherwiseLogEtaRealized m n T Δ s Dop hlog ≤ Dop := by
  unfold theorem_4_16_otherwiseLogEtaRealized
  exact min_le_right _ _

theorem theorem_4_16_otherwiseLogEtaRealized_sourceDomain
    (m n T : ℕ) (Δ s Dop : ℝ)
    (hlog : theorem_4_16_otherwiseLogScheduleDomain m n T Δ s Dop) :
    theorem_4_16_sourceDomain T
      (theorem_4_16_otherwiseLogEtaRealized m n T Δ s Dop hlog) Dop :=
  ⟨hlog.1, theorem_4_16_otherwiseLogEtaRealized_pos m n T Δ s Dop hlog,
    theorem_4_16_otherwiseLogEtaRealized_le m n T Δ s Dop hlog⟩

def theorem_4_16_otherwiseLogScheduleCorrectionNeeded
    (m n T : ℕ) (Δ s Dop : ℝ) : Prop :=
  horizonDomain T ∧ ¬ theorem_4_16_otherwiseLogScheduleDomain m n T Δ s Dop

def theorem_4_16_otherwiseLogScheduleSourceBoundary
    (m n T : ℕ) (Δ s Dop : ℝ) : Prop :=
  SourceScalarDomainBoundary (horizonDomain T)
    (theorem_4_16_otherwiseLogScheduleDomain m n T Δ s Dop)
    (theorem_4_16_otherwiseLogScheduleCorrectionNeeded m n T Δ s Dop)

def theorem_4_16_positiveDisplayedBound (m n : ℕ) (T : ℕ)
    (Δ Jtilde s Dop : ℝ) : ℝ :=
  Dop ^ 2 * Jtilde / (T : ℝ) +
    Dop ^ 2 * Jtilde / (2 * (T : ℝ)) *
      (sourceLogQuot ((T : ℝ) * Δ) (Dop ^ 2 * Jtilde)) ^ 2 +
    s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Dop ^ 3 /
      (6 * (T : ℝ) ^ 2) *
      (sourceLogQuot ((T : ℝ) * Δ) (Dop ^ 2 * Jtilde)) ^ 2

def theorem_4_16_branchDisplayedBoundRealized (m n : ℕ) (T : ℕ)
    (Δ Jtilde s Dop : ℝ)
    (hlog : theorem_4_16_logScheduleDomain T Δ Jtilde Dop) : ℝ :=
  Dop ^ 2 * Jtilde / (T : ℝ) +
    Dop ^ 2 * Jtilde / (2 * (T : ℝ)) *
      (realizedSourceLogQuot ((T : ℝ) * Δ) (Dop ^ 2 * Jtilde) hlog.2.2.1) ^ 2 +
    s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Dop ^ 3 /
      (6 * (T : ℝ) ^ 2) *
      (realizedSourceLogQuot ((T : ℝ) * Δ) (Dop ^ 2 * Jtilde) hlog.2.2.1) ^ 2

theorem theorem_4_16_branchDisplayedBoundRealized_eq
    (m n : ℕ) (T : ℕ) (Δ Jtilde s Dop : ℝ)
    (hlog : theorem_4_16_logScheduleDomain T Δ Jtilde Dop) :
    theorem_4_16_branchDisplayedBoundRealized m n T Δ Jtilde s Dop hlog =
      theorem_4_16_positiveDisplayedBound m n T Δ Jtilde s Dop :=
  rfl

def theorem_4_16_otherwiseCorrectedDisplayedBound
    (m n : ℕ) (T : ℕ) (Δ Jtilde s Dop : ℝ) : ℝ :=
  s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Dop ^ 3 / (T : ℝ) ^ 2 +
    Dop ^ 2 * Jtilde / (2 * (T : ℝ)) *
      (sourceLogQuot ((T : ℝ) ^ 2 * Δ)
        (Dop ^ 3 * s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3))) ^ 2 +
    s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Dop ^ 3 /
      (6 * (T : ℝ) ^ 2) *
    (sourceLogQuot ((T : ℝ) ^ 2 * Δ)
        (Dop ^ 3 * s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3))) ^ 2

def theorem_4_16_otherwiseCorrectedDisplayedBoundRealized
    (m n : ℕ) (T : ℕ) (Δ Jtilde s Dop : ℝ)
    (hlog : theorem_4_16_otherwiseLogScheduleDomain m n T Δ s Dop) : ℝ :=
  s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Dop ^ 3 / (T : ℝ) ^ 2 +
    Dop ^ 2 * Jtilde / (2 * (T : ℝ)) *
      (realizedSourceLogQuot ((T : ℝ) ^ 2 * Δ)
        (Dop ^ 3 * s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3))
        hlog.2.2.1) ^ 2 +
    s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Dop ^ 3 /
      (6 * (T : ℝ) ^ 2) *
      (realizedSourceLogQuot ((T : ℝ) ^ 2 * Δ)
        (Dop ^ 3 * s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3)) hlog.2.2.1) ^ 2

theorem theorem_4_16_otherwiseCorrectedDisplayedBoundRealized_eq
    (m n : ℕ) (T : ℕ) (Δ Jtilde s Dop : ℝ)
    (hlog : theorem_4_16_otherwiseLogScheduleDomain m n T Δ s Dop) :
    theorem_4_16_otherwiseCorrectedDisplayedBoundRealized
        m n T Δ Jtilde s Dop hlog =
      theorem_4_16_otherwiseCorrectedDisplayedBound
        m n T Δ Jtilde s Dop :=
  rfl

def theorem_4_16_positiveHorizonSchedule {m n : ℕ}
    (P : Objective m n) (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (W0 : Mat m n) (Δ Dop : ℝ) : Prop :=
  ∀ N : ℕ, horizonDomain N →
    let cfgN := cfgForHorizon N
    let JN := hessianDirectionalWeightedAverage P cfgN N (cfgN.eta 0) Dop
    cfgN.W0 = W0 ∧
      ∃ hlog : theorem_4_16_logScheduleDomain N Δ JN Dop,
        ∀ t ∈ Finset.range N,
          cfgN.eta t = theorem_4_16_logEtaRealized N Δ JN Dop hlog

def theorem_4_16_branchRegimeThresholdDomain
    (m n : ℕ) (s Dop : ℝ) : Prop :=
  sourceSqrtDomain s ∧
    sourceInvDomain Dop ∧
    sourceSqrtDomain (sourceInv Dop) ∧
    sourceSqrtDomain (sourceSqrt ((matrixRankBound m n : ℝ) ^ 3))

def theorem_4_16_branchRegimeThreshold
    (m n : ℕ) (s Dop ε : ℝ)
    (hdom : theorem_4_16_branchRegimeThresholdDomain m n s Dop) : ℝ :=
  let ⟨hs, hDopInv, hsDopInv, hsRankFourth⟩ := hdom
  realizedSourceSqrt s hs *
    realizedSourceSqrt (realizedSourceInv Dop hDopInv) hsDopInv *
      realizedSourceSqrt
        (realizedSourceSqrt ((matrixRankBound m n : ℝ) ^ 3)
          (rankCube_sourceSqrtDomain m n))
        hsRankFourth *
        Real.sqrt ε

def theorem_4_16_positiveBranchRegime {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T : ℕ) (s Dop : ℝ)
    (hdom : theorem_4_16_branchRegimeThresholdDomain m n s Dop) : Prop :=
  let Jtilde := hessianDirectionalWeightedAverage P cfg T (cfg.eta 0) Dop
  AsymptoticLowerReal epsilonDomain
    (fun _ => Jtilde)
    (fun ε => theorem_4_16_branchRegimeThreshold m n s Dop ε hdom)
    (theoremScope "Theorem 4.16 Jtilde lower branch" ["epsilon"])

def theorem_4_16_positiveRunForHorizon {m n : ℕ}
    (P : Objective m n) (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (W0 : Mat m n) (Δ s Dop : ℝ) (N : ℕ) : Prop :=
  horizonDomain N ∧
    let cfgN := cfgForHorizon N
    let JN := hessianDirectionalWeightedAverage P cfgN N (cfgN.eta 0) Dop
    cfgN.W0 = W0 ∧
      (∃ hlog : theorem_4_16_logScheduleDomain N Δ JN Dop,
        ∀ t ∈ Finset.range N,
          cfgN.eta t = theorem_4_16_logEtaRealized N Δ JN Dop hlog) ∧
      ∃ hregDom : theorem_4_16_branchRegimeThresholdDomain m n s Dop,
        theorem_4_16_positiveBranchRegime P cfgN N s Dop hregDom

theorem theorem_4_16_positiveRunForHorizon_step_regime {m n : ℕ}
    (P : Objective m n) (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (W0 : Mat m n) (Δ s Dop : ℝ) (N : ℕ)
    (hrun : theorem_4_16_positiveRunForHorizon
      P cfgForHorizon W0 Δ s Dop N) :
    0 < (cfgForHorizon N).eta 0 ∧ (cfgForHorizon N).eta 0 ≤ Dop := by
  unfold theorem_4_16_positiveRunForHorizon at hrun
  dsimp at hrun
  rcases hrun with ⟨hN, _hW0, ⟨hlog, heta⟩, _hregime⟩
  have hzero : 0 ∈ Finset.range N := Finset.mem_range.mpr hN
  rw [heta 0 hzero]
  exact ⟨theorem_4_16_logEtaRealized_pos N _ _ Dop hlog,
    theorem_4_16_logEtaRealized_le N _ _ Dop hlog⟩

def theorem_4_16_otherwiseHorizonSchedule {m n : ℕ}
    (_P : Objective m n) (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (W0 : Mat m n) (Δ s Dop : ℝ) : Prop :=
  ∀ N : ℕ, horizonDomain N →
    let cfgN := cfgForHorizon N
    cfgN.W0 = W0 ∧
      ∃ hlog : theorem_4_16_otherwiseLogScheduleDomain m n N Δ s Dop,
        ∀ t ∈ Finset.range N,
          cfgN.eta t = theorem_4_16_otherwiseLogEtaRealized m n N Δ s Dop hlog

def theorem_4_16_otherwiseBranchRegime {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T : ℕ) (s Dop : ℝ)
    (hdom : theorem_4_16_branchRegimeThresholdDomain m n s Dop) : Prop :=
  let Jtilde := hessianDirectionalWeightedAverage P cfg T (cfg.eta 0) Dop
  AsymptoticUpperReal epsilonDomain
    (fun _ => Jtilde)
    (fun ε => theorem_4_16_branchRegimeThreshold m n s Dop ε hdom)
    (theoremScope "Theorem 4.16 otherwise branch" ["epsilon"])

def theorem_4_16_otherwiseRunForHorizon {m n : ℕ}
    (P : Objective m n) (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (W0 : Mat m n) (Δ s Dop : ℝ) (N : ℕ) : Prop :=
  horizonDomain N ∧
    let cfgN := cfgForHorizon N
    cfgN.W0 = W0 ∧
      (∃ hlog : theorem_4_16_otherwiseLogScheduleDomain m n N Δ s Dop,
        ∀ t ∈ Finset.range N,
          cfgN.eta t = theorem_4_16_otherwiseLogEtaRealized m n N Δ s Dop hlog) ∧
      ∃ hregDom : theorem_4_16_branchRegimeThresholdDomain m n s Dop,
        theorem_4_16_otherwiseBranchRegime P cfgN N s Dop hregDom

theorem theorem_4_16_otherwiseRunForHorizon_step_regime {m n : ℕ}
    (P : Objective m n) (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (W0 : Mat m n) (Δ s Dop : ℝ) (N : ℕ)
    (hrun : theorem_4_16_otherwiseRunForHorizon
      P cfgForHorizon W0 Δ s Dop N) :
    0 < (cfgForHorizon N).eta 0 ∧ (cfgForHorizon N).eta 0 ≤ Dop := by
  unfold theorem_4_16_otherwiseRunForHorizon at hrun
  dsimp at hrun
  rcases hrun with ⟨hN, _hW0, ⟨hlog, heta⟩, _hregime⟩
  have hzero : 0 ∈ Finset.range N := Finset.mem_range.mpr hN
  rw [heta 0 hzero]
  exact ⟨theorem_4_16_otherwiseLogEtaRealized_pos m n N Δ s Dop hlog,
    theorem_4_16_otherwiseLogEtaRealized_le m n N Δ s Dop hlog⟩

def theorem_4_16_downstream_phase2_boundary {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T : ℕ) (s η Dop : ℝ) (hfinite : P.HasFiniteInfimum) : Prop :=
  let Δ := sourceObjectiveInitialGap P cfg.W0 hfinite
  let Jtilde := hessianDirectionalWeightedAverage P cfg T η Dop
  ∃ hdom : theorem_4_16_rhsDomain m n T Δ Jtilde s η Dop,
    0 < η ∧ η ≤ Dop

def theorem_4_16_sourceDomainCorrectionNeeded {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T : ℕ) (s η Dop : ℝ) (hfinite : P.HasFiniteInfimum) : Prop :=
  theorem_4_16_sourceDomain T η Dop ∧
    ¬ theorem_4_16_downstream_phase2_boundary P cfg T s η Dop hfinite

theorem theorem_4_16_sourceDomain_of_downstream {m n : ℕ}
    {P : Objective m n} {cfg : DeterministicMuonConfig m n}
    {T : ℕ} {s η Dop : ℝ} {hfinite : P.HasFiniteInfimum} :
    theorem_4_16_downstream_phase2_boundary P cfg T s η Dop hfinite →
      theorem_4_16_sourceDomain T η Dop := by
  rintro ⟨hdom, hηpos, hηle⟩
  exact ⟨hdom.1, hηpos, hηle⟩

theorem theorem_4_16_downstream_phase2_boundary_of_sourceDomain {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T : ℕ) (s η Dop : ℝ) (hfinite : P.HasFiniteInfimum)
    (hsrc : theorem_4_16_sourceDomain T η Dop) :
    theorem_4_16_downstream_phase2_boundary P cfg T s η Dop hfinite := by
  have hDop : 0 < Dop := lt_of_lt_of_le hsrc.2.1 hsrc.2.2
  refine ⟨⟨hsrc.1, ?_, rankCube_sourceSqrtDomain m n⟩, hsrc.2⟩
  exact ne_of_gt hDop

theorem theorem_4_16_source_domain_obligation {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T : ℕ) (s η Dop : ℝ) (hfinite : P.HasFiniteInfimum) :
    SourceScalarDomainBoundary (theorem_4_16_sourceDomain T η Dop)
      (theorem_4_16_downstream_phase2_boundary P cfg T s η Dop hfinite)
      (theorem_4_16_sourceDomainCorrectionNeeded P cfg T s η Dop hfinite) := by
  constructor
  · exact theorem_4_16_sourceDomain_of_downstream
  · intro hsrc
    exact Or.inl
      (theorem_4_16_downstream_phase2_boundary_of_sourceDomain
        P cfg T s η Dop hfinite hsrc)

theorem theorem_4_16_contraction_of_sourceDomain
    {T : ℕ} {η Dop : ℝ} (hsrc : theorem_4_16_sourceDomain T η Dop) :
    0 ≤ 1 - η / Dop ∧ 1 - η / Dop < 1 := by
  have hDop : 0 < Dop := lt_of_lt_of_le hsrc.2.1 hsrc.2.2
  have hratioPos : 0 < η / Dop := div_pos hsrc.2.1 hDop
  have hratioLe : η / Dop ≤ 1 := (div_le_one hDop).2 hsrc.2.2
  constructor <;> linarith

def theorem_4_16_log_schedule_downstream_phase2_boundary {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T : ℕ) (η Dop : ℝ) (hfinite : P.HasFiniteInfimum) : Prop :=
  let Δ := sourceObjectiveInitialGap P cfg.W0 hfinite
  let Jtilde := hessianDirectionalWeightedAverage P cfg T η Dop
  theorem_4_16_logScheduleSourceBoundary T Δ Jtilde Dop

def theorem_4_16_otherwise_log_schedule_downstream_phase2_boundary {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (T : ℕ) (s _η Dop : ℝ) (hfinite : P.HasFiniteInfimum) : Prop :=
  let Δ := sourceObjectiveInitialGap P cfg.W0 hfinite
  theorem_4_16_otherwiseLogScheduleSourceBoundary m n T Δ s Dop

/- A rate-domain run is valid at its own horizon.  In particular, the
   bounded-distance contract is not borrowed from the unrelated fixed horizon
   appearing in the registered theorem invocation. -/
def theorem_4_16_positiveSourceRunForHorizon {m n : ℕ}
    (P : Objective m n) (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (Wstar W0 : Mat m n) (Δ s Dop : ℝ) (N : ℕ) : Prop :=
  BoundedOperatorDistance P (cfgForHorizon N) N Wstar Dop ∧
    theorem_4_16_positiveRunForHorizon
      P cfgForHorizon W0 Δ s Dop N

def theorem_4_16_otherwiseSourceRunForHorizon {m n : ℕ}
    (P : Objective m n) (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (Wstar W0 : Mat m n) (Δ s Dop : ℝ) (N : ℕ) : Prop :=
  BoundedOperatorDistance P (cfgForHorizon N) N Wstar Dop ∧
    theorem_4_16_otherwiseRunForHorizon
      P cfgForHorizon W0 Δ s Dop N

/- The branch comparison in Appendix C.5 is uniform over the horizon family.
   A pointwise `AsymptoticUpperReal` or `AsymptoticLowerReal` witness at each
   `N` is insufficient because its hidden constant may depend on `N`.  These
   predicates expose one family constant and one threshold.  They deliberately
   contain only the paper's Jtilde comparison: logarithmic envelopes are proof
   consequences when the fixed scalar parameters are nondegenerate and must
   not be smuggled into the source-facing branch premise. -/
def theorem_4_16_positiveFamilyBranchRegime {m n : ℕ}
    (P : Objective m n) (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (Wstar W0 : Mat m n) (Δ s Dop : ℝ) : Prop :=
  ∃ C : ℝ, ∃ N₀ : ℕ, 0 < C ∧
    ∀ N : ℕ,
      theorem_4_16_positiveSourceRunForHorizon P cfgForHorizon
        Wstar W0 Δ s Dop N →
      N₀ ≤ N →
      let JN := hessianDirectionalWeightedAverage P (cfgForHorizon N) N
        ((cfgForHorizon N).eta 0) Dop
      0 ≤ JN ∧
        s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Dop ≤
          C * (N : ℝ) * JN

def theorem_4_16_otherwiseFamilyBranchRegime {m n : ℕ}
    (P : Objective m n) (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (Wstar W0 : Mat m n) (Δ s Dop : ℝ) : Prop :=
  ∃ C : ℝ, ∃ N₀ : ℕ, 0 < C ∧
    ∀ N : ℕ,
      theorem_4_16_otherwiseSourceRunForHorizon P cfgForHorizon
        Wstar W0 Δ s Dop N →
      N₀ ≤ N →
      let JN := hessianDirectionalWeightedAverage P (cfgForHorizon N) N
        ((cfgForHorizon N).eta 0) Dop
      0 ≤ JN ∧
        JN * Dop ^ 2 * (N : ℝ) ≤
          C * (s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Dop ^ 3)

/- The positive displayed formula is a derived obligation, not a source
   assumption.  The otherwise formula is deliberately eventual: its corrected
   quadratic term can only be enlarged after the family regime supplies the
   explicit pointwise fact `0 ≤ JN`. -/
def theorem_4_16_positiveDisplayedBoundFamily {m n : ℕ}
    (P : Objective m n) (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (Wstar W0 : Mat m n) (Δ s Dop : ℝ)
    (hfinite : P.HasFiniteInfimum) : Prop :=
  ∀ N : ℕ,
    theorem_4_16_positiveSourceRunForHorizon P cfgForHorizon
      Wstar W0 Δ s Dop N →
    sourceObjectiveGapAt P (cfgForHorizon N) N hfinite ≤
      theorem_4_16_positiveDisplayedBound m n N Δ
        (hessianDirectionalWeightedAverage P (cfgForHorizon N) N
          ((cfgForHorizon N).eta 0) Dop) s Dop

def theorem_4_16_otherwiseCorrectedDisplayedBoundEventually {m n : ℕ}
    (P : Objective m n) (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (Wstar W0 : Mat m n) (Δ s Dop : ℝ)
    (hfinite : P.HasFiniteInfimum) : Prop :=
  ∃ N₀ : ℕ, ∀ N : ℕ,
      theorem_4_16_otherwiseSourceRunForHorizon P cfgForHorizon
        Wstar W0 Δ s Dop N →
      N₀ ≤ N →
      sourceObjectiveGapAt P (cfgForHorizon N) N hfinite ≤
        theorem_4_16_otherwiseCorrectedDisplayedBound m n N Δ
          (hessianDirectionalWeightedAverage P (cfgForHorizon N) N
            ((cfgForHorizon N).eta 0) Dop) s Dop

def theorem_4_16_positiveFullScaleDomain
    (m n : ℕ) (s Dop : ℝ) : Prop :=
  0 < s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Dop

def theorem_4_16_positiveFullScaleCorrectionNeeded
    (m n : ℕ) (s Dop : ℝ) : Prop :=
  s * Real.sqrt ((matrixRankBound m n : ℝ) ^ 3) * Dop = 0

def theorem_4_16_positiveFullScaleSourceBoundary
    (m n : ℕ) (s Dop : ℝ) : Prop :=
  SourceScalarDomainBoundary True
    (theorem_4_16_positiveFullScaleDomain m n s Dop)
    (theorem_4_16_positiveFullScaleCorrectionNeeded m n s Dop)

/- The positive precision claim needs a scalar horizon crossing independently
   of the analytic formula bound.  This contract contains only the corrected
   scalar display and the claimed horizon scale; in particular it contains no
   objective-gap conclusion. -/
def theorem_4_16_positiveScalarCrossing {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (Wstar : Mat m n) (Δ s Dop : ℝ)
    (cfgForHorizon : ℕ → DeterministicMuonConfig m n) : Prop :=
  ∃ k : ℕ, ∃ C ε₀ : ℝ,
    0 < C ∧ 0 < ε₀ ∧
      ConstantRespectsScope
        (theoremScope "Theorem 4.16 positive-Jtilde scalar crossing" ["epsilon"]) C ∧
      ∀ ε : ℝ, epsilonDomain ε → ε ≤ ε₀ →
        ∃ N : ℕ,
          theorem_4_16_positiveSourceRunForHorizon P cfgForHorizon
            Wstar cfg.W0 Δ s Dop N ∧
          theorem_4_16_positiveDisplayedBound m n N Δ
              (hessianDirectionalWeightedAverage P (cfgForHorizon N) N
                ((cfgForHorizon N).eta 0) Dop) s Dop ≤ ε ∧
          (N : ℝ) ≤ C * (accuracyPolylogEnvelope k ε *
            theorem_4_16_complexityRate m n
              (hessianDirectionalWeightedAverage P (cfgForHorizon N) N
                ((cfgForHorizon N).eta 0) Dop) Dop ε)

def theorem_4_16_positive_branch_rate_and_complexity {m n : ℕ}
    (P : Objective m n) (cfg : DeterministicMuonConfig m n)
    (Wstar : Mat m n) (Δ s Dop : ℝ)
    (cfgForHorizon : ℕ → DeterministicMuonConfig m n)
    (hfinite : P.HasFiniteInfimum) : Prop :=
  theorem_4_16_positiveFullScaleSourceBoundary m n s Dop ∧
  (theorem_4_16_positiveFullScaleDomain m n s Dop →
    TildeAsymptoticUpperNatOn
      (fun N => theorem_4_16_positiveSourceRunForHorizon P cfgForHorizon
          Wstar cfg.W0 Δ s Dop N ∧
        theorem_4_16_branchRateDomain m n
          (hessianDirectionalWeightedAverage P (cfgForHorizon N) N
            ((cfgForHorizon N).eta 0) Dop) Dop N)
      (fun N _hN => sourceObjectiveGapAt P (cfgForHorizon N) N hfinite)
      (fun N hN => theorem_4_16_branchRateRealized m n
        (hessianDirectionalWeightedAverage P (cfgForHorizon N) N
          ((cfgForHorizon N).eta 0) Dop) Dop N hN.2)
      (theoremScope "Theorem 4.16 positive-Jtilde branch rate" ["T"])) ∧
  (theorem_4_16_positiveScalarCrossing P cfg Wstar Δ s Dop cfgForHorizon →
    TildeSourceHorizonObjectivePrecisionComplexityWithHorizonRate P hfinite cfgForHorizon
      (fun N => theorem_4_16_positiveSourceRunForHorizon P cfgForHorizon
        Wstar cfg.W0 Δ s Dop N)
      (fun N ε => theorem_4_16_complexityRate m n
        (hessianDirectionalWeightedAverage P (cfgForHorizon N) N
          ((cfgForHorizon N).eta 0) Dop) Dop ε)
      (theoremScope "Theorem 4.16 positive-Jtilde epsilon complexity" ["epsilon"]))

end SGD.Muon
end
