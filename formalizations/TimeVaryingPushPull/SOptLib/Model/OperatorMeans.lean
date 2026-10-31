import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open scoped ComplexOrder ContinuousFunctionalCalculus MatrixOrder Matrix.Norms.Operator NNReal

namespace SOptLib.OperatorMeansPrivate

private theorem log_mul_of_commute
    {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    (a b : A) (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b)
    (hab : Commute a b) :
    CFC.log (a * b) = CFC.log a + CFC.log b := by
  let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  have hlogcomm : Commute (CFC.log a) (CFC.log b) :=
    ((hab.cfc_real Real.log).symm.cfc_real Real.log).symm
  calc
    CFC.log (a * b) =
        CFC.log (NormedSpace.exp (CFC.log a + CFC.log b)) := by
      rw [NormedSpace.exp_add_of_commute hlogcomm,
        CFC.exp_log a ha, CFC.exp_log b hb]
    _ = CFC.log a + CFC.log b :=
      CFC.log_exp _ (IsSelfAdjoint.log.add IsSelfAdjoint.log)

private theorem rpow_eq_exp_smul_log
    {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
    [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    (a : A) (t : ℝ) (ha : IsStrictlyPositive a) :
    CFC.rpow a t = NormedSpace.exp (t • CFC.log a) := by
  have hlogcont : ContinuousOn Real.log (spectrum ℝ a) := by
    fun_prop (disch := intro x hx; exact ne_of_gt (ha.spectrum_pos hx))
  have hself : IsSelfAdjoint (t • CFC.log a) := by
    rw [CFC.log, ← cfc_const_mul (R := ℝ) t Real.log a (hf := hlogcont)]
    exact cfc_predicate _ a
  have hmulcont : ContinuousOn (fun x : ℝ => t * Real.log x) (spectrum ℝ a) := by
    fun_prop (disch := intro x hx; exact ne_of_gt (ha.spectrum_pos hx))
  have hexpcont : ContinuousOn Real.exp
      ((fun x : ℝ => t * Real.log x) '' spectrum ℝ a) :=
    Real.continuous_exp.continuousOn
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real ha.nonneg]
  rw [← CFC.real_exp_eq_normedSpace_exp hself]
  rw [CFC.log, ← cfc_const_mul (R := ℝ) t Real.log a (hf := hlogcont)]
  calc
    cfc (fun x : ℝ => x ^ t) a =
        cfc (fun x : ℝ => Real.exp (t * Real.log x)) a := by
      apply cfc_congr
      intro x hx
      change x ^ t = Real.exp (t * Real.log x)
      rw [Real.rpow_def_of_pos (ha.spectrum_pos hx)]
      congr 1
      ring
    _ = cfc Real.exp (cfc (fun x : ℝ => t * Real.log x) a) :=
      cfc_comp' (R := ℝ) Real.exp (fun x : ℝ => t * Real.log x) a
        (hg := hexpcont) (hf := hmulcont) (ha := ha.isSelfAdjoint)

private theorem rpow_mul_of_commute
    {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    (a b : A) (t : ℝ) (ha : IsStrictlyPositive a) (hb : IsStrictlyPositive b)
    (hab : Commute a b) :
    CFC.rpow (a * b) t = CFC.rpow a t * CFC.rpow b t := by
  let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  have hprod : IsStrictlyPositive (a * b) := (ha.commute_iff hb).mp hab
  have hlogcomm : Commute (CFC.log a) (CFC.log b) :=
    ((hab.cfc_real Real.log).symm.cfc_real Real.log).symm
  rw [rpow_eq_exp_smul_log (a * b) t hprod,
    rpow_eq_exp_smul_log a t ha, rpow_eq_exp_smul_log b t hb,
    log_mul_of_commute a b ha hb hab, smul_add]
  exact NormedSpace.exp_add_of_commute ((hlogcomm.smul_left t).smul_right t)

end SOptLib.OperatorMeansPrivate

namespace Matrix

-- Generalization plan (G0):
-- concept/name: binary weighted Kubo--Ando geometric mean of finite real matrices,
--   named `Matrix.binaryWeightedGeometricMean`; orig was `binaryWeightedGeometricMean`
-- generality used: arbitrary finite index type with decidable equality, two real square
--   matrices, and a real weight; positivity and a unit-interval weight are deliberately
--   absent because Mathlib's continuous functional calculus is totalized
-- portable call pattern: full-matrix adaptive-gradient, matrix multiplicative-weights,
--   and operator-interpolation proofs change the finite dimension, positive matrices,
--   and weight while using the same perspective object and its positivity, endpoint,
--   commuting-evaluation, and monotonicity specifications
-- counterargument checked: although the body is one formula, it is the standard
--   noncommutative perspective defining the Kubo--Ando weighted geometric mean, and its
--   surrounding positivity, endpoint, commuting-evaluation, and joint-monotonicity API
--   makes it a stable mathematical object rather than paper-local caller syntax
-- coverage search: symbol searches for "binary weighted operator geometric mean positive
--   matrices perspective" and "matrix geometric mean positive definite real power
--   congruence" found only the Shampoo-local definition and its theorems; Mathlib semantic
--   search found no named finite-matrix weighted geometric mean, so coverage is absent
-- minimal hypotheses: `Fintype` and `DecidableEq` are exactly those used by finite-matrix
--   multiplication and Hermitian continuous functional calculus; no positivity is needed
--   by the definitional construction

/-- The binary weighted Kubo--Ando geometric mean of finite real square matrices.

This is the noncommutative perspective
`A^(1/2) * (A^(-1/2) * B * A^(-1/2))^t * A^(1/2)`, with all real powers
formed by Mathlib's continuous functional calculus.

Layer: Model | Concept: binary weighted Kubo--Ando geometric mean
Proof: (definitional construction; continuous-functional-calculus powers combined by the noncommutative matrix perspective)
Source: Kubo--Ando operator means and Mathlib Hermitian matrix continuous functional calculus for real powers
Used in: recursive finite-family operator interpolation inside matrix-preconditioned regret proofs, where positivity, endpoint evaluation, commuting reduction, and joint monotonicity are required
Book citation: book/research/Source.json#/definitions/0
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, matrix geometric-mean monotonicity support -/
noncomputable def binaryWeightedGeometricMean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (t : ℝ) : Matrix ι ι ℝ :=
  let Aneg := cfc (R := ℝ) (p := IsSelfAdjoint)
    (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) A
  let Ahalf := cfc (R := ℝ) (p := IsSelfAdjoint)
    (fun x : ℝ => x ^ (1 / 2 : ℝ)) A
  Ahalf * cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ t)
    (Aneg * B * Aneg) * Ahalf

/-- The binary weighted geometric mean unfolds to its CFC matrix-perspective formula.

Layer: Model | Gap: Level 0 (defining formula for the binary weighted Kubo--Ando geometric mean)
Proof: by rfl after unfolding `Matrix.binaryWeightedGeometricMean`
Source: Kubo--Ando operator means and Mathlib Hermitian matrix continuous functional calculus for real powers
Used in: expanding the operator mean when proving positive definiteness, endpoint identities, commuting evaluation, and Löwner-order monotonicity for matrix preconditioners
Book citation: book/research/Source.json#/definitions/0
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, matrix geometric-mean monotonicity support -/
@[simp]
theorem binaryWeightedGeometricMean_def {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (t : ℝ) :
    binaryWeightedGeometricMean A B t =
      let Aneg := cfc (R := ℝ) (p := IsSelfAdjoint)
        (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) A
      let Ahalf := cfc (R := ℝ) (p := IsSelfAdjoint)
        (fun x : ℝ => x ^ (1 / 2 : ℝ)) A
      Ahalf * cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ t)
        (Aneg * B * Aneg) * Ahalf :=
  rfl

/-- At weight zero, the binary weighted geometric mean is its left endpoint.

Layer: Model | Gap: Level 0 (zero-weight endpoint of the binary weighted Kubo--Ando geometric mean)
Proof: the middle CFC real power at exponent zero is the identity, after which the two outer half-powers multiply back to the positive-semidefinite left input
Source: Mathlib continuous-functional-calculus real-power zero, addition, and one laws
Used in: endpoint cases of operator-mean monotonicity and recursive finite-family interpolation
Book citation: book/research/Source.json#/definitions/0
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, matrix geometric-mean monotonicity support -/
@[simp]
theorem binaryWeightedGeometricMean_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (hA : A.PosSemidef) (hB : B.IsHermitian) :
    binaryWeightedGeometricMean A B 0 = A := by
  let Aneg := cfc (R := ℝ) (p := IsSelfAdjoint)
    (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) A
  let Ahalf := cfc (R := ℝ) (p := IsSelfAdjoint)
    (fun x : ℝ => x ^ (1 / 2 : ℝ)) A
  have hAneg_self : IsSelfAdjoint Aneg := by
    dsimp only [Aneg]
    cfc_tac
  have hAneg_conjTranspose : Matrix.conjTranspose Aneg = Aneg := hAneg_self
  have hmiddle_self : IsSelfAdjoint (Aneg * B * Aneg) := by
    show Matrix.conjTranspose (Aneg * B * Aneg) = Aneg * B * Aneg
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hAneg_conjTranspose, hB, Matrix.mul_assoc]
  change Ahalf *
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (0 : ℝ))
        (Aneg * B * Aneg) * Ahalf = A
  simp_rw [Real.rpow_zero]
  rw [cfc_const_one ℝ (Aneg * B * Aneg) hmiddle_self, mul_one]
  change cfc (R := ℝ) (p := IsSelfAdjoint)
      (fun x : ℝ => x ^ (1 / 2 : ℝ)) A *
    cfc (R := ℝ) (p := IsSelfAdjoint)
      (fun x : ℝ => x ^ (1 / 2 : ℝ)) A = A
  rw [← CFC.rpow_eq_cfc_real (a := A) (y := (1 / 2 : ℝ)) hA.nonneg,
    ← CFC.sqrt_eq_rpow, CFC.sqrt_mul_sqrt_self A hA.nonneg]

end Matrix

namespace Matrix

-- Generalization plan (G0):
-- concept/name: commuting evaluation of the binary weighted Kubo--Ando geometric mean;
--   orig was `Shampoo.binaryWeightedGeometricMean_eq_rpow_mul_of_commute`
-- generality used: arbitrary finite index type with decidable equality, two positive-definite
--   real square matrices, an unrestricted real weight, and a `Commute` hypothesis
-- portable call pattern: full-matrix adaptive-gradient, matrix multiplicative-weights, and
--   operator-interpolation proofs vary the finite dimension, positive-definite matrices, and
--   weight while reducing the same binary operator mean to complementary commuting powers
-- counterargument checked: this is not paper-local traceability or a caller-side rewrite;
--   it is the standard commutative specification theorem for the named noncommutative mean,
--   and it combines conjugation, iterated-power, product-power, and exponent-addition laws
-- coverage search: queries for "binary weighted geometric mean equals complementary real
--   powers product commuting positive definite matrices" and "weighted geometric mean of
--   commuting positive definite matrices equals product of powers" found the staged mean API,
--   Mathlib CFC power laws, and `CFC.rpow_mul_of_commute`, but no full evaluation theorem
-- minimal hypotheses: positive definiteness of both inputs supplies all negative powers and
--   product strict positivity; commutation is pointwise and no unit-interval bound on the
--   weight is used

/-- For commuting positive-definite real matrices, the binary weighted geometric mean is the
product of the complementary real powers of its inputs.

Layer: Model | Gap: Level 1 (commuting evaluation of the binary weighted Kubo--Ando geometric mean)
Proof: commute the inverse half-power through the right input, distribute the middle CFC power over the resulting positive product, collapse the iterated inverse power, and combine the remaining powers of the left input
Source: Kubo--Ando operator means; Mathlib `CFC.rpow_add`, `CFC.rpow_rpow`, and commutation through continuous functional calculus, together with `CFC.rpow_mul_of_commute`
Used in: normalized finite-family operator interpolation for Shampoo-style matrix and tensor preconditioners, where a recursive binary mean of commuting factors must be converted back to an explicit weighted power product
Book citation: book/research/Source.json#/definitions/0
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, commuting operator-mean evaluation -/
theorem binaryWeightedGeometricMean_eq_rpow_mul_of_commute
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (t : ℝ) (hA : A.PosDef) (hB : B.PosDef)
    (hAB : Commute A B) :
    binaryWeightedGeometricMean A B t =
      CFC.rpow A (1 - t) * CFC.rpow B t := by
  let H := CFC.rpow A (1 / 2 : ℝ)
  let Aneg := CFC.rpow A (-(1 / 2 : ℝ))
  let N := CFC.rpow A (-1 : ℝ)
  let Npow := CFC.rpow A (-t)
  let Q := CFC.rpow B t
  have hN : IsStrictlyPositive N := by
    dsimp only [N]
    exact hA.isStrictlyPositive.rpow A (-1 : ℝ)
  have hNB : Commute N B := by
    dsimp only [N, CFC.rpow]
    exact hAB.cfc_nnreal (fun x => x ^ (-1 : ℝ))
  have hmiddle : IsStrictlyPositive (N * B) :=
    (hN.commute_iff hB.isStrictlyPositive).mp hNB
  have hAnegB : Commute Aneg B := by
    dsimp only [Aneg, CFC.rpow]
    exact hAB.cfc_nnreal (fun x => x ^ (-(1 / 2 : ℝ)))
  have hmiddle_eq : Aneg * B * Aneg = N * B := by
    calc
      Aneg * B * Aneg = (Aneg * Aneg) * B := by
        rw [mul_assoc, hAnegB.symm.eq, ← mul_assoc]
      _ = N * B := by
        congr 1
        dsimp only [Aneg, N]
        rw [show CFC.rpow A (-(1 / 2 : ℝ)) * CFC.rpow A (-(1 / 2 : ℝ)) =
            CFC.rpow A ((-(1 / 2 : ℝ)) + (-(1 / 2 : ℝ))) by
          simpa only [CFC.rpow_eq_pow] using
            (CFC.rpow_add (a := A) (x := -(1 / 2 : ℝ))
              (y := -(1 / 2 : ℝ)) hA.isUnit).symm]
        congr 1
        ring
  have hQH : Commute Q H := by
    dsimp only [Q, H, CFC.rpow]
    exact (hAB.cfc_nnreal (fun x => x ^ (1 / 2 : ℝ))).symm.cfc_nnreal
      (fun x => x ^ t)
  change
    cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ)) A *
        cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ t)
          (cfc (R := ℝ) (p := IsSelfAdjoint)
              (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) A * B *
            cfc (R := ℝ) (p := IsSelfAdjoint)
              (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) A) *
        cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ)) A =
      CFC.rpow A (1 - t) * Q
  have hHcfc :
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ)) A = H :=
    (CFC.rpow_eq_cfc_real hA.posSemidef.nonneg).symm
  have hAnegcfc :
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) A =
        Aneg :=
    (CFC.rpow_eq_cfc_real hA.posSemidef.nonneg).symm
  rw [hHcfc, hAnegcfc, hmiddle_eq,
    ← CFC.rpow_eq_cfc_real hmiddle.nonneg]
  change H * CFC.rpow (N * B) t * H = CFC.rpow A (1 - t) * Q
  rw [SOptLib.OperatorMeansPrivate.rpow_mul_of_commute N B t hN
    hB.isStrictlyPositive hNB]
  rw [show CFC.rpow (CFC.rpow A (-1 : ℝ)) t = CFC.rpow A ((-1 : ℝ) * t) by
    simpa only [CFC.rpow_eq_pow] using
      CFC.rpow_rpow A (-1 : ℝ) t (by norm_num) hA.isStrictlyPositive]
  rw [show (-1 : ℝ) * t = -t by ring]
  change H * (Npow * Q) * H = CFC.rpow A (1 - t) * Q
  calc
    H * (Npow * Q) * H = H * (Npow * (Q * H)) := by
      simp only [mul_assoc]
    _ = H * (Npow * (H * Q)) := by rw [hQH.eq]
    _ = (H * Npow * H) * Q := by simp only [mul_assoc]
    _ = CFC.rpow A (((1 / 2 : ℝ) + (-t)) + (1 / 2 : ℝ)) * Q := by
      dsimp only [H, Npow]
      rw [show CFC.rpow A (1 / 2 : ℝ) * CFC.rpow A (-t) =
          CFC.rpow A ((1 / 2 : ℝ) + (-t)) by
        simpa only [CFC.rpow_eq_pow] using
          (CFC.rpow_add (a := A) (x := (1 / 2 : ℝ)) (y := -t) hA.isUnit).symm]
      rw [show CFC.rpow A ((1 / 2 : ℝ) + (-t)) * CFC.rpow A (1 / 2 : ℝ) =
          CFC.rpow A (((1 / 2 : ℝ) + (-t)) + (1 / 2 : ℝ)) by
        simpa only [CFC.rpow_eq_pow] using
          (CFC.rpow_add (a := A) (x := (1 / 2 : ℝ) + (-t))
            (y := (1 / 2 : ℝ)) hA.isUnit).symm]
    _ = CFC.rpow A (1 - t) * Q := by
      congr 2
      ring

end Matrix

namespace MatrixBinaryWeightedGeometricMeanMono

private noncomputable def realMatrixComplexification
    {ι : Type u} [Fintype ι] [DecidableEq ι] :
    Matrix ι ι ℝ →⋆ₐ[ℝ] CStarMatrix ι ι ℂ :=
  let scalarCast : ℝ →⋆ₐ[ℝ] ℂ :=
    { toFun := fun r => (r : ℂ)
      map_one' := Complex.ofReal_one
      map_mul' := Complex.ofReal_mul
      map_zero' := Complex.ofReal_zero
      map_add' := Complex.ofReal_add
      commutes' := fun _ => rfl
      map_star' := fun r => by simp }
  let matrixCast : Matrix ι ι ℝ →⋆ₐ[ℝ] Matrix ι ι ℂ :=
    StarAlgHom.mk (AlgHom.mapMatrix scalarCast.toAlgHom)
      (by
        intro A
        change Matrix.map (star A) scalarCast = star (Matrix.map A scalarCast)
        ext i j
        simp [scalarCast, Matrix.star_eq_conjTranspose])
  let e : Matrix ι ι ℂ ≃⋆ₐ[ℝ] CStarMatrix ι ι ℂ :=
    (CStarMatrix.ofMatrixStarAlgEquiv (n := ι) (A := ℂ)).restrictScalars ℝ
  StarAlgHom.mk (e.toAlgEquiv.toAlgHom.comp matrixCast.toAlgHom)
    (by
      intro A
      change e (matrixCast (star A)) = star (e (matrixCast A))
      rw [map_star matrixCast, map_star e])


private theorem cstarMatrix_integral_mono_ae
    {X ι : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    [Fintype ι]
    {f g : X → CStarMatrix ι ι ℂ}
    (hf : MeasureTheory.Integrable f μ) (hg : MeasureTheory.Integrable g μ)
    (hfg : ∀ᵐ x ∂μ, f x ≤ g x) :
    (∫ x, f x ∂μ) ≤ ∫ x, g x ∂μ := by
  classical
  let h : X → CStarMatrix ι ι ℂ := fun x => g x - f x
  have hh : MeasureTheory.Integrable h μ := hg.sub hf
  have hh_nonneg : ∀ᵐ x ∂μ, 0 ≤ h x := by
    filter_upwards [hfg] with x hx
    exact sub_nonneg.mpr hx
  let e : Matrix ι ι ℂ ≃⋆ₐ[ℂ] CStarMatrix ι ι ℂ :=
    CStarMatrix.ofMatrixStarAlgEquiv
  let H : CStarMatrix ι ι ℂ := ∫ x, h x ∂μ
  have hH_self : IsSelfAdjoint H := by
    change star H = H
    calc
      star H = ∫ x, star (h x) ∂μ := by
        symm
        exact ContinuousLinearMap.integral_comp_comm
          (starL' ℝ : CStarMatrix ι ι ℂ ≃L[ℝ] CStarMatrix ι ι ℂ).toContinuousLinearMap hh
      _ = ∫ x, h x ∂μ := MeasureTheory.integral_congr_ae <|
        hh_nonneg.mono fun x hx => (IsSelfAdjoint.of_nonneg hx).star_eq
      _ = H := rfl
  let M : Matrix ι ι ℂ := e.symm H
  have hM_self : M.IsHermitian := by
    change star M = M
    calc
      star M = e.symm (star H) := (map_star e.symm H).symm
      _ = e.symm H := congrArg e.symm hH_self.star_eq
      _ = M := rfl
  have hM_psd : M.PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hM_self
    intro v
    letI : FiniteDimensional ℂ (CStarMatrix ι ι ℂ) :=
      (CStarMatrix.ofMatrixₗ (R := ℂ)).finiteDimensional
    let qComplexLinear : CStarMatrix ι ι ℂ →ₗ[ℂ] ℂ :=
      { toFun := fun N => dotProduct (star v) ((e.symm N : Matrix ι ι ℂ).mulVec v)
        map_add' := by
          intro N₁ N₂
          rw [map_add, Matrix.add_mulVec, dotProduct_add]
        map_smul' := by
          intro c N
          rw [map_smul, Matrix.smul_mulVec, dotProduct_smul]
          simp only [RingHom.id_apply] }
    let qComplex : CStarMatrix ι ι ℂ →L[ℂ] ℂ :=
      LinearMap.toContinuousLinearMap qComplexLinear
    let q : CStarMatrix ι ι ℂ →L[ℝ] ℝ :=
      { toFun := fun N => Complex.re (qComplex N)
        map_add' := by
          intro N₁ N₂
          rw [map_add, Complex.add_re]
        map_smul' := by
          intro r N
          change Complex.re (dotProduct (star v)
              ((e.symm (r • N) : Matrix ι ι ℂ).mulVec v)) =
            r * Complex.re (dotProduct (star v)
              ((e.symm N : Matrix ι ι ℂ).mulVec v))
          rw [Algebra.smul_def]
          rw [IsScalarTower.algebraMap_apply ℝ ℂ (CStarMatrix ι ι ℂ) r]
          rw [← Algebra.smul_def, map_smul, Matrix.smul_mulVec, dotProduct_smul]
          simp [Complex.mul_re]
        cont := Complex.reCLM.continuous.comp qComplex.continuous }
    have hq_nonneg_of_nonneg (N : CStarMatrix ι ι ℂ) (hN : 0 ≤ N) :
        0 ≤ q N := by
      have hMN : 0 ≤ e.symm N := by
        apply (map_le_map_iff e).mp
        simpa using hN
      have hquad := (Matrix.nonneg_iff_posSemidef.mp hMN).dotProduct_mulVec_nonneg v
      simpa [q, qComplex, qComplexLinear] using (Complex.nonneg_iff.mp hquad).1
    have hqH_nonneg : 0 ≤ q H := by
      have hq_integral : q H = ∫ x, q (h x) ∂μ := by
        symm
        exact ContinuousLinearMap.integral_comp_comm q hh
      let scalar : X → ℝ := fun x => if 0 ≤ h x then q (h x) else 0
      have hscalar_nonneg : ∀ x, 0 ≤ scalar x := by
        intro x
        simp only [scalar]
        split_ifs with hx
        · exact hq_nonneg_of_nonneg (h x) hx
        · exact le_rfl
      have hscalar_ae : (fun x => q (h x)) =ᵐ[μ] scalar := by
        filter_upwards [hh_nonneg] with x hx
        simp [scalar, hx]
      rw [hq_integral, MeasureTheory.integral_congr_ae hscalar_ae]
      exact MeasureTheory.integral_nonneg hscalar_nonneg
    apply Complex.nonneg_iff.mpr
    constructor
    · simpa [q, qComplex, qComplexLinear, M] using hqH_nonneg
    · simpa using (hM_self.im_star_dotProduct_mulVec_self v).symm
  have hM_nonneg : 0 ≤ M := Matrix.nonneg_iff_posSemidef.mpr hM_psd
  have hH_nonneg : 0 ≤ H := by
    have heM : e 0 ≤ e M := (map_le_map_iff e).2 hM_nonneg
    simpa [M] using heM
  rw [← sub_nonneg, ← MeasureTheory.integral_sub hg hf]
  exact hH_nonneg

private theorem cfc_rpowIntegrand₀₁_eq_resolvent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι ℝ) (p s : ℝ) (hX : X.PosSemidef) (hs : 0 < s) :
    cfc (R := ℝ) (p := IsSelfAdjoint) (Real.rpowIntegrand₀₁ p s) X =
      (s ^ p) • ((s⁻¹) • (1 : Matrix ι ι ℝ) -
        (s • (1 : Matrix ι ι ℝ) + X)⁻¹) := by
  have hnonzero : ∀ x ∈ spectrum ℝ X, s + x ≠ 0 := by
    intro x hx
    have hx_nonneg : 0 ≤ x := by
      rw [hX.1.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      exact hX.eigenvalues_nonneg i
    exact ne_of_gt (add_pos_of_pos_of_nonneg hs hx_nonneg)
  change cfc (R := ℝ) (p := IsSelfAdjoint)
      (fun x : ℝ => (s ^ p) * (s⁻¹ - (s + x)⁻¹)) X = _
  have hcont_add :
      ContinuousOn (fun x : ℝ => s + x) (spectrum ℝ X) :=
    continuousOn_const.add continuousOn_id
  have hcont_inv :
      ContinuousOn (fun x : ℝ => (s + x)⁻¹) (spectrum ℝ X) :=
    hcont_add.inv₀ hnonzero
  have hcont_diff :
      ContinuousOn (fun x : ℝ => s⁻¹ - (s + x)⁻¹) (spectrum ℝ X) :=
    continuousOn_const.sub hcont_inv
  have hconst :
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun _ : ℝ => s⁻¹) X =
        (s⁻¹) • (1 : Matrix ι ι ℝ) := by
    rw [cfc_const (R := ℝ) (p := IsSelfAdjoint) s⁻¹ X hX.1]
    simp [Algebra.smul_def]
  have hadd :
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => s + x) X =
        s • (1 : Matrix ι ι ℝ) + X := by
    rw [cfc_const_add (R := ℝ) (p := IsSelfAdjoint) s (fun x : ℝ => x) X
      continuousOn_id hX.1]
    rw [cfc_id' (p := IsSelfAdjoint) ℝ X hX.1]
    simp [Algebra.smul_def]
  have hinv :
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => (s + x)⁻¹) X =
        (s • (1 : Matrix ι ι ℝ) + X)⁻¹ := by
    rw [cfc_inv (p := IsSelfAdjoint) (f := fun x : ℝ => s + x) (a := X)
      hnonzero hcont_add hX.1]
    rw [hadd]
    exact (Matrix.nonsing_inv_eq_ringInverse
      (A := s • (1 : Matrix ι ι ℝ) + X)).symm
  calc
    cfc (R := ℝ) (p := IsSelfAdjoint)
        (fun x : ℝ => (s ^ p) * (s⁻¹ - (s + x)⁻¹)) X =
        (s ^ p) • cfc (R := ℝ) (p := IsSelfAdjoint)
          (fun x : ℝ => s⁻¹ - (s + x)⁻¹) X :=
      cfc_const_mul (R := ℝ) (p := IsSelfAdjoint) (s ^ p)
        (fun x : ℝ => s⁻¹ - (s + x)⁻¹) X hcont_diff
    _ = (s ^ p) •
        (cfc (R := ℝ) (p := IsSelfAdjoint) (fun _ : ℝ => s⁻¹) X -
          cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => (s + x)⁻¹) X) := by
      rw [cfc_sub (R := ℝ) (p := IsSelfAdjoint)
        (fun _ : ℝ => s⁻¹) (fun x : ℝ => (s + x)⁻¹) X
        continuousOn_const hcont_inv]
    _ = (s ^ p) • ((s⁻¹) • (1 : Matrix ι ι ℝ) -
        (s • (1 : Matrix ι ι ℝ) + X)⁻¹) := by rw [hconst, hinv]

-- Generalization plan (G0):
-- concept/name: unit-weight endpoint of the binary weighted Kubo--Ando geometric mean;
--   orig was `Shampoo.binaryWeightedGeometricMean_one`
-- generality used: arbitrary finite index type with decidable equality, a positive-definite
--   left real square matrix, and a positive-semidefinite right real square matrix
-- portable call pattern: full-matrix adaptive-gradient, matrix multiplicative-weights,
--   and operator-interpolation proofs vary the finite dimension and endpoint matrices while
--   using the same unit-weight identity to close a boundary case
-- counterargument checked: this is an endpoint specification of the already named operator
--   mean rather than paper-local traceability; it is not a pure rename because its proof
--   combines CFC first-power evaluation, positive-semidefinite congruence, and cancellation
--   of inverse half-powers
-- coverage search: symbol searches for "binary weighted operator geometric mean equals right
--   input at weight one positive definite" and "matrix geometric mean one equals second
--   endpoint" found only the Shampoo-local candidate and the staged definition/zero endpoint;
--   Mathlib semantic search returned scalar mean inequalities, so coverage is absent
-- minimal hypotheses: positive definiteness of the left input supplies invertibility for the
--   opposite half-powers; the source's right-input positive definiteness is weakened to
--   positive semidefiniteness, exactly what the middle first-power evaluation requires

/-- At weight one, the binary weighted geometric mean is its right endpoint.

Layer: Model | Gap: Level 0 (unit-weight endpoint of the binary weighted Kubo--Ando geometric mean)
Proof: evaluate the middle CFC real power at one, reassociate the perspective product, and cancel the positive-definite left input's opposite half-powers with `CFC.rpow_mul_rpow_neg` and `CFC.rpow_neg_mul_rpow`
Source: Mathlib continuous-functional-calculus real-power one and opposite-power cancellation laws, together with positive-semidefinite matrix congruence
Used in: boundary cases of joint operator-mean monotonicity and recursive finite-family interpolation for matrix and tensor preconditioners
Book citation: book/research/Source.json#/definitions/0
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, matrix geometric-mean monotonicity support -/
@[simp]
private theorem binaryWeightedGeometricMean_one_aux {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (hA : A.PosDef) (hB : B.PosSemidef) :
    Matrix.binaryWeightedGeometricMean A B 1 = B := by
  let Aneg := cfc (R := ℝ) (p := IsSelfAdjoint)
    (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) A
  let Ahalf := cfc (R := ℝ) (p := IsSelfAdjoint)
    (fun x : ℝ => x ^ (1 / 2 : ℝ)) A
  have hAneg : Aneg.PosDef := by
    rw [show Aneg = A ^ (-(1 / 2 : ℝ)) by
      exact (CFC.rpow_eq_cfc_real hA.posSemidef.nonneg).symm]
    exact Matrix.isStrictlyPositive_iff_posDef.mp
      (hA.isStrictlyPositive.rpow A (-(1 / 2 : ℝ)))
  have hAneg_self : Matrix.conjTranspose Aneg = Aneg := hAneg.1
  have hmiddle : (Aneg * B * Aneg).PosSemidef := by
    simpa only [hAneg_self] using hB.conjTranspose_mul_mul_same Aneg
  have hhalf_neg : Ahalf * Aneg = 1 := by
    rw [show Ahalf = A ^ (1 / 2 : ℝ) by
      exact (CFC.rpow_eq_cfc_real hA.posSemidef.nonneg).symm]
    rw [show Aneg = A ^ (-(1 / 2 : ℝ)) by
      exact (CFC.rpow_eq_cfc_real hA.posSemidef.nonneg).symm]
    exact CFC.rpow_mul_rpow_neg (1 / 2 : ℝ) hA.isStrictlyPositive
  have hneg_half : Aneg * Ahalf = 1 := by
    rw [show Aneg = A ^ (-(1 / 2 : ℝ)) by
      exact (CFC.rpow_eq_cfc_real hA.posSemidef.nonneg).symm]
    rw [show Ahalf = A ^ (1 / 2 : ℝ) by
      exact (CFC.rpow_eq_cfc_real hA.posSemidef.nonneg).symm]
    exact CFC.rpow_neg_mul_rpow (1 / 2 : ℝ) hA.isStrictlyPositive
  change Ahalf *
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 : ℝ))
        (Aneg * B * Aneg) * Ahalf = B
  rw [← CFC.rpow_eq_cfc_real hmiddle.nonneg,
    CFC.rpow_one (Aneg * B * Aneg) hmiddle.nonneg]
  calc
    Ahalf * (Aneg * B * Aneg) * Ahalf =
        (Ahalf * Aneg) * B * (Aneg * Ahalf) := by simp only [mul_assoc]
    _ = B := by rw [hhalf_neg, hneg_half, one_mul, mul_one]

end MatrixBinaryWeightedGeometricMeanMono

namespace Matrix

/-- At weight one, the binary weighted geometric mean is its right endpoint.

Layer: Model | Gap: Level 0 (unit-weight endpoint of the binary weighted Kubo--Ando geometric mean)
Proof: evaluate the middle CFC real power at one, reassociate the perspective product, and cancel the positive-definite left input's opposite half-powers with `CFC.rpow_mul_rpow_neg` and `CFC.rpow_neg_mul_rpow`
Source: Mathlib continuous-functional-calculus real-power one and opposite-power cancellation laws, together with positive-semidefinite matrix congruence
Used in: boundary cases of joint operator-mean monotonicity and recursive finite-family interpolation for matrix and tensor preconditioners
Book citation: book/research/Source.json#/definitions/0
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, matrix geometric-mean monotonicity support -/
@[simp]
theorem binaryWeightedGeometricMean_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (hA : A.PosDef) (hB : B.PosSemidef) :
    binaryWeightedGeometricMean A B 1 = B := by
  let Aneg := cfc (R := ℝ) (p := IsSelfAdjoint)
    (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) A
  let Ahalf := cfc (R := ℝ) (p := IsSelfAdjoint)
    (fun x : ℝ => x ^ (1 / 2 : ℝ)) A
  have hAneg : Aneg.PosDef := by
    rw [show Aneg = A ^ (-(1 / 2 : ℝ)) by
      exact (CFC.rpow_eq_cfc_real hA.posSemidef.nonneg).symm]
    exact Matrix.isStrictlyPositive_iff_posDef.mp
      (hA.isStrictlyPositive.rpow A (-(1 / 2 : ℝ)))
  have hAneg_self : Matrix.conjTranspose Aneg = Aneg := hAneg.1
  have hmiddle : (Aneg * B * Aneg).PosSemidef := by
    simpa only [hAneg_self] using hB.conjTranspose_mul_mul_same Aneg
  have hhalf_neg : Ahalf * Aneg = 1 := by
    rw [show Ahalf = A ^ (1 / 2 : ℝ) by
      exact (CFC.rpow_eq_cfc_real hA.posSemidef.nonneg).symm]
    rw [show Aneg = A ^ (-(1 / 2 : ℝ)) by
      exact (CFC.rpow_eq_cfc_real hA.posSemidef.nonneg).symm]
    exact CFC.rpow_mul_rpow_neg (1 / 2 : ℝ) hA.isStrictlyPositive
  have hneg_half : Aneg * Ahalf = 1 := by
    rw [show Aneg = A ^ (-(1 / 2 : ℝ)) by
      exact (CFC.rpow_eq_cfc_real hA.posSemidef.nonneg).symm]
    rw [show Ahalf = A ^ (1 / 2 : ℝ) by
      exact (CFC.rpow_eq_cfc_real hA.posSemidef.nonneg).symm]
    exact CFC.rpow_neg_mul_rpow (1 / 2 : ℝ) hA.isStrictlyPositive
  change Ahalf *
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 : ℝ))
        (Aneg * B * Aneg) * Ahalf = B
  rw [← CFC.rpow_eq_cfc_real hmiddle.nonneg,
    CFC.rpow_one (Aneg * B * Aneg) hmiddle.nonneg]
  calc
    Ahalf * (Aneg * B * Aneg) * Ahalf =
        (Ahalf * Aneg) * B * (Aneg * Ahalf) := by simp only [mul_assoc]
    _ = B := by rw [hhalf_neg, hneg_half, one_mul, mul_one]

/-- The binary weighted geometric mean of positive-definite real matrices is positive definite
for every real weight.

Layer: Model | Gap: Level 1 (strict positivity of the binary weighted Kubo--Ando geometric mean)
Proof: use `IsStrictlyPositive.rpow` for the inverse half-power, half-power, and middle real power, then apply positive-definite congruence twice using invertibility of the outer factors
Source: Mathlib `IsStrictlyPositive.rpow`, `Matrix.isStrictlyPositive_iff_posDef`, `CFC.rpow_eq_cfc_real`, and `Matrix.PosDef.conjTranspose_mul_mul_same`
Used in: recursive operator interpolation for matrix and tensor preconditioners, where each binary interpolation step must preserve invertibility and positive definiteness
Book citation: book/research/Source.json#/definitions/0
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, matrix geometric-mean monotonicity support -/
theorem binaryWeightedGeometricMean_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (t : ℝ) (hA : A.PosDef) (hB : B.PosDef) :
    (binaryWeightedGeometricMean A B t).PosDef := by
  let Aneg := cfc (R := ℝ) (p := IsSelfAdjoint)
    (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) A
  let Ahalf := cfc (R := ℝ) (p := IsSelfAdjoint)
    (fun x : ℝ => x ^ (1 / 2 : ℝ)) A
  have hAneg : Aneg.PosDef := by
    rw [show Aneg = A ^ (-(1 / 2 : ℝ)) by
      exact (CFC.rpow_eq_cfc_real hA.posSemidef.nonneg).symm]
    exact Matrix.isStrictlyPositive_iff_posDef.mp
      (hA.isStrictlyPositive.rpow A (-(1 / 2 : ℝ)))
  have hAhalf : Ahalf.PosDef := by
    rw [show Ahalf = A ^ (1 / 2 : ℝ) by
      exact (CFC.rpow_eq_cfc_real hA.posSemidef.nonneg).symm]
    exact Matrix.isStrictlyPositive_iff_posDef.mp
      (hA.isStrictlyPositive.rpow A (1 / 2 : ℝ))
  have hAneg_conjTranspose : Matrix.conjTranspose Aneg = Aneg := hAneg.1
  have hAhalf_conjTranspose : Matrix.conjTranspose Ahalf = Ahalf := hAhalf.1
  have hmiddle : (Aneg * B * Aneg).PosDef := by
    simpa only [hAneg_conjTranspose] using
      hB.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hAneg.isUnit)
  have hmiddlePow :
      (cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ t)
        (Aneg * B * Aneg)).PosDef := by
    rw [← CFC.rpow_eq_cfc_real hmiddle.posSemidef.nonneg]
    exact Matrix.isStrictlyPositive_iff_posDef.mp
      (hmiddle.isStrictlyPositive.rpow (Aneg * B * Aneg) t)
  change (Ahalf *
    cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ t)
      (Aneg * B * Aneg) * Ahalf).PosDef
  simpa only [hAhalf_conjTranspose] using
    hmiddlePow.conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_of_isUnit hAhalf.isUnit)

end Matrix

namespace MatrixBinaryWeightedGeometricMeanMono

private noncomputable def matrixRpow
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (t : ℝ) : Matrix ι ι ℝ :=
  cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ t) A

private theorem matrixRpow_posDef
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (t : ℝ) (hA : A.PosDef) :
    (matrixRpow A t).PosDef := by
  rw [matrixRpow, ← CFC.rpow_eq_cfc_real hA.posSemidef.nonneg]
  exact Matrix.isStrictlyPositive_iff_posDef.mp
    (hA.isStrictlyPositive.rpow A t)

private theorem matrixRpow_zero
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) :
    matrixRpow A 0 = 1 := by
  rw [matrixRpow, ← CFC.rpow_eq_cfc_real hA.nonneg]
  exact CFC.rpow_zero A

private theorem matrixRpow_add
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (s t : ℝ) (hA : A.PosDef) :
    matrixRpow A (s + t) = matrixRpow A s * matrixRpow A t := by
  rw [matrixRpow, matrixRpow, matrixRpow,
    ← CFC.rpow_eq_cfc_real hA.posSemidef.nonneg,
    ← CFC.rpow_eq_cfc_real hA.posSemidef.nonneg,
    ← CFC.rpow_eq_cfc_real hA.posSemidef.nonneg]
  exact CFC.rpow_add hA.isUnit

private theorem matrixRpow_neg_half_mul_half
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    matrixRpow A (-(1 / 2 : ℝ)) * matrixRpow A (1 / 2 : ℝ) = 1 := by
  rw [← matrixRpow_add A _ _ hA]
  norm_num
  exact matrixRpow_zero A hA.posSemidef

private theorem matrixRpow_half_mul_neg_half
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    matrixRpow A (1 / 2 : ℝ) * matrixRpow A (-(1 / 2 : ℝ)) = 1 := by
  rw [← matrixRpow_add A _ _ hA]
  norm_num
  exact matrixRpow_zero A hA.posSemidef

private theorem matrixRpow_half_mul_half
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    matrixRpow A (1 / 2 : ℝ) * matrixRpow A (1 / 2 : ℝ) = A := by
  rw [← matrixRpow_add A _ _ hA]
  norm_num
  rw [matrixRpow, ← CFC.rpow_eq_cfc_real hA.posSemidef.nonneg]
  exact CFC.rpow_one A hA.posSemidef.nonneg

@[reducible] private noncomputable def complexCStarMatrixRealCFC
    {ι : Type u} [Fintype ι] [DecidableEq ι] :
    ContinuousFunctionalCalculus ℝ (CStarMatrix ι ι ℂ) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

@[reducible] private noncomputable def complexCStarMatrixNonnegSpectrum
    {ι : Type u} [Fintype ι] [DecidableEq ι] :
    NonnegSpectrumClass ℝ (CStarMatrix ι ι ℂ) :=
  CStarAlgebra.instNonnegSpectrumClass

private noncomputable def complexMatrixRpow
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : CStarMatrix ι ι ℂ) (t : ℝ) : CStarMatrix ι ι ℂ := by
  letI hCFC : ContinuousFunctionalCalculus ℝ
      (CStarMatrix ι ι ℂ) IsSelfAdjoint := complexCStarMatrixRealCFC
  letI hNS : NonnegSpectrumClass ℝ (CStarMatrix ι ι ℂ) :=
    complexCStarMatrixNonnegSpectrum
  exact @CFC.rpow _ inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance hCFC hNS A t

private theorem starAlgHom_mono_of_le
    {R A B : Type*} [CommRing R]
    [Ring A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
    [Ring B] [PartialOrder B] [StarRing B] [StarOrderedRing B]
    [Algebra R A] [Algebra R B]
    (f : A →⋆ₐ[R] B) {a b : A} (hab : a ≤ b) : f a ≤ f b := by
  exact OrderHomClass.mono f hab

private theorem realMatrixComplexification_nonneg_iff
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) :
    0 ≤ realMatrixComplexification A ↔ 0 ≤ A := by
  let scalarCast : ℝ →⋆ₐ[ℝ] ℂ :=
    { toFun := fun r => (r : ℂ)
      map_one' := Complex.ofReal_one
      map_mul' := Complex.ofReal_mul
      map_zero' := Complex.ofReal_zero
      map_add' := Complex.ofReal_add
      commutes' := fun _ => rfl
      map_star' := fun r => by simp }
  let matrixCast : Matrix ι ι ℝ →⋆ₐ[ℝ] Matrix ι ι ℂ :=
    StarAlgHom.mk (AlgHom.mapMatrix scalarCast.toAlgHom)
      (by
        intro M
        change Matrix.map (star M) scalarCast = star (Matrix.map M scalarCast)
        ext i j
        simp [scalarCast, Matrix.star_eq_conjTranspose])
  let e : Matrix ι ι ℂ ≃⋆ₐ[ℝ] CStarMatrix ι ι ℂ :=
    (CStarMatrix.ofMatrixStarAlgEquiv (n := ι) (A := ℂ)).restrictScalars ℝ
  let castA : Matrix ι ι ℂ := Matrix.map A scalarCast
  have hcomplexify : realMatrixComplexification A = e castA := by rfl
  rw [hcomplexify]
  change e 0 ≤ e castA ↔ 0 ≤ A
  rw [map_le_map_iff e]
  constructor
  · intro hcast
    have hcast_psd : castA.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hcast
    rw [Matrix.nonneg_iff_posSemidef]
    constructor
    · apply Matrix.IsHermitian.ext
      intro i j
      apply Complex.ofReal_injective
      simpa [castA, scalarCast] using hcast_psd.1.apply i j
    · intro v
      let vc : ι →₀ ℂ :=
        v.mapRange (fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
      have hv := hcast_psd.2 vc
      have heq :
          vc.sum (fun i vi => vc.sum fun j vj => star vi * castA i j * vj) =
            ((v.sum fun i vi => v.sum fun j vj => star vi * A i j * vj : ℝ) : ℂ) := by
        dsimp [vc]
        rw [Finsupp.sum_mapRange_index (by intro; simp)]
        simp only [Finsupp.sum,
          Finsupp.support_mapRange_of_injective Complex.ofReal_zero v
            Complex.ofReal_injective,
          castA, scalarCast, Matrix.map_apply, StarAlgHom.coe_mk]
        push_cast
        simp [Finsupp.mapRange_apply]
      rw [heq] at hv
      exact (Complex.nonneg_iff.mp hv).1
  · intro hA
    exact map_nonneg matrixCast.toNonUnitalStarAlgHom hA

private theorem nonsing_inv_antitone_of_posDef
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (hA : A.PosDef) (hAB : A ≤ B) :
    B⁻¹ ≤ A⁻¹ := by
  have hB : B.PosDef := by
    convert hA.add_posSemidef (Matrix.le_iff.mp hAB) using 1
    abel
  let φ := realMatrixComplexification (ι := ι)
  let a : (Matrix ι ι ℝ)ˣ := hA.isUnit.unit
  let b : (Matrix ι ι ℝ)ˣ := hB.isUnit.unit
  let φa : (CStarMatrix ι ι ℂ)ˣ := Units.map φ.toMonoidHom a
  let φb : (CStarMatrix ι ι ℂ)ˣ := Units.map φ.toMonoidHom b
  have hcomplex_order : (φa : CStarMatrix ι ι ℂ) ≤ φb := by
    simpa [φa, φb, φ, a, b, IsUnit.unit_spec] using
      starAlgHom_mono_of_le φ hAB
  have hcomplex_A_nonneg : 0 ≤ (φa : CStarMatrix ι ι ℂ) := by
    simpa [φa, φ, a, IsUnit.unit_spec] using
      (realMatrixComplexification_nonneg_iff A).2 hA.posSemidef.nonneg
  have hcomplex_inv :
      (↑φb⁻¹ : CStarMatrix ι ι ℂ) ≤ (↑φa⁻¹ : CStarMatrix ι ι ℂ) :=
    CStarAlgebra.inv_le_inv hcomplex_A_nonneg hcomplex_order
  have himage_inv : φ B⁻¹ ≤ φ A⁻¹ := by
    simpa [φa, φb, φ, a, b, IsUnit.unit_spec, Matrix.coe_units_inv] using hcomplex_inv
  rw [Matrix.le_iff]
  apply Matrix.nonneg_iff_posSemidef.mp
  apply (realMatrixComplexification_nonneg_iff (A⁻¹ - B⁻¹)).mp
  rw [map_sub]
  exact sub_nonneg.mpr himage_inv


private theorem realMatrixComplexification_matrixRpow
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (t : ℝ) (hA : A.PosSemidef) :
    realMatrixComplexification (matrixRpow A t) =
      complexMatrixRpow (realMatrixComplexification A) t := by
  letI hCFC : ContinuousFunctionalCalculus ℝ
      (CStarMatrix ι ι ℂ) IsSelfAdjoint := complexCStarMatrixRealCFC
  letI hNS : NonnegSpectrumClass ℝ (CStarMatrix ι ι ℂ) :=
    complexCStarMatrixNonnegSpectrum
  letI hSemi : IsSemitopologicalRing (CStarMatrix ι ι ℂ) := inferInstance
  letI hT2 : T2Space (CStarMatrix ι ι ℂ) := inferInstance
  have hnonneg : 0 ≤ realMatrixComplexification A :=
    (realMatrixComplexification_nonneg_iff A).2 hA.nonneg
  have hrpow_eq :
      complexMatrixRpow (realMatrixComplexification A) t =
        cfc (fun x : ℝ => x ^ t) (realMatrixComplexification A) := by
    rw [complexMatrixRpow]
    exact @CFC.rpow_eq_cfc_real _ inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance hCFC hNS hSemi hT2
      (realMatrixComplexification A) t hnonneg
  rw [matrixRpow, hrpow_eq]
  have hf : ContinuousOn (fun x : ℝ => x ^ t) (spectrum ℝ A) := by
    have hfin : (spectrum ℝ A).Finite := by
      rw [hA.1.spectrum_real_eq_range_eigenvalues]
      exact Set.finite_range _
    exact hfin.continuousOn _
  have hφ : Continuous (realMatrixComplexification (ι := ι)) := by
    change Continuous (fun M : Matrix ι ι ℝ =>
      CStarMatrix.ofMatrix (Matrix.map M fun r : ℝ => (r : ℂ)))
    have hcast : Continuous (fun M : Matrix ι ι ℝ =>
        Matrix.map M fun r : ℝ => (r : ℂ)) := by
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      change Continuous (fun M : Matrix ι ι ℝ => (M i j : ℂ))
      fun_prop
    exact CStarMatrix.uniformEmbedding_ofMatrix.isUniformInducing.isInducing.continuous.comp hcast
  exact (realMatrixComplexification (ι := ι)).map_cfc
    (fun x : ℝ => x ^ t) A
    (hf := hf) (hφ := hφ) (ha := hA.1)
    (hφa := (show IsSelfAdjoint A from hA.1).map
      (realMatrixComplexification (ι := ι)))

private noncomputable def weightedHarmonicResolvent
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (s : ℝ) : Matrix ι ι ℝ :=
  (A⁻¹ + s • B⁻¹)⁻¹

private theorem weightedHarmonicResolvent_mono
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A B C D : Matrix ι ι ℝ) (s : ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef) (hD : D.PosDef)
    (hAC : A ≤ C) (hBD : B ≤ D) (hs : 0 < s) :
    weightedHarmonicResolvent A B s ≤ weightedHarmonicResolvent C D s := by
  have hCinv_Ainv : C⁻¹ ≤ A⁻¹ :=
    nonsing_inv_antitone_of_posDef A C hA hAC
  have hDinv_Binv : D⁻¹ ≤ B⁻¹ :=
    nonsing_inv_antitone_of_posDef B D hB hBD
  have hsum : C⁻¹ + s • D⁻¹ ≤ A⁻¹ + s • B⁻¹ :=
    add_le_add hCinv_Ainv (smul_le_smul_of_nonneg_left hDinv_Binv hs.le)
  exact nonsing_inv_antitone_of_posDef
    (C⁻¹ + s • D⁻¹) (A⁻¹ + s • B⁻¹)
    (hC.inv.add (hD.inv.smul hs)) hsum

private theorem weightedHarmonicResolvent_eq_rpow_perspective_integrand
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (s : ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hs : 0 < s) :
    matrixRpow A (1 / 2 : ℝ) *
          ((s⁻¹) • (1 : Matrix ι ι ℝ) -
            (s • (1 : Matrix ι ι ℝ) +
              matrixRpow A (-(1 / 2 : ℝ)) * B *
                matrixRpow A (-(1 / 2 : ℝ)))⁻¹) *
        matrixRpow A (1 / 2 : ℝ) =
      (s⁻¹) • weightedHarmonicResolvent A B s := by
  classical
  let P : Matrix ι ι ℝ := matrixRpow A (1 / 2 : ℝ)
  let Q : Matrix ι ι ℝ := matrixRpow A (-(1 / 2 : ℝ))
  let K : Matrix ι ι ℝ := s • A + B
  have hK_pd : K.PosDef := (hA.smul hs).add hB
  have hP_Q : P * Q = (1 : Matrix ι ι ℝ) := by
    simpa [P, Q] using matrixRpow_half_mul_neg_half A hA
  have hQ_P : Q * P = (1 : Matrix ι ι ℝ) := by
    simpa [P, Q] using matrixRpow_neg_half_mul_half A hA
  have hP_P : P * P = A := by
    simpa [P] using matrixRpow_half_mul_half A hA
  have hKinv_K : K⁻¹ * K = (1 : Matrix ι ι ℝ) := by
    have hdet : K.det ≠ 0 := ne_of_gt hK_pd.det_pos
    letI : Invertible K.det := invertibleOfNonzero hdet
    letI : Invertible K := Matrix.invertibleOfDetInvertible K
    exact Matrix.inv_mul_of_invertible K
  have hB_Binv : B * B⁻¹ = (1 : Matrix ι ι ℝ) := by
    have hdet : B.det ≠ 0 := ne_of_gt hB.det_pos
    letI : Invertible B.det := invertibleOfNonzero hdet
    letI : Invertible B := Matrix.invertibleOfDetInvertible B
    exact Matrix.mul_inv_of_invertible B
  have hA_Ainv : A * A⁻¹ = (1 : Matrix ι ι ℝ) := by
    have hdet : A.det ≠ 0 := ne_of_gt hA.det_pos
    letI : Invertible A.det := invertibleOfNonzero hdet
    letI : Invertible A := Matrix.invertibleOfDetInvertible A
    exact Matrix.mul_inv_of_invertible A
  have hmiddle :
      s • (1 : Matrix ι ι ℝ) + Q * B * Q = Q * K * Q := by
    have hQAQ : Q * A * Q = (1 : Matrix ι ι ℝ) := by
      rw [← hP_P]
      calc
        Q * (P * P) * Q = (Q * P) * (P * Q) := by noncomm_ring
        _ = 1 := by rw [hQ_P, hP_Q, one_mul]
    dsimp [K]
    rw [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, hQAQ]
  have hmiddle_inv :
      (s • (1 : Matrix ι ι ℝ) + Q * B * Q)⁻¹ = P * K⁻¹ * P := by
    rw [hmiddle]
    apply Matrix.inv_eq_left_inv
    calc
      (P * K⁻¹ * P) * (Q * K * Q) =
          P * K⁻¹ * (P * Q) * K * Q := by noncomm_ring
      _ = P * (K⁻¹ * K) * Q := by rw [hP_Q]; simp [mul_assoc]
      _ = 1 := by rw [hKinv_K, mul_one, hP_Q]
  have hresolver_inv :
      weightedHarmonicResolvent A B s = A * K⁻¹ * B := by
    unfold weightedHarmonicResolvent
    apply Matrix.inv_eq_left_inv
    calc
      (A * K⁻¹ * B) * (A⁻¹ + s • B⁻¹) =
          A * K⁻¹ * (B + s • A) * A⁻¹ := by
            noncomm_ring [hA_Ainv, hB_Binv]
      _ = A * (K⁻¹ * K) * A⁻¹ := by
            rw [show B + s • A = K by simp [K, add_comm]]
            simp [mul_assoc]
      _ = 1 := by rw [hKinv_K, mul_one, hA_Ainv]
  change P * ((s⁻¹) • (1 : Matrix ι ι ℝ) -
      (s • (1 : Matrix ι ι ℝ) + Q * B * Q)⁻¹) * P =
    (s⁻¹) • weightedHarmonicResolvent A B s
  rw [hmiddle_inv, hresolver_inv]
  rw [mul_sub, sub_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, mul_one]
  have hconj : P * (P * K⁻¹ * P) * P = A * K⁻¹ * A := by
    calc
      P * (P * K⁻¹ * P) * P = (P * P) * K⁻¹ * (P * P) := by
        noncomm_ring
      _ = A * K⁻¹ * A := by rw [hP_P]
  rw [hconj]
  have hexpand : A = s • (A * K⁻¹ * A) + A * K⁻¹ * B := by
    calc
      A = A * (K⁻¹ * K) := by rw [hKinv_K, mul_one]
      _ = s • (A * K⁻¹ * A) + A * K⁻¹ * B := by
        dsimp [K]
        simp only [mul_add, mul_assoc, Matrix.mul_smul, Matrix.smul_mul]
  have hscaled :
      (s⁻¹) • A = A * K⁻¹ * A + (s⁻¹) • (A * K⁻¹ * B) := by
    calc
      (s⁻¹) • A = (s⁻¹) • (s • (A * K⁻¹ * A) + A * K⁻¹ * B) :=
        congrArg ((s⁻¹) • ·) hexpand
      _ = A * K⁻¹ * A + (s⁻¹) • (A * K⁻¹ * B) := by
        rw [smul_add, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
  rw [hP_P, hscaled]
  module

private theorem rpowPerspectiveIntegrand_eq_smul_weightedHarmonicResolvent
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (p s : ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hs : 0 < s) :
    let Aneg := matrixRpow A (-(1 / 2 : ℝ))
    let Ahalf := matrixRpow A (1 / 2 : ℝ)
    Ahalf * cfc (R := ℝ) (p := IsSelfAdjoint)
          (Real.rpowIntegrand₀₁ p s) (Aneg * B * Aneg) * Ahalf =
      (s ^ (p - 1)) • weightedHarmonicResolvent A B s := by
  classical
  let Aneg := matrixRpow A (-(1 / 2 : ℝ))
  let Ahalf := matrixRpow A (1 / 2 : ℝ)
  have hAneg : Aneg.PosDef := matrixRpow_posDef A _ hA
  have hAneg_star : Matrix.conjTranspose Aneg = Aneg := hAneg.1
  have hmiddle : (Aneg * B * Aneg).PosDef := by
    simpa only [hAneg_star] using
      hB.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hAneg.isUnit)
  have hcfc := cfc_rpowIntegrand₀₁_eq_resolvent
    (Aneg * B * Aneg) p s hmiddle.posSemidef hs
  have hperspective := weightedHarmonicResolvent_eq_rpow_perspective_integrand
    A B s hA hB hs
  change Ahalf * cfc (R := ℝ) (p := IsSelfAdjoint)
      (Real.rpowIntegrand₀₁ p s) (Aneg * B * Aneg) * Ahalf = _
  rw [hcfc]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  rw [hperspective, smul_smul]
  congr 1
  rw [Real.rpow_sub_one hs.ne' p]
  exact (div_eq_mul_inv (s ^ p) s).symm

private theorem complexifiedRpowPerspectiveIntegrand_eq_smul_resolvent
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    [ContinuousFunctionalCalculus ℝ (CStarMatrix ι ι ℂ) IsSelfAdjoint]
    [NonnegSpectrumClass ℝ (CStarMatrix ι ι ℂ)]
    (A B : Matrix ι ι ℝ) (p s : ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hs : 0 < s) :
    let φ := realMatrixComplexification (ι := ι)
    let Aneg := matrixRpow A (-(1 / 2 : ℝ))
    let Ahalf := matrixRpow A (1 / 2 : ℝ)
    φ Ahalf * cfc (R := ℝ) (p := IsSelfAdjoint)
          (Real.rpowIntegrand₀₁ p s) (φ Aneg * φ B * φ Aneg) * φ Ahalf =
      (s ^ (p - 1)) • φ (weightedHarmonicResolvent A B s) := by
  let φ := realMatrixComplexification (ι := ι)
  let Aneg := matrixRpow A (-(1 / 2 : ℝ))
  let Ahalf := matrixRpow A (1 / 2 : ℝ)
  have hAneg : Aneg.PosDef := matrixRpow_posDef A _ hA
  have hAneg_star : Matrix.conjTranspose Aneg = Aneg := hAneg.1
  have hmiddle : (Aneg * B * Aneg).PosDef := by
    simpa only [hAneg_star] using
      hB.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hAneg.isUnit)
  have hf : ContinuousOn (Real.rpowIntegrand₀₁ p s)
      (spectrum ℝ (Aneg * B * Aneg)) := by
    have hnonzero : ∀ x ∈ spectrum ℝ (Aneg * B * Aneg), s + x ≠ 0 := by
      intro x hx
      have hx_nonneg : 0 ≤ x := by
        rw [hmiddle.1.spectrum_real_eq_range_eigenvalues] at hx
        obtain ⟨i, rfl⟩ := hx
        exact hmiddle.posSemidef.eigenvalues_nonneg i
      exact ne_of_gt (add_pos_of_pos_of_nonneg hs hx_nonneg)
    unfold Real.rpowIntegrand₀₁
    fun_prop (disch := assumption)
  have hmap_cfc :
      φ (cfc (R := ℝ) (p := IsSelfAdjoint)
          (Real.rpowIntegrand₀₁ p s) (Aneg * B * Aneg)) =
        cfc (R := ℝ) (p := IsSelfAdjoint)
          (Real.rpowIntegrand₀₁ p s) (φ (Aneg * B * Aneg)) := by
    exact φ.map_cfc (Real.rpowIntegrand₀₁ p s) (Aneg * B * Aneg)
      (hf := hf)
      (hφ := by
        change Continuous (fun M : Matrix ι ι ℝ =>
          CStarMatrix.ofMatrix (Matrix.map M fun r : ℝ => (r : ℂ)))
        have hcast : Continuous (fun M : Matrix ι ι ℝ =>
            Matrix.map M fun r : ℝ => (r : ℂ)) := by
          apply continuous_pi
          intro i
          apply continuous_pi
          intro j
          change Continuous (fun M : Matrix ι ι ℝ => (M i j : ℂ))
          fun_prop
        exact CStarMatrix.uniformEmbedding_ofMatrix.isUniformInducing.isInducing.continuous.comp
          hcast)
      (ha := hmiddle.1)
      (hφa := (show IsSelfAdjoint (Aneg * B * Aneg) from hmiddle.1).map φ)
  have hsource := congrArg φ
    (rpowPerspectiveIntegrand_eq_smul_weightedHarmonicResolvent
      A B p s hA hB hs)
  change φ (Ahalf * cfc (R := ℝ) (p := IsSelfAdjoint)
      (Real.rpowIntegrand₀₁ p s) (Aneg * B * Aneg) * Ahalf) =
    φ ((s ^ (p - 1)) • weightedHarmonicResolvent A B s) at hsource
  rw [map_mul, map_mul, hmap_cfc, map_mul, map_mul, map_smul] at hsource
  change φ Ahalf * cfc (R := ℝ) (p := IsSelfAdjoint)
      (Real.rpowIntegrand₀₁ p s) (φ Aneg * φ B * φ Aneg) * φ Ahalf = _
  exact hsource

private theorem complexifiedRpowPerspectiveIntegrand_mono
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    [ContinuousFunctionalCalculus ℝ (CStarMatrix ι ι ℂ) IsSelfAdjoint]
    [NonnegSpectrumClass ℝ (CStarMatrix ι ι ℂ)]
    (A B C D : Matrix ι ι ℝ) (p s : ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef) (hD : D.PosDef)
    (hAC : A ≤ C) (hBD : B ≤ D) (hs : 0 < s) :
    let φ := realMatrixComplexification (ι := ι)
    let Aneg := matrixRpow A (-(1 / 2 : ℝ))
    let Ahalf := matrixRpow A (1 / 2 : ℝ)
    let Cneg := matrixRpow C (-(1 / 2 : ℝ))
    let Chalf := matrixRpow C (1 / 2 : ℝ)
    φ Ahalf * cfc (R := ℝ) (p := IsSelfAdjoint)
          (Real.rpowIntegrand₀₁ p s) (φ Aneg * φ B * φ Aneg) * φ Ahalf ≤
      φ Chalf * cfc (R := ℝ) (p := IsSelfAdjoint)
          (Real.rpowIntegrand₀₁ p s) (φ Cneg * φ D * φ Cneg) * φ Chalf := by
  let φ := realMatrixComplexification (ι := ι)
  let Aneg := matrixRpow A (-(1 / 2 : ℝ))
  let Ahalf := matrixRpow A (1 / 2 : ℝ)
  let Cneg := matrixRpow C (-(1 / 2 : ℝ))
  let Chalf := matrixRpow C (1 / 2 : ℝ)
  change φ Ahalf * cfc (R := ℝ) (p := IsSelfAdjoint)
        (Real.rpowIntegrand₀₁ p s) (φ Aneg * φ B * φ Aneg) * φ Ahalf ≤
    φ Chalf * cfc (R := ℝ) (p := IsSelfAdjoint)
        (Real.rpowIntegrand₀₁ p s) (φ Cneg * φ D * φ Cneg) * φ Chalf
  rw [complexifiedRpowPerspectiveIntegrand_eq_smul_resolvent A B p s hA hB hs,
    complexifiedRpowPerspectiveIntegrand_eq_smul_resolvent C D p s hC hD hs]
  have hreal :
      (s ^ (p - 1)) • weightedHarmonicResolvent A B s ≤
        (s ^ (p - 1)) • weightedHarmonicResolvent C D s :=
    smul_le_smul_of_nonneg_left
      (weightedHarmonicResolvent_mono A B C D s hA hB hC hD hAC hBD hs)
      (Real.rpow_nonneg hs.le _)
  change (s ^ (p - 1)) • φ (weightedHarmonicResolvent A B s) ≤
    (s ^ (p - 1)) • φ (weightedHarmonicResolvent C D s)
  calc
    (s ^ (p - 1)) • φ (weightedHarmonicResolvent A B s) =
        φ ((s ^ (p - 1)) • weightedHarmonicResolvent A B s) :=
      (map_smul φ (s ^ (p - 1)) (weightedHarmonicResolvent A B s)).symm
    _ ≤ φ ((s ^ (p - 1)) • weightedHarmonicResolvent C D s) :=
      starAlgHom_mono_of_le φ hreal
    _ = (s ^ (p - 1)) • φ (weightedHarmonicResolvent C D s) :=
      map_smul φ (s ^ (p - 1)) (weightedHarmonicResolvent C D s)

/-- The binary weighted Kubo--Ando geometric mean is jointly monotone on
positive-definite finite real matrices for weights in the unit interval.

Layer: Model | Gap: Level 2 (joint Löwner monotonicity of the binary weighted operator geometric mean)
Proof: represent the interior real power by Mathlib's nonunital-CFC Bochner integral, identify each perspective integrand with a positive multiple of a jointly monotone harmonic resolvent, integrate the pointwise order, and handle the two endpoint weights by the staged endpoint identities.
Source: Kubo--Ando operator means; Mathlib nonunital continuous-functional-calculus integral representation of fractional powers, inverse antitonicity, and finite complex C-star-matrix Bochner integration
Used in: recursive matrix and tensor preconditioner interpolation, where coordinatewise growth of two positive-definite metric inputs must imply growth of their weighted operator mean
Book citation: book/research/Source.json#/key_lemmas/7
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Lemma 6 operator-mean monotonicity support -/
theorem _root_.Matrix.binaryWeightedGeometricMean_mono
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A B C D : Matrix ι ι ℝ) (t : ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef) (hD : D.PosDef)
    (hAC : A ≤ C) (hBD : B ≤ D) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Matrix.binaryWeightedGeometricMean A B t ≤
      Matrix.binaryWeightedGeometricMean C D t := by
  rcases lt_or_eq_of_le ht0 with htpos | rfl
  · rcases lt_or_eq_of_le ht1 with htlt | rfl
    · let hSemiCanonical : IsSemitopologicalRing
          (CStarMatrix ι ι ℂ) := inferInstance
      let hT2Canonical : T2Space (CStarMatrix ι ι ℂ) := inferInstance
      let hSMulCanonical : SMul ℝ (CStarMatrix ι ι ℂ) := inferInstance
      letI hSMul : SMul ℝ (CStarMatrix ι ι ℂ) := hSMulCanonical
      let hModuleCanonical : Module ℝ (CStarMatrix ι ι ℂ) := inferInstance
      letI hModule : Module ℝ (CStarMatrix ι ι ℂ) := hModuleCanonical
      letI hTower : IsScalarTower ℝ (CStarMatrix ι ι ℂ) (CStarMatrix ι ι ℂ) :=
        IsScalarTower.of_algebraMap_smul fun r X => by
          rw [Algebra.smul_def]
          simp only [smul_eq_mul]
      letI hCFC : ContinuousFunctionalCalculus ℝ
          (CStarMatrix ι ι ℂ) IsSelfAdjoint := complexCStarMatrixRealCFC
      have hTowerCheck : IsScalarTower ℝ
          (CStarMatrix ι ι ℂ) (CStarMatrix ι ι ℂ) := hTower
      letI hSmulComm : SMulCommClass ℝ
          (CStarMatrix ι ι ℂ) (CStarMatrix ι ι ℂ) := by
        constructor
        intro r X Y
        change r • (X * Y) = X * (r • Y)
        ext i j
        simp [Matrix.mul_apply, Finset.mul_sum]
      letI hNCFC : @NonUnitalContinuousFunctionalCalculus ℝ
          (CStarMatrix ι ι ℂ) IsSelfAdjoint
          inferInstance inferInstance inferInstance inferInstance inferInstance
          inferInstance inferInstance inferInstance inferInstance hModule hTower
          hSmulComm :=
        let hNCFCAlgebra := @ContinuousFunctionalCalculus.toNonUnital
          ℝ (CStarMatrix ι ι ℂ) IsSelfAdjoint
          inferInstance inferInstance inferInstance inferInstance inferInstance
          inferInstance inferInstance inferInstance inferInstance hCFC
        hNCFCAlgebra
      let cfcN := @cfcₙ ℝ (CStarMatrix ι ι ℂ) IsSelfAdjoint
        inferInstance inferInstance inferInstance inferInstance inferInstance
        inferInstance inferInstance inferInstance inferInstance hModule hTower
        hSmulComm hNCFC
      letI hNS : NonnegSpectrumClass ℝ (CStarMatrix ι ι ℂ) :=
        complexCStarMatrixNonnegSpectrum
      let nnrpowN := @CFC.nnrpow (CStarMatrix ι ι ℂ)
        inferInstance inferInstance inferInstance inferInstance hModule hSmulComm
        hTower inferInstance hNCFC hNS
      let φ := realMatrixComplexification (ι := ι)
      let Aneg := matrixRpow A (-(1 / 2 : ℝ))
      let Ahalf := matrixRpow A (1 / 2 : ℝ)
      let Cneg := matrixRpow C (-(1 / 2 : ℝ))
      let Chalf := matrixRpow C (1 / 2 : ℝ)
      let XA : CStarMatrix ι ι ℂ := φ Aneg * φ B * φ Aneg
      let XC : CStarMatrix ι ι ℂ := φ Cneg * φ D * φ Cneg
      let q : ℝ≥0 := ⟨t, ht0⟩
      have hq : q ∈ Set.Ioo (0 : ℝ≥0) 1 := by
        constructor
        · exact_mod_cast htpos
        · exact_mod_cast htlt
      have hAneg : Aneg.PosDef := matrixRpow_posDef A _ hA
      have hCneg : Cneg.PosDef := matrixRpow_posDef C _ hC
      have hAneg_star : Matrix.conjTranspose Aneg = Aneg := hAneg.1
      have hCneg_star : Matrix.conjTranspose Cneg = Cneg := hCneg.1
      have hmiddleA : (Aneg * B * Aneg).PosDef := by
        simpa only [hAneg_star] using
          hB.conjTranspose_mul_mul_same
            (Matrix.mulVec_injective_of_isUnit hAneg.isUnit)
      have hmiddleC : (Cneg * D * Cneg).PosDef := by
        simpa only [hCneg_star] using
          hD.conjTranspose_mul_mul_same
            (Matrix.mulVec_injective_of_isUnit hCneg.isUnit)
      have hXA : 0 ≤ XA := by
        have himage := map_nonneg φ.toNonUnitalStarAlgHom hmiddleA.posSemidef.nonneg
        simpa only [XA, map_mul] using himage
      have hXC : 0 ≤ XC := by
        have himage := map_nonneg φ.toNonUnitalStarAlgHom hmiddleC.posSemidef.nonneg
        simpa only [XC, map_mul] using himage
      obtain ⟨μ, hμ⟩ :=
        CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁
          (CStarMatrix ι ι ℂ) hq
      have hμA := hμ XA hXA
      have hμC := hμ XC hXC
      change MeasureTheory.IntegrableOn
          (fun s => cfcN (Real.rpowIntegrand₀₁ q s) XA) (Set.Ioi 0) μ ∧
          nnrpowN XA q =
            ∫ s in Set.Ioi 0, cfcN (Real.rpowIntegrand₀₁ q s) XA ∂μ at hμA
      change MeasureTheory.IntegrableOn
          (fun s => cfcN (Real.rpowIntegrand₀₁ q s) XC) (Set.Ioi 0) μ ∧
          nnrpowN XC q =
            ∫ s in Set.Ioi 0, cfcN (Real.rpowIntegrand₀₁ q s) XC ∂μ at hμC
      let LA := ContinuousLinearMap.mulLeftRight ℂ
        (CStarMatrix ι ι ℂ) (φ Ahalf) (φ Ahalf)
      let LC := ContinuousLinearMap.mulLeftRight ℂ
        (CStarMatrix ι ι ℂ) (φ Chalf) (φ Chalf)
      have hintA : MeasureTheory.IntegrableOn
          (fun s => LA (cfcN (Real.rpowIntegrand₀₁ q s) XA)) (Set.Ioi 0) μ :=
        LA.integrable_comp hμA.1
      have hintC : MeasureTheory.IntegrableOn
          (fun s => LC (cfcN (Real.rpowIntegrand₀₁ q s) XC)) (Set.Ioi 0) μ :=
        LC.integrable_comp hμC.1
      have hintegral :
          (∫ s in Set.Ioi 0, LA (cfcN (Real.rpowIntegrand₀₁ q s) XA) ∂μ) ≤
            ∫ s in Set.Ioi 0, LC (cfcN (Real.rpowIntegrand₀₁ q s) XC) ∂μ := by
        apply cstarMatrix_integral_mono_ae hintA hintC
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
        have hfA : ContinuousOn (Real.rpowIntegrand₀₁ q s)
            (quasispectrum ℝ XA) := by
          exact (Real.continuousOn_rpowIntegrand₀₁_Ici
            (show (t : ℝ) ∈ Set.Ioo 0 1 from ⟨htpos, htlt⟩) hs).mono (by
              intro x hx
              exact quasispectrum_nonneg_of_nonneg XA hXA x hx)
        have hfC : ContinuousOn (Real.rpowIntegrand₀₁ q s)
            (quasispectrum ℝ XC) := by
          exact (Real.continuousOn_rpowIntegrand₀₁_Ici
            (show (t : ℝ) ∈ Set.Ioo 0 1 from ⟨htpos, htlt⟩) hs).mono (by
              intro x hx
              exact quasispectrum_nonneg_of_nonneg XC hXC x hx)
        change φ Ahalf * cfcN (Real.rpowIntegrand₀₁ q s) XA * φ Ahalf ≤
          φ Chalf * cfcN (Real.rpowIntegrand₀₁ q s) XC * φ Chalf
        have hcfA : cfcN (Real.rpowIntegrand₀₁ q s) XA =
            cfc (Real.rpowIntegrand₀₁ q s) XA := by
          exact cfcₙ_eq_cfc (hf := hfA) (hf0 := Real.rpowIntegrand₀₁_zero_right)
        have hcfC : cfcN (Real.rpowIntegrand₀₁ q s) XC =
            cfc (Real.rpowIntegrand₀₁ q s) XC := by
          exact cfcₙ_eq_cfc (hf := hfC) (hf0 := Real.rpowIntegrand₀₁_zero_right)
        rw [hcfA, hcfC]
        simpa only [XA, XC, q] using
          (complexifiedRpowPerspectiveIntegrand_mono
            A B C D t s hA hB hC hD hAC hBD hs)
      have hqreal : 0 < (q : ℝ) := by exact_mod_cast hq.1
      have hnnA : nnrpowN XA q = cfcN (fun x : ℝ => x ^ (q : ℝ)) XA := by
        exact @CFC.nnrpow_eq_cfcₙ_real
          (CStarMatrix ι ι ℂ) inferInstance inferInstance
          inferInstance inferInstance hModule hSmulComm hTower inferInstance
          hNCFC hNS inferInstance inferInstance XA q hXA
      have hnnC : nnrpowN XC q = cfcN (fun x : ℝ => x ^ (q : ℝ)) XC := by
        exact @CFC.nnrpow_eq_cfcₙ_real
          (CStarMatrix ι ι ℂ) inferInstance inferInstance
          inferInstance inferInstance hModule hSmulComm hTower inferInstance
          hNCFC hNS inferInstance inferInstance XC q hXC
      have hcfPowA : cfcN (fun x : ℝ => x ^ (q : ℝ)) XA =
          cfc (fun x : ℝ => x ^ (q : ℝ)) XA := by
        exact cfcₙ_eq_cfc
          (hf := (Real.continuous_rpow_const hqreal.le).continuousOn)
          (hf0 := Real.zero_rpow hqreal.ne')
      have hcfPowC : cfcN (fun x : ℝ => x ^ (q : ℝ)) XC =
          cfc (fun x : ℝ => x ^ (q : ℝ)) XC := by
        exact cfcₙ_eq_cfc
          (hf := (Real.continuous_rpow_const hqreal.le).continuousOn)
          (hf0 := Real.zero_rpow hqreal.ne')
      have hpowA : complexMatrixRpow XA t = nnrpowN XA q := by
        calc
          complexMatrixRpow XA t = cfc (fun x : ℝ => x ^ t) XA := by
            simpa only [complexMatrixRpow] using
              (@CFC.rpow_eq_cfc_real
                (CStarMatrix ι ι ℂ) inferInstance inferInstance
                inferInstance inferInstance inferInstance inferInstance hCFC hNS
                hSemiCanonical hT2Canonical XA t hXA)
          _ = cfc (fun x : ℝ => x ^ (q : ℝ)) XA := by rfl
          _ = cfcN (fun x : ℝ => x ^ (q : ℝ)) XA := hcfPowA.symm
          _ = nnrpowN XA q := hnnA.symm
      have hpowC : complexMatrixRpow XC t = nnrpowN XC q := by
        calc
          complexMatrixRpow XC t = cfc (fun x : ℝ => x ^ t) XC := by
            simpa only [complexMatrixRpow] using
              (@CFC.rpow_eq_cfc_real
                (CStarMatrix ι ι ℂ) inferInstance inferInstance
                inferInstance inferInstance inferInstance inferInstance hCFC hNS
                hSemiCanonical hT2Canonical XC t hXC)
          _ = cfc (fun x : ℝ => x ^ (q : ℝ)) XC := by rfl
          _ = cfcN (fun x : ℝ => x ^ (q : ℝ)) XC := hcfPowC.symm
          _ = nnrpowN XC q := hnnC.symm
      have hmeanA : φ (Matrix.binaryWeightedGeometricMean A B t) =
          ∫ s in Set.Ioi 0, LA (cfcN (Real.rpowIntegrand₀₁ q s) XA) ∂μ := by
        change φ (Ahalf * matrixRpow (Aneg * B * Aneg) t * Ahalf) = _
        rw [map_mul, map_mul,
          realMatrixComplexification_matrixRpow
            (Aneg * B * Aneg) t hmiddleA.posSemidef]
        rw [map_mul, map_mul]
        change φ Ahalf * complexMatrixRpow XA t * φ Ahalf = _
        rw [hpowA, hμA.2]
        exact (LA.integral_comp_comm hμA.1).symm
      have hmeanC : φ (Matrix.binaryWeightedGeometricMean C D t) =
          ∫ s in Set.Ioi 0, LC (cfcN (Real.rpowIntegrand₀₁ q s) XC) ∂μ := by
        change φ (Chalf * matrixRpow (Cneg * D * Cneg) t * Chalf) = _
        rw [map_mul, map_mul,
          realMatrixComplexification_matrixRpow
            (Cneg * D * Cneg) t hmiddleC.posSemidef]
        rw [map_mul, map_mul]
        change φ Chalf * complexMatrixRpow XC t * φ Chalf = _
        rw [hpowC, hμC.2]
        exact (LC.integral_comp_comm hμC.1).symm
      rw [← hmeanA, ← hmeanC] at hintegral
      rw [Matrix.le_iff]
      apply Matrix.nonneg_iff_posSemidef.mp
      apply (realMatrixComplexification_nonneg_iff
        (Matrix.binaryWeightedGeometricMean C D t -
          Matrix.binaryWeightedGeometricMean A B t)).mp
      rw [map_sub]
      exact sub_nonneg.mpr hintegral
    · rw [binaryWeightedGeometricMean_one_aux A B hA hB.posSemidef,
        binaryWeightedGeometricMean_one_aux C D hC hD.posSemidef]
      exact hBD
  · rw [Matrix.binaryWeightedGeometricMean_zero A B hA.posSemidef hB.1,
      Matrix.binaryWeightedGeometricMean_zero C D hC.posSemidef hD.1]
    exact hAC

end MatrixBinaryWeightedGeometricMeanMono
