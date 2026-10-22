import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Topology.Basic
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.OrderClosed
import SOptLib.Model.Iterates
import SOptLib.Model.Iterates.gradientStep
import SOptLib.Model.Norms
import SOptLib.Model.Norms.FiniteMatrixQuadraticForm
import SOptLib.Model.Norms.finiteMatrixQuadraticForm_segment_expansion
import SOptLib.Model.OperatorMeans
import SOptLib.Model.ParameterChoices
import SOptLib.Model.Tensors
import SOptLib.Glue.Algebra
import SOptLib.Glue.Analysis
import SOptLib.Glue.Calculus
import SOptLib.Layer0.Objective.finiteHorizon_convex_regret_le_gradient_inner_sum
import SOptLib.Layer1.Descent
import SOptLib.Layer1.Telescope

section
open scoped BigOperators MatrixOrder

namespace Shampoo

abbrev MatrixSpace (m n : Nat) := Matrix (Fin m) (Fin n) ℝ
abbrev SquareMatrix (n : Nat) := MatrixSpace n n
abbrev GenericSquare (ι : Type*) := Matrix ι ι ℝ

/- Book JSON definitions.PSD_PD_order_and_powers:
   "A^alpha = sum_i lambda_i^alpha u_i u_i^T" for PSD A. -/
noncomputable def psdMatrixPower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : GenericSquare ι) (α : ℝ) (hA : A.PosSemidef) : GenericSquare ι :=
  (hA.1.eigenvectorUnitary : GenericSquare ι) *
    Matrix.diagonal (fun i : ι => (hA.1.eigenvalues i) ^ α) *
    star (hA.1.eigenvectorUnitary : GenericSquare ι)

noncomputable def matrixPower {n : Nat} (A : SquareMatrix n) (α : ℝ)
    (hA : A.PosSemidef) : SquareMatrix n :=
  psdMatrixPower A α hA

/- The spectral definition is exactly Mathlib's continuous functional
   calculus on the positive cone.  This is the cycle-free bridge used by the
   weighted-mean development; it does not introduce a second power
   convention. -/
theorem psdMatrixPower_eq_cfc {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : GenericSquare ι) (s : ℝ) (hC : C.PosSemidef) :
    psdMatrixPower C s hC =
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s) C := by
  classical
  symm
  rw [hC.1.cfc_eq]
  rfl

theorem psdMatrixPower_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : GenericSquare ι} (hAB : A = B) (s : ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    psdMatrixPower A s hA = psdMatrixPower B s hB := by
  subst B
  congr

theorem psdMatrixPower_posDef_of_posDef {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (C : GenericSquare ι) (s : ℝ) (hC : C.PosDef) :
    (psdMatrixPower C s hC.posSemidef).PosDef := by
  classical
  let U : unitary (GenericSquare ι) := hC.posSemidef.1.eigenvectorUnitary
  let lam : ι → ℝ := hC.posSemidef.1.eigenvalues
  have hdiag_pd :
      (Matrix.diagonal (fun i : ι => (lam i) ^ s) : GenericSquare ι).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    exact Real.rpow_pos_of_pos (by simpa [lam] using hC.eigenvalues_pos i) s
  change ((U : GenericSquare ι) *
    Matrix.diagonal (fun i : ι => (lam i) ^ s) *
    star (U : GenericSquare ι)).PosDef
  exact (Matrix.IsUnit.posDef_star_right_conjugate_iff
    (Unitary.toUnits U).isUnit).mpr hdiag_pd

theorem matrixPower_posDef_of_posDef {n : Nat}
    (C : SquareMatrix n) (s : ℝ) (hC : C.PosDef) :
    (matrixPower C s hC.posSemidef).PosDef :=
  psdMatrixPower_posDef_of_posDef C s hC

noncomputable def orderedMatrixProductNat {q n : Nat} (X : Fin q → SquareMatrix n) :
    Nat → SquareMatrix n
  | 0 => 1
  | a + 1 =>
      if h : a < q then
        orderedMatrixProductNat X a * X ⟨a, h⟩
      else
        orderedMatrixProductNat X a

noncomputable def orderedMatrixProduct {q n : Nat} (X : Fin q → SquareMatrix n) :
    SquareMatrix n :=
  orderedMatrixProductNat X q

private theorem orderedMatrixProduct_eq_list_prod {q n : Nat}
    (X : Fin q → SquareMatrix n) :
    orderedMatrixProduct X = (List.ofFn X).prod := by
  change orderedMatrixProductNat X q = (List.ofFn X).prod
  have hprefix : ∀ a : Nat, a ≤ q →
      orderedMatrixProductNat X a = ((List.ofFn X).take a).prod := by
    intro a ha
    induction a with
    | zero =>
        simp [orderedMatrixProductNat]
    | succ a ih =>
        have hlt : a < q := Nat.lt_of_succ_le ha
        rw [orderedMatrixProductNat, dif_pos hlt,
          List.prod_take_succ (List.ofFn X) a]
        · rw [ih (Nat.le_of_lt hlt)]
          rw [List.getElem_ofFn (f := X) (i := a)]
        · simpa using hlt
  calc
    orderedMatrixProductNat X q = ((List.ofFn X).take q).prod := hprefix q le_rfl
    _ = (List.ofFn X).prod := by
      rw [List.take_of_length_le]
      simp

end Shampoo
end

section
open scoped BigOperators ComplexOrder ContinuousFunctionalCalculus MatrixOrder NNReal

namespace Shampoo

/- The real continuous-functional-calculus power used internally by the
   weighted operator mean.  It is propositionally identical to the paper's
   spectral `matrixPower` on PSD inputs, while avoiding proof terms in the
   body of the noncommutative perspective construction. -/
noncomputable def positiveMatrixRpow {n : Nat}
    (A : SquareMatrix n) (t : ℝ) : SquareMatrix n :=
  cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ t) A

theorem positiveMatrixRpow_eq_matrixPower {n : Nat}
    (A : SquareMatrix n) (t : ℝ) (hA : A.PosSemidef) :
    positiveMatrixRpow A t = matrixPower A t hA := by
  rw [positiveMatrixRpow, matrixPower, psdMatrixPower_eq_cfc A t hA]

theorem positiveMatrixRpow_posDef {n : Nat}
    (A : SquareMatrix n) (t : ℝ) (hA : A.PosDef) :
    (positiveMatrixRpow A t).PosDef := by
  rw [positiveMatrixRpow_eq_matrixPower A t hA.posSemidef]
  exact matrixPower_posDef_of_posDef A t hA

theorem positiveMatrixRpow_nonneg {n : Nat}
    (A : SquareMatrix n) (t : ℝ) (hA : A.PosSemidef) :
    0 ≤ positiveMatrixRpow A t := by
  rw [positiveMatrixRpow, ← CFC.rpow_eq_cfc_real (a := A) (y := t)]
  exact CFC.rpow_nonneg

/- Mathlib's operator-monotonicity theorem for real powers is stated in a
   complex C-star algebra.  The entrywise real-to-complex embedding below is
   an order embedding on the self-adjoint cone and intertwines the two real
   functional calculi.  Keeping this transport next to the weighted mean
   avoids depending on the downstream Shampoo development. -/
noncomputable section

@[reducible] private noncomputable def helperModulePrivate_complexCStarMatrixRealCFC {n : Nat} :
    ContinuousFunctionalCalculus ℝ (CStarMatrix (Fin n) (Fin n) ℂ)
      IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

@[reducible] private noncomputable def helperModulePrivate_complexCStarMatrixNonnegSpectrum {n : Nat} :
    NonnegSpectrumClass ℝ (CStarMatrix (Fin n) (Fin n) ℂ) :=
  CStarAlgebra.instNonnegSpectrumClass

private noncomputable def helperModulePrivate_complexMatrixRpow {n : Nat}
    (A : CStarMatrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    CStarMatrix (Fin n) (Fin n) ℂ := by
  letI hCFC : ContinuousFunctionalCalculus ℝ
      (CStarMatrix (Fin n) (Fin n) ℂ) IsSelfAdjoint :=
    helperModulePrivate_complexCStarMatrixRealCFC (n := n)
  letI hNS : NonnegSpectrumClass ℝ (CStarMatrix (Fin n) (Fin n) ℂ) :=
    helperModulePrivate_complexCStarMatrixNonnegSpectrum (n := n)
  exact @CFC.rpow _ inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance hCFC hNS A t

private theorem helperModulePrivate_complexMatrixRpow_mono {n : Nat}
    (A B : CStarMatrix (Fin n) (Fin n) ℂ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hAB : A ≤ B) :
    helperModulePrivate_complexMatrixRpow A t ≤ helperModulePrivate_complexMatrixRpow B t := by
  letI hCFC : ContinuousFunctionalCalculus ℝ
      (CStarMatrix (Fin n) (Fin n) ℂ) IsSelfAdjoint :=
    helperModulePrivate_complexCStarMatrixRealCFC (n := n)
  letI hNS : NonnegSpectrumClass ℝ (CStarMatrix (Fin n) (Fin n) ℂ) :=
    helperModulePrivate_complexCStarMatrixNonnegSpectrum (n := n)
  simpa only [helperModulePrivate_complexMatrixRpow] using
    (CFC.monotone_rpow ⟨ht0, ht1⟩ hAB)

private def helperModulePrivate_realToComplexStarAlgHom : ℝ →⋆ₐ[ℝ] ℂ where
  toFun r := (r : ℂ)
  map_one' := Complex.ofReal_one
  map_mul' := Complex.ofReal_mul
  map_zero' := Complex.ofReal_zero
  map_add' := Complex.ofReal_add
  commutes' := fun _ => rfl
  map_star' := fun r => by simp

private noncomputable def helperModulePrivate_realMatrixCastStarAlgHom {n : Nat} :
    SquareMatrix n →⋆ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  StarAlgHom.mk (AlgHom.mapMatrix helperModulePrivate_realToComplexStarAlgHom.toAlgHom)
    (by
      intro A
      change Matrix.map (star A) helperModulePrivate_realToComplexStarAlgHom =
        star (Matrix.map A helperModulePrivate_realToComplexStarAlgHom)
      ext i j
      simp [helperModulePrivate_realToComplexStarAlgHom, Matrix.star_eq_conjTranspose])

private noncomputable def helperModulePrivate_realMatrixComplexification {n : Nat} :
    SquareMatrix n →⋆ₐ[ℝ] CStarMatrix (Fin n) (Fin n) ℂ :=
  SOptLib.realMatrixComplexification (ι := Fin n)


private theorem helperModulePrivate_starAlgHom_mono_of_le
    {R A B : Type*} [CommRing R]
    [Ring A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
    [Ring B] [PartialOrder B] [StarRing B] [StarOrderedRing B]
    [Algebra R A] [Algebra R B]
    (f : A →⋆ₐ[R] B) {a b : A} (hab : a ≤ b) : f a ≤ f b := by
  exact OrderHomClass.mono f hab

private theorem helperModulePrivate_starAlgEquiv_le_iff
    {R A B : Type*} [CommRing R]
    [Ring A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
    [Ring B] [PartialOrder B] [StarRing B] [StarOrderedRing B]
    [Algebra R A] [Algebra R B]
    (e : A ≃⋆ₐ[R] B) (a b : A) : e a ≤ e b ↔ a ≤ b := by
  exact map_le_map_iff e

private theorem helperModulePrivate_realMatrixComplexification_nonneg_iff {n : Nat}
    (A : SquareMatrix n) : 0 ≤ helperModulePrivate_realMatrixComplexification A ↔ 0 ≤ A := by
  let e : Matrix (Fin n) (Fin n) ℂ ≃⋆ₐ[ℝ] CStarMatrix (Fin n) (Fin n) ℂ :=
    (CStarMatrix.ofMatrixStarAlgEquiv (n := Fin n) (A := ℂ)).restrictScalars ℝ
  let castA : Matrix (Fin n) (Fin n) ℂ := Matrix.map A helperModulePrivate_realToComplexStarAlgHom
  have hcomplexify : helperModulePrivate_realMatrixComplexification A = e castA := by rfl
  rw [hcomplexify]
  change e 0 ≤ e castA ↔ 0 ≤ A
  rw [helperModulePrivate_starAlgEquiv_le_iff e 0 castA]
  constructor
  · intro hcast
    have hcast_psd : castA.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hcast
    rw [Matrix.nonneg_iff_posSemidef]
    constructor
    · apply Matrix.IsHermitian.ext
      intro i j
      apply Complex.ofReal_injective
      simpa [castA, helperModulePrivate_realToComplexStarAlgHom] using hcast_psd.1.apply i j
    · intro v
      let vc : Fin n →₀ ℂ :=
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
          castA, helperModulePrivate_realToComplexStarAlgHom, Complex.star_def, Matrix.map_apply,
          StarAlgHom.coe_mk, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
          OneHom.coe_mk]
        push_cast
        simp [Finsupp.mapRange_apply, helperModulePrivate_realToComplexStarAlgHom]
      rw [heq] at hv
      exact (Complex.nonneg_iff.mp hv).1
  · intro hA
    exact map_nonneg
      helperModulePrivate_realMatrixCastStarAlgHom.toNonUnitalStarAlgHom hA

private theorem realMatrixComplexification_positiveMatrixRpow {n : Nat}
    (A : SquareMatrix n) (t : ℝ) (hA : A.PosSemidef) :
    helperModulePrivate_realMatrixComplexification (positiveMatrixRpow A t) =
      helperModulePrivate_complexMatrixRpow (helperModulePrivate_realMatrixComplexification A) t := by
  letI hCFC : ContinuousFunctionalCalculus ℝ
      (CStarMatrix (Fin n) (Fin n) ℂ) IsSelfAdjoint :=
    helperModulePrivate_complexCStarMatrixRealCFC (n := n)
  letI hNS : NonnegSpectrumClass ℝ (CStarMatrix (Fin n) (Fin n) ℂ) :=
    helperModulePrivate_complexCStarMatrixNonnegSpectrum (n := n)
  letI hSemi : IsSemitopologicalRing (CStarMatrix (Fin n) (Fin n) ℂ) :=
    inferInstance
  letI hT2 : T2Space (CStarMatrix (Fin n) (Fin n) ℂ) := inferInstance
  have hnonneg : 0 ≤ helperModulePrivate_realMatrixComplexification A :=
    (helperModulePrivate_realMatrixComplexification_nonneg_iff A).2 hA.nonneg
  have hrpow_eq :
      helperModulePrivate_complexMatrixRpow (helperModulePrivate_realMatrixComplexification A) t =
        cfc (fun x : ℝ => x ^ t) (helperModulePrivate_realMatrixComplexification A) := by
    rw [helperModulePrivate_complexMatrixRpow]
    exact @CFC.rpow_eq_cfc_real _ inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance hCFC hNS hSemi hT2
      (helperModulePrivate_realMatrixComplexification A) t hnonneg
  rw [positiveMatrixRpow, hrpow_eq]
  have hf : ContinuousOn (fun x : ℝ => x ^ t) (spectrum ℝ A) := by
    have hfin : (spectrum ℝ A).Finite := by
      rw [hA.1.spectrum_real_eq_range_eigenvalues]
      exact Set.finite_range _
    exact hfin.continuousOn _
  exact helperModulePrivate_realMatrixComplexification.map_cfc (fun x : ℝ => x ^ t) A
    (hf := hf)
    (hφ := by
      have hcast : Continuous (helperModulePrivate_realMatrixCastStarAlgHom (n := n)) := by
        apply continuous_pi
        intro i
        apply continuous_pi
        intro j
        change Continuous (fun M : SquareMatrix n => (M i j : ℂ))
        fun_prop
      change Continuous (fun M : SquareMatrix n =>
        CStarMatrix.ofMatrix (helperModulePrivate_realMatrixCastStarAlgHom M))
      exact CStarMatrix.uniformEmbedding_ofMatrix.isUniformInducing.isInducing.continuous.comp
        hcast)
    (ha := hA.1)
    (hφa := by
      calc
        star (helperModulePrivate_realMatrixComplexification A) =
            helperModulePrivate_realMatrixComplexification (star A) :=
          (map_star helperModulePrivate_realMatrixComplexification A).symm
        _ = helperModulePrivate_realMatrixComplexification A := by
          change helperModulePrivate_realMatrixComplexification A.transpose = helperModulePrivate_realMatrixComplexification A
          exact congrArg helperModulePrivate_realMatrixComplexification hA.1)

theorem positiveMatrixRpow_mono {n : Nat}
    (A B : SquareMatrix n) (t : ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hAB : A ≤ B)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    positiveMatrixRpow A t ≤ positiveMatrixRpow B t := by
  simpa only [positiveMatrixRpow] using
    TensorsProofSupport.Matrix.cfc_rpow_mono_of_posSemidef A B t hA hAB ⟨ht0, ht1⟩

end

theorem positiveMatrixRpow_zero {n : Nat}
    (A : SquareMatrix n) (hA : A.PosSemidef) :
    positiveMatrixRpow A 0 = 1 := by
  rw [positiveMatrixRpow, ← CFC.rpow_eq_cfc_real (a := A) (y := 0)]
  exact CFC.rpow_zero A

theorem positiveMatrixRpow_one {n : Nat}
    (A : SquareMatrix n) (hA : A.PosSemidef) :
    positiveMatrixRpow A 1 = A := by
  rw [positiveMatrixRpow, ← CFC.rpow_eq_cfc_real (a := A) (y := 1)]
  exact CFC.rpow_one A

theorem positiveMatrixRpow_add {n : Nat}
    (A : SquareMatrix n) (s t : ℝ) (hA : A.PosDef) :
    positiveMatrixRpow A (s + t) =
      positiveMatrixRpow A s * positiveMatrixRpow A t := by
  rw [positiveMatrixRpow, positiveMatrixRpow, positiveMatrixRpow,
    ← CFC.rpow_eq_cfc_real (a := A) (y := s + t),
    ← CFC.rpow_eq_cfc_real (a := A) (y := s),
    ← CFC.rpow_eq_cfc_real (a := A) (y := t)]
  exact CFC.rpow_add hA.isUnit

theorem positiveMatrixRpow_neg_one_eq_nonsing_inv {n : Nat}
    (A : SquareMatrix n) (hA : A.PosDef) :
    positiveMatrixRpow A (-1 : ℝ) = A⁻¹ := by
  have hleft : positiveMatrixRpow A (-1 : ℝ) * A = 1 := by
    calc
      positiveMatrixRpow A (-1 : ℝ) * A =
          positiveMatrixRpow A (-1 : ℝ) * positiveMatrixRpow A 1 := by
            rw [positiveMatrixRpow_one A hA.posSemidef]
      _ = positiveMatrixRpow A ((-1 : ℝ) + 1) :=
        (positiveMatrixRpow_add A _ _ hA).symm
      _ = 1 := by
        norm_num
        exact positiveMatrixRpow_zero A hA.posSemidef
  exact (Matrix.inv_eq_left_inv hleft).symm

/- Inversion reverses the Loewner order on positive-definite real matrices.
   The proof uses the already established order-reflecting complexification,
   so the result keeps the paper-facing matrices real while reusing Mathlib's
   canonical C-star-algebra inverse-order theorem. -/
theorem nonsing_inv_antitone_of_posDef {n : Nat}
    (A B : SquareMatrix n) (hA : A.PosDef) (hB : B.PosDef) (hAB : A ≤ B) :
    B⁻¹ ≤ A⁻¹ := by
  exact Matrix.nonsing_inv_antitone_of_posDef (A := A) (B := B) (hA := hA) (hAB := hAB)

/- The harmonic resolvent appearing in the integral representation of the
   weighted operator geometric mean.  Unlike the final perspective, its joint
   monotonicity is an immediate consequence of the antitonicity of inversion. -/
noncomputable def weightedHarmonicResolvent {n : Nat}
    (A B : SquareMatrix n) (s : ℝ) : SquareMatrix n :=
  (A⁻¹ + s • B⁻¹)⁻¹

theorem weightedHarmonicResolvent_posDef {n : Nat}
    (A B : SquareMatrix n) (s : ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hs : 0 < s) :
    (weightedHarmonicResolvent A B s).PosDef := by
  exact (hA.inv.add (hB.inv.smul hs)).inv

theorem weightedHarmonicResolvent_mono {n : Nat}
    (A B C D : SquareMatrix n) (s : ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef) (hD : D.PosDef)
    (hAC : A ≤ C) (hBD : B ≤ D) (hs : 0 < s) :
    weightedHarmonicResolvent A B s ≤
      weightedHarmonicResolvent C D s := by
  simpa only [weightedHarmonicResolvent] using
    (Matrix.weightedHarmonicResolvent_mono A B C D s hA hB hAC hBD hs.le)

theorem positiveMatrixRpow_commute_right {n : Nat}
    (A B : SquareMatrix n) (t : ℝ) (hAB : A * B = B * A) :
    positiveMatrixRpow A t * B = B * positiveMatrixRpow A t := by
  change Commute (positiveMatrixRpow A t) B
  exact (show Commute A B from hAB).cfc_real (fun x : ℝ => x ^ t)

theorem positiveMatrixRpow_neg_half_conjugate_of_commute {n : Nat}
    (A B : SquareMatrix n) (hA : A.PosDef) (hAB : A * B = B * A) :
    positiveMatrixRpow A (-(1 / 2 : ℝ)) * B *
        positiveMatrixRpow A (-(1 / 2 : ℝ)) =
      positiveMatrixRpow A (-1 : ℝ) * B := by
  have hcomm := positiveMatrixRpow_commute_right A B (-(1 / 2 : ℝ)) hAB
  calc
    positiveMatrixRpow A (-(1 / 2 : ℝ)) * B *
        positiveMatrixRpow A (-(1 / 2 : ℝ)) =
        (positiveMatrixRpow A (-(1 / 2 : ℝ)) *
          positiveMatrixRpow A (-(1 / 2 : ℝ))) * B := by
            rw [mul_assoc, ← hcomm, ← mul_assoc]
    _ = positiveMatrixRpow A
          ((-(1 / 2 : ℝ)) + (-(1 / 2 : ℝ))) * B := by
            rw [positiveMatrixRpow_add A _ _ hA]
    _ = positiveMatrixRpow A (-1 : ℝ) * B := by norm_num

theorem positiveMatrixRpow_neg_half_mul_half {n : Nat}
    (A : SquareMatrix n) (hA : A.PosDef) :
    positiveMatrixRpow A (-(1 / 2 : ℝ)) *
        positiveMatrixRpow A (1 / 2 : ℝ) = 1 := by
  rw [← positiveMatrixRpow_add A _ _ hA]
  norm_num
  exact positiveMatrixRpow_zero A hA.posSemidef

theorem positiveMatrixRpow_half_mul_neg_half {n : Nat}
    (A : SquareMatrix n) (hA : A.PosDef) :
    positiveMatrixRpow A (1 / 2 : ℝ) *
        positiveMatrixRpow A (-(1 / 2 : ℝ)) = 1 := by
  rw [← positiveMatrixRpow_add A _ _ hA]
  norm_num
  exact positiveMatrixRpow_zero A hA.posSemidef

theorem positiveMatrixRpow_half_mul_half {n : Nat}
    (A : SquareMatrix n) (hA : A.PosDef) :
    positiveMatrixRpow A (1 / 2 : ℝ) *
        positiveMatrixRpow A (1 / 2 : ℝ) = A := by
  rw [← positiveMatrixRpow_add A _ _ hA]
  norm_num
  exact positiveMatrixRpow_one A hA.posSemidef

/- The rational perspective integrand occurring in the integral proof of
   Kubo--Ando monotonicity is exactly a positive scalar multiple of the
   jointly monotone harmonic resolvent.  This is purely matrix algebra; in
   particular it does not assume that `A` and `B` commute. -/
private theorem weightedHarmonicResolvent_eq_rpow_perspective_integrand {n : Nat}
    (A B : SquareMatrix n) (s : ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hs : 0 < s) :
    positiveMatrixRpow A (1 / 2 : ℝ) *
          ((s⁻¹) • (1 : SquareMatrix n) -
            (s • (1 : SquareMatrix n) +
              positiveMatrixRpow A (-(1 / 2 : ℝ)) * B *
                positiveMatrixRpow A (-(1 / 2 : ℝ)))⁻¹) *
        positiveMatrixRpow A (1 / 2 : ℝ) =
      (s⁻¹) • weightedHarmonicResolvent A B s := by
  simpa only [positiveMatrixRpow, weightedHarmonicResolvent,
    ← CFC.rpow_eq_cfc_real hA.posSemidef.nonneg] using
    (Matrix.rpowPerspectiveKernel_eq_smul_weightedHarmonicResolvent A B s hA hB hs)

/- Algebraic evaluation of Mathlib's scalar `rpow` integrand by the real
   matrix CFC.  The positivity assumption is used only to keep `s + x` away
   from zero on the spectrum. -/
private theorem cfc_rpowIntegrand_eq_resolvent_kernel {n : Nat}
    (X : SquareMatrix n) (p s : ℝ) (hX : X.PosSemidef) (hs : 0 < s) :
    cfc (R := ℝ) (p := IsSelfAdjoint) (Real.rpowIntegrand₀₁ p s) X =
      (s ^ p) • ((s⁻¹) • (1 : SquareMatrix n) -
        (s • (1 : SquareMatrix n) + X)⁻¹) := by
  exact TensorsProofSupport.Matrix.cfc_rpowIntegrand₀₁_eq_resolvent X p s hX hs

/- After taking the perspective, every scalar `rpow` integrand becomes the
   harmonic-resolvent kernel used above.  This is the pointwise bridge needed
   by the integral proof of joint monotonicity. -/
private theorem rpowPerspectiveIntegrand_eq_smul_weightedHarmonicResolvent {n : Nat}
    (A B : SquareMatrix n) (p s : ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hs : 0 < s) :
    let Aneg := positiveMatrixRpow A (-(1 / 2 : ℝ))
    let Ahalf := positiveMatrixRpow A (1 / 2 : ℝ)
    Ahalf * cfc (R := ℝ) (p := IsSelfAdjoint)
          (Real.rpowIntegrand₀₁ p s) (Aneg * B * Aneg) * Ahalf =
      (s ^ (p - 1)) • weightedHarmonicResolvent A B s := by
  simpa only [positiveMatrixRpow, weightedHarmonicResolvent,
    ← CFC.rpow_eq_cfc_real hA.posSemidef.nonneg] using
    (Matrix.rpowPerspectiveIntegrand_eq_smul_weightedHarmonicResolvent
      A B p s hA hB hs)

/- The preceding real-matrix identity transported into the complex C-star
   matrix algebra, where Mathlib's Bochner integral representation is
   available. -/
private theorem complexifiedRpowPerspectiveIntegrand_eq_smul_resolvent {n : Nat}
    [ContinuousFunctionalCalculus ℝ
      (CStarMatrix (Fin n) (Fin n) ℂ) IsSelfAdjoint]
    [NonnegSpectrumClass ℝ (CStarMatrix (Fin n) (Fin n) ℂ)]
    (A B : SquareMatrix n) (p s : ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hs : 0 < s) :
    let φ := helperModulePrivate_realMatrixComplexification (n := n)
    let Aneg := positiveMatrixRpow A (-(1 / 2 : ℝ))
    let Ahalf := positiveMatrixRpow A (1 / 2 : ℝ)
    φ Ahalf * cfc (R := ℝ) (p := IsSelfAdjoint)
          (Real.rpowIntegrand₀₁ p s) (φ Aneg * φ B * φ Aneg) * φ Ahalf =
      (s ^ (p - 1)) • φ (weightedHarmonicResolvent A B s) := by
  let φ := helperModulePrivate_realMatrixComplexification (n := n)
  let Aneg := positiveMatrixRpow A (-(1 / 2 : ℝ))
  let Ahalf := positiveMatrixRpow A (1 / 2 : ℝ)
  have hAneg : Aneg.PosDef := positiveMatrixRpow_posDef A _ hA
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
        have hcast : Continuous (helperModulePrivate_realMatrixCastStarAlgHom (n := n)) := by
          apply continuous_pi
          intro i
          apply continuous_pi
          intro j
          change Continuous (fun M : SquareMatrix n => (M i j : ℂ))
          fun_prop
        change Continuous (fun M : SquareMatrix n =>
          CStarMatrix.ofMatrix (helperModulePrivate_realMatrixCastStarAlgHom M))
        exact CStarMatrix.uniformEmbedding_ofMatrix.isUniformInducing.isInducing.continuous.comp
          hcast)
      (ha := hmiddle.1)
      (hφa := by
        calc
          star (φ (Aneg * B * Aneg)) = φ (star (Aneg * B * Aneg)) :=
            (map_star φ (Aneg * B * Aneg)).symm
          _ = φ (Aneg * B * Aneg) := by
            apply congrArg φ
            exact hmiddle.1)
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

private theorem complexifiedRpowPerspectiveIntegrand_mono {n : Nat}
    [ContinuousFunctionalCalculus ℝ
      (CStarMatrix (Fin n) (Fin n) ℂ) IsSelfAdjoint]
    [NonnegSpectrumClass ℝ (CStarMatrix (Fin n) (Fin n) ℂ)]
    (A B C D : SquareMatrix n) (p s : ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef) (hD : D.PosDef)
    (hAC : A ≤ C) (hBD : B ≤ D) (hs : 0 < s) :
    let φ := helperModulePrivate_realMatrixComplexification (n := n)
    let Aneg := positiveMatrixRpow A (-(1 / 2 : ℝ))
    let Ahalf := positiveMatrixRpow A (1 / 2 : ℝ)
    let Cneg := positiveMatrixRpow C (-(1 / 2 : ℝ))
    let Chalf := positiveMatrixRpow C (1 / 2 : ℝ)
    φ Ahalf * cfc (R := ℝ) (p := IsSelfAdjoint)
          (Real.rpowIntegrand₀₁ p s) (φ Aneg * φ B * φ Aneg) * φ Ahalf ≤
      φ Chalf * cfc (R := ℝ) (p := IsSelfAdjoint)
          (Real.rpowIntegrand₀₁ p s) (φ Cneg * φ D * φ Cneg) * φ Chalf := by
  let φ := helperModulePrivate_realMatrixComplexification (n := n)
  let Aneg := positiveMatrixRpow A (-(1 / 2 : ℝ))
  let Ahalf := positiveMatrixRpow A (1 / 2 : ℝ)
  let Cneg := positiveMatrixRpow C (-(1 / 2 : ℝ))
  let Chalf := positiveMatrixRpow C (1 / 2 : ℝ)
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
      helperModulePrivate_starAlgHom_mono_of_le φ hreal
    _ = (s ^ (p - 1)) • φ (weightedHarmonicResolvent C D s) :=
      map_smul φ (s ^ (p - 1)) (weightedHarmonicResolvent C D s)

/- The Loewner cone in a finite complex matrix algebra is preserved by
   Bochner integration.  This proof deliberately uses the canonical real
   scalar action on `CStarMatrix`: it scalarizes against arbitrary vectors,
   commutes those continuous real-linear functionals through the integral,
   and reconstructs positive semidefiniteness. -/
private theorem cstarMatrix_integral_mono_ae_via_quadratic_forms
    {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X} {n : Nat}
    {f g : X → CStarMatrix (Fin n) (Fin n) ℂ}
    (hf : MeasureTheory.Integrable f μ) (hg : MeasureTheory.Integrable g μ)
    (hfg : ∀ᵐ x ∂μ, f x ≤ g x) :
    (∫ x, f x ∂μ) ≤ ∫ x, g x ∂μ := by
  exact TensorsProofSupport.CStarMatrix.integral_mono_ae hf hg hfg

/- Attempted explicit nonunital-CFC bridge.  The statement itself currently
   exposes Mathlib's competing real scalar actions on `CStarMatrix`: the
   `NonUnitalContinuousFunctionalCalculus` binder requests a different hidden
   `IsScalarTower` instance from the preceding explicit binder. -/
/-
private theorem complexifiedRpowPerspectiveIntegrand_mono_cfcₙ {n : Nat}
    [Module ℝ (CStarMatrix (Fin n) (Fin n) ℂ)]
    [IsScalarTower ℝ
      (CStarMatrix (Fin n) (Fin n) ℂ)
      (CStarMatrix (Fin n) (Fin n) ℂ)]
    [SMulCommClass ℝ
      (CStarMatrix (Fin n) (Fin n) ℂ)
      (CStarMatrix (Fin n) (Fin n) ℂ)]
    [ContinuousFunctionalCalculus ℝ
      (CStarMatrix (Fin n) (Fin n) ℂ) IsSelfAdjoint]
    [NonUnitalContinuousFunctionalCalculus ℝ
      (CStarMatrix (Fin n) (Fin n) ℂ) IsSelfAdjoint]
    [NonnegSpectrumClass ℝ (CStarMatrix (Fin n) (Fin n) ℂ)]
    (A B C D : SquareMatrix n) (p s : ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef) (hD : D.PosDef)
    (hAC : A ≤ C) (hBD : B ≤ D)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hs : 0 < s)
    (hXA : 0 ≤
      let φ := helperModulePrivate_realMatrixComplexification (n := n)
      let Aneg := positiveMatrixRpow A (-(1 / 2 : ℝ))
      φ Aneg * φ B * φ Aneg)
    (hXC : 0 ≤
      let φ := helperModulePrivate_realMatrixComplexification (n := n)
      let Cneg := positiveMatrixRpow C (-(1 / 2 : ℝ))
      φ Cneg * φ D * φ Cneg) :
    let φ := helperModulePrivate_realMatrixComplexification (n := n)
    let Aneg := positiveMatrixRpow A (-(1 / 2 : ℝ))
    let Ahalf := positiveMatrixRpow A (1 / 2 : ℝ)
    let Cneg := positiveMatrixRpow C (-(1 / 2 : ℝ))
    let Chalf := positiveMatrixRpow C (1 / 2 : ℝ)
    φ Ahalf * cfcₙ (Real.rpowIntegrand₀₁ p s)
          (φ Aneg * φ B * φ Aneg) * φ Ahalf ≤
      φ Chalf * cfcₙ (Real.rpowIntegrand₀₁ p s)
          (φ Cneg * φ D * φ Cneg) * φ Chalf := by
  let φ := helperModulePrivate_realMatrixComplexification (n := n)
  let Aneg := positiveMatrixRpow A (-(1 / 2 : ℝ))
  let Ahalf := positiveMatrixRpow A (1 / 2 : ℝ)
  let Cneg := positiveMatrixRpow C (-(1 / 2 : ℝ))
  let Chalf := positiveMatrixRpow C (1 / 2 : ℝ)
  let XA := φ Aneg * φ B * φ Aneg
  let XC := φ Cneg * φ D * φ Cneg
  have hfA : ContinuousOn (Real.rpowIntegrand₀₁ p s) (quasispectrum ℝ XA) := by
    exact (Real.continuousOn_rpowIntegrand₀₁_Ici hp hs).mono (by
      intro x hx
      exact quasispectrum_nonneg_of_nonneg XA hXA x hx)
  have hfC : ContinuousOn (Real.rpowIntegrand₀₁ p s) (quasispectrum ℝ XC) := by
    exact (Real.continuousOn_rpowIntegrand₀₁_Ici hp hs).mono (by
      intro x hx
      exact quasispectrum_nonneg_of_nonneg XC hXC x hx)
  change φ Ahalf * cfcₙ (Real.rpowIntegrand₀₁ p s) XA * φ Ahalf ≤
    φ Chalf * cfcₙ (Real.rpowIntegrand₀₁ p s) XC * φ Chalf
  rw [cfcₙ_eq_cfc (hf := hfA) (hf0 := Real.rpowIntegrand₀₁_zero_right),
    cfcₙ_eq_cfc (hf := hfC) (hf0 := Real.rpowIntegrand₀₁_zero_right)]
  exact complexifiedRpowPerspectiveIntegrand_mono
    A B C D p s hA hB hC hD hAC hBD hs
-/

/- The binary weighted operator geometric mean.  This is the genuine
   noncommutative perspective object whose recursive finite-family iteration
   is monotone.  For commuting inputs its value reduces to
   `A^(1-t) * B^t`; that evaluation is a theorem obligation, not its
   definition. -/
noncomputable def binaryWeightedGeometricMean {n : Nat}
    (A B : SquareMatrix n) (t : ℝ) : SquareMatrix n :=
  Matrix.binaryWeightedGeometricMean A B t

private theorem selfAdjoint_mul_mul_mono {n : Nat}
    (A B C : SquareMatrix n) (hC : Matrix.conjTranspose C = C)
    (hAB : A ≤ B) : C * A * C ≤ C * B * C := by
  exact IsSelfAdjoint.conjugate_le_conjugate hAB hC

/- Monotonicity in the second coordinate is the direct Löwner--Heinz half of
   joint monotonicity.  The first-coordinate half is the genuinely missing
   Kubo--Ando perspective argument; this theorem isolates it from the already
   checked real/complex transport and congruence algebra. -/
theorem binaryWeightedGeometricMean_mono_right {n : Nat}
    (A B D : SquareMatrix n) (t : ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hD : D.PosDef)
    (hBD : B ≤ D) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    binaryWeightedGeometricMean A B t ≤
      binaryWeightedGeometricMean A D t := by
  exact Matrix.binaryWeightedGeometricMean_mono
    A B A D t hA hB hA hD le_rfl hBD ht0 ht1

theorem binaryWeightedGeometricMean_posDef {n : Nat}
    (A B : SquareMatrix n) (t : ℝ) (hA : A.PosDef) (hB : B.PosDef) :
    (binaryWeightedGeometricMean A B t).PosDef := by
  exact Matrix.binaryWeightedGeometricMean_posDef A B t hA hB

theorem binaryWeightedGeometricMean_zero {n : Nat}
    (A B : SquareMatrix n) (hA : A.PosDef) (hB : B.PosDef) :
    binaryWeightedGeometricMean A B 0 = A := by
  exact Matrix.binaryWeightedGeometricMean_zero A B hA.posSemidef hB.1

theorem binaryWeightedGeometricMean_one {n : Nat}
    (A B : SquareMatrix n) (hA : A.PosDef) (hB : B.PosDef) :
    binaryWeightedGeometricMean A B 1 = B := by
  exact Matrix.binaryWeightedGeometricMean_one A B (hA := hA) (hB := hB.posSemidef)

/- Joint monotonicity of the binary Kubo--Ando weighted geometric mean.
   The interior case uses the nonunital CFC integral representation under the
   canonical scalar action and the preceding order-preserving integral lemma. -/
private theorem binaryWeightedGeometricMean_mono_joint {n : Nat}
    (A B C D : SquareMatrix n) (t : ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef) (hD : D.PosDef)
    (hAC : A ≤ C) (hBD : B ≤ D) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    binaryWeightedGeometricMean A B t ≤
      binaryWeightedGeometricMean C D t := by
  exact Matrix.binaryWeightedGeometricMean_mono
    (A := A) (B := B) (C := C) (D := D) (t := t)
    hA hB hC hD hAC hBD ht0 ht1

/- The following attempted aggregation proof is retained as route-local
   implementation notes.  Choosing `Module.complexToReal` resolves the
   ordered-Bochner instances, but the `cfcₙ` terms returned by the integral
   theorem still carry hidden scalar-action instances incompatible with the
   unital CFC transport helper above. -/
/-
/- Genuine joint monotonicity of the binary Kubo--Ando weighted geometric
   mean.  The interior case is proved by the common positive-measure integral
   representation; the endpoint cases are the checked algebraic identities
   above. -/
private theorem binaryWeightedGeometricMean_joint_mono {n : Nat}
    (A B C D : SquareMatrix n) (t : ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef) (hD : D.PosDef)
    (hAC : A ≤ C) (hBD : B ≤ D) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    binaryWeightedGeometricMean A B t ≤
      binaryWeightedGeometricMean C D t := by
  rcases lt_or_eq_of_le ht0 with htpos | rfl
  · rcases lt_or_eq_of_le ht1 with htlt | rfl
    · letI hRealModule : Module ℝ (CStarMatrix (Fin n) (Fin n) ℂ) :=
        Module.complexToReal (CStarMatrix (Fin n) (Fin n) ℂ)
      letI hRealNormedSpace : NormedSpace ℝ
          (CStarMatrix (Fin n) (Fin n) ℂ) :=
        NormedSpace.complexToReal
      letI hCFC : ContinuousFunctionalCalculus ℝ
          (CStarMatrix (Fin n) (Fin n) ℂ) IsSelfAdjoint :=
        IsSelfAdjoint.instContinuousFunctionalCalculus
      letI hNCFC : NonUnitalContinuousFunctionalCalculus ℝ
          (CStarMatrix (Fin n) (Fin n) ℂ) IsSelfAdjoint :=
        ContinuousFunctionalCalculus.toNonUnital
      letI hNS : NonnegSpectrumClass ℝ (CStarMatrix (Fin n) (Fin n) ℂ) :=
        CStarAlgebra.instNonnegSpectrumClass
      haveI hTower : IsScalarTower ℝ
          (CStarMatrix (Fin n) (Fin n) ℂ)
          (CStarMatrix (Fin n) (Fin n) ℂ) :=
        ⟨fun r X Y => by
          change (r • X) * Y = r • (X * Y)
          ext i j
          change (∑ k, ((r : ℂ) * X i k) * Y k j) =
            (r : ℂ) * ∑ k, X i k * Y k j
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring⟩
      haveI hComm : SMulCommClass ℝ
          (CStarMatrix (Fin n) (Fin n) ℂ)
          (CStarMatrix (Fin n) (Fin n) ℂ) :=
        ⟨fun r X Y => by
          simp only [smul_eq_mul]
          change r • (X * Y) = X * (r • Y)
          ext i j
          change (r : ℂ) * (∑ k, X i k * Y k j) =
            ∑ k, X i k * ((r : ℂ) * Y k j)
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring⟩
      have hsmul_nonneg (r : ℝ) (hr : 0 ≤ r)
          (X : CStarMatrix (Fin n) (Fin n) ℂ) (hX : 0 ≤ X) : 0 ≤ r • X := by
        rw [StarOrderedRing.nonneg_iff] at hX ⊢
        induction hX using AddSubmonoid.closure_induction with
        | mem W hW =>
            obtain ⟨Z, rfl⟩ := hW
            apply AddSubmonoid.subset_closure
            refine ⟨Real.sqrt r • Z, ?_⟩
            ext i j
            simp only [CStarMatrix.mul_apply, CStarMatrix.star_eq_conjTranspose,
              CStarMatrix.conjTranspose_apply, Pi.smul_apply]
            change (∑ x, star ((Real.sqrt r : ℂ) * Z x i) *
                ((Real.sqrt r : ℂ) * Z x j)) =
              (r : ℂ) * ∑ x, star (Z x i) * Z x j
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            rw [star_mul']
            rw [Complex.star_def, Complex.conj_ofReal]
            change (((Real.sqrt r : ℂ) * star (Z k i)) *
                ((Real.sqrt r : ℂ) * Z k j)) =
              (r : ℂ) * (star (Z k i) * Z k j)
            calc
              ((Real.sqrt r : ℂ) * star (Z k i)) *
                  ((Real.sqrt r : ℂ) * Z k j) =
                  ((Real.sqrt r * Real.sqrt r : ℝ) : ℂ) *
                    (star (Z k i) * Z k j) := by push_cast; ring
              _ = (r : ℂ) * (star (Z k i) * Z k j) := by
                rw [Real.mul_self_sqrt hr]
        | zero =>
            have heq : r • (0 : CStarMatrix (Fin n) (Fin n) ℂ) = 0 := by
              ext i j
              simp
            rw [heq]
            exact AddSubmonoid.zero_mem
              (AddSubmonoid.closure
                (Set.range fun Z : CStarMatrix (Fin n) (Fin n) ℂ => star Z * Z))
        | add X Y _hX _hY ihX ihY =>
            have heq : r • (X + Y) = r • X + r • Y := by
              ext i j
              change (r : ℂ) * (X i j + Y i j) =
                (r : ℂ) * X i j + (r : ℂ) * Y i j
              ring
            rw [heq]
            exact AddSubmonoid.add_mem
                (AddSubmonoid.closure
                  (Set.range fun Z : CStarMatrix (Fin n) (Fin n) ℂ => star Z * Z))
                ihX ihY
      letI hOrder : IsOrderedModule ℝ (CStarMatrix (Fin n) (Fin n) ℂ) := {
        smul_le_smul_of_nonneg_left := fun r hr X Y hXY => by
          rw [← sub_nonneg]
          have heq : r • (Y - X) = r • Y - r • X := by
            ext i j
            change (r : ℂ) * (Y i j - X i j) =
              (r : ℂ) * Y i j - (r : ℂ) * X i j
            ring
          rw [← heq]
          exact hsmul_nonneg r hr (Y - X) (sub_nonneg.mpr hXY)
        smul_le_smul_of_nonneg_right := fun X hX r s hrs => by
          rw [← sub_nonneg]
          have heq : (s - r) • X = s • X - r • X := by
            ext i j
            change ((s - r : ℝ) : ℂ) * X i j =
              (s : ℂ) * X i j - (r : ℂ) * X i j
            push_cast
            ring
          rw [← heq]
          exact hsmul_nonneg (s - r) (sub_nonneg.mpr hrs) X hX }
      let φ := helperModulePrivate_realMatrixComplexification (n := n)
      let Aneg := positiveMatrixRpow A (-(1 / 2 : ℝ))
      let Ahalf := positiveMatrixRpow A (1 / 2 : ℝ)
      let Cneg := positiveMatrixRpow C (-(1 / 2 : ℝ))
      let Chalf := positiveMatrixRpow C (1 / 2 : ℝ)
      let XA : CStarMatrix (Fin n) (Fin n) ℂ := φ Aneg * φ B * φ Aneg
      let XC : CStarMatrix (Fin n) (Fin n) ℂ := φ Cneg * φ D * φ Cneg
      let q : ℝ≥0 := ⟨t, ht0⟩
      have hq : q ∈ Set.Ioo (0 : ℝ≥0) 1 := by
        constructor
        · exact_mod_cast htpos
        · exact_mod_cast htlt
      have hAneg : Aneg.PosDef := positiveMatrixRpow_posDef A _ hA
      have hCneg : Cneg.PosDef := positiveMatrixRpow_posDef C _ hC
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
        have himage := map_nonneg
          φ.toNonUnitalStarAlgHom hmiddleA.posSemidef.nonneg
        simpa only [XA, map_mul] using himage
      have hXC : 0 ≤ XC := by
        have himage := map_nonneg
          φ.toNonUnitalStarAlgHom hmiddleC.posSemidef.nonneg
        simpa only [XC, map_mul] using himage
      obtain ⟨μ, hμ⟩ :=
        CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁
          (CStarMatrix (Fin n) (Fin n) ℂ) hq
      have hμA := hμ XA hXA
      have hμC := hμ XC hXC
      let LA := ContinuousLinearMap.mulLeftRight ℂ
        (CStarMatrix (Fin n) (Fin n) ℂ) (φ Ahalf) (φ Ahalf)
      let LC := ContinuousLinearMap.mulLeftRight ℂ
        (CStarMatrix (Fin n) (Fin n) ℂ) (φ Chalf) (φ Chalf)
      have hintA : MeasureTheory.IntegrableOn
          (fun s => LA (cfcₙ (Real.rpowIntegrand₀₁ q s) XA)) (Set.Ioi 0) μ :=
        LA.integrable_comp hμA.1
      have hintC : MeasureTheory.IntegrableOn
          (fun s => LC (cfcₙ (Real.rpowIntegrand₀₁ q s) XC)) (Set.Ioi 0) μ :=
        LC.integrable_comp hμC.1
      have hintegral :
          (∫ s in Set.Ioi 0, LA (cfcₙ (Real.rpowIntegrand₀₁ q s) XA) ∂μ) ≤
            ∫ s in Set.Ioi 0, LC (cfcₙ (Real.rpowIntegrand₀₁ q s) XC) ∂μ := by
        apply MeasureTheory.integral_mono_ae hintA hintC
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
        have hqt : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨htpos, htlt⟩
        have hpoint := complexifiedRpowPerspectiveIntegrand_mono_cfcₙ
          A B C D t s hA hB hC hD hAC hBD hqt hs hXA hXC
        simpa only [LA, LC, XA, XC, q, ContinuousLinearMap.mulLeftRight_apply] using hpoint
      have hpowA : helperModulePrivate_complexMatrixRpow XA t = XA ^ q := by
        simpa only [helperModulePrivate_complexMatrixRpow] using
          (CFC.nnrpow_eq_rpow (a := XA) hq.1).symm
      have hpowC : helperModulePrivate_complexMatrixRpow XC t = XC ^ q := by
        simpa only [helperModulePrivate_complexMatrixRpow] using
          (CFC.nnrpow_eq_rpow (a := XC) hq.1).symm
      have hmeanA : φ (binaryWeightedGeometricMean A B t) =
          ∫ s in Set.Ioi 0, LA (cfcₙ (Real.rpowIntegrand₀₁ q s) XA) ∂μ := by
        change φ (Ahalf * positiveMatrixRpow (Aneg * B * Aneg) t * Ahalf) = _
        rw [map_mul, map_mul,
          realMatrixComplexification_positiveMatrixRpow
            (Aneg * B * Aneg) t hmiddleA.posSemidef]
        rw [map_mul, map_mul]
        change φ Ahalf * helperModulePrivate_complexMatrixRpow XA t * φ Ahalf = _
        rw [hpowA, hμA.2]
        exact (LA.integral_comp_comm hμA.1).symm
      have hmeanC : φ (binaryWeightedGeometricMean C D t) =
          ∫ s in Set.Ioi 0, LC (cfcₙ (Real.rpowIntegrand₀₁ q s) XC) ∂μ := by
        change φ (Chalf * positiveMatrixRpow (Cneg * D * Cneg) t * Chalf) = _
        rw [map_mul, map_mul,
          realMatrixComplexification_positiveMatrixRpow
            (Cneg * D * Cneg) t hmiddleC.posSemidef]
        rw [map_mul, map_mul]
        change φ Chalf * helperModulePrivate_complexMatrixRpow XC t * φ Chalf = _
        rw [hpowC, hμC.2]
        exact (LC.integral_comp_comm hμC.1).symm
      rw [← hmeanA, ← hmeanC] at hintegral
      rw [Matrix.le_iff]
      apply Matrix.nonneg_iff_posSemidef.mp
      apply (helperModulePrivate_realMatrixComplexification_nonneg_iff
        (binaryWeightedGeometricMean C D t -
          binaryWeightedGeometricMean A B t)).mp
      rw [map_sub]
      exact sub_nonneg.mpr hintegral
    · simpa [binaryWeightedGeometricMean_one A B hA hB,
        binaryWeightedGeometricMean_one C D hC hD] using hBD
  · simpa [binaryWeightedGeometricMean_zero A B hA hB,
      binaryWeightedGeometricMean_zero C D hC hD] using hAC
-/

end Shampoo
end

open scoped BigOperators ComplexOrder ContinuousFunctionalCalculus Kronecker MatrixOrder NNReal

namespace Shampoo

abbrev MultiIndex {k : Nat} (dims : Fin k → Nat) :=
  SOptLib.TensorIndex (fun i => Fin (dims i))
abbrev TensorSpace {k : Nat} (dims : Fin k → Nat) :=
  SOptLib.TensorSpace (fun i => Fin (dims i)) ℝ
abbrev FlatMatrixIndex (m n : Nat) := Fin m × Fin n
abbrev PosNat := {r : Nat // 0 < r}

noncomputable def finiteMax {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) : ℝ :=
  Finset.sup' (Finset.univ : Finset ι) Finset.univ_nonempty f

/- The paper's negative fractional powers are inverse powers along a
   positive-definite accumulator chain.  This wrapper keeps that domain in the
   update semantics instead of silently evaluating singular PSD powers. -/
noncomputable def pdMatrixPower {n : Nat} (A : SquareMatrix n) (α : ℝ)
    (hA : A.PosDef) : SquareMatrix n :=
  matrixPower A α hA.posSemidef

theorem matrixPower_spectral_formula {n : Nat} (A : SquareMatrix n) (α : ℝ)
    (hA : A.PosSemidef) :
    matrixPower A α hA =
      (hA.1.eigenvectorUnitary : SquareMatrix n) *
        Matrix.diagonal (fun i : Fin n => (hA.1.eigenvalues i) ^ α) *
        star (hA.1.eigenvectorUnitary : SquareMatrix n) := by
  rfl

def matrixTrace {n : Nat} (A : SquareMatrix n) : ℝ :=
  Matrix.trace A

def genericTrace {ι : Type*} [Fintype ι] [DecidableEq ι] (A : GenericSquare ι) : ℝ :=
  Matrix.trace A

def matrixGramLeft {m n : Nat} (G : MatrixSpace m n) : SquareMatrix m :=
  Matrix.leftGram G

def matrixGramRight {m n : Nat} (G : MatrixSpace m n) : SquareMatrix n :=
  Matrix.rightGram G

def matrixInner {m n : Nat} (G V : MatrixSpace m n) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, G i j * V i j

def tensorInner {k : Nat} {dims : Fin k → Nat} (G V : TensorSpace dims) : ℝ :=
  ∑ idx : MultiIndex dims, G idx * V idx

def diagonalPart {n : Nat} (A : SquareMatrix n) : SquareMatrix n :=
  Matrix.diagonalPart A

def zeroTensor {k : Nat} {dims : Fin k → Nat} : TensorSpace dims :=
  fun _ => 0

def replaceIndex {k : Nat} {dims : Fin k → Nat}
    (idx : MultiIndex dims) (i : Fin k) (s : Fin (dims i)) : MultiIndex dims :=
  fun j =>
    if h : j = i then
      Fin.cast (by rw [h]) s
    else
      idx j

abbrev ModeColumn {k : Nat} (dims : Fin k → Nat) (i : Fin k) :=
  SOptLib.TensorModeColumn (fun j => Fin (dims j)) i


/- Book JSON definitions.Matricization:
   "mat_i(A) = (vec(A_i1) ... vec(A_ini))^T". -/
def matricization {k : Nat} {dims : Fin k → Nat}
    (A : TensorSpace dims) (i : Fin k) :
    Matrix (Fin (dims i)) (ModeColumn dims i) ℝ :=
  SOptLib.tensorMatricization A i

/- Book JSON definitions.Tensor_contraction:
   "A^(i) = mat_i(A) mat_i(A)^T". -/
def tensorContraction {k : Nat} {dims : Fin k → Nat}
    (A : TensorSpace dims) (i : Fin k) : SquareMatrix (dims i) :=
  SOptLib.tensorContraction A i

/- Book JSON definitions.Tensor_matrix_product:
   "(A x_i M)_{j_1,...,j_k} = sum_s M_{j_i s} A_{...,s,...}". -/
def tensorModeProduct {k : Nat} {dims : Fin k → Nat}
    (A : TensorSpace dims) (i : Fin k) (M : SquareMatrix (dims i)) :
    TensorSpace dims :=
  SOptLib.tensorModeProduct A i M

noncomputable def frobeniusNorm {m n : Nat} (A : MatrixSpace m n) : ℝ :=
  Real.sqrt (∑ i : Fin m, ∑ j : Fin n, A i j * A i j)

noncomputable def tensorFrobeniusNorm {k : Nat} {dims : Fin k → Nat}
    (A : TensorSpace dims) : ℝ :=
  Real.sqrt (∑ idx : MultiIndex dims, A idx * A idx)

noncomputable def matrixEntrywiseSupNorm {m n : Nat} [Nonempty (FlatMatrixIndex m n)]
    (A : MatrixSpace m n) : ℝ :=
  finiteMax fun ij : FlatMatrixIndex m n => |A ij.1 ij.2|

/- Book JSON assumptions.Learning_rate_Theorem7 / Learning_rate_Theorem10:
   "eta = D/sqrt(2r)". -/
noncomputable def learningRate (D r : ℝ) : ℝ :=
  SOptLib.sqrtTwoScaleStepSize D r

noncomputable def positiveRankReal (r : PosNat) : ℝ :=
  (r.1 : ℝ)

theorem positiveRankReal_pos (r : PosNat) : 0 < positiveRankReal r := by
  dsimp [positiveRankReal]
  exact_mod_cast r.2

theorem learningRate_pos_of_pos {D r : ℝ} (hD : 0 < D) (hr : 0 < r) :
    0 < learningRate D r := by
  exact SOptLib.sqrtTwoScaleStepSize_pos D r hD hr

def matrixBasis {m n : Nat} (i : Fin m) (j : Fin n) : MatrixSpace m n :=
  fun i' j' => if i' = i then if j' = j then 1 else 0 else 0

noncomputable def tensorBasis {k : Nat} {dims : Fin k → Nat}
    (idx : MultiIndex dims) : TensorSpace dims :=
  fun idx' => if idx' = idx then 1 else 0

/- Book JSON additional_algorithm_specs.Algorithm 1 step "G_t = nabla f_t(W_t)".
   The source writes an ordinary mathematical gradient.  We model that as a
   Frechet derivative represented by the Frobenius inner product with `G`,
   not as coordinate partial derivatives and not as a totalized `fderiv`. -/
def IsMatrixGradientAt {T m n : Nat}
    (loss : Fin T → MatrixSpace m n → ℝ) (t : Fin T)
    (W G : MatrixSpace m n) : Prop :=
  ∃ D : MatrixSpace m n →L[ℝ] ℝ,
    HasFDerivAt (loss t) D W ∧ ∀ V : MatrixSpace m n, D V = matrixInner G V

noncomputable def matrixLossGradient {T m n : Nat}
    (loss : Fin T → MatrixSpace m n → ℝ) (t : Fin T)
    (W : MatrixSpace m n)
    (hgrad : ∃ G : MatrixSpace m n, IsMatrixGradientAt loss t W G) :
    MatrixSpace m n :=
  Classical.choose hgrad

theorem matrixLossGradient_spec {T m n : Nat}
    (loss : Fin T → MatrixSpace m n → ℝ) (t : Fin T)
    (W : MatrixSpace m n)
    (hgrad : ∃ G : MatrixSpace m n, IsMatrixGradientAt loss t W G) :
    IsMatrixGradientAt loss t W (matrixLossGradient loss t W hgrad) := by
  exact Classical.choose_spec hgrad

private theorem sum_Icc_one_matrix_fin_reindex {T : Nat} [Nonempty (Fin T)]
    {α : Type*} [AddCommMonoid α] (F : Fin T → α) :
    (Finset.Icc 1 T).sum
        (fun s => F (if h : s - 1 < T then ⟨s - 1, h⟩
          else Classical.choice (inferInstance : Nonempty (Fin T)))) =
      ∑ t : Fin T, F t := by
  exact sum_Icc_one_pred_fin_eq_sum F

/- Book JSON algorithm_spec.steps.gradient:
   "G_t = nabla f_t(W_t)" for order-k tensors. -/
def IsTensorGradientAt {k T : Nat} {dims : Fin k → Nat}
    (loss : Fin T → TensorSpace dims → ℝ) (t : Fin T)
    (W G : TensorSpace dims) : Prop :=
  ∃ D : TensorSpace dims →L[ℝ] ℝ,
    HasFDerivAt (loss t) D W ∧ ∀ V : TensorSpace dims, D V = tensorInner G V

noncomputable def tensorLossGradient {k T : Nat} {dims : Fin k → Nat}
    (loss : Fin T → TensorSpace dims → ℝ) (t : Fin T)
    (W : TensorSpace dims)
    (hgrad : ∃ G : TensorSpace dims, IsTensorGradientAt loss t W G) :
    TensorSpace dims :=
  Classical.choose hgrad

theorem tensorLossGradient_spec {k T : Nat} {dims : Fin k → Nat}
    (loss : Fin T → TensorSpace dims → ℝ) (t : Fin T)
    (W : TensorSpace dims)
    (hgrad : ∃ G : TensorSpace dims, IsTensorGradientAt loss t W G) :
    IsTensorGradientAt loss t W (tensorLossGradient loss t W hgrad) := by
  exact Classical.choose_spec hgrad

def vectorOuter {ι : Type*} (g : ι → ℝ) : GenericSquare ι :=
  fun i j => g i * g j


def matrixOuter {m n : Nat} (u : Fin m → ℝ) (v : Fin n → ℝ) : MatrixSpace m n :=
  fun i j => u i * v j

def vectorDot {ι : Type*} [Fintype ι] (x y : ι → ℝ) : ℝ :=
  ∑ i, x i * y i

def quadraticForm {ι : Type*} [Fintype ι] (x : ι → ℝ) (H : GenericSquare ι) : ℝ :=
  ∑ i, ∑ j, x i * H i j * x j

noncomputable def dualQuadraticForm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℝ) (H : GenericSquare ι) : ℝ :=
  SOptLib.finiteMatrixDualQuadraticForm H (WithLp.toLp 2 g)

noncomputable def omdUpdate {d : Nat} (eta : ℝ) (H : SquareMatrix d)
    (g w : Fin d → ℝ) : Fin d → ℝ :=
  SOptLib.preconditionedGradientStep eta H g w

def matrixVec {m n : Nat} (G : MatrixSpace m n) : FlatMatrixIndex m n → ℝ :=
  fun ij => G ij.1 ij.2


def genericMatrixVec {ι κ : Type*} (M : Matrix ι κ ℝ) : ι × κ → ℝ :=
  fun rc => M rc.1 rc.2

def tensorVecReindexedByMode {k : Nat} {dims : Fin k → Nat}
    (A : TensorSpace dims) (i : Fin k) : Fin (dims i) × ModeColumn dims i → ℝ :=
  fun rc =>  A ((fun row col => (Equiv.piSplitAt i (fun j => Fin (dims j))).symm (row, col)) rc.1 rc.2)

def tensorVecReindexedByTransposedMode {k : Nat} {dims : Fin k → Nat}
    (A : TensorSpace dims) (i : Fin k) : ModeColumn dims i × Fin (dims i) → ℝ :=
  fun cr =>  A ((fun row col => (Equiv.piSplitAt i (fun j => Fin (dims j))).symm (row, col)) cr.2 cr.1)

def firstMode (k : Nat) : Fin (k + 1) :=
  ⟨0, Nat.succ_pos k⟩

def lastMode (k : Nat) : Fin (k + 1) :=
  ⟨k, Nat.lt_succ_self k⟩

def tensorKronecker {k : Nat} {dims : Fin k → Nat}
    (M : (i : Fin k) → SquareMatrix (dims i)) :
    GenericSquare (MultiIndex dims) :=
  SOptLib.tensorKronecker M

def modeEmbeddedMatrix {k : Nat} {dims : Fin k → Nat} (i : Fin k)
    (B : SquareMatrix (dims i)) : GenericSquare (MultiIndex dims) :=
  SOptLib.tensorModeEmbedding i B

noncomputable def tensorModeProductsNat {k : Nat} {dims : Fin k → Nat}
    (A : TensorSpace dims) (M : (i : Fin k) → SquareMatrix (dims i)) :
    Nat → TensorSpace dims :=
  SOptLib.tensorModeProductsPrefix A M

noncomputable def tensorModeProducts {k : Nat} {dims : Fin k → Nat}
    (A : TensorSpace dims) (M : (i : Fin k) → SquareMatrix (dims i)) :
    TensorSpace dims :=
  SOptLib.tensorModeProducts A M

def currentIndex {T : Nat} (t : Fin T) : Fin (T + 1) :=
  ⟨t.1, Nat.lt_trans t.2 (Nat.lt_succ_self T)⟩

def nextIndex {T : Nat} (t : Fin T) : Fin (T + 1) :=
  ⟨t.1 + 1, Nat.succ_lt_succ t.2⟩

def IsOMDTrajectory {T d : Nat} (eta : ℝ)
    (w : Fin (T + 1) → Fin d → ℝ) (g : Fin T → Fin d → ℝ)
    (H : Fin T → SquareMatrix d) : Prop :=
  SOptLib.IsPreconditionedGradientTrajectory eta w g H

/- Book JSON additional_algorithm_specs.Algorithm 1: matrix Shampoo. -/
structure MatrixAlgorithm1 (T m n : Nat) where
  epsilon : ℝ
  epsilon_nonneg : 0 ≤ epsilon
  eta : ℝ
  loss : Fin T → MatrixSpace m n → ℝ
  loss_convex : ∀ t : Fin T, ConvexOn ℝ Set.univ (loss t)

abbrev MatrixState (m n : Nat) :=
  SOptLib.TwoSidedMatrixPreconditionerState (Fin m) (Fin n) ℝ

namespace MatrixAlgorithm1

noncomputable def gradient (S : MatrixAlgorithm1 T m n) (t : Fin T)
    (W : MatrixSpace m n)
    (hgrad : ∃ G : MatrixSpace m n, IsMatrixGradientAt S.loss t W G) :
    MatrixSpace m n :=
  matrixLossGradient S.loss t W hgrad

theorem gradient_def (S : MatrixAlgorithm1 T m n) (t : Fin T)
    (W : MatrixSpace m n)
    (hgrad : ∃ G : MatrixSpace m n, IsMatrixGradientAt S.loss t W G) :
    S.gradient t W hgrad = matrixLossGradient S.loss t W hgrad := by
  rfl

theorem gradient_spec_of_exists (S : MatrixAlgorithm1 T m n) (t : Fin T)
    (W : MatrixSpace m n)
    (hgrad : ∃ G : MatrixSpace m n, IsMatrixGradientAt S.loss t W G) :
    IsMatrixGradientAt S.loss t W (S.gradient t W hgrad) := by
  simpa [gradient] using matrixLossGradient_spec S.loss t W hgrad

def initialState (S : MatrixAlgorithm1 T m n) : MatrixState m n :=
  SOptLib.twoSidedMatrixPreconditionerInitialState S.epsilon

theorem initial_leftAccumulator_psd (S : MatrixAlgorithm1 T m n) :
    (S.initialState).L.PosSemidef := by
  simpa [initialState] using
    (Matrix.PosSemidef.one.smul S.epsilon_nonneg :
      Matrix.PosSemidef (S.epsilon • (1 : SquareMatrix m)))

theorem initial_rightAccumulator_psd (S : MatrixAlgorithm1 T m n) :
    (S.initialState).R.PosSemidef := by
  simpa [initialState] using
    (Matrix.PosSemidef.one.smul S.epsilon_nonneg :
      Matrix.PosSemidef (S.epsilon • (1 : SquareMatrix n)))

theorem step_leftAccumulator_psd (S : MatrixAlgorithm1 T m n) (t : Fin T)
    (st : MatrixState m n) (G : MatrixSpace m n) (hL : st.L.PosSemidef) :
    (st.L + matrixGramLeft G).PosSemidef := by
  exact hL.add (by
    simpa [matrixGramLeft] using
      (Matrix.PosSemidef.one.mul_mul_conjTranspose_same (B := G)))

theorem step_rightAccumulator_psd (S : MatrixAlgorithm1 T m n) (t : Fin T)
    (st : MatrixState m n) (G : MatrixSpace m n) (hR : st.R.PosSemidef) :
    (st.R + matrixGramRight G).PosSemidef := by
  exact hR.add (by
    simpa [matrixGramRight] using
      (Matrix.PosSemidef.one.conjTranspose_mul_mul_same (B := G)))

noncomputable def stepState (S : MatrixAlgorithm1 T m n) (t : Fin T)
    (st : MatrixState m n) (G : MatrixSpace m n)
    (_hG : IsMatrixGradientAt S.loss t st.W G)
    (hLpd : (st.L + matrixGramLeft G).PosDef)
    (hRpd : (st.R + matrixGramRight G).PosDef) :
    MatrixState m n :=
  SOptLib.twoSidedMatrixPreconditionedStep S.eta st G hLpd hRpd

/- Book JSON source_discrepancies.Epsilon_PD_condition_not_explicit_in_theorem_heads:
   strict positive-definite inverse-power domains are not consequences of the
   stated `epsilon >= 0` setup.  The corrected run boundary carries exactly the
   per-step evidence needed to interpret Algorithm 1's negative powers. -/
structure CorrectedRun (S : MatrixAlgorithm1 T m n) where
  state : Fin (T + 1) → MatrixState m n
  gradientAt : Fin T → MatrixSpace m n
  initial :
    state ⟨0, Nat.succ_pos T⟩ = S.initialState
  gradient_spec :
    ∀ t : Fin T, IsMatrixGradientAt S.loss t (state (currentIndex t)).W (gradientAt t)
  left_step_posDef :
    ∀ t : Fin T, ((state (currentIndex t)).L + matrixGramLeft (gradientAt t)).PosDef
  right_step_posDef :
    ∀ t : Fin T, ((state (currentIndex t)).R + matrixGramRight (gradientAt t)).PosDef
  step :
    ∀ t : Fin T,
      state (nextIndex t) =
        S.stepState t (state (currentIndex t)) (gradientAt t) (gradient_spec t)
          (left_step_posDef t) (right_step_posDef t)

noncomputable def CorrectedRun.iterate {S : MatrixAlgorithm1 T m n}
    (run : S.CorrectedRun) (t : Fin (T + 1)) : MatrixSpace m n :=
  (run.state t).W

noncomputable def CorrectedRun.leftAccumulator {S : MatrixAlgorithm1 T m n}
    (run : S.CorrectedRun) (t : Fin (T + 1)) : SquareMatrix m :=
  (run.state t).L

theorem CorrectedRun.leftAccumulator_psd {S : MatrixAlgorithm1 T m n}
    (run : S.CorrectedRun) (t : Fin (T + 1)) :
    (run.leftAccumulator t).PosSemidef := by
  induction t using Fin.induction with
  | zero =>
      change Matrix.PosSemidef ((run.state ⟨0, Nat.succ_pos T⟩).L)
      rw [run.initial]
      exact S.initial_leftAccumulator_psd
  | succ t ih =>
      change Matrix.PosSemidef ((run.state (nextIndex t)).L)
      rw [run.step t]
      simpa [MatrixAlgorithm1.stepState] using (run.left_step_posDef t).posSemidef

noncomputable def CorrectedRun.rightAccumulator {S : MatrixAlgorithm1 T m n}
    (run : S.CorrectedRun) (t : Fin (T + 1)) : SquareMatrix n :=
  (run.state t).R

theorem CorrectedRun.rightAccumulator_psd {S : MatrixAlgorithm1 T m n}
    (run : S.CorrectedRun) (t : Fin (T + 1)) :
    (run.rightAccumulator t).PosSemidef := by
  induction t using Fin.induction with
  | zero =>
      change Matrix.PosSemidef ((run.state ⟨0, Nat.succ_pos T⟩).R)
      rw [run.initial]
      exact S.initial_rightAccumulator_psd
  | succ t ih =>
      change Matrix.PosSemidef ((run.state (nextIndex t)).R)
      rw [run.step t]
      simpa [MatrixAlgorithm1.stepState] using (run.right_step_posDef t).posSemidef

noncomputable def CorrectedRun.finalState {S : MatrixAlgorithm1 T m n}
    (run : S.CorrectedRun) : MatrixState m n :=
  run.state ⟨T, Nat.lt_succ_self T⟩

noncomputable def CorrectedRun.regret {S : MatrixAlgorithm1 T m n}
    (run : S.CorrectedRun) (Wstar : MatrixSpace m n) : ℝ :=
  ∑ t : Fin T, (S.loss t (run.iterate (currentIndex t)) - S.loss t Wstar)

noncomputable def CorrectedRun.comparatorRadius {S : MatrixAlgorithm1 T m n}
    (run : S.CorrectedRun) [Nonempty (Fin T)]
    (Wstar : MatrixSpace m n) : ℝ :=
  finiteMax fun t : Fin T => frobeniusNorm (run.iterate (currentIndex t) - Wstar)

theorem initialState_spec (S : MatrixAlgorithm1 T m n) :
    (S.initialState).W = 0 ∧
      (S.initialState).L = S.epsilon • (1 : SquareMatrix m) ∧
      (S.initialState).R = S.epsilon • (1 : SquareMatrix n) := by
  simp [initialState]

theorem stepState_spec (S : MatrixAlgorithm1 T m n) (t : Fin T) (st : MatrixState m n) :
    ∀ (G : MatrixSpace m n) (hG : IsMatrixGradientAt S.loss t st.W G)
      (hLpd : (st.L + matrixGramLeft G).PosDef)
      (hRpd : (st.R + matrixGramRight G).PosDef),
    let st' := S.stepState t st G hG hLpd hRpd
    st'.L = st.L + G * G.transpose ∧
      st'.R = st.R + G.transpose * G ∧
      st'.W = st.W - S.eta •
        (pdMatrixPower st'.L (-(1 / 4 : ℝ)) hLpd * G *
          pdMatrixPower st'.R (-(1 / 4 : ℝ)) hRpd) := by
  intro G hG hLpd hRpd
  simp [stepState, SOptLib.twoSidedMatrixPreconditionedStep, matrixGramLeft,
    matrixGramRight, pdMatrixPower, matrixPower, psdMatrixPower]

end MatrixAlgorithm1

private theorem euclidean_inner_eq_vectorDot {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) :
    inner ℝ ((EuclideanSpace.equiv ι ℝ).symm x)
      ((EuclideanSpace.equiv ι ℝ).symm y) = vectorDot x y := by
  have hreal : ∀ a b : ℝ, inner ℝ a b = a * b := by
    intro a b
    norm_num [inner]
    ring
  rw [PiLp.inner_apply]
  simp [EuclideanSpace.equiv, vectorDot, PiLp.toLp_apply, hreal]

private theorem euclidean_inner_sub_eq_vectorDot {ι : Type*} [Fintype ι]
    (x y z : ι → ℝ) :
    inner ℝ ((EuclideanSpace.equiv ι ℝ).symm x)
      (((EuclideanSpace.equiv ι ℝ).symm y) -
        ((EuclideanSpace.equiv ι ℝ).symm z)) =
      vectorDot x (y - z) := by
  have hsub :
      ((EuclideanSpace.equiv ι ℝ).symm y) -
          ((EuclideanSpace.equiv ι ℝ).symm z) =
        (EuclideanSpace.equiv ι ℝ).symm (y - z) := by
    ext i
    simp [EuclideanSpace.equiv]
  rw [hsub]
  exact euclidean_inner_eq_vectorDot x (y - z)

private theorem theorem7_flattened_loss_gradient_bridge {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun) (t : Fin T) :
    HasGradientWithinAt
      (fun v : EuclideanSpace ℝ (FlatMatrixIndex m n) =>
        S.loss t (fun i j => (EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ v) (i, j)))
      ((EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ).symm (matrixVec (run.gradientAt t)))
      Set.univ
      ((EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ).symm
        (matrixVec (run.iterate (currentIndex t)))) := by
  classical
  letI : NormedAddCommGroup (MatrixSpace m n) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (MatrixSpace m n) := Matrix.normedSpace
  have hMatrixInner : ∀ (G : MatrixSpace m n)
      (v : EuclideanSpace ℝ (FlatMatrixIndex m n)),
      matrixInner G
          (fun i j => (EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ v) (i, j)) =
        inner ℝ ((EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ).symm
          (matrixVec G)) v := by
    intro G v
    have hinner := euclidean_inner_eq_vectorDot (matrixVec G)
      ((EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ) v)
    calc
      matrixInner G
          (fun i j => (EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ v) (i, j)) =
          vectorDot (matrixVec G) ((EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ) v) := by
            rw [matrixInner, vectorDot]
            rw [← Finset.sum_product']
            simp [matrixVec, Finset.univ_product_univ]
      _ = inner ℝ ((EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ).symm
            (matrixVec G))
          ((EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ).symm
            ((EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ) v)) := hinner.symm
      _ = inner ℝ ((EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ).symm
            (matrixVec G)) v := by
          simp
  obtain ⟨D, hD, hD_apply⟩ := run.gradient_spec t
  let unvecLin : EuclideanSpace ℝ (FlatMatrixIndex m n) →ₗ[ℝ] MatrixSpace m n :=
    { toFun := fun v i j => (EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ v) (i, j)
      map_add' := by
        intro x y
        ext i j
        simp
      map_smul' := by
        intro a x
        ext i j
        simp }
  let unvecCLM : EuclideanSpace ℝ (FlatMatrixIndex m n) →L[ℝ] MatrixSpace m n :=
    unvecLin.toContinuousLinearMap
  let x : EuclideanSpace ℝ (FlatMatrixIndex m n) :=
    (EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ).symm
      (matrixVec (run.iterate (currentIndex t)))
  have hx : unvecCLM x = run.iterate (currentIndex t) := by
    ext i j
    simp [unvecCLM, unvecLin, x, matrixVec]
  have hD_at : HasFDerivAt (S.loss t) D (unvecCLM x) := by
    simpa [hx, MatrixAlgorithm1.CorrectedRun.iterate] using hD
  have hdualEq :
      D.comp unvecCLM =
        InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (FlatMatrixIndex m n))
          ((EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ).symm
            (matrixVec (run.gradientAt t))) := by
    ext v
    calc
      (D.comp unvecCLM) v = D (unvecCLM v) := rfl
      _ = matrixInner (run.gradientAt t) (unvecCLM v) := hD_apply _
      _ = matrixInner (run.gradientAt t)
          (fun i j => (EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ v) (i, j)) := by
            simp [unvecCLM, unvecLin]
      _ = inner ℝ ((EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ).symm
          (matrixVec (run.gradientAt t))) v := hMatrixInner (run.gradientAt t) v
      _ = (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (FlatMatrixIndex m n))
          ((EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ).symm
            (matrixVec (run.gradientAt t)))) v := by
            simp [InnerProductSpace.toDual_apply_apply]
  have hgradAt : HasGradientAt
      (fun v : EuclideanSpace ℝ (FlatMatrixIndex m n) => S.loss t (unvecCLM v))
      ((EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ).symm
        (matrixVec (run.gradientAt t))) x := by
    apply gradient_comp_continuousLinearMap_of_fderiv_pairing
        unvecCLM (S.loss t) D x
    · exact hD_at
    · intro v
      change (D.comp unvecCLM) v = _
      rw [hdualEq]
      simp [InnerProductSpace.toDual_apply_apply]
  rw [hasGradientWithinAt_univ]
  simpa [x, unvecCLM, unvecLin] using hgradAt

/- Book JSON algorithm_spec: Algorithm 2 tensor Shampoo. -/
structure TensorAlgorithm2 (k T : Nat) where
  dims : Fin k → Nat
  dims_pos : ∀ i : Fin k, 0 < dims i
  epsilon : ℝ
  epsilon_nonneg : 0 ≤ epsilon
  eta : ℝ
  loss : Fin T → TensorSpace dims → ℝ
  loss_convex : ∀ t : Fin T, ConvexOn ℝ Set.univ (loss t)

abbrev TensorState {k : Nat} (dims : Fin k → Nat) :=
  SOptLib.ModewiseTensorPreconditionerState (Fin k) (fun i => Fin (dims i)) ℝ

namespace TensorAlgorithm2

noncomputable def gradient (S : TensorAlgorithm2 k T) (t : Fin T)
    (W : TensorSpace S.dims)
    (hgrad : ∃ G : TensorSpace S.dims, IsTensorGradientAt S.loss t W G) :
    TensorSpace S.dims :=
  tensorLossGradient S.loss t W hgrad

theorem gradient_def (S : TensorAlgorithm2 k T) (t : Fin T)
    (W : TensorSpace S.dims)
    (hgrad : ∃ G : TensorSpace S.dims, IsTensorGradientAt S.loss t W G) :
    S.gradient t W hgrad = tensorLossGradient S.loss t W hgrad := by
  rfl

theorem gradient_spec_of_exists (S : TensorAlgorithm2 k T) (t : Fin T)
    (W : TensorSpace S.dims)
    (hgrad : ∃ G : TensorSpace S.dims, IsTensorGradientAt S.loss t W G) :
    IsTensorGradientAt S.loss t W (S.gradient t W hgrad) := by
  simpa [gradient] using tensorLossGradient_spec S.loss t W hgrad

def initialState (S : TensorAlgorithm2 k T) : TensorState S.dims where
  W := zeroTensor
  H := fun i => S.epsilon • (1 : SquareMatrix (S.dims i))

theorem initial_accumulator_psd (S : TensorAlgorithm2 k T) (i : Fin k) :
    ((S.initialState).H i).PosSemidef := by
  simpa [initialState] using
    (Matrix.PosSemidef.one.smul S.epsilon_nonneg :
      Matrix.PosSemidef (S.epsilon • (1 : SquareMatrix (S.dims i))))

noncomputable def preconditionModesNat (S : TensorAlgorithm2 k T)
    (H : (i : Fin k) → SquareMatrix (S.dims i))
    (hH : ∀ i : Fin k, (H i).PosDef)
    (G : TensorSpace S.dims) : Nat → TensorSpace S.dims
  | 0 => G
  | q + 1 =>
      if hq : q < k then
        tensorModeProduct (S.preconditionModesNat H hH G q) ⟨q, hq⟩
          (pdMatrixPower (H ⟨q, hq⟩) (-(1 / ((2 : ℝ) * (k : ℝ)))) (hH ⟨q, hq⟩))
      else
        S.preconditionModesNat H hH G q

noncomputable def preconditionedGradient (S : TensorAlgorithm2 k T)
    (H : (i : Fin k) → SquareMatrix (S.dims i))
    (hH : ∀ i : Fin k, (H i).PosDef)
    (G : TensorSpace S.dims) : TensorSpace S.dims :=
  S.preconditionModesNat H hH G k

theorem step_accumulator_psd (S : TensorAlgorithm2 k T) (t : Fin T)
    (st : TensorState S.dims) (G : TensorSpace S.dims)
    (hH : ∀ i : Fin k, (st.H i).PosSemidef) (i : Fin k) :
    (st.H i + tensorContraction G i).PosSemidef := by
  exact (hH i).add (by
    simpa [tensorContraction] using
      (Matrix.PosSemidef.one.mul_mul_conjTranspose_same (B := matricization G i)))

noncomputable def stepState (S : TensorAlgorithm2 k T) (t : Fin T)
    (st : TensorState S.dims) (G : TensorSpace S.dims)
    (_hG : IsTensorGradientAt S.loss t st.W G)
    (hHpd : ∀ i : Fin k, (st.H i + tensorContraction G i).PosDef) :
    TensorState S.dims :=
  let Hnew : (i : Fin k) → SquareMatrix (S.dims i) :=
    fun i => st.H i + tensorContraction G i
  { W := st.W - S.eta • S.preconditionedGradient Hnew hHpd G
    H := Hnew }

/- Corrected-domain trajectory for Algorithm 2: each tensor gradient is
   explicitly certified, and each updated mode accumulator is strictly
   positive definite before its negative fractional power is formed. -/
structure CorrectedRun (S : TensorAlgorithm2 k T) where
  state : Fin (T + 1) → TensorState S.dims
  gradientAt : Fin T → TensorSpace S.dims
  initial :
    state ⟨0, Nat.succ_pos T⟩ = S.initialState
  gradient_spec :
    ∀ t : Fin T, IsTensorGradientAt S.loss t (state (currentIndex t)).W (gradientAt t)
  step_posDef :
    ∀ t : Fin T, ∀ i : Fin k,
      ((state (currentIndex t)).H i + tensorContraction (gradientAt t) i).PosDef
  step :
    ∀ t : Fin T,
      state (nextIndex t) =
        S.stepState t (state (currentIndex t)) (gradientAt t) (gradient_spec t)
          (step_posDef t)

noncomputable def CorrectedRun.iterate {S : TensorAlgorithm2 k T}
    (run : S.CorrectedRun) (t : Fin (T + 1)) : TensorSpace S.dims :=
  (run.state t).W

noncomputable def CorrectedRun.accumulator {S : TensorAlgorithm2 k T}
    (run : S.CorrectedRun) (i : Fin k) (t : Fin (T + 1)) :
    SquareMatrix (S.dims i) :=
  (run.state t).H i

theorem CorrectedRun.accumulator_psd {S : TensorAlgorithm2 k T}
    (run : S.CorrectedRun) (i : Fin k) (t : Fin (T + 1)) :
    (run.accumulator i t).PosSemidef := by
  induction t using Fin.induction with
  | zero =>
      change Matrix.PosSemidef ((run.state ⟨0, Nat.succ_pos T⟩).H i)
      rw [run.initial]
      exact S.initial_accumulator_psd i
  | succ t ih =>
      change Matrix.PosSemidef ((run.state (nextIndex t)).H i)
      rw [run.step t]
      simpa [TensorAlgorithm2.stepState] using (run.step_posDef t i).posSemidef

noncomputable def CorrectedRun.finalState {S : TensorAlgorithm2 k T}
    (run : S.CorrectedRun) : TensorState S.dims :=
  run.state ⟨T, Nat.lt_succ_self T⟩

noncomputable def CorrectedRun.regret {S : TensorAlgorithm2 k T}
    (run : S.CorrectedRun) (Wstar : TensorSpace S.dims) : ℝ :=
  ∑ t : Fin T, (S.loss t (run.iterate (currentIndex t)) - S.loss t Wstar)

noncomputable def CorrectedRun.comparatorRadius {S : TensorAlgorithm2 k T}
    (run : S.CorrectedRun) [Nonempty (Fin T)]
    (Wstar : TensorSpace S.dims) : ℝ :=
  finiteMax fun t : Fin T => tensorFrobeniusNorm (run.iterate (currentIndex t) - Wstar)

noncomputable def rankGeometricMean [Nonempty (Fin k)] (rankBound : Fin k → PosNat) : ℝ :=
  SOptLib.positiveNatGeometricMean rankBound

theorem initialState_spec (S : TensorAlgorithm2 k T) :
    (S.initialState).W = zeroTensor ∧
      (∀ i : Fin k, (S.initialState).H i = S.epsilon • (1 : SquareMatrix (S.dims i))) := by
  simp [initialState]

theorem stepState_spec (S : TensorAlgorithm2 k T) (t : Fin T) (st : TensorState S.dims) :
    ∀ (G : TensorSpace S.dims) (hG : IsTensorGradientAt S.loss t st.W G)
      (hHpd : ∀ i : Fin k, (st.H i + tensorContraction G i).PosDef),
    let st' := S.stepState t st G hG hHpd
    (∀ i : Fin k, st'.H i = st.H i + tensorContraction G i) ∧
      st'.W = st.W - S.eta • S.preconditionedGradient st'.H hHpd G := by
  intro G hG hHpd
  simp [stepState]

end TensorAlgorithm2

private theorem theorem10_flattened_loss_gradient_bridge {k T : Nat}
    (S : TensorAlgorithm2 k T) (run : S.CorrectedRun) (t : Fin T) :
    HasGradientWithinAt
      (fun v : EuclideanSpace ℝ (MultiIndex S.dims) =>
        S.loss t (fun idx => (EuclideanSpace.equiv (MultiIndex S.dims) ℝ v) idx))
      ((EuclideanSpace.equiv (MultiIndex S.dims) ℝ).symm ( (run.gradientAt t)))
      Set.univ
      ((EuclideanSpace.equiv (MultiIndex S.dims) ℝ).symm
        ( (run.iterate (currentIndex t)))) := by
  classical
  have hTensorInner : ∀ (G : TensorSpace S.dims)
      (v : EuclideanSpace ℝ (MultiIndex S.dims)),
      tensorInner G
          (fun idx => (EuclideanSpace.equiv (MultiIndex S.dims) ℝ v) idx) =
        inner ℝ ((EuclideanSpace.equiv (MultiIndex S.dims) ℝ).symm
          ( G)) v := by
    intro G v
    have hinner := euclidean_inner_eq_vectorDot ( G)
      ((EuclideanSpace.equiv (MultiIndex S.dims) ℝ) v)
    calc
      tensorInner G
          (fun idx => (EuclideanSpace.equiv (MultiIndex S.dims) ℝ v) idx) =
          vectorDot ( G) ((EuclideanSpace.equiv (MultiIndex S.dims) ℝ) v) := by
            simp [tensorInner, vectorDot]
      _ = inner ℝ ((EuclideanSpace.equiv (MultiIndex S.dims) ℝ).symm
            ( G))
          ((EuclideanSpace.equiv (MultiIndex S.dims) ℝ).symm
            ((EuclideanSpace.equiv (MultiIndex S.dims) ℝ) v)) := hinner.symm
      _ = inner ℝ ((EuclideanSpace.equiv (MultiIndex S.dims) ℝ).symm
            ( G)) v := by
          simp
  obtain ⟨D, hD, hD_apply⟩ := run.gradient_spec t
  let unvecLin : EuclideanSpace ℝ (MultiIndex S.dims) →ₗ[ℝ] TensorSpace S.dims :=
    { toFun := fun v idx => (EuclideanSpace.equiv (MultiIndex S.dims) ℝ v) idx
      map_add' := by
        intro x y
        ext idx
        simp
      map_smul' := by
        intro a x
        ext idx
        simp }
  let unvecCLM : EuclideanSpace ℝ (MultiIndex S.dims) →L[ℝ] TensorSpace S.dims :=
    unvecLin.toContinuousLinearMap
  let x : EuclideanSpace ℝ (MultiIndex S.dims) :=
    (EuclideanSpace.equiv (MultiIndex S.dims) ℝ).symm
      ( (run.iterate (currentIndex t)))
  have hx : unvecCLM x = run.iterate (currentIndex t) := by
    ext idx
    simp [unvecCLM, unvecLin, x]
  have hD_at : HasFDerivAt (S.loss t) D (unvecCLM x) := by
    simpa [hx, TensorAlgorithm2.CorrectedRun.iterate] using hD
  have hlin_deriv : HasFDerivAt
      (fun v : EuclideanSpace ℝ (MultiIndex S.dims) => unvecCLM v)
      unvecCLM x := by
    simpa using (unvecCLM.hasFDerivAt (x := x))
  have hcomp_raw : HasFDerivAt
      ((S.loss t) ∘ (fun v : EuclideanSpace ℝ (MultiIndex S.dims) => unvecCLM v))
      (D.comp unvecCLM) x := by
    exact hD_at.comp (x := x)
      (f := fun v : EuclideanSpace ℝ (MultiIndex S.dims) => unvecCLM v)
      hlin_deriv
  have hcomp : HasFDerivAt
      (fun v : EuclideanSpace ℝ (MultiIndex S.dims) => S.loss t (unvecCLM v))
      (D.comp unvecCLM) x := by
    simpa [Function.comp_def] using hcomp_raw
  have hdualEq :
      D.comp unvecCLM =
        InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (MultiIndex S.dims))
          ((EuclideanSpace.equiv (MultiIndex S.dims) ℝ).symm
            ( (run.gradientAt t))) := by
    ext v
    calc
      (D.comp unvecCLM) v = D (unvecCLM v) := rfl
      _ = tensorInner (run.gradientAt t) (unvecCLM v) := hD_apply _
      _ = tensorInner (run.gradientAt t)
          (fun idx => (EuclideanSpace.equiv (MultiIndex S.dims) ℝ v) idx) := by
            simp [unvecCLM, unvecLin]
      _ = inner ℝ ((EuclideanSpace.equiv (MultiIndex S.dims) ℝ).symm
          ( (run.gradientAt t))) v := hTensorInner (run.gradientAt t) v
      _ = (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (MultiIndex S.dims))
          ((EuclideanSpace.equiv (MultiIndex S.dims) ℝ).symm
            ( (run.gradientAt t)))) v := by
            simp [InnerProductSpace.toDual_apply_apply]
  have hgradAt : HasGradientAt
      (fun v : EuclideanSpace ℝ (MultiIndex S.dims) => S.loss t (unvecCLM v))
      ((EuclideanSpace.equiv (MultiIndex S.dims) ℝ).symm
        ( (run.gradientAt t))) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    simpa [hdualEq] using hcomp
  rw [hasGradientWithinAt_univ]
  simpa [x, unvecCLM, unvecLin] using hgradAt

private theorem theorem10_next_accumulator_posDef {k T : Nat}
    (S : TensorAlgorithm2 k T) (run : S.CorrectedRun) (t : Fin T) (i : Fin k) :
    (run.accumulator i (nextIndex t)).PosDef := by
  change ((run.state (nextIndex t)).H i).PosDef
  rw [run.step t]
  simpa [TensorAlgorithm2.stepState, TensorAlgorithm2.CorrectedRun.accumulator] using
    run.step_posDef t i

private theorem theorem10_preconditionedGradient_eq_tensorModeProducts {k T : Nat}
    (S : TensorAlgorithm2 k T) (H : (i : Fin k) → SquareMatrix (S.dims i))
    (hH : ∀ i : Fin k, (H i).PosDef) (G : TensorSpace S.dims) :
    S.preconditionedGradient H hH G =
      tensorModeProducts G
        (fun i : Fin k =>
          pdMatrixPower (H i) (-(1 / ((2 : ℝ) * (k : ℝ)))) (hH i)) := by
  classical
  let M : (i : Fin k) → SquareMatrix (S.dims i) :=
    fun i => pdMatrixPower (H i) (-(1 / ((2 : ℝ) * (k : ℝ)))) (hH i)
  have hrec : ∀ q : Nat, S.preconditionModesNat H hH G q =
      tensorModeProductsNat G M q := by
    intro q
    induction q with
    | zero =>
        simp [TensorAlgorithm2.preconditionModesNat, tensorModeProductsNat]
    | succ q ih =>
        by_cases hq : q < k
        · simp [TensorAlgorithm2.preconditionModesNat, tensorModeProductsNat,
            tensorModeProduct, hq, ih, M]
        · simp [TensorAlgorithm2.preconditionModesNat, tensorModeProductsNat, hq, ih, M]
  simpa [TensorAlgorithm2.preconditionedGradient, tensorModeProducts, M] using hrec k

private theorem theorem10_algorithm2_tensor_update_modeProducts {k T : Nat}
    (S : TensorAlgorithm2 k T) (run : S.CorrectedRun) :
    ∀ t : Fin T,
      run.iterate (nextIndex t) =
        run.iterate (currentIndex t) -
          S.eta • tensorModeProducts (run.gradientAt t)
            (fun i : Fin k =>
              pdMatrixPower (run.accumulator i (nextIndex t))
                (-(1 / ((2 : ℝ) * (k : ℝ))))
                (theorem10_next_accumulator_posDef S run t i)) := by
  classical
  intro t
  have hW := congrArg SOptLib.ModewiseTensorPreconditionerState.W (run.step t)
  have hpre :
      S.preconditionedGradient
          (fun i : Fin k => (run.state (currentIndex t)).H i +
            tensorContraction (run.gradientAt t) i)
          (run.step_posDef t) (run.gradientAt t) =
        tensorModeProducts (run.gradientAt t)
          (fun i : Fin k =>
            pdMatrixPower
              ((fun i : Fin k => (run.state (currentIndex t)).H i +
                tensorContraction (run.gradientAt t) i) i)
              (-(1 / ((2 : ℝ) * (k : ℝ)))) (run.step_posDef t i)) := by
    exact theorem10_preconditionedGradient_eq_tensorModeProducts S
      (fun i : Fin k => (run.state (currentIndex t)).H i +
        tensorContraction (run.gradientAt t) i)
      (run.step_posDef t) (run.gradientAt t)
  have hacc : ∀ i : Fin k,
      run.accumulator i (nextIndex t) =
        (run.state (currentIndex t)).H i + tensorContraction (run.gradientAt t) i := by
    intro i
    change (run.state (nextIndex t)).H i =
      (run.state (currentIndex t)).H i + tensorContraction (run.gradientAt t) i
    have hH := congrArg (fun st : TensorState S.dims => st.H i) (run.step t)
    simpa [TensorAlgorithm2.stepState] using hH
  have hpd_congr : ∀ {n : Nat} {A B : SquareMatrix n}, A = B → ∀ (s : ℝ)
      (hA : A.PosDef) (hB : B.PosDef),
      pdMatrixPower A s hA = pdMatrixPower B s hB := by
    intro n A B hAB s hA hB
    subst B
    congr
  calc
    run.iterate (nextIndex t) =
        run.iterate (currentIndex t) -
          S.eta •
            S.preconditionedGradient
              (fun i : Fin k => (run.state (currentIndex t)).H i +
                tensorContraction (run.gradientAt t) i)
              (run.step_posDef t) (run.gradientAt t) := by
          simpa [TensorAlgorithm2.stepState, TensorAlgorithm2.CorrectedRun.iterate] using hW
    _ = run.iterate (currentIndex t) -
          S.eta • tensorModeProducts (run.gradientAt t)
            (fun i : Fin k =>
              pdMatrixPower
                ((fun i : Fin k => (run.state (currentIndex t)).H i +
                  tensorContraction (run.gradientAt t) i) i)
                (-(1 / ((2 : ℝ) * (k : ℝ)))) (run.step_posDef t i)) := by
          rw [hpre]
    _ = run.iterate (currentIndex t) -
          S.eta • tensorModeProducts (run.gradientAt t)
            (fun i : Fin k =>
              pdMatrixPower (run.accumulator i (nextIndex t))
                (-(1 / ((2 : ℝ) * (k : ℝ))))
                (theorem10_next_accumulator_posDef S run t i)) := by
          have hM :
              (fun i : Fin k =>
                pdMatrixPower
                  ((fun i : Fin k => (run.state (currentIndex t)).H i +
                    tensorContraction (run.gradientAt t) i) i)
                  (-(1 / ((2 : ℝ) * (k : ℝ)))) (run.step_posDef t i)) =
                (fun i : Fin k =>
                  pdMatrixPower (run.accumulator i (nextIndex t))
                    (-(1 / ((2 : ℝ) * (k : ℝ))))
                    (theorem10_next_accumulator_posDef S run t i)) := by
            funext i
            exact hpd_congr (hacc i).symm (-(1 / ((2 : ℝ) * (k : ℝ))))
              (run.step_posDef t i) (theorem10_next_accumulator_posDef S run t i)
          rw [hM]

/- Book JSON additional_algorithm_specs.Algorithm 3: diagonal matrix Shampoo. -/
structure DiagonalAlgorithm3 (T m n : Nat) where
  epsilon : ℝ
  epsilon_nonneg : 0 ≤ epsilon
  eta : ℝ
  loss : Fin T → MatrixSpace m n → ℝ
  loss_convex : ∀ t : Fin T, ConvexOn ℝ Set.univ (loss t)

namespace DiagonalAlgorithm3

noncomputable def gradient (S : DiagonalAlgorithm3 T m n) (t : Fin T)
    (W : MatrixSpace m n)
    (hgrad : ∃ G : MatrixSpace m n, IsMatrixGradientAt S.loss t W G) :
    MatrixSpace m n :=
  matrixLossGradient S.loss t W hgrad

theorem gradient_def (S : DiagonalAlgorithm3 T m n) (t : Fin T)
    (W : MatrixSpace m n)
    (hgrad : ∃ G : MatrixSpace m n, IsMatrixGradientAt S.loss t W G) :
    S.gradient t W hgrad = matrixLossGradient S.loss t W hgrad := by
  rfl

theorem gradient_spec_of_exists (S : DiagonalAlgorithm3 T m n) (t : Fin T)
    (W : MatrixSpace m n)
    (hgrad : ∃ G : MatrixSpace m n, IsMatrixGradientAt S.loss t W G) :
    IsMatrixGradientAt S.loss t W (S.gradient t W hgrad) := by
  simpa [gradient] using matrixLossGradient_spec S.loss t W hgrad

def initialState (S : DiagonalAlgorithm3 T m n) : MatrixState m n where
  W := 0
  L := S.epsilon • (1 : SquareMatrix m)
  R := S.epsilon • (1 : SquareMatrix n)

theorem initial_leftAccumulator_psd (S : DiagonalAlgorithm3 T m n) :
    (S.initialState).L.PosSemidef := by
  simpa [initialState] using
    (Matrix.PosSemidef.one.smul S.epsilon_nonneg :
      Matrix.PosSemidef (S.epsilon • (1 : SquareMatrix m)))

theorem initial_rightAccumulator_psd (S : DiagonalAlgorithm3 T m n) :
    (S.initialState).R.PosSemidef := by
  simpa [initialState] using
    (Matrix.PosSemidef.one.smul S.epsilon_nonneg :
      Matrix.PosSemidef (S.epsilon • (1 : SquareMatrix n)))

theorem step_leftAccumulator_psd (S : DiagonalAlgorithm3 T m n) (t : Fin T)
    (st : MatrixState m n) (G : MatrixSpace m n) (hL : st.L.PosSemidef) :
    (st.L + diagonalPart (matrixGramLeft G)).PosSemidef := by
  exact hL.add (by
    apply Matrix.PosSemidef.diagonal
    intro i
    simpa [diagonalPart] using
      (Matrix.PosSemidef.diag_nonneg
        (by
          simpa [matrixGramLeft] using
            (Matrix.PosSemidef.one.mul_mul_conjTranspose_same (B := G)) :
          Matrix.PosSemidef (matrixGramLeft G)) (i := i)))

theorem step_rightAccumulator_psd (S : DiagonalAlgorithm3 T m n) (t : Fin T)
    (st : MatrixState m n) (G : MatrixSpace m n) (hR : st.R.PosSemidef) :
    (st.R + diagonalPart (matrixGramRight G)).PosSemidef := by
  exact hR.add (by
    apply Matrix.PosSemidef.diagonal
    intro i
    simpa [diagonalPart] using
      (Matrix.PosSemidef.diag_nonneg
        (by
          simpa [matrixGramRight] using
            (Matrix.PosSemidef.one.conjTranspose_mul_mul_same (B := G)) :
          Matrix.PosSemidef (matrixGramRight G)) (i := i)))

noncomputable def stepState (S : DiagonalAlgorithm3 T m n) (t : Fin T)
    (st : MatrixState m n) (G : MatrixSpace m n)
    (_hG : IsMatrixGradientAt S.loss t st.W G)
    (hLpd : (st.L + diagonalPart (matrixGramLeft G)).PosDef)
    (hRpd : (st.R + diagonalPart (matrixGramRight G)).PosDef) :
    MatrixState m n :=
  let Lnew := st.L + diagonalPart (matrixGramLeft G)
  let Rnew := st.R + diagonalPart (matrixGramRight G)
  { W := st.W -
      S.eta • (pdMatrixPower Lnew (-(1 / 4 : ℝ)) hLpd * G *
        pdMatrixPower Rnew (-(1 / 4 : ℝ)) hRpd)
    L := Lnew
    R := Rnew }

/- Corrected-domain trajectory for Appendix A's diagonal Shampoo variant. -/
structure CorrectedRun (S : DiagonalAlgorithm3 T m n) where
  state : Fin (T + 1) → MatrixState m n
  gradientAt : Fin T → MatrixSpace m n
  initial :
    state ⟨0, Nat.succ_pos T⟩ = S.initialState
  gradient_spec :
    ∀ t : Fin T, IsMatrixGradientAt S.loss t (state (currentIndex t)).W (gradientAt t)
  left_step_posDef :
    ∀ t : Fin T,
      ((state (currentIndex t)).L + diagonalPart (matrixGramLeft (gradientAt t))).PosDef
  right_step_posDef :
    ∀ t : Fin T,
      ((state (currentIndex t)).R + diagonalPart (matrixGramRight (gradientAt t))).PosDef
  step :
    ∀ t : Fin T,
      state (nextIndex t) =
        S.stepState t (state (currentIndex t)) (gradientAt t) (gradient_spec t)
          (left_step_posDef t) (right_step_posDef t)

noncomputable def CorrectedRun.iterate {S : DiagonalAlgorithm3 T m n}
    (run : S.CorrectedRun) (t : Fin (T + 1)) : MatrixSpace m n :=
  (run.state t).W

noncomputable def CorrectedRun.leftAccumulator {S : DiagonalAlgorithm3 T m n}
    (run : S.CorrectedRun) (t : Fin (T + 1)) :
    SquareMatrix m :=
  (run.state t).L

theorem CorrectedRun.leftAccumulator_psd {S : DiagonalAlgorithm3 T m n}
    (run : S.CorrectedRun) (t : Fin (T + 1)) :
    (run.leftAccumulator t).PosSemidef := by
  induction t using Fin.induction with
  | zero =>
      change Matrix.PosSemidef ((run.state ⟨0, Nat.succ_pos T⟩).L)
      rw [run.initial]
      exact S.initial_leftAccumulator_psd
  | succ t ih =>
      change Matrix.PosSemidef ((run.state (nextIndex t)).L)
      rw [run.step t]
      simpa [DiagonalAlgorithm3.stepState] using (run.left_step_posDef t).posSemidef

noncomputable def CorrectedRun.rightAccumulator {S : DiagonalAlgorithm3 T m n}
    (run : S.CorrectedRun) (t : Fin (T + 1)) :
    SquareMatrix n :=
  (run.state t).R

theorem CorrectedRun.rightAccumulator_psd {S : DiagonalAlgorithm3 T m n}
    (run : S.CorrectedRun) (t : Fin (T + 1)) :
    (run.rightAccumulator t).PosSemidef := by
  induction t using Fin.induction with
  | zero =>
      change Matrix.PosSemidef ((run.state ⟨0, Nat.succ_pos T⟩).R)
      rw [run.initial]
      exact S.initial_rightAccumulator_psd
  | succ t ih =>
      change Matrix.PosSemidef ((run.state (nextIndex t)).R)
      rw [run.step t]
      simpa [DiagonalAlgorithm3.stepState] using (run.right_step_posDef t).posSemidef

noncomputable def CorrectedRun.regret {S : DiagonalAlgorithm3 T m n}
    (run : S.CorrectedRun) (Wstar : MatrixSpace m n) : ℝ :=
  ∑ t : Fin T, (S.loss t (run.iterate (currentIndex t)) - S.loss t Wstar)

noncomputable def CorrectedRun.comparatorRadiusInfinity {S : DiagonalAlgorithm3 T m n}
    (run : S.CorrectedRun) [Nonempty (Fin T)] [Nonempty (FlatMatrixIndex m n)]
    (Wstar : MatrixSpace m n) : ℝ :=
  finiteMax fun t : Fin T => matrixEntrywiseSupNorm (run.iterate (currentIndex t) - Wstar)

theorem initialState_spec (S : DiagonalAlgorithm3 T m n) :
    (S.initialState).W = 0 ∧
      (S.initialState).L = S.epsilon • (1 : SquareMatrix m) ∧
      (S.initialState).R = S.epsilon • (1 : SquareMatrix n) := by
  simp [initialState]

theorem stepState_spec (S : DiagonalAlgorithm3 T m n) (t : Fin T) (st : MatrixState m n) :
    ∀ (G : MatrixSpace m n) (hG : IsMatrixGradientAt S.loss t st.W G)
      (hLpd : (st.L + diagonalPart (matrixGramLeft G)).PosDef)
      (hRpd : (st.R + diagonalPart (matrixGramRight G)).PosDef),
    let st' := S.stepState t st G hG hLpd hRpd
    st'.L = st.L + diagonalPart (G * G.transpose) ∧
      st'.R = st.R + diagonalPart (G.transpose * G) ∧
      st'.W = st.W - S.eta •
        (pdMatrixPower st'.L (-(1 / 4 : ℝ)) hLpd * G *
          pdMatrixPower st'.R (-(1 / 4 : ℝ)) hRpd) := by
  intro G hG hLpd hRpd
  simp [stepState, matrixGramLeft, matrixGramRight]

end DiagonalAlgorithm3

private theorem theorem13_flattened_loss_gradient_bridge {T m n : Nat}
    (S : DiagonalAlgorithm3 T m n) (run : S.CorrectedRun) (t : Fin T) :
    HasGradientWithinAt
      (fun v : EuclideanSpace ℝ (FlatMatrixIndex m n) =>
        S.loss t (fun i j => (EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ v) (i, j)))
      ((EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ).symm (matrixVec (run.gradientAt t)))
      Set.univ
      ((EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ).symm
        (matrixVec (run.iterate (currentIndex t)))) := by
  classical
  letI : NormedAddCommGroup (MatrixSpace m n) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (MatrixSpace m n) := Matrix.normedSpace
  have hMatrixInner : ∀ (G : MatrixSpace m n)
      (v : EuclideanSpace ℝ (FlatMatrixIndex m n)),
      matrixInner G
          (fun i j => (EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ v) (i, j)) =
        inner ℝ ((EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ).symm
          (matrixVec G)) v := by
    intro G v
    have hinner := euclidean_inner_eq_vectorDot (matrixVec G)
      ((EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ) v)
    calc
      matrixInner G
          (fun i j => (EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ v) (i, j)) =
          vectorDot (matrixVec G) ((EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ) v) := by
            rw [matrixInner, vectorDot]
            rw [← Finset.sum_product']
            simp [matrixVec, Finset.univ_product_univ]
      _ = inner ℝ ((EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ).symm
            (matrixVec G))
          ((EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ).symm
            ((EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ) v)) := hinner.symm
      _ = inner ℝ ((EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ).symm
            (matrixVec G)) v := by
          simp
  obtain ⟨D, hD, hD_apply⟩ := run.gradient_spec t
  let unvecLin : EuclideanSpace ℝ (FlatMatrixIndex m n) →ₗ[ℝ] MatrixSpace m n :=
    { toFun := fun v i j => (EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ v) (i, j)
      map_add' := by
        intro x y
        ext i j
        simp
      map_smul' := by
        intro a x
        ext i j
        simp }
  let unvecCLM : EuclideanSpace ℝ (FlatMatrixIndex m n) →L[ℝ] MatrixSpace m n :=
    unvecLin.toContinuousLinearMap
  let x : EuclideanSpace ℝ (FlatMatrixIndex m n) :=
    (EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ).symm
      (matrixVec (run.iterate (currentIndex t)))
  have hx : unvecCLM x = run.iterate (currentIndex t) := by
    ext i j
    simp [unvecCLM, unvecLin, x, matrixVec]
  have hD_at : HasFDerivAt (S.loss t) D (unvecCLM x) := by
    simpa [hx, DiagonalAlgorithm3.CorrectedRun.iterate] using hD
  have hlin_deriv : HasFDerivAt
      (fun v : EuclideanSpace ℝ (FlatMatrixIndex m n) => unvecCLM v)
      unvecCLM x := by
    simpa using (unvecCLM.hasFDerivAt (x := x))
  have hcomp_raw : HasFDerivAt
      ((S.loss t) ∘ (fun v : EuclideanSpace ℝ (FlatMatrixIndex m n) => unvecCLM v))
      (D.comp unvecCLM) x := by
    exact hD_at.comp (x := x)
      (f := fun v : EuclideanSpace ℝ (FlatMatrixIndex m n) => unvecCLM v)
      hlin_deriv
  have hcomp : HasFDerivAt
      (fun v : EuclideanSpace ℝ (FlatMatrixIndex m n) => S.loss t (unvecCLM v))
      (D.comp unvecCLM) x := by
    simpa [Function.comp_def] using hcomp_raw
  have hdualEq :
      D.comp unvecCLM =
        InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (FlatMatrixIndex m n))
          ((EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ).symm
            (matrixVec (run.gradientAt t))) := by
    ext v
    calc
      (D.comp unvecCLM) v = D (unvecCLM v) := rfl
      _ = matrixInner (run.gradientAt t) (unvecCLM v) := hD_apply _
      _ = matrixInner (run.gradientAt t)
          (fun i j => (EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ v) (i, j)) := by
            simp [unvecCLM, unvecLin]
      _ = inner ℝ ((EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ).symm
          (matrixVec (run.gradientAt t))) v := hMatrixInner (run.gradientAt t) v
      _ = (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (FlatMatrixIndex m n))
          ((EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ).symm
            (matrixVec (run.gradientAt t)))) v := by
            simp [InnerProductSpace.toDual_apply_apply]
  have hgradAt : HasGradientAt
      (fun v : EuclideanSpace ℝ (FlatMatrixIndex m n) => S.loss t (unvecCLM v))
      ((EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ).symm
        (matrixVec (run.gradientAt t))) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    simpa [hdualEq] using hcomp
  rw [hasGradientWithinAt_univ]
  simpa [x, unvecCLM, unvecLin] using hgradAt

theorem tensor_contraction_eq_matricization_gram {k : Nat} {dims : Fin k → Nat}
    (A : TensorSpace dims) (i : Fin k) :
    tensorContraction A i = matricization A i * (matricization A i).transpose := by
  rfl

/- Book JSON key_lemmas.Lemma_1_adaptive_OMD_regret.
   Source discrepancy: the PDF statement (source/original_source.txt lines
   232-238) contains the factor `1 / (2 * eta)` but does not state `eta > 0`.
   In Lean, division by zero is totalized, and the eta = 0 specialization of
   the old unconstrained statement is false (already with T = d = 1, H = 1,
   constant zero iterates, g = 1, and wstar = -1), as formalized by
   `Lemma_1_adaptive_OMD_regret_unqualified_false` below.  We therefore expose
   the standard positive-stepsize side condition required by the cited OMD
   bound. -/
theorem Lemma_1_adaptive_OMD_regret_unqualified_false :
    ¬ (∀ {T d : Nat} (eta : ℝ)
      (w : Fin (T + 1) → Fin d → ℝ) (g : Fin T → Fin d → ℝ)
      (H : Fin T → SquareMatrix d) (wstar : Fin d → ℝ),
      IsOMDTrajectory eta w g H →
      (∀ t : Fin T, (H t).PosDef) →
      ∑ t : Fin T, vectorDot (g t) (w (currentIndex t) - wstar) ≤
        (1 / (2 * eta)) *
          ∑ t : Fin T,
            (quadraticForm (w (currentIndex t) - wstar) (H t) -
              quadraticForm (w (nextIndex t) - wstar) (H t)) +
        (eta / 2) * ∑ t : Fin T, dualQuadraticForm (g t) (H t)) := by
  intro h
  let w : Fin (1 + 1) → Fin 1 → ℝ := fun _ _ => 0
  let g : Fin 1 → Fin 1 → ℝ := fun _ _ => 1
  let H : Fin 1 → SquareMatrix 1 := fun _ => 1
  let wstar : Fin 1 → ℝ := fun _ => -1
  have hupdate : IsOMDTrajectory (0 : ℝ) w g H := by
    intro t
    ext i
    simp [w, H, omdUpdate]
  have hHpd : ∀ t : Fin 1, (H t).PosDef := by
    intro t
    simpa [H] using (Matrix.PosDef.one : Matrix.PosDef (1 : SquareMatrix 1))
  have hbad := h (T := 1) (d := 1) (0 : ℝ) w g H wstar hupdate hHpd
  norm_num [vectorDot, quadraticForm, dualQuadraticForm, w, g, H, wstar,
    currentIndex, nextIndex] at hbad

private theorem quadraticForm_eq_toBilin {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (H : GenericSquare ι) :
    quadraticForm x H = Matrix.toBilin' H x x := by
  rw [Matrix.toBilin'_apply]
  rfl

private theorem quadraticForm_eq_dotProduct_mulVec {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (H : GenericSquare ι) :
    quadraticForm x H = x ⬝ᵥ (H.mulVec x) := by
  classical
  unfold quadraticForm dotProduct Matrix.mulVec
  refine Finset.sum_congr rfl ?_
  intro i _hi
  change (∑ j, x i * H i j * x j) = x i * (∑ j, H i j * x j)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  ring

private theorem quadraticForm_sub_matrix {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (A B : GenericSquare ι) :
    quadraticForm x (A - B) = quadraticForm x A - quadraticForm x B := by
  simpa [quadraticForm, SOptLib.finiteMatrixQuadraticForm,
    SOptLib.finiteMatrixVec, Finset.mul_sum, mul_assoc] using
      SOptLib.finiteMatrixQuadraticForm_sub_matrix (WithLp.toLp 2 x) A B

private theorem quadraticForm_zero_matrix {ι : Type*} [Fintype ι]
    (x : ι → ℝ) :
    quadraticForm x (0 : GenericSquare ι) = 0 := by
  unfold quadraticForm
  simp

private theorem quadraticForm_nonneg_of_posSemidef {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (M : GenericSquare ι) (hM : M.PosSemidef) :
    0 ≤ quadraticForm x M := by
  simpa [quadraticForm, SOptLib.finiteMatrixQuadraticForm, SOptLib.finiteMatrixVec,
    Finset.mul_sum, mul_assoc] using
    SOptLib.finiteMatrixQuadraticForm_nonneg_of_posSemidef (WithLp.toLp 2 x) M hM

private theorem genericTrace_sub_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : GenericSquare ι) :
    genericTrace (A - B) = genericTrace A - genericTrace B := by
  simp [genericTrace, Matrix.trace_sub]

private theorem genericTrace_zero_matrix {ι : Type*} [Fintype ι] [DecidableEq ι] :
    genericTrace (0 : GenericSquare ι) = 0 := by
  simp [genericTrace]

private theorem genericTrace_nonneg_of_posSemidef {ι : Type*}
    [Fintype ι] [DecidableEq ι] (M : GenericSquare ι) (hM : M.PosSemidef) :
    0 ≤ genericTrace M := by
  classical
  let lam : ι → ℝ := hM.1.eigenvalues
  have htrace_eigs : genericTrace M = ∑ i, lam i := by
    dsimp [genericTrace]
    conv_lhs =>
      rw [hM.1.spectral_theorem, Unitary.conjStarAlgAut_apply,
        Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
    simp [lam, Function.comp_def]
  rw [htrace_eigs]
  exact Finset.sum_nonneg (by
    intro i _hi
    exact hM.eigenvalues_nonneg i)

private theorem genericTrace_mono_of_matrix_le {ι : Type*}
    [Fintype ι] [DecidableEq ι] {A B : GenericSquare ι} (hAB : A ≤ B) :
    genericTrace A ≤ genericTrace B := by
  simpa [genericTrace] using Matrix.trace_mono_of_le hAB

set_option synthInstance.maxHeartbeats 200000 in
private theorem finite_changing_metric_quadratic_telescope_le_trace_nat {T : Nat}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : Nat → ι → ℝ) (H : Nat → GenericSquare ι) (D : ℝ)
    (hH0 : H 0 = 0)
    (hInc : ∀ t : Fin T, (H (t.val + 1) - H t.val).PosSemidef)
    (hFinalPSD : (H T).PosSemidef)
    (hRadiusTraceBound : ∀ (t : Fin T) (M : GenericSquare ι),
      M.PosSemidef → quadraticForm (x t.val) M ≤ D ^ 2 * genericTrace M) :
    (∑ t : Fin T,
      (quadraticForm (x t.val) (H (t.val + 1)) -
        quadraticForm (x (t.val + 1)) (H (t.val + 1)))) ≤
      D ^ 2 * genericTrace (H T) := by
  classical
  simpa [quadraticForm_eq_toBilin, genericTrace] using
    (SOptLib.sum_changingMatrixQuadraticForm_le_sq_mul_trace_terminal
      (x := x) (H := H) (D := D) (hH0 := hH0) (hInc := hInc)
      (hIncBound := by
        intro t
        simpa [quadraticForm_eq_toBilin, genericTrace] using
          hRadiusTraceBound t (H (t.val + 1) - H t.val) (hInc t)))

private theorem finite_changing_metric_quadratic_telescope_le_trace {T : Nat}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : Fin (T + 1) → ι → ℝ) (H : Fin (T + 1) → GenericSquare ι) (D : ℝ)
    (hH0 : H ⟨0, Nat.zero_lt_succ T⟩ = 0)
    (hInc : ∀ t : Fin T, (H (nextIndex t) - H (currentIndex t)).PosSemidef)
    (hFinalPSD : (H ⟨T, Nat.lt_succ_self T⟩).PosSemidef)
    (hRadiusTraceBound : ∀ (t : Fin T) (M : GenericSquare ι),
      M.PosSemidef → quadraticForm (x (currentIndex t)) M ≤ D ^ 2 * genericTrace M) :
    (∑ t : Fin T,
      (quadraticForm (x (currentIndex t)) (H (nextIndex t)) -
        quadraticForm (x (nextIndex t)) (H (nextIndex t)))) ≤
      D ^ 2 * genericTrace (H ⟨T, Nat.lt_succ_self T⟩) := by
  classical
  let clampIndex : Nat → Fin (T + 1) := fun n =>
    ⟨min n T, Nat.lt_succ_of_le (Nat.min_le_right n T)⟩
  let xNat : Nat → ι → ℝ := fun n => x (clampIndex n)
  let HNat : Nat → GenericSquare ι := fun n => H (clampIndex n)
  have hcur (t : Fin T) : clampIndex t.val = currentIndex t := by
    ext
    simp [clampIndex, currentIndex, Nat.min_eq_left (Nat.le_of_lt t.isLt)]
  have hnxt (t : Fin T) : clampIndex (t.val + 1) = nextIndex t := by
    ext
    simp [clampIndex, nextIndex, Nat.min_eq_left (Nat.succ_le_of_lt t.isLt)]
  have hfin : clampIndex T = (⟨T, Nat.lt_succ_self T⟩ : Fin (T + 1)) := by
    ext
    simp [clampIndex]
  have hzero : clampIndex 0 = (⟨0, Nat.zero_lt_succ T⟩ : Fin (T + 1)) := by
    ext
    simp [clampIndex]
  have hNat :=
    finite_changing_metric_quadratic_telescope_le_trace_nat (T := T)
      (ι := ι) xNat HNat D
      (by simpa [HNat, clampIndex] using hH0)
      (by
        intro t
        simpa [HNat, hcur t, hnxt t] using hInc t)
      (by simpa [HNat, hfin] using hFinalPSD)
      (by
        intro t M hM
        simpa [xNat, hcur t] using hRadiusTraceBound t M hM)
  simpa [xNat, HNat, hcur, hnxt, hfin] using hNat

set_option synthInstance.maxHeartbeats 200000 in
private theorem finite_changing_metric_quadratic_telescope_le_trace_of_increment_bound
    {T : Nat} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : Fin (T + 1) → ι → ℝ) (H : Fin (T + 1) → GenericSquare ι) (D : ℝ)
    (hH0 : H ⟨0, Nat.zero_lt_succ T⟩ = 0)
    (hInc : ∀ t : Fin T, (H (nextIndex t) - H (currentIndex t)).PosSemidef)
    (hFinalPSD : (H ⟨T, Nat.lt_succ_self T⟩).PosSemidef)
    (hIncBound : ∀ t : Fin T,
      quadraticForm (x (currentIndex t)) (H (nextIndex t) - H (currentIndex t)) ≤
        D ^ 2 * genericTrace (H (nextIndex t) - H (currentIndex t))) :
    (∑ t : Fin T,
      (quadraticForm (x (currentIndex t)) (H (nextIndex t)) -
        quadraticForm (x (nextIndex t)) (H (nextIndex t)))) ≤
      D ^ 2 * genericTrace (H ⟨T, Nat.lt_succ_self T⟩) := by
  simpa [quadraticForm_eq_toBilin, genericTrace, currentIndex, nextIndex] using
    (SOptLib.sum_changingMatrixQuadraticForm_le_mul_trace_terminal_of_increment_bound
      (x := x) (H := H) (C := D ^ 2) hH0 (by
        simpa [Matrix.toBilin'_apply'] using
          hFinalPSD.dotProduct_mulVec_nonneg (x ⟨T, Nat.lt_succ_self T⟩)) (by
        intro t
        simpa [quadraticForm_eq_toBilin, genericTrace, currentIndex, nextIndex] using
          hIncBound t))

private theorem quadraticForm_mono_of_matrix_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) {A B : GenericSquare ι} (hAB : A ≤ B) :
    quadraticForm x A ≤ quadraticForm x B := by
  simpa only [quadraticForm_eq_toBilin] using Matrix.toBilin_self_mono_of_le x hAB

private theorem matrix_le_trace_smul_one_of_posSemidef {ι : Type*}
    [Fintype ι] [DecidableEq ι] (M : GenericSquare ι) (hM : M.PosSemidef) :
    M ≤ Matrix.trace M • (1 : GenericSquare ι) := by
  exact Matrix.le_trace_smul_one_of_posSemidef M hM

private theorem quadraticForm_smul_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (c : ℝ) :
    quadraticForm x (c • (1 : GenericSquare ι)) = (∑ i, x i ^ 2) * c := by
  classical
  unfold quadraticForm
  calc
    (∑ i, ∑ j, x i * (c • (1 : GenericSquare ι)) i j * x j) =
        ∑ i, x i * c * x i := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          simp [Matrix.one_apply]
    _ = ∑ i, x i ^ 2 * c := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          ring
    _ = (∑ i, x i ^ 2) * c := by
          rw [Finset.sum_mul]

private theorem quadraticForm_le_sq_sum_mul_trace_of_posSemidef {ι : Type*}
    [Fintype ι] [DecidableEq ι] (x : ι → ℝ) (M : GenericSquare ι)
    (hM : M.PosSemidef) :
    quadraticForm x M ≤ (∑ i, x i ^ 2) * genericTrace M := by
  simpa only [quadraticForm_eq_toBilin, genericTrace] using
    Matrix.toBilin_self_le_sum_sq_mul_trace_of_posSemidef x M hM

private theorem quadraticForm_diagonal_le_finiteMax_sq_mul_trace {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (x : ι → ℝ) (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) :
    quadraticForm x (Matrix.diagonal d : GenericSquare ι) ≤
      (finiteMax fun i : ι => |x i|) ^ 2 *
        genericTrace (Matrix.diagonal d : GenericSquare ι) := by
  simpa [quadraticForm_eq_toBilin, genericTrace] using
    Matrix.toBilin_diagonal_self_le_sq_mul_trace_of_coordinate_bound
      x d (finiteMax fun i : ι => |x i|) hd (fun i => by
        dsimp [finiteMax]
        exact Finset.le_sup' (fun j : ι => |x j|) (Finset.mem_univ i))

private theorem quadraticForm_eq_diagonal_le_finiteMax_sq_mul_trace {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (x : ι → ℝ) (M : GenericSquare ι)
    (hMdiag : M = Matrix.diagonal (fun i : ι => M i i)) (hMpsd : M.PosSemidef) :
    quadraticForm x M ≤
      (finiteMax fun i : ι => |x i|) ^ 2 * genericTrace M := by
  simpa [quadraticForm_eq_toBilin, genericTrace] using
    Matrix.toBilin_self_le_sq_mul_trace_of_diagonal_posSemidef
      x M (finiteMax fun i : ι => |x i|) hMdiag hMpsd (fun i => by
        dsimp [finiteMax]
        exact Finset.le_sup' (fun j : ι => |x j|) (Finset.mem_univ i))

private theorem matrix_mulVec_inv_mulVec_of_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : GenericSquare ι) (hHpd : H.PosDef) (g : ι → ℝ) :
    H.mulVec (H⁻¹.mulVec g) = g := by
  exact Matrix.mulVec_inv_mulVec_of_posDef H hHpd g

private theorem matrix_inv_mulVec_mulVec_of_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : GenericSquare ι) (hHpd : H.PosDef) (g : ι → ℝ) :
    H⁻¹.mulVec (H.mulVec g) = g := by
  exact Matrix.inv_mulVec_mulVec_of_posDef H hHpd g

private theorem toBilin_inv_mulVec_right_eq_vectorDot {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a g : ι → ℝ) (H : GenericSquare ι) (hHpd : H.PosDef) :
    Matrix.toBilin' H a (H⁻¹.mulVec g) = vectorDot g a := by
  simpa [vectorDot] using
    Matrix.toBilin_inv_mulVec_right_eq_dotProduct_of_posDef
      (a := a) (g := g) (H := H) (hH := hHpd)

private theorem dualQuadraticForm_eq_vectorDot_inv_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℝ) (H : GenericSquare ι) :
    dualQuadraticForm g H = vectorDot g (H⁻¹.mulVec g) := by
  classical
  unfold dualQuadraticForm SOptLib.finiteMatrixDualQuadraticForm vectorDot Matrix.mulVec
    dotProduct
  refine Finset.sum_congr rfl ?_
  intro i _hi
  simp [Finset.mul_sum, mul_assoc]

private theorem quadraticForm_omd_shift_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (eta : ℝ) (a g : ι → ℝ) (H : GenericSquare ι) (hHpd : H.PosDef) :
    quadraticForm (a - eta • H⁻¹.mulVec g) H =
      quadraticForm a H - 2 * eta * vectorDot g a +
        eta ^ 2 * dualQuadraticForm g H := by
  simpa only [quadraticForm_eq_toBilin, vectorDot, dualQuadraticForm,
    SOptLib.finiteMatrixDualQuadraticForm, Matrix.toBilin'_apply] using
      Matrix.toBilin_inv_mulVec_shift_self eta a g H hHpd

private theorem omd_one_step_regret_bound {ι : Type*} [Fintype ι] [DecidableEq ι] (eta : ℝ)
    (heta_pos : 0 < eta)
    (wcur wnext g wstar : ι → ℝ) (H : GenericSquare ι)
    (hHpd : H.PosDef)
    (hstep : wnext = wcur - eta • H⁻¹.mulVec g) :
    vectorDot g (wcur - wstar) ≤
      (1 / (2 * eta)) *
        (quadraticForm (wcur - wstar) H -
          quadraticForm (wnext - wstar) H) +
      (eta / 2) * dualQuadraticForm g H := by
  simpa only [vectorDot, quadraticForm_eq_toBilin, dualQuadraticForm,
    SOptLib.finiteMatrixDualQuadraticForm, Matrix.toBilin'_apply] using
      SOptLib.preconditionedGradientStep_inner_le_quadratic_drop_add_dual
        eta (ne_of_gt heta_pos) wcur wnext g wstar H hHpd
        (by simpa only [SOptLib.preconditionedGradientStep_def] using hstep)

theorem Lemma_1_adaptive_OMD_regret {T d : Nat} (eta : ℝ)
    (heta_pos : 0 < eta)
    (w : Fin (T + 1) → Fin d → ℝ) (g : Fin T → Fin d → ℝ)
    (H : Fin T → SquareMatrix d) (wstar : Fin d → ℝ)
    (hupdate : IsOMDTrajectory eta w g H)
    (hHpd : ∀ t : Fin T, (H t).PosDef) :
    ∑ t : Fin T, vectorDot (g t) (w (currentIndex t) - wstar) ≤
      (1 / (2 * eta)) *
        ∑ t : Fin T,
          (quadraticForm (w (currentIndex t) - wstar) (H t) -
            quadraticForm (w (nextIndex t) - wstar) (H t)) +
      (eta / 2) * ∑ t : Fin T, dualQuadraticForm (g t) (H t) := by
  classical
  let rhsStep : Fin T → ℝ := fun t =>
    (1 / (2 * eta)) *
      (quadraticForm (w (currentIndex t) - wstar) (H t) -
        quadraticForm (w (nextIndex t) - wstar) (H t)) +
    (eta / 2) * dualQuadraticForm (g t) (H t)
  have hsum :
      ∑ t : Fin T, vectorDot (g t) (w (currentIndex t) - wstar) ≤
        ∑ t : Fin T, rhsStep t := by
    refine Finset.sum_le_sum ?_
    intro t _ht
    exact omd_one_step_regret_bound eta heta_pos
      (w (currentIndex t)) (w (nextIndex t)) (g t) wstar (H t)
      (hHpd t) (by simpa [omdUpdate] using hupdate t)
  calc
    ∑ t : Fin T, vectorDot (g t) (w (currentIndex t) - wstar)
        ≤ ∑ t : Fin T, rhsStep t := hsum
    _ = (1 / (2 * eta)) *
          ∑ t : Fin T,
            (quadraticForm (w (currentIndex t) - wstar) (H t) -
              quadraticForm (w (nextIndex t) - wstar) (H t)) +
        (eta / 2) * ∑ t : Fin T, dualQuadraticForm (g t) (H t) := by
          dsimp [rhsStep]
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

private theorem finite_index_adaptive_omd_regret {T : Nat} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (eta : ℝ)
    (heta_pos : 0 < eta)
    (w : Fin (T + 1) → ι → ℝ) (g : Fin T → ι → ℝ)
    (H : Fin T → GenericSquare ι) (wstar : ι → ℝ)
    (hupdate : ∀ t : Fin T,
      w (nextIndex t) = w (currentIndex t) - eta • (H t)⁻¹.mulVec (g t))
    (hHpd : ∀ t : Fin T, (H t).PosDef) :
    ∑ t : Fin T, vectorDot (g t) (w (currentIndex t) - wstar) ≤
      (1 / (2 * eta)) *
        ∑ t : Fin T,
          (quadraticForm (w (currentIndex t) - wstar) (H t) -
            quadraticForm (w (nextIndex t) - wstar) (H t)) +
      (eta / 2) * ∑ t : Fin T, dualQuadraticForm (g t) (H t) := by
  simpa only [currentIndex, nextIndex, vectorDot, quadraticForm_eq_toBilin,
    dualQuadraticForm, SOptLib.finiteMatrixDualQuadraticForm,
    Matrix.toBilin'_apply] using
      (SOptLib.sum_inner_le_sum_quadratic_drop_add_dual_of_preconditionedGradientSteps
        eta (ne_of_gt heta_pos) w g H wstar
        (fun t => by
          simpa only [currentIndex, nextIndex,
            SOptLib.preconditionedGradientStep_def] using hupdate t)
        hHpd)

private theorem dualQuadraticForm_eq_trace_vectorOuter_mul_inv {d : Nat}
    (g : Fin d → ℝ) (K : SquareMatrix d) (hK : K.PosDef) :
    dualQuadraticForm g K = matrixTrace (vectorOuter g * K⁻¹) := by
  simpa [dualQuadraticForm, matrixTrace, vectorOuter, Matrix.vecMulVec] using
    SOptLib.finiteMatrixDualQuadraticForm_eq_trace_vecMulVec_mul_inv
      (g := g) (K := K)


private theorem fin_prefix_sum_succ {T : Nat} (f : Fin T → ℝ) {n : Nat}
    (hn : n < T) :
    (∑ s : Fin T, if s.1 < n + 1 then f s else 0) =
      (∑ s : Fin T, if s.1 < n then f s else 0) + f ⟨n, hn⟩ := by
  classical
  let a : Fin T := ⟨n, hn⟩
  have hfilter :
      (Finset.univ.filter (fun s : Fin T => s.1 < n + 1)) =
        insert a (Finset.univ.filter (fun s : Fin T => s.1 < n)) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hs
      have hle : s.1 ≤ n := Nat.lt_succ_iff.mp hs
      rcases Nat.lt_or_eq_of_le hle with hlt | heq
      · exact Or.inr hlt
      · left
        ext
        exact heq
    · intro hs
      rcases hs with hs | hs
      · rw [hs]
        exact Nat.lt_succ_self n
      · exact Nat.lt_trans hs (Nat.lt_succ_self n)
  calc
    (∑ s : Fin T, if s.1 < n + 1 then f s else 0)
        = Finset.sum (Finset.univ.filter (fun s : Fin T => s.1 < n + 1)) f := by
            simp [Finset.sum_filter]
    _ = Finset.sum (insert a (Finset.univ.filter (fun s : Fin T => s.1 < n))) f := by
            rw [hfilter]
    _ = f a + Finset.sum (Finset.univ.filter (fun s : Fin T => s.1 < n)) f := by
            rw [Finset.sum_insert]
            simp [a]
    _ = (∑ s : Fin T, if s.1 < n then f s else 0) + f ⟨n, hn⟩ := by
            simp [Finset.sum_filter, a, add_comm]

private theorem fin_prefix_sum_succ_addCommMonoid {T : Nat} {α : Type*}
    [AddCommMonoid α] (f : Fin T → α) {n : Nat} (hn : n < T) :
    (∑ s : Fin T, if s.1 < n + 1 then f s else 0) =
      (∑ s : Fin T, if s.1 < n then f s else 0) + f ⟨n, hn⟩ := by
  exact sum_fin_lt_succ_eq_sum_fin_lt_add f hn

private theorem fin_prefix_sum_final {T : Nat} (f : Fin T → ℝ) :
    (∑ s : Fin T, if s.1 < T then f s else 0) = ∑ s : Fin T, f s := by
  classical
  refine Finset.sum_congr rfl ?_
  intro s hs
  simp [s.2]

private theorem ftl_btl_prefix_induction_nat {T d : Nat}
    (g : Fin T → Fin d → ℝ) (H : Fin (T + 1) → SquareMatrix d)
    (Phi : SquareMatrix d → ℝ)
    (hHpd : ∀ t : Fin (T + 1), (H t).PosDef)
    (hPrefixMin : ∀ N : Fin (T + 1), ∀ K : SquareMatrix d, K.PosDef →
      (∑ s : Fin T, if s.1 < N.1 then dualQuadraticForm (g s) (H N) else 0) +
          Phi (H N) ≤
        (∑ s : Fin T, if s.1 < N.1 then dualQuadraticForm (g s) K else 0) +
          Phi K) :
    ∀ n : Nat, ∀ hn : n ≤ T,
      (∑ s : Fin T, if s.1 < n then dualQuadraticForm (g s) (H (nextIndex s)) else 0) +
          Phi (H ⟨0, Nat.succ_pos T⟩) ≤
        (∑ s : Fin T,
            if s.1 < n then
              dualQuadraticForm (g s) (H ⟨n, Nat.lt_succ_of_le hn⟩)
            else 0) +
          Phi (H ⟨n, Nat.lt_succ_of_le hn⟩) := by
  classical
  intro n
  induction n with
  | zero =>
      intro hn
      simp
  | succ n ih =>
      intro hn
      have hnT : n < T := Nat.lt_of_succ_le hn
      let N : Fin (T + 1) := ⟨n, Nat.lt_succ_of_le (Nat.le_of_lt hnT)⟩
      let Nnext : Fin (T + 1) := ⟨n + 1, Nat.lt_succ_of_le hn⟩
      let idx : Fin T := ⟨n, hnT⟩
      have ihN :
          (∑ s : Fin T, if s.1 < n then dualQuadraticForm (g s) (H (nextIndex s)) else 0) +
              Phi (H ⟨0, Nat.succ_pos T⟩) ≤
            (∑ s : Fin T,
                if s.1 < n then dualQuadraticForm (g s) (H N) else 0) +
              Phi (H N) := by
        simpa [N] using ih (Nat.le_of_lt hnT)
      have hminN :
          (∑ s : Fin T, if s.1 < n then dualQuadraticForm (g s) (H N) else 0) +
              Phi (H N) ≤
            (∑ s : Fin T, if s.1 < n then dualQuadraticForm (g s) (H Nnext) else 0) +
              Phi (H Nnext) := by
        simpa [N] using hPrefixMin N (H Nnext) (hHpd Nnext)
      have hchain :
          (∑ s : Fin T, if s.1 < n then dualQuadraticForm (g s) (H (nextIndex s)) else 0) +
              Phi (H ⟨0, Nat.succ_pos T⟩) ≤
            (∑ s : Fin T, if s.1 < n then dualQuadraticForm (g s) (H Nnext) else 0) +
              Phi (H Nnext) :=
        le_trans ihN hminN
      have hleft :=
        fin_prefix_sum_succ
          (fun s : Fin T => dualQuadraticForm (g s) (H (nextIndex s))) hnT
      have hright :=
        fin_prefix_sum_succ
          (fun s : Fin T => dualQuadraticForm (g s) (H Nnext)) hnT
      have hnext : nextIndex idx = Nnext := by
        ext
        rfl
      have hterm :
          dualQuadraticForm (g idx) (H (nextIndex idx)) =
            dualQuadraticForm (g idx) (H Nnext) := by
        rw [hnext]
      have hstep := add_le_add_right hchain (dualQuadraticForm (g idx) (H Nnext))
      calc
        (∑ s : Fin T,
            if s.1 < n + 1 then dualQuadraticForm (g s) (H (nextIndex s)) else 0) +
            Phi (H ⟨0, Nat.succ_pos T⟩)
            = ((∑ s : Fin T,
                if s.1 < n then dualQuadraticForm (g s) (H (nextIndex s)) else 0) +
                Phi (H ⟨0, Nat.succ_pos T⟩)) +
              dualQuadraticForm (g idx) (H Nnext) := by
                rw [hleft]
                rw [hterm]
                ring
        _ ≤ ((∑ s : Fin T,
                if s.1 < n then dualQuadraticForm (g s) (H Nnext) else 0) +
                Phi (H Nnext)) +
              dualQuadraticForm (g idx) (H Nnext) := by
                linarith
        _ = (∑ s : Fin T,
              if s.1 < n + 1 then dualQuadraticForm (g s) (H Nnext) else 0) +
              Phi (H Nnext) := by
                rw [hright]
                ring

/- Book JSON key_lemmas.Lemma_2_FTL_BTL_potential. -/
theorem Lemma_2_FTL_BTL_potential {T d : Nat}
    (g : Fin T → Fin d → ℝ) (M H : Fin (T + 1) → SquareMatrix d)
    (Phi : SquareMatrix d → ℝ)
    (hM : ∀ t : Fin (T + 1),
      M t = ∑ s : Fin T, if s.1 < t.1 then vectorOuter (g s) else 0)
    (hHpd : ∀ t : Fin (T + 1), (H t).PosDef)
    (hMin : ∀ t : Fin (T + 1), ∀ K : SquareMatrix d, K.PosDef →
      matrixTrace (M t * (H t)⁻¹) + Phi (H t) ≤ matrixTrace (M t * K⁻¹) + Phi K) :
    ∑ t : Fin T, dualQuadraticForm (g t) (H (nextIndex t)) ≤
      ∑ t : Fin T, dualQuadraticForm (g t) (H ⟨T, Nat.lt_succ_self T⟩) +
        Phi (H ⟨T, Nat.lt_succ_self T⟩) - Phi (H ⟨0, Nat.succ_pos T⟩) := by
  classical
  have hPrefixMin :
      ∀ N : Fin (T + 1), ∀ K : SquareMatrix d, K.PosDef →
        (∑ s : Fin T, if s.1 < N.1 then dualQuadraticForm (g s) (H N) else 0) +
            Phi (H N) ≤
          (∑ s : Fin T, if s.1 < N.1 then dualQuadraticForm (g s) K else 0) +
            Phi K := by
    intro N K hK
    simpa [matrixTrace, dualQuadraticForm] using
      (SOptLib.prefix_dualQuadratic_objective_le_of_trace_inverse_minimizer
        (g := g) (A := M N) (H := H N) (K := K) (Phi := Phi) (N := N)
        (hA := by simpa [vectorOuter, Matrix.vecMulVec] using hM N)
        (hmin := hMin N K hK))
  have hBTL := ftl_btl_prefix_induction_nat g H Phi hHpd hPrefixMin T le_rfl
  have hBTL' :
      (∑ t : Fin T, dualQuadraticForm (g t) (H (nextIndex t))) +
          Phi (H ⟨0, Nat.succ_pos T⟩) ≤
        (∑ t : Fin T, dualQuadraticForm (g t) (H ⟨T, Nat.lt_succ_self T⟩)) +
          Phi (H ⟨T, Nat.lt_succ_self T⟩) := by
    simpa [fin_prefix_sum_final] using hBTL
  linarith

private theorem dualQuadraticForm_eq_genericTrace_vectorOuter_mul_inv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℝ) (K : GenericSquare ι) (hK : K.PosDef) :
    dualQuadraticForm g K = genericTrace (vectorOuter g * K⁻¹) := by
  simpa [dualQuadraticForm, genericTrace, vectorOuter, Matrix.vecMulVec] using
    SOptLib.finiteMatrixDualQuadraticForm_eq_trace_vecMulVec_mul_inv
      (g := g) (K := K)

private theorem prefix_objective_eq_genericTrace_objective {T : Nat}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Fin T → ι → ℝ) (M : Fin (T + 1) → GenericSquare ι)
    (Phi : GenericSquare ι → ℝ)
    (hM : ∀ t : Fin (T + 1),
      M t = ∑ s : Fin T, if s.1 < t.1 then vectorOuter (g s) else 0)
    (N : Fin (T + 1)) (K : GenericSquare ι) (hK : K.PosDef) :
    genericTrace (M N * K⁻¹) + Phi K =
      (∑ s : Fin T, if s.1 < N.1 then dualQuadraticForm (g s) K else 0) +
        Phi K := by
  simpa [genericTrace, vectorOuter, Matrix.vecMulVec, dualQuadraticForm] using
    (SOptLib.trace_prefix_outer_sum_mul_inv_add_eq_sum_dualQuadraticForm_add
      (g := g) (A := M N) (N := N)
      (hA := by
        simpa [vectorOuter, Matrix.vecMulVec] using hM N)
      (K := K) (c := Phi K))

private theorem prefix_minimizer_inequality_generic {T : Nat}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Fin T → ι → ℝ) (M H : Fin (T + 1) → GenericSquare ι)
    (Phi : GenericSquare ι → ℝ)
    (hM : ∀ t : Fin (T + 1),
      M t = ∑ s : Fin T, if s.1 < t.1 then vectorOuter (g s) else 0)
    (hHpd : ∀ t : Fin (T + 1), (H t).PosDef)
    (hMin : ∀ t : Fin (T + 1), ∀ K : GenericSquare ι, K.PosDef →
      genericTrace (M t * (H t)⁻¹) + Phi (H t) ≤ genericTrace (M t * K⁻¹) + Phi K)
    (N : Fin (T + 1)) (K : GenericSquare ι) (hK : K.PosDef) :
    (∑ s : Fin T, if s.1 < N.1 then dualQuadraticForm (g s) (H N) else 0) +
        Phi (H N) ≤
      (∑ s : Fin T, if s.1 < N.1 then dualQuadraticForm (g s) K else 0) +
        Phi K := by
  simpa [genericTrace, dualQuadraticForm] using
    (SOptLib.prefix_dualQuadratic_objective_le_of_trace_inverse_minimizer
      (g := g) (A := M N) (H := H N) (K := K) (Phi := Phi) (N := N)
      (hA := by simpa [vectorOuter, Matrix.vecMulVec] using hM N)
      (hmin := hMin N K hK))

private theorem ftl_btl_prefix_induction_generic {T : Nat}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Fin T → ι → ℝ) (H : Fin (T + 1) → GenericSquare ι)
    (Phi : GenericSquare ι → ℝ)
    (hHpd : ∀ t : Fin (T + 1), (H t).PosDef)
    (hPrefixMin : ∀ N : Fin (T + 1), ∀ K : GenericSquare ι, K.PosDef →
      (∑ s : Fin T, if s.1 < N.1 then dualQuadraticForm (g s) (H N) else 0) +
          Phi (H N) ≤
        (∑ s : Fin T, if s.1 < N.1 then dualQuadraticForm (g s) K else 0) +
          Phi K) :
    ∀ n : Nat, ∀ hn : n ≤ T,
      (∑ s : Fin T, if s.1 < n then dualQuadraticForm (g s) (H (nextIndex s)) else 0) +
          Phi (H ⟨0, Nat.succ_pos T⟩) ≤
        (∑ s : Fin T,
            if s.1 < n then
              dualQuadraticForm (g s) (H ⟨n, Nat.lt_succ_of_le hn⟩)
            else 0) +
          Phi (H ⟨n, Nat.lt_succ_of_le hn⟩) := by
  classical
  intro n
  induction n with
  | zero =>
      intro hn
      simp
  | succ n ih =>
      intro hn
      have hnT : n < T := Nat.lt_of_succ_le hn
      let N : Fin (T + 1) := ⟨n, Nat.lt_succ_of_le (Nat.le_of_lt hnT)⟩
      let Nnext : Fin (T + 1) := ⟨n + 1, Nat.lt_succ_of_le hn⟩
      let idx : Fin T := ⟨n, hnT⟩
      have ihN :
          (∑ s : Fin T, if s.1 < n then dualQuadraticForm (g s) (H (nextIndex s)) else 0) +
              Phi (H ⟨0, Nat.succ_pos T⟩) ≤
            (∑ s : Fin T,
                if s.1 < n then dualQuadraticForm (g s) (H N) else 0) +
              Phi (H N) := by
        simpa [N] using ih (Nat.le_of_lt hnT)
      have hminN :
          (∑ s : Fin T, if s.1 < n then dualQuadraticForm (g s) (H N) else 0) +
              Phi (H N) ≤
            (∑ s : Fin T, if s.1 < n then dualQuadraticForm (g s) (H Nnext) else 0) +
              Phi (H Nnext) := by
        simpa [N] using hPrefixMin N (H Nnext) (hHpd Nnext)
      have hchain :
          (∑ s : Fin T, if s.1 < n then dualQuadraticForm (g s) (H (nextIndex s)) else 0) +
              Phi (H ⟨0, Nat.succ_pos T⟩) ≤
            (∑ s : Fin T, if s.1 < n then dualQuadraticForm (g s) (H Nnext) else 0) +
              Phi (H Nnext) :=
        le_trans ihN hminN
      have hleft :=
        fin_prefix_sum_succ
          (fun s : Fin T => dualQuadraticForm (g s) (H (nextIndex s))) hnT
      have hright :=
        fin_prefix_sum_succ
          (fun s : Fin T => dualQuadraticForm (g s) (H Nnext)) hnT
      have hnext : nextIndex idx = Nnext := by
        ext
        rfl
      have hterm :
          dualQuadraticForm (g idx) (H (nextIndex idx)) =
            dualQuadraticForm (g idx) (H Nnext) := by
        rw [hnext]
      have hstep := add_le_add_right hchain (dualQuadraticForm (g idx) (H Nnext))
      calc
        (∑ s : Fin T,
            if s.1 < n + 1 then dualQuadraticForm (g s) (H (nextIndex s)) else 0) +
            Phi (H ⟨0, Nat.succ_pos T⟩)
            = ((∑ s : Fin T,
                if s.1 < n then dualQuadraticForm (g s) (H (nextIndex s)) else 0) +
                Phi (H ⟨0, Nat.succ_pos T⟩)) +
              dualQuadraticForm (g idx) (H Nnext) := by
                rw [hleft]
                rw [hterm]
                ring
        _ ≤ ((∑ s : Fin T,
                if s.1 < n then dualQuadraticForm (g s) (H Nnext) else 0) +
                Phi (H Nnext)) +
              dualQuadraticForm (g idx) (H Nnext) := by
                linarith
        _ = (∑ s : Fin T,
              if s.1 < n + 1 then dualQuadraticForm (g s) (H Nnext) else 0) +
              Phi (H Nnext) := by
                rw [hright]
                ring

private theorem Lemma_2_FTL_BTL_potential_generic {T : Nat}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Fin T → ι → ℝ) (M H : Fin (T + 1) → GenericSquare ι)
    (Phi : GenericSquare ι → ℝ)
    (hM : ∀ t : Fin (T + 1),
      M t = ∑ s : Fin T, if s.1 < t.1 then vectorOuter (g s) else 0)
    (hHpd : ∀ t : Fin (T + 1), (H t).PosDef)
    (hMin : ∀ t : Fin (T + 1), ∀ K : GenericSquare ι, K.PosDef →
      genericTrace (M t * (H t)⁻¹) + Phi (H t) ≤ genericTrace (M t * K⁻¹) + Phi K) :
    ∑ t : Fin T, dualQuadraticForm (g t) (H (nextIndex t)) ≤
      ∑ t : Fin T, dualQuadraticForm (g t) (H ⟨T, Nat.lt_succ_self T⟩) +
        Phi (H ⟨T, Nat.lt_succ_self T⟩) - Phi (H ⟨0, Nat.succ_pos T⟩) := by
  simpa [nextIndex] using
    (sum_cost_le_terminal_cost_add_potential_sub_of_prefix_minimizers
      (cost := fun t K => dualQuadraticForm (g t) K) (leader := H)
      (potential := Phi) (admissible := fun K : GenericSquare ι => K.PosDef)
      hHpd (fun N K hK => prefix_minimizer_inequality_generic g M H Phi hM hHpd hMin N K hK))

/- Book JSON key_lemmas.Lemma_3_kron_calculus. -/
/- Source discrepancy note: Lemma 3(iv) is printed as unconditional
   monotonicity of Kronecker products under Loewner order.  The scalar
   case A = B = 0 and A' = B' = -1 satisfies A' <= A and B' <= B but
   gives A' ⊗ B' = 1 not <= 0 = A ⊗ B.  The PSD lower-factor
   hypotheses below are the minimal domain correction used by the
   accumulator chain.  The theorem immediately below formalizes the
   counterexample for the retired unqualified statement. -/
theorem Lemma_3_iv_kron_order_preserving_unqualified_false :
    ¬ (∀ (A A' : SquareMatrix 1) (B B' : SquareMatrix 1),
      A' ≤ A → B' ≤ B → A' ⊗ₖ B' ≤ A ⊗ₖ B) := by
  intro h
  let Z : SquareMatrix 1 := 0
  let N : SquareMatrix 1 := fun _ _ => (-1 : ℝ)
  have hNleZ : N ≤ Z := by
    rw [Matrix.le_iff]
    have hdiag : (Matrix.diagonal (fun _ : Fin 1 => (1 : ℝ))).PosSemidef := by
      apply Matrix.PosSemidef.diagonal
      intro i
      norm_num
    convert hdiag using 1
    ext i j
    fin_cases i
    fin_cases j
    norm_num [Z, N, Matrix.diagonal]
  have hbad : N ⊗ₖ N ≤ Z ⊗ₖ Z := h Z N Z N hNleZ hNleZ
  rw [Matrix.le_iff] at hbad
  have hdiag :=
    Matrix.PosSemidef.diag_nonneg hbad (i := ((0 : Fin 1), (0 : Fin 1)))
  norm_num [Z, N, Matrix.kroneckerMap_apply] at hdiag

theorem Lemma_3_iv_kron_order_preserving {m n : Nat}
    (A A' : SquareMatrix m) (B B' : SquareMatrix n)
    (hA' : A'.PosSemidef) (hB' : B'.PosSemidef)
    (hAA' : A' ≤ A) (hBB' : B' ≤ B) :
    A' ⊗ₖ B' ≤ A ⊗ₖ B := by
  exact Matrix.kronecker_mono_of_posSemidef_of_le
    A' A B' B hA' hB' hAA' hBB'

theorem Lemma_3_iv_kron_psd {m n : Nat}
    (A : SquareMatrix m) (B : SquareMatrix n)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A ⊗ₖ B).PosSemidef := by
  exact hA.kronecker hB

theorem Lemma_3_vi_rank_one_vectorization {m n : Nat}
    (u : Fin m → ℝ) (v : Fin n → ℝ) :
    matrixVec (matrixOuter u v) = Function.uncurry (Matrix.vecMulVec u v) := by
  rfl

theorem Lemma_3_kron_calculus_order_component {m n : Nat}
    (A A' : SquareMatrix m) (B B' : SquareMatrix n)
    (hA' : A'.PosSemidef) (hB' : B'.PosSemidef)
    (hAA' : A' ≤ A) (hBB' : B' ≤ B) :
    A' ⊗ₖ B' ≤ A ⊗ₖ B := by
  exact Lemma_3_iv_kron_order_preserving A A' B B' hA' hB' hAA' hBB'

private theorem genericTrace_kronecker {m n : Nat}
    (A : SquareMatrix m) (B : SquareMatrix n) :
    genericTrace (A ⊗ₖ B) = matrixTrace A * matrixTrace B := by
  unfold genericTrace matrixTrace
  simpa using (Matrix.trace_kronecker A B)

private theorem kronecker_diagonal_power_rewrite {m n : Nat}
    (lam : Fin m → ℝ) (mu : Fin n → ℝ) (s : ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hmu : ∀ j, 0 ≤ mu j) :
    Matrix.diagonal (fun ij : Fin m × Fin n => (lam ij.1 * mu ij.2) ^ s) =
      Matrix.diagonal (fun i : Fin m => (lam i) ^ s) ⊗ₖ
        Matrix.diagonal (fun j : Fin n => (mu j) ^ s) := by
  exact TensorsProofSupport.Matrix.diagonal_rpow_mul_eq_kronecker_diagonal_rpow
    lam mu s hlam hmu

private theorem psd_spectral_triple {n : Nat} (A : SquareMatrix n)
    (hA : A.PosSemidef) :
    A = (hA.1.eigenvectorUnitary : SquareMatrix n) *
        Matrix.diagonal (fun i : Fin n => hA.1.eigenvalues i) *
        star (hA.1.eigenvectorUnitary : SquareMatrix n) := by
  simpa [Unitary.conjStarAlgAut_apply, Function.comp_def] using hA.1.spectral_theorem

private theorem star_kronecker_real {m n : Nat}
    (A : SquareMatrix m) (B : SquareMatrix n) :
    star (A ⊗ₖ B) = star A ⊗ₖ star B := by
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose]

private theorem kronecker_unitary_diagonalization_for_psd {m n : Nat}
    (A : SquareMatrix m) (B : SquareMatrix n)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    A ⊗ₖ B =
      ((hA.1.eigenvectorUnitary : SquareMatrix m) ⊗ₖ
          (hB.1.eigenvectorUnitary : SquareMatrix n)) *
        Matrix.diagonal
          (fun ij : Fin m × Fin n => hA.1.eigenvalues ij.1 * hB.1.eigenvalues ij.2) *
        star
          ((hA.1.eigenvectorUnitary : SquareMatrix m) ⊗ₖ
            (hB.1.eigenvectorUnitary : SquareMatrix n)) := by
  simpa using
    TensorsProofSupport.Matrix.IsHermitian.kronecker_spectral_decomposition
      A B hA.1 hB.1


private theorem psdMatrixPower_reindexAlgEquiv {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (A : GenericSquare ι) (s : ℝ) (hA : A.PosSemidef)
    (hA' : (Matrix.reindexAlgEquiv ℝ ℝ e A).PosSemidef) :
    Matrix.reindexAlgEquiv ℝ ℝ e (psdMatrixPower A s hA) =
      psdMatrixPower (Matrix.reindexAlgEquiv ℝ ℝ e A) s hA' := by
  simpa only [psdMatrixPower_eq_cfc] using
    Matrix.reindexAlgEquiv_cfc_rpow e A s hA.1

private theorem pdMatrixPower_congr {n : Nat}
    {A B : SquareMatrix n} (hAB : A = B) (s : ℝ)
    (hA : A.PosDef) (hB : B.PosDef) :
    pdMatrixPower A s hA = pdMatrixPower B s hB := by
  subst B
  congr

private theorem matrix_le_reindexAlgEquiv_iff {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (A C : GenericSquare ι) :
    A ≤ C ↔
      Matrix.reindexAlgEquiv ℝ ℝ e A ≤ Matrix.reindexAlgEquiv ℝ ℝ e C := by
  rw [Matrix.le_iff, Matrix.le_iff]
  rw [← map_sub]
  simpa [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply] using
    (Matrix.posSemidef_submatrix_equiv (M := C - A) e.symm).symm

private theorem orderedMatrixProductNat_reindexAlgEquiv {q m n : Nat}
    (e : Fin m ≃ Fin n) (X : Fin q → SquareMatrix m) :
    ∀ a : Nat,
      orderedMatrixProductNat (fun i : Fin q => Matrix.reindexAlgEquiv ℝ ℝ e (X i)) a =
        Matrix.reindexAlgEquiv ℝ ℝ e (orderedMatrixProductNat X a) := by
  intro a
  induction a with
  | zero =>
      simp [orderedMatrixProductNat]
  | succ a ih =>
      by_cases ha : a < q
      · simp only [orderedMatrixProductNat, ha, dif_pos]
        rw [ih, Matrix.reindexAlgEquiv_mul]
      · simp only [orderedMatrixProductNat, ha, dif_neg]
        exact ih

private theorem orderedMatrixProduct_reindexAlgEquiv {q m n : Nat}
    (e : Fin m ≃ Fin n) (X : Fin q → SquareMatrix m) :
    orderedMatrixProduct (fun i : Fin q => Matrix.reindexAlgEquiv ℝ ℝ e (X i)) =
      Matrix.reindexAlgEquiv ℝ ℝ e (orderedMatrixProduct X) := by
  simpa [orderedMatrixProduct] using
    orderedMatrixProductNat_reindexAlgEquiv (q := q) e X q

private theorem reindexAlgEquiv_smul_for_Lemma11 {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (c : ℝ) (A : GenericSquare ι) :
    Matrix.reindexAlgEquiv ℝ ℝ e (c • A) =
      c • Matrix.reindexAlgEquiv ℝ ℝ e A := by
  ext i j
  rfl

private theorem fin_univ_filter_lt_succ_prod_for_Lemma11 {q : Nat}
    (c : Fin q → ℝ) {a : Nat} (ha : a < q) :
    (∏ i ∈ (Finset.univ.filter (fun i : Fin q => i.1 < a + 1)), c i) =
      (∏ i ∈ (Finset.univ.filter (fun i : Fin q => i.1 < a)), c i) *
        c ⟨a, ha⟩ := by
  classical
  let ia : Fin q := ⟨a, ha⟩
  have hnot_mem : ia ∉ Finset.univ.filter (fun i : Fin q => i.1 < a) := by
    simp [ia]
  have hfilter :
      Finset.univ.filter (fun i : Fin q => i.1 < a + 1) =
        insert ia (Finset.univ.filter (fun i : Fin q => i.1 < a)) := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hi
      by_cases hlt : i.1 < a
      · exact Or.inr hlt
      · have hle : i.1 ≤ a := Nat.le_of_lt_succ hi
        have hge : a ≤ i.1 := Nat.le_of_not_gt hlt
        have hval : i.1 = a := le_antisymm hle hge
        exact Or.inl (Fin.ext hval)
    · intro hi
      rcases hi with hi | hi
      · subst i
        exact Nat.lt_succ_self a
      · exact Nat.lt_trans hi (Nat.lt_succ_self a)
  rw [hfilter, Finset.prod_insert hnot_mem]
  ring

private theorem matrix_smul_mul_smul_for_Lemma11 {n : Nat}
    (a b : ℝ) (A B : SquareMatrix n) :
    (a • A) * (b • B) = (a * b) • (A * B) := by
  ext i j
  simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]

private theorem orderedMatrixProductNat_smul_for_Lemma11 {q n : Nat}
    (c : Fin q → ℝ) (X : Fin q → SquareMatrix n) :
    ∀ a : Nat, a ≤ q →
      orderedMatrixProductNat (fun i : Fin q => c i • X i) a =
        (∏ i ∈ (Finset.univ.filter (fun i : Fin q => i.1 < a)), c i) •
          orderedMatrixProductNat X a := by
  intro a ha
  induction a with
  | zero =>
      simp [orderedMatrixProductNat]
  | succ a ih =>
      have hlt : a < q := Nat.lt_of_succ_le ha
      have hle : a ≤ q := Nat.le_of_succ_le ha
      calc
        orderedMatrixProductNat (fun i : Fin q => c i • X i) (a + 1) =
            orderedMatrixProductNat (fun i : Fin q => c i • X i) a *
              (c ⟨a, hlt⟩ • X ⟨a, hlt⟩) := by
              simp [orderedMatrixProductNat, hlt]
        _ =
            ((∏ i ∈ (Finset.univ.filter (fun i : Fin q => i.1 < a)), c i) •
                orderedMatrixProductNat X a) *
              (c ⟨a, hlt⟩ • X ⟨a, hlt⟩) := by
              rw [ih hle]
        _ =
            ((∏ i ∈ (Finset.univ.filter (fun i : Fin q => i.1 < a)), c i) *
                c ⟨a, hlt⟩) •
              (orderedMatrixProductNat X a * X ⟨a, hlt⟩) := by
              exact matrix_smul_mul_smul_for_Lemma11
                (∏ i ∈ (Finset.univ.filter (fun i : Fin q => i.1 < a)), c i)
                (c ⟨a, hlt⟩) (orderedMatrixProductNat X a) (X ⟨a, hlt⟩)
        _ =
            (∏ i ∈ (Finset.univ.filter (fun i : Fin q => i.1 < a + 1)), c i) •
              orderedMatrixProductNat X (a + 1) := by
              rw [fin_univ_filter_lt_succ_prod_for_Lemma11 c hlt]
              simp [orderedMatrixProductNat, hlt]

private theorem orderedMatrixProduct_smul_for_Lemma11 {q n : Nat}
    (c : Fin q → ℝ) (X : Fin q → SquareMatrix n) :
    orderedMatrixProduct (fun i : Fin q => c i • X i) =
      (∏ i : Fin q, c i) • orderedMatrixProduct X := by
  classical
  have h :=
    orderedMatrixProductNat_smul_for_Lemma11 (q := q) (n := n) c X q le_rfl
  have hfilter :
      Finset.univ.filter (fun i : Fin q => i.1 < q) = Finset.univ := by
    apply Finset.ext
    intro i
    simp [i.2]
  simpa [orderedMatrixProduct, hfilter] using h

private theorem polynomial_aeval_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam : ι → ℝ) (q : Polynomial ℝ) :
    Polynomial.aeval (Matrix.diagonal (fun i : ι => lam i) : GenericSquare ι) q =
      Matrix.diagonal (fun i : ι => q.eval (lam i)) := by
  simpa using TensorsProofSupport.Matrix.polynomial_aeval_diagonal lam q

private theorem cfc_rpow_diagonal_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam : ι → ℝ) (s : ℝ) (hlam : ∀ i, 0 ≤ lam i) :
    cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s)
        (Matrix.diagonal (fun i : ι => lam i) : GenericSquare ι) =
      Matrix.diagonal (fun i : ι => (lam i) ^ s) := by
  exact TensorsProofSupport.Matrix.cfc_rpow_diagonal lam s

private theorem matrixPower_diagonal_nonneg {n : Nat}
    (d : Fin n → ℝ) (s : ℝ) (hd : ∀ i, 0 ≤ d i)
    (hD : (Matrix.diagonal d : SquareMatrix n).PosSemidef) :
    matrixPower (Matrix.diagonal d : SquareMatrix n) s hD =
      Matrix.diagonal (fun i : Fin n => (d i) ^ s) := by
  classical
  unfold matrixPower
  rw [psdMatrixPower_eq_cfc]
  exact cfc_rpow_diagonal_nonneg d s hd

private theorem exists_diagonal_matrixPower_of_eq_diagonal {n : Nat}
    (A : SquareMatrix n) (s : ℝ) (hA : A.PosSemidef)
    (hAdiag : A = Matrix.diagonal (fun i : Fin n => A i i)) :
    ∃ d : Fin n → ℝ, matrixPower A s hA = Matrix.diagonal d := by
  classical
  let d : Fin n → ℝ := fun i => A i i
  let D : SquareMatrix n := Matrix.diagonal d
  have hd : ∀ i, 0 ≤ d i := by
    intro i
    exact Matrix.PosSemidef.diag_nonneg hA (i := i)
  have hDpsd : D.PosSemidef := by
    simpa [D] using Matrix.PosSemidef.diagonal (d := d) hd
  have hcongr : matrixPower A s hA = matrixPower D s hDpsd := by
    unfold matrixPower
    exact psdMatrixPower_congr (by simpa [D, d] using hAdiag) s hA hDpsd
  refine ⟨fun i : Fin n => (d i) ^ s, ?_⟩
  exact hcongr.trans (by simpa [D] using matrixPower_diagonal_nonneg d s hd hDpsd)

private theorem kronecker_eq_diagonal_diag_of_exists_diagonal {m n : Nat}
    (A : SquareMatrix m) (B : SquareMatrix n)
    (hA : ∃ d : Fin m → ℝ, A = Matrix.diagonal d)
    (hB : ∃ d : Fin n → ℝ, B = Matrix.diagonal d) :
    A ⊗ₖ B =
      Matrix.diagonal (fun ij : FlatMatrixIndex m n => (A ⊗ₖ B) ij ij) := by
  classical
  rcases hA with ⟨a, rfl⟩
  rcases hB with ⟨b, rfl⟩
  ext ij kl
  by_cases h : ij = kl
  · subst kl
    simp [Matrix.kroneckerMap_apply]
  · have hnot : ¬ (ij.1 = kl.1 ∧ ij.2 = kl.2) := by
      intro hp
      exact h (Prod.ext hp.1 hp.2)
    by_cases h1 : ij.1 = kl.1
    · have h2 : ij.2 ≠ kl.2 := by
        intro h2
        exact hnot ⟨h1, h2⟩
      simp [Matrix.kroneckerMap_apply, Matrix.diagonal_apply, h, h1, h2]
    · simp [Matrix.kroneckerMap_apply, Matrix.diagonal_apply, h, h1]

private theorem matrix_sub_eq_diagonal_diag_of_eq_diagonal_diag {ι : Type*}
    [Fintype ι] [DecidableEq ι] (A B : GenericSquare ι)
    (hA : A = Matrix.diagonal (fun i : ι => A i i))
    (hB : B = Matrix.diagonal (fun i : ι => B i i)) :
    A - B = Matrix.diagonal (fun i : ι => (A - B) i i) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · have hAij : A i j = 0 := by
      have h := congr_fun (congr_fun hA i) j
      simpa [Matrix.diagonal_apply, hij] using h
    have hBij : B i j = 0 := by
      have h := congr_fun (congr_fun hB i) j
      simpa [Matrix.diagonal_apply, hij] using h
    simp [Matrix.diagonal_apply, hij, hAij, hBij]

private theorem cfc_unitary_conj {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ℝ → ℝ) (U : unitary (GenericSquare ι)) (D : GenericSquare ι)
    (hD : IsSelfAdjoint D) :
    cfc (R := ℝ) (p := IsSelfAdjoint) f
        (((U : GenericSquare ι) * D) * star (U : GenericSquare ι)) =
      ((U : GenericSquare ι) *
          cfc (R := ℝ) (p := IsSelfAdjoint) f D) *
        star (U : GenericSquare ι) := by
  exact TensorsProofSupport.Matrix.cfc_unitary_conj f U D hD

private theorem cfc_rpow_eq_of_unitary_diagonalization {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (C : GenericSquare ι) (s : ℝ) (hC : C.PosSemidef)
    (U : unitary (GenericSquare ι)) (lam : ι → ℝ)
    (hdiag : C = (U : GenericSquare ι) *
        Matrix.diagonal (fun i : ι => lam i) * star (U : GenericSquare ι))
    (hlam : ∀ i, 0 ≤ lam i) :
    cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s) C =
      (U : GenericSquare ι) * Matrix.diagonal (fun i : ι => (lam i) ^ s) *
        star (U : GenericSquare ι) := by
  exact TensorsProofSupport.Matrix.cfc_rpow_eq_of_unitary_diagonalization C s U lam hdiag

private theorem psdMatrixPower_eq_of_unitary_diagonalization {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (C : GenericSquare ι) (s : ℝ) (hC : C.PosSemidef)
    (U : unitary (GenericSquare ι)) (lam : ι → ℝ)
    (hdiag : C = (U : GenericSquare ι) *
        Matrix.diagonal (fun i : ι => lam i) * star (U : GenericSquare ι))
    (hlam : ∀ i, 0 ≤ lam i) :
    psdMatrixPower C s hC =
      (U : GenericSquare ι) * Matrix.diagonal (fun i : ι => (lam i) ^ s) *
        star (U : GenericSquare ι) := by
  classical
  calc
    psdMatrixPower C s hC =
        cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s) C := by
          rw [psdMatrixPower_eq_cfc C s hC]
    _ = (U : GenericSquare ι) * Matrix.diagonal (fun i : ι => (lam i) ^ s) *
        star (U : GenericSquare ι) := by
          exact cfc_rpow_eq_of_unitary_diagonalization C s hC U lam hdiag hlam

private theorem psdMatrixPower_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : GenericSquare ι) (s : ℝ) (hC : C.PosSemidef) :
    (psdMatrixPower C s hC).PosSemidef := by
  classical
  let U : unitary (GenericSquare ι) := hC.1.eigenvectorUnitary
  let lam : ι → ℝ := hC.1.eigenvalues
  have hdiag : C = (U : GenericSquare ι) *
      Matrix.diagonal (fun i : ι => lam i) * star (U : GenericSquare ι) := by
    simpa [U, lam, Unitary.conjStarAlgAut_apply, Function.comp_def] using
      hC.1.spectral_theorem
  have hpow :
      psdMatrixPower C s hC =
        (U : GenericSquare ι) * Matrix.diagonal (fun i : ι => (lam i) ^ s) *
          star (U : GenericSquare ι) := by
    exact psdMatrixPower_eq_of_unitary_diagonalization C s hC U lam hdiag
      (fun i => hC.eigenvalues_nonneg i)
  have hdiag_psd :
      (Matrix.diagonal (fun i : ι => (lam i) ^ s) : GenericSquare ι).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    exact Real.rpow_nonneg (hC.eigenvalues_nonneg i) s
  have hUunit : IsUnit (U : GenericSquare ι) := (Unitary.toUnits U).isUnit
  rw [hpow]
  exact (Matrix.IsUnit.posSemidef_star_right_conjugate_iff hUunit).mpr hdiag_psd

private theorem matrixPower_posSemidef {n : Nat}
    (C : SquareMatrix n) (s : ℝ) (hC : C.PosSemidef) :
    (matrixPower C s hC).PosSemidef := by
  simpa [matrixPower] using psdMatrixPower_posSemidef C s hC

private theorem transpose_eq_self_of_posSemidef {n : Nat}
    (C : SquareMatrix n) (hC : C.PosSemidef) :
    C.transpose = C := by
  have hstar : star C = C := hC.1.eq
  ext i j
  have hij := congrFun (congrFun hstar j) i
  simpa [Matrix.star_apply] using hij.symm

private theorem matrixPower_transpose_eq_self {n : Nat}
    (C : SquareMatrix n) (s : ℝ) (hC : C.PosSemidef) :
    (matrixPower C s hC).transpose = matrixPower C s hC := by
  exact transpose_eq_self_of_posSemidef
    (matrixPower C s hC) (matrixPower_posSemidef C s hC)

private theorem psdMatrixPower_posDef_of_posDef_pos_exp {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (C : GenericSquare ι) (s : ℝ) (hC : C.PosDef) (hs : 0 < s) :
    (psdMatrixPower C s hC.posSemidef).PosDef := by
  classical
  let hCpsd : C.PosSemidef := hC.posSemidef
  let U : unitary (GenericSquare ι) := hCpsd.1.eigenvectorUnitary
  let lam : ι → ℝ := hCpsd.1.eigenvalues
  have hdiag : C = (U : GenericSquare ι) *
      Matrix.diagonal (fun i : ι => lam i) * star (U : GenericSquare ι) := by
    simpa [U, lam, hCpsd, Unitary.conjStarAlgAut_apply, Function.comp_def] using
      hCpsd.1.spectral_theorem
  have hpow :
      psdMatrixPower C s hC.posSemidef =
        (U : GenericSquare ι) * Matrix.diagonal (fun i : ι => (lam i) ^ s) *
          star (U : GenericSquare ι) := by
    exact psdMatrixPower_eq_of_unitary_diagonalization C s hC.posSemidef U lam hdiag
      (fun i => hC.posSemidef.eigenvalues_nonneg i)
  have hdiag_pd :
      (Matrix.diagonal (fun i : ι => (lam i) ^ s) : GenericSquare ι).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    exact Real.rpow_pos_of_pos (by simpa [hCpsd, lam] using hC.eigenvalues_pos i) s
  have hUunit : IsUnit (U : GenericSquare ι) := (Unitary.toUnits U).isUnit
  rw [hpow]
  exact (Matrix.IsUnit.posDef_star_right_conjugate_iff hUunit).mpr hdiag_pd

private theorem matrixPower_posDef_of_posDef_pos_exp {n : Nat}
    (C : SquareMatrix n) (s : ℝ) (hC : C.PosDef) (hCpsd : C.PosSemidef)
    (hs : 0 < s) :
    (matrixPower C s hCpsd).PosDef := by
  have hpow :
      matrixPower C s hCpsd = psdMatrixPower C s hC.posSemidef := by
    simp [matrixPower]
  rw [hpow]
  exact psdMatrixPower_posDef_of_posDef_pos_exp C s hC hs

private theorem psdMatrixPower_neg_half_eq_inv_psdMatrixPower_half {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (C : GenericSquare ι) (hCpd : C.PosDef) :
    psdMatrixPower C (-(1 / 2 : ℝ)) hCpd.posSemidef =
      (psdMatrixPower C (1 / 2 : ℝ) hCpd.posSemidef)⁻¹ := by
  classical
  let Root : GenericSquare ι := psdMatrixPower C (1 / 2 : ℝ) hCpd.posSemidef
  let Neg : GenericSquare ι := psdMatrixPower C (-(1 / 2 : ℝ)) hCpd.posSemidef
  have hRoot_pd : Root.PosDef := by
    exact psdMatrixPower_posDef_of_posDef_pos_exp C (1 / 2 : ℝ) hCpd (by norm_num)
  have hmul : Neg * Root = 1 := by
    let U : unitary (GenericSquare ι) := hCpd.posSemidef.1.eigenvectorUnitary
    let lam : ι → ℝ := hCpd.posSemidef.1.eigenvalues
    let Dneg : GenericSquare ι := Matrix.diagonal (fun i : ι => (lam i) ^ (-(1 / 2 : ℝ)))
    let Droot : GenericSquare ι := Matrix.diagonal (fun i : ι => (lam i) ^ (1 / 2 : ℝ))
    have hdiag : C = (U : GenericSquare ι) *
        Matrix.diagonal (fun i : ι => lam i) * star (U : GenericSquare ι) := by
      simpa [U, lam, Unitary.conjStarAlgAut_apply, Function.comp_def] using
        hCpd.posSemidef.1.spectral_theorem
    have hneg :
        Neg = (U : GenericSquare ι) * Dneg * star (U : GenericSquare ι) := by
      simpa [Neg, U, lam, Dneg] using
        psdMatrixPower_eq_of_unitary_diagonalization C (-(1 / 2 : ℝ))
          hCpd.posSemidef U lam hdiag
          (fun i => hCpd.posSemidef.eigenvalues_nonneg i)
    have hroot :
        Root = (U : GenericSquare ι) * Droot * star (U : GenericSquare ι) := by
      simpa [Root, U, lam, Droot] using
        psdMatrixPower_eq_of_unitary_diagonalization C (1 / 2 : ℝ)
          hCpd.posSemidef U lam hdiag
          (fun i => hCpd.posSemidef.eigenvalues_nonneg i)
    have hDmul : Dneg * Droot = 1 := by
      ext i j
      by_cases hij : i = j
      · subst j
        have hpos : 0 < lam i := by
          simpa [lam] using hCpd.eigenvalues_pos i
        have hpow :
            (lam i) ^ (-(1 / 2 : ℝ)) * (lam i) ^ (1 / 2 : ℝ) = 1 := by
          calc
            (lam i) ^ (-(1 / 2 : ℝ)) * (lam i) ^ (1 / 2 : ℝ) =
                (lam i) ^ (-(1 / 2 : ℝ) + (1 / 2 : ℝ)) := by
                  rw [Real.rpow_add hpos]
            _ = 1 := by norm_num [Real.rpow_zero]
        simpa [Dneg, Droot, Matrix.diagonal_mul_diagonal] using hpow
      · simp [Dneg, Droot, Matrix.diagonal_mul_diagonal, hij]
    calc
      Neg * Root =
          ((U : GenericSquare ι) * Dneg * star (U : GenericSquare ι)) *
            ((U : GenericSquare ι) * Droot * star (U : GenericSquare ι)) := by
            rw [hneg, hroot]
      _ = (U : GenericSquare ι) *
            (Dneg * (star (U : GenericSquare ι) * (U : GenericSquare ι)) * Droot) *
            star (U : GenericSquare ι) := by
            noncomm_ring
      _ = (U : GenericSquare ι) * 1 * star (U : GenericSquare ι) := by
            simp [Unitary.coe_star_mul_self, hDmul, mul_assoc]
      _ = 1 := by
            simp [Unitary.coe_mul_star_self]
  have hdet_ne : Root.det ≠ 0 := ne_of_gt hRoot_pd.det_pos
  letI : Invertible Root.det := invertibleOfNonzero hdet_ne
  letI : Invertible Root := Matrix.invertibleOfDetInvertible Root
  calc
    psdMatrixPower C (-(1 / 2 : ℝ)) hCpd.posSemidef = Neg := by rfl
    _ = Neg * 1 := by simp
    _ = Neg * (Root * Root⁻¹) := by rw [Matrix.mul_inv_of_invertible]
    _ = (Neg * Root) * Root⁻¹ := by noncomm_ring
    _ = Root⁻¹ := by rw [hmul]; simp
    _ = (psdMatrixPower C (1 / 2 : ℝ) hCpd.posSemidef)⁻¹ := by rfl

private theorem pdMatrixPower_neg_quarter_eq_inv_matrixPower_quarter {n : Nat}
    (C : SquareMatrix n) (hCpd : C.PosDef) (hCpsd : C.PosSemidef) :
    pdMatrixPower C (-(1 / 4 : ℝ)) hCpd =
      (matrixPower C (1 / 4 : ℝ) hCpsd)⁻¹ := by
  classical
  have hroot_congr :
      matrixPower C (1 / 4 : ℝ) hCpsd =
        matrixPower C (1 / 4 : ℝ) hCpd.posSemidef := by
    simpa [matrixPower] using
      (psdMatrixPower_congr (A := C) (B := C) rfl (1 / 4 : ℝ)
        hCpsd hCpd.posSemidef)
  rw [hroot_congr]
  let Root : SquareMatrix n := matrixPower C (1 / 4 : ℝ) hCpd.posSemidef
  let Neg : SquareMatrix n := pdMatrixPower C (-(1 / 4 : ℝ)) hCpd
  have hRoot_pd : Root.PosDef := by
    exact matrixPower_posDef_of_posDef_pos_exp C (1 / 4 : ℝ) hCpd hCpd.posSemidef
      (by norm_num)
  have hmul : Neg * Root = 1 := by
    let U : unitary (SquareMatrix n) := hCpd.posSemidef.1.eigenvectorUnitary
    let lam : Fin n → ℝ := hCpd.posSemidef.1.eigenvalues
    let Dneg : SquareMatrix n := Matrix.diagonal (fun i : Fin n => (lam i) ^ (-(1 / 4 : ℝ)))
    let Droot : SquareMatrix n := Matrix.diagonal (fun i : Fin n => (lam i) ^ (1 / 4 : ℝ))
    have hdiag : C = (U : SquareMatrix n) *
        Matrix.diagonal (fun i : Fin n => lam i) * star (U : SquareMatrix n) := by
      simpa [U, lam, Unitary.conjStarAlgAut_apply, Function.comp_def] using
        hCpd.posSemidef.1.spectral_theorem
    have hneg :
        Neg = (U : SquareMatrix n) * Dneg * star (U : SquareMatrix n) := by
      simpa [Neg, pdMatrixPower, matrixPower, U, lam, Dneg] using
        psdMatrixPower_eq_of_unitary_diagonalization C (-(1 / 4 : ℝ))
          hCpd.posSemidef U lam hdiag
          (fun i => hCpd.posSemidef.eigenvalues_nonneg i)
    have hroot :
        Root = (U : SquareMatrix n) * Droot * star (U : SquareMatrix n) := by
      simpa [Root, matrixPower, U, lam, Droot] using
        psdMatrixPower_eq_of_unitary_diagonalization C (1 / 4 : ℝ)
          hCpd.posSemidef U lam hdiag
          (fun i => hCpd.posSemidef.eigenvalues_nonneg i)
    have hDmul : Dneg * Droot = 1 := by
      ext i j
      by_cases hij : i = j
      · subst j
        have hpos : 0 < lam i := by
          simpa [lam] using hCpd.eigenvalues_pos i
        have hpow :
            (lam i) ^ (-(1 / 4 : ℝ)) * (lam i) ^ (1 / 4 : ℝ) = 1 := by
          calc
            (lam i) ^ (-(1 / 4 : ℝ)) * (lam i) ^ (1 / 4 : ℝ) =
                (lam i) ^ (-(1 / 4 : ℝ) + (1 / 4 : ℝ)) := by
                  rw [Real.rpow_add hpos]
            _ = 1 := by norm_num [Real.rpow_zero]
        simpa [Dneg, Droot, Matrix.diagonal_mul_diagonal] using hpow
      · simp [Dneg, Droot, Matrix.diagonal_mul_diagonal, hij]
    calc
      Neg * Root =
          ((U : SquareMatrix n) * Dneg * star (U : SquareMatrix n)) *
            ((U : SquareMatrix n) * Droot * star (U : SquareMatrix n)) := by
            rw [hneg, hroot]
      _ = (U : SquareMatrix n) *
            (Dneg * (star (U : SquareMatrix n) * (U : SquareMatrix n)) * Droot) *
            star (U : SquareMatrix n) := by
            noncomm_ring
      _ = (U : SquareMatrix n) * 1 * star (U : SquareMatrix n) := by
            simp [Unitary.coe_star_mul_self, hDmul, mul_assoc]
      _ = 1 := by
            simp [Unitary.coe_mul_star_self]
  have hdet_ne : Root.det ≠ 0 := ne_of_gt hRoot_pd.det_pos
  letI : Invertible Root.det := invertibleOfNonzero hdet_ne
  letI : Invertible Root := Matrix.invertibleOfDetInvertible Root
  calc
    pdMatrixPower C (-(1 / 4 : ℝ)) hCpd = Neg := by rfl
    _ = Neg * 1 := by simp
    _ = Neg * (Root * Root⁻¹) := by rw [Matrix.mul_inv_of_invertible]
    _ = (Neg * Root) * Root⁻¹ := by noncomm_ring
    _ = Root⁻¹ := by rw [hmul]; simp
    _ = (matrixPower C (1 / 4 : ℝ) hCpd.posSemidef)⁻¹ := by rfl

private theorem psdMatrixPower_half_mul_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : GenericSquare ι) (hC : C.PosSemidef) :
    psdMatrixPower C (1 / 2 : ℝ) hC *
        psdMatrixPower C (1 / 2 : ℝ) hC = C := by
  classical
  let U : unitary (GenericSquare ι) := hC.1.eigenvectorUnitary
  let lam : ι → ℝ := hC.1.eigenvalues
  let D : GenericSquare ι := Matrix.diagonal (fun i : ι => lam i)
  let Dh : GenericSquare ι := Matrix.diagonal (fun i : ι => (lam i) ^ (1 / 2 : ℝ))
  have hdiag : C = (U : GenericSquare ι) * D * star (U : GenericSquare ι) := by
    simpa [U, D, lam, Unitary.conjStarAlgAut_apply, Function.comp_def] using
      hC.1.spectral_theorem
  have hpow :
      psdMatrixPower C (1 / 2 : ℝ) hC =
        (U : GenericSquare ι) * Dh * star (U : GenericSquare ι) := by
    simpa [U, Dh, lam] using
      psdMatrixPower_eq_of_unitary_diagonalization C (1 / 2 : ℝ) hC U lam
        (by simpa [U, D, lam] using hdiag)
        (fun i => hC.eigenvalues_nonneg i)
  have hDh : Dh * Dh = D := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Dh, D, Matrix.diagonal_mul_diagonal]
      rw [← Real.rpow_add_of_nonneg
        (show 0 ≤ lam i by simpa [lam] using hC.eigenvalues_nonneg i)
        (show 0 ≤ (2⁻¹ : ℝ) by norm_num) (show 0 ≤ (2⁻¹ : ℝ) by norm_num)]
      norm_num [Real.rpow_one]
    · simp [Dh, D, Matrix.diagonal_mul_diagonal, hij]
  calc
    psdMatrixPower C (1 / 2 : ℝ) hC *
        psdMatrixPower C (1 / 2 : ℝ) hC =
        ((U : GenericSquare ι) * Dh * star (U : GenericSquare ι)) *
          ((U : GenericSquare ι) * Dh * star (U : GenericSquare ι)) := by
          rw [hpow]
    _ = (U : GenericSquare ι) * D * star (U : GenericSquare ι) := by
          calc
            ((U : GenericSquare ι) * Dh * star (U : GenericSquare ι)) *
                ((U : GenericSquare ι) * Dh * star (U : GenericSquare ι)) =
                (U : GenericSquare ι) *
                  (Dh * (star (U : GenericSquare ι) * (U : GenericSquare ι)) * Dh) *
                  star (U : GenericSquare ι) := by
                  noncomm_ring
            _ = (U : GenericSquare ι) * D * star (U : GenericSquare ι) := by
                  simp [mul_assoc, Unitary.coe_star_mul_self, hDh]
    _ = C := hdiag.symm

/- Mathlib's Loewner--Heinz theorem is stated for complex C⋆-algebras.  Real
   matrices carry the same positive cone, so we transport the paper's real
   spectral power through the canonical entrywise embedding into complex
   `CStarMatrix`, apply `CFC.monotone_rpow`, and reflect positivity back. -/
noncomputable section

/- Make the real self-adjoint functional calculus on complex C⋆ matrices
   explicit.  Batch elaboration can infer this instance through the generic
   restriction-of-scalars construction, but naming it here also makes the
   source route stable under the project's incremental/LSP checker. -/
@[reducible] private noncomputable def complexCStarMatrixRealCFC {n : Nat} :
    ContinuousFunctionalCalculus ℝ (CStarMatrix (Fin n) (Fin n) ℂ)
      IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

@[reducible] private noncomputable def complexCStarMatrixNonnegSpectrum {n : Nat} :
    NonnegSpectrumClass ℝ (CStarMatrix (Fin n) (Fin n) ℂ) :=
  CStarAlgebra.instNonnegSpectrumClass

private noncomputable def complexMatrixRpow {n : Nat}
    (A : CStarMatrix (Fin n) (Fin n) ℂ) (alpha : ℝ) :
    CStarMatrix (Fin n) (Fin n) ℂ := by
  letI hCFC : ContinuousFunctionalCalculus ℝ
      (CStarMatrix (Fin n) (Fin n) ℂ) IsSelfAdjoint :=
    complexCStarMatrixRealCFC (n := n)
  letI hNS : NonnegSpectrumClass ℝ (CStarMatrix (Fin n) (Fin n) ℂ) :=
    complexCStarMatrixNonnegSpectrum (n := n)
  exact @CFC.rpow _ inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance hCFC hNS A alpha

private theorem complexMatrixRpow_mono {n : Nat}
    (A B : CStarMatrix (Fin n) (Fin n) ℂ) (alpha : ℝ)
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1) (hAB : A ≤ B) :
    complexMatrixRpow A alpha ≤ complexMatrixRpow B alpha := by
  letI hCFC : ContinuousFunctionalCalculus ℝ
      (CStarMatrix (Fin n) (Fin n) ℂ) IsSelfAdjoint :=
    complexCStarMatrixRealCFC (n := n)
  letI hNS : NonnegSpectrumClass ℝ (CStarMatrix (Fin n) (Fin n) ℂ) :=
    complexCStarMatrixNonnegSpectrum (n := n)
  simpa only [complexMatrixRpow] using
    (CFC.monotone_rpow ⟨halpha0, halpha1⟩ hAB)

private def realToComplexStarAlgHom : ℝ →⋆ₐ[ℝ] ℂ where
  toFun r := (r : ℂ)
  map_one' := Complex.ofReal_one
  map_mul' := Complex.ofReal_mul
  map_zero' := Complex.ofReal_zero
  map_add' := Complex.ofReal_add
  commutes' := fun _ => rfl
  map_star' := fun r => by simp

private noncomputable def realMatrixCastStarAlgHom {n : Nat} :
    SquareMatrix n →⋆ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  StarAlgHom.mk (AlgHom.mapMatrix realToComplexStarAlgHom.toAlgHom)
    (by
      intro A
      change Matrix.map (star A) realToComplexStarAlgHom =
        star (Matrix.map A realToComplexStarAlgHom)
      ext i j
      simp [realToComplexStarAlgHom, Matrix.star_eq_conjTranspose])

private noncomputable def realMatrixComplexification {n : Nat} :
    SquareMatrix n →⋆ₐ[ℝ] CStarMatrix (Fin n) (Fin n) ℂ :=
  let e : Matrix (Fin n) (Fin n) ℂ ≃⋆ₐ[ℝ] CStarMatrix (Fin n) (Fin n) ℂ :=
    (CStarMatrix.ofMatrixStarAlgEquiv (n := Fin n) (A := ℂ)).restrictScalars ℝ
  StarAlgHom.mk
    (e.toAlgEquiv.toAlgHom.comp realMatrixCastStarAlgHom.toAlgHom)
    (by
      intro A
      change e (realMatrixCastStarAlgHom (star A)) =
        star (e (realMatrixCastStarAlgHom A))
      rw [map_star realMatrixCastStarAlgHom, map_star e])

private theorem starAlgHom_nonneg_of_nonneg
    {R A B : Type*} [CommSemiring R]
    [NonUnitalSemiring A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
    [NonUnitalSemiring B] [PartialOrder B] [StarRing B] [StarOrderedRing B]
    [Module R A] [Module R B]
    (f : A →⋆ₙₐ[R] B) {a : A} (ha : 0 ≤ a) : 0 ≤ f a := by
  rw [StarOrderedRing.nonneg_iff] at ha ⊢
  induction ha using AddSubmonoid.closure_induction with
  | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      exact AddSubmonoid.subset_closure ⟨f s, by rw [map_mul, map_star]⟩
  | zero => simpa using (AddSubmonoid.zero_mem
      (AddSubmonoid.closure (Set.range fun s : B => star s * s)))
  | add x y _hx _hy ihx ihy =>
      simpa using AddSubmonoid.add_mem
        (AddSubmonoid.closure (Set.range fun s : B => star s * s)) ihx ihy

private theorem starAlgHom_mono_of_le
    {R A B : Type*} [CommRing R]
    [Ring A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
    [Ring B] [PartialOrder B] [StarRing B] [StarOrderedRing B]
    [Algebra R A] [Algebra R B]
    (f : A →⋆ₐ[R] B) {a b : A} (hab : a ≤ b) : f a ≤ f b := by
  rw [← sub_nonneg, ← map_sub]
  exact starAlgHom_nonneg_of_nonneg f.toNonUnitalStarAlgHom (sub_nonneg.mpr hab)

private theorem starAlgEquiv_le_iff
    {R A B : Type*} [CommRing R]
    [Ring A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
    [Ring B] [PartialOrder B] [StarRing B] [StarOrderedRing B]
    [Algebra R A] [Algebra R B]
    (e : A ≃⋆ₐ[R] B) (a b : A) : e a ≤ e b ↔ a ≤ b := by
  constructor
  · intro h
    simpa using starAlgHom_mono_of_le
      (StarAlgHom.mk e.symm.toAlgEquiv.toAlgHom
        (fun x => by simpa using map_star e.symm x)) h
  · exact starAlgHom_mono_of_le
      (StarAlgHom.mk e.toAlgEquiv.toAlgHom
        (fun x => by simpa using map_star e x))

private theorem realMatrixComplexification_nonneg_iff {n : Nat}
    (A : SquareMatrix n) : 0 ≤ realMatrixComplexification A ↔ 0 ≤ A := by
  let e : Matrix (Fin n) (Fin n) ℂ ≃⋆ₐ[ℝ] CStarMatrix (Fin n) (Fin n) ℂ :=
    (CStarMatrix.ofMatrixStarAlgEquiv (n := Fin n) (A := ℂ)).restrictScalars ℝ
  let castA : Matrix (Fin n) (Fin n) ℂ := Matrix.map A realToComplexStarAlgHom
  have hcomplexify : realMatrixComplexification A = e castA := by rfl
  rw [hcomplexify]
  change e 0 ≤ e castA ↔ 0 ≤ A
  rw [starAlgEquiv_le_iff e 0 castA]
  constructor
  · intro hcast
    have hcast_psd : castA.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hcast
    rw [Matrix.nonneg_iff_posSemidef]
    constructor
    · apply Matrix.IsHermitian.ext
      intro i j
      apply Complex.ofReal_injective
      simpa [castA, realToComplexStarAlgHom] using hcast_psd.1.apply i j
    · intro v
      let vc : Fin n →₀ ℂ :=
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
          castA, realToComplexStarAlgHom, Complex.star_def, Matrix.map_apply,
          StarAlgHom.coe_mk, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
          OneHom.coe_mk]
        push_cast
        simp [Finsupp.mapRange_apply, realToComplexStarAlgHom]
      rw [heq] at hv
      exact (Complex.nonneg_iff.mp hv).1
  · intro hA
    exact starAlgHom_nonneg_of_nonneg
      realMatrixCastStarAlgHom.toNonUnitalStarAlgHom hA

private theorem continuous_realMatrixComplexification {n : Nat} :
    Continuous (realMatrixComplexification (n := n)) := by
  simpa only [realMatrixComplexification, realMatrixCastStarAlgHom,
    realToComplexStarAlgHom, SOptLib.realMatrixComplexification] using
      (SOptLib.continuous_realMatrixComplexification (ι := Fin n))

private theorem squareMatrix_le_of_tendsto_of_tendsto {n : Nat} {Z : Type*}
    {l : Filter Z} [l.NeBot] (f g : Z → SquareMatrix n) (A B : SquareMatrix n)
    (hf : Filter.Tendsto f l (nhds A)) (hg : Filter.Tendsto g l (nhds B))
    (hfg : Filter.Eventually (fun z => f z ≤ g z) l) : A ≤ B := by
  exact TensorsProofSupport.Matrix.le_of_tendsto_of_tendsto f g A B hf hg hfg

private theorem realMatrixComplexification_matrixPower {n : Nat}
    (A : SquareMatrix n) (alpha : ℝ) (hA : A.PosSemidef) :
    realMatrixComplexification (matrixPower A alpha hA) =
      complexMatrixRpow (realMatrixComplexification A) alpha := by
  letI hCFC : ContinuousFunctionalCalculus ℝ
      (CStarMatrix (Fin n) (Fin n) ℂ) IsSelfAdjoint :=
    complexCStarMatrixRealCFC (n := n)
  letI hNS : NonnegSpectrumClass ℝ (CStarMatrix (Fin n) (Fin n) ℂ) :=
    complexCStarMatrixNonnegSpectrum (n := n)
  letI hSemi : IsSemitopologicalRing (CStarMatrix (Fin n) (Fin n) ℂ) :=
    inferInstance
  letI hT2 : T2Space (CStarMatrix (Fin n) (Fin n) ℂ) := inferInstance
  have hnonneg : 0 ≤ realMatrixComplexification A :=
    (realMatrixComplexification_nonneg_iff A).2 hA.nonneg
  have hrpow_eq :
      complexMatrixRpow (realMatrixComplexification A) alpha =
        cfc (fun x : ℝ => x ^ alpha) (realMatrixComplexification A) := by
    rw [complexMatrixRpow]
    exact @CFC.rpow_eq_cfc_real _ inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance hCFC hNS hSemi hT2
      (realMatrixComplexification A) alpha hnonneg
  change realMatrixComplexification (psdMatrixPower A alpha hA) = _
  rw [hrpow_eq, psdMatrixPower_eq_cfc A alpha hA]
  have hf : ContinuousOn (fun x : ℝ => x ^ alpha) (spectrum ℝ A) := by
    have hfin : (spectrum ℝ A).Finite := by
      rw [hA.1.spectrum_real_eq_range_eigenvalues]
      exact Set.finite_range _
    exact hfin.continuousOn _
  exact realMatrixComplexification.map_cfc (fun x : ℝ => x ^ alpha) A
    (hf := hf)
    (hφ := by
      have hcast : Continuous (realMatrixCastStarAlgHom (n := n)) :=
        by
          apply continuous_pi
          intro i
          apply continuous_pi
          intro j
          change Continuous (fun M : SquareMatrix n => (M i j : ℂ))
          fun_prop
      change Continuous (fun M : SquareMatrix n =>
        CStarMatrix.ofMatrix (realMatrixCastStarAlgHom M))
      exact CStarMatrix.uniformEmbedding_ofMatrix.isUniformInducing.isInducing.continuous.comp
        hcast)
    (ha := hA.1)
    (hφa := by
      calc
        star (realMatrixComplexification A) =
            realMatrixComplexification (star A) :=
          (map_star realMatrixComplexification A).symm
        _ = realMatrixComplexification A := by
          change realMatrixComplexification A.transpose = realMatrixComplexification A
          exact congrArg realMatrixComplexification hA.1)

private theorem matrixPower_mono_independent {n : Nat}
    (A B : SquareMatrix n) (alpha : ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hAB : A ≤ B)
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1) :
    matrixPower A alpha hA ≤ matrixPower B alpha hB := by
  letI hCFC : ContinuousFunctionalCalculus ℝ
      (CStarMatrix (Fin n) (Fin n) ℂ) IsSelfAdjoint :=
    complexCStarMatrixRealCFC (n := n)
  letI hNS : NonnegSpectrumClass ℝ (CStarMatrix (Fin n) (Fin n) ℂ) :=
    complexCStarMatrixNonnegSpectrum (n := n)
  have hcomplex_order :
      realMatrixComplexification A ≤ realMatrixComplexification B := by
    apply sub_nonneg.mp
    rw [← map_sub, realMatrixComplexification_nonneg_iff]
    exact sub_nonneg.mpr hAB
  have hcomplex_power :
      complexMatrixRpow (realMatrixComplexification A) alpha ≤
        complexMatrixRpow (realMatrixComplexification B) alpha := by
    exact complexMatrixRpow_mono _ _ alpha halpha0 halpha1 hcomplex_order
  have himage_power :
      realMatrixComplexification (matrixPower A alpha hA) ≤
        realMatrixComplexification (matrixPower B alpha hB) := by
    simpa [realMatrixComplexification_matrixPower] using hcomplex_power
  rw [Matrix.le_iff]
  apply Matrix.nonneg_iff_posSemidef.mp
  apply (realMatrixComplexification_nonneg_iff
    (matrixPower B alpha hB - matrixPower A alpha hA)).mp
  rw [map_sub]
  exact sub_nonneg.mpr himage_power

end

private theorem orderedMatrixProductNat_const_eq_pow {q n : Nat}
    (B : SquareMatrix n) :
    ∀ a : Nat, a ≤ q →
      orderedMatrixProductNat (fun _ : Fin q => B) a = B ^ a := by
  intro a
  induction a with
  | zero =>
      intro _ha
      simp [orderedMatrixProductNat]
  | succ a ih =>
      intro ha
      have hlt : a < q := Nat.lt_of_succ_le ha
      have hle : a ≤ q := Nat.le_of_succ_le ha
      simp [orderedMatrixProductNat, hlt, ih hle, pow_succ]

private theorem orderedMatrixProduct_const_eq_pow {q n : Nat}
    (B : SquareMatrix n) :
    orderedMatrixProduct (fun _ : Fin q => B) = B ^ q := by
  simpa [orderedMatrixProduct] using
    orderedMatrixProductNat_const_eq_pow (q := q) (n := n) B q (le_rfl)

private theorem diagonal_pow_eq_diagonal_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) :
    ∀ q : Nat,
      (Matrix.diagonal d : GenericSquare ι) ^ q =
        Matrix.diagonal (fun i : ι => d i ^ q) := by
  intro q
  induction q with
  | zero =>
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
  | succ q ih =>
      calc
        (Matrix.diagonal d : GenericSquare ι) ^ (q + 1) =
            Matrix.diagonal (fun i : ι => d i ^ q) * Matrix.diagonal d := by
              rw [pow_succ, ih]
        _ = Matrix.diagonal (fun i : ι => d i ^ (q + 1)) := by
              ext i j
              by_cases hij : i = j
              · subst j
                simp [Matrix.diagonal_mul_diagonal, pow_succ]
              · simp [Matrix.diagonal_mul_diagonal, hij]

private theorem psdMatrixPower_inv_natCast_pow_eq_self {ι : Type*}
    [Fintype ι] [DecidableEq ι] {q : Nat} (hq : 0 < q)
    (C : GenericSquare ι) (hC : C.PosSemidef) :
    (psdMatrixPower C (1 / (q : ℝ)) hC) ^ q = C := by
  classical
  let U : unitary (GenericSquare ι) := hC.1.eigenvectorUnitary
  let lam : ι → ℝ := hC.1.eigenvalues
  let D : GenericSquare ι := Matrix.diagonal (fun i : ι => lam i)
  let Droot : GenericSquare ι := Matrix.diagonal (fun i : ι => (lam i) ^ (1 / (q : ℝ)))
  have hdiag : C = (U : GenericSquare ι) * D * star (U : GenericSquare ι) := by
    simpa [U, D, lam, Unitary.conjStarAlgAut_apply, Function.comp_def] using
      hC.1.spectral_theorem
  have hpow :
      psdMatrixPower C (1 / (q : ℝ)) hC =
        (U : GenericSquare ι) * Droot * star (U : GenericSquare ι) := by
    simpa [U, Droot, lam] using
      psdMatrixPower_eq_of_unitary_diagonalization C (1 / (q : ℝ)) hC U lam
        (by simpa [U, D, lam] using hdiag)
        (fun i => hC.eigenvalues_nonneg i)
  have hconj_pow :
      ∀ a : Nat,
        (((U : GenericSquare ι) * Droot * star (U : GenericSquare ι)) ^ a) =
          (U : GenericSquare ι) * (Droot ^ a) * star (U : GenericSquare ι) := by
    intro a
    induction a with
    | zero =>
        simp [pow_zero, Unitary.coe_mul_star_self]
    | succ a ih =>
        calc
          (((U : GenericSquare ι) * Droot * star (U : GenericSquare ι)) ^ (a + 1)) =
              ((U : GenericSquare ι) * (Droot ^ a) * star (U : GenericSquare ι)) *
                ((U : GenericSquare ι) * Droot * star (U : GenericSquare ι)) := by
                rw [pow_succ, ih]
          _ = (U : GenericSquare ι) * (Droot ^ (a + 1)) * star (U : GenericSquare ι) := by
                calc
                  ((U : GenericSquare ι) * (Droot ^ a) * star (U : GenericSquare ι)) *
                      ((U : GenericSquare ι) * Droot * star (U : GenericSquare ι)) =
                    (U : GenericSquare ι) *
                      ((Droot ^ a) * (star (U : GenericSquare ι) *
                        (U : GenericSquare ι)) * Droot) *
                      star (U : GenericSquare ι) := by
                      noncomm_ring
                  _ = (U : GenericSquare ι) * (Droot ^ (a + 1)) *
                      star (U : GenericSquare ι) := by
                      simp [pow_succ, mul_assoc, Unitary.coe_star_mul_self]
  have hDroot_pow : Droot ^ q = D := by
    calc
      Droot ^ q =
          Matrix.diagonal (fun i : ι => ((lam i) ^ (1 / (q : ℝ))) ^ q) := by
            simpa [Droot] using diagonal_pow_eq_diagonal_pow
              (fun i : ι => (lam i) ^ (1 / (q : ℝ))) q
      _ = D := by
          ext i j
          by_cases hij : i = j
          · subst j
            have hroot :
                ((lam i) ^ (1 / (q : ℝ))) ^ q = lam i := by
              simpa [one_div, Real.rpow_one] using
                Real.rpow_inv_natCast_pow (hC.eigenvalues_nonneg i)
                  (by exact_mod_cast (ne_of_gt hq))
            simpa [D, one_div] using hroot
          · simp [D, hij]
  calc
    (psdMatrixPower C (1 / (q : ℝ)) hC) ^ q =
        (((U : GenericSquare ι) * Droot * star (U : GenericSquare ι)) ^ q) := by
          rw [hpow]
    _ = (U : GenericSquare ι) * (Droot ^ q) * star (U : GenericSquare ι) := by
          rw [hconj_pow q]
    _ = C := by
          rw [hDroot_pow]
          exact hdiag.symm

private theorem psdMatrixPower_smul_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c α : ℝ) (A : GenericSquare ι) (hA : A.PosSemidef) (hc : 0 ≤ c)
    (hcA : (c • A).PosSemidef) :
    psdMatrixPower (c • A) α hcA = c ^ α • psdMatrixPower A α hA := by
  simpa only [psdMatrixPower_eq_cfc] using
    TensorsProofSupport.Matrix.cfc_rpow_smul_of_nonneg c α A hA hc

private theorem orderedMatrixProduct_const_matrixPower_inv_card_eq_self {q n : Nat}
    [Nonempty (Fin q)] (M : SquareMatrix n) (hM : M.PosSemidef) :
    orderedMatrixProduct (fun _ : Fin q => matrixPower M (1 / (q : ℝ)) hM) = M := by
  classical
  have hq_pos : 0 < q := by
    let i : Fin q := Classical.choice inferInstance
    exact Nat.lt_of_le_of_lt (Nat.zero_le i.1) i.2
  calc
    orderedMatrixProduct (fun _ : Fin q => matrixPower M (1 / (q : ℝ)) hM) =
        (matrixPower M (1 / (q : ℝ)) hM) ^ q := by
          exact orderedMatrixProduct_const_eq_pow
            (q := q) (n := n) (matrixPower M (1 / (q : ℝ)) hM)
    _ = M := by
          simpa [matrixPower] using
            psdMatrixPower_inv_natCast_pow_eq_self (q := q) hq_pos M hM

private theorem psdMatrixPower_kronecker {m n : Nat}
    (A : SquareMatrix m) (B : SquareMatrix n) (s : ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    psdMatrixPower (A ⊗ₖ B) s (Lemma_3_iv_kron_psd A B hA hB) =
      matrixPower A s hA ⊗ₖ matrixPower B s hB := by
  simpa only [psdMatrixPower_eq_cfc, matrixPower] using
    TensorsProofSupport.Matrix.cfc_rpow_kronecker A B s hA hB

theorem Lemma_3_kron_calculus {m n : Nat}
    (A A' : SquareMatrix m) (B B' : SquareMatrix n)
    (s : ℝ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hA' : A'.PosSemidef) (hB' : B'.PosSemidef)
    (hAA' : A' ≤ A) (hBB' : B' ≤ B) :
    (A ⊗ₖ B) * (A' ⊗ₖ B') = (A * A') ⊗ₖ (B * B') ∧
      (A ⊗ₖ B).transpose = A.transpose ⊗ₖ B.transpose ∧
      psdMatrixPower (A ⊗ₖ B) s (Lemma_3_iv_kron_psd A B hA hB) =
        matrixPower A s hA ⊗ₖ matrixPower B s hB ∧
      A' ⊗ₖ B' ≤ A ⊗ₖ B ∧
      (A ⊗ₖ B).PosSemidef ∧
      genericTrace (A ⊗ₖ B) = matrixTrace A * matrixTrace B ∧
      ∀ (u : Fin m → ℝ) (v : Fin n → ℝ),
        matrixVec (matrixOuter u v) = Function.uncurry (Matrix.vecMulVec u v) := by
  classical
  constructor
  · simpa using (Matrix.mul_kronecker_mul A A' B B').symm
  constructor
  · simpa using (Matrix.kroneckerMap_transpose (fun x y : ℝ => x * y) A B).symm
  constructor
  · exact psdMatrixPower_kronecker A B s hA hB
  constructor
  · exact Lemma_3_iv_kron_order_preserving A A' B B' hA' hB' hAA' hBB'
  constructor
  · exact Lemma_3_iv_kron_psd A B hA hB
  constructor
  · exact genericTrace_kronecker A B
  · intro u v
    exact Lemma_3_vi_rank_one_vectorization u v

/- Book JSON key_lemmas.Lemma_4_matrix_kron_vec. -/
theorem Lemma_4_matrix_kron_vec {m n : Nat}
    (G : MatrixSpace m n) (L : SquareMatrix m) (R : SquareMatrix n) :
    (L ⊗ₖ R.transpose).mulVec (matrixVec G) = matrixVec (L * G * R) := by
  classical
  ext ij
  rcases ij with ⟨i, j⟩
  simp [Matrix.mulVec, matrixVec, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.transpose_apply, dotProduct, Finset.sum_mul]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  rw [Finset.sum_comm]
  simp [mul_left_comm, mul_comm]

private theorem kron_inverse_mulVec_matrixVec_pd_neg_quarter {m n : Nat}
    (G : MatrixSpace m n) (L : SquareMatrix m) (R : SquareMatrix n)
    (hLpd : L.PosDef) (hRpd : R.PosDef)
    (hLpsd : L.PosSemidef) (hRpsd : R.PosSemidef) :
    ((((matrixPower L (1 / 4 : ℝ) hLpsd) ⊗ₖ
        (matrixPower R (1 / 4 : ℝ) hRpsd))⁻¹).mulVec (matrixVec G)) =
      matrixVec (pdMatrixPower L (-(1 / 4 : ℝ)) hLpd * G *
        pdMatrixPower R (-(1 / 4 : ℝ)) hRpd) := by
  classical
  let Lq : SquareMatrix m := matrixPower L (1 / 4 : ℝ) hLpsd
  let Rq : SquareMatrix n := matrixPower R (1 / 4 : ℝ) hRpsd
  let Lneg : SquareMatrix m := pdMatrixPower L (-(1 / 4 : ℝ)) hLpd
  let Rneg : SquareMatrix n := pdMatrixPower R (-(1 / 4 : ℝ)) hRpd
  have hLinv : Lneg = Lq⁻¹ := by
    simpa [Lq, Lneg] using
      pdMatrixPower_neg_quarter_eq_inv_matrixPower_quarter L hLpd hLpsd
  have hRinv : Rneg = Rq⁻¹ := by
    simpa [Rq, Rneg] using
      pdMatrixPower_neg_quarter_eq_inv_matrixPower_quarter R hRpd hRpsd
  have hRneg_symm : Rneg.transpose = Rneg := by
    have hRneg_psd : Rneg.PosSemidef := by
      simpa [Rneg, pdMatrixPower] using
        matrixPower_posSemidef R (-(1 / 4 : ℝ)) hRpd.posSemidef
    exact transpose_eq_self_of_posSemidef Rneg hRneg_psd
  calc
    ((((matrixPower L (1 / 4 : ℝ) hLpsd) ⊗ₖ
        (matrixPower R (1 / 4 : ℝ) hRpsd))⁻¹).mulVec (matrixVec G)) =
        ((Lq⁻¹ ⊗ₖ Rq⁻¹).mulVec (matrixVec G)) := by
          simp [Lq, Rq, Matrix.inv_kronecker]
    _ = ((Lneg ⊗ₖ Rneg).mulVec (matrixVec G)) := by
          rw [hLinv, hRinv]
    _ = ((Lneg ⊗ₖ Rneg.transpose).mulVec (matrixVec G)) := by
          rw [hRneg_symm]
    _ = matrixVec (Lneg * G * Rneg) := by
          exact Lemma_4_matrix_kron_vec G Lneg Rneg
    _ = matrixVec (pdMatrixPower L (-(1 / 4 : ℝ)) hLpd * G *
        pdMatrixPower R (-(1 / 4 : ℝ)) hRpd) := by
          simp [Lneg, Rneg]

/- A real spectral power preserves commutation.  This is the first structural
   step needed to regard the paper's ordered product as a positive weighted
   geometric mean, rather than as an arbitrary non-self-adjoint product. -/
private theorem matrixPower_comm_of_comm {n : Nat}
    (A B : SquareMatrix n) (a b : ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAB : A * B = B * A) :
    matrixPower A a hA * matrixPower B b hB =
      matrixPower B b hB * matrixPower A a hA := by
  rw [matrixPower, matrixPower, psdMatrixPower_eq_cfc A a hA,
    psdMatrixPower_eq_cfc B b hB]
  exact (((show Commute A B from hAB).cfc_real (fun x : ℝ => x ^ a)).symm.cfc_real
    (fun x : ℝ => x ^ b)).symm

/- The endpoint exponent is evaluated directly by the same CFC realization as
   `matrixPower`.  Keeping this before Lemma 5 lets the source theorem discharge
   the one-factor case without invoking the downstream Loewner theorem. -/
private theorem matrixPower_exponent_one {n : Nat}
    (A : SquareMatrix n) (hA : A.PosSemidef) :
    matrixPower A 1 hA = A := by
  rw [matrixPower, psdMatrixPower_eq_cfc A 1 hA]
  simpa only [Real.rpow_one] using
    (cfc_id' (R := ℝ) (p := IsSelfAdjoint) A hA.1)

private theorem matrixPower_exponent_zero {n : Nat}
    (A : SquareMatrix n) (hA : A.PosSemidef) :
    matrixPower A 0 hA = 1 := by
  rw [matrixPower_spectral_formula A 0 hA]
  simp [Real.rpow_zero, Matrix.mul_assoc]

/- Products of a finite pairwise-commuting PSD family are PSD.  The induction
   follows the paper's factor order exactly, so it can be consumed directly at
   the Lemma 5 boundary. -/
private theorem orderedMatrixProduct_posSemidef_of_pairwise_comm {q n : Nat}
    (A : Fin q → SquareMatrix n)
    (hA : ∀ i, (A i).PosSemidef)
    (hcomm : ∀ i j, A i * A j = A j * A i) :
    (orderedMatrixProduct A).PosSemidef := by
  rw [orderedMatrixProduct_eq_list_prod, ← Matrix.nonneg_iff_posSemidef]
  exact List.prod_nonneg_of_pairwise_commute (List.ofFn A)
    (List.forall_mem_ofFn_iff.mpr fun i ↦ (hA i).nonneg)
    (List.pairwise_ofFn.mpr fun _ _ _ ↦ hcomm _ _)

private theorem matrix_mul_le_mul_left_of_commute {n : Nat}
    (P A B : SquareMatrix n) (hP : P.PosSemidef) (hAB : A ≤ B)
    (hPA : Commute P A) (hPB : Commute P B) : P * A ≤ P * B := by
  exact mul_le_mul_left_of_nonneg_of_commute P A B hP.nonneg hAB hPA hPB

/- If each earlier lower factor commutes with each later upper factor,
   Loewner--Heinz can be multiplied factor by factor.  This triangular condition
   is weaker than total cross-family commutation, but remains a genuine strict
   subcase of Ando's theorem. -/
private theorem orderedMatrixProduct_mono_of_cross_commute {q n : Nat}
    (A B : Fin q → SquareMatrix n)
    (hA : ∀ i, (A i).PosSemidef) (hB : ∀ i, (B i).PosSemidef)
    (hAB : ∀ i, A i ≤ B i)
    (hAcomm : ∀ i j, A i * A j = A j * A i)
    (hBcomm : ∀ i j, B i * B j = B j * B i)
    (hcross : ∀ i j, i.1 < j.1 → A i * B j = B j * A i) :
    orderedMatrixProduct A ≤ orderedMatrixProduct B := by
  simpa only [orderedMatrixProduct_eq_list_prod] using
    (List.prod_ofFn_le_prod_ofFn_of_le_of_cross_commute A B
      (fun i ↦ (hA i).nonneg) hAB
      (fun i j ↦ hAcomm i j) (fun i j ↦ hBcomm i j)
      (fun i j hij ↦ hcross i j hij))

private theorem orderedMatrixProduct_two {n : Nat} (A : Fin 2 → SquareMatrix n) :
    orderedMatrixProduct A = A 0 * A 1 := by
  calc
    orderedMatrixProduct A = orderedMatrixProductNat A 2 := rfl
    _ = orderedMatrixProductNat A 1 * A 1 := rfl
    _ = A 0 * A 1 := by
      change (1 : SquareMatrix n) * A 0 * A 1 = A 0 * A 1
      rw [one_mul]

/- Inserting an identity factor preserves the paper's literal factor order.
   This is the reindexing bridge needed to interpret a zero weight by deleting
   its coordinate, rather than by extending the positive-weight integral
   formula to an undefined `1 / Gamma 0` endpoint. -/
private theorem orderedMatrixProductNat_cons {q n : Nat}
    (A0 : SquareMatrix n) (A : Fin q → SquareMatrix n) :
    ∀ a : Nat, a ≤ q →
      orderedMatrixProductNat (Fin.cons A0 A) (a + 1) =
        A0 * orderedMatrixProductNat A a := by
  intro a
  induction a with
  | zero =>
      intro _ha
      simp [orderedMatrixProductNat]
  | succ a ih =>
      intro ha
      have hlt : a < q := Nat.lt_of_succ_le ha
      have hlt' : a + 1 < q + 1 := Nat.succ_lt_succ hlt
      calc
        orderedMatrixProductNat (Fin.cons A0 A) (a + 1 + 1) =
            orderedMatrixProductNat (Fin.cons A0 A) (a + 1) *
              (Fin.cons A0 A : Fin (q + 1) → SquareMatrix n) ⟨a + 1, hlt'⟩ := by
                rw [orderedMatrixProductNat, dif_pos hlt']
        _ = (A0 * orderedMatrixProductNat A a) * A ⟨a, hlt⟩ := by
              rw [ih (Nat.le_of_succ_le ha)]
              rfl
        _ = A0 * (orderedMatrixProductNat A a * A ⟨a, hlt⟩) :=
              Matrix.mul_assoc _ _ _
        _ = A0 * orderedMatrixProductNat A (a + 1) := by
              rw [orderedMatrixProductNat, dif_pos hlt]

private theorem orderedMatrixProduct_cons {q n : Nat}
    (A0 : SquareMatrix n) (A : Fin q → SquareMatrix n) :
    orderedMatrixProduct (Fin.cons A0 A) = A0 * orderedMatrixProduct A := by
  exact orderedMatrixProductNat_cons A0 A q le_rfl

private theorem posDef_mul_of_commute {n : Nat}
    (A B : SquareMatrix n) (hA : A.PosDef) (hB : B.PosDef)
    (hAB : A * B = B * A) : (A * B).PosDef := by
  exact Matrix.isStrictlyPositive_iff_posDef.mp
    ((hA.isStrictlyPositive.commute_iff hB.isStrictlyPositive).mp hAB)

private theorem orderedMatrixProduct_posDef_of_pairwise_comm {q n : Nat}
    (A : Fin q → SquareMatrix n) (hA : ∀ i, (A i).PosDef)
    (hcomm : ∀ i j, A i * A j = A j * A i) :
    (orderedMatrixProduct A).PosDef := by
  rw [orderedMatrixProduct_eq_list_prod, ← Matrix.isStrictlyPositive_iff_posDef]
  exact TensorsProofSupport.List.prod_isStrictlyPositive_of_pairwise_commute (List.ofFn A)
    (List.forall_mem_ofFn_iff.mpr fun i ↦ (hA i).isStrictlyPositive)
    (List.pairwise_ofFn.mpr fun _ _ _ ↦ hcomm _ _)

/- The operator-norm scope supplies the normed-ring structure used only to
   expose the matrix exponential.  The equality remains about the canonical
   real CFC used by `positiveMatrixRpow`. -/
open scoped Matrix.Norms.Operator in
private theorem positiveMatrixRpow_eq_exp_log {n : Nat}
    (A : SquareMatrix n) (t : ℝ) (hA : A.PosDef) :
    positiveMatrixRpow A t = NormedSpace.exp (t • CFC.log A) := by
  simpa only [positiveMatrixRpow, ← CFC.rpow_eq_cfc_real hA.posSemidef.nonneg,
    CFC.rpow_eq_pow] using
      TensorsProofSupport.CFC.rpow_eq_exp_smul_log A t hA.isStrictlyPositive

open scoped Matrix.Norms.Operator in
private theorem cfc_log_mul_of_commute {n : Nat}
    (A B : SquareMatrix n) (hA : A.PosDef) (hB : B.PosDef)
    (hAB : A * B = B * A) :
    CFC.log (A * B) = CFC.log A + CFC.log B :=
  TensorsProofSupport.CFC.log_mul_of_commute
    A B hA.isStrictlyPositive hB.isStrictlyPositive hAB

open scoped Matrix.Norms.Operator in
private theorem positiveMatrixRpow_mul_of_commute {n : Nat}
    (A B : SquareMatrix n) (t : ℝ) (hA : A.PosDef) (hB : B.PosDef)
    (hAB : A * B = B * A) :
    positiveMatrixRpow (A * B) t =
      positiveMatrixRpow A t * positiveMatrixRpow B t := by
  simpa only [positiveMatrixRpow, CFC.rpow_eq_pow,
    CFC.rpow_eq_cfc_real
      ((hA.isStrictlyPositive.commute_iff hB.isStrictlyPositive).mp hAB).nonneg,
    CFC.rpow_eq_cfc_real hA.posSemidef.nonneg,
    CFC.rpow_eq_cfc_real hB.posSemidef.nonneg] using
    TensorsProofSupport.CFC.rpow_mul_of_commute
      A B t hA.isStrictlyPositive hB.isStrictlyPositive hAB

private theorem orderedMatrixProduct_commute_right {q n : Nat}
    (A : Fin q → SquareMatrix n) (B : SquareMatrix n)
    (hcomm : ∀ i, A i * B = B * A i) :
    orderedMatrixProduct A * B = B * orderedMatrixProduct A := by
  classical
  induction q with
  | zero =>
      simp [orderedMatrixProduct, orderedMatrixProductNat]
  | succ q ih =>
      obtain ⟨A0, A, rfl⟩ := Fin.exists_cons A
      have h0 : A0 * B = B * A0 := hcomm 0
      have htail : orderedMatrixProduct A * B = B * orderedMatrixProduct A :=
        ih A (fun i => hcomm i.succ)
      rw [orderedMatrixProduct_cons]
      calc
        (A0 * orderedMatrixProduct A) * B =
            A0 * (orderedMatrixProduct A * B) := by rw [mul_assoc]
        _ = A0 * (B * orderedMatrixProduct A) := by rw [htail]
        _ = (A0 * B) * orderedMatrixProduct A := by rw [mul_assoc]
        _ = (B * A0) * orderedMatrixProduct A := by rw [h0]
        _ = B * (A0 * orderedMatrixProduct A) := by rw [mul_assoc]

open scoped Matrix.Norms.Operator in
private theorem positiveMatrixRpow_orderedMatrixProduct {q n : Nat}
    (A : Fin q → SquareMatrix n) (t : ℝ)
    (hA : ∀ i, (A i).PosDef)
    (hcomm : ∀ i j, A i * A j = A j * A i) :
    positiveMatrixRpow (orderedMatrixProduct A) t =
      orderedMatrixProduct (fun i => positiveMatrixRpow (A i) t) := by
  have hpos : ∀ a ∈ List.ofFn A, IsStrictlyPositive a :=
    List.forall_mem_ofFn_iff.mpr fun i ↦ (hA i).isStrictlyPositive
  have hpair : (List.ofFn A).Pairwise Commute :=
    List.pairwise_ofFn.mpr fun _ _ _ ↦ hcomm _ _
  have hprod_pos : IsStrictlyPositive (List.ofFn A).prod :=
    TensorsProofSupport.List.prod_isStrictlyPositive_of_pairwise_commute
      (List.ofFn A) hpos hpair
  rw [orderedMatrixProduct_eq_list_prod, orderedMatrixProduct_eq_list_prod,
    positiveMatrixRpow, ← CFC.rpow_eq_cfc_real hprod_pos.nonneg]
  change CFC.rpow (List.ofFn A).prod t = _
  rw [TensorsProofSupport.CFC.rpow_list_prod_of_pairwise_commute
    (List.ofFn A) t hpos hpair]
  apply congrArg List.prod
  rw [List.ofFn_comp' A (fun a => positiveMatrixRpow a t)]
  apply List.map_congr_left
  intro a ha
  exact CFC.rpow_eq_cfc_real (hpos a ha).nonneg

open scoped Matrix.Norms.Operator in
private theorem positiveMatrixRpow_rpow {n : Nat}
    (A : SquareMatrix n) (u t : ℝ) (hA : A.PosDef) :
    positiveMatrixRpow (positiveMatrixRpow A u) t =
      positiveMatrixRpow A (t * u) := by
  have hAu : (positiveMatrixRpow A u).PosDef :=
    positiveMatrixRpow_posDef A _ hA
  rw [positiveMatrixRpow_eq_exp_log _ t hAu,
    positiveMatrixRpow_eq_exp_log A (t * u) hA,
    positiveMatrixRpow_eq_exp_log A u hA]
  rw [CFC.log_exp (u • CFC.log A)
    ((IsSelfAdjoint.all u).smul (IsSelfAdjoint.log (a := A)))]
  congr 1
  module

private theorem positiveMatrixRpow_rpow_neg_one {n : Nat}
    (A : SquareMatrix n) (t : ℝ) (hA : A.PosDef) :
    positiveMatrixRpow (positiveMatrixRpow A (-1 : ℝ)) t =
      positiveMatrixRpow A (-t) := by
  rw [positiveMatrixRpow_rpow A (-1 : ℝ) t hA]
  congr 1
  ring

private theorem binaryWeightedGeometricMean_eq_rpow_mul_of_commute {n : Nat}
    (A B : SquareMatrix n) (t : ℝ) (hA : A.PosDef) (hB : B.PosDef)
    (hAB : A * B = B * A) :
    binaryWeightedGeometricMean A B t =
      positiveMatrixRpow A (1 - t) * positiveMatrixRpow B t := by
  simpa only [binaryWeightedGeometricMean, positiveMatrixRpow, CFC.rpow_eq_pow,
    CFC.rpow_eq_cfc_real hA.posSemidef.nonneg,
    CFC.rpow_eq_cfc_real hB.posSemidef.nonneg] using
    Matrix.binaryWeightedGeometricMean_eq_rpow_mul_of_commute
      A B t hA hB (show Commute A B from hAB)

/- The sole non-analytic bridge still needed by the normalized finite-family
   induction: for a commuting positive-definite family, a binary mean of the
   first factor and the normalized tail evaluates to the original ordered
   product. -/
private theorem orderedMatrixProduct_eq_binaryMean_cons_normalized {q n : Nat}
    [Nonempty (Fin q)] (A : Fin (q + 1) → SquareMatrix n)
    (beta : Fin (q + 1) → ℝ) (hA : ∀ i, (A i).PosDef)
    (hcomm : ∀ i j, A i * A j = A j * A i)
    (hbeta : ∀ i, 0 < beta i) (hbeta_sum : (∑ i, beta i) = 1) :
    let s := ∑ i : Fin q, beta i.succ
    let P := orderedMatrixProduct (fun i : Fin q =>
      matrixPower (A i.succ) (beta i.succ / s) (hA i.succ).posSemidef)
    P.PosDef →
      orderedMatrixProduct (fun i : Fin (q + 1) =>
          matrixPower (A i) (beta i) (hA i).posSemidef) =
        binaryWeightedGeometricMean (A 0) P s := by
  dsimp only
  intro _hP
  have hrpow (i : Fin (q + 1)) (t : ℝ) :
      CFC.rpow (A i) t = matrixPower (A i) t (hA i).posSemidef := by
    rw [CFC.rpow_eq_pow,
      CFC.rpow_eq_cfc_real (hA i).posSemidef.nonneg]
    change positiveMatrixRpow (A i) t = _
    exact positiveMatrixRpow_eq_matrixPower (A i) t (hA i).posSemidef
  simpa only [orderedMatrixProduct_eq_list_prod, binaryWeightedGeometricMean,
    TensorsProofSupport.Matrix.binaryWeightedGeometricMean, hrpow] using
      TensorsProofSupport.Matrix.prod_rpow_eq_binaryWeightedGeometricMean_cons_normalized
        (q := q) A beta hA (fun i j => show Commute (A i) (A j) from hcomm i j)
          (fun i : Fin q => hbeta i.succ) hbeta_sum

private theorem orderedMatrixProduct_insertNth_one {q n : Nat}
    (p : Fin (q + 1)) (A : Fin q → SquareMatrix n) :
    orderedMatrixProduct (Fin.insertNth p (1 : SquareMatrix n) A) =
      orderedMatrixProduct A := by
  simpa only [orderedMatrixProduct_eq_list_prod] using
    List.prod_ofFn_insertNth_one p A

private theorem orderedMatrixProduct_delete_one {q n : Nat}
    (A : Fin (q + 1) → SquareMatrix n) (p : Fin (q + 1)) (hp : A p = 1) :
    orderedMatrixProduct A = orderedMatrixProduct (p.removeNth A) := by
  simpa only [orderedMatrixProduct_eq_list_prod] using
    TensorsProofSupport.List.prod_ofFn_removeNth_of_eq_one A p hp

private theorem orderedMatrixProduct_delete_zero_weight {q n : Nat}
    (A : Fin (q + 1) → SquareMatrix n) (alpha : Fin (q + 1) → ℝ)
    (hA : ∀ i, (A i).PosSemidef) (p : Fin (q + 1)) (hp : alpha p = 0) :
    orderedMatrixProduct
        (fun i => matrixPower (A i) (alpha i) (hA i)) =
      orderedMatrixProduct
        (fun j => matrixPower (A (p.succAbove j)) (alpha (p.succAbove j))
          (hA (p.succAbove j))) := by
  apply orderedMatrixProduct_delete_one _ p
  simpa [hp] using matrixPower_exponent_zero (A p) (hA p)

private theorem matrixPower_one {n : Nat} (beta : ℝ)
    (hI : (1 : SquareMatrix n).PosSemidef) :
    matrixPower (1 : SquareMatrix n) beta hI = 1 := by
  classical
  let U : unitary (SquareMatrix n) := (1 : unitary (SquareMatrix n))
  have hdiag : (1 : SquareMatrix n) =
      (U : SquareMatrix n) * Matrix.diagonal (fun _ : Fin n => (1 : ℝ)) *
        star (U : SquareMatrix n) := by
    simp [U]
  have hpow := psdMatrixPower_eq_of_unitary_diagonalization
    (C := (1 : SquareMatrix n)) beta hI U (fun _ : Fin n => (1 : ℝ)) hdiag
    (by intro i; norm_num)
  rw [matrixPower]
  calc
    psdMatrixPower (1 : SquareMatrix n) beta hI =
        (U : SquareMatrix n) * Matrix.diagonal (fun i : Fin n => ((1 : ℝ) ^ beta)) *
          star (U : SquareMatrix n) := hpow
    _ = 1 := by simp [U, Real.one_rpow]

/- Adding a nonnegative scalar multiple of the identity is the canonical
   positive-definite regularization used to extend the cited weighted mean to
   singular PSD inputs.  Keeping the proof argument in this definition avoids
   any total-inverse interpretation at the boundary. -/
private theorem matrix_add_nnnreal_one_posSemidef {n : Nat}
    (A : SquareMatrix n) (hA : A.PosSemidef) (ε : ℝ≥0) :
    (A + (ε : ℝ) • (1 : SquareMatrix n)).PosSemidef := by
  exact hA.add (Matrix.PosSemidef.one.smul ε.coe_nonneg)

private theorem matrix_add_nnnreal_one_posDef {n : Nat}
    (A : SquareMatrix n) (hA : A.PosSemidef) (ε : ℝ≥0) (hε : 0 < ε) :
    (A + (ε : ℝ) • (1 : SquareMatrix n)).PosDef := by
  exact Matrix.PosDef.posSemidef_add hA
    (Matrix.PosDef.one.smul (by exact_mod_cast hε))

private theorem matrix_add_nnnreal_one_diagonalization {n : Nat}
    (A : SquareMatrix n) (U : unitary (SquareMatrix n)) (lam : Fin n → ℝ)
    (hdiag : A = (U : SquareMatrix n) * Matrix.diagonal lam *
      star (U : SquareMatrix n)) (ε : ℝ≥0) :
    A + (ε : ℝ) • (1 : SquareMatrix n) =
      (U : SquareMatrix n) *
        Matrix.diagonal (fun i : Fin n => lam i + (ε : ℝ)) *
        star (U : SquareMatrix n) := by
  exact TensorsProofSupport.Matrix.add_smul_one_eq_unitary_diagonalization_add
    A U lam hdiag (ε : ℝ)

private theorem matrixPower_add_nnnreal_one_eq_fixed_diagonal {n : Nat}
    (A : SquareMatrix n) (alpha : ℝ) (hA : A.PosSemidef)
    (U : unitary (SquareMatrix n)) (lam : Fin n → ℝ)
    (hdiag : A = (U : SquareMatrix n) * Matrix.diagonal lam *
      star (U : SquareMatrix n)) (hlam : ∀ i, 0 ≤ lam i) (ε : ℝ≥0) :
    matrixPower (A + (ε : ℝ) • (1 : SquareMatrix n)) alpha
        (matrix_add_nnnreal_one_posSemidef A hA ε) =
      (U : SquareMatrix n) *
        Matrix.diagonal (fun i : Fin n => (lam i + (ε : ℝ)) ^ alpha) *
        star (U : SquareMatrix n) := by
  unfold matrixPower
  exact psdMatrixPower_eq_of_unitary_diagonalization
    (A + (ε : ℝ) • (1 : SquareMatrix n)) alpha
    (matrix_add_nnnreal_one_posSemidef A hA ε) U
    (fun i : Fin n => lam i + (ε : ℝ))
    (matrix_add_nnnreal_one_diagonalization A U lam hdiag ε)
    (fun i => add_nonneg (hlam i) ε.coe_nonneg)

/- Spectral real powers with nonnegative exponent are continuous under the
   paper's `A + ε I` regularization, including at singular `A`.  This is proved
   using the fixed spectral basis of `A`; it does not compare Mathlib's chosen
   eigenbases for the nearby matrices. -/
private theorem matrixPower_add_nnnreal_one_tendsto {n : Nat}
    (A : SquareMatrix n) (alpha : ℝ) (hA : A.PosSemidef) (halpha : 0 ≤ alpha) :
    Filter.Tendsto
      (fun ε : ℝ≥0 => matrixPower (A + (ε : ℝ) • (1 : SquareMatrix n)) alpha
        (matrix_add_nnnreal_one_posSemidef A hA ε))
      (nhds 0) (nhds (matrixPower A alpha hA)) := by
  classical
  let U : unitary (SquareMatrix n) := hA.1.eigenvectorUnitary
  let lam : Fin n → ℝ := hA.1.eigenvalues
  let D : SquareMatrix n := Matrix.diagonal lam
  have hdiag : A = (U : SquareMatrix n) * D * star (U : SquareMatrix n) := by
    simpa [U, D, lam, Unitary.conjStarAlgAut_apply, Function.comp_def] using
      hA.1.spectral_theorem
  have hpow : ∀ ε : ℝ≥0,
      matrixPower (A + (ε : ℝ) • (1 : SquareMatrix n)) alpha
          (matrix_add_nnnreal_one_posSemidef A hA ε) =
        (U : SquareMatrix n) *
          Matrix.diagonal (fun i : Fin n => (lam i + (ε : ℝ)) ^ alpha) *
          star (U : SquareMatrix n) := by
    intro ε
    exact matrixPower_add_nnnreal_one_eq_fixed_diagonal A alpha hA U lam
      (by simpa [D] using hdiag) (fun i => hA.eigenvalues_nonneg i) ε
  have hpow_zero : matrixPower A alpha hA =
      (U : SquareMatrix n) * Matrix.diagonal (fun i : Fin n => (lam i) ^ alpha) *
        star (U : SquareMatrix n) := by
    unfold matrixPower
    exact psdMatrixPower_eq_of_unitary_diagonalization A alpha hA U lam hdiag
      (fun i => hA.eigenvalues_nonneg i)
  let spectral : ℝ≥0 → SquareMatrix n := fun ε =>
    (U : SquareMatrix n) *
      Matrix.diagonal (fun i : Fin n => (lam i + (ε : ℝ)) ^ alpha) *
      star (U : SquareMatrix n)
  have hcont : Continuous spectral := by
    have hentry : ∀ i : Fin n,
        Continuous (fun ε : ℝ≥0 => (lam i + (ε : ℝ)) ^ alpha) := by
      intro i
      exact (Real.continuous_rpow_const halpha).comp
        (continuous_const.add NNReal.continuous_coe)
    have hdiag_cont : Continuous (fun ε : ℝ≥0 =>
        (Matrix.diagonal (fun i : Fin n => (lam i + (ε : ℝ)) ^ alpha) :
          SquareMatrix n)) := by
      apply continuous_matrix
      intro i j
      by_cases hij : i = j
      · subst j
        simpa using hentry i
      · simpa [Matrix.diagonal_apply, hij] using
          (continuous_const : Continuous (fun _ : ℝ≥0 => (0 : ℝ)))
    simpa only [spectral] using
      (continuous_const.mul hdiag_cont).mul continuous_const
  have hzero : spectral 0 = matrixPower A alpha hA := by
    rw [hpow_zero]
    simp only [spectral, NNReal.coe_zero, add_zero]
  have ht : Filter.Tendsto spectral (nhds 0)
      (nhds (matrixPower A alpha hA)) := by
    have ht0 : Filter.Tendsto spectral (nhds 0) (nhds (spectral 0)) :=
      hcont.continuousAt
    rw [hzero] at ht0
    exact ht0
  exact ht.congr' (Filter.Eventually.of_forall fun ε => by
    change spectral ε = matrixPower (A + (ε : ℝ) • (1 : SquareMatrix n)) alpha
      (matrix_add_nnnreal_one_posSemidef A hA ε)
    exact (hpow ε).symm)

private theorem tendsto_orderedMatrixProduct {q n : Nat} {Z : Type*}
    {l : Filter Z} (F : Z → Fin q → SquareMatrix n)
    (A : Fin q → SquareMatrix n)
    (hF : ∀ i, Filter.Tendsto (fun z => F z i) l (nhds (A i))) :
    Filter.Tendsto (fun z => orderedMatrixProduct (F z)) l
      (nhds (orderedMatrixProduct A)) := by
  have hprefix : ∀ a : Nat, a ≤ q →
      Filter.Tendsto (fun z => orderedMatrixProductNat (F z) a) l
        (nhds (orderedMatrixProductNat A a)) := by
    intro a
    induction a with
    | zero =>
        intro _ha
        simpa [orderedMatrixProductNat] using
          (tendsto_const_nhds : Filter.Tendsto (fun _ : Z => (1 : SquareMatrix n)) l
            (nhds 1))
    | succ a ih =>
        intro ha
        have hlt : a < q := Nat.lt_of_succ_le ha
        simpa [orderedMatrixProductNat, hlt] using
          (ih (Nat.le_of_succ_le ha)).mul (hF ⟨a, hlt⟩)
  exact hprefix q le_rfl

/- Book JSON key_lemmas.Lemma_5_Ando_geometric_mean. -/
theorem Lemma_5_Ando_geometric_mean {q n : Nat}
    (X Y : Fin q → SquareMatrix n) (alpha : Fin q → ℝ)
    (hX : ∀ i, (X i).PosSemidef) (hY : ∀ i, (Y i).PosSemidef)
    (hXY : ∀ i, X i ≤ Y i)
    (hXcomm : ∀ i j, X i * X j = X j * X i)
    (hYcomm : ∀ i j, Y i * Y j = Y j * Y i)
    (halpha_nonneg : ∀ i, 0 ≤ alpha i)
    (halpha_sum : (∑ i : Fin q, alpha i) = 1) :
    orderedMatrixProduct (fun i : Fin q => matrixPower (X i) (alpha i) (hX i)) ≤
      orderedMatrixProduct (fun i : Fin q => matrixPower (Y i) (alpha i) (hY i)) := by
  have hXpow : ∀ i, matrixPower (X i) (alpha i) (hX i) =
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ alpha i) (X i) := by
    intro i
    exact (positiveMatrixRpow_eq_matrixPower (X i) (alpha i) (hX i)).symm
  have hYpow : ∀ i, matrixPower (Y i) (alpha i) (hY i) =
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ alpha i) (Y i) := by
    intro i
    exact (positiveMatrixRpow_eq_matrixPower (Y i) (alpha i) (hY i)).symm
  rw [orderedMatrixProduct_eq_list_prod, orderedMatrixProduct_eq_list_prod]
  simp_rw [hXpow, hYpow]
  have hXrpow : (fun i => CFC.rpow (X i) (alpha i)) =
      (fun i => cfc (R := ℝ) (p := IsSelfAdjoint)
        (fun x : ℝ => x ^ alpha i) (X i)) := by
    funext i
    change (X i) ^ alpha i = _
    exact CFC.rpow_eq_cfc_real (hX i).nonneg
  have hYrpow : (fun i => CFC.rpow (Y i) (alpha i)) =
      (fun i => cfc (R := ℝ) (p := IsSelfAdjoint)
        (fun x : ℝ => x ^ alpha i) (Y i)) := by
    funext i
    change (Y i) ^ alpha i = _
    exact CFC.rpow_eq_cfc_real (hY i).nonneg
  have hmono := TensorsProofSupport.Matrix.list_prod_cfc_rpow_mono_of_pairwise_commute
    X Y alpha hX hY hXY
    (fun i j => show Commute (X i) (X j) from hXcomm i j)
    (fun i j => show Commute (Y i) (Y j) from hYcomm i j)
    halpha_nonneg halpha_sum
  simpa only [hXrpow, hYrpow] using hmono

/- Book JSON key_lemmas.Lemma_6_operator_monotone_powers. -/
theorem Lemma_6_operator_monotone_powers {n : Nat}
    (X Y : SquareMatrix n) (alpha : ℝ)
    (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hXY : X ≤ Y) (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1) :
    matrixPower X alpha hX ≤ matrixPower Y alpha hY := by
  classical
  let I : SquareMatrix n := 1
  let Xs : Fin 2 → SquareMatrix n := fun i => if i = 0 then X else I
  let Ys : Fin 2 → SquareMatrix n := fun i => if i = 0 then Y else I
  let weights : Fin 2 → ℝ := fun i => if i = 0 then alpha else 1 - alpha
  have hI : I.PosSemidef := by
    simpa [I] using (Matrix.PosSemidef.one : (1 : SquareMatrix n).PosSemidef)
  have hXs : ∀ i, (Xs i).PosSemidef := by
    intro i
    fin_cases i <;> simp [Xs, I, hX, hI]
  have hYs : ∀ i, (Ys i).PosSemidef := by
    intro i
    fin_cases i <;> simp [Ys, I, hY, hI]
  have hXsYs : ∀ i, Xs i ≤ Ys i := by
    intro i
    fin_cases i <;> simp [Xs, Ys, I, hXY]
  have hXscomm : ∀ i j, Xs i * Xs j = Xs j * Xs i := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Xs, I]
  have hYscomm : ∀ i j, Ys i * Ys j = Ys j * Ys i := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Ys, I]
  have hweights_nonneg : ∀ i, 0 ≤ weights i := by
    intro i
    fin_cases i
    · simpa [weights] using halpha0
    · simpa [weights] using sub_nonneg.mpr halpha1
  have hweights_sum : (∑ i : Fin 2, weights i) = 1 := by
    simp [weights, Fin.sum_univ_two]
  have hando := Lemma_5_Ando_geometric_mean Xs Ys weights hXs hYs hXsYs
    hXscomm hYscomm hweights_nonneg hweights_sum
  simpa [Xs, Ys, weights, I, orderedMatrixProduct_two, matrixPower_one] using hando

/- Book JSON key_lemmas.Gram_self_product_PSD plus
   assumptions.Epsilon_nonnegative_rank_lemmas:
   epsilon >= 0 and Gram/self-contraction definitions derive the PSD domain
   needed by fractional powers in Lemmas 8 and 11. -/
private theorem finset_sum_posSemidef_of_forall {ι : Type*} {n : Nat} [DecidableEq ι]
    (s : Finset ι) (A : ι → SquareMatrix n)
    (hA : ∀ i ∈ s, (A i).PosSemidef) :
    (s.sum fun i => A i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using
        (Matrix.PosSemidef.zero : Matrix.PosSemidef (0 : SquareMatrix n))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact
        (hA a (Finset.mem_insert_self a s)).add
          (ih (by
            intro i hi
            exact hA i (Finset.mem_insert_of_mem hi)))

private theorem finset_sum_generic_posSemidef_of_forall {ι κ : Type*}
    [DecidableEq ι] [Fintype κ] (s : Finset ι) (A : ι → GenericSquare κ)
    (hA : ∀ i ∈ s, (A i).PosSemidef) :
    (s.sum fun i => A i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using
        (Matrix.PosSemidef.zero : Matrix.PosSemidef (0 : GenericSquare κ))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact
        (hA a (Finset.mem_insert_self a s)).add
          (ih (by
            intro i hi
            exact hA i (Finset.mem_insert_of_mem hi)))

private theorem psdMatrixPower_kronecker_right_one_generic {m : Nat} {κ : Type*}
    [Fintype κ] [DecidableEq κ]
    (A : SquareMatrix m) (s : ℝ) (hA : A.PosSemidef) :
    psdMatrixPower (A ⊗ₖ (1 : GenericSquare κ)) s
        (hA.kronecker (Matrix.PosSemidef.one :
          (1 : GenericSquare κ).PosSemidef)) =
      matrixPower A s hA ⊗ₖ (1 : GenericSquare κ) := by
  classical
  let eκ : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  let ep : Fin m × κ ≃ Fin m × Fin (Fintype.card κ) :=
    (Equiv.refl (Fin m)).prodCongr eκ
  let Iκ : GenericSquare κ := 1
  let Ifin : SquareMatrix (Fintype.card κ) := 1
  have hbase_reindex :
      Matrix.reindexAlgEquiv ℝ ℝ ep (A ⊗ₖ Iκ) =
        A ⊗ₖ Ifin := by
    ext ij kl
    rcases ij with ⟨i, j⟩
    rcases kl with ⟨i', j'⟩
    by_cases hj : j = j'
    · subst j'
      simp [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, ep, Iκ, Ifin,
        Matrix.kroneckerMap_apply]
    · have hj' : eκ.symm j ≠ eκ.symm j' := by
        intro h
        exact hj (eκ.symm.injective h)
      simp [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, ep, Iκ, Ifin,
        Matrix.kroneckerMap_apply, hj, hj']
  have hpow_reindex :
      Matrix.reindexAlgEquiv ℝ ℝ ep
          (matrixPower A s hA ⊗ₖ Iκ) =
        matrixPower A s hA ⊗ₖ Ifin := by
    ext ij kl
    rcases ij with ⟨i, j⟩
    rcases kl with ⟨i', j'⟩
    by_cases hj : j = j'
    · subst j'
      simp [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, ep, Iκ, Ifin,
        Matrix.kroneckerMap_apply]
    · have hj' : eκ.symm j ≠ eκ.symm j' := by
        intro h
        exact hj (eκ.symm.injective h)
      simp [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, ep, Iκ, Ifin,
        Matrix.kroneckerMap_apply, hj, hj']
  have hIκ : Iκ.PosSemidef := by
    simpa [Iκ] using
      (Matrix.PosSemidef.one : (1 : GenericSquare κ).PosSemidef)
  have hIfin : Ifin.PosSemidef := by
    simpa [Ifin] using
      (Matrix.PosSemidef.one :
        (1 : SquareMatrix (Fintype.card κ)).PosSemidef)
  have hAIκ : (A ⊗ₖ Iκ).PosSemidef := hA.kronecker hIκ
  have hAIfin : (A ⊗ₖ Ifin).PosSemidef := by
    simpa [Ifin] using
      Lemma_3_iv_kron_psd A (1 : SquareMatrix (Fintype.card κ)) hA
        (Matrix.PosSemidef.one :
          (1 : SquareMatrix (Fintype.card κ)).PosSemidef)
  have hAIκ_reindex :
      (Matrix.reindexAlgEquiv ℝ ℝ ep (A ⊗ₖ Iκ)).PosSemidef := by
    simpa [hbase_reindex] using hAIfin
  have hleft_reindex :
      Matrix.reindexAlgEquiv ℝ ℝ ep
          (psdMatrixPower (A ⊗ₖ Iκ) s hAIκ) =
        matrixPower A s hA ⊗ₖ Ifin := by
    calc
      Matrix.reindexAlgEquiv ℝ ℝ ep
          (psdMatrixPower (A ⊗ₖ Iκ) s hAIκ) =
          psdMatrixPower (Matrix.reindexAlgEquiv ℝ ℝ ep (A ⊗ₖ Iκ)) s
            hAIκ_reindex := by
            exact psdMatrixPower_reindexAlgEquiv ep (A ⊗ₖ Iκ) s hAIκ
              hAIκ_reindex
      _ = psdMatrixPower (A ⊗ₖ Ifin) s hAIfin := by
            exact psdMatrixPower_congr hbase_reindex s hAIκ_reindex hAIfin
      _ = matrixPower A s hA ⊗ₖ matrixPower Ifin s hIfin := by
            rw [Subsingleton.elim hAIfin
              (Lemma_3_iv_kron_psd A Ifin hA hIfin)]
            exact psdMatrixPower_kronecker A Ifin s hA hIfin
      _ = matrixPower A s hA ⊗ₖ Ifin := by
            rw [matrixPower_one]
  exact (Matrix.reindexAlgEquiv ℝ ℝ ep).injective (by
    simpa [Iκ, Ifin] using hleft_reindex.trans hpow_reindex.symm)

private theorem vectorOuter_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℝ) :
    (vectorOuter g).PosSemidef := by
  classical
  let B : Matrix ι Unit ℝ := fun i _ => g i
  have hB : B * B.transpose = vectorOuter g := by
    ext i j
    simp [B, vectorOuter, Matrix.mul_apply]
  simpa [hB] using
    (Matrix.PosSemidef.one.mul_mul_conjTranspose_same (B := B))

private theorem matrix_rank_domination_M_posSemidef {T m n : Nat}
    (G : Fin T → MatrixSpace m n) (r : PosNat) (epsilon : ℝ)
    (heps : 0 ≤ epsilon) :
    (epsilon • (1 : GenericSquare (FlatMatrixIndex m n)) +
        (1 / positiveRankReal r) •
          (∑ t : Fin T, vectorOuter (matrixVec (G t)))).PosSemidef := by
  have h0 : (epsilon • (1 : GenericSquare (FlatMatrixIndex m n))).PosSemidef :=
    Matrix.PosSemidef.one.smul heps
  have hsum : (∑ t : Fin T, vectorOuter (matrixVec (G t))).PosSemidef :=
    finset_sum_generic_posSemidef_of_forall Finset.univ
      (fun t : Fin T => @vectorOuter (FlatMatrixIndex m n) (matrixVec (G t)))
      (by
        intro t _ht
        exact vectorOuter_posSemidef (ι := FlatMatrixIndex m n) (matrixVec (G t)))
  have hscale : 0 ≤ (1 / positiveRankReal r : ℝ) := by
    simpa [one_div] using inv_nonneg.mpr (le_of_lt (positiveRankReal_pos r))
  exact h0.add (hsum.smul hscale)

private theorem diagonalPart_posSemidef_of_posSemidef {n : Nat} {A : SquareMatrix n}
    (hA : A.PosSemidef) :
    (diagonalPart A).PosSemidef := by
  simpa [diagonalPart] using Matrix.diagonalPart_posSemidef hA

theorem accumulated_matrix_left_psd_from_epsilon {T m n : Nat}
    (G : Fin T → MatrixSpace m n) (epsilon : ℝ) (heps : 0 ≤ epsilon) :
    (epsilon • (1 : SquareMatrix m) + ∑ t : Fin T, matrixGramLeft (G t)).PosSemidef := by
  have h0 : (epsilon • (1 : SquareMatrix m)).PosSemidef :=
    Matrix.PosSemidef.one.smul heps
  have hsum : (∑ t : Fin T, matrixGramLeft (G t)).PosSemidef :=
    finset_sum_posSemidef_of_forall Finset.univ
      (fun t : Fin T => matrixGramLeft (G t))
      (by
        intro t _ht
        simpa [matrixGramLeft] using
          (Matrix.PosSemidef.one.mul_mul_conjTranspose_same (B := G t)))
  simpa using h0.add hsum

theorem accumulated_matrix_right_psd_from_epsilon {T m n : Nat}
    (G : Fin T → MatrixSpace m n) (epsilon : ℝ) (heps : 0 ≤ epsilon) :
    (epsilon • (1 : SquareMatrix n) + ∑ t : Fin T, matrixGramRight (G t)).PosSemidef := by
  have h0 : (epsilon • (1 : SquareMatrix n)).PosSemidef :=
    Matrix.PosSemidef.one.smul heps
  have hsum : (∑ t : Fin T, matrixGramRight (G t)).PosSemidef :=
    finset_sum_posSemidef_of_forall Finset.univ
      (fun t : Fin T => matrixGramRight (G t))
      (by
        intro t _ht
        simpa [matrixGramRight] using
          (Matrix.PosSemidef.one.conjTranspose_mul_mul_same (B := G t)))
  simpa using h0.add hsum

theorem accumulated_tensor_contraction_psd_from_epsilon {k T : Nat}
    {dims : Fin k → Nat} (G : Fin T → TensorSpace dims) (epsilon : ℝ)
    (heps : 0 ≤ epsilon) (i : Fin k) :
    (epsilon • (1 : SquareMatrix (dims i)) +
        ∑ t : Fin T, tensorContraction (G t) i).PosSemidef := by
  have h0 : (epsilon • (1 : SquareMatrix (dims i))).PosSemidef :=
    Matrix.PosSemidef.one.smul heps
  have hsum : (∑ t : Fin T, tensorContraction (G t) i).PosSemidef :=
    finset_sum_posSemidef_of_forall Finset.univ
      (fun t : Fin T => tensorContraction (G t) i)
      (by
        intro t _ht
        simpa [tensorContraction] using
          (Matrix.PosSemidef.one.mul_mul_conjTranspose_same
            (B := matricization (G t) i)))
  simpa using h0.add hsum

theorem accumulated_diagonal_left_psd_from_epsilon {T m n : Nat}
    (G : Fin T → MatrixSpace m n) (epsilon : ℝ) (heps : 0 ≤ epsilon) :
    (epsilon • (1 : SquareMatrix m) +
        ∑ t : Fin T, diagonalPart (matrixGramLeft (G t))).PosSemidef := by
  have h0 : (epsilon • (1 : SquareMatrix m)).PosSemidef :=
    Matrix.PosSemidef.one.smul heps
  have hsum : (∑ t : Fin T, diagonalPart (matrixGramLeft (G t))).PosSemidef :=
    finset_sum_posSemidef_of_forall Finset.univ
      (fun t : Fin T => diagonalPart (matrixGramLeft (G t)))
      (by
        intro t _ht
        exact
          diagonalPart_posSemidef_of_posSemidef
            (by
              simpa [matrixGramLeft] using
                (Matrix.PosSemidef.one.mul_mul_conjTranspose_same (B := G t))))
  simpa using h0.add hsum

theorem accumulated_diagonal_right_psd_from_epsilon {T m n : Nat}
    (G : Fin T → MatrixSpace m n) (epsilon : ℝ) (heps : 0 ≤ epsilon) :
    (epsilon • (1 : SquareMatrix n) +
        ∑ t : Fin T, diagonalPart (matrixGramRight (G t))).PosSemidef := by
  have h0 : (epsilon • (1 : SquareMatrix n)).PosSemidef :=
    Matrix.PosSemidef.one.smul heps
  have hsum : (∑ t : Fin T, diagonalPart (matrixGramRight (G t))).PosSemidef :=
    finset_sum_posSemidef_of_forall Finset.univ
      (fun t : Fin T => diagonalPart (matrixGramRight (G t)))
      (by
        intro t _ht
        exact
          diagonalPart_posSemidef_of_posSemidef
            (by
              simpa [matrixGramRight] using
                (Matrix.PosSemidef.one.conjTranspose_mul_mul_same (B := G t))))
  simpa using h0.add hsum

private theorem sq_sum_le_card_mul_sum_sq_real {ι : Type*} [Fintype ι]
    (a : ι → ℝ) :
    (∑ i : ι, a i) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i : ι, (a i) ^ 2 := by
  classical
  have h := Finset.sum_mul_sq_le_sq_mul_sq
    (s := (Finset.univ : Finset ι)) (f := fun _ : ι => (1 : ℝ)) (g := a)
  simpa using h

private theorem vectorOuter_dotProduct_mulVec {α : Type*} [Fintype α]
    (x g : α → ℝ) :
    dotProduct (star x) ((vectorOuter g).mulVec x) =
      (∑ a : α, x a * g a) ^ 2 := by
  classical
  simp [dotProduct, Matrix.mulVec, vectorOuter, pow_two, Finset.mul_sum,
    Finset.sum_mul, Finset.sum_comm, mul_assoc, mul_left_comm, mul_comm]

private theorem vector_sum_outer_le_card_smul_sum_outer {ι α : Type*}
    [Fintype ι] [Fintype α] (w : ι → α → ℝ) :
    vectorOuter (fun a : α => ∑ i : ι, w i a) ≤
      (Fintype.card ι : ℝ) • ∑ i : ι, vectorOuter (w i) := by
  simpa [vectorOuter] using
    (TensorsProofSupport.Matrix.vecMulVec_sum_le_card_smul_sum_vecMulVec w)

private theorem vectorKronecker_outer_eq_kron_outer {m n : Nat}
    (u : Fin m → ℝ) (v : Fin n → ℝ) :
    vectorOuter (Function.uncurry (Matrix.vecMulVec u v)) = vectorOuter u ⊗ₖ vectorOuter v := by
  simpa [vectorOuter] using Matrix.vecMulVec_vectorKronecker_self u v

private theorem vectorOuter_le_one_of_sum_sq_le_one {m : Nat} (u : Fin m → ℝ)
    (hu : ∑ i : Fin m, u i ^ 2 ≤ 1) :
    vectorOuter u ≤ (1 : SquareMatrix m) := by
  simpa [vectorOuter, Matrix.vecMulVec] using
    (TensorsProofSupport.Matrix.vecMulVec_le_one_of_sum_sq_le_one u hu)

private theorem matrix_col_mem_toLin_range {m n : Nat} (G : MatrixSpace m n)
    (j : Fin n) :
    G.col j ∈ LinearMap.range (Matrix.toLin' G) := by
  refine ⟨Pi.single j (1 : ℝ), ?_⟩
  ext i
  simp [Matrix.toLin'_apply, Matrix.mulVec, Matrix.col_apply]

private theorem matrix_rank_eq_finrank_toLin_range {m n : Nat} (G : MatrixSpace m n) :
    Module.finrank ℝ (LinearMap.range (Matrix.toLin' G)) = G.rank := by
  change Module.finrank ℝ (LinearMap.range (Matrix.toLin' G)) =
    Module.finrank ℝ (LinearMap.range G.mulVecLin)
  rw [Matrix.toLin'_apply']

private theorem matrix_col_mem_euclidean_toLin_range {m n : Nat} (G : MatrixSpace m n)
    (j : Fin n) :
    (WithLp.toLp 2 (G.col j) : EuclideanSpace ℝ (Fin m)) ∈
      LinearMap.range
        (((WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm : (Fin m → ℝ) ≃ₗ[ℝ]
            EuclideanSpace ℝ (Fin m)).toLinearMap.comp (Matrix.toLin' G)) := by
  refine ⟨Pi.single j (1 : ℝ), ?_⟩
  change ((WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm)
      (Matrix.toLin' G (Pi.single j (1 : ℝ))) =
    (WithLp.toLp 2 (G.col j) : EuclideanSpace ℝ (Fin m))
  apply (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).injective
  ext i
  simp [Matrix.toLin'_apply, Matrix.mulVec, Matrix.col_apply]

private theorem matrix_rank_eq_finrank_euclidean_toLin_range {m n : Nat}
    (G : MatrixSpace m n) :
    Module.finrank ℝ
        (LinearMap.range
          (((WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm : (Fin m → ℝ) ≃ₗ[ℝ]
              EuclideanSpace ℝ (Fin m)).toLinearMap.comp (Matrix.toLin' G))) =
      G.rank := by
  let e : (Fin m → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
    (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm
  calc
    Module.finrank ℝ (LinearMap.range (e.toLinearMap.comp (Matrix.toLin' G))) =
        Module.finrank ℝ ((LinearMap.range (Matrix.toLin' G)).map e.toLinearMap) := by
          rw [LinearMap.range_comp]
    _ = Module.finrank ℝ (LinearMap.range (Matrix.toLin' G)) := by
          exact e.finrank_map_eq (LinearMap.range (Matrix.toLin' G))
    _ = G.rank := matrix_rank_eq_finrank_toLin_range G

private theorem matrix_rank_column_space_rank_one_expansion {m n : Nat}
    (G : MatrixSpace m n) :
    ∃ (u : Fin G.rank → Fin m → ℝ) (b : Fin G.rank → Fin n → ℝ),
      G = ∑ a : Fin G.rank, matrixOuter (u a) (b a) ∧
        ∀ a : Fin G.rank, ∑ i : Fin m, u a i ^ 2 ≤ 1 := by
  simpa [matrixOuter, Matrix.vecMulVec] using
    (Matrix.exists_rank_one_sum_eq_with_left_norm_le_one G)

private theorem matrix_rank_column_space_rank_one_expansion_outer_bound {m n : Nat}
    (G : MatrixSpace m n) :
    ∃ (u : Fin G.rank → Fin m → ℝ) (b : Fin G.rank → Fin n → ℝ),
      G = ∑ a : Fin G.rank, matrixOuter (u a) (b a) ∧
        ∀ a : Fin G.rank, vectorOuter (u a) ≤ (1 : SquareMatrix m) := by
  obtain ⟨u, b, hG, hunit⟩ := matrix_rank_column_space_rank_one_expansion G
  exact ⟨u, b, hG, fun a => vectorOuter_le_one_of_sum_sq_le_one (u a) (hunit a)⟩

set_option maxHeartbeats 400000 in
private theorem matrix_rank_column_space_orthonormal_rank_one_expansion {m n : Nat}
    (G : MatrixSpace m n) :
    ∃ (u : Fin G.rank → Fin m → ℝ) (b : Fin G.rank → Fin n → ℝ),
      G = ∑ a : Fin G.rank, matrixOuter (u a) (b a) ∧
        (∀ a a' : Fin G.rank,
          ∑ i : Fin m, u a i * u a' i = if a = a' then 1 else 0) ∧
        ∀ a : Fin G.rank, vectorOuter (u a) ≤ (1 : SquareMatrix m) := by
  simpa [matrixOuter, vectorOuter, Matrix.vecMulVec] using
    (TensorsProofSupport.Matrix.exists_rank_one_sum_eq_with_orthonormal_left G)

private theorem finite_orthonormal_coordinate_gram_collapse
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (u : ι → κ → ℝ) (x y : ι → ℝ)
    (horth : ∀ a a' : ι, ∑ k : κ, u a k * u a' k = if a = a' then 1 else 0) :
    ∑ k : κ, (∑ a : ι, u a k * x a) * (∑ a' : ι, u a' k * y a') =
      ∑ a : ι, x a * y a := by
  exact finite_orthonormal_coordinate_bilinear_collapse u x y horth

private theorem matrixGramRight_eq_sum_vectorOuter_of_orthonormal_rank_one_expansion
    {m n : Nat} {G : MatrixSpace m n}
    {u : Fin G.rank → Fin m → ℝ} {b : Fin G.rank → Fin n → ℝ}
    (hG : G = ∑ a : Fin G.rank, matrixOuter (u a) (b a))
    (horth : ∀ a a' : Fin G.rank,
      ∑ i : Fin m, u a i * u a' i = if a = a' then 1 else 0) :
    matrixGramRight G = ∑ a : Fin G.rank, vectorOuter (b a) := by
  simpa [matrixGramRight, matrixOuter, vectorOuter, Matrix.vecMulVec] using
    TensorsProofSupport.Matrix.transpose_mul_self_eq_sum_vecMulVec_of_orthonormal_left
      G u b hG horth

private theorem smul_le_self_of_nonneg_le_one_posSemidef {ι : Type*}
    [Fintype ι] [DecidableEq ι] (A : GenericSquare ι) {c : ℝ}
    (hA : A.PosSemidef) (hc1 : c ≤ 1) :
    c • A ≤ A := by
  rw [Matrix.le_iff]
  have hdiff : A - c • A = (1 - c) • A := by
    ext i j
    simp [sub_mul]
  have hscale : 0 ≤ 1 - c := sub_nonneg.mpr hc1
  simpa [hdiff] using hA.smul hscale

private theorem rank_scaled_vector_sum_outer_bound {m n : Nat}
    (G : MatrixSpace m n) (r : PosNat) (hrank : G.rank ≤ r.1)
    (u : Fin G.rank → Fin m → ℝ) (b : Fin G.rank → Fin n → ℝ)
    (hsum_vec :
      vectorOuter (matrixVec G) ≤
        (Fintype.card (Fin G.rank) : ℝ) •
          ∑ a : Fin G.rank, vectorOuter (Function.uncurry (Matrix.vecMulVec (u a) (b a)))) :
    (1 / positiveRankReal r) • vectorOuter (matrixVec G) ≤
      ∑ a : Fin G.rank, vectorOuter (Function.uncurry (Matrix.vecMulVec (u a) (b a))) := by
  classical
  let S : GenericSquare (FlatMatrixIndex m n) :=
    ∑ a : Fin G.rank, vectorOuter (Function.uncurry (Matrix.vecMulVec (u a) (b a)))
  have hSpsd : S.PosSemidef :=
    finset_sum_generic_posSemidef_of_forall Finset.univ
      (fun a : Fin G.rank =>
        vectorOuter (Function.uncurry (Matrix.vecMulVec (u a) (b a))))
      (by
        intro a _ha
        exact vectorOuter_posSemidef
          (ι := FlatMatrixIndex m n) (Function.uncurry (Matrix.vecMulVec (u a) (b a))))
  have hscale_nonneg : 0 ≤ (1 / positiveRankReal r : ℝ) := by
    exact div_nonneg zero_le_one (le_of_lt (positiveRankReal_pos r))
  have hscaled :
      (1 / positiveRankReal r) • vectorOuter (matrixVec G) ≤
        (1 / positiveRankReal r) •
          ((Fintype.card (Fin G.rank) : ℝ) • S) :=
    smul_le_smul_of_nonneg_left (by simpa [S] using hsum_vec) hscale_nonneg
  have hcard_le : (Fintype.card (Fin G.rank) : ℝ) ≤ positiveRankReal r := by
    rw [Fintype.card_fin, positiveRankReal]
    exact_mod_cast hrank
  have hcoef_le_one :
      (1 / positiveRankReal r) * (Fintype.card (Fin G.rank) : ℝ) ≤ 1 := by
    have hpos := positiveRankReal_pos r
    calc
      (1 / positiveRankReal r) * (Fintype.card (Fin G.rank) : ℝ) =
          (positiveRankReal r)⁻¹ * (Fintype.card (Fin G.rank) : ℝ) := by
            rw [one_div]
      _ ≤ (positiveRankReal r)⁻¹ * positiveRankReal r :=
            mul_le_mul_of_nonneg_left hcard_le
              (inv_nonneg.mpr (le_of_lt hpos))
      _ = 1 := inv_mul_cancel₀ hpos.ne'
  have hcoef :
      (1 / positiveRankReal r) •
          ((Fintype.card (Fin G.rank) : ℝ) • S) ≤ S := by
    simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using
      smul_le_self_of_nonneg_le_one_posSemidef S hSpsd hcoef_le_one
  exact le_trans hscaled hcoef

private theorem sum_vectorKronecker_outer_le_one_kron_sum_outer {m n d : Nat}
    (u : Fin d → Fin m → ℝ) (b : Fin d → Fin n → ℝ)
    (hubound : ∀ a : Fin d, vectorOuter (u a) ≤ (1 : SquareMatrix m)) :
    (∑ a : Fin d, vectorOuter (Function.uncurry (Matrix.vecMulVec (u a) (b a)))) ≤
      (1 : SquareMatrix m) ⊗ₖ
        (∑ a : Fin d, vectorOuter (b a)) := by
  simpa [vectorOuter] using
    TensorsProofSupport.Matrix.sum_vecMulVec_product_le_one_kronecker_sum_vecMulVec
      u b hubound

private theorem sum_vectorKronecker_outer_le_one_kron_gram_right {m n : Nat}
    (G : MatrixSpace m n)
    (u : Fin G.rank → Fin m → ℝ) (b : Fin G.rank → Fin n → ℝ)
    (hubound : ∀ a : Fin G.rank, vectorOuter (u a) ≤ (1 : SquareMatrix m))
    (hgramR : matrixGramRight G = ∑ a : Fin G.rank, vectorOuter (b a)) :
    (∑ a : Fin G.rank, vectorOuter (Function.uncurry (Matrix.vecMulVec (u a) (b a)))) ≤
      (1 : SquareMatrix m) ⊗ₖ matrixGramRight G := by
  simpa [hgramR] using
    sum_vectorKronecker_outer_le_one_kron_sum_outer u b hubound

private theorem matrix_rank_row_space_orthonormal_rank_one_expansion {m n : Nat}
    (G : MatrixSpace m n) :
    ∃ (u : Fin G.rank → Fin m → ℝ) (b : Fin G.rank → Fin n → ℝ),
      G = ∑ a : Fin G.rank, matrixOuter (u a) (b a) ∧
        (∀ a a' : Fin G.rank,
          ∑ j : Fin n, b a j * b a' j = if a = a' then 1 else 0) ∧
        ∀ a : Fin G.rank, vectorOuter (b a) ≤ (1 : SquareMatrix n) := by
  simpa [matrixOuter, vectorOuter, Matrix.vecMulVec] using
    (TensorsProofSupport.Matrix.exists_rank_one_sum_eq_with_orthonormal_right G)

private theorem matrixGramLeft_eq_sum_vectorOuter_of_row_orthonormal_rank_one_expansion
    {m n : Nat} {G : MatrixSpace m n}
    {u : Fin G.rank → Fin m → ℝ} {b : Fin G.rank → Fin n → ℝ}
    (hG : G = ∑ a : Fin G.rank, matrixOuter (u a) (b a))
    (horth : ∀ a a' : Fin G.rank,
      ∑ j : Fin n, b a j * b a' j = if a = a' then 1 else 0) :
    matrixGramLeft G = ∑ a : Fin G.rank, vectorOuter (u a) := by
  simpa [matrixGramLeft, matrixOuter, vectorOuter, Matrix.vecMulVec] using
    TensorsProofSupport.Matrix.mul_transpose_eq_sum_vecMulVec_of_orthonormal_right
      G u b hG horth

private theorem sum_vectorKronecker_outer_le_sum_outer_kron_one {m n d : Nat}
    (u : Fin d → Fin m → ℝ) (b : Fin d → Fin n → ℝ)
    (hbbound : ∀ a : Fin d, vectorOuter (b a) ≤ (1 : SquareMatrix n)) :
    (∑ a : Fin d, vectorOuter (Function.uncurry (Matrix.vecMulVec (u a) (b a)))) ≤
      (∑ a : Fin d, vectorOuter (u a)) ⊗ₖ
        (1 : SquareMatrix n) := by
  simpa [vectorOuter] using
    TensorsProofSupport.Matrix.sum_vecMulVec_product_le_sum_vecMulVec_kronecker_one
      u b hbbound

private theorem sum_vectorKronecker_outer_le_gram_left_kron_one {m n : Nat}
    (G : MatrixSpace m n)
    (u : Fin G.rank → Fin m → ℝ) (b : Fin G.rank → Fin n → ℝ)
    (hbbound : ∀ a : Fin G.rank, vectorOuter (b a) ≤ (1 : SquareMatrix n))
    (hgramL : matrixGramLeft G = ∑ a : Fin G.rank, vectorOuter (u a)) :
    (∑ a : Fin G.rank, vectorOuter (Function.uncurry (Matrix.vecMulVec (u a) (b a)))) ≤
      matrixGramLeft G ⊗ₖ (1 : SquareMatrix n) := by
  simpa [hgramL] using
    sum_vectorKronecker_outer_le_sum_outer_kron_one u b hbbound

/- Book JSON key_lemmas.Lemma_9_single_matrix_rank_domination. -/
theorem Lemma_9_single_matrix_rank_domination {m n : Nat}
    (G : MatrixSpace m n) (r : PosNat) (hrank : G.rank ≤ r.1) :
    (1 / positiveRankReal r) • vectorOuter (matrixVec G) ≤
        ((1 : SquareMatrix m) ⊗ₖ matrixGramRight G) ∧
      (1 / positiveRankReal r) • vectorOuter (matrixVec G) ≤
        (matrixGramLeft G ⊗ₖ (1 : SquareMatrix n)) := by
  simpa [positiveRankReal, vectorOuter, matrixVec, matrixGramRight,
    matrixGramLeft, one_div] using
      (Matrix.inv_rank_smul_vecMulVec_vectorization_le_kronecker_grams
        G r.1 r.2 hrank)

private theorem smul_one_flat_eq_one_kron_smul_one {m n : Nat} (epsilon : ℝ) :
    epsilon • (1 : GenericSquare (FlatMatrixIndex m n)) =
      (1 : SquareMatrix m) ⊗ₖ (epsilon • (1 : SquareMatrix n)) := by
  ext ij kl
  rcases ij with ⟨i, j⟩
  rcases kl with ⟨k, l⟩
  by_cases hik : i = k
  · subst k
    by_cases hjl : j = l
    · subst l
      simp [Matrix.kroneckerMap_apply]
    · simp [Matrix.kroneckerMap_apply, hjl]
  · simp [Matrix.kroneckerMap_apply, hik]

private theorem smul_one_flat_eq_smul_one_kron_one {m n : Nat} (epsilon : ℝ) :
    epsilon • (1 : GenericSquare (FlatMatrixIndex m n)) =
      (epsilon • (1 : SquareMatrix m)) ⊗ₖ (1 : SquareMatrix n) := by
  ext ij kl
  rcases ij with ⟨i, j⟩
  rcases kl with ⟨k, l⟩
  by_cases hik : i = k
  · subst k
    by_cases hjl : j = l
    · subst l
      simp [Matrix.kroneckerMap_apply]
    · simp [Matrix.kroneckerMap_apply, hjl]
  · simp [Matrix.kroneckerMap_apply, hik]

private theorem one_kron_sum_matrixGramRight {T m n : Nat}
    (G : Fin T → MatrixSpace m n) :
    (1 : SquareMatrix m) ⊗ₖ (∑ t : Fin T, matrixGramRight (G t)) =
      ∑ t : Fin T, (1 : SquareMatrix m) ⊗ₖ matrixGramRight (G t) := by
  ext ij kl
  simp_rw [Matrix.sum_apply, Matrix.kroneckerMap_apply]
  rw [Matrix.sum_apply]
  rw [Finset.mul_sum]

private theorem sum_matrixGramLeft_kron_one {T m n : Nat}
    (G : Fin T → MatrixSpace m n) :
    (∑ t : Fin T, matrixGramLeft (G t)) ⊗ₖ (1 : SquareMatrix n) =
      ∑ t : Fin T, matrixGramLeft (G t) ⊗ₖ (1 : SquareMatrix n) := by
  ext ij kl
  simp_rw [Matrix.sum_apply, Matrix.kroneckerMap_apply]
  rw [Matrix.sum_apply]
  rw [Finset.sum_mul]

private theorem matrix_rank_domination_two_upper_bounds {T m n : Nat}
    (G : Fin T → MatrixSpace m n) (r : PosNat) (epsilon : ℝ)
    (hrank : ∀ t : Fin T, (G t).rank ≤ r.1) (heps : 0 ≤ epsilon) :
    let A : SquareMatrix m :=
      epsilon • (1 : SquareMatrix m) + ∑ t : Fin T, matrixGramLeft (G t)
    let B : SquareMatrix n :=
      epsilon • (1 : SquareMatrix n) + ∑ t : Fin T, matrixGramRight (G t)
    let M : GenericSquare (FlatMatrixIndex m n) :=
      epsilon • (1 : GenericSquare (FlatMatrixIndex m n)) +
        (1 / positiveRankReal r) • (∑ t : Fin T, vectorOuter (matrixVec (G t)))
    M ≤ (1 : SquareMatrix m) ⊗ₖ B ∧ M ≤ A ⊗ₖ (1 : SquareMatrix n) := by
  simpa [positiveRankReal, vectorOuter, matrixVec, matrixGramRight,
    matrixGramLeft, one_div] using
      (TensorsProofSupport.Matrix.regularized_inv_rank_vecMulVec_sum_le_kronecker_gram_bounds
        G r.1 epsilon r.2 hrank)

private theorem ando_geometric_mean_two_flat_same_lower {m n : Nat}
    (M Y0 Y1 : GenericSquare (FlatMatrixIndex m n))
    (hM : M.PosSemidef) (hY0 : Y0.PosSemidef) (hY1 : Y1.PosSemidef)
    (hM_le_Y0 : M ≤ Y0) (hM_le_Y1 : M ≤ Y1)
    (hYcomm : Y0 * Y1 = Y1 * Y0) :
    psdMatrixPower M (1 / 2 : ℝ) hM *
        psdMatrixPower M (1 / 2 : ℝ) hM ≤
      psdMatrixPower Y0 (1 / 2 : ℝ) hY0 *
        psdMatrixPower Y1 (1 / 2 : ℝ) hY1 := by
  classical
  let e : FlatMatrixIndex m n ≃ Fin (Fintype.card (FlatMatrixIndex m n)) :=
    Fintype.equivFin (FlatMatrixIndex m n)
  let Mf : SquareMatrix (Fintype.card (FlatMatrixIndex m n)) :=
    Matrix.reindexAlgEquiv ℝ ℝ e M
  let Y0f : SquareMatrix (Fintype.card (FlatMatrixIndex m n)) :=
    Matrix.reindexAlgEquiv ℝ ℝ e Y0
  let Y1f : SquareMatrix (Fintype.card (FlatMatrixIndex m n)) :=
    Matrix.reindexAlgEquiv ℝ ℝ e Y1
  have hMf : Mf.PosSemidef := by
    simpa [Mf, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply] using
      ((Matrix.posSemidef_submatrix_equiv e.symm).2 hM)
  have hY0f : Y0f.PosSemidef := by
    simpa [Y0f, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply] using
      ((Matrix.posSemidef_submatrix_equiv e.symm).2 hY0)
  have hY1f : Y1f.PosSemidef := by
    simpa [Y1f, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply] using
      ((Matrix.posSemidef_submatrix_equiv e.symm).2 hY1)
  have hMf_le_Y0f : Mf ≤ Y0f := by
    simpa [Mf, Y0f] using
      (matrix_le_reindexAlgEquiv_iff e M Y0).1 hM_le_Y0
  have hMf_le_Y1f : Mf ≤ Y1f := by
    simpa [Mf, Y1f] using
      (matrix_le_reindexAlgEquiv_iff e M Y1).1 hM_le_Y1
  have hYfcomm : Y0f * Y1f = Y1f * Y0f := by
    calc
      Y0f * Y1f =
          Matrix.reindexAlgEquiv ℝ ℝ e (Y0 * Y1) := by
            rw [Matrix.reindexAlgEquiv_mul]
      _ = Matrix.reindexAlgEquiv ℝ ℝ e (Y1 * Y0) := by
            rw [hYcomm]
      _ = Y1f * Y0f := by
            rw [Matrix.reindexAlgEquiv_mul]
  let X : Fin 2 → SquareMatrix (Fintype.card (FlatMatrixIndex m n)) := fun _ => Mf
  let Y : Fin 2 → SquareMatrix (Fintype.card (FlatMatrixIndex m n)) :=
    fun i => if i = 0 then Y0f else Y1f
  let alpha : Fin 2 → ℝ := fun _ => (1 / 2 : ℝ)
  have hX : ∀ i, (X i).PosSemidef := by
    intro i
    simp [X, hMf]
  have hY : ∀ i, (Y i).PosSemidef := by
    intro i
    fin_cases i <;> simp [Y, hY0f, hY1f]
  have hXY : ∀ i, X i ≤ Y i := by
    intro i
    fin_cases i <;> simp [X, Y, hMf_le_Y0f, hMf_le_Y1f]
  have hXcomm : ∀ i j, X i * X j = X j * X i := by
    intro i j
    simp [X]
  have hYcomm_fin : ∀ i j, Y i * Y j = Y j * Y i := by
    intro i j
    fin_cases i <;> fin_cases j
    · simp [Y]
    · simpa [Y] using hYfcomm
    · simpa [Y] using hYfcomm.symm
    · simp [Y]
  have halpha_nonneg : ∀ i, 0 ≤ alpha i := by
    intro i
    norm_num [alpha]
  have halpha_sum : (∑ i : Fin 2, alpha i) = 1 := by
    norm_num [alpha, Fin.sum_univ_two]
  have hando :=
    Lemma_5_Ando_geometric_mean X Y alpha hX hY hXY hXcomm hYcomm_fin
      halpha_nonneg halpha_sum
  have hfin :
      Matrix.reindexAlgEquiv ℝ ℝ e
          (psdMatrixPower M (1 / 2 : ℝ) hM *
            psdMatrixPower M (1 / 2 : ℝ) hM) ≤
        Matrix.reindexAlgEquiv ℝ ℝ e
          (psdMatrixPower Y0 (1 / 2 : ℝ) hY0 *
            psdMatrixPower Y1 (1 / 2 : ℝ) hY1) := by
    rw [Matrix.reindexAlgEquiv_mul, Matrix.reindexAlgEquiv_mul]
    rw [psdMatrixPower_reindexAlgEquiv e M (1 / 2 : ℝ) hM hMf]
    rw [psdMatrixPower_reindexAlgEquiv e Y0 (1 / 2 : ℝ) hY0 hY0f]
    rw [psdMatrixPower_reindexAlgEquiv e Y1 (1 / 2 : ℝ) hY1 hY1f]
    simpa [X, Y, alpha, matrixPower, orderedMatrixProduct_two] using hando
  exact
    (matrix_le_reindexAlgEquiv_iff e
      (psdMatrixPower M (1 / 2 : ℝ) hM *
        psdMatrixPower M (1 / 2 : ℝ) hM)
      (psdMatrixPower Y0 (1 / 2 : ℝ) hY0 *
        psdMatrixPower Y1 (1 / 2 : ℝ) hY1)).2 hfin

private theorem two_kron_upper_bounds_geometric_mean {m n : Nat}
    (M : GenericSquare (FlatMatrixIndex m n)) (A : SquareMatrix m) (B : SquareMatrix n)
    (hM : M.PosSemidef) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hM_le_IB : M ≤ (1 : SquareMatrix m) ⊗ₖ B)
    (hM_le_AI : M ≤ A ⊗ₖ (1 : SquareMatrix n)) :
    M ≤ matrixPower A (1 / 2 : ℝ) hA ⊗ₖ matrixPower B (1 / 2 : ℝ) hB := by
  have h :=
    TensorsProofSupport.Matrix.le_cfc_sqrt_kronecker_cfc_sqrt_of_two_kronecker_bounds
    M A B hM hA hB hM_le_IB hM_le_AI
  rw [CFC.sqrt_eq_rpow, CFC.rpow_eq_cfc_real hA.nonneg,
    CFC.sqrt_eq_rpow, CFC.rpow_eq_cfc_real hB.nonneg] at h
  simpa only [matrixPower, psdMatrixPower_eq_cfc] using h

/- Book JSON key_lemmas.Lemma_8_matrix_rank_domination. -/
theorem Lemma_8_matrix_rank_domination {T m n : Nat}
    (G : Fin T → MatrixSpace m n) (r : PosNat) (epsilon : ℝ)
    (hrank : ∀ t : Fin T, (G t).rank ≤ r.1) (heps : 0 ≤ epsilon) :
    epsilon • (1 : GenericSquare (FlatMatrixIndex m n)) +
        (1 / positiveRankReal r) • (∑ t : Fin T, vectorOuter (matrixVec (G t))) ≤
      (matrixPower (epsilon • (1 : SquareMatrix m) + ∑ t : Fin T, matrixGramLeft (G t))
          (1 / 2 : ℝ) (accumulated_matrix_left_psd_from_epsilon G epsilon heps) ⊗ₖ
        matrixPower (epsilon • (1 : SquareMatrix n) + ∑ t : Fin T, matrixGramRight (G t))
          (1 / 2 : ℝ) (accumulated_matrix_right_psd_from_epsilon G epsilon heps)) := by
  have h :=
    TensorsProofSupport.Matrix.regularized_inv_rank_vecMulVec_sum_le_cfc_sqrt_kronecker_grams
    G r.1 epsilon r.2 hrank heps
  have hA :
      (epsilon • (1 : SquareMatrix m) +
        ∑ t : Fin T, Matrix.leftGram (G t)).PosSemidef := by
    simpa [matrixGramLeft, Matrix.leftGram] using
      accumulated_matrix_left_psd_from_epsilon G epsilon heps
  have hB :
      (epsilon • (1 : SquareMatrix n) +
        ∑ t : Fin T, Matrix.rightGram (G t)).PosSemidef := by
    simpa [matrixGramRight, Matrix.rightGram] using
      accumulated_matrix_right_psd_from_epsilon G epsilon heps
  dsimp only at h
  have hA' :
      (epsilon • (1 : SquareMatrix m) +
        ∑ t : Fin T, TensorsProofSupport.Matrix.leftGram (G t)).PosSemidef := by
    simpa [TensorsProofSupport.Matrix.leftGram, Matrix.leftGram] using hA
  have hB' :
      (epsilon • (1 : SquareMatrix n) +
        ∑ t : Fin T, TensorsProofSupport.Matrix.rightGram (G t)).PosSemidef := by
    simpa [TensorsProofSupport.Matrix.rightGram, Matrix.rightGram] using hB
  have hsqrtA : CFC.sqrt
      (epsilon • (1 : SquareMatrix m) +
        ∑ t : Fin T, TensorsProofSupport.Matrix.leftGram (G t)) =
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ))
        (epsilon • (1 : SquareMatrix m) +
          ∑ t : Fin T, TensorsProofSupport.Matrix.leftGram (G t)) := by
    rw [CFC.sqrt_eq_rpow]
    exact CFC.rpow_eq_cfc_real hA'.nonneg
  have hsqrtB : CFC.sqrt
      (epsilon • (1 : SquareMatrix n) +
        ∑ t : Fin T, TensorsProofSupport.Matrix.rightGram (G t)) =
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ))
        (epsilon • (1 : SquareMatrix n) +
          ∑ t : Fin T, TensorsProofSupport.Matrix.rightGram (G t)) := by
    rw [CFC.sqrt_eq_rpow]
    exact CFC.rpow_eq_cfc_real hB'.nonneg
  rw [hsqrtA, hsqrtB] at h
  simpa only [positiveRankReal, one_div, vectorOuter, Matrix.vecMulVec, matrixVec,
    matrixGramLeft, matrixGramRight, TensorsProofSupport.Matrix.leftGram,
    TensorsProofSupport.Matrix.rightGram, Matrix.leftGram, Matrix.rightGram,
    matrixPower, psdMatrixPower_eq_cfc] using h

private def modeIndexEquiv_for_Lemma11 {k : Nat} {dims : Fin k → Nat}
    (i : Fin k) : Fin (dims i) × ModeColumn dims i ≃ MultiIndex dims where
  toFun := fun rc => (fun row col => (Equiv.piSplitAt i (fun j => Fin (dims j))).symm (row, col)) rc.1 rc.2
  invFun := fun idx => (idx i, fun j => idx j.1)
  left_inv := by
    intro rc
    rcases rc with ⟨row, col⟩
    apply Prod.ext
    · simp [Equiv.piSplitAt]
    · funext j
      simp [Equiv.piSplitAt, j.property]
  right_inv := by
    intro idx
    funext j
    by_cases h : j = i
    · subst j
      simp [Equiv.piSplitAt]
    · simp [Equiv.piSplitAt, h]

private theorem modeColumn_identity_eq_prod_for_Lemma11 {k : Nat} {dims : Fin k → Nat}
    {i : Fin k} (c c' : ModeColumn dims i) :
    (1 : GenericSquare (ModeColumn dims i)) c c' =
      ∏ j : {j : Fin k // j ≠ i}, if c j = c' j then (1 : ℝ) else 0 := by
  classical
  by_cases h : c = c'
  · subst h
    simp
  · have hne : ∃ j : {j : Fin k // j ≠ i}, c j ≠ c' j := by
      by_contra hnone
      apply h
      funext j
      by_contra hj
      exact hnone ⟨j, hj⟩
    rcases hne with ⟨j, hj⟩
    rw [Matrix.one_apply_ne h]
    exact (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])).symm

private theorem mode_embedded_reindex_eq_kron_for_Lemma11 {k : Nat} {dims : Fin k → Nat}
    (i : Fin k) (B : SquareMatrix (dims i))
    (rc rc' : Fin (dims i) × ModeColumn dims i) :
    modeEmbeddedMatrix i B ((fun row col => (Equiv.piSplitAt i (fun j => Fin (dims j))).symm (row, col)) rc.1 rc.2) ((fun row col => (Equiv.piSplitAt i (fun j => Fin (dims j))).symm (row, col)) rc'.1 rc'.2) =
      (B ⊗ₖ (1 : GenericSquare (ModeColumn dims i))) rc rc' := by
  classical
  rcases rc with ⟨row, col⟩
  rcases rc' with ⟨row', col'⟩
  have hprod :
      (∏ x : {j : Fin k // j ≠ i},
          if ((fun row col => (Equiv.piSplitAt i (fun j => Fin (dims j))).symm (row, col)) row col) x.1 = ((fun row col => (Equiv.piSplitAt i (fun j => Fin (dims j))).symm (row, col)) row' col') x.1 then (1 : ℝ) else 0) =
        ∏ x : {j : Fin k // j ≠ i}, if col x = col' x then (1 : ℝ) else 0 := by
    apply Finset.prod_congr rfl
    intro x hx
    simp [Equiv.piSplitAt, x.property]
  rw [Matrix.kroneckerMap_apply, modeColumn_identity_eq_prod_for_Lemma11]
  unfold modeEmbeddedMatrix SOptLib.tensorModeEmbedding
  rw [hprod]
  simp [Equiv.piSplitAt]

private theorem modeEmbeddedMatrix_posSemidef_for_Lemma11 {k : Nat} {dims : Fin k → Nat}
    (i : Fin k) (B : SquareMatrix (dims i)) (hB : B.PosSemidef) :
    (modeEmbeddedMatrix i B).PosSemidef := by
  exact SOptLib.tensorModeEmbedding_posSemidef (dims := fun j => Fin (dims j)) i B hB

private theorem reindexAlgEquiv_kron_eq_modeEmbeddedMatrix_for_Lemma11 {k : Nat}
    {dims : Fin k → Nat} (i : Fin k) (B : SquareMatrix (dims i)) :
    Matrix.reindexAlgEquiv ℝ ℝ (modeIndexEquiv_for_Lemma11 (dims := dims) i)
        (B ⊗ₖ (1 : GenericSquare (ModeColumn dims i))) =
      modeEmbeddedMatrix i B := by
  classical
  let e := modeIndexEquiv_for_Lemma11 (dims := dims) i
  ext idx idx'
  calc
    Matrix.reindexAlgEquiv ℝ ℝ e
        (B ⊗ₖ (1 : GenericSquare (ModeColumn dims i))) idx idx' =
      (B ⊗ₖ (1 : GenericSquare (ModeColumn dims i))) (e.symm idx) (e.symm idx') := by
        rfl
    _ = modeEmbeddedMatrix i B (e (e.symm idx)) (e (e.symm idx')) := by
        change
          (B ⊗ₖ (1 : GenericSquare (ModeColumn dims i))) (e.symm idx) (e.symm idx') =
            modeEmbeddedMatrix i B
              ((fun row col => (Equiv.piSplitAt i (fun j => Fin (dims j))).symm (row, col)) (e.symm idx).1 (e.symm idx).2)
              ((fun row col => (Equiv.piSplitAt i (fun j => Fin (dims j))).symm (row, col)) (e.symm idx').1 (e.symm idx').2)
        exact (mode_embedded_reindex_eq_kron_for_Lemma11 i B
          (e.symm idx) (e.symm idx')).symm
    _ = modeEmbeddedMatrix i B idx idx' := by
        simpa [e.right_inv idx, e.right_inv idx']

private theorem psdMatrixPower_modeEmbeddedMatrix_for_Lemma11 {k : Nat}
    {dims : Fin k → Nat} (i : Fin k) (B : SquareMatrix (dims i)) (s : ℝ)
    (hB : B.PosSemidef) :
    psdMatrixPower (modeEmbeddedMatrix i B) s
        (modeEmbeddedMatrix_posSemidef_for_Lemma11 i B hB) =
      modeEmbeddedMatrix i (matrixPower B s hB) := by
  simpa [modeEmbeddedMatrix, matrixPower, psdMatrixPower_eq_cfc] using
    (SOptLib.tensorModeEmbedding_cfc_rpow
      (dims := fun j => Fin (dims j)) i B s hB.1)

private theorem scaled_modeEmbeddedMatrix_posSemidef_for_Lemma11 {k : Nat}
    {dims : Fin k → Nat} (i : Fin k) (r : PosNat) (B : SquareMatrix (dims i))
    (hB : B.PosSemidef) :
    (positiveRankReal r • modeEmbeddedMatrix i B).PosSemidef := by
  exact (modeEmbeddedMatrix_posSemidef_for_Lemma11 i B hB).smul
    (le_of_lt (positiveRankReal_pos r))

private theorem tensorKronecker_mul_for_Lemma11 {k : Nat} {dims : Fin k → Nat}
    (X Y : (i : Fin k) → SquareMatrix (dims i)) :
    tensorKronecker X * tensorKronecker Y =
      tensorKronecker (fun i => X i * Y i) := by
  ext a b
  have h := congrFun (congrFun (SOptLib.tensorKronecker_mul X Y) a) b
  simp only [tensorKronecker, SOptLib.tensorKronecker_apply, Matrix.mul_apply] at h ⊢
  rw [← h]
  apply Finset.sum_congr
  · ext x
    simp
  · intro x _hx
    rfl

private theorem modeEmbeddedMatrix_eq_tensorKronecker_single_for_Lemma11 {k : Nat}
    {dims : Fin k → Nat} (i : Fin k) (B : SquareMatrix (dims i)) :
    modeEmbeddedMatrix i B =
      tensorKronecker
        (fun j : Fin k =>
          if h : j = i then
            by
              subst j
              exact B
          else
            (1 : SquareMatrix (dims j))) := by
  exact SOptLib.tensorModeEmbedding_eq_tensorKronecker_single
    (dims := fun j => Fin (dims j)) i B

private theorem tensorKronecker_one_for_Lemma11 {k : Nat} {dims : Fin k → Nat} :
    tensorKronecker (fun i : Fin k => (1 : SquareMatrix (dims i))) =
      (1 : GenericSquare (MultiIndex dims)) := by
  exact SOptLib.tensorKronecker_one

private theorem orderedMatrixProductNat_reindexed_modeEmbeddedMatrix_for_Lemma11 {k N : Nat}
    {dims : Fin k → Nat} (e : MultiIndex dims ≃ Fin N)
    (B : (i : Fin k) → SquareMatrix (dims i)) :
    ∀ a : Nat, a ≤ k →
      orderedMatrixProductNat
          (fun i : Fin k => Matrix.reindexAlgEquiv ℝ ℝ e (modeEmbeddedMatrix i (B i))) a =
        Matrix.reindexAlgEquiv ℝ ℝ e
          (tensorKronecker
            (fun j : Fin k =>
              if _h : j.1 < a then B j else (1 : SquareMatrix (dims j)))) := by
  intro a ha
  induction a with
  | zero =>
      simp [orderedMatrixProductNat, tensorKronecker_one_for_Lemma11]
  | succ a ih =>
      have hlt : a < k := Nat.lt_of_succ_le ha
      have hle : a ≤ k := Nat.le_of_succ_le ha
      calc
        orderedMatrixProductNat
            (fun i : Fin k => Matrix.reindexAlgEquiv ℝ ℝ e (modeEmbeddedMatrix i (B i)))
            (a + 1) =
            orderedMatrixProductNat
              (fun i : Fin k => Matrix.reindexAlgEquiv ℝ ℝ e (modeEmbeddedMatrix i (B i))) a *
              Matrix.reindexAlgEquiv ℝ ℝ e
                (modeEmbeddedMatrix ⟨a, hlt⟩ (B ⟨a, hlt⟩)) := by
              simp [orderedMatrixProductNat, hlt]
        _ =
            Matrix.reindexAlgEquiv ℝ ℝ e
              (tensorKronecker
              (fun j : Fin k =>
                if _h : j.1 < a then B j else (1 : SquareMatrix (dims j)))) *
              Matrix.reindexAlgEquiv ℝ ℝ e
                (modeEmbeddedMatrix ⟨a, hlt⟩ (B ⟨a, hlt⟩)) := by
              rw [ih hle]
        _ =
            Matrix.reindexAlgEquiv ℝ ℝ e
              (tensorKronecker
                (fun j : Fin k =>
                  if _h : j.1 < a + 1 then B j else (1 : SquareMatrix (dims j)))) := by
              rw [← Matrix.reindexAlgEquiv_mul]
              apply congrArg (Matrix.reindexAlgEquiv ℝ ℝ e)
              rw [modeEmbeddedMatrix_eq_tensorKronecker_single_for_Lemma11,
                tensorKronecker_mul_for_Lemma11]
              apply congrArg tensorKronecker
              funext j
              by_cases hja : j.1 < a
              · have hne : j ≠ ⟨a, hlt⟩ := by
                  intro h
                  have : j.1 = a := congrArg Fin.val h
                  omega
                simp [hja, Nat.lt_trans hja (Nat.lt_succ_self a), hne]
              · by_cases hjeq : j = ⟨a, hlt⟩
                · subst j
                  simp
                · have hnot : ¬ j.1 < a + 1 := by
                    intro hj
                    have hle_a : j.1 ≤ a := Nat.le_of_lt_succ hj
                    have hge_a : a ≤ j.1 := Nat.le_of_not_gt hja
                    have hval : j.1 = a := le_antisymm hle_a hge_a
                    apply hjeq
                    exact Fin.ext hval
                  simp [hja, hjeq, hnot]

private theorem orderedMatrixProduct_reindexed_modeEmbeddedMatrix_for_Lemma11 {k N : Nat}
    {dims : Fin k → Nat} (e : MultiIndex dims ≃ Fin N)
    (B : (i : Fin k) → SquareMatrix (dims i)) :
    orderedMatrixProduct
        (fun i : Fin k => Matrix.reindexAlgEquiv ℝ ℝ e (modeEmbeddedMatrix i (B i))) =
      Matrix.reindexAlgEquiv ℝ ℝ e (tensorKronecker B) := by
  simpa only [orderedMatrixProduct_eq_list_prod, modeEmbeddedMatrix, tensorKronecker] using
    (SOptLib.List.prod_ofFn_tensorModeEmbedding_eq_tensorKronecker
      (R := ℝ) (dims := fun i : Fin k => Fin (dims i))
      (modeOrder := (OrderIso.refl (Fin k)).toEquiv) (e := e) (B := B))

private theorem modeEmbeddedMatrix_comm_of_ne_for_Lemma11 {k : Nat}
    {dims : Fin k → Nat} (i j : Fin k) (hij : i ≠ j)
    (B : SquareMatrix (dims i)) (C : SquareMatrix (dims j)) :
    modeEmbeddedMatrix i B * modeEmbeddedMatrix j C =
      modeEmbeddedMatrix j C * modeEmbeddedMatrix i B := by
  exact SOptLib.tensorModeEmbedding_comm_of_ne (dims := fun l => Fin (dims l)) i j hij B C

private theorem scaled_modeEmbeddedMatrix_comm_for_Lemma11 {k : Nat}
    {dims : Fin k → Nat} (rankBound : Fin k → PosNat)
    (A : (i : Fin k) → SquareMatrix (dims i)) :
    ∀ i j : Fin k,
      (positiveRankReal (rankBound i) • modeEmbeddedMatrix i (A i)) *
          (positiveRankReal (rankBound j) • modeEmbeddedMatrix j (A j)) =
        (positiveRankReal (rankBound j) • modeEmbeddedMatrix j (A j)) *
          (positiveRankReal (rankBound i) • modeEmbeddedMatrix i (A i)) := by
  classical
  intro i j
  by_cases hij : i = j
  · subst j
    rfl
  · calc
      (positiveRankReal (rankBound i) • modeEmbeddedMatrix i (A i)) *
          (positiveRankReal (rankBound j) • modeEmbeddedMatrix j (A j)) =
        (positiveRankReal (rankBound i) * positiveRankReal (rankBound j)) •
          (modeEmbeddedMatrix i (A i) * modeEmbeddedMatrix j (A j)) := by
            ext a b
            simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
      _ =
        (positiveRankReal (rankBound j) * positiveRankReal (rankBound i)) •
          (modeEmbeddedMatrix j (A j) * modeEmbeddedMatrix i (A i)) := by
            rw [modeEmbeddedMatrix_comm_of_ne_for_Lemma11 i j hij]
            ring_nf
      _ =
        (positiveRankReal (rankBound j) • modeEmbeddedMatrix j (A j)) *
          (positiveRankReal (rankBound i) • modeEmbeddedMatrix i (A i)) := by
            ext a b
            simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]

private theorem rankGeometricMean_eq_prod_rpow_for_Lemma11 {k : Nat}
    [Nonempty (Fin k)] (rankBound : Fin k → PosNat) :
    (∏ i : Fin k, positiveRankReal (rankBound i) ^ (1 / (k : ℝ))) =
      TensorAlgorithm2.rankGeometricMean rankBound := by
  simpa [positiveRankReal, TensorAlgorithm2.rankGeometricMean] using
    (SOptLib.positiveNatGeometricMean_eq_prod_rpow rankBound).symm

private theorem tensor_rank_domination_M_posSemidef {k T : Nat} {dims : Fin k → Nat}
    (G : Fin T → TensorSpace dims) (epsilon : ℝ) (heps : 0 ≤ epsilon) :
    (epsilon • (1 : GenericSquare (MultiIndex dims)) +
        ∑ t : Fin T, vectorOuter ( (G t))).PosSemidef := by
  have h0 : (epsilon • (1 : GenericSquare (MultiIndex dims))).PosSemidef :=
    Matrix.PosSemidef.one.smul heps
  have hsum : (∑ t : Fin T, vectorOuter ( (G t))).PosSemidef :=
    finset_sum_generic_posSemidef_of_forall Finset.univ
      (fun t : Fin T => @vectorOuter (MultiIndex dims) ( (G t)))
      (by
        intro t _ht
        exact vectorOuter_posSemidef (ι := MultiIndex dims) ( (G t)))
  exact h0.add hsum

private theorem same_lower_ando_geometric_mean {q n : Nat} [Nonempty (Fin q)]
    (M : SquareMatrix n) (Y : Fin q → SquareMatrix n)
    (hM : M.PosSemidef) (hY : ∀ i, (Y i).PosSemidef)
    (hMY : ∀ i, M ≤ Y i)
    (hYcomm : ∀ i j, Y i * Y j = Y j * Y i) :
    orderedMatrixProduct (fun i : Fin q => matrixPower M (1 / (q : ℝ)) hM) ≤
      orderedMatrixProduct (fun i : Fin q =>
        matrixPower (Y i) (1 / (q : ℝ)) (hY i)) := by
  classical
  let X : Fin q → SquareMatrix n := fun _ => M
  let alpha : Fin q → ℝ := fun _ => 1 / (q : ℝ)
  have hX : ∀ i, (X i).PosSemidef := by
    intro i
    simpa [X] using hM
  have hXY : ∀ i, X i ≤ Y i := by
    intro i
    simpa [X] using hMY i
  have hXcomm : ∀ i j, X i * X j = X j * X i := by
    intro i j
    simp [X]
  have halpha_nonneg : ∀ i, 0 ≤ alpha i := by
    intro i
    dsimp [alpha]
    positivity
  have hq_pos : 0 < q := by
    let i : Fin q := Classical.choice inferInstance
    exact Nat.lt_of_le_of_lt (Nat.zero_le i.1) i.2
  have hq_ne : (q : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hq_pos)
  have halpha_sum : (∑ i : Fin q, alpha i) = 1 := by
    calc
      (∑ i : Fin q, alpha i) = (q : ℝ) * (1 / (q : ℝ)) := by
        simp [alpha]
      _ = 1 := by
        field_simp [hq_ne]
  simpa [X, alpha] using
    Lemma_5_Ando_geometric_mean X Y alpha hX hY hXY hXcomm hYcomm
      halpha_nonneg halpha_sum

private theorem generic_column_left_rank_domination {m : Nat} {κ : Type*}
    [Fintype κ] [DecidableEq κ] (G : Matrix (Fin m) κ ℝ) (r : PosNat)
    (hrank : G.rank ≤ r.1) :
    (1 / positiveRankReal r) •
        vectorOuter (fun rc : Fin m × κ => G rc.1 rc.2) ≤
      ((G * G.transpose) ⊗ₖ (1 : GenericSquare κ)) := by
  classical
  let eκ : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  let Gf : MatrixSpace m (Fintype.card κ) := fun row col => G row (eκ.symm col)
  let ep : Fin m × κ ≃ FlatMatrixIndex m (Fintype.card κ) :=
    { toFun := fun rc => (rc.1, eκ rc.2)
      invFun := fun ij => (ij.1, eκ.symm ij.2)
      left_inv := by
        intro rc
        rcases rc with ⟨row, col⟩
        simp
      right_inv := by
        intro ij
        rcases ij with ⟨row, col⟩
        simp }
  have hrankf : Gf.rank ≤ r.1 := by
    have hrank_eq : Gf.rank = G.rank := by
      simpa [Gf, Matrix.submatrix] using
        (Matrix.rank_submatrix (A := G) (Equiv.refl (Fin m)) eκ.symm)
    simpa [hrank_eq] using hrank
  have h9 :
      (1 / positiveRankReal r) • vectorOuter (matrixVec Gf) ≤
        (matrixGramLeft Gf ⊗ₖ (1 : SquareMatrix (Fintype.card κ))) :=
    (Lemma_9_single_matrix_rank_domination Gf r hrankf).2
  have hleft_reindex :
      Matrix.reindexAlgEquiv ℝ ℝ ep
          ((1 / positiveRankReal r) •
            vectorOuter (fun rc : Fin m × κ => G rc.1 rc.2)) =
        (1 / positiveRankReal r) • vectorOuter (matrixVec Gf) := by
    ext ij kl
    rcases ij with ⟨row, col⟩
    rcases kl with ⟨row', col'⟩
    simp [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, ep, Gf, matrixVec,
      vectorOuter]
  have hright_reindex :
      Matrix.reindexAlgEquiv ℝ ℝ ep
          ((G * G.transpose) ⊗ₖ (1 : GenericSquare κ)) =
        (matrixGramLeft Gf ⊗ₖ (1 : SquareMatrix (Fintype.card κ))) := by
    ext ij kl
    rcases ij with ⟨row, col⟩
    rcases kl with ⟨row', col'⟩
    by_cases hcol : col = col'
    · subst col'
      have hsum :
          (∑ x : κ, G row x * G row' x) =
            ∑ x : Fin (Fintype.card κ), G row (eκ.symm x) * G row' (eκ.symm x) := by
        simpa using
          (eκ.sum_comp
            (fun x : Fin (Fintype.card κ) => G row (eκ.symm x) * G row' (eκ.symm x)))
      simp [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, ep, Matrix.kroneckerMap_apply,
        Matrix.mul_apply, Matrix.transpose_apply, matrixGramLeft, Gf, hsum]
    · have hne : eκ.symm col ≠ eκ.symm col' := by
        intro h
        exact hcol (eκ.symm.injective h)
      simp [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, ep, Matrix.kroneckerMap_apply,
        hcol, hne]
  have hreindexed :
      Matrix.reindexAlgEquiv ℝ ℝ ep
          ((1 / positiveRankReal r) •
            vectorOuter (fun rc : Fin m × κ => G rc.1 rc.2)) ≤
        Matrix.reindexAlgEquiv ℝ ℝ ep
          ((G * G.transpose) ⊗ₖ (1 : GenericSquare κ)) := by
    simpa [hleft_reindex, hright_reindex] using h9
  exact
    (matrix_le_reindexAlgEquiv_iff ep
      ((1 / positiveRankReal r) •
        vectorOuter (fun rc : Fin m × κ => G rc.1 rc.2))
      ((G * G.transpose) ⊗ₖ (1 : GenericSquare κ))).2 hreindexed

private theorem tensor_single_mode_rank_bound {k : Nat} {dims : Fin k → Nat}
    (G : TensorSpace dims) (i : Fin k) (r : PosNat)
    (hrank : (matricization G i).rank ≤ r.1) :
    (1 / positiveRankReal r) • vectorOuter ( G) ≤
      modeEmbeddedMatrix i (tensorContraction G i) := by
  simpa [positiveRankReal, one_div, vectorOuter, modeEmbeddedMatrix,
    tensorContraction] using
    (SOptLib.inv_rank_smul_tensorVectorization_vecMulVec_le_tensorModeEmbedding_contraction
      (dims := fun j : Fin k => Fin (dims j)) G i r.1 r.2 hrank)

private theorem modeEmbeddedMatrix_add_for_Lemma11 {k : Nat} {dims : Fin k → Nat}
    (i : Fin k) (B C : SquareMatrix (dims i)) :
    modeEmbeddedMatrix i (B + C) =
      modeEmbeddedMatrix i B + modeEmbeddedMatrix i C := by
  ext a b
  simp [modeEmbeddedMatrix, add_mul]

private theorem modeEmbeddedMatrix_smul_for_Lemma11 {k : Nat} {dims : Fin k → Nat}
    (i : Fin k) (c : ℝ) (B : SquareMatrix (dims i)) :
    modeEmbeddedMatrix i (c • B) = c • modeEmbeddedMatrix i B := by
  ext a b
  simp [modeEmbeddedMatrix, mul_assoc]

private theorem modeEmbeddedMatrix_sum_for_Lemma11 {k T : Nat} {dims : Fin k → Nat}
    (i : Fin k) (B : Fin T → SquareMatrix (dims i)) :
    modeEmbeddedMatrix i (∑ t : Fin T, B t) =
      ∑ t : Fin T, modeEmbeddedMatrix i (B t) := by
  ext a b
  simp [modeEmbeddedMatrix, Matrix.sum_apply, Finset.sum_mul]

private theorem modeEmbeddedMatrix_one_for_Lemma11 {k : Nat} {dims : Fin k → Nat}
    (i : Fin k) :
    modeEmbeddedMatrix i (1 : SquareMatrix (dims i)) =
      (1 : GenericSquare (MultiIndex dims)) := by
  exact SOptLib.tensorModeEmbedding_one (dims := fun j => Fin (dims j)) i

private theorem tensor_mode_accumulated_bound {k T : Nat} {dims : Fin k → Nat}
    (G : Fin T → TensorSpace dims) (i : Fin k) (r : PosNat) (epsilon : ℝ)
    (hrank : ∀ t : Fin T, (matricization (G t) i).rank ≤ r.1)
    (heps : 0 ≤ epsilon) :
    epsilon • (1 : GenericSquare (MultiIndex dims)) +
        (∑ t : Fin T, vectorOuter ( (G t))) ≤
      positiveRankReal r •
        modeEmbeddedMatrix i
          (epsilon • (1 : SquareMatrix (dims i)) +
            ∑ t : Fin T, tensorContraction (G t) i) := by
  simpa [positiveRankReal, vectorOuter, modeEmbeddedMatrix, tensorContraction] using
    (SOptLib.regularized_tensor_vecMulVec_sum_le_rank_smul_tensorModeEmbedding_contraction_sum
      (dims := fun j : Fin k => Fin (dims j)) G i r.1 epsilon r.2 hrank heps)

/- Book JSON key_lemmas.Lemma_11_tensor_rank_domination. -/
theorem Lemma_11_tensor_rank_domination {k T : Nat} {dims : Fin k → Nat}
    (G : Fin T → TensorSpace dims) (rankBound : Fin k → PosNat) (epsilon : ℝ)
    [Nonempty (Fin k)]
    (hrank : ∀ i : Fin k, ∀ t : Fin T, (matricization (G t) i).rank ≤ (rankBound i).1)
    (heps : 0 ≤ epsilon) :
    epsilon • (1 : GenericSquare (MultiIndex dims)) +
        (∑ t : Fin T, vectorOuter ( (G t))) ≤
      (TensorAlgorithm2.rankGeometricMean rankBound) •
        tensorKronecker
          (fun i => matrixPower
            (epsilon • (1 : SquareMatrix (dims i)) + ∑ t : Fin T, tensorContraction (G t) i)
            (1 / (k : ℝ)) (accumulated_tensor_contraction_psd_from_epsilon G epsilon heps i)) := by
  classical
  let M : GenericSquare (MultiIndex dims) :=
    epsilon • (1 : GenericSquare (MultiIndex dims)) +
      ∑ t : Fin T, vectorOuter ( (G t))
  let A : (i : Fin k) → SquareMatrix (dims i) :=
    fun i => epsilon • (1 : SquareMatrix (dims i)) +
      ∑ t : Fin T, tensorContraction (G t) i
  have hmode :
      ∀ i : Fin k, M ≤
        positiveRankReal (rankBound i) • modeEmbeddedMatrix i (A i) := by
    intro i
    simpa [M, A] using
      tensor_mode_accumulated_bound G i (rankBound i) epsilon (hrank i) heps
  have hfinal :
      M ≤
        (TensorAlgorithm2.rankGeometricMean rankBound) •
          tensorKronecker
            (fun i => matrixPower (A i) (1 / (k : ℝ))
              (by
                simpa [A] using
                  accumulated_tensor_contraction_psd_from_epsilon G epsilon heps i)) := by
    have hMpsd : M.PosSemidef := by
      simpa [M] using tensor_rank_domination_M_posSemidef G epsilon heps
    have hApsd : ∀ i : Fin k, (A i).PosSemidef := by
      intro i
      simpa [A] using accumulated_tensor_contraction_psd_from_epsilon G epsilon heps i
    have hYpsd :
        ∀ i : Fin k,
          (positiveRankReal (rankBound i) • modeEmbeddedMatrix i (A i)).PosSemidef := by
      intro i
      exact scaled_modeEmbeddedMatrix_posSemidef_for_Lemma11 i (rankBound i) (A i) (hApsd i)
    let Y : Fin k → GenericSquare (MultiIndex dims) :=
      fun i => positiveRankReal (rankBound i) • modeEmbeddedMatrix i (A i)
    have hYcomm : ∀ i j : Fin k, Y i * Y j = Y j * Y i := by
      simpa [Y] using scaled_modeEmbeddedMatrix_comm_for_Lemma11 rankBound A
    let e : MultiIndex dims ≃ Fin (Fintype.card (MultiIndex dims)) :=
      Fintype.equivFin (MultiIndex dims)
    let R : GenericSquare (MultiIndex dims) →
        SquareMatrix (Fintype.card (MultiIndex dims)) :=
      fun Z => Matrix.reindexAlgEquiv ℝ ℝ e Z
    have hMpsdFin : (R M).PosSemidef := by
      simpa [R, e, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply] using
        ((Matrix.posSemidef_submatrix_equiv (M := M) e.symm).2 hMpsd)
    have hYpsdFin : ∀ i : Fin k, (R (Y i)).PosSemidef := by
      intro i
      simpa [R, e, Y, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply] using
        ((Matrix.posSemidef_submatrix_equiv (M := Y i) e.symm).2 (by
          simpa [Y] using hYpsd i))
    have hmodeFin : ∀ i : Fin k, R M ≤ R (Y i) := by
      intro i
      simpa [R, Y] using
        (matrix_le_reindexAlgEquiv_iff e M (Y i)).1 (by
          simpa [Y] using hmode i)
    have hYcommFin : ∀ i j : Fin k, R (Y i) * R (Y j) = R (Y j) * R (Y i) := by
      intro i j
      have h := congrArg (fun Z => Matrix.reindexAlgEquiv ℝ ℝ e Z) (hYcomm i j)
      simpa [R, Matrix.reindexAlgEquiv_mul] using h
    have handoFin :
        orderedMatrixProduct
            (fun i : Fin k => matrixPower (R M) (1 / (k : ℝ)) hMpsdFin) ≤
          orderedMatrixProduct
            (fun i : Fin k => matrixPower (R (Y i)) (1 / (k : ℝ)) (hYpsdFin i)) := by
      exact same_lower_ando_geometric_mean
        (M := R M) (Y := fun i : Fin k => R (Y i))
        hMpsdFin hYpsdFin hmodeFin hYcommFin
    let finalRhs : GenericSquare (MultiIndex dims) :=
      (TensorAlgorithm2.rankGeometricMean rankBound) •
        tensorKronecker
          (fun i => matrixPower (A i) (1 / (k : ℝ)) (hApsd i))
    have hlower :
        orderedMatrixProduct
            (fun _ : Fin k => matrixPower (R M) (1 / (k : ℝ)) hMpsdFin) =
          R M := by
      exact orderedMatrixProduct_const_matrixPower_inv_card_eq_self (R M) hMpsdFin
    have hupper :
        orderedMatrixProduct
            (fun i : Fin k => matrixPower (R (Y i)) (1 / (k : ℝ)) (hYpsdFin i)) =
          R finalRhs := by
      have hpow_reindex :
          ∀ i : Fin k,
            matrixPower (R (Y i)) (1 / (k : ℝ)) (hYpsdFin i) =
              R (psdMatrixPower (Y i) (1 / (k : ℝ))
                (show (Y i).PosSemidef from by
                  simpa [Y] using hYpsd i)) := by
        intro i
        change
          psdMatrixPower (R (Y i)) (1 / (k : ℝ)) (hYpsdFin i) =
            R (psdMatrixPower (Y i) (1 / (k : ℝ))
              (show (Y i).PosSemidef from by
                simpa [Y] using hYpsd i))
        symm
        simpa [R] using
          psdMatrixPower_reindexAlgEquiv e (Y i) (1 / (k : ℝ))
            (show (Y i).PosSemidef from by
              simpa [Y] using hYpsd i)
            (hYpsdFin i)
      have hupper_reindexed :
          orderedMatrixProduct
              (fun i : Fin k =>
                R (psdMatrixPower (Y i) (1 / (k : ℝ))
                  (show (Y i).PosSemidef from by
                    simpa [Y] using hYpsd i))) =
            R finalRhs := by
        have hpow_scaled :
            ∀ i : Fin k,
              psdMatrixPower (Y i) (1 / (k : ℝ))
                  (show (Y i).PosSemidef from by
                    simpa [Y] using hYpsd i) =
                (positiveRankReal (rankBound i) ^ (1 / (k : ℝ))) •
                  psdMatrixPower (modeEmbeddedMatrix i (A i)) (1 / (k : ℝ))
                    (modeEmbeddedMatrix_posSemidef_for_Lemma11 i (A i) (hApsd i)) := by
          intro i
          have hmodeEmb :
              (modeEmbeddedMatrix i (A i)).PosSemidef :=
            modeEmbeddedMatrix_posSemidef_for_Lemma11 i (A i) (hApsd i)
          have hscaled :
              (positiveRankReal (rankBound i) • modeEmbeddedMatrix i (A i)).PosSemidef := by
            simpa [Y] using hYpsd i
          have hraw :=
            psdMatrixPower_smul_nonneg
              (positiveRankReal (rankBound i)) (1 / (k : ℝ))
              (modeEmbeddedMatrix i (A i)) hmodeEmb
              (le_of_lt (positiveRankReal_pos (rankBound i))) hscaled
          simpa [Y] using hraw
        have hupper_scaled :
            orderedMatrixProduct
                (fun i : Fin k =>
                  R ((positiveRankReal (rankBound i) ^ (1 / (k : ℝ))) •
                    psdMatrixPower (modeEmbeddedMatrix i (A i)) (1 / (k : ℝ))
                      (modeEmbeddedMatrix_posSemidef_for_Lemma11 i (A i) (hApsd i)))) =
              R finalRhs := by
          have hnormalized :=
            SOptLib.List.prod_tensorModeEmbedding_cfc_rpow_smul
              (modeOrder := Equiv.refl (Fin k)) (e := e)
              (c := fun i => positiveRankReal (rankBound i)) (A := A)
              (s := 1 / (k : ℝ)) (fun i => (hApsd i).1)
          have hscalar :
              (∏ i : Fin k, positiveRankReal (rankBound i) ^ (1 / (k : ℝ))) =
                TensorAlgorithm2.rankGeometricMean rankBound := by
            simpa using rankGeometricMean_eq_prod_rpow_for_Lemma11 rankBound
          have hnormalized' :
              (List.ofFn (fun i : Fin k =>
                R ((positiveRankReal (rankBound i) ^ (1 / (k : ℝ))) •
                  cfc (R := ℝ) (p := IsSelfAdjoint)
                    (fun x : ℝ => x ^ (1 / (k : ℝ)))
                    (SOptLib.tensorModeEmbedding i (A i))))).prod =
                R ((∏ i : Fin k,
                    positiveRankReal (rankBound i) ^ (1 / (k : ℝ))) •
                  SOptLib.tensorKronecker (fun i =>
                    cfc (R := ℝ) (p := IsSelfAdjoint)
                      (fun x : ℝ => x ^ (1 / (k : ℝ))) (A i))) := by
            simpa only [Equiv.refl_apply] using hnormalized
          rw [orderedMatrixProduct_eq_list_prod]
          simp only [psdMatrixPower_eq_cfc, modeEmbeddedMatrix]
          rw [hnormalized']
          apply congrArg R
          rw [hscalar]
          simp only [finalRhs, tensorKronecker, matrixPower, psdMatrixPower_eq_cfc]
        have hfun :
            (fun i : Fin k =>
              R (psdMatrixPower (Y i) (1 / (k : ℝ))
                (show (Y i).PosSemidef from by
                  simpa [Y] using hYpsd i))) =
              (fun i : Fin k =>
                R ((positiveRankReal (rankBound i) ^ (1 / (k : ℝ))) •
                  psdMatrixPower (modeEmbeddedMatrix i (A i)) (1 / (k : ℝ))
                    (modeEmbeddedMatrix_posSemidef_for_Lemma11 i (A i) (hApsd i)))) := by
          funext i
          rw [hpow_scaled i]
        rw [hfun]
        exact hupper_scaled
      have hfun :
          (fun i : Fin k => matrixPower (R (Y i)) (1 / (k : ℝ)) (hYpsdFin i)) =
            (fun i : Fin k =>
              R (psdMatrixPower (Y i) (1 / (k : ℝ))
                (show (Y i).PosSemidef from by
                  simpa [Y] using hYpsd i))) := by
        funext i
        exact hpow_reindex i
      rw [hfun]
      exact hupper_reindexed
    have hfin : R M ≤ R finalRhs := by
      have h := handoFin
      rw [hlower, hupper] at h
      exact h
    exact (matrix_le_reindexAlgEquiv_iff e M finalRhs).2 hfin
  simpa [M, A] using hfinal

/- Book JSON key_lemmas.Lemma_12_tensor_kron_vec. -/
private theorem multiIndex_sum_split_mode {k : Nat} {dims : Fin k → Nat}
    (i : Fin k) (F : MultiIndex dims → ℝ) :
    (∑ idx : MultiIndex dims, F idx) =
      ∑ row : Fin (dims i), ∑ col : ModeColumn dims i, F ((fun row col => (Equiv.piSplitAt i (fun j => Fin (dims j))).symm (row, col)) row col) := by
  simpa only using
    (SOptLib.sum_tensorIndex_eq_sum_mode_coordinate_complement
      (dims := fun j => Fin (dims j)) i F)

private theorem multiIndex_selected_delta_sum {k : Nat} {dims : Fin k → Nat}
    (i : Fin k) (c : Fin (dims i) → ℝ) (B : MultiIndex dims → ℝ) :
    (∑ s : Fin (dims i),
        c s * ∑ j : MultiIndex dims, (if j i = s then (1 : ℝ) else 0) * B j) =
      ∑ j : MultiIndex dims, c (j i) * B j := by
  exact Fintype.sum_selected_pi_kroneckerDelta_mul i c B

private theorem prod_univ_split_selected_mode {k : Nat} (i : Fin k) (f : Fin k → ℝ) :
    (∏ j : Fin k, f j) = f i * ∏ j : {j : Fin k // j ≠ i}, f j.1 := by
  classical
  have hcompl :
      (∏ j ∈ (Finset.univ : Finset (Fin k)).erase i, f j) =
        ∏ j : {j : Fin k // j ≠ i}, f j.1 := by
    exact Finset.prod_subtype ((Finset.univ : Finset (Fin k)).erase i) (by intro j; simp) f
  rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin k)) f (Finset.mem_univ i),
    hcompl]

private theorem prefix_product_replaceIndex_selected_delta {k : Nat} {dims : Fin k → Nat}
    (M : (i : Fin k) → SquareMatrix (dims i)) (idx : MultiIndex dims)
    (q : Nat) (hq : q < k) (s : Fin (dims ⟨q, hq⟩)) (j : MultiIndex dims) :
    (∏ i : Fin k,
        if i.1 < q then M i (replaceIndex idx ⟨q, hq⟩ s i) (j i)
        else if j i = replaceIndex idx ⟨q, hq⟩ s i then (1 : ℝ) else 0) =
      (if j ⟨q, hq⟩ = s then (1 : ℝ) else 0) *
        (∏ i : Fin k,
          if i.1 < q then M i (idx i) (j i)
          else if i = ⟨q, hq⟩ then (1 : ℝ)
          else if j i = idx i then (1 : ℝ) else 0) := by
  classical
  rw [prod_univ_split_selected_mode ⟨q, hq⟩
      (fun i : Fin k =>
        if i.1 < q then M i (replaceIndex idx ⟨q, hq⟩ s i) (j i)
        else if j i = replaceIndex idx ⟨q, hq⟩ s i then (1 : ℝ) else 0)]
  rw [prod_univ_split_selected_mode ⟨q, hq⟩
      (fun i : Fin k =>
        if i.1 < q then M i (idx i) (j i)
        else if i = ⟨q, hq⟩ then (1 : ℝ)
        else if j i = idx i then (1 : ℝ) else 0)]
  have hprod :
      (∏ x : {i : Fin k // i ≠ ⟨q, hq⟩},
          if x.1.1 < q then
            M x.1 (replaceIndex idx ⟨q, hq⟩ s x.1) (j x.1)
          else if j x.1 = replaceIndex idx ⟨q, hq⟩ s x.1 then (1 : ℝ) else 0) =
        (∏ x : {i : Fin k // i ≠ ⟨q, hq⟩},
          if x.1.1 < q then M x.1 (idx x.1) (j x.1)
          else if x.1 = ⟨q, hq⟩ then (1 : ℝ)
          else if j x.1 = idx x.1 then (1 : ℝ) else 0) := by
    apply Finset.prod_congr rfl
    intro x _hx
    simp [replaceIndex, x.property]
  rw [hprod]
  simp [replaceIndex]

private theorem prefix_product_succ_selected_factor {k : Nat} {dims : Fin k → Nat}
    (M : (i : Fin k) → SquareMatrix (dims i)) (idx : MultiIndex dims)
    (q : Nat) (hq : q < k) (j : MultiIndex dims) :
    (∏ i : Fin k,
        if i.1 ≤ q then M i (idx i) (j i)
        else if j i = idx i then (1 : ℝ) else 0) =
      M ⟨q, hq⟩ (idx ⟨q, hq⟩) (j ⟨q, hq⟩) *
        (∏ i : Fin k,
          if i.1 < q then M i (idx i) (j i)
          else if i = ⟨q, hq⟩ then (1 : ℝ)
          else if j i = idx i then (1 : ℝ) else 0) := by
  classical
  rw [prod_univ_split_selected_mode ⟨q, hq⟩
      (fun i : Fin k =>
        if i.1 ≤ q then M i (idx i) (j i)
        else if j i = idx i then (1 : ℝ) else 0)]
  rw [prod_univ_split_selected_mode ⟨q, hq⟩
      (fun i : Fin k =>
        if i.1 < q then M i (idx i) (j i)
        else if i = ⟨q, hq⟩ then (1 : ℝ)
        else if j i = idx i then (1 : ℝ) else 0)]
  have hprod :
      (∏ x : {i : Fin k // i ≠ ⟨q, hq⟩},
          if x.1.1 ≤ q then M x.1 (idx x.1) (j x.1)
          else if j x.1 = idx x.1 then (1 : ℝ) else 0) =
        (∏ x : {i : Fin k // i ≠ ⟨q, hq⟩},
          if x.1.1 < q then M x.1 (idx x.1) (j x.1)
          else if x.1 = ⟨q, hq⟩ then (1 : ℝ)
          else if j x.1 = idx x.1 then (1 : ℝ) else 0) := by
    apply Finset.prod_congr rfl
    intro x _hx
    have hle_iff_lt : x.1.1 ≤ q ↔ x.1.1 < q := by
      constructor
      · intro hxle
        exact Nat.lt_of_le_of_ne hxle (by
          intro hval
          apply x.property
          apply Fin.ext
          exact hval)
      · exact Nat.le_of_lt
    simp [propext hle_iff_lt, x.property]
  rw [hprod]
  simp

private theorem tensorModeProductsNat_coord_prefix {k : Nat} {dims : Fin k → Nat}
    (G : TensorSpace dims) (M : (i : Fin k) → SquareMatrix (dims i)) :
    ∀ q (idx : MultiIndex dims), q ≤ k →
      tensorModeProductsNat G M q idx =
        ∑ j : MultiIndex dims,
          ((∏ i : Fin k,
              if i.1 < q then M i (idx i) (j i)
              else if j i = idx i then (1 : ℝ) else 0) * G j) := by
  simpa [tensorModeProductsNat] using
    (SOptLib.tensorModeProductsPrefix_apply G M)

theorem Lemma_12_tensor_kron_vec {k : Nat} {dims : Fin k → Nat}
    (G : TensorSpace dims) (M : (i : Fin k) → SquareMatrix (dims i)) :
    (tensorKronecker M).mulVec ( G) =  (tensorModeProducts G M) := by
  simpa [tensorKronecker, tensorModeProducts] using
    (SOptLib.tensorKronecker_mulVec_tensorVectorization G M)

private theorem psdMatrixPower_posDef_of_posDef_exp {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (C : GenericSquare ι) (s : ℝ) (hC : C.PosDef) :
    (psdMatrixPower C s hC.posSemidef).PosDef := by
  classical
  let hCpsd : C.PosSemidef := hC.posSemidef
  let U : unitary (GenericSquare ι) := hCpsd.1.eigenvectorUnitary
  let lam : ι → ℝ := hCpsd.1.eigenvalues
  have hdiag : C = (U : GenericSquare ι) *
      Matrix.diagonal (fun i : ι => lam i) * star (U : GenericSquare ι) := by
    simpa [U, lam, hCpsd, Unitary.conjStarAlgAut_apply, Function.comp_def] using
      hCpsd.1.spectral_theorem
  have hpow :
      psdMatrixPower C s hC.posSemidef =
        (U : GenericSquare ι) * Matrix.diagonal (fun i : ι => (lam i) ^ s) *
          star (U : GenericSquare ι) := by
    exact psdMatrixPower_eq_of_unitary_diagonalization C s hC.posSemidef U lam hdiag
      (fun i => hC.posSemidef.eigenvalues_nonneg i)
  have hdiag_pd :
      (Matrix.diagonal (fun i : ι => (lam i) ^ s) : GenericSquare ι).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    exact Real.rpow_pos_of_pos (by simpa [hCpsd, lam] using hC.eigenvalues_pos i) s
  have hUunit : IsUnit (U : GenericSquare ι) := (Unitary.toUnits U).isUnit
  rw [hpow]
  exact (Matrix.IsUnit.posDef_star_right_conjugate_iff hUunit).mpr hdiag_pd

private theorem matrixPower_posDef_of_posDef_exp {n : Nat}
    (C : SquareMatrix n) (s : ℝ) (hC : C.PosDef) (hCpsd : C.PosSemidef) :
    (matrixPower C s hCpsd).PosDef := by
  have hpow :
      matrixPower C s hCpsd = psdMatrixPower C s hC.posSemidef := by
    simp [matrixPower]
  rw [hpow]
  exact psdMatrixPower_posDef_of_posDef_exp C s hC

private theorem pdMatrixPower_neg_eq_inv_matrixPower_pos {n : Nat}
    (C : SquareMatrix n) (s : ℝ) (hCpd : C.PosDef) (hCpsd : C.PosSemidef) :
    pdMatrixPower C (-s) hCpd = (matrixPower C s hCpsd)⁻¹ := by
  classical
  have hroot_congr :
      matrixPower C s hCpsd =
        matrixPower C s hCpd.posSemidef := by
    simpa [matrixPower] using
      (psdMatrixPower_congr (A := C) (B := C) rfl s
        hCpsd hCpd.posSemidef)
  rw [hroot_congr]
  let Root : SquareMatrix n := matrixPower C s hCpd.posSemidef
  let Neg : SquareMatrix n := pdMatrixPower C (-s) hCpd
  have hRoot_pd : Root.PosDef := by
    exact matrixPower_posDef_of_posDef_exp C s hCpd hCpd.posSemidef
  have hmul : Neg * Root = 1 := by
    let U : unitary (SquareMatrix n) := hCpd.posSemidef.1.eigenvectorUnitary
    let lam : Fin n → ℝ := hCpd.posSemidef.1.eigenvalues
    let Dneg : SquareMatrix n := Matrix.diagonal (fun i : Fin n => (lam i) ^ (-s))
    let Droot : SquareMatrix n := Matrix.diagonal (fun i : Fin n => (lam i) ^ s)
    have hdiag : C = (U : SquareMatrix n) *
        Matrix.diagonal (fun i : Fin n => lam i) * star (U : SquareMatrix n) := by
      simpa [U, lam, Unitary.conjStarAlgAut_apply, Function.comp_def] using
        hCpd.posSemidef.1.spectral_theorem
    have hneg :
        Neg = (U : SquareMatrix n) * Dneg * star (U : SquareMatrix n) := by
      simpa [Neg, pdMatrixPower, matrixPower, U, lam, Dneg] using
        psdMatrixPower_eq_of_unitary_diagonalization C (-s)
          hCpd.posSemidef U lam hdiag
          (fun i => hCpd.posSemidef.eigenvalues_nonneg i)
    have hroot :
        Root = (U : SquareMatrix n) * Droot * star (U : SquareMatrix n) := by
      simpa [Root, matrixPower, U, lam, Droot] using
        psdMatrixPower_eq_of_unitary_diagonalization C s
          hCpd.posSemidef U lam hdiag
          (fun i => hCpd.posSemidef.eigenvalues_nonneg i)
    have hDmul : Dneg * Droot = 1 := by
      ext i j
      by_cases hij : i = j
      · subst j
        have hpos : 0 < lam i := by
          simpa [lam] using hCpd.eigenvalues_pos i
        have hpow :
            (lam i) ^ (-s) * (lam i) ^ s = 1 := by
          calc
            (lam i) ^ (-s) * (lam i) ^ s =
                (lam i) ^ (-s + s) := by
                  rw [Real.rpow_add hpos]
            _ = 1 := by
                  rw [show -s + s = 0 by ring, Real.rpow_zero]
        simpa [Dneg, Droot, Matrix.diagonal_mul_diagonal] using hpow
      · simp [Dneg, Droot, Matrix.diagonal_mul_diagonal, hij]
    calc
      Neg * Root =
          ((U : SquareMatrix n) * Dneg * star (U : SquareMatrix n)) *
            ((U : SquareMatrix n) * Droot * star (U : SquareMatrix n)) := by
            rw [hneg, hroot]
      _ = (U : SquareMatrix n) *
            (Dneg * (star (U : SquareMatrix n) * (U : SquareMatrix n)) * Droot) *
            star (U : SquareMatrix n) := by
            noncomm_ring
      _ = (U : SquareMatrix n) * 1 * star (U : SquareMatrix n) := by
            simp [Unitary.coe_star_mul_self, hDmul, mul_assoc]
      _ = 1 := by
            simp [Unitary.coe_mul_star_self]
  have hdet_ne : Root.det ≠ 0 := ne_of_gt hRoot_pd.det_pos
  letI : Invertible Root.det := invertibleOfNonzero hdet_ne
  letI : Invertible Root := Matrix.invertibleOfDetInvertible Root
  calc
    pdMatrixPower C (-s) hCpd = Neg := by rfl
    _ = Neg * 1 := by simp
    _ = Neg * (Root * Root⁻¹) := by rw [Matrix.mul_inv_of_invertible]
    _ = (Neg * Root) * Root⁻¹ := by noncomm_ring
    _ = Root⁻¹ := by rw [hmul]; simp
    _ = (matrixPower C s hCpd.posSemidef)⁻¹ := by rfl

private theorem tensorKronecker_inv_eq_tensorKronecker_pd_neg_power {k : Nat}
    {dims : Fin k → Nat} (C : (i : Fin k) → SquareMatrix (dims i)) (s : ℝ)
    (hCpd : ∀ i : Fin k, (C i).PosDef)
    (hCpsd : ∀ i : Fin k, (C i).PosSemidef)
    (hHpd : (tensorKronecker (fun i : Fin k => matrixPower (C i) s (hCpsd i))).PosDef) :
    (tensorKronecker (fun i : Fin k => matrixPower (C i) s (hCpsd i)))⁻¹ =
      tensorKronecker (fun i : Fin k => pdMatrixPower (C i) (-s) (hCpd i)) := by
  calc
    _ = tensorKronecker (fun i : Fin k => (matrixPower (C i) s (hCpsd i))⁻¹) := by
      simpa [tensorKronecker] using SOptLib.tensorKronecker_nonsing_inv
        (fun i : Fin k => matrixPower (C i) s (hCpsd i))
        (fun i => (matrixPower_posDef_of_posDef_exp (C i) s (hCpd i) (hCpsd i)).isUnit)
    _ = _ := by
      apply congrArg tensorKronecker
      funext i
      exact (pdMatrixPower_neg_eq_inv_matrixPower_pos (C i) s (hCpd i) (hCpsd i)).symm

private theorem tensorKronecker_inverse_mulVec_tensorVec_pd_neg_power {k : Nat}
    {dims : Fin k → Nat} (G : TensorSpace dims)
    (C : (i : Fin k) → SquareMatrix (dims i)) (s : ℝ)
    (hCpd : ∀ i : Fin k, (C i).PosDef)
    (hCpsd : ∀ i : Fin k, (C i).PosSemidef)
    (hHpd : (tensorKronecker (fun i : Fin k => matrixPower (C i) s (hCpsd i))).PosDef) :
    ((tensorKronecker (fun i : Fin k => matrixPower (C i) s (hCpsd i)))⁻¹).mulVec
        ( G) =
       (tensorModeProducts G
        (fun i : Fin k => pdMatrixPower (C i) (-s) (hCpd i))) := by
  classical
  rw [tensorKronecker_inv_eq_tensorKronecker_pd_neg_power C s hCpd hCpsd hHpd]
  exact Lemma_12_tensor_kron_vec G
    (fun i : Fin k => pdMatrixPower (C i) (-s) (hCpd i))

private theorem tensorKronecker_isUnit_of_forall_posDef {k : Nat} {dims : Fin k → Nat}
    (M : (i : Fin k) → SquareMatrix (dims i))
    (hM : ∀ i : Fin k, (M i).PosDef) :
    IsUnit (tensorKronecker M) := by
  classical
  letI : ∀ i : Fin k, DecidableEq (Fin (dims i)) :=
    fun i => instDecidableEqFin (dims i)
  exact SOptLib.tensorKronecker_isUnit_of_forall_isUnit M
    (fun i => (hM i).isUnit)

private def multiIndexConsEquiv {k : Nat} (dims : Fin (k + 1) → Nat) :
    MultiIndex dims ≃ Fin (dims 0) × MultiIndex (fun i : Fin k => dims i.succ) where
  toFun := fun idx => (idx 0, fun i => idx i.succ)
  invFun := fun rc => Fin.cases rc.1 rc.2
  left_inv := by
    intro idx
    funext i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j
      rfl
  right_inv := by
    intro rc
    rcases rc with ⟨head, tail⟩
    apply Prod.ext
    · rfl
    · funext i
      rfl

private theorem tensorKronecker_succ_reindex_eq_kronecker {k : Nat}
    {dims : Fin (k + 1) → Nat}
    (M : (i : Fin (k + 1)) → SquareMatrix (dims i)) :
    Matrix.reindexAlgEquiv ℝ ℝ (multiIndexConsEquiv dims) (tensorKronecker M) =
      (M 0) ⊗ₖ tensorKronecker (fun i : Fin k => M i.succ) := by
  classical
  ext rc rc'
  rcases rc with ⟨head, tail⟩
  rcases rc' with ⟨head', tail'⟩
  simp [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.kroneckerMap_apply,
    multiIndexConsEquiv, tensorKronecker, Fin.prod_univ_succ]

private theorem tensorKronecker_posSemidef_of_forall_posSemidef {k : Nat}
    {dims : Fin k → Nat} (M : (i : Fin k) → SquareMatrix (dims i))
    (hM : ∀ i : Fin k, (M i).PosSemidef) :
    (tensorKronecker M).PosSemidef := by
  simpa [tensorKronecker] using SOptLib.tensorKronecker_posSemidef M hM

private theorem tensorKronecker_posDef_of_forall_posDef {k : Nat} {dims : Fin k → Nat}
    (M : (i : Fin k) → SquareMatrix (dims i))
    (hM : ∀ i : Fin k, (M i).PosDef) :
    (tensorKronecker M).PosDef :=
  SOptLib.tensorKronecker_posDef M hM

private theorem theorem10_source_flat_update_and_pd_preconditioner {k T : Nat}
    (S : TensorAlgorithm2 k T) (run : S.CorrectedRun) [Nonempty (Fin k)] :
    let a : ℝ := 1 / ((2 : ℝ) * (k : ℝ))
    let H : Fin T → GenericSquare (MultiIndex S.dims) := fun t =>
      tensorKronecker (fun i : Fin k =>
        matrixPower (run.accumulator i (nextIndex t)) a
          (run.accumulator_psd i (nextIndex t)))
    (∀ t : Fin T, (H t).PosDef) ∧
      ∀ t : Fin T,
         (run.iterate (nextIndex t)) =
           (run.iterate (currentIndex t)) -
            S.eta • (H t)⁻¹.mulVec ( (run.gradientAt t)) := by
  classical
  let a : ℝ := 1 / ((2 : ℝ) * (k : ℝ))
  let H : Fin T → GenericSquare (MultiIndex S.dims) := fun t =>
    tensorKronecker (fun i : Fin k =>
      matrixPower (run.accumulator i (nextIndex t)) a
        (run.accumulator_psd i (nextIndex t)))
  have ha_pos : 0 < a := by
    have hk_pos_nat : 0 < k := Fin.pos_iff_nonempty.mpr inferInstance
    have hk_pos : 0 < (k : ℝ) := by exact_mod_cast hk_pos_nat
    dsimp [a]
    positivity
  have hfactor_pd : ∀ t : Fin T, ∀ i : Fin k,
      (matrixPower (run.accumulator i (nextIndex t)) a
        (run.accumulator_psd i (nextIndex t))).PosDef := by
    intro t i
    exact matrixPower_posDef_of_posDef_pos_exp
      (run.accumulator i (nextIndex t)) a
      (theorem10_next_accumulator_posDef S run t i)
      (run.accumulator_psd i (nextIndex t)) ha_pos
  have hHpd : ∀ t : Fin T, (H t).PosDef := by
    intro t
    exact tensorKronecker_posDef_of_forall_posDef
      (fun i : Fin k =>
        matrixPower (run.accumulator i (nextIndex t)) a
          (run.accumulator_psd i (nextIndex t)))
      (hfactor_pd t)
  have hupdate : ∀ t : Fin T,
       (run.iterate (nextIndex t)) =
         (run.iterate (currentIndex t)) -
          S.eta • (H t)⁻¹.mulVec ( (run.gradientAt t)) := by
    intro t
    have hbridge :
        (H t)⁻¹.mulVec ( (run.gradientAt t)) =
           (tensorModeProducts (run.gradientAt t)
            (fun i : Fin k =>
              pdMatrixPower (run.accumulator i (nextIndex t)) (-a)
                (theorem10_next_accumulator_posDef S run t i))) := by
      simpa [H, a] using
        tensorKronecker_inverse_mulVec_tensorVec_pd_neg_power
          (run.gradientAt t)
          (fun i : Fin k => run.accumulator i (nextIndex t)) a
          (fun i => theorem10_next_accumulator_posDef S run t i)
          (fun i => run.accumulator_psd i (nextIndex t))
          (by simpa [H] using hHpd t)
    have hbridge' :
        tensorModeProducts (run.gradientAt t)
            (fun i : Fin k =>
              pdMatrixPower (run.accumulator i (nextIndex t))
                (-(1 / ((2 : ℝ) * (k : ℝ))))
                (theorem10_next_accumulator_posDef S run t i)) =
          (H t)⁻¹.mulVec ( (run.gradientAt t)) := by
      simpa [H, a] using hbridge.symm
    rw [theorem10_algorithm2_tensor_update_modeProducts S run t]
    ext idx
    have hidx := congrFun hbridge' idx
    simp only [Pi.sub_apply, Pi.smul_apply]
    rw [hidx]
  exact ⟨hHpd, hupdate⟩

private theorem tensorVec_current_sub_sq_sum_le_comparatorRadius_sq {k T : Nat}
    (S : TensorAlgorithm2 k T) (run : S.CorrectedRun)
    [Nonempty (Fin T)] (Wstar : TensorSpace S.dims) (t : Fin T) :
    (∑ idx : MultiIndex S.dims,
      ( (run.iterate (currentIndex t)) idx -  Wstar idx) ^ 2) ≤
      (run.comparatorRadius Wstar) ^ 2 := by
  classical
  let A : TensorSpace S.dims := run.iterate (currentIndex t) - Wstar
  let normA : ℝ := tensorFrobeniusNorm A
  let D : ℝ := run.comparatorRadius Wstar
  have hsum_nonneg :
      0 ≤ (∑ idx : MultiIndex S.dims, A idx * A idx) := by
    exact Finset.sum_nonneg (by
      intro idx _hidx
      exact mul_self_nonneg _)
  have hflat_eq :
      (∑ idx : MultiIndex S.dims,
        ( (run.iterate (currentIndex t)) idx -  Wstar idx) ^ 2) =
        (∑ idx : MultiIndex S.dims, A idx * A idx) := by
    simp [A, pow_two]
  have hnorm_sq :
      normA ^ 2 = (∑ idx : MultiIndex S.dims, A idx * A idx) := by
    simp [normA, tensorFrobeniusNorm, Real.sq_sqrt hsum_nonneg]
  have hnorm_le : normA ≤ D := by
    dsimp [normA, A, D, TensorAlgorithm2.CorrectedRun.comparatorRadius, finiteMax]
    exact Finset.le_sup'
      (fun t : Fin T => tensorFrobeniusNorm (run.iterate (currentIndex t) - Wstar))
      (Finset.mem_univ t)
  have hnorm_nonneg : 0 ≤ normA := by
    simp [normA, tensorFrobeniusNorm]
  have hD_nonneg : 0 ≤ D := le_trans hnorm_nonneg hnorm_le
  have hsq : normA ^ 2 ≤ D ^ 2 := by
    nlinarith [sq_nonneg (D - normA)]
  calc
    (∑ idx : MultiIndex S.dims,
      ( (run.iterate (currentIndex t)) idx -  Wstar idx) ^ 2)
        = normA ^ 2 := by rw [hflat_eq, hnorm_sq]
    _ ≤ D ^ 2 := hsq
    _ = (run.comparatorRadius Wstar) ^ 2 := by simp [D]

private theorem theorem10_accumulator_current_le_next {k T : Nat}
    (S : TensorAlgorithm2 k T) (run : S.CorrectedRun) (t : Fin T) (i : Fin k) :
    run.accumulator i (currentIndex t) ≤ run.accumulator i (nextIndex t) := by
  classical
  rw [Matrix.le_iff]
  have hstate :
      (run.state (nextIndex t)).H i =
        (run.state (currentIndex t)).H i + tensorContraction (run.gradientAt t) i := by
    have hH := congrArg (fun st : TensorState S.dims => st.H i) (run.step t)
    simpa [TensorAlgorithm2.stepState] using hH
  have hgram : (tensorContraction (run.gradientAt t) i).PosSemidef := by
    simpa [tensorContraction] using
      (Matrix.PosSemidef.one.mul_mul_conjTranspose_same
        (B := matricization (run.gradientAt t) i))
  change
    (run.accumulator i (nextIndex t) -
        run.accumulator i (currentIndex t)).PosSemidef
  simpa [TensorAlgorithm2.CorrectedRun.accumulator, hstate] using hgram

private theorem tensor_corrected_run_accumulator_eq_prefix_sum {k T : Nat}
    (S : TensorAlgorithm2 k T) (run : S.CorrectedRun) (i : Fin k)
    (N : Fin (T + 1)) :
    run.accumulator i N =
      S.epsilon • (1 : SquareMatrix (S.dims i)) +
        ∑ s : Fin T, if s.1 < N.1 then tensorContraction (run.gradientAt s) i else 0 := by
  exact fin_state_eq_base_add_sum_lt_of_succ_eq_add
    (state := run.accumulator i)
    (increment := fun s => tensorContraction (run.gradientAt s) i)
    (base := S.epsilon • (1 : SquareMatrix (S.dims i)))
    (by simpa [TensorAlgorithm2.CorrectedRun.accumulator,
      TensorAlgorithm2.initialState] using
        congrArg (fun st : TensorState S.dims => st.H i) run.initial)
    (by
      intro t
      simpa [TensorAlgorithm2.CorrectedRun.accumulator, currentIndex, nextIndex,
        TensorAlgorithm2.stepState] using
          congrArg (fun st : TensorState S.dims => st.H i) (run.step t))
    N

private theorem theorem10_hhat_prefix_posSemidef {k T : Nat}
    (S : TensorAlgorithm2 k T) (run : S.CorrectedRun) (N : Fin (T + 1)) :
    (S.epsilon • (1 : GenericSquare (MultiIndex S.dims)) +
      ∑ s : Fin T,
        if s.1 < N.1 then vectorOuter ( (run.gradientAt s)) else 0).PosSemidef := by
  classical
  have h0 :
      (S.epsilon • (1 : GenericSquare (MultiIndex S.dims))).PosSemidef :=
    Matrix.PosSemidef.one.smul S.epsilon_nonneg
  have hsum :
      (∑ s : Fin T,
        if s.1 < N.1 then vectorOuter ( (run.gradientAt s)) else 0 :
          GenericSquare (MultiIndex S.dims)).PosSemidef := by
    refine finset_sum_generic_posSemidef_of_forall Finset.univ
      (fun s : Fin T =>
        if s.1 < N.1 then vectorOuter ( (run.gradientAt s)) else 0) ?_
    intro s _hs
    by_cases hsN : s.1 < N.1
    · simpa [hsN] using
        vectorOuter_posSemidef (ι := MultiIndex S.dims) ( (run.gradientAt s))
    · simpa [hsN] using
      (Matrix.PosSemidef.zero : (0 : GenericSquare (MultiIndex S.dims)).PosSemidef)
  exact h0.add hsum

private theorem generic_hhat_prefix_posSemidef {T : Nat}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Fin T → ι → ℝ) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (N : Fin (T + 1)) :
    (epsilon • (1 : GenericSquare ι) +
      ∑ s : Fin T, if s.1 < N.1 then vectorOuter (g s) else 0).PosSemidef := by
  classical
  have h0 : (epsilon • (1 : GenericSquare ι)).PosSemidef :=
    Matrix.PosSemidef.one.smul heps
  have hsum :
      (∑ s : Fin T, if s.1 < N.1 then vectorOuter (g s) else 0 :
        GenericSquare ι).PosSemidef := by
    refine finset_sum_generic_posSemidef_of_forall Finset.univ
      (fun s : Fin T => if s.1 < N.1 then vectorOuter (g s) else 0) ?_
    intro s _hs
    by_cases hsN : s.1 < N.1
    · simpa [hsN] using vectorOuter_posSemidef (ι := ι) (g s)
    · simpa [hsN] using
        (Matrix.PosSemidef.zero : (0 : GenericSquare ι).PosSemidef)
  exact h0.add hsum

private theorem generic_prefix_outer_le_next_hhat_base {T : Nat}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Fin T → ι → ℝ) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (t : Fin T) :
    vectorOuter (g t) ≤
      epsilon • (1 : GenericSquare ι) +
        ∑ s : Fin T, if s.1 < (nextIndex t).1 then vectorOuter (g s) else 0 := by
  simpa [nextIndex] using
    term_le_base_add_sum_fin_lt_next_of_nonneg
      (A := fun s : Fin T => vectorOuter (g s))
      (base := epsilon • (1 : GenericSquare ι))
      (hbase := (Matrix.PosSemidef.one.smul heps).nonneg)
      (t := t)
      (hA := fun s _ => (vectorOuter_posSemidef (ι := ι) (g s)).nonneg)

private theorem theorem10_prefix_rank_domination {k T : Nat}
    (S : TensorAlgorithm2 k T) (run : S.CorrectedRun)
    [Nonempty (Fin k)]
    (rankBound : Fin k → PosNat)
    (hrank : ∀ i : Fin k, ∀ t : Fin T,
      (matricization (run.gradientAt t) i).rank ≤ (rankBound i).1)
    (N : Fin (T + 1)) :
    S.epsilon • (1 : GenericSquare (MultiIndex S.dims)) +
        (∑ s : Fin T,
          if s.1 < N.1 then vectorOuter ( (run.gradientAt s)) else 0) ≤
      (TensorAlgorithm2.rankGeometricMean rankBound) •
        tensorKronecker
          (fun i : Fin k =>
            matrixPower (run.accumulator i N) (1 / (k : ℝ))
              (run.accumulator_psd i N)) := by
  classical
  simpa [vectorOuter, TensorAlgorithm2.rankGeometricMean, tensorKronecker,
      matrixPower, psdMatrixPower_eq_cfc,
      tensor_corrected_run_accumulator_eq_prefix_sum S run] using
    (SOptLib.regularized_tensor_rank_prefix_outer_sum_le_geometricMean_smul_tensorKronecker_contraction_prefix
      (G := run.gradientAt) (rankBound := rankBound) (epsilon := S.epsilon)
      (N := N) (fun i t _ht => hrank i t) (by
        intro H hH
        simpa [vectorOuter, TensorAlgorithm2.rankGeometricMean, tensorKronecker,
          matrixPower, psdMatrixPower_eq_cfc] using
          (Lemma_11_tensor_rank_domination H rankBound S.epsilon hH S.epsilon_nonneg)))

private theorem tensorKronecker_mono_of_forall_le {k : Nat} {dims : Fin k → Nat}
    (A B : (i : Fin k) → SquareMatrix (dims i))
    (hApsd : ∀ i : Fin k, (A i).PosSemidef)
    (hAB : ∀ i : Fin k, A i ≤ B i) :
    tensorKronecker A ≤ tensorKronecker B := by
  exact SOptLib.tensorKronecker_mono_of_forall_le A B hApsd hAB

private theorem theorem10_powered_tensor_preconditioner_current_le_next {k T : Nat}
    (S : TensorAlgorithm2 k T) (run : S.CorrectedRun)
    [Nonempty (Fin k)] (t : Fin T) :
    tensorKronecker (fun i : Fin k =>
        matrixPower (run.accumulator i (currentIndex t))
          (1 / ((2 : ℝ) * (k : ℝ))) (run.accumulator_psd i (currentIndex t))) ≤
      tensorKronecker (fun i : Fin k =>
        matrixPower (run.accumulator i (nextIndex t))
          (1 / ((2 : ℝ) * (k : ℝ))) (run.accumulator_psd i (nextIndex t))) := by
  classical
  let a : ℝ := 1 / ((2 : ℝ) * (k : ℝ))
  have hk_pos_nat : 0 < k := Fin.pos_iff_nonempty.mpr inferInstance
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast hk_pos_nat
  have hden_pos : 0 < (2 : ℝ) * (k : ℝ) := by positivity
  have hden_ge_one : (1 : ℝ) ≤ (2 : ℝ) * (k : ℝ) := by
    have hk_ge_one : (1 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hk_pos_nat)
    nlinarith
  have ha0 : 0 ≤ a := by
    dsimp [a]
    positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    simpa [one_div] using inv_le_one_of_one_le₀ hden_ge_one
  have hpow_le : ∀ i : Fin k,
      matrixPower (run.accumulator i (currentIndex t)) a
          (run.accumulator_psd i (currentIndex t)) ≤
        matrixPower (run.accumulator i (nextIndex t)) a
          (run.accumulator_psd i (nextIndex t)) := by
    intro i
    exact Lemma_6_operator_monotone_powers
      (run.accumulator i (currentIndex t))
      (run.accumulator i (nextIndex t)) a
      (run.accumulator_psd i (currentIndex t))
      (run.accumulator_psd i (nextIndex t))
      (theorem10_accumulator_current_le_next S run t i) ha0 ha1
  have hpow_psd : ∀ i : Fin k,
      (matrixPower (run.accumulator i (currentIndex t)) a
          (run.accumulator_psd i (currentIndex t))).PosSemidef := by
    intro i
    exact matrixPower_posSemidef (run.accumulator i (currentIndex t)) a
      (run.accumulator_psd i (currentIndex t))
  simpa [a] using
    tensorKronecker_mono_of_forall_le
      (fun i : Fin k =>
        matrixPower (run.accumulator i (currentIndex t)) a
          (run.accumulator_psd i (currentIndex t)))
      (fun i : Fin k =>
        matrixPower (run.accumulator i (nextIndex t)) a
          (run.accumulator_psd i (nextIndex t)))
      hpow_psd hpow_le

private theorem theorem10_powered_tensor_preconditioner_increment_psd {k T : Nat}
    (S : TensorAlgorithm2 k T) (run : S.CorrectedRun)
    [Nonempty (Fin k)] (t : Fin T) :
    (tensorKronecker (fun i : Fin k =>
        matrixPower (run.accumulator i (nextIndex t))
          (1 / ((2 : ℝ) * (k : ℝ))) (run.accumulator_psd i (nextIndex t))) -
      tensorKronecker (fun i : Fin k =>
        matrixPower (run.accumulator i (currentIndex t))
          (1 / ((2 : ℝ) * (k : ℝ))) (run.accumulator_psd i (currentIndex t)))).PosSemidef := by
  exact Matrix.le_iff.mp
    (theorem10_powered_tensor_preconditioner_current_le_next S run t)

private theorem genericTrace_reindexAlgEquiv {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (A : GenericSquare ι) :
    genericTrace (Matrix.reindexAlgEquiv ℝ ℝ e A) = genericTrace A := by
  simpa [genericTrace] using (Matrix.trace_reindexAlgEquiv (S := ℝ) e A)

private theorem genericTrace_kronecker_generic {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : GenericSquare ι) (B : GenericSquare κ) :
    genericTrace (A ⊗ₖ B) = genericTrace A * genericTrace B := by
  classical
  unfold genericTrace
  simpa using (Matrix.trace_kronecker A B)

private theorem genericTrace_tensorKronecker_eq_prod_trace {k : Nat}
    {dims : Fin k → Nat} (M : (i : Fin k) → SquareMatrix (dims i)) :
    genericTrace (tensorKronecker M) = ∏ i : Fin k, matrixTrace (M i) := by
  have h := (SOptLib.tensorKronecker_trace
    (ι := Fin k) (R := ℝ) (dims := fun i => Fin (dims i)) M)
  apply Eq.trans ?_ (by simpa [matrixTrace] using h)
  unfold genericTrace tensorKronecker Matrix.trace
  apply Finset.sum_congr
  · ext x
    simp
  · intro x hx
    rfl

private theorem theorem10_source_first_term_le_radius_sq_trace {k T : Nat}
    (S : TensorAlgorithm2 k T) (run : S.CorrectedRun)
    [Nonempty (Fin k)] [Nonempty (Fin T)] (Wstar : TensorSpace S.dims) :
    (∑ t : Fin T,
      (quadraticForm
          ( (run.iterate (currentIndex t)) -  Wstar)
          (tensorKronecker (fun i : Fin k =>
            matrixPower (run.accumulator i (nextIndex t))
              (1 / ((2 : ℝ) * (k : ℝ))) (run.accumulator_psd i (nextIndex t)))) -
        quadraticForm
          ( (run.iterate (nextIndex t)) -  Wstar)
          (tensorKronecker (fun i : Fin k =>
            matrixPower (run.accumulator i (nextIndex t))
              (1 / ((2 : ℝ) * (k : ℝ))) (run.accumulator_psd i (nextIndex t)))))) ≤
      (run.comparatorRadius Wstar) ^ 2 *
        genericTrace
          (tensorKronecker (fun i : Fin k =>
            matrixPower (run.accumulator i ⟨T, Nat.lt_succ_self T⟩)
              (1 / ((2 : ℝ) * (k : ℝ)))
              (run.accumulator_psd i ⟨T, Nat.lt_succ_self T⟩))) := by
  classical
  have hRadiusSq : ∀ t : Fin T,
      (∑ idx : MultiIndex S.dims,
        ( (run.iterate (currentIndex t)) idx -  Wstar idx) ^ 2) ≤
        (run.comparatorRadius Wstar) ^ 2 := by
    intro t
    exact tensorVec_current_sub_sq_sum_le_comparatorRadius_sq S run Wstar t
  have hRadiusTraceBound : ∀ (t : Fin T) (M : GenericSquare (MultiIndex S.dims)),
      M.PosSemidef →
      quadraticForm ( (run.iterate (currentIndex t)) -  Wstar) M ≤
        (run.comparatorRadius Wstar) ^ 2 * genericTrace M := by
    intro t M hM
    have hquad :=
      quadraticForm_le_sq_sum_mul_trace_of_posSemidef
        ( (run.iterate (currentIndex t)) -  Wstar) M hM
    have htrace_nonneg : 0 ≤ genericTrace M := by
      simpa [genericTrace] using hM.trace_nonneg
    have hmul :=
      mul_le_mul_of_nonneg_right (hRadiusSq t) htrace_nonneg
    exact le_trans hquad hmul
  let metric : Fin (T + 1) → GenericSquare (MultiIndex S.dims) := fun u =>
    tensorKronecker (fun i : Fin k =>
      matrixPower (run.accumulator i u)
        (1 / ((2 : ℝ) * (k : ℝ))) (run.accumulator_psd i u))
  let Hext : Fin (T + 1) → GenericSquare (MultiIndex S.dims) := fun u =>
    if u.val = 0 then 0 else metric u
  have hTpos : 0 < T := by
    rcases ‹Nonempty (Fin T)› with ⟨t⟩
    exact Nat.lt_of_le_of_lt (Nat.zero_le t.val) t.isLt
  have hTne : T ≠ 0 := Nat.ne_of_gt hTpos
  have hHext0 : Hext ⟨0, Nat.zero_lt_succ T⟩ = 0 := by
    simp [Hext]
  have hHextInc : ∀ t : Fin T,
      (Hext (nextIndex t) - Hext (currentIndex t)).PosSemidef := by
    intro t
    have hnext : Hext (nextIndex t) = metric (nextIndex t) := by
      simp [Hext, nextIndex]
    by_cases ht0 : t.val = 0
    · have hcur : Hext (currentIndex t) = 0 := by
        simp [Hext, currentIndex, ht0]
      have hmetric_psd : (metric (nextIndex t)).PosSemidef := by
        exact tensorKronecker_posSemidef_of_forall_posSemidef
          (fun i : Fin k =>
            matrixPower (run.accumulator i (nextIndex t))
              (1 / ((2 : ℝ) * (k : ℝ))) (run.accumulator_psd i (nextIndex t)))
          (fun i => matrixPower_posSemidef (run.accumulator i (nextIndex t))
            (1 / ((2 : ℝ) * (k : ℝ))) (run.accumulator_psd i (nextIndex t)))
      simpa [hnext, hcur, metric] using hmetric_psd
    · have hcur : Hext (currentIndex t) = metric (currentIndex t) := by
        simp [Hext, currentIndex, ht0]
      simpa [hnext, hcur, metric] using
        theorem10_powered_tensor_preconditioner_increment_psd S run t
  have hHextFinalPSD : (Hext ⟨T, Nat.lt_succ_self T⟩).PosSemidef := by
    have hmetric_psd : (metric ⟨T, Nat.lt_succ_self T⟩).PosSemidef := by
      exact tensorKronecker_posSemidef_of_forall_posSemidef
        (fun i : Fin k =>
          matrixPower (run.accumulator i ⟨T, Nat.lt_succ_self T⟩)
            (1 / ((2 : ℝ) * (k : ℝ))) (run.accumulator_psd i ⟨T, Nat.lt_succ_self T⟩))
        (fun i => matrixPower_posSemidef (run.accumulator i ⟨T, Nat.lt_succ_self T⟩)
          (1 / ((2 : ℝ) * (k : ℝ))) (run.accumulator_psd i ⟨T, Nat.lt_succ_self T⟩))
    simpa [Hext, metric, hTne] using hmetric_psd
  have htelescope :=
    finite_changing_metric_quadratic_telescope_le_trace
      (T := T) (ι := MultiIndex S.dims)
      (x := fun u : Fin (T + 1) =>  (run.iterate u) -  Wstar)
      (H := Hext) (D := run.comparatorRadius Wstar)
      hHext0 hHextInc hHextFinalPSD hRadiusTraceBound
  simpa [Hext, metric, nextIndex, hTne] using htelescope

def rankOneTensor {k : Nat} {dims : Fin k → Nat}
    (u : (i : Fin k) → Fin (dims i) → ℝ) : TensorSpace dims :=
  SOptLib.rankOneTensor u

private theorem replaceIndex_modeIndex_same {k : Nat} {dims : Fin k → Nat}
    {i : Fin k} (row : Fin (dims i)) (col : ModeColumn dims i) (s : Fin (dims i)) :
    replaceIndex ((fun row col => (Equiv.piSplitAt i (fun j => Fin (dims j))).symm (row, col)) row col) i s = (fun row col => (Equiv.piSplitAt i (fun j => Fin (dims j))).symm (row, col)) s col := by
  funext j
  by_cases h : j = i
  · subst j
    simp [replaceIndex, Equiv.piSplitAt]
  · simp [replaceIndex, Equiv.piSplitAt, h]

/- Book JSON key_lemmas.Lemma_14_tensor_vec_mat_identities. -/
theorem Lemma_14_vec_matricization_identity {k : Nat} {dims : Fin k → Nat}
    (A : TensorSpace dims) (i : Fin k) :
    genericMatrixVec (matricization A i) = tensorVecReindexedByMode A i := by
  rfl

theorem Lemma_14_vec_transposed_matricization_identity {k : Nat} {dims : Fin k → Nat}
    (A : TensorSpace dims) (i : Fin k) :
    genericMatrixVec ((matricization A i).transpose) =
      tensorVecReindexedByTransposedMode A i := by
  rfl

theorem Lemma_14_vec_first_matricization_identity {k : Nat}
    {dims : Fin (k + 1) → Nat} (A : TensorSpace dims) :
    genericMatrixVec (matricization A (firstMode k)) =
      tensorVecReindexedByMode A (firstMode k) := by
  rfl

theorem Lemma_14_vec_last_transposed_matricization_identity {k : Nat}
    {dims : Fin (k + 1) → Nat} (A : TensorSpace dims) :
    genericMatrixVec ((matricization A (lastMode k)).transpose) =
      tensorVecReindexedByTransposedMode A (lastMode k) := by
  rfl

theorem Lemma_14_tensor_vec_mat_identities {k : Nat} {dims : Fin k → Nat}
    (u : (i : Fin k) → Fin (dims i) → ℝ)
    (A : TensorSpace dims) (i : Fin k) (M : SquareMatrix (dims i)) :
    ( (rankOneTensor u) =
        fun idx : MultiIndex dims => ∏ j : Fin k, u j (idx j)) ∧
      (matricization (rankOneTensor u) i =
        fun row col => u i row * ∏ j : {j : Fin k // j ≠ i}, u j.1 (col j)) ∧
      (genericMatrixVec (matricization A i) = tensorVecReindexedByMode A i) ∧
      (genericMatrixVec ((matricization A i).transpose) =
        tensorVecReindexedByTransposedMode A i) ∧
      (matricization (tensorModeProduct A i M) i = M * matricization A i) := by
  classical
  constructor
  · rfl
  constructor
  · have hmat := SOptLib.tensorMatricization_rankOneTensor (u := u) i
    ext row col
    change SOptLib.rankOneTensor u
      ((Equiv.piSplitAt i (fun j => Fin (dims j))).symm (row, col)) = _
    convert congrFun (congrFun hmat row) col using 1
    congr 1
    funext j
    by_cases hji : j = i
    · subst j
      simp [Equiv.piSplitAt]
    · simp [Equiv.piSplitAt, hji]
  constructor
  · rfl
  constructor
  · rfl
  · ext row col
    simp [matricization, tensorModeProduct, Matrix.mul_apply, replaceIndex_modeIndex_same]

private def modeIndexEquiv {k : Nat} {dims : Fin k → Nat}
    (i : Fin k) : Fin (dims i) × ModeColumn dims i ≃ MultiIndex dims where
  toFun := fun rc => (fun row col => (Equiv.piSplitAt i (fun j => Fin (dims j))).symm (row, col)) rc.1 rc.2
  invFun := fun idx => (idx i, fun j => idx j.1)
  left_inv := by
    intro rc
    rcases rc with ⟨row, col⟩
    apply Prod.ext
    · simp [Equiv.piSplitAt]
    · funext j
      simp [Equiv.piSplitAt, j.property]
  right_inv := by
    intro idx
    funext j
    by_cases h : j = i
    · subst j
      simp [Equiv.piSplitAt]
    · simp [Equiv.piSplitAt, h]

private theorem matrix_le_equiv_congr {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (A C : GenericSquare α) (B D : GenericSquare β)
    (hA : ∀ x y, A x y = B (e x) (e y))
    (hC : ∀ x y, C x y = D (e x) (e y)) :
    A ≤ C ↔ B ≤ D := by
  rw [Matrix.le_iff, Matrix.le_iff]
  have hdiff : C - A = (D - B).submatrix e e := by
    ext x y
    simp [Matrix.submatrix_apply, hA, hC]
  rw [hdiff]
  exact Matrix.posSemidef_submatrix_equiv e

private theorem modeColumn_identity_eq_prod {k : Nat} {dims : Fin k → Nat}
    {i : Fin k} (c c' : ModeColumn dims i) :
    (1 : GenericSquare (ModeColumn dims i)) c c' =
      ∏ j : {j : Fin k // j ≠ i}, if c j = c' j then (1 : ℝ) else 0 := by
  classical
  by_cases h : c = c'
  · subst h
    simp
  · have hne : ∃ j : {j : Fin k // j ≠ i}, c j ≠ c' j := by
      by_contra hnone
      apply h
      funext j
      by_contra hj
      exact hnone ⟨j, hj⟩
    rcases hne with ⟨j, hj⟩
    rw [Matrix.one_apply_ne h]
    exact (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])).symm

private theorem vectorOuter_matricization_reindex_eq {k : Nat} {dims : Fin k → Nat}
    (G : TensorSpace dims) (i : Fin k)
    (rc rc' : Fin (dims i) × ModeColumn dims i) :
    vectorOuter (fun rc : Fin (dims i) × ModeColumn dims i =>
        matricization G i rc.1 rc.2) rc rc' =
      vectorOuter ( G)
        ((fun row col => (Equiv.piSplitAt i (fun j => Fin (dims j))).symm (row, col)) rc.1 rc.2) ((fun row col => (Equiv.piSplitAt i (fun j => Fin (dims j))).symm (row, col)) rc'.1 rc'.2) := by
  rfl

private theorem mode_embedded_reindex_eq_kron {k : Nat} {dims : Fin k → Nat}
    (i : Fin k) (B : SquareMatrix (dims i))
    (rc rc' : Fin (dims i) × ModeColumn dims i) :
    modeEmbeddedMatrix i B ((fun row col => (Equiv.piSplitAt i (fun j => Fin (dims j))).symm (row, col)) rc.1 rc.2) ((fun row col => (Equiv.piSplitAt i (fun j => Fin (dims j))).symm (row, col)) rc'.1 rc'.2) =
      (B ⊗ₖ (1 : GenericSquare (ModeColumn dims i))) rc rc' := by
  classical
  rcases rc with ⟨row, col⟩
  rcases rc' with ⟨row', col'⟩
  have hprod :
      (∏ x : {j : Fin k // j ≠ i},
          if ((fun row col => (Equiv.piSplitAt i (fun j => Fin (dims j))).symm (row, col)) row col) x.1 = ((fun row col => (Equiv.piSplitAt i (fun j => Fin (dims j))).symm (row, col)) row' col') x.1 then (1 : ℝ) else 0) =
        ∏ x : {j : Fin k // j ≠ i}, if col x = col' x then (1 : ℝ) else 0 := by
    apply Finset.prod_congr rfl
    intro x hx
    simp [Equiv.piSplitAt, x.property]
  rw [Matrix.kroneckerMap_apply, modeColumn_identity_eq_prod]
  unfold modeEmbeddedMatrix SOptLib.tensorModeEmbedding
  rw [hprod]
  simp [Equiv.piSplitAt]

/- Book JSON key_lemmas.Lemma_15_matricized_psd_equivalence. -/
theorem Lemma_15_matricized_psd_equivalence {k : Nat} {dims : Fin k → Nat}
    (G : TensorSpace dims) (i : Fin k) (B : SquareMatrix (dims i)) :
    vectorOuter (fun rc : Fin (dims i) × ModeColumn dims i => matricization G i rc.1 rc.2) ≤
        (B ⊗ₖ (1 : GenericSquare (ModeColumn dims i))) ↔
      vectorOuter ( G) ≤ modeEmbeddedMatrix i B := by
  classical
  have hmodeIndex :
      (fun rc : Fin (dims i) × ModeColumn dims i => G ((fun row col => (Equiv.piSplitAt i (fun j => Fin (dims j))).symm (row, col)) rc.1 rc.2)) =
        fun rc => G (fun j => if h : j = i then
          _root_.cast (by rw [h]) rc.1 else rc.2 ⟨j, h⟩) := by
    funext rc
    congr 1
    funext j
    by_cases hji : j = i
    · subst j
      simp [Equiv.piSplitAt]
    · simp [Equiv.piSplitAt, hji]
  change Matrix.vecMulVec (fun rc => G ((fun row col => (Equiv.piSplitAt i (fun j => Fin (dims j))).symm (row, col)) rc.1 rc.2))
        (fun rc => G ((fun row col => (Equiv.piSplitAt i (fun j => Fin (dims j))).symm (row, col)) rc.1 rc.2)) ≤
      (B ⊗ₖ (1 : GenericSquare (ModeColumn dims i))) ↔
    Matrix.vecMulVec G G ≤ fun a b => B (a i) (b i) *
      ∏ j : {j : Fin k // j ≠ i}, if a j.1 = b j.1 then (1 : ℝ) else 0
  rw [hmodeIndex]
  let e : Fin (dims i) × ModeColumn dims i ≃ MultiIndex dims :=
    { toFun := fun rc j =>
        if h : j = i then
          _root_.cast (by rw [h]) rc.1
        else
          rc.2 ⟨j, h⟩
      invFun := fun idx => (idx i, fun j => idx j.1)
      left_inv := by
        intro rc
        rcases rc with ⟨row, col⟩
        apply Prod.ext
        · simp
        · funext j
          simp [j.property]
      right_inv := by
        intro idx
        funext j
        by_cases h : j = i
        · subst j
          simp
        · simp [h] }
  have h := SOptLib.tensorMatricization_vecMulVec_le_kronecker_iff
    (dims := fun j : Fin k => Fin (dims j)) G i B
  have hcomparison :
      Matrix.reindexAlgEquiv ℝ ℝ e
          (B ⊗ₖ (1 : GenericSquare (ModeColumn dims i))) =
        fun a b => B (a i) (b i) *
          ∏ j : {j : Fin k // j ≠ i}, if a j.1 = b j.1 then (1 : ℝ) else 0 := by
    ext a b
    simp [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
      e, modeColumn_identity_eq_prod]
  first
  | exact h
  | change Matrix.vecMulVec (fun rc => G (e rc)) (fun rc => G (e rc)) ≤
        (B ⊗ₖ (1 : GenericSquare (ModeColumn dims i))) ↔
      Matrix.vecMulVec G G ≤
        Matrix.reindexAlgEquiv ℝ ℝ e
          (B ⊗ₖ (1 : GenericSquare (ModeColumn dims i))) at h
    rw [hcomparison] at h
    exact h

noncomputable def finalIndex (T : Nat) : Fin (T + 1) :=
  ⟨T, Nat.lt_succ_self T⟩

/- Book JSON source_discrepancies.Theorem_7_RT_index_in_extraction:
   The display extracted R_T with a t=0..T sum, while Algorithm 1 updates
   from t=1..T.  The algorithmic accumulator below is the recurrence-backed
   endpoint used for the paper's Algorithm 1 model. -/
theorem Theorem_7_rightAccumulator_algorithmic_endpoint
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun) :
    run.rightAccumulator (finalIndex T) = (run.finalState).R := by
  rfl

/- Book JSON source_discrepancies.Theorem_13_RT_index_in_extraction:
   The display analogously extracts R_T with a t=0..T diagonal sum, while
   Algorithm 3 updates from t=1..T. -/
theorem Theorem_13_rightAccumulator_algorithmic_endpoint
    (S : DiagonalAlgorithm3 T m n) (run : S.CorrectedRun) :
    run.rightAccumulator (finalIndex T) = (run.state (finalIndex T)).R := by
  rfl

private theorem theorem7_source_flat_update_and_pd_preconditioner {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun) :
    (∀ t : Fin T,
      matrixVec (run.iterate (nextIndex t)) =
        matrixVec (run.iterate (currentIndex t)) - S.eta •
          ((((matrixPower (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
                (run.leftAccumulator_psd (nextIndex t))) ⊗ₖ
              (matrixPower (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
                (run.rightAccumulator_psd (nextIndex t))))⁻¹).mulVec
            (matrixVec (run.gradientAt t)))) ∧
    (∀ t : Fin T,
      ((matrixPower (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
          (run.leftAccumulator_psd (nextIndex t))) ⊗ₖ
        (matrixPower (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
          (run.rightAccumulator_psd (nextIndex t)))).PosDef) := by
  classical
  constructor
  · intro t
    have hLnext_posDef : (run.leftAccumulator (nextIndex t)).PosDef := by
      change ((run.state (nextIndex t)).L).PosDef
      rw [run.step t]
      simpa [MatrixAlgorithm1.stepState, MatrixAlgorithm1.CorrectedRun.leftAccumulator,
        matrixGramLeft] using run.left_step_posDef t
    have hRnext_posDef : (run.rightAccumulator (nextIndex t)).PosDef := by
      change ((run.state (nextIndex t)).R).PosDef
      rw [run.step t]
      simpa [MatrixAlgorithm1.stepState, MatrixAlgorithm1.CorrectedRun.rightAccumulator,
        matrixGramRight] using run.right_step_posDef t
    have hLstate :
        (run.state (nextIndex t)).L =
          (run.state (currentIndex t)).L + matrixGramLeft (run.gradientAt t) := by
      have hL := congrArg SOptLib.TwoSidedMatrixPreconditionerState.L (run.step t)
      simpa [MatrixAlgorithm1.stepState, matrixGramLeft] using hL
    have hRstate :
        (run.state (nextIndex t)).R =
          (run.state (currentIndex t)).R + matrixGramRight (run.gradientAt t) := by
      have hR := congrArg SOptLib.TwoSidedMatrixPreconditionerState.R (run.step t)
      simpa [MatrixAlgorithm1.stepState, matrixGramRight] using hR
    have hmatrix_update :
        run.iterate (nextIndex t) =
          run.iterate (currentIndex t) -
            S.eta •
              (pdMatrixPower ((run.state (currentIndex t)).L +
                    matrixGramLeft (run.gradientAt t)) (-(1 / 4 : ℝ))
                  (run.left_step_posDef t) *
                run.gradientAt t *
                pdMatrixPower ((run.state (currentIndex t)).R +
                    matrixGramRight (run.gradientAt t)) (-(1 / 4 : ℝ))
                  (run.right_step_posDef t)) := by
      have hW := congrArg SOptLib.TwoSidedMatrixPreconditionerState.W (run.step t)
      simpa [MatrixAlgorithm1.stepState, SOptLib.twoSidedMatrixPreconditionedStep,
        MatrixAlgorithm1.CorrectedRun.iterate, matrixGramLeft, matrixGramRight] using hW
    -- Remaining source Eq. (2) transport:
    -- `(L^(1/4) ⊗ R^(1/4))⁻¹ vec(G) = vec(L^(-1/4) G R^(-1/4))`,
    -- with symmetry/transpose normalization for `Lemma_4_matrix_kron_vec`.
    have hLsum :
        (run.state (currentIndex t)).L + matrixGramLeft (run.gradientAt t) =
          run.leftAccumulator (nextIndex t) := by
      simpa [MatrixAlgorithm1.CorrectedRun.leftAccumulator] using hLstate.symm
    have hRsum :
        (run.state (currentIndex t)).R + matrixGramRight (run.gradientAt t) =
          run.rightAccumulator (nextIndex t) := by
      simpa [MatrixAlgorithm1.CorrectedRun.rightAccumulator] using hRstate.symm
    have hmatrix_update_next :
        run.iterate (nextIndex t) =
          run.iterate (currentIndex t) -
            S.eta •
              (pdMatrixPower (run.leftAccumulator (nextIndex t)) (-(1 / 4 : ℝ))
                  hLnext_posDef *
                run.gradientAt t *
                pdMatrixPower (run.rightAccumulator (nextIndex t)) (-(1 / 4 : ℝ))
                  hRnext_posDef) := by
      have hLpow_eq :
          pdMatrixPower ((run.state (currentIndex t)).L + matrixGramLeft (run.gradientAt t))
              (-(1 / 4 : ℝ)) (run.left_step_posDef t) =
            pdMatrixPower (run.leftAccumulator (nextIndex t)) (-(1 / 4 : ℝ))
              hLnext_posDef := by
        exact pdMatrixPower_congr hLsum (-(1 / 4 : ℝ))
          (run.left_step_posDef t) hLnext_posDef
      have hRpow_eq :
          pdMatrixPower ((run.state (currentIndex t)).R + matrixGramRight (run.gradientAt t))
              (-(1 / 4 : ℝ)) (run.right_step_posDef t) =
            pdMatrixPower (run.rightAccumulator (nextIndex t)) (-(1 / 4 : ℝ))
              hRnext_posDef := by
        exact pdMatrixPower_congr hRsum (-(1 / 4 : ℝ))
          (run.right_step_posDef t) hRnext_posDef
      calc
        run.iterate (nextIndex t) =
            run.iterate (currentIndex t) -
              S.eta •
                (pdMatrixPower ((run.state (currentIndex t)).L +
                      matrixGramLeft (run.gradientAt t)) (-(1 / 4 : ℝ))
                    (run.left_step_posDef t) *
                  run.gradientAt t *
                  pdMatrixPower ((run.state (currentIndex t)).R +
                      matrixGramRight (run.gradientAt t)) (-(1 / 4 : ℝ))
                    (run.right_step_posDef t)) := hmatrix_update
        _ = run.iterate (currentIndex t) -
              S.eta •
                (pdMatrixPower (run.leftAccumulator (nextIndex t)) (-(1 / 4 : ℝ))
                    hLnext_posDef *
                  run.gradientAt t *
                  pdMatrixPower (run.rightAccumulator (nextIndex t)) (-(1 / 4 : ℝ))
                    hRnext_posDef) := by
          rw [hLpow_eq, hRpow_eq]
    have hvec_precond :
        ((((matrixPower (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
              (run.leftAccumulator_psd (nextIndex t))) ⊗ₖ
            (matrixPower (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
              (run.rightAccumulator_psd (nextIndex t))))⁻¹).mulVec
          (matrixVec (run.gradientAt t))) =
          matrixVec
            (pdMatrixPower (run.leftAccumulator (nextIndex t)) (-(1 / 4 : ℝ))
                hLnext_posDef *
              run.gradientAt t *
              pdMatrixPower (run.rightAccumulator (nextIndex t)) (-(1 / 4 : ℝ))
                hRnext_posDef) := by
      exact kron_inverse_mulVec_matrixVec_pd_neg_quarter
        (run.gradientAt t)
        (run.leftAccumulator (nextIndex t))
        (run.rightAccumulator (nextIndex t))
        hLnext_posDef hRnext_posDef
        (run.leftAccumulator_psd (nextIndex t))
        (run.rightAccumulator_psd (nextIndex t))
    rw [hmatrix_update_next]
    rw [hvec_precond]
    ext ij
    simp [matrixVec]
  · intro t
    -- Remaining positivity transport: positive fractional powers preserve
    -- per-step accumulator PosDef, and PosDef is closed under the full
    -- Kronecker product.
    have hLnext_posDef : (run.leftAccumulator (nextIndex t)).PosDef := by
      change ((run.state (nextIndex t)).L).PosDef
      rw [run.step t]
      simpa [MatrixAlgorithm1.stepState, MatrixAlgorithm1.CorrectedRun.leftAccumulator,
        matrixGramLeft] using run.left_step_posDef t
    have hRnext_posDef : (run.rightAccumulator (nextIndex t)).PosDef := by
      change ((run.state (nextIndex t)).R).PosDef
      rw [run.step t]
      simpa [MatrixAlgorithm1.stepState, MatrixAlgorithm1.CorrectedRun.rightAccumulator,
        matrixGramRight] using run.right_step_posDef t
    have hLpow_pd :
        (matrixPower (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
          (run.leftAccumulator_psd (nextIndex t))).PosDef := by
      exact matrixPower_posDef_of_posDef_pos_exp
        (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ) hLnext_posDef
        (run.leftAccumulator_psd (nextIndex t)) (by norm_num)
    have hRpow_pd :
        (matrixPower (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
          (run.rightAccumulator_psd (nextIndex t))).PosDef := by
      exact matrixPower_posDef_of_posDef_pos_exp
        (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ) hRnext_posDef
        (run.rightAccumulator_psd (nextIndex t)) (by norm_num)
    simpa using hLpow_pd.kronecker hRpow_pd

private theorem theorem13_flattened_algorithm3_update_and_pd_preconditioner {T m n : Nat}
    (S : DiagonalAlgorithm3 T m n) (run : S.CorrectedRun) :
    (∀ t : Fin T,
      matrixVec (run.iterate (nextIndex t)) =
        matrixVec (run.iterate (currentIndex t)) - S.eta •
          ((((matrixPower (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
                (run.leftAccumulator_psd (nextIndex t))) ⊗ₖ
              (matrixPower (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
                (run.rightAccumulator_psd (nextIndex t))))⁻¹).mulVec
            (matrixVec (run.gradientAt t)))) ∧
    (∀ t : Fin T,
      ((matrixPower (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
          (run.leftAccumulator_psd (nextIndex t))) ⊗ₖ
        (matrixPower (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
          (run.rightAccumulator_psd (nextIndex t)))).PosDef) := by
  classical
  constructor
  · intro t
    have hLnext_posDef : (run.leftAccumulator (nextIndex t)).PosDef := by
      change ((run.state (nextIndex t)).L).PosDef
      rw [run.step t]
      simpa [DiagonalAlgorithm3.stepState, DiagonalAlgorithm3.CorrectedRun.leftAccumulator,
        matrixGramLeft] using run.left_step_posDef t
    have hRnext_posDef : (run.rightAccumulator (nextIndex t)).PosDef := by
      change ((run.state (nextIndex t)).R).PosDef
      rw [run.step t]
      simpa [DiagonalAlgorithm3.stepState, DiagonalAlgorithm3.CorrectedRun.rightAccumulator,
        matrixGramRight] using run.right_step_posDef t
    have hLstate :
        (run.state (nextIndex t)).L =
          (run.state (currentIndex t)).L +
            diagonalPart (matrixGramLeft (run.gradientAt t)) := by
      have hL := congrArg SOptLib.TwoSidedMatrixPreconditionerState.L (run.step t)
      simpa [DiagonalAlgorithm3.stepState, matrixGramLeft] using hL
    have hRstate :
        (run.state (nextIndex t)).R =
          (run.state (currentIndex t)).R +
            diagonalPart (matrixGramRight (run.gradientAt t)) := by
      have hR := congrArg SOptLib.TwoSidedMatrixPreconditionerState.R (run.step t)
      simpa [DiagonalAlgorithm3.stepState, matrixGramRight] using hR
    have hmatrix_update :
        run.iterate (nextIndex t) =
          run.iterate (currentIndex t) -
            S.eta •
              (pdMatrixPower ((run.state (currentIndex t)).L +
                    diagonalPart (matrixGramLeft (run.gradientAt t))) (-(1 / 4 : ℝ))
                  (run.left_step_posDef t) *
                run.gradientAt t *
                pdMatrixPower ((run.state (currentIndex t)).R +
                    diagonalPart (matrixGramRight (run.gradientAt t))) (-(1 / 4 : ℝ))
                  (run.right_step_posDef t)) := by
      have hW := congrArg SOptLib.TwoSidedMatrixPreconditionerState.W (run.step t)
      simpa [DiagonalAlgorithm3.stepState, DiagonalAlgorithm3.CorrectedRun.iterate,
        matrixGramLeft, matrixGramRight] using hW
    have hLsum :
        (run.state (currentIndex t)).L +
            diagonalPart (matrixGramLeft (run.gradientAt t)) =
          run.leftAccumulator (nextIndex t) := by
      simpa [DiagonalAlgorithm3.CorrectedRun.leftAccumulator] using hLstate.symm
    have hRsum :
        (run.state (currentIndex t)).R +
            diagonalPart (matrixGramRight (run.gradientAt t)) =
          run.rightAccumulator (nextIndex t) := by
      simpa [DiagonalAlgorithm3.CorrectedRun.rightAccumulator] using hRstate.symm
    have hmatrix_update_next :
        run.iterate (nextIndex t) =
          run.iterate (currentIndex t) -
            S.eta •
              (pdMatrixPower (run.leftAccumulator (nextIndex t)) (-(1 / 4 : ℝ))
                  hLnext_posDef *
                run.gradientAt t *
                pdMatrixPower (run.rightAccumulator (nextIndex t)) (-(1 / 4 : ℝ))
                  hRnext_posDef) := by
      have hLpow_eq :
          pdMatrixPower ((run.state (currentIndex t)).L +
              diagonalPart (matrixGramLeft (run.gradientAt t)))
              (-(1 / 4 : ℝ)) (run.left_step_posDef t) =
            pdMatrixPower (run.leftAccumulator (nextIndex t)) (-(1 / 4 : ℝ))
              hLnext_posDef := by
        exact pdMatrixPower_congr hLsum (-(1 / 4 : ℝ))
          (run.left_step_posDef t) hLnext_posDef
      have hRpow_eq :
          pdMatrixPower ((run.state (currentIndex t)).R +
              diagonalPart (matrixGramRight (run.gradientAt t)))
              (-(1 / 4 : ℝ)) (run.right_step_posDef t) =
            pdMatrixPower (run.rightAccumulator (nextIndex t)) (-(1 / 4 : ℝ))
              hRnext_posDef := by
        exact pdMatrixPower_congr hRsum (-(1 / 4 : ℝ))
          (run.right_step_posDef t) hRnext_posDef
      calc
        run.iterate (nextIndex t) =
            run.iterate (currentIndex t) -
              S.eta •
                (pdMatrixPower ((run.state (currentIndex t)).L +
                      diagonalPart (matrixGramLeft (run.gradientAt t))) (-(1 / 4 : ℝ))
                    (run.left_step_posDef t) *
                  run.gradientAt t *
                  pdMatrixPower ((run.state (currentIndex t)).R +
                      diagonalPart (matrixGramRight (run.gradientAt t))) (-(1 / 4 : ℝ))
                    (run.right_step_posDef t)) := hmatrix_update
        _ = run.iterate (currentIndex t) -
              S.eta •
                (pdMatrixPower (run.leftAccumulator (nextIndex t)) (-(1 / 4 : ℝ))
                    hLnext_posDef *
                  run.gradientAt t *
                  pdMatrixPower (run.rightAccumulator (nextIndex t)) (-(1 / 4 : ℝ))
                    hRnext_posDef) := by
          rw [hLpow_eq, hRpow_eq]
    have hvec_precond :
        ((((matrixPower (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
              (run.leftAccumulator_psd (nextIndex t))) ⊗ₖ
            (matrixPower (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
              (run.rightAccumulator_psd (nextIndex t))))⁻¹).mulVec
          (matrixVec (run.gradientAt t))) =
          matrixVec
            (pdMatrixPower (run.leftAccumulator (nextIndex t)) (-(1 / 4 : ℝ))
                hLnext_posDef *
              run.gradientAt t *
              pdMatrixPower (run.rightAccumulator (nextIndex t)) (-(1 / 4 : ℝ))
                hRnext_posDef) := by
      exact kron_inverse_mulVec_matrixVec_pd_neg_quarter
        (run.gradientAt t)
        (run.leftAccumulator (nextIndex t))
        (run.rightAccumulator (nextIndex t))
        hLnext_posDef hRnext_posDef
        (run.leftAccumulator_psd (nextIndex t))
        (run.rightAccumulator_psd (nextIndex t))
    rw [hmatrix_update_next]
    rw [hvec_precond]
    ext ij
    simp [matrixVec]
  · intro t
    have hLnext_posDef : (run.leftAccumulator (nextIndex t)).PosDef := by
      change ((run.state (nextIndex t)).L).PosDef
      rw [run.step t]
      simpa [DiagonalAlgorithm3.stepState, DiagonalAlgorithm3.CorrectedRun.leftAccumulator,
        matrixGramLeft] using run.left_step_posDef t
    have hRnext_posDef : (run.rightAccumulator (nextIndex t)).PosDef := by
      change ((run.state (nextIndex t)).R).PosDef
      rw [run.step t]
      simpa [DiagonalAlgorithm3.stepState, DiagonalAlgorithm3.CorrectedRun.rightAccumulator,
        matrixGramRight] using run.right_step_posDef t
    have hLpow_pd :
        (matrixPower (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
          (run.leftAccumulator_psd (nextIndex t))).PosDef := by
      exact matrixPower_posDef_of_posDef_pos_exp
        (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ) hLnext_posDef
        (run.leftAccumulator_psd (nextIndex t)) (by norm_num)
    have hRpow_pd :
        (matrixPower (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
          (run.rightAccumulator_psd (nextIndex t))).PosDef := by
      exact matrixPower_posDef_of_posDef_pos_exp
        (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ) hRnext_posDef
        (run.rightAccumulator_psd (nextIndex t)) (by norm_num)
    simpa using hLpow_pd.kronecker hRpow_pd

private theorem matrixVec_current_sub_sq_sum_le_comparatorRadius_sq {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    [Nonempty (Fin T)] (Wstar : MatrixSpace m n) (t : Fin T) :
    (∑ ij : FlatMatrixIndex m n,
      (matrixVec (run.iterate (currentIndex t)) ij - matrixVec Wstar ij) ^ 2) ≤
      (run.comparatorRadius Wstar) ^ 2 := by
  classical
  let A : MatrixSpace m n := run.iterate (currentIndex t) - Wstar
  let normA : ℝ := frobeniusNorm A
  let D : ℝ := run.comparatorRadius Wstar
  have hsum_nonneg :
      0 ≤ (∑ i : Fin m, ∑ j : Fin n, A i j * A i j) := by
    exact Finset.sum_nonneg (by
      intro i _hi
      exact Finset.sum_nonneg (by
        intro j _hj
        exact mul_self_nonneg _))
  have hflat_eq :
      (∑ ij : FlatMatrixIndex m n,
        (matrixVec (run.iterate (currentIndex t)) ij - matrixVec Wstar ij) ^ 2) =
        (∑ i : Fin m, ∑ j : Fin n, A i j * A i j) := by
    change
      (∑ ij ∈ (Finset.univ : Finset (Fin m × Fin n)),
        (matrixVec (run.iterate (currentIndex t)) ij - matrixVec Wstar ij) ^ 2) =
        (∑ i : Fin m, ∑ j : Fin n, A i j * A i j)
    rw [← Finset.univ_product_univ]
    rw [Finset.sum_product]
    simp [A, matrixVec, pow_two]
  have hnorm_sq :
      normA ^ 2 = (∑ i : Fin m, ∑ j : Fin n, A i j * A i j) := by
    simp [normA, frobeniusNorm, Real.sq_sqrt hsum_nonneg]
  have hnorm_le : normA ≤ D := by
    dsimp [normA, A, D, MatrixAlgorithm1.CorrectedRun.comparatorRadius, finiteMax]
    exact Finset.le_sup'
      (fun t : Fin T => frobeniusNorm (run.iterate (currentIndex t) - Wstar))
      (Finset.mem_univ t)
  have hnorm_nonneg : 0 ≤ normA := by
    simp [normA, frobeniusNorm]
  have hD_nonneg : 0 ≤ D := le_trans hnorm_nonneg hnorm_le
  have hsq : normA ^ 2 ≤ D ^ 2 := by
    nlinarith [sq_nonneg (D - normA)]
  calc
    (∑ ij : FlatMatrixIndex m n,
      (matrixVec (run.iterate (currentIndex t)) ij - matrixVec Wstar ij) ^ 2)
        = normA ^ 2 := by rw [hflat_eq, hnorm_sq]
    _ ≤ D ^ 2 := hsq
    _ = (run.comparatorRadius Wstar) ^ 2 := by simp [D]

private theorem theorem7_leftAccumulator_current_le_next {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun) (t : Fin T) :
    run.leftAccumulator (currentIndex t) ≤ run.leftAccumulator (nextIndex t) := by
  classical
  rw [Matrix.le_iff]
  have hstate :
      (run.state (nextIndex t)).L =
        (run.state (currentIndex t)).L + matrixGramLeft (run.gradientAt t) := by
    have hL := congrArg SOptLib.TwoSidedMatrixPreconditionerState.L (run.step t)
    simpa [MatrixAlgorithm1.stepState, matrixGramLeft] using hL
  have hgram : (matrixGramLeft (run.gradientAt t)).PosSemidef := by
    simpa [matrixGramLeft] using
      (Matrix.PosSemidef.one.mul_mul_conjTranspose_same (B := run.gradientAt t))
  change
    (run.leftAccumulator (nextIndex t) -
        run.leftAccumulator (currentIndex t)).PosSemidef
  simpa [MatrixAlgorithm1.CorrectedRun.leftAccumulator, hstate] using hgram

private theorem theorem7_rightAccumulator_current_le_next {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun) (t : Fin T) :
    run.rightAccumulator (currentIndex t) ≤ run.rightAccumulator (nextIndex t) := by
  classical
  rw [Matrix.le_iff]
  have hstate :
      (run.state (nextIndex t)).R =
        (run.state (currentIndex t)).R + matrixGramRight (run.gradientAt t) := by
    have hR := congrArg SOptLib.TwoSidedMatrixPreconditionerState.R (run.step t)
    simpa [MatrixAlgorithm1.stepState, matrixGramRight] using hR
  have hgram : (matrixGramRight (run.gradientAt t)).PosSemidef := by
    simpa [matrixGramRight] using
      (Matrix.PosSemidef.one.conjTranspose_mul_mul_same (B := run.gradientAt t))
  change
    (run.rightAccumulator (nextIndex t) -
        run.rightAccumulator (currentIndex t)).PosSemidef
  simpa [MatrixAlgorithm1.CorrectedRun.rightAccumulator, hstate] using hgram

private theorem theorem7_powered_kron_preconditioner_current_le_next {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun) (t : Fin T) :
    ((matrixPower (run.leftAccumulator (currentIndex t)) (1 / 4 : ℝ)
        (run.leftAccumulator_psd (currentIndex t))) ⊗ₖ
      (matrixPower (run.rightAccumulator (currentIndex t)) (1 / 4 : ℝ)
        (run.rightAccumulator_psd (currentIndex t)))) ≤
    ((matrixPower (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
        (run.leftAccumulator_psd (nextIndex t))) ⊗ₖ
      (matrixPower (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
        (run.rightAccumulator_psd (nextIndex t)))) := by
  classical
  let Lcur : SquareMatrix m := run.leftAccumulator (currentIndex t)
  let Lnext : SquareMatrix m := run.leftAccumulator (nextIndex t)
  let Rcur : SquareMatrix n := run.rightAccumulator (currentIndex t)
  let Rnext : SquareMatrix n := run.rightAccumulator (nextIndex t)
  let LcurPow : SquareMatrix m :=
    matrixPower Lcur (1 / 4 : ℝ) (run.leftAccumulator_psd (currentIndex t))
  let LnextPow : SquareMatrix m :=
    matrixPower Lnext (1 / 4 : ℝ) (run.leftAccumulator_psd (nextIndex t))
  let RcurPow : SquareMatrix n :=
    matrixPower Rcur (1 / 4 : ℝ) (run.rightAccumulator_psd (currentIndex t))
  let RnextPow : SquareMatrix n :=
    matrixPower Rnext (1 / 4 : ℝ) (run.rightAccumulator_psd (nextIndex t))
  have hLpow_le : LcurPow ≤ LnextPow := by
    simpa [Lcur, Lnext, LcurPow, LnextPow] using
      (Lemma_6_operator_monotone_powers
        (run.leftAccumulator (currentIndex t))
        (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
        (run.leftAccumulator_psd (currentIndex t))
        (run.leftAccumulator_psd (nextIndex t))
        (theorem7_leftAccumulator_current_le_next S run t)
        (by norm_num) (by norm_num))
  have hRpow_le : RcurPow ≤ RnextPow := by
    simpa [Rcur, Rnext, RcurPow, RnextPow] using
      (Lemma_6_operator_monotone_powers
        (run.rightAccumulator (currentIndex t))
        (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
        (run.rightAccumulator_psd (currentIndex t))
        (run.rightAccumulator_psd (nextIndex t))
        (theorem7_rightAccumulator_current_le_next S run t)
        (by norm_num) (by norm_num))
  have hLcurPow_psd : LcurPow.PosSemidef := by
    simpa [Lcur, LcurPow] using
      matrixPower_posSemidef (run.leftAccumulator (currentIndex t)) (1 / 4 : ℝ)
        (run.leftAccumulator_psd (currentIndex t))
  have hRcurPow_psd : RcurPow.PosSemidef := by
    simpa [Rcur, RcurPow] using
      matrixPower_posSemidef (run.rightAccumulator (currentIndex t)) (1 / 4 : ℝ)
        (run.rightAccumulator_psd (currentIndex t))
  simpa [Lcur, Lnext, Rcur, Rnext, LcurPow, LnextPow, RcurPow, RnextPow] using
    (Lemma_3_iv_kron_order_preserving LnextPow LcurPow RnextPow RcurPow
      hLcurPow_psd hRcurPow_psd hLpow_le hRpow_le)

private theorem theorem7_powered_kron_preconditioner_increment_psd {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun) (t : Fin T) :
    (((matrixPower (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
        (run.leftAccumulator_psd (nextIndex t))) ⊗ₖ
      (matrixPower (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
        (run.rightAccumulator_psd (nextIndex t)))) -
    ((matrixPower (run.leftAccumulator (currentIndex t)) (1 / 4 : ℝ)
        (run.leftAccumulator_psd (currentIndex t))) ⊗ₖ
      (matrixPower (run.rightAccumulator (currentIndex t)) (1 / 4 : ℝ)
        (run.rightAccumulator_psd (currentIndex t))))).PosSemidef := by
  exact Matrix.le_iff.mp
    (theorem7_powered_kron_preconditioner_current_le_next S run t)

private theorem matrix_corrected_run_leftAccumulator_eq_prefix_sum {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun) (N : Fin (T + 1)) :
    run.leftAccumulator N =
      S.epsilon • (1 : SquareMatrix m) +
        ∑ s : Fin T, if s.1 < N.1 then matrixGramLeft (run.gradientAt s) else 0 := by
  classical
  induction N using Fin.induction with
  | zero =>
      change (run.state ⟨0, Nat.succ_pos T⟩).L =
        S.epsilon • (1 : SquareMatrix m) +
          ∑ s : Fin T, if s.1 < 0 then matrixGramLeft (run.gradientAt s) else 0
      rw [run.initial]
      simp [MatrixAlgorithm1.initialState]
  | succ t ih =>
      have hstep :
          (run.state (nextIndex t)).L =
            (run.state (currentIndex t)).L + matrixGramLeft (run.gradientAt t) := by
        rw [run.step t]
        simp [MatrixAlgorithm1.stepState, SOptLib.twoSidedMatrixPreconditionedStep,
          matrixGramLeft]
      have hsum :=
        fin_prefix_sum_succ_addCommMonoid
          (fun s : Fin T => matrixGramLeft (run.gradientAt s)) t.2
      change (run.state (nextIndex t)).L =
        S.epsilon • (1 : SquareMatrix m) +
          ∑ s : Fin T, if s.1 < t.1 + 1 then matrixGramLeft (run.gradientAt s) else 0
      rw [hstep]
      rw [hsum]
      change (run.state (currentIndex t)).L + matrixGramLeft (run.gradientAt t) =
        S.epsilon • (1 : SquareMatrix m) +
          ((∑ s : Fin T, if s.1 < t.1 then matrixGramLeft (run.gradientAt s) else 0) +
            matrixGramLeft (run.gradientAt t))
      have hih :
          (run.state (currentIndex t)).L =
            S.epsilon • (1 : SquareMatrix m) +
              ∑ s : Fin T, if s.1 < t.1 then matrixGramLeft (run.gradientAt s) else 0 := by
        simpa [MatrixAlgorithm1.CorrectedRun.leftAccumulator, currentIndex] using ih
      rw [hih]
      abel

private theorem matrix_corrected_run_rightAccumulator_eq_prefix_sum {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun) (N : Fin (T + 1)) :
    run.rightAccumulator N =
      S.epsilon • (1 : SquareMatrix n) +
        ∑ s : Fin T, if s.1 < N.1 then matrixGramRight (run.gradientAt s) else 0 := by
  classical
  induction N using Fin.induction with
  | zero =>
      change (run.state ⟨0, Nat.succ_pos T⟩).R =
        S.epsilon • (1 : SquareMatrix n) +
          ∑ s : Fin T, if s.1 < 0 then matrixGramRight (run.gradientAt s) else 0
      rw [run.initial]
      simp [MatrixAlgorithm1.initialState]
  | succ t ih =>
      have hstep :
          (run.state (nextIndex t)).R =
            (run.state (currentIndex t)).R + matrixGramRight (run.gradientAt t) := by
        rw [run.step t]
        simp [MatrixAlgorithm1.stepState, SOptLib.twoSidedMatrixPreconditionedStep,
          matrixGramRight]
      have hsum :=
        fin_prefix_sum_succ_addCommMonoid
          (fun s : Fin T => matrixGramRight (run.gradientAt s)) t.2
      change (run.state (nextIndex t)).R =
        S.epsilon • (1 : SquareMatrix n) +
          ∑ s : Fin T, if s.1 < t.1 + 1 then matrixGramRight (run.gradientAt s) else 0
      rw [hstep]
      rw [hsum]
      change (run.state (currentIndex t)).R + matrixGramRight (run.gradientAt t) =
        S.epsilon • (1 : SquareMatrix n) +
          ((∑ s : Fin T, if s.1 < t.1 then matrixGramRight (run.gradientAt s) else 0) +
            matrixGramRight (run.gradientAt t))
      have hih :
          (run.state (currentIndex t)).R =
            S.epsilon • (1 : SquareMatrix n) +
              ∑ s : Fin T, if s.1 < t.1 then matrixGramRight (run.gradientAt s) else 0 := by
        simpa [MatrixAlgorithm1.CorrectedRun.rightAccumulator, currentIndex] using ih
      rw [hih]
      abel

private theorem theorem7_prefix_rank_domination {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat)
    (hrank : ∀ t : Fin T, (run.gradientAt t).rank ≤ rankBound.1)
    (N : Fin (T + 1)) :
    S.epsilon • (1 : GenericSquare (FlatMatrixIndex m n)) +
        (1 / positiveRankReal rankBound) •
          (∑ s : Fin T,
            if s.1 < N.1 then vectorOuter (matrixVec (run.gradientAt s)) else 0) ≤
      (matrixPower (run.leftAccumulator N) (1 / 2 : ℝ)
          (run.leftAccumulator_psd N) ⊗ₖ
        matrixPower (run.rightAccumulator N) (1 / 2 : ℝ)
          (run.rightAccumulator_psd N)) := by
  simpa only [positiveRankReal, one_div, vectorOuter, Matrix.vecMulVec, matrixVec,
    matrixGramLeft, matrixGramRight, matrixPower, psdMatrixPower_eq_cfc,
    matrix_corrected_run_leftAccumulator_eq_prefix_sum,
    matrix_corrected_run_rightAccumulator_eq_prefix_sum] using
      (Matrix.regularized_rank_prefix_vecMulVec_sum_le_cfc_sqrt_kronecker_gram_prefixes
        run.gradientAt rankBound.1 S.epsilon N rankBound.2
        (fun t _ht => hrank t) S.epsilon_nonneg)

private theorem theorem7_source_first_term_le_radius_sq_trace {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    [Nonempty (Fin T)] (Wstar : MatrixSpace m n) :
    (∑ t : Fin T,
      (quadraticForm
          (matrixVec (run.iterate (currentIndex t)) - matrixVec Wstar)
          ((matrixPower (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
              (run.leftAccumulator_psd (nextIndex t))) ⊗ₖ
            (matrixPower (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
              (run.rightAccumulator_psd (nextIndex t)))) -
        quadraticForm
          (matrixVec (run.iterate (nextIndex t)) - matrixVec Wstar)
          ((matrixPower (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
              (run.leftAccumulator_psd (nextIndex t))) ⊗ₖ
            (matrixPower (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
              (run.rightAccumulator_psd (nextIndex t)))))) ≤
      (run.comparatorRadius Wstar) ^ 2 *
        genericTrace
          ((matrixPower (run.leftAccumulator (finalIndex T)) (1 / 4 : ℝ)
              (run.leftAccumulator_psd (finalIndex T))) ⊗ₖ
            (matrixPower (run.rightAccumulator (finalIndex T)) (1 / 4 : ℝ)
              (run.rightAccumulator_psd (finalIndex T)))) := by
  classical
  -- Source Eq. (3): telescope the monotone full Kronecker preconditioner,
  -- drop the nonnegative terminal tail, and bound each PSD increment by the
  -- comparator-radius square times its trace.
  have hRadiusSq : ∀ t : Fin T,
      (∑ ij : FlatMatrixIndex m n,
        (matrixVec (run.iterate (currentIndex t)) ij - matrixVec Wstar ij) ^ 2) ≤
        (run.comparatorRadius Wstar) ^ 2 := by
    intro t
    exact matrixVec_current_sub_sq_sum_le_comparatorRadius_sq S run Wstar t
  have hRadiusTraceBound : ∀ (t : Fin T) (M : GenericSquare (FlatMatrixIndex m n)),
      M.PosSemidef →
      quadraticForm (matrixVec (run.iterate (currentIndex t)) - matrixVec Wstar) M ≤
        (run.comparatorRadius Wstar) ^ 2 * genericTrace M := by
    intro t M hM
    have hquad :=
      quadraticForm_le_sq_sum_mul_trace_of_posSemidef
        (matrixVec (run.iterate (currentIndex t)) - matrixVec Wstar) M hM
    have htrace_nonneg : 0 ≤ genericTrace M := by
      simpa [genericTrace] using hM.trace_nonneg
    have hmul :=
      mul_le_mul_of_nonneg_right (hRadiusSq t) htrace_nonneg
    exact le_trans hquad hmul
  let metric : Fin (T + 1) → GenericSquare (FlatMatrixIndex m n) := fun u =>
    ((matrixPower (run.leftAccumulator u) (1 / 4 : ℝ)
        (run.leftAccumulator_psd u)) ⊗ₖ
      (matrixPower (run.rightAccumulator u) (1 / 4 : ℝ)
        (run.rightAccumulator_psd u)))
  let Hext : Fin (T + 1) → GenericSquare (FlatMatrixIndex m n) := fun u =>
    if u.val = 0 then 0 else metric u
  have hTpos : 0 < T := by
    rcases ‹Nonempty (Fin T)› with ⟨t⟩
    exact Nat.lt_of_le_of_lt (Nat.zero_le t.val) t.isLt
  have hTne : T ≠ 0 := Nat.ne_of_gt hTpos
  have hHext0 : Hext ⟨0, Nat.zero_lt_succ T⟩ = 0 := by
    simp [Hext]
  have hHextInc : ∀ t : Fin T,
      (Hext (nextIndex t) - Hext (currentIndex t)).PosSemidef := by
    intro t
    have hnext : Hext (nextIndex t) = metric (nextIndex t) := by
      simp [Hext, nextIndex]
    by_cases ht0 : t.val = 0
    · have hcur : Hext (currentIndex t) = 0 := by
        simp [Hext, currentIndex, ht0]
      have hLpsd :
          (matrixPower (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
            (run.leftAccumulator_psd (nextIndex t))).PosSemidef := by
        exact matrixPower_posSemidef (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
          (run.leftAccumulator_psd (nextIndex t))
      have hRpsd :
          (matrixPower (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
            (run.rightAccumulator_psd (nextIndex t))).PosSemidef := by
        exact matrixPower_posSemidef (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
          (run.rightAccumulator_psd (nextIndex t))
      have hmetric_psd : (metric (nextIndex t)).PosSemidef := by
        simpa [metric] using
          Lemma_3_iv_kron_psd
            (matrixPower (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
              (run.leftAccumulator_psd (nextIndex t)))
            (matrixPower (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
              (run.rightAccumulator_psd (nextIndex t)))
            hLpsd hRpsd
      simpa [hnext, hcur] using hmetric_psd
    · have hcur : Hext (currentIndex t) = metric (currentIndex t) := by
        simp [Hext, currentIndex, ht0]
      simpa [hnext, hcur, metric] using
        theorem7_powered_kron_preconditioner_increment_psd S run t
  have hHextFinalPSD : (Hext ⟨T, Nat.lt_succ_self T⟩).PosSemidef := by
    have hLpsd :
        (matrixPower (run.leftAccumulator ⟨T, Nat.lt_succ_self T⟩) (1 / 4 : ℝ)
          (run.leftAccumulator_psd ⟨T, Nat.lt_succ_self T⟩)).PosSemidef := by
      exact matrixPower_posSemidef (run.leftAccumulator ⟨T, Nat.lt_succ_self T⟩) (1 / 4 : ℝ)
        (run.leftAccumulator_psd ⟨T, Nat.lt_succ_self T⟩)
    have hRpsd :
        (matrixPower (run.rightAccumulator ⟨T, Nat.lt_succ_self T⟩) (1 / 4 : ℝ)
          (run.rightAccumulator_psd ⟨T, Nat.lt_succ_self T⟩)).PosSemidef := by
      exact matrixPower_posSemidef (run.rightAccumulator ⟨T, Nat.lt_succ_self T⟩) (1 / 4 : ℝ)
        (run.rightAccumulator_psd ⟨T, Nat.lt_succ_self T⟩)
    have hmetric_psd : (metric ⟨T, Nat.lt_succ_self T⟩).PosSemidef := by
      simpa [metric] using
        Lemma_3_iv_kron_psd
          (matrixPower (run.leftAccumulator ⟨T, Nat.lt_succ_self T⟩) (1 / 4 : ℝ)
            (run.leftAccumulator_psd ⟨T, Nat.lt_succ_self T⟩))
          (matrixPower (run.rightAccumulator ⟨T, Nat.lt_succ_self T⟩) (1 / 4 : ℝ)
            (run.rightAccumulator_psd ⟨T, Nat.lt_succ_self T⟩))
          hLpsd hRpsd
    simpa [Hext, metric, hTne] using hmetric_psd
  have htelescope :=
    finite_changing_metric_quadratic_telescope_le_trace
      (T := T) (ι := FlatMatrixIndex m n)
      (x := fun u : Fin (T + 1) => matrixVec (run.iterate u) - matrixVec Wstar)
      (H := Hext) (D := run.comparatorRadius Wstar)
      hHext0 hHextInc hHextFinalPSD hRadiusTraceBound
  simpa [Hext, metric, nextIndex, finalIndex, hTne] using htelescope

private theorem generic_operator_monotone_powers {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : GenericSquare ι) (alpha : ℝ)
    (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hXY : X ≤ Y) (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1) :
    psdMatrixPower X alpha hX ≤ psdMatrixPower Y alpha hY := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let Xf : SquareMatrix (Fintype.card ι) := Matrix.reindexAlgEquiv ℝ ℝ e X
  let Yf : SquareMatrix (Fintype.card ι) := Matrix.reindexAlgEquiv ℝ ℝ e Y
  have hXf : Xf.PosSemidef := by
    simpa [Xf, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply] using
      ((Matrix.posSemidef_submatrix_equiv e.symm).2 hX)
  have hYf : Yf.PosSemidef := by
    simpa [Yf, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply] using
      ((Matrix.posSemidef_submatrix_equiv e.symm).2 hY)
  have hXYf : Xf ≤ Yf := by
    simpa [Xf, Yf] using (matrix_le_reindexAlgEquiv_iff e X Y).1 hXY
  have hfin :
      matrixPower Xf alpha hXf ≤ matrixPower Yf alpha hYf :=
    Lemma_6_operator_monotone_powers Xf Yf alpha hXf hYf hXYf halpha0 halpha1
  have hreindexed :
      Matrix.reindexAlgEquiv ℝ ℝ e (psdMatrixPower X alpha hX) ≤
        Matrix.reindexAlgEquiv ℝ ℝ e (psdMatrixPower Y alpha hY) := by
    rw [psdMatrixPower_reindexAlgEquiv e X alpha hX hXf]
    rw [psdMatrixPower_reindexAlgEquiv e Y alpha hY hYf]
    simpa [matrixPower, Xf, Yf] using hfin
  exact
    (matrix_le_reindexAlgEquiv_iff e
      (psdMatrixPower X alpha hX) (psdMatrixPower Y alpha hY)).2 hreindexed

private theorem psdMatrixPower_half_half_eq_quarter {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (C : GenericSquare ι) (hC : C.PosSemidef)
    (hHalf : (psdMatrixPower C (1 / 2 : ℝ) hC).PosSemidef) :
    psdMatrixPower (psdMatrixPower C (1 / 2 : ℝ) hC) (1 / 2 : ℝ) hHalf =
      psdMatrixPower C (1 / 4 : ℝ) hC := by
  classical
  let U : unitary (GenericSquare ι) := hC.1.eigenvectorUnitary
  let lam : ι → ℝ := hC.1.eigenvalues
  let Dhalf : GenericSquare ι := Matrix.diagonal (fun i : ι => (lam i) ^ (1 / 2 : ℝ))
  have hdiag :
      C =
        (U : GenericSquare ι) * Matrix.diagonal lam * star (U : GenericSquare ι) := by
    simpa [U, lam, Unitary.conjStarAlgAut_apply, Function.comp_def] using
      hC.1.spectral_theorem
  have hhalf_diag :
      psdMatrixPower C (1 / 2 : ℝ) hC =
        (U : GenericSquare ι) * Dhalf * star (U : GenericSquare ι) := by
    simpa [U, Dhalf, lam] using
      psdMatrixPower_eq_of_unitary_diagonalization C (1 / 2 : ℝ) hC U lam hdiag
        (fun i => hC.eigenvalues_nonneg i)
  have hhalf_eigs_nonneg : ∀ i : ι, 0 ≤ (lam i) ^ (1 / 2 : ℝ) := by
    intro i
    exact Real.rpow_nonneg (hC.eigenvalues_nonneg i) (1 / 2 : ℝ)
  have hscalar : ∀ i : ι, ((lam i) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) =
      (lam i) ^ (1 / 4 : ℝ) := by
    intro i
    have hmul :=
      Real.rpow_mul (hC.eigenvalues_nonneg i) (1 / 2 : ℝ) (1 / 2 : ℝ)
    calc
      ((lam i) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) =
          (lam i) ^ ((1 / 2 : ℝ) * (1 / 2 : ℝ)) := hmul.symm
      _ = (lam i) ^ (1 / 4 : ℝ) := by norm_num
  calc
    psdMatrixPower (psdMatrixPower C (1 / 2 : ℝ) hC) (1 / 2 : ℝ) hHalf =
        (U : GenericSquare ι) *
          Matrix.diagonal (fun i : ι => ((lam i) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ)) *
          star (U : GenericSquare ι) := by
          exact
            psdMatrixPower_eq_of_unitary_diagonalization
              (psdMatrixPower C (1 / 2 : ℝ) hC) (1 / 2 : ℝ) hHalf
              U (fun i : ι => (lam i) ^ (1 / 2 : ℝ)) hhalf_diag
              hhalf_eigs_nonneg
    _ = (U : GenericSquare ι) *
          Matrix.diagonal (fun i : ι => (lam i) ^ (1 / 4 : ℝ)) *
          star (U : GenericSquare ι) := by
          have hdiag_scalar :
              Matrix.diagonal (fun i : ι => ((lam i) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ)) =
                Matrix.diagonal (fun i : ι => (lam i) ^ (1 / 4 : ℝ)) := by
            ext i j
            by_cases hij : i = j
            · subst j
              simpa using hscalar i
            · simp [Matrix.diagonal, hij]
          rw [hdiag_scalar]
    _ = psdMatrixPower C (1 / 4 : ℝ) hC := by
          exact
            (psdMatrixPower_eq_of_unitary_diagonalization C (1 / 4 : ℝ) hC U lam
              hdiag (fun i => hC.eigenvalues_nonneg i)).symm

private theorem psdMatrixPower_matrixPower_mul {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (C : GenericSquare ι) (a b : ℝ) (hC : C.PosSemidef)
    (hPow : (psdMatrixPower C a hC).PosSemidef) :
    psdMatrixPower (psdMatrixPower C a hC) b hPow =
      psdMatrixPower C (a * b) hC := by
  simpa only [psdMatrixPower_eq_cfc] using
    TensorsProofSupport.Matrix.cfc_rpow_cfc_rpow_of_posSemidef C a b hC

private theorem psdMatrixPower_kronecker_right_generic {m : Nat} {κ : Type*}
    [Fintype κ] [DecidableEq κ]
    (A : SquareMatrix m) (B : GenericSquare κ) (s : ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    psdMatrixPower (A ⊗ₖ B) s (hA.kronecker hB) =
      matrixPower A s hA ⊗ₖ psdMatrixPower B s hB := by
  classical
  let eκ : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  let ep : Fin m × κ ≃ Fin m × Fin (Fintype.card κ) :=
    (Equiv.refl (Fin m)).prodCongr eκ
  let Bfin : SquareMatrix (Fintype.card κ) := Matrix.reindexAlgEquiv ℝ ℝ eκ B
  have hBfin : Bfin.PosSemidef := by
    simpa [Bfin, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply] using
      ((Matrix.posSemidef_submatrix_equiv eκ.symm).2 hB)
  have hbase_reindex :
      Matrix.reindexAlgEquiv ℝ ℝ ep (A ⊗ₖ B) =
        A ⊗ₖ Bfin := by
    ext ij kl
    rcases ij with ⟨i, j⟩
    rcases kl with ⟨i', j'⟩
    simp [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, ep, eκ, Bfin,
      Matrix.kroneckerMap_apply]
  have hpow_reindex :
      Matrix.reindexAlgEquiv ℝ ℝ ep
          (matrixPower A s hA ⊗ₖ psdMatrixPower B s hB) =
        matrixPower A s hA ⊗ₖ Matrix.reindexAlgEquiv ℝ ℝ eκ
          (psdMatrixPower B s hB) := by
    ext ij kl
    rcases ij with ⟨i, j⟩
    rcases kl with ⟨i', j'⟩
    simp [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, ep, eκ,
      Matrix.kroneckerMap_apply]
  have hAB : (A ⊗ₖ B).PosSemidef := hA.kronecker hB
  have hABfin : (A ⊗ₖ Bfin).PosSemidef := by
    simpa [Bfin] using Lemma_3_iv_kron_psd A Bfin hA hBfin
  have hAB_reindex :
      (Matrix.reindexAlgEquiv ℝ ℝ ep (A ⊗ₖ B)).PosSemidef := by
    simpa [hbase_reindex] using hABfin
  have hBpow_reindex :
      Matrix.reindexAlgEquiv ℝ ℝ eκ (psdMatrixPower B s hB) =
        matrixPower Bfin s hBfin := by
    simpa [matrixPower, Bfin] using
      psdMatrixPower_reindexAlgEquiv eκ B s hB hBfin
  have hleft_reindex :
      Matrix.reindexAlgEquiv ℝ ℝ ep
          (psdMatrixPower (A ⊗ₖ B) s hAB) =
        matrixPower A s hA ⊗ₖ Matrix.reindexAlgEquiv ℝ ℝ eκ
          (psdMatrixPower B s hB) := by
    calc
      Matrix.reindexAlgEquiv ℝ ℝ ep
          (psdMatrixPower (A ⊗ₖ B) s hAB) =
          psdMatrixPower (Matrix.reindexAlgEquiv ℝ ℝ ep (A ⊗ₖ B)) s
            hAB_reindex := by
            exact psdMatrixPower_reindexAlgEquiv ep (A ⊗ₖ B) s hAB
              hAB_reindex
      _ = psdMatrixPower (A ⊗ₖ Bfin) s hABfin := by
            exact psdMatrixPower_congr hbase_reindex s hAB_reindex hABfin
      _ = matrixPower A s hA ⊗ₖ matrixPower Bfin s hBfin := by
            rw [Subsingleton.elim hABfin (Lemma_3_iv_kron_psd A Bfin hA hBfin)]
            exact psdMatrixPower_kronecker A Bfin s hA hBfin
      _ = matrixPower A s hA ⊗ₖ Matrix.reindexAlgEquiv ℝ ℝ eκ
          (psdMatrixPower B s hB) := by
            rw [hBpow_reindex]
  exact (Matrix.reindexAlgEquiv ℝ ℝ ep).injective (by
    exact hleft_reindex.trans hpow_reindex.symm)

private theorem psdMatrixPower_one_generic {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (s : ℝ) (hI : (1 : GenericSquare ι).PosSemidef) :
    psdMatrixPower (1 : GenericSquare ι) s hI = 1 := by
  classical
  let U : unitary (GenericSquare ι) := (1 : unitary (GenericSquare ι))
  have hdiag : (1 : GenericSquare ι) =
      (U : GenericSquare ι) * Matrix.diagonal (fun _ : ι => (1 : ℝ)) *
        star (U : GenericSquare ι) := by
    simp [U]
  have hpow := psdMatrixPower_eq_of_unitary_diagonalization
    (C := (1 : GenericSquare ι)) s hI U (fun _ : ι => (1 : ℝ)) hdiag
    (by intro i; norm_num)
  calc
    psdMatrixPower (1 : GenericSquare ι) s hI =
        (U : GenericSquare ι) * Matrix.diagonal (fun i : ι => ((1 : ℝ) ^ s)) *
          star (U : GenericSquare ι) := hpow
    _ = 1 := by simp [U, Real.one_rpow]

private theorem psdMatrixPower_tensorKronecker {k : Nat} {dims : Fin k → Nat}
    (M : (i : Fin k) → SquareMatrix (dims i)) (s : ℝ)
    (hM : ∀ i : Fin k, (M i).PosSemidef)
    (hTK : (tensorKronecker M).PosSemidef) :
    psdMatrixPower (tensorKronecker M) s hTK =
      tensorKronecker (fun i : Fin k => matrixPower (M i) s (hM i)) := by
  simpa only [tensorKronecker, matrixPower, psdMatrixPower_eq_cfc] using
    (SOptLib.tensorKronecker_cfc_rpow M s hM)

private theorem psdMatrixPower_tensorKronecker_mode_inv_card_half {k : Nat}
    {dims : Fin k → Nat} [Nonempty (Fin k)]
    (A : (i : Fin k) → SquareMatrix (dims i))
    (hA : ∀ i : Fin k, (A i).PosSemidef)
    (hTK : (tensorKronecker
      (fun i : Fin k => matrixPower (A i) (1 / (k : ℝ)) (hA i))).PosSemidef) :
    psdMatrixPower
        (tensorKronecker
          (fun i : Fin k => matrixPower (A i) (1 / (k : ℝ)) (hA i)))
        (1 / 2 : ℝ) hTK =
      tensorKronecker
        (fun i : Fin k =>
          matrixPower (A i) (1 / ((2 : ℝ) * (k : ℝ))) (hA i)) := by
  classical
  let M : (i : Fin k) → SquareMatrix (dims i) :=
    fun i => matrixPower (A i) (1 / (k : ℝ)) (hA i)
  have hM : ∀ i : Fin k, (M i).PosSemidef := by
    intro i
    exact matrixPower_posSemidef (A i) (1 / (k : ℝ)) (hA i)
  have hdist :
      psdMatrixPower (tensorKronecker M) (1 / 2 : ℝ) hTK =
        tensorKronecker
          (fun i : Fin k => matrixPower (M i) (1 / 2 : ℝ) (hM i)) := by
    exact psdMatrixPower_tensorKronecker M (1 / 2 : ℝ) hM hTK
  have hk_pos_nat : 0 < k := Fin.pos_iff_nonempty.mpr inferInstance
  have hk_ne : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hk_pos_nat)
  have hexp :
      (1 / (k : ℝ)) * (1 / 2 : ℝ) =
        1 / ((2 : ℝ) * (k : ℝ)) := by
    field_simp [hk_ne]
  calc
    psdMatrixPower (tensorKronecker M) (1 / 2 : ℝ) hTK =
        tensorKronecker
          (fun i : Fin k => matrixPower (M i) (1 / 2 : ℝ) (hM i)) := hdist
    _ = tensorKronecker
        (fun i : Fin k =>
          matrixPower (A i) (1 / ((2 : ℝ) * (k : ℝ))) (hA i)) := by
          apply congrArg tensorKronecker
          funext i
          have hcomp :
              matrixPower (M i) (1 / 2 : ℝ) (hM i) =
                matrixPower (A i) ((1 / (k : ℝ)) * (1 / 2 : ℝ)) (hA i) := by
            simpa [M, matrixPower] using
              psdMatrixPower_matrixPower_mul (A i) (1 / (k : ℝ)) (1 / 2 : ℝ)
                (hA i) (hM i)
          rw [hcomp, hexp]

private theorem theorem10_tensor_hhat_order_from_prefix_rank_domination {k T : Nat}
    (S : TensorAlgorithm2 k T) (run : S.CorrectedRun)
    [Nonempty (Fin k)]
    (rankBound : Fin k → PosNat)
    (hrank : ∀ i : Fin k, ∀ t : Fin T,
      (matricization (run.gradientAt t) i).rank ≤ (rankBound i).1)
    (N : Fin (T + 1)) :
    psdMatrixPower
        (S.epsilon • (1 : GenericSquare (MultiIndex S.dims)) +
          ∑ s : Fin T,
            if s.1 < N.1 then vectorOuter ( (run.gradientAt s)) else 0)
        (1 / 2 : ℝ) (theorem10_hhat_prefix_posSemidef S run N) ≤
      Real.sqrt (TensorAlgorithm2.rankGeometricMean rankBound) •
        tensorKronecker
          (fun i : Fin k =>
            matrixPower (run.accumulator i N) (1 / ((2 : ℝ) * (k : ℝ)))
              (run.accumulator_psd i N)) := by
  classical
  have hdomLocal := theorem10_prefix_rank_domination S run rankBound hrank N
  have hdom :
      S.epsilon • (1 : Matrix (MultiIndex S.dims) (MultiIndex S.dims) ℝ) +
          (∑ t : Fin T,
            if t.1 < N.1 then Matrix.vecMulVec (run.gradientAt t) (run.gradientAt t) else 0) ≤
        SOptLib.positiveNatGeometricMean rankBound •
          SOptLib.tensorKronecker (fun i : Fin k =>
            cfc (R := ℝ) (p := IsSelfAdjoint)
              (fun x : ℝ => x ^ (1 / (k : ℝ)))
              (S.epsilon • (1 : Matrix (Fin (S.dims i)) (Fin (S.dims i)) ℝ) +
                ∑ t : Fin T,
                  if t.1 < N.1 then SOptLib.tensorContraction (run.gradientAt t) i else 0)) := by
    simpa only [vectorOuter, TensorAlgorithm2.rankGeometricMean, tensorKronecker,
      matrixPower, psdMatrixPower_eq_cfc,
      tensor_corrected_run_accumulator_eq_prefix_sum S run] using hdomLocal
  have hpowered :=
    SOptLib.regularized_tensor_rank_prefix_cfc_sqrt_le_sqrt_geometricMean_smul_tensorKronecker_half_contractions
      (G := run.gradientAt) (rankBound := rankBound) (epsilon := S.epsilon)
      (N := N) S.epsilon_nonneg hdom
  rw [psdMatrixPower_eq_cfc]
  simpa only [vectorOuter, TensorAlgorithm2.rankGeometricMean, tensorKronecker,
      matrixPower, psdMatrixPower_eq_cfc,
      tensor_corrected_run_accumulator_eq_prefix_sum S run] using hpowered

private theorem theorem7_hhat_prefix_posSemidef {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat) (N : Fin (T + 1)) :
    ((positiveRankReal rankBound * S.epsilon) •
        (1 : GenericSquare (FlatMatrixIndex m n)) +
      ∑ s : Fin T,
        if s.1 < N.1 then vectorOuter (matrixVec (run.gradientAt s)) else 0).PosSemidef := by
  simpa [Matrix.regularizedPrefixGram] using
    Matrix.regularizedPrefixGram_posSemidef
      (fun s : Fin T => matrixVec (run.gradientAt s))
      (mul_nonneg (le_of_lt (positiveRankReal_pos rankBound)) S.epsilon_nonneg) N

private noncomputable def theorem7_hhat_prefix_base {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat) (N : Fin (T + 1)) :
    GenericSquare (FlatMatrixIndex m n) :=
  Matrix.regularizedPrefixGram (fun s => matrixVec (run.gradientAt s))
    (positiveRankReal rankBound * S.epsilon) N

private noncomputable def theorem7_hhat_prefix {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat) (N : Fin (T + 1)) :
    GenericSquare (FlatMatrixIndex m n) :=
  psdMatrixPower (theorem7_hhat_prefix_base S run rankBound N) (1 / 2 : ℝ)
    (by
      simpa [theorem7_hhat_prefix_base] using
        theorem7_hhat_prefix_posSemidef S run rankBound N)

private theorem theorem7_hhat_prefix_zero_at_epsilon_zero {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat) (hepsilon : S.epsilon = 0) :
    theorem7_hhat_prefix S run rankBound ⟨0, Nat.succ_pos T⟩ = 0 := by
  classical
  have hbase :
      theorem7_hhat_prefix_base S run rankBound ⟨0, Nat.succ_pos T⟩ = 0 := by
    ext i j
    simp [theorem7_hhat_prefix_base, hepsilon]
  calc
    theorem7_hhat_prefix S run rankBound ⟨0, Nat.succ_pos T⟩ =
        psdMatrixPower (0 : GenericSquare (FlatMatrixIndex m n)) (1 / 2 : ℝ)
          Matrix.PosSemidef.zero := by
            exact psdMatrixPower_congr hbase (1 / 2 : ℝ) _ Matrix.PosSemidef.zero
    _ = 0 := by
      rw [psdMatrixPower_eq_cfc, ← CFC.rpow_eq_cfc_real]
      exact CFC.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)

private theorem theorem7_hhat_prefix_zero_not_posDef_at_epsilon_zero
    {T m n : Nat} [Nonempty (FlatMatrixIndex m n)]
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat) (hepsilon : S.epsilon = 0) :
    ¬ (theorem7_hhat_prefix S run rankBound ⟨0, Nat.succ_pos T⟩).PosDef := by
  rw [theorem7_hhat_prefix_zero_at_epsilon_zero S run rankBound hepsilon]
  intro hpos
  let i : FlatMatrixIndex m n := Classical.choice inferInstance
  let x : FlatMatrixIndex m n →₀ ℝ := Finsupp.single i 1
  have hx : x ≠ 0 := by
    simp [x]
  have hxpos := hpos.2 hx
  simpa using hxpos

private noncomputable def theorem7_hhat_prefix_gram_sum {T m n : Nat}
    {S : MatrixAlgorithm1 T m n} (run : S.CorrectedRun) (N : Fin (T + 1)) :
    GenericSquare (FlatMatrixIndex m n) :=
  ∑ s : Fin T,
    if s.1 < N.1 then vectorOuter (matrixVec (run.gradientAt s)) else 0

private theorem theorem7_hhat_prefix_gram_sum_posSemidef {T m n : Nat}
    {S : MatrixAlgorithm1 T m n} (run : S.CorrectedRun) (N : Fin (T + 1)) :
    (theorem7_hhat_prefix_gram_sum run N).PosSemidef := by
  classical
  refine finset_sum_generic_posSemidef_of_forall Finset.univ
    (fun s : Fin T =>
      if s.1 < N.1 then vectorOuter (matrixVec (run.gradientAt s)) else 0) ?_
  intro s _hs
  by_cases hsN : s.1 < N.1
  · simpa [theorem7_hhat_prefix_gram_sum, hsN] using
      vectorOuter_posSemidef (ι := FlatMatrixIndex m n) (matrixVec (run.gradientAt s))
  · simpa [theorem7_hhat_prefix_gram_sum, hsN] using
      (Matrix.PosSemidef.zero : (0 : GenericSquare (FlatMatrixIndex m n)).PosSemidef)

private noncomputable def theorem7_hhat_delta_prefix_base {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat) (delta : ℝ) (N : Fin (T + 1)) :
    GenericSquare (FlatMatrixIndex m n) :=
  (positiveRankReal rankBound * S.epsilon + delta) •
      (1 : GenericSquare (FlatMatrixIndex m n)) +
    theorem7_hhat_prefix_gram_sum run N

private theorem theorem7_hhat_delta_prefix_base_posDef {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat) {delta : ℝ} (hdelta : 0 < delta)
    (N : Fin (T + 1)) :
    (theorem7_hhat_delta_prefix_base S run rankBound delta N).PosDef := by
  simpa [theorem7_hhat_delta_prefix_base, theorem7_hhat_prefix_gram_sum,
    Matrix.regularizedPrefixGram, vectorOuter] using
    Matrix.regularizedPrefixGram_posDef
      (fun s : Fin T => matrixVec (run.gradientAt s))
      (add_pos_of_nonneg_of_pos
        (mul_nonneg (le_of_lt (positiveRankReal_pos rankBound)) S.epsilon_nonneg)
        hdelta) N

private noncomputable def theorem7_hhat_delta_prefix {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat) (delta : ℝ) (N : Fin (T + 1))
    (hbase : (theorem7_hhat_delta_prefix_base S run rankBound delta N).PosSemidef) :
    GenericSquare (FlatMatrixIndex m n) :=
  psdMatrixPower (theorem7_hhat_delta_prefix_base S run rankBound delta N)
    (1 / 2 : ℝ) hbase

private theorem theorem7_hhat_delta_prefix_posDef {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat) {delta : ℝ} (hdelta : 0 < delta)
    (N : Fin (T + 1)) :
    (theorem7_hhat_delta_prefix S run rankBound delta N
      (theorem7_hhat_delta_prefix_base_posDef
        S run rankBound hdelta N).posSemidef).PosDef := by
  simpa [theorem7_hhat_delta_prefix] using
    psdMatrixPower_posDef_of_posDef_pos_exp
      (theorem7_hhat_delta_prefix_base S run rankBound delta N)
      (1 / 2 : ℝ)
      (theorem7_hhat_delta_prefix_base_posDef S run rankBound hdelta N)
      (by norm_num)

private noncomputable def theorem7_hhat_delta_prefix_pd {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat) (delta : ℝ) (hdelta : 0 < delta)
    (N : Fin (T + 1)) : GenericSquare (FlatMatrixIndex m n) :=
  theorem7_hhat_delta_prefix S run rankBound delta N
    (theorem7_hhat_delta_prefix_base_posDef
      S run rankBound hdelta N).posSemidef

private theorem theorem7_hhat_delta_prefix_pd_posDef {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat) {delta : ℝ} (hdelta : 0 < delta)
    (N : Fin (T + 1)) :
    (theorem7_hhat_delta_prefix_pd S run rankBound delta hdelta N).PosDef := by
  simpa [theorem7_hhat_delta_prefix_pd] using
    theorem7_hhat_delta_prefix_posDef S run rankBound hdelta N

private theorem theorem7_hhat_delta_lemma2_posDef_premise {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat) {delta : ℝ} (hdelta : 0 < delta) :
    ∀ N : Fin (T + 1),
      (theorem7_hhat_delta_prefix_pd S run rankBound delta hdelta N).PosDef := by
  intro N
  exact theorem7_hhat_delta_prefix_pd_posDef S run rankBound hdelta N

private noncomputable def theorem7_equation6_potential {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (rankBound : PosNat)
    (H : GenericSquare (FlatMatrixIndex m n)) : ℝ :=
  Matrix.traceInversePotential (positiveRankReal rankBound * S.epsilon) H

private noncomputable def theorem7_equation6_delta_potential {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (rankBound : PosNat) (delta : ℝ)
    (H : GenericSquare (FlatMatrixIndex m n)) : ℝ :=
  genericTrace H +
    (positiveRankReal rankBound * S.epsilon + delta) * genericTrace H⁻¹

private theorem generic_transpose_eq_self_of_posSemidef {ι : Type*}
    [Fintype ι] [DecidableEq ι] (C : GenericSquare ι) (hC : C.PosSemidef) :
    C.transpose = C := by
  have hstar : star C = C := hC.1.eq
  ext i j
  have hij := congrFun (congrFun hstar j) i
  simpa [Matrix.star_apply] using hij.symm

private theorem generic_transpose_eq_self_of_posDef {ι : Type*}
    [Fintype ι] [DecidableEq ι] (C : GenericSquare ι) (hC : C.PosDef) :
    C.transpose = C :=
  generic_transpose_eq_self_of_posSemidef C hC.posSemidef

private theorem generic_inv_mul_of_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : GenericSquare ι) (hC : C.PosDef) :
    C⁻¹ * C = 1 := by
  classical
  have hdet_ne : C.det ≠ 0 := ne_of_gt hC.det_pos
  letI : Invertible C.det := invertibleOfNonzero hdet_ne
  letI : Invertible C := Matrix.invertibleOfDetInvertible C
  exact Matrix.inv_mul_of_invertible C

private theorem generic_mul_inv_of_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : GenericSquare ι) (hC : C.PosDef) :
    C * C⁻¹ = 1 := by
  classical
  have hdet_ne : C.det ≠ 0 := ne_of_gt hC.det_pos
  letI : Invertible C.det := invertibleOfNonzero hdet_ne
  letI : Invertible C := Matrix.invertibleOfDetInvertible C
  exact Matrix.mul_inv_of_invertible C

private theorem generic_inv_transpose_eq_self_of_posDef {ι : Type*}
    [Fintype ι] [DecidableEq ι] (C : GenericSquare ι) (hC : C.PosDef) :
    (C⁻¹).transpose = C⁻¹ := by
  ext i j
  have h := (hC.isHermitian.inv).apply j i
  simpa [Matrix.star_apply] using h.symm

private theorem genericTrace_transpose_mul_self_nonneg {ι : Type*}
    [Fintype ι] [DecidableEq ι] (A : GenericSquare ι) :
    0 ≤ genericTrace (A.transpose * A) := by
  classical
  unfold genericTrace Matrix.trace
  change 0 ≤ ∑ i : ι, ∑ j : ι, A j i * A j i
  exact Finset.sum_nonneg (by
    intro i _hi
    exact Finset.sum_nonneg (by
      intro j _hj
      exact mul_self_nonneg (A j i)))

private theorem generic_sqrt_inv_mul_inv_eq_inv_of_square {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (K R : GenericSquare ι) (hK : K.PosDef) (hR : R.PosDef) (hRsqr : R * R = K) :
    R⁻¹ * R⁻¹ = K⁻¹ := by
  classical
  have hR_left : R⁻¹ * R = (1 : GenericSquare ι) := generic_inv_mul_of_posDef R hR
  have hR_right : R * R⁻¹ = (1 : GenericSquare ι) := generic_mul_inv_of_posDef R hR
  have hK_right : K * K⁻¹ = (1 : GenericSquare ι) := generic_mul_inv_of_posDef K hK
  have hcancel : (R⁻¹ * R⁻¹) * (R * R) = (1 : GenericSquare ι) := by
    calc
      (R⁻¹ * R⁻¹) * (R * R) = R⁻¹ * (R⁻¹ * R) * R := by simp [mul_assoc]
      _ = 1 := by rw [hR_left]; simp [hR_left]
  calc
    R⁻¹ * R⁻¹ = (R⁻¹ * R⁻¹) * 1 := by simp
    _ = (R⁻¹ * R⁻¹) * (K * K⁻¹) := by rw [hK_right]
    _ = ((R⁻¹ * R⁻¹) * K) * K⁻¹ := by simp [mul_assoc]
    _ = ((R⁻¹ * R⁻¹) * (R * R)) * K⁻¹ := by rw [hRsqr]
    _ = K⁻¹ := by
      rw [hcancel]
      simp

set_option maxHeartbeats 800000 in
private theorem genericTrace_trace_young_posDef {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (H K : GenericSquare ι) (hH : H.PosDef) (hK : K.PosDef) :
    2 * genericTrace H ≤ genericTrace (H * H * K⁻¹) + genericTrace K := by
  simpa [genericTrace] using
    Matrix.two_mul_trace_le_trace_mul_mul_inv_add_trace_of_posDef H K hH.1 hK

private theorem trace_regularized_sqrt_objective_eq_two_trace_of_square_identity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : GenericSquare ι) (c : ℝ) (H : GenericSquare ι)
    (hH : H.PosDef)
    (hHsqr : H * H = c • (1 : GenericSquare ι) + M) :
    genericTrace (M * H⁻¹) + (genericTrace H + c * genericTrace H⁻¹) =
      2 * genericTrace H := by
  simpa [genericTrace, Matrix.traceInversePotential_def] using
    Matrix.trace_mul_inv_add_traceInversePotential_eq_two_trace_of_square M c H hH.isUnit hHsqr

/- Matrix AM-GM bridge behind the paper's derivative sentence in Theorem 7,
   lines 523-531.  This is the remaining noncommutative spectral inequality
   after the square-root construction has been separated out: if
   `H^2 = c I + M`, then the regularized trace objective is minimized at
   `H` over the positive-definite cone. -/
private theorem trace_regularized_sqrt_minimizer_of_square_identity {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (M : GenericSquare ι) (c : ℝ) (H : GenericSquare ι)
    (hH : H.PosDef)
    (K : GenericSquare ι) (hK : K.PosDef)
    (hHsqr : H * H = c • (1 : GenericSquare ι) + M) :
    genericTrace (M * H⁻¹) + (genericTrace H + c * genericTrace H⁻¹) ≤
      genericTrace (M * K⁻¹) + (genericTrace K + c * genericTrace K⁻¹) := by
  simpa [genericTrace, Matrix.traceInversePotential_def] using
    Matrix.traceInversePotential_objective_minimized_of_square
      (M := M) (c := c) (H := H) (K := K)
      (hHunit := hH.isUnit) (hHherm := hH.1) (hK := hK) (hHsqr := hHsqr)

/- Source Theorem 7, Eq. (6), reduces the Lemma 2 minimizer premise to
   the spectral fact that `sqrt (c I + M)` minimizes
   `Tr(M K^{-1}) + Tr(K) + c Tr(K^{-1})` over `K ≻ 0`.
   This is the remaining full-matrix spectral calculus leaf; it is private
   and keeps the δ repair away from public theorem assumptions. -/
private theorem trace_regularized_sqrt_minimizer_of_posDef {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (M : GenericSquare ι) (c : ℝ)
    (hA : (c • (1 : GenericSquare ι) + M).PosDef)
    (K : GenericSquare ι) (hK : K.PosDef) :
    let H : GenericSquare ι :=
      psdMatrixPower (c • (1 : GenericSquare ι) + M) (1 / 2 : ℝ)
        hA.posSemidef
    genericTrace (M * H⁻¹) + (genericTrace H + c * genericTrace H⁻¹) ≤
      genericTrace (M * K⁻¹) + (genericTrace K + c * genericTrace K⁻¹) := by
  simpa only [genericTrace, Matrix.traceInversePotential_def,
    psdMatrixPower_eq_cfc, ← CFC.rpow_eq_cfc_real hA.posSemidef.nonneg,
    ← CFC.sqrt_eq_rpow] using
      Matrix.cfc_sqrt_minimizes_traceInversePotential_objective M c hA K hK

private theorem generic_regularized_prefix_base_posDef {T : Nat}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Fin T → ι → ℝ) {c : ℝ} (hc : 0 < c) (N : Fin (T + 1)) :
    (c • (1 : GenericSquare ι) +
      ∑ s : Fin T, if s.1 < N.1 then vectorOuter (g s) else 0).PosDef := by
  classical
  have hidentity : (c • (1 : GenericSquare ι)).PosDef :=
    Matrix.PosDef.one.smul hc
  have hprefix :
      (∑ s : Fin T, if s.1 < N.1 then vectorOuter (g s) else 0 :
        GenericSquare ι).PosSemidef := by
    refine finset_sum_generic_posSemidef_of_forall Finset.univ
      (fun s : Fin T => if s.1 < N.1 then vectorOuter (g s) else 0) ?_
    intro s _hs
    by_cases hsN : s.1 < N.1
    · simpa [hsN] using vectorOuter_posSemidef (ι := ι) (g s)
    · simpa [hsN] using
        (Matrix.PosSemidef.zero : (0 : GenericSquare ι).PosSemidef)
  exact hidentity.add_posSemidef hprefix

private theorem generic_regularized_hhat_equation6_bound {T : Nat}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Fin T → ι → ℝ) {c : ℝ} (hc : 0 < c) :
    (∑ t : Fin T,
      dualQuadraticForm (g t)
        (psdMatrixPower
          (c • (1 : GenericSquare ι) +
            ∑ s : Fin T,
              if s.1 < (nextIndex t).1 then vectorOuter (g s) else 0)
          (1 / 2 : ℝ)
          (generic_regularized_prefix_base_posDef g hc (nextIndex t)).posSemidef)) ≤
      2 * genericTrace
        (psdMatrixPower
          (c • (1 : GenericSquare ι) +
            ∑ s : Fin T,
              if s.1 < (finalIndex T).1 then vectorOuter (g s) else 0)
          (1 / 2 : ℝ)
          (generic_regularized_prefix_base_posDef g hc (finalIndex T)).posSemidef) := by
  classical
  have hsqrt_eq_cfc (N : Fin (T + 1)) :
      CFC.sqrt (Matrix.regularizedPrefixGram g c N) =
        cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ))
          (Matrix.regularizedPrefixGram g c N) := by
    rw [CFC.sqrt_eq_rpow,
      CFC.rpow_eq_cfc_real
        (Matrix.regularizedPrefixGram_posDef g hc N).posSemidef.nonneg]
  have hbound :=
    Matrix.sum_dualQuadraticForm_regularizedPrefixGram_sqrt_le_two_trace g hc
  simp only [hsqrt_eq_cfc] at hbound
  simpa only [dualQuadraticForm, genericTrace, psdMatrixPower_eq_cfc,
    vectorOuter, Matrix.vecMulVec, Matrix.regularizedPrefixGram,
    nextIndex, finalIndex] using
      hbound

private noncomputable def theorem7_hhat_delta_lemma2_minimizer_premise {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat) {delta : ℝ} (hdelta : 0 < delta) : Prop :=
  ∀ N : Fin (T + 1), ∀ K : GenericSquare (FlatMatrixIndex m n), K.PosDef →
    genericTrace
        (theorem7_hhat_prefix_gram_sum run N *
          (theorem7_hhat_delta_prefix_pd S run rankBound delta hdelta N)⁻¹) +
        theorem7_equation6_delta_potential S rankBound delta
          (theorem7_hhat_delta_prefix_pd S run rankBound delta hdelta N) ≤
    genericTrace (theorem7_hhat_prefix_gram_sum run N * K⁻¹) +
        theorem7_equation6_delta_potential S rankBound delta K

private theorem theorem7_hhat_delta_lemma2_minimizer_premise_from_spectral
    {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat) {delta : ℝ} (hdelta : 0 < delta) :
    theorem7_hhat_delta_lemma2_minimizer_premise S run rankBound hdelta := by
  classical
  intro N K hK
  simpa [theorem7_hhat_delta_lemma2_minimizer_premise,
    theorem7_hhat_delta_prefix_pd, theorem7_hhat_delta_prefix,
    theorem7_hhat_delta_prefix_base, theorem7_equation6_delta_potential] using
    trace_regularized_sqrt_minimizer_of_posDef
      (ι := FlatMatrixIndex m n)
      (theorem7_hhat_prefix_gram_sum run N)
      (positiveRankReal rankBound * S.epsilon + delta)
      (theorem7_hhat_delta_prefix_base_posDef S run rankBound hdelta N)
      K hK

private noncomputable def theorem7_hhat_delta_equation6_bound_prop {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat) {delta : ℝ} (hdelta : 0 < delta) : Prop :=
  ∑ t : Fin T,
      dualQuadraticForm (matrixVec (run.gradientAt t))
        (theorem7_hhat_delta_prefix_pd S run rankBound delta hdelta (nextIndex t)) ≤
    2 * genericTrace
      (theorem7_hhat_delta_prefix_pd S run rankBound delta hdelta (finalIndex T))

private theorem theorem7_hhat_delta_equation6_bound {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat) {delta : ℝ} (hdelta : 0 < delta) :
    theorem7_hhat_delta_equation6_bound_prop S run rankBound hdelta := by
  classical
  let c : ℝ := positiveRankReal rankBound * S.epsilon + delta
  let g : Fin T → FlatMatrixIndex m n → ℝ := fun t => matrixVec (run.gradientAt t)
  let M : Fin (T + 1) → GenericSquare (FlatMatrixIndex m n) :=
    fun N => theorem7_hhat_prefix_gram_sum run N
  let H : Fin (T + 1) → GenericSquare (FlatMatrixIndex m n) :=
    fun N => theorem7_hhat_delta_prefix_pd S run rankBound delta hdelta N
  let Phi : GenericSquare (FlatMatrixIndex m n) → ℝ :=
    theorem7_equation6_delta_potential S rankBound delta
  have hM :
      ∀ N : Fin (T + 1),
        M N = ∑ s : Fin T, if s.1 < N.1 then vectorOuter (g s) else 0 := by
    intro N
    rfl
  have hHpd : ∀ N : Fin (T + 1), (H N).PosDef := by
    intro N
    simpa [H] using
      theorem7_hhat_delta_lemma2_posDef_premise S run rankBound hdelta N
  have hMin :
      ∀ N : Fin (T + 1), ∀ K : GenericSquare (FlatMatrixIndex m n), K.PosDef →
        genericTrace (M N * (H N)⁻¹) + Phi (H N) ≤
          genericTrace (M N * K⁻¹) + Phi K := by
    simpa [M, H, Phi] using
      theorem7_hhat_delta_lemma2_minimizer_premise_from_spectral
        S run rankBound hdelta
  have hLemma :=
    Lemma_2_FTL_BTL_potential_generic
      g M H Phi hM hHpd hMin
  let HT : GenericSquare (FlatMatrixIndex m n) := H (finalIndex T)
  let H0 : GenericSquare (FlatMatrixIndex m n) := H ⟨0, Nat.succ_pos T⟩
  have hHTpd : HT.PosDef := by
    simpa [HT] using hHpd (finalIndex T)
  have hH0pd : H0.PosDef := by
    simpa [H0] using hHpd ⟨0, Nat.succ_pos T⟩
  have hfinal_sum :
      (∑ t : Fin T, dualQuadraticForm (g t) HT) =
        genericTrace (M (finalIndex T) * HT⁻¹) := by
    have hobj :=
      prefix_objective_eq_genericTrace_objective
        g M (fun _ : GenericSquare (FlatMatrixIndex m n) => (0 : ℝ))
        hM (finalIndex T) HT hHTpd
    have hprefix :
        (∑ s : Fin T, if s.1 < (finalIndex T).1 then dualQuadraticForm (g s) HT else 0) =
          ∑ s : Fin T, dualQuadraticForm (g s) HT := by
      simpa [finalIndex] using
        fin_prefix_sum_final (T := T) (fun s : Fin T => dualQuadraticForm (g s) HT)
    linarith
  have hHT_sq :
      HT * HT = c • (1 : GenericSquare (FlatMatrixIndex m n)) + M (finalIndex T) := by
    simpa [HT, H, M, c, theorem7_hhat_delta_prefix_pd,
      theorem7_hhat_delta_prefix, theorem7_hhat_delta_prefix_base] using
      psdMatrixPower_half_mul_self
        (theorem7_hhat_delta_prefix_base S run rankBound delta (finalIndex T))
        (theorem7_hhat_delta_prefix_base_posDef
          S run rankBound hdelta (finalIndex T)).posSemidef
  have hfinal_objective :
      (∑ t : Fin T, dualQuadraticForm (g t) HT) + Phi HT =
        2 * genericTrace HT := by
    calc
      (∑ t : Fin T, dualQuadraticForm (g t) HT) + Phi HT
          = genericTrace (M (finalIndex T) * HT⁻¹) +
              (genericTrace HT + c * genericTrace HT⁻¹) := by
              rw [hfinal_sum]
              simp [Phi, theorem7_equation6_delta_potential, c]
      _ = 2 * genericTrace HT := by
              exact
                trace_regularized_sqrt_objective_eq_two_trace_of_square_identity
                  (M (finalIndex T)) c HT hHTpd hHT_sq
  have hc_nonneg : 0 ≤ c := by
    have hbase : 0 ≤ positiveRankReal rankBound * S.epsilon :=
      mul_nonneg (le_of_lt (positiveRankReal_pos rankBound)) S.epsilon_nonneg
    exact le_trans hbase (le_add_of_nonneg_right (le_of_lt hdelta))
  have hPhi0_nonneg : 0 ≤ Phi H0 := by
    have htrace_H0 : 0 ≤ genericTrace H0 :=
      genericTrace_nonneg_of_posSemidef H0 hH0pd.posSemidef
    have htrace_inv_H0 : 0 ≤ genericTrace H0⁻¹ :=
      genericTrace_nonneg_of_posSemidef H0⁻¹ (Matrix.PosDef.inv hH0pd).posSemidef
    simp [Phi, theorem7_equation6_delta_potential, c]
    nlinarith
  have hLemma' :
      ∑ t : Fin T, dualQuadraticForm (g t) (H (nextIndex t)) ≤
        2 * genericTrace HT - Phi H0 := by
    calc
      ∑ t : Fin T, dualQuadraticForm (g t) (H (nextIndex t))
          ≤ (∑ t : Fin T, dualQuadraticForm (g t) (H ⟨T, Nat.lt_succ_self T⟩)) +
              Phi (H ⟨T, Nat.lt_succ_self T⟩) - Phi (H ⟨0, Nat.succ_pos T⟩) := hLemma
      _ = 2 * genericTrace HT - Phi H0 := by
              rw [show H ⟨T, Nat.lt_succ_self T⟩ = HT by rfl]
              rw [show H ⟨0, Nat.succ_pos T⟩ = H0 by rfl]
              rw [hfinal_objective]
  have htarget_g :
      ∑ t : Fin T, dualQuadraticForm (g t) (H (nextIndex t)) ≤
        2 * genericTrace HT := by
    linarith
  simpa [theorem7_hhat_delta_equation6_bound_prop, g, H, HT] using htarget_g

private noncomputable def theorem7_singular_total_inverse_matrix :
    GenericSquare (Fin 2) :=
  fun i j => if i = 0 ∧ j = 0 then 1 else 0

private noncomputable def theorem7_singular_total_inverse_vector :
    Fin 2 → ℝ :=
  fun i => if i = 0 then 1 else 0

private noncomputable def theorem7_delta_regularized_witness_matrix
    (delta : ℝ) : GenericSquare (Fin 2) :=
  theorem7_singular_total_inverse_matrix + delta • (1 : GenericSquare (Fin 2))

private theorem theorem7_singular_total_inverse_dualQuadraticForm_zero :
    dualQuadraticForm theorem7_singular_total_inverse_vector
      theorem7_singular_total_inverse_matrix = 0 := by
  have hdet : Matrix.det theorem7_singular_total_inverse_matrix = 0 := by
    simp [theorem7_singular_total_inverse_matrix, Matrix.det_fin_two]
  simp [dualQuadraticForm, quadraticForm, theorem7_singular_total_inverse_vector,
    Matrix.inv_def, hdet]

private theorem theorem7_delta_regularized_witness_dualQuadraticForm_eq
    (delta : ℝ) (hdelta_ne : delta ≠ 0) (hone_delta_ne : 1 + delta ≠ 0) :
    dualQuadraticForm theorem7_singular_total_inverse_vector
      (theorem7_delta_regularized_witness_matrix delta) = (1 + delta)⁻¹ := by
  have hadj :
      Matrix.adjugate
          (theorem7_singular_total_inverse_matrix +
            delta • (1 : GenericSquare (Fin 2))) 0 0 = delta := by
    simp [theorem7_singular_total_inverse_matrix, Matrix.adjugate_fin_two]
  simp [dualQuadraticForm, quadraticForm, theorem7_singular_total_inverse_vector,
    theorem7_delta_regularized_witness_matrix, theorem7_singular_total_inverse_matrix,
    Matrix.inv_def, Matrix.det_fin_two, hadj]
  field_simp [hdelta_ne, hone_delta_ne]

private noncomputable def theorem7_equation6_regularized_domain_route {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat) (delta : ℝ) (hdelta : 0 < delta) :
    ∀ N : Fin (T + 1),
      (theorem7_hhat_delta_prefix_pd S run rankBound delta hdelta N).PosDef :=
  theorem7_hhat_delta_lemma2_posDef_premise S run rankBound hdelta

private theorem theorem7_hhat_order_from_prefix_rank_domination {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat)
    (hrank : ∀ t : Fin T, (run.gradientAt t).rank ≤ rankBound.1)
    (N : Fin (T + 1))
    (hHhat :
      ((positiveRankReal rankBound * S.epsilon) •
          (1 : GenericSquare (FlatMatrixIndex m n)) +
        ∑ s : Fin T,
          if s.1 < N.1 then vectorOuter (matrixVec (run.gradientAt s)) else 0).PosSemidef) :
    psdMatrixPower
        ((positiveRankReal rankBound * S.epsilon) •
            (1 : GenericSquare (FlatMatrixIndex m n)) +
          ∑ s : Fin T,
            if s.1 < N.1 then vectorOuter (matrixVec (run.gradientAt s)) else 0)
        (1 / 2 : ℝ) hHhat ≤
      Real.sqrt (positiveRankReal rankBound) •
        ((matrixPower (run.leftAccumulator N) (1 / 4 : ℝ)
            (run.leftAccumulator_psd N)) ⊗ₖ
          (matrixPower (run.rightAccumulator N) (1 / 4 : ℝ)
            (run.rightAccumulator_psd N))) := by
  classical
  let r : ℝ := positiveRankReal rankBound
  let M : GenericSquare (FlatMatrixIndex m n) :=
    ∑ s : Fin T,
      if s.1 < N.1 then vectorOuter (matrixVec (run.gradientAt s)) else 0
  let base : GenericSquare (FlatMatrixIndex m n) :=
    S.epsilon • (1 : GenericSquare (FlatMatrixIndex m n)) + (1 / r) • M
  let full : GenericSquare (FlatMatrixIndex m n) :=
    (matrixPower (run.leftAccumulator N) (1 / 2 : ℝ)
        (run.leftAccumulator_psd N)) ⊗ₖ
      (matrixPower (run.rightAccumulator N) (1 / 2 : ℝ)
        (run.rightAccumulator_psd N))
  let H : GenericSquare (FlatMatrixIndex m n) :=
    (matrixPower (run.leftAccumulator N) (1 / 4 : ℝ)
        (run.leftAccumulator_psd N)) ⊗ₖ
      (matrixPower (run.rightAccumulator N) (1 / 4 : ℝ)
        (run.rightAccumulator_psd N))
  have hrpos : 0 < r := by
    simpa [r] using positiveRankReal_pos rankBound
  have hrnonneg : 0 ≤ r := le_of_lt hrpos
  have hprefix : base ≤ full := by
    simpa [base, full, M, r] using
      theorem7_prefix_rank_domination S run rankBound hrank N
  have hscaled : r • base ≤ r • full :=
    smul_le_smul_of_nonneg_left hprefix hrnonneg
  have hscaled_left :
      r • base =
        (r * S.epsilon) • (1 : GenericSquare (FlatMatrixIndex m n)) + M := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [base, M, one_div, smul_add, smul_smul, Matrix.one_apply, hrpos.ne']
      field_simp [hrpos.ne']
    · simp [base, M, one_div, smul_add, smul_smul, Matrix.one_apply, hij, hrpos.ne']
  have hLhalf_psd :
      (matrixPower (run.leftAccumulator N) (1 / 2 : ℝ)
        (run.leftAccumulator_psd N)).PosSemidef :=
    matrixPower_posSemidef (run.leftAccumulator N) (1 / 2 : ℝ)
      (run.leftAccumulator_psd N)
  have hRhalf_psd :
      (matrixPower (run.rightAccumulator N) (1 / 2 : ℝ)
        (run.rightAccumulator_psd N)).PosSemidef :=
    matrixPower_posSemidef (run.rightAccumulator N) (1 / 2 : ℝ)
      (run.rightAccumulator_psd N)
  have hfull_psd : full.PosSemidef := by
    simpa [full] using
      Lemma_3_iv_kron_psd
        (matrixPower (run.leftAccumulator N) (1 / 2 : ℝ)
          (run.leftAccumulator_psd N))
        (matrixPower (run.rightAccumulator N) (1 / 2 : ℝ)
          (run.rightAccumulator_psd N))
        hLhalf_psd hRhalf_psd
  have hscaled_psd : (r • full).PosSemidef :=
    hfull_psd.smul hrnonneg
  have hroot_raw :
      psdMatrixPower
          ((positiveRankReal rankBound * S.epsilon) •
              (1 : GenericSquare (FlatMatrixIndex m n)) +
            ∑ s : Fin T,
              if s.1 < N.1 then vectorOuter (matrixVec (run.gradientAt s)) else 0)
          (1 / 2 : ℝ) hHhat ≤
        psdMatrixPower (r • full) (1 / 2 : ℝ) hscaled_psd := by
    have horder :
        ((positiveRankReal rankBound * S.epsilon) •
            (1 : GenericSquare (FlatMatrixIndex m n)) +
          ∑ s : Fin T,
            if s.1 < N.1 then vectorOuter (matrixVec (run.gradientAt s)) else 0) ≤
          r • full := by
      simpa [M, r] using hscaled_left ▸ hscaled
    exact
      generic_operator_monotone_powers
        ((positiveRankReal rankBound * S.epsilon) •
            (1 : GenericSquare (FlatMatrixIndex m n)) +
          ∑ s : Fin T,
            if s.1 < N.1 then vectorOuter (matrixVec (run.gradientAt s)) else 0)
        (r • full) (1 / 2 : ℝ) hHhat hscaled_psd horder
        (by norm_num) (by norm_num)
  have hfull_half_to_H :
      psdMatrixPower full (1 / 2 : ℝ) hfull_psd = H := by
    let Lhalf : SquareMatrix m :=
      matrixPower (run.leftAccumulator N) (1 / 2 : ℝ)
        (run.leftAccumulator_psd N)
    let Rhalf : SquareMatrix n :=
      matrixPower (run.rightAccumulator N) (1 / 2 : ℝ)
        (run.rightAccumulator_psd N)
    let Lquarter : SquareMatrix m :=
      matrixPower (run.leftAccumulator N) (1 / 4 : ℝ)
        (run.leftAccumulator_psd N)
    let Rquarter : SquareMatrix n :=
      matrixPower (run.rightAccumulator N) (1 / 4 : ℝ)
        (run.rightAccumulator_psd N)
    have hpow_kron :
        psdMatrixPower full (1 / 2 : ℝ) hfull_psd =
          matrixPower Lhalf (1 / 2 : ℝ) hLhalf_psd ⊗ₖ
            matrixPower Rhalf (1 / 2 : ℝ) hRhalf_psd := by
      have hkron_psd :
          (Lhalf ⊗ₖ Rhalf).PosSemidef :=
        Lemma_3_iv_kron_psd Lhalf Rhalf hLhalf_psd hRhalf_psd
      calc
        psdMatrixPower full (1 / 2 : ℝ) hfull_psd =
            psdMatrixPower (Lhalf ⊗ₖ Rhalf) (1 / 2 : ℝ) hkron_psd := by
              have hfull_eq : full = Lhalf ⊗ₖ Rhalf := by
                rfl
              exact psdMatrixPower_congr hfull_eq (1 / 2 : ℝ) hfull_psd hkron_psd
        _ = matrixPower Lhalf (1 / 2 : ℝ) hLhalf_psd ⊗ₖ
              matrixPower Rhalf (1 / 2 : ℝ) hRhalf_psd := by
              exact psdMatrixPower_kronecker Lhalf Rhalf (1 / 2 : ℝ)
                hLhalf_psd hRhalf_psd
    have hLquarter :
        matrixPower Lhalf (1 / 2 : ℝ) hLhalf_psd = Lquarter := by
      simpa [matrixPower, Lhalf, Lquarter] using
        psdMatrixPower_half_half_eq_quarter
          (run.leftAccumulator N) (run.leftAccumulator_psd N) hLhalf_psd
    have hRquarter :
        matrixPower Rhalf (1 / 2 : ℝ) hRhalf_psd = Rquarter := by
      simpa [matrixPower, Rhalf, Rquarter] using
        psdMatrixPower_half_half_eq_quarter
          (run.rightAccumulator N) (run.rightAccumulator_psd N) hRhalf_psd
    calc
      psdMatrixPower full (1 / 2 : ℝ) hfull_psd =
          matrixPower Lhalf (1 / 2 : ℝ) hLhalf_psd ⊗ₖ
            matrixPower Rhalf (1 / 2 : ℝ) hRhalf_psd := hpow_kron
      _ = Lquarter ⊗ₖ Rquarter := by
          rw [hLquarter, hRquarter]
      _ = H := by
          rfl
  calc
    psdMatrixPower
        ((positiveRankReal rankBound * S.epsilon) •
            (1 : GenericSquare (FlatMatrixIndex m n)) +
          ∑ s : Fin T,
            if s.1 < N.1 then vectorOuter (matrixVec (run.gradientAt s)) else 0)
        (1 / 2 : ℝ) hHhat
        ≤ psdMatrixPower (r • full) (1 / 2 : ℝ) hscaled_psd := hroot_raw
    _ = Real.sqrt r • H := by
      calc
        psdMatrixPower (r • full) (1 / 2 : ℝ) hscaled_psd =
            r ^ (1 / 2 : ℝ) • psdMatrixPower full (1 / 2 : ℝ) hfull_psd := by
              exact psdMatrixPower_smul_nonneg r (1 / 2 : ℝ) full hfull_psd
                hrnonneg hscaled_psd
        _ = Real.sqrt r • H := by
              rw [hfull_half_to_H]
              simp [Real.sqrt_eq_rpow]
    _ = Real.sqrt (positiveRankReal rankBound) •
        ((matrixPower (run.leftAccumulator N) (1 / 4 : ℝ)
            (run.leftAccumulator_psd N)) ⊗ₖ
          (matrixPower (run.rightAccumulator N) (1 / 4 : ℝ)
            (run.rightAccumulator_psd N))) := by
      simp [H, r]

private theorem theorem7_hhat_final_trace_to_algorithm_trace {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat)
    (hEq5Final :
      psdMatrixPower
          ((positiveRankReal rankBound * S.epsilon) •
              (1 : GenericSquare (FlatMatrixIndex m n)) +
            ∑ s : Fin T,
              if s.1 < (finalIndex T).1 then vectorOuter (matrixVec (run.gradientAt s)) else 0)
          (1 / 2 : ℝ)
          (theorem7_hhat_prefix_posSemidef S run rankBound (finalIndex T)) ≤
        Real.sqrt (positiveRankReal rankBound) •
          ((matrixPower (run.leftAccumulator (finalIndex T)) (1 / 4 : ℝ)
              (run.leftAccumulator_psd (finalIndex T))) ⊗ₖ
            (matrixPower (run.rightAccumulator (finalIndex T)) (1 / 4 : ℝ)
              (run.rightAccumulator_psd (finalIndex T)))) ) :
    2 * Real.sqrt (positiveRankReal rankBound) *
        genericTrace
          (psdMatrixPower
            ((positiveRankReal rankBound * S.epsilon) •
                (1 : GenericSquare (FlatMatrixIndex m n)) +
              ∑ s : Fin T,
                if s.1 < (finalIndex T).1 then vectorOuter (matrixVec (run.gradientAt s)) else 0)
            (1 / 2 : ℝ)
            (theorem7_hhat_prefix_posSemidef S run rankBound (finalIndex T))) ≤
      2 * positiveRankReal rankBound *
        genericTrace
          ((matrixPower (run.leftAccumulator (finalIndex T)) (1 / 4 : ℝ)
              (run.leftAccumulator_psd (finalIndex T))) ⊗ₖ
            (matrixPower (run.rightAccumulator (finalIndex T)) (1 / 4 : ℝ)
              (run.rightAccumulator_psd (finalIndex T)))) := by
  classical
  let r : ℝ := positiveRankReal rankBound
  let Hhat : GenericSquare (FlatMatrixIndex m n) :=
    psdMatrixPower
      ((positiveRankReal rankBound * S.epsilon) •
          (1 : GenericSquare (FlatMatrixIndex m n)) +
        ∑ s : Fin T,
          if s.1 < (finalIndex T).1 then vectorOuter (matrixVec (run.gradientAt s)) else 0)
      (1 / 2 : ℝ)
      (theorem7_hhat_prefix_posSemidef S run rankBound (finalIndex T))
  let Halg : GenericSquare (FlatMatrixIndex m n) :=
    (matrixPower (run.leftAccumulator (finalIndex T)) (1 / 4 : ℝ)
        (run.leftAccumulator_psd (finalIndex T))) ⊗ₖ
      (matrixPower (run.rightAccumulator (finalIndex T)) (1 / 4 : ℝ)
        (run.rightAccumulator_psd (finalIndex T)))
  have hrpos : 0 < r := by
    simpa [r] using positiveRankReal_pos rankBound
  have hrnonneg : 0 ≤ r := le_of_lt hrpos
  have htrace_le :
      genericTrace Hhat ≤ genericTrace (Real.sqrt r • Halg) := by
    exact genericTrace_mono_of_matrix_le (by simpa [Hhat, Halg, r] using hEq5Final)
  have htrace_smul :
      genericTrace (Real.sqrt r • Halg) = Real.sqrt r * genericTrace Halg := by
    simp [genericTrace]
  have htrace_le' : genericTrace Hhat ≤ Real.sqrt r * genericTrace Halg := by
    simpa [htrace_smul] using htrace_le
  have hcoef_nonneg : 0 ≤ 2 * Real.sqrt r := by
    positivity
  have hscaled :
      (2 * Real.sqrt r) * genericTrace Hhat ≤
        (2 * Real.sqrt r) * (Real.sqrt r * genericTrace Halg) :=
    mul_le_mul_of_nonneg_left htrace_le' hcoef_nonneg
  have hsqrt_mul : Real.sqrt r * Real.sqrt r = r := by
    have hsqrt_sq : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt hrnonneg
    nlinarith
  calc
    2 * Real.sqrt (positiveRankReal rankBound) * genericTrace Hhat
        = (2 * Real.sqrt r) * genericTrace Hhat := by
            simp [r, mul_assoc]
    _ ≤ (2 * Real.sqrt r) * (Real.sqrt r * genericTrace Halg) := hscaled
    _ = 2 * r * genericTrace Halg := by
            calc
              (2 * Real.sqrt r) * (Real.sqrt r * genericTrace Halg) =
                  2 * (Real.sqrt r * Real.sqrt r) * genericTrace Halg := by ring
              _ = 2 * r * genericTrace Halg := by rw [hsqrt_mul]
    _ = 2 * positiveRankReal rankBound * genericTrace Halg := by
            simp [r]

private noncomputable def theorem7_hhat_delta_dual_value_total {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat) (delta : ℝ) (t : Fin T) : ℝ :=
  if hdelta : 0 < delta then
    dualQuadraticForm (matrixVec (run.gradientAt t))
      (theorem7_hhat_delta_prefix_pd S run rankBound delta hdelta (nextIndex t))
  else
    0

private noncomputable def theorem7_hhat_delta_trace_value_total {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat) (delta : ℝ) : ℝ :=
  if hdelta : 0 < delta then
    genericTrace
      (theorem7_hhat_delta_prefix_pd S run rankBound delta hdelta (finalIndex T))
  else
    0

private theorem theorem7_hhat_delta_trace_value_total_spectral {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat) {delta : ℝ} (hdelta : 0 < delta) :
    theorem7_hhat_delta_trace_value_total S run rankBound delta =
      ∑ i : FlatMatrixIndex m n,
        ((theorem7_hhat_prefix_posSemidef S run rankBound (finalIndex T)).1.eigenvalues i +
            delta) ^ (1 / 2 : ℝ) := by
  classical
  let A : GenericSquare (FlatMatrixIndex m n) :=
    (positiveRankReal rankBound * S.epsilon) •
        (1 : GenericSquare (FlatMatrixIndex m n)) +
      ∑ s : Fin T,
        if s.1 < (finalIndex T).1 then
          vectorOuter (matrixVec (run.gradientAt s)) else 0
  let hA : A.PosSemidef :=
    theorem7_hhat_prefix_posSemidef S run rankBound (finalIndex T)
  let U : unitary (GenericSquare (FlatMatrixIndex m n)) := hA.1.eigenvectorUnitary
  let lam : FlatMatrixIndex m n → ℝ := hA.1.eigenvalues
  have hdiagA :
      A = (U : GenericSquare (FlatMatrixIndex m n)) *
          Matrix.diagonal (fun i : FlatMatrixIndex m n => lam i) *
          star (U : GenericSquare (FlatMatrixIndex m n)) := by
    simpa [A, U, lam, hA, Unitary.conjStarAlgAut_apply, Function.comp_def] using
      hA.1.spectral_theorem
  have hbase_delta :
      theorem7_hhat_delta_prefix_base S run rankBound delta (finalIndex T) =
        A + delta • (1 : GenericSquare (FlatMatrixIndex m n)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [A, theorem7_hhat_prefix_base, theorem7_hhat_delta_prefix_base,
        theorem7_hhat_prefix_gram_sum, Matrix.one_apply]
      ring
    · simp [A, theorem7_hhat_prefix_base, theorem7_hhat_delta_prefix_base,
        theorem7_hhat_prefix_gram_sum, Matrix.one_apply, hij]
  have hdiag_delta :
      theorem7_hhat_delta_prefix_base S run rankBound delta (finalIndex T) =
        (U : GenericSquare (FlatMatrixIndex m n)) *
          Matrix.diagonal (fun i : FlatMatrixIndex m n => lam i + delta) *
          star (U : GenericSquare (FlatMatrixIndex m n)) := by
    let I : GenericSquare (FlatMatrixIndex m n) := 1
    let D : GenericSquare (FlatMatrixIndex m n) := Matrix.diagonal lam
    let Dδ : GenericSquare (FlatMatrixIndex m n) :=
      Matrix.diagonal (fun i : FlatMatrixIndex m n => lam i + delta)
    have hDδ : Dδ = D + delta • I := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Dδ, D, I, Matrix.one_apply]
      · simp [Dδ, D, I, Matrix.one_apply, hij]
    have hconj_I :
        (U : GenericSquare (FlatMatrixIndex m n)) * I *
            star (U : GenericSquare (FlatMatrixIndex m n)) = I := by
      simp [I, Matrix.mul_assoc, Unitary.coe_mul_star_self]
    calc
      theorem7_hhat_delta_prefix_base S run rankBound delta (finalIndex T) =
          A + delta • I := by simpa [I] using hbase_delta
      _ =
          (U : GenericSquare (FlatMatrixIndex m n)) * D *
              star (U : GenericSquare (FlatMatrixIndex m n)) +
            delta • I := by
            rw [hdiagA]
      _ =
          (U : GenericSquare (FlatMatrixIndex m n)) * D *
              star (U : GenericSquare (FlatMatrixIndex m n)) +
            delta • ((U : GenericSquare (FlatMatrixIndex m n)) * I *
              star (U : GenericSquare (FlatMatrixIndex m n))) := by
            rw [hconj_I]
      _ =
          (U : GenericSquare (FlatMatrixIndex m n)) * (D + delta • I) *
              star (U : GenericSquare (FlatMatrixIndex m n)) := by
            simp [smul_mul_assoc, Matrix.mul_assoc, mul_add, add_mul]
      _ =
          (U : GenericSquare (FlatMatrixIndex m n)) * Dδ *
              star (U : GenericSquare (FlatMatrixIndex m n)) := by
            rw [hDδ]
  have hshift_nonneg : ∀ i : FlatMatrixIndex m n, 0 ≤ lam i + delta := by
    intro i
    exact add_nonneg (hA.eigenvalues_nonneg i) (le_of_lt hdelta)
  have hpow :
      theorem7_hhat_delta_prefix_pd S run rankBound delta hdelta (finalIndex T) =
        (U : GenericSquare (FlatMatrixIndex m n)) *
          Matrix.diagonal
            (fun i : FlatMatrixIndex m n => (lam i + delta) ^ (1 / 2 : ℝ)) *
          star (U : GenericSquare (FlatMatrixIndex m n)) := by
    simpa [theorem7_hhat_delta_prefix_pd, theorem7_hhat_delta_prefix] using
      psdMatrixPower_eq_of_unitary_diagonalization
        (theorem7_hhat_delta_prefix_base S run rankBound delta (finalIndex T))
        (1 / 2 : ℝ)
        (theorem7_hhat_delta_prefix_base_posDef
          S run rankBound hdelta (finalIndex T)).posSemidef
        U (fun i : FlatMatrixIndex m n => lam i + delta) hdiag_delta hshift_nonneg
  calc
    theorem7_hhat_delta_trace_value_total S run rankBound delta =
        genericTrace
          (theorem7_hhat_delta_prefix_pd S run rankBound delta hdelta (finalIndex T)) := by
          rw [theorem7_hhat_delta_trace_value_total, dif_pos hdelta]
    _ = ∑ i : FlatMatrixIndex m n, (lam i + delta) ^ (1 / 2 : ℝ) := by
          unfold genericTrace
          rw [hpow]
          rw [Matrix.trace_mul_cycle]
          simp [Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.trace_diagonal]
    _ =
        ∑ i : FlatMatrixIndex m n,
          ((theorem7_hhat_prefix_posSemidef S run rankBound (finalIndex T)).1.eigenvalues i +
              delta) ^ (1 / 2 : ℝ) := by
          rfl

private theorem theorem7_hhat_delta_trace_value_total_tendsto {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat) :
    Filter.Tendsto
      (fun delta : ℝ =>
        theorem7_hhat_delta_trace_value_total S run rankBound delta)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds
        (genericTrace
          (psdMatrixPower
            ((positiveRankReal rankBound * S.epsilon) •
                (1 : GenericSquare (FlatMatrixIndex m n)) +
              ∑ s : Fin T,
                if s.1 < (finalIndex T).1 then
                  vectorOuter (matrixVec (run.gradientAt s)) else 0)
            (1 / 2 : ℝ)
            (theorem7_hhat_prefix_posSemidef S run rankBound (finalIndex T))))) := by
  classical
  let A : GenericSquare (FlatMatrixIndex m n) :=
    (positiveRankReal rankBound * S.epsilon) •
        (1 : GenericSquare (FlatMatrixIndex m n)) +
      ∑ s : Fin T,
        if s.1 < (finalIndex T).1 then
          vectorOuter (matrixVec (run.gradientAt s)) else 0
  let hA : A.PosSemidef :=
    theorem7_hhat_prefix_posSemidef S run rankBound (finalIndex T)
  let U : unitary (GenericSquare (FlatMatrixIndex m n)) := hA.1.eigenvectorUnitary
  let lam : FlatMatrixIndex m n → ℝ := hA.1.eigenvalues
  have hpow0 :
      psdMatrixPower A (1 / 2 : ℝ) hA =
        (U : GenericSquare (FlatMatrixIndex m n)) *
          Matrix.diagonal
            (fun i : FlatMatrixIndex m n => (lam i) ^ (1 / 2 : ℝ)) *
          star (U : GenericSquare (FlatMatrixIndex m n)) := by
    have hdiagA :
        A = (U : GenericSquare (FlatMatrixIndex m n)) *
            Matrix.diagonal (fun i : FlatMatrixIndex m n => lam i) *
            star (U : GenericSquare (FlatMatrixIndex m n)) := by
      simpa [A, U, lam, hA, Unitary.conjStarAlgAut_apply, Function.comp_def] using
        hA.1.spectral_theorem
    exact
      psdMatrixPower_eq_of_unitary_diagonalization A (1 / 2 : ℝ) hA U lam hdiagA
        (fun i => hA.eigenvalues_nonneg i)
  have htrace0 :
      genericTrace (psdMatrixPower A (1 / 2 : ℝ) hA) =
        ∑ i : FlatMatrixIndex m n, (lam i) ^ (1 / 2 : ℝ) := by
    unfold genericTrace
    rw [hpow0]
    rw [Matrix.trace_mul_cycle]
    simp [Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.trace_diagonal]
  have hsum :
      Filter.Tendsto
        (fun delta : ℝ =>
          ∑ i : FlatMatrixIndex m n, (lam i + delta) ^ (1 / 2 : ℝ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (∑ i : FlatMatrixIndex m n, (lam i) ^ (1 / 2 : ℝ))) := by
    simpa using
      (tendsto_finset_sum (s := (Finset.univ : Finset (FlatMatrixIndex m n)))
        (f := fun i delta => (lam i + delta) ^ (1 / 2 : ℝ))
        (a := fun i => (lam i) ^ (1 / 2 : ℝ))
        (x := nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (fun i _ => by
          have hlin :
              Filter.Tendsto (fun delta : ℝ => lam i + delta)
                (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (lam i + 0)) := by
            exact (tendsto_const_nhds.add
              (tendsto_nhdsWithin_of_tendsto_nhds (f := id) Filter.tendsto_id))
          have hrpow :=
            hlin.rpow_const (p := (1 / 2 : ℝ)) (Or.inr (by norm_num))
          simpa using hrpow))
  have heq_eventual :
      (fun delta : ℝ =>
        theorem7_hhat_delta_trace_value_total S run rankBound delta) =ᶠ[
          nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        (fun delta : ℝ =>
          ∑ i : FlatMatrixIndex m n, (lam i + delta) ^ (1 / 2 : ℝ)) := by
    filter_upwards
      [show Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) by
        exact self_mem_nhdsWithin]
      with delta hdelta
    simpa [lam, hA, A] using
      theorem7_hhat_delta_trace_value_total_spectral S run rankBound hdelta
  have htarget :
      Filter.Tendsto
        (fun delta : ℝ =>
          theorem7_hhat_delta_trace_value_total S run rankBound delta)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (∑ i : FlatMatrixIndex m n, (lam i) ^ (1 / 2 : ℝ))) :=
    hsum.congr' heq_eventual.symm
  have htrace0_target :
      genericTrace
        (psdMatrixPower
          ((positiveRankReal rankBound * S.epsilon) •
              (1 : GenericSquare (FlatMatrixIndex m n)) +
            ∑ s : Fin T,
              if s.1 < (finalIndex T).1 then
                vectorOuter (matrixVec (run.gradientAt s)) else 0)
          (1 / 2 : ℝ)
          (theorem7_hhat_prefix_posSemidef S run rankBound (finalIndex T))) =
        ∑ i : FlatMatrixIndex m n, (lam i) ^ (1 / 2 : ℝ) := by
    simpa [A, hA] using htrace0
  rw [htrace0_target]
  exact htarget

private theorem quadraticForm_unitary_diagonal_star_spectral_sum {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (U : unitary (GenericSquare ι)) (d : ι → ℝ) :
    quadraticForm x
        ((U : GenericSquare ι) * Matrix.diagonal d *
          star (U : GenericSquare ι)) =
      ∑ k : ι, (∑ i : ι, x i * (U : GenericSquare ι) i k) ^ 2 * d k := by
  simpa only [quadraticForm_eq_toBilin] using
    Matrix.toBilin_mul_diagonal_mul_transpose_self_eq_sum_sq_mul
      x d (U : GenericSquare ι)

private theorem vectorDot_unitary_spectral_coords {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (x y : ι → ℝ) (U : unitary (GenericSquare ι)) :
    vectorDot x y =
      ∑ k : ι,
        (∑ i : ι, x i * (U : GenericSquare ι) i k) *
          (∑ j : ι, y j * (U : GenericSquare ι) j k) := by
  classical
  simpa only [vectorDot, mul_comm] using
    (finite_orthonormal_coordinate_bilinear_collapse
      (fun i k => (U : GenericSquare ι) i k) x y (fun i j => by
        have hunit := congrArg (fun M : GenericSquare ι => M i j)
          (Unitary.coe_mul_star_self U)
        simpa [Matrix.mul_apply, Matrix.one_apply] using hunit)).symm

private theorem quadraticForm_smul_matrix {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (c : ℝ) (H : GenericSquare ι) :
    quadraticForm x (c • H) = c * quadraticForm x H := by
  classical
  unfold quadraticForm
  simp [Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm]

private theorem spectral_support_weighted_cauchy {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (lam coeff z : ι → ℝ)
    (hlam_nonneg : ∀ i : ι, 0 ≤ lam i)
    (hcoeff_zero : ∀ i : ι, lam i = 0 → coeff i = 0) :
    (∑ i : ι, coeff i * z i) ^ 2 ≤
      (∑ i : ι, coeff i ^ 2 * (lam i) ^ (-(1 / 2 : ℝ))) *
        (∑ i : ι, z i ^ 2 * (lam i) ^ (1 / 2 : ℝ)) := by
  exact Finset.sum_mul_sq_le_inverse_sqrt_weight_mul_sqrt_weight lam coeff z hlam_nonneg hcoeff_zero

private theorem nonneg_le_of_sq_le_mul_self {x C : ℝ}
    (hx : 0 ≤ x) (hC : 0 ≤ C) (h : x ^ 2 ≤ C * x) : x ≤ C := by
  by_cases hxzero : x = 0
  · subst hxzero
    exact hC
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
    have hmul := mul_le_mul_of_nonneg_right h (le_of_lt (inv_pos.mpr hxpos))
    have hleft : x ^ 2 * x⁻¹ = x := by
      field_simp [hxzero]
    have hright : C * x * x⁻¹ = C := by
      field_simp [hxzero]
    simpa [hleft, hright, mul_assoc] using hmul

private theorem spectral_coeff_zero_of_vectorOuter_le_psd_zero_eigen {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (g : ι → ℝ) (A : GenericSquare ι) (hA : A.PosSemidef)
    (hOuter : vectorOuter g ≤ A) (i : ι)
    (hi : hA.1.eigenvalues i = 0) :
    (∑ j : ι, g j * (hA.1.eigenvectorUnitary : GenericSquare ι) j i) = 0 := by
  apply Matrix.spectral_coeff_eq_zero_of_vecMulVec_le_of_eigenvalue_eq_zero
    (g := g) (A := A) (hA := hA.1) (i := i) (hi := hi)
  simpa [vectorOuter, Matrix.vecMulVec] using hOuter

private theorem spectral_support_inverse_sqrt_tendsto {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (lam coeff : ι → ℝ)
    (hlam_nonneg : ∀ i : ι, 0 ≤ lam i)
    (hcoeff_zero : ∀ i : ι, lam i = 0 → coeff i = 0) :
    Filter.Tendsto
      (fun delta : ℝ =>
        ∑ i : ι, coeff i ^ 2 * (lam i + delta) ^ (-(1 / 2 : ℝ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∑ i : ι, coeff i ^ 2 * (lam i) ^ (-(1 / 2 : ℝ)))) := by
  exact tendsto_sum_sq_mul_add_rpow_neg_half_of_support
    lam coeff hlam_nonneg hcoeff_zero

private theorem theorem7_hhat_delta_dual_value_total_spectral_support {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat) (t : Fin T) :
    ∃ coeff : FlatMatrixIndex m n → ℝ,
      (∀ {delta : ℝ} (hdelta : 0 < delta),
        theorem7_hhat_delta_dual_value_total S run rankBound delta t =
          ∑ i : FlatMatrixIndex m n,
            coeff i ^ 2 *
              (((theorem7_hhat_prefix_posSemidef S run rankBound
                    (nextIndex t)).1.eigenvalues i + delta) ^
                (-(1 / 2 : ℝ)))) ∧
      (∀ i : FlatMatrixIndex m n,
        (theorem7_hhat_prefix_posSemidef S run rankBound
          (nextIndex t)).1.eigenvalues i = 0 →
          coeff i = 0) ∧
      (∀ i : FlatMatrixIndex m n,
        coeff i =
          ∑ j : FlatMatrixIndex m n, matrixVec (run.gradientAt t) j *
            ((theorem7_hhat_prefix_posSemidef S run rankBound
              (nextIndex t)).1.eigenvectorUnitary :
                GenericSquare (FlatMatrixIndex m n)) j i) := by
  classical
  let A : GenericSquare (FlatMatrixIndex m n) :=
    theorem7_hhat_prefix_base S run rankBound (nextIndex t)
  let hA : A.PosSemidef := by
    simpa [A, theorem7_hhat_prefix_base] using
      theorem7_hhat_prefix_posSemidef S run rankBound (nextIndex t)
  let U : unitary (GenericSquare (FlatMatrixIndex m n)) := hA.1.eigenvectorUnitary
  let lam : FlatMatrixIndex m n → ℝ := hA.1.eigenvalues
  let coeff : FlatMatrixIndex m n → ℝ := fun i =>
    ∑ j : FlatMatrixIndex m n, matrixVec (run.gradientAt t) j *
      (U : GenericSquare (FlatMatrixIndex m n)) j i
  have houter (v : FlatMatrixIndex m n → ℝ) :
      vectorOuter v = Matrix.vecMulVec v v := rfl
  refine ⟨coeff, ?_, ?_, ?_⟩
  · intro delta hdelta
    let Aδ : GenericSquare (FlatMatrixIndex m n) :=
      theorem7_hhat_delta_prefix_base S run rankBound delta (nextIndex t)
    have hAδpd :
        Aδ.PosDef :=
      theorem7_hhat_delta_prefix_base_posDef S run rankBound hdelta (nextIndex t)
    have hbase_delta :
        Aδ = A + delta • (1 : GenericSquare (FlatMatrixIndex m n)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Aδ, A, theorem7_hhat_prefix_base, theorem7_hhat_delta_prefix_base,
          theorem7_hhat_prefix_gram_sum, houter, Matrix.vecMulVec,
          Matrix.one_apply]
        ring
      · simp [Aδ, A, theorem7_hhat_prefix_base, theorem7_hhat_delta_prefix_base,
          theorem7_hhat_prefix_gram_sum, houter, Matrix.vecMulVec,
          Matrix.one_apply, hij]
    have hdiagA :
        A = (U : GenericSquare (FlatMatrixIndex m n)) *
            Matrix.diagonal (fun i : FlatMatrixIndex m n => lam i) *
            star (U : GenericSquare (FlatMatrixIndex m n)) := by
      simpa [A, U, lam, hA, Unitary.conjStarAlgAut_apply, Function.comp_def] using
        hA.1.spectral_theorem
    have hdiag_delta :
        Aδ =
          (U : GenericSquare (FlatMatrixIndex m n)) *
            Matrix.diagonal (fun i : FlatMatrixIndex m n => lam i + delta) *
            star (U : GenericSquare (FlatMatrixIndex m n)) := by
      let I : GenericSquare (FlatMatrixIndex m n) := 1
      let D : GenericSquare (FlatMatrixIndex m n) := Matrix.diagonal lam
      let Dδ : GenericSquare (FlatMatrixIndex m n) :=
        Matrix.diagonal (fun i : FlatMatrixIndex m n => lam i + delta)
      have hDδ : Dδ = D + delta • I := by
        ext i j
        by_cases hij : i = j
        · subst j
          simp [Dδ, D, I, Matrix.one_apply]
        · simp [Dδ, D, I, Matrix.one_apply, hij]
      have hconj_I :
          (U : GenericSquare (FlatMatrixIndex m n)) * I *
              star (U : GenericSquare (FlatMatrixIndex m n)) = I := by
        simp [I, Matrix.mul_assoc, Unitary.coe_mul_star_self]
      calc
        Aδ = A + delta • I := by simpa [I] using hbase_delta
        _ =
            (U : GenericSquare (FlatMatrixIndex m n)) * D *
                star (U : GenericSquare (FlatMatrixIndex m n)) +
              delta • I := by
              rw [hdiagA]
        _ =
            (U : GenericSquare (FlatMatrixIndex m n)) * D *
                star (U : GenericSquare (FlatMatrixIndex m n)) +
              delta • ((U : GenericSquare (FlatMatrixIndex m n)) * I *
                star (U : GenericSquare (FlatMatrixIndex m n))) := by
              rw [hconj_I]
        _ =
            (U : GenericSquare (FlatMatrixIndex m n)) * (D + delta • I) *
                star (U : GenericSquare (FlatMatrixIndex m n)) := by
              simp [smul_mul_assoc, Matrix.mul_assoc, mul_add, add_mul]
        _ =
            (U : GenericSquare (FlatMatrixIndex m n)) * Dδ *
                star (U : GenericSquare (FlatMatrixIndex m n)) := by
              rw [hDδ]
    have hshift_nonneg : ∀ i : FlatMatrixIndex m n, 0 ≤ lam i + delta := by
      intro i
      exact add_nonneg (hA.eigenvalues_nonneg i) (le_of_lt hdelta)
    have hinv :
        (theorem7_hhat_delta_prefix_pd S run rankBound delta hdelta
          (nextIndex t))⁻¹ =
          (U : GenericSquare (FlatMatrixIndex m n)) *
            Matrix.diagonal
              (fun i : FlatMatrixIndex m n => (lam i + delta) ^ (-(1 / 2 : ℝ))) *
            star (U : GenericSquare (FlatMatrixIndex m n)) := by
      have hneg :
          psdMatrixPower Aδ (-(1 / 2 : ℝ)) hAδpd.posSemidef =
            (U : GenericSquare (FlatMatrixIndex m n)) *
              Matrix.diagonal
                (fun i : FlatMatrixIndex m n => (lam i + delta) ^ (-(1 / 2 : ℝ))) *
              star (U : GenericSquare (FlatMatrixIndex m n)) := by
        exact
          psdMatrixPower_eq_of_unitary_diagonalization Aδ (-(1 / 2 : ℝ))
            hAδpd.posSemidef U (fun i : FlatMatrixIndex m n => lam i + delta)
            hdiag_delta hshift_nonneg
      calc
        (theorem7_hhat_delta_prefix_pd S run rankBound delta hdelta
            (nextIndex t))⁻¹ =
            (psdMatrixPower Aδ (1 / 2 : ℝ) hAδpd.posSemidef)⁻¹ := by
              rfl
        _ = psdMatrixPower Aδ (-(1 / 2 : ℝ)) hAδpd.posSemidef := by
              exact (psdMatrixPower_neg_half_eq_inv_psdMatrixPower_half Aδ hAδpd).symm
        _ =
            (U : GenericSquare (FlatMatrixIndex m n)) *
              Matrix.diagonal
                (fun i : FlatMatrixIndex m n => (lam i + delta) ^ (-(1 / 2 : ℝ))) *
              star (U : GenericSquare (FlatMatrixIndex m n)) := hneg
    calc
      theorem7_hhat_delta_dual_value_total S run rankBound delta t =
          dualQuadraticForm (matrixVec (run.gradientAt t))
            (theorem7_hhat_delta_prefix_pd S run rankBound delta hdelta
              (nextIndex t)) := by
          rw [theorem7_hhat_delta_dual_value_total, dif_pos hdelta]
      _ =
          quadraticForm (matrixVec (run.gradientAt t))
            ((U : GenericSquare (FlatMatrixIndex m n)) *
              Matrix.diagonal
                (fun i : FlatMatrixIndex m n => (lam i + delta) ^ (-(1 / 2 : ℝ))) *
              star (U : GenericSquare (FlatMatrixIndex m n))) := by
          simp [dualQuadraticForm, quadraticForm, hinv]
      _ =
          ∑ i : FlatMatrixIndex m n,
            coeff i ^ 2 * (lam i + delta) ^ (-(1 / 2 : ℝ)) := by
          simpa [coeff] using
            quadraticForm_unitary_diagonal_star_spectral_sum
              (matrixVec (run.gradientAt t)) U
              (fun i : FlatMatrixIndex m n => (lam i + delta) ^ (-(1 / 2 : ℝ)))
      _ =
          ∑ i : FlatMatrixIndex m n,
            coeff i ^ 2 *
              (((theorem7_hhat_prefix_posSemidef S run rankBound
                    (nextIndex t)).1.eigenvalues i + delta) ^
                (-(1 / 2 : ℝ))) := by
          rfl
  · -- Remaining support fact: the current outer-product summand is part of
    -- the PSD prefix at `nextIndex t`; a zero eigenvalue of that prefix forces
    -- the corresponding spectral coordinate of the current gradient to vanish.
    have hOuter :
        vectorOuter (matrixVec (run.gradientAt t)) ≤ A := by
      let Rest : GenericSquare (FlatMatrixIndex m n) :=
        (positiveRankReal rankBound * S.epsilon) •
            (1 : GenericSquare (FlatMatrixIndex m n)) +
          ∑ s : Fin T,
            if s.1 < t.1 then vectorOuter (matrixVec (run.gradientAt s)) else 0
      have hcoeff_nonneg : 0 ≤ positiveRankReal rankBound * S.epsilon :=
        mul_nonneg (le_of_lt (positiveRankReal_pos rankBound)) S.epsilon_nonneg
      have hscalar :
          ((positiveRankReal rankBound * S.epsilon) •
              (1 : GenericSquare (FlatMatrixIndex m n))).PosSemidef :=
        Matrix.PosSemidef.one.smul hcoeff_nonneg
      have hprefix :
          (∑ s : Fin T,
            if s.1 < t.1 then vectorOuter (matrixVec (run.gradientAt s)) else 0 :
              GenericSquare (FlatMatrixIndex m n)).PosSemidef := by
        refine finset_sum_generic_posSemidef_of_forall Finset.univ
          (fun s : Fin T =>
            if s.1 < t.1 then vectorOuter (matrixVec (run.gradientAt s)) else 0) ?_
        intro s _hs
        by_cases hsN : s.1 < t.1
        · simpa [hsN] using
            vectorOuter_posSemidef (ι := FlatMatrixIndex m n)
              (matrixVec (run.gradientAt s))
        · simpa [hsN] using
            (Matrix.PosSemidef.zero :
              (0 : GenericSquare (FlatMatrixIndex m n)).PosSemidef)
      have hRest : Rest.PosSemidef := by
        simpa [Rest] using hscalar.add hprefix
      have hsum :=
        fin_prefix_sum_succ_addCommMonoid
          (fun s : Fin T => vectorOuter (matrixVec (run.gradientAt s))) t.2
      have hA_decomp : A = vectorOuter (matrixVec (run.gradientAt t)) + Rest := by
        calc
          A =
              (positiveRankReal rankBound * S.epsilon) •
                  (1 : GenericSquare (FlatMatrixIndex m n)) +
                ∑ s : Fin T,
                  if s.1 < t.1 + 1 then
                    vectorOuter (matrixVec (run.gradientAt s)) else 0 := by
                simp [A, theorem7_hhat_prefix_base, houter, Matrix.vecMulVec,
                  nextIndex]
          _ =
              (positiveRankReal rankBound * S.epsilon) •
                  (1 : GenericSquare (FlatMatrixIndex m n)) +
                ((∑ s : Fin T,
                  if s.1 < t.1 then
                    vectorOuter (matrixVec (run.gradientAt s)) else 0) +
                  vectorOuter (matrixVec (run.gradientAt t))) := by
                rw [hsum]
          _ = vectorOuter (matrixVec (run.gradientAt t)) + Rest := by
                simp [Rest]
                abel
      have hdiff : (A - vectorOuter (matrixVec (run.gradientAt t))).PosSemidef := by
        rw [hA_decomp]
        simpa [add_comm, add_left_comm, add_assoc] using hRest
      exact Matrix.le_iff.mpr hdiff
    intro i hi
    simpa [coeff, hA, A] using
      spectral_coeff_zero_of_vectorOuter_le_psd_zero_eigen
        (matrixVec (run.gradientAt t)) A hA hOuter i (by simpa [hA, A] using hi)
  · intro i
    rfl

private theorem spectral_support_inverse_sqrt_order_dual_bound {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (A B : GenericSquare ι) (hA : A.PosSemidef) (hB : B.PosDef)
    (alpha : ℝ) (halpha_nonneg : 0 ≤ alpha) (g coeff : ι → ℝ)
    (hroot_le : psdMatrixPower A (1 / 2 : ℝ) hA ≤ alpha • B)
    (hcoeff_def : ∀ i : ι,
      coeff i = ∑ j : ι, g j * (hA.1.eigenvectorUnitary : GenericSquare ι) j i)
    (hcoeff_zero : ∀ i : ι, hA.1.eigenvalues i = 0 → coeff i = 0) :
    dualQuadraticForm g B ≤
      alpha *
        ∑ i : ι, coeff i ^ 2 * (hA.1.eigenvalues i) ^ (-(1 / 2 : ℝ)) := by
  simpa only [dualQuadraticForm] using
    (Matrix.dualQuadraticForm_le_mul_spectralSupport_of_cfc_sqrt_le
      A B hA hB alpha halpha_nonneg g coeff
      (by simpa only [← psdMatrixPower_eq_cfc A (1 / 2 : ℝ) hA] using hroot_le)
      hcoeff_def hcoeff_zero)


private theorem generic_hhat_delta_trace_spectral {T : Nat}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Fin T → ι → ℝ) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    {delta : ℝ} (hdelta : 0 < delta) :
    genericTrace
      (psdMatrixPower
        ((epsilon + delta) • (1 : GenericSquare ι) +
          ∑ s : Fin T,
            if s.1 < (finalIndex T).1 then vectorOuter (g s) else 0)
        (1 / 2 : ℝ)
        (generic_regularized_prefix_base_posDef
          g (by linarith : 0 < epsilon + delta) (finalIndex T)).posSemidef) =
      ∑ i : ι,
        ((generic_hhat_prefix_posSemidef g heps (finalIndex T)).1.eigenvalues i +
          delta) ^ (1 / 2 : ℝ) := by
  simpa only [genericTrace, psdMatrixPower_eq_cfc, add_smul, add_assoc,
    add_left_comm, add_comm] using
    (Matrix.trace_cfc_sqrt_add_smul_one_eq_sum_sqrt_eigenvalues_add
      (epsilon • (1 : GenericSquare ι) +
        ∑ s : Fin T,
          if s.1 < (finalIndex T).1 then vectorOuter (g s) else 0)
      delta (generic_hhat_prefix_posSemidef g heps (finalIndex T)).1)

private theorem generic_hhat_delta_trace_tendsto {T : Nat}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Fin T → ι → ℝ) {epsilon : ℝ} (heps : 0 ≤ epsilon) :
    Filter.Tendsto
      (fun delta : ℝ =>
        if hdelta : 0 < delta then
          genericTrace
            (psdMatrixPower
              ((epsilon + delta) • (1 : GenericSquare ι) +
                ∑ s : Fin T,
                  if s.1 < (finalIndex T).1 then vectorOuter (g s) else 0)
              (1 / 2 : ℝ)
              (generic_regularized_prefix_base_posDef
                g (add_pos_of_nonneg_of_pos heps hdelta) (finalIndex T)).posSemidef)
        else
          0)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds
        (genericTrace
          (psdMatrixPower
            (epsilon • (1 : GenericSquare ι) +
              ∑ s : Fin T,
                if s.1 < (finalIndex T).1 then vectorOuter (g s) else 0)
            (1 / 2 : ℝ)
            (generic_hhat_prefix_posSemidef g heps (finalIndex T))))) := by
  simpa only [genericTrace, psdMatrixPower_eq_cfc, add_smul, add_assoc,
    add_left_comm, add_comm] using
    (Matrix.tendsto_trace_cfc_sqrt_add_smul_one_nhdsWithin_zero
      (epsilon • (1 : GenericSquare ι) +
        ∑ s : Fin T,
          if s.1 < (finalIndex T).1 then vectorOuter (g s) else 0)
      (generic_hhat_prefix_posSemidef g heps (finalIndex T)).1)

private theorem generic_hhat_delta_dual_value_spectral_support {T : Nat}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Fin T → ι → ℝ) {epsilon : ℝ} (heps : 0 ≤ epsilon) (t : Fin T) :
    ∃ coeff : ι → ℝ,
      (∀ {delta : ℝ} (hdelta : 0 < delta),
        dualQuadraticForm (g t)
          (psdMatrixPower
            ((epsilon + delta) • (1 : GenericSquare ι) +
              ∑ s : Fin T,
                if s.1 < (nextIndex t).1 then vectorOuter (g s) else 0)
            (1 / 2 : ℝ)
            (generic_regularized_prefix_base_posDef
              g (by linarith : 0 < epsilon + delta) (nextIndex t)).posSemidef) =
          ∑ i : ι,
            coeff i ^ 2 *
              (((generic_hhat_prefix_posSemidef g heps (nextIndex t)).1.eigenvalues i +
                  delta) ^ (-(1 / 2 : ℝ)))) ∧
      (∀ i : ι,
        (generic_hhat_prefix_posSemidef g heps (nextIndex t)).1.eigenvalues i = 0 →
          coeff i = 0) ∧
      (∀ i : ι,
        coeff i =
          ∑ j : ι, g t j *
            ((generic_hhat_prefix_posSemidef g heps
              (nextIndex t)).1.eigenvectorUnitary : GenericSquare ι) j i) := by
  classical
  let A : GenericSquare ι :=
    epsilon • (1 : GenericSquare ι) +
      ∑ s : Fin T, if s.1 < (nextIndex t).1 then vectorOuter (g s) else 0
  let hA : A.PosSemidef := by
    simpa [A] using generic_hhat_prefix_posSemidef g heps (nextIndex t)
  let U : unitary (GenericSquare ι) := hA.1.eigenvectorUnitary
  let lam : ι → ℝ := hA.1.eigenvalues
  let coeff : ι → ℝ := fun i =>
    ∑ j : ι, g t j * (U : GenericSquare ι) j i
  refine ⟨coeff, ?_, ?_, ?_⟩
  · intro delta hdelta
    let Aδ : GenericSquare ι :=
      (epsilon + delta) • (1 : GenericSquare ι) +
        ∑ s : Fin T, if s.1 < (nextIndex t).1 then vectorOuter (g s) else 0
    have hAδpd : Aδ.PosDef := by
      simpa [Aδ] using
        generic_regularized_prefix_base_posDef
          g (by linarith : 0 < epsilon + delta) (nextIndex t)
    have hbase_delta : Aδ = A + delta • (1 : GenericSquare ι) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Aδ, A, Matrix.one_apply]
        ring
      · simp [Aδ, A, Matrix.one_apply, hij]
    have hdiagA :
        A = (U : GenericSquare ι) *
            Matrix.diagonal (fun i : ι => lam i) *
            star (U : GenericSquare ι) := by
      simpa [A, U, lam, hA, Unitary.conjStarAlgAut_apply, Function.comp_def] using
        hA.1.spectral_theorem
    have hdiag_delta :
        Aδ =
          (U : GenericSquare ι) *
            Matrix.diagonal (fun i : ι => lam i + delta) *
            star (U : GenericSquare ι) := by
      let I : GenericSquare ι := 1
      let D : GenericSquare ι := Matrix.diagonal lam
      let Dδ : GenericSquare ι := Matrix.diagonal (fun i : ι => lam i + delta)
      have hDδ : Dδ = D + delta • I := by
        ext i j
        by_cases hij : i = j
        · subst j
          simp [Dδ, D, I, Matrix.one_apply]
        · simp [Dδ, D, I, Matrix.one_apply, hij]
      have hconj_I :
          (U : GenericSquare ι) * I * star (U : GenericSquare ι) = I := by
        simp [I, Matrix.mul_assoc, Unitary.coe_mul_star_self]
      calc
        Aδ = A + delta • I := by simpa [I] using hbase_delta
        _ =
            (U : GenericSquare ι) * D * star (U : GenericSquare ι) +
              delta • I := by
              rw [hdiagA]
        _ =
            (U : GenericSquare ι) * D * star (U : GenericSquare ι) +
              delta • ((U : GenericSquare ι) * I * star (U : GenericSquare ι)) := by
              rw [hconj_I]
        _ =
            (U : GenericSquare ι) * (D + delta • I) *
              star (U : GenericSquare ι) := by
              simp [smul_mul_assoc, Matrix.mul_assoc, mul_add, add_mul]
        _ =
            (U : GenericSquare ι) * Dδ * star (U : GenericSquare ι) := by
              rw [hDδ]
    have hshift_nonneg : ∀ i : ι, 0 ≤ lam i + delta := by
      intro i
      exact add_nonneg (hA.eigenvalues_nonneg i) (le_of_lt hdelta)
    have hinv :
        (psdMatrixPower Aδ (1 / 2 : ℝ) hAδpd.posSemidef)⁻¹ =
          (U : GenericSquare ι) *
            Matrix.diagonal (fun i : ι => (lam i + delta) ^ (-(1 / 2 : ℝ))) *
            star (U : GenericSquare ι) := by
      have hneg :
          psdMatrixPower Aδ (-(1 / 2 : ℝ)) hAδpd.posSemidef =
            (U : GenericSquare ι) *
              Matrix.diagonal (fun i : ι => (lam i + delta) ^ (-(1 / 2 : ℝ))) *
              star (U : GenericSquare ι) := by
        exact
          psdMatrixPower_eq_of_unitary_diagonalization Aδ (-(1 / 2 : ℝ))
            hAδpd.posSemidef U (fun i : ι => lam i + delta)
            hdiag_delta hshift_nonneg
      calc
        (psdMatrixPower Aδ (1 / 2 : ℝ) hAδpd.posSemidef)⁻¹ =
            psdMatrixPower Aδ (-(1 / 2 : ℝ)) hAδpd.posSemidef := by
              exact (psdMatrixPower_neg_half_eq_inv_psdMatrixPower_half Aδ hAδpd).symm
        _ =
            (U : GenericSquare ι) *
              Matrix.diagonal (fun i : ι => (lam i + delta) ^ (-(1 / 2 : ℝ))) *
              star (U : GenericSquare ι) := hneg
    have hinv_expr :
        (psdMatrixPower
            ((epsilon + delta) • (1 : GenericSquare ι) +
              ∑ s : Fin T,
                if s.1 < (nextIndex t).1 then vectorOuter (g s) else 0)
            (1 / 2 : ℝ)
            (generic_regularized_prefix_base_posDef
              g (by linarith : 0 < epsilon + delta) (nextIndex t)).posSemidef)⁻¹ =
          (U : GenericSquare ι) *
            Matrix.diagonal (fun i : ι => (lam i + delta) ^ (-(1 / 2 : ℝ))) *
            star (U : GenericSquare ι) := by
      have hpow :
          psdMatrixPower
              ((epsilon + delta) • (1 : GenericSquare ι) +
                ∑ s : Fin T,
                  if s.1 < (nextIndex t).1 then vectorOuter (g s) else 0)
              (1 / 2 : ℝ)
              (generic_regularized_prefix_base_posDef
                g (by linarith : 0 < epsilon + delta) (nextIndex t)).posSemidef =
            psdMatrixPower Aδ (1 / 2 : ℝ) hAδpd.posSemidef := by
        exact psdMatrixPower_congr (by rfl) (1 / 2 : ℝ) _ _
      rw [hpow]
      exact hinv
    calc
      dualQuadraticForm (g t)
          (psdMatrixPower
            ((epsilon + delta) • (1 : GenericSquare ι) +
              ∑ s : Fin T,
                if s.1 < (nextIndex t).1 then vectorOuter (g s) else 0)
            (1 / 2 : ℝ)
            (generic_regularized_prefix_base_posDef
              g (by linarith : 0 < epsilon + delta) (nextIndex t)).posSemidef) =
          quadraticForm (g t)
            ((U : GenericSquare ι) *
              Matrix.diagonal (fun i : ι => (lam i + delta) ^ (-(1 / 2 : ℝ))) *
              star (U : GenericSquare ι)) := by
          rw [dualQuadraticForm]
          exact congrArg (quadraticForm (g t)) hinv_expr
      _ = ∑ i : ι, coeff i ^ 2 * (lam i + delta) ^ (-(1 / 2 : ℝ)) := by
          simpa [coeff] using
            quadraticForm_unitary_diagonal_star_spectral_sum
              (g t) U (fun i : ι => (lam i + delta) ^ (-(1 / 2 : ℝ)))
      _ =
          ∑ i : ι,
            coeff i ^ 2 *
              (((generic_hhat_prefix_posSemidef g heps (nextIndex t)).1.eigenvalues i +
                  delta) ^ (-(1 / 2 : ℝ))) := by
          rfl
  · have hOuter : vectorOuter (g t) ≤ A := by
      simpa [A] using generic_prefix_outer_le_next_hhat_base g heps t
    intro i hi
    simpa [coeff, hA, A] using
      spectral_coeff_zero_of_vectorOuter_le_psd_zero_eigen
        (g t) A hA hOuter i (by simpa [hA, A] using hi)
  · intro i
    rfl

private theorem generic_hhat_positive_delta_dual_support_limits_exist {T : Nat}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Fin T → ι → ℝ) {epsilon : ℝ} (heps : 0 ≤ epsilon) :
    ∃ supportDual : Fin T → ℝ,
      ∀ t : Fin T,
        Filter.Tendsto
          (fun delta : ℝ =>
            if hdelta : 0 < delta then
              dualQuadraticForm (g t)
                (psdMatrixPower
                  ((epsilon + delta) • (1 : GenericSquare ι) +
                    ∑ s : Fin T,
                      if s.1 < (nextIndex t).1 then vectorOuter (g s) else 0)
                  (1 / 2 : ℝ)
                  (generic_regularized_prefix_base_posDef
                    g (add_pos_of_nonneg_of_pos heps hdelta) (nextIndex t)).posSemidef)
            else
              0)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (supportDual t)) := by
  classical
  choose coeff hcoeff_spec hcoeff_zero _hcoeff_def using
    generic_hhat_delta_dual_value_spectral_support g heps
  let supportDual : Fin T → ℝ := fun t =>
    ∑ i : ι,
      (coeff t i) ^ 2 *
        ((generic_hhat_prefix_posSemidef g heps
            (nextIndex t)).1.eigenvalues i) ^ (-(1 / 2 : ℝ))
  refine ⟨supportDual, ?_⟩
  intro t
  let lam : ι → ℝ := fun i =>
    (generic_hhat_prefix_posSemidef g heps (nextIndex t)).1.eigenvalues i
  have hlim :
      Filter.Tendsto
        (fun delta : ℝ =>
          ∑ i : ι, (coeff t i) ^ 2 * (lam i + delta) ^ (-(1 / 2 : ℝ)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds
          (∑ i : ι, (coeff t i) ^ 2 * (lam i) ^ (-(1 / 2 : ℝ)))) := by
    exact
      spectral_support_inverse_sqrt_tendsto lam (coeff t)
        (fun i => by
          simpa [lam] using
            (generic_hhat_prefix_posSemidef g heps (nextIndex t)).eigenvalues_nonneg i)
        (fun i hi => hcoeff_zero t i (by simpa [lam] using hi))
  have heventual :
      (fun delta : ℝ =>
        if hdelta : 0 < delta then
          dualQuadraticForm (g t)
            (psdMatrixPower
              ((epsilon + delta) • (1 : GenericSquare ι) +
                ∑ s : Fin T,
                  if s.1 < (nextIndex t).1 then vectorOuter (g s) else 0)
              (1 / 2 : ℝ)
              (generic_regularized_prefix_base_posDef
                g (add_pos_of_nonneg_of_pos heps hdelta) (nextIndex t)).posSemidef)
        else
          0) =ᶠ[
          nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        (fun delta : ℝ =>
          ∑ i : ι, (coeff t i) ^ 2 * (lam i + delta) ^ (-(1 / 2 : ℝ))) := by
    filter_upwards
      [show Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) by
        exact self_mem_nhdsWithin]
      with delta hdelta
    have hdelta_pos : 0 < delta := hdelta
    rw [dif_pos hdelta_pos]
    simpa [lam, dualQuadraticForm, psdMatrixPower_eq_cfc, add_smul,
      add_assoc, add_left_comm, add_comm] using hcoeff_spec t hdelta_pos
  have htarget :
      supportDual t =
        ∑ i : ι, (coeff t i) ^ 2 * (lam i) ^ (-(1 / 2 : ℝ)) := by
    rfl
  rw [htarget]
  exact hlim.congr' heventual.symm

private theorem generic_hhat_support_bound_of_regularized_limits {T : Nat}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Fin T → ι → ℝ) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (supportDual : Fin T → ℝ)
    (traceLimit : ℝ)
    (hDualLimit : ∀ t : Fin T,
      Filter.Tendsto
        (fun delta : ℝ =>
          if hdelta : 0 < delta then
            dualQuadraticForm (g t)
              (psdMatrixPower
                ((epsilon + delta) • (1 : GenericSquare ι) +
                  ∑ s : Fin T,
                    if s.1 < (nextIndex t).1 then vectorOuter (g s) else 0)
                (1 / 2 : ℝ)
                (generic_regularized_prefix_base_posDef
                  g (add_pos_of_nonneg_of_pos heps hdelta) (nextIndex t)).posSemidef)
          else
            0)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (supportDual t)))
    (hTraceLimit :
      Filter.Tendsto
        (fun delta : ℝ =>
          if hdelta : 0 < delta then
            genericTrace
              (psdMatrixPower
                ((epsilon + delta) • (1 : GenericSquare ι) +
                  ∑ s : Fin T,
                    if s.1 < (finalIndex T).1 then vectorOuter (g s) else 0)
                (1 / 2 : ℝ)
                (generic_regularized_prefix_base_posDef
                  g (add_pos_of_nonneg_of_pos heps hdelta) (finalIndex T)).posSemidef)
          else
            0)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds traceLimit)) :
    (∑ t : Fin T, supportDual t) ≤ 2 * traceLimit := by
  letI : Filter.NeBot (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    simpa using
      (nhdsWithin_Ioi_neBot (a := (0 : ℝ)) (b := 0) (le_refl 0))
  exact Filter.sum_le_mul_of_tendsto_of_eventually
    (s := Finset.univ)
    (l := nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (f := _) (g := _)
    (a := supportDual) (b := 2) (c := traceLimit)
    (fun t _ht ↦ hDualLimit t) hTraceLimit
    (by
      filter_upwards
        [show Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) by
          exact self_mem_nhdsWithin]
        with delta hdelta
      have hdelta_pos : 0 < delta := hdelta
      have hc : 0 < epsilon + delta := add_pos_of_nonneg_of_pos heps hdelta_pos
      calc
        (∑ t : Fin T,
          if hdelta : 0 < delta then
            dualQuadraticForm (g t)
              (psdMatrixPower
                ((epsilon + delta) • (1 : GenericSquare ι) +
                  ∑ s : Fin T,
                    if s.1 < (nextIndex t).1 then vectorOuter (g s) else 0)
                (1 / 2 : ℝ)
                (generic_regularized_prefix_base_posDef
                  g (add_pos_of_nonneg_of_pos heps hdelta) (nextIndex t)).posSemidef)
          else
            0) =
            ∑ t : Fin T,
              dualQuadraticForm (g t)
                (psdMatrixPower
                  ((epsilon + delta) • (1 : GenericSquare ι) +
                    ∑ s : Fin T,
                      if s.1 < (nextIndex t).1 then vectorOuter (g s) else 0)
                  (1 / 2 : ℝ)
                  (generic_regularized_prefix_base_posDef g hc
                    (nextIndex t)).posSemidef) := by
              apply Finset.sum_congr rfl
              intro t _ht
              rw [dif_pos hdelta_pos]
        _ ≤ 2 * genericTrace
              (psdMatrixPower
                ((epsilon + delta) • (1 : GenericSquare ι) +
                  ∑ s : Fin T,
                    if s.1 < (finalIndex T).1 then vectorOuter (g s) else 0)
                (1 / 2 : ℝ)
                (generic_regularized_prefix_base_posDef g hc
                  (finalIndex T)).posSemidef) := by
              simpa using
                generic_regularized_hhat_equation6_bound (T := T) (ι := ι) g hc
        _ = 2 *
              (if hdelta : 0 < delta then
                genericTrace
                  (psdMatrixPower
                    ((epsilon + delta) • (1 : GenericSquare ι) +
                      ∑ s : Fin T,
                        if s.1 < (finalIndex T).1 then vectorOuter (g s) else 0)
                    (1 / 2 : ℝ)
                    (generic_regularized_prefix_base_posDef
                      g (add_pos_of_nonneg_of_pos heps hdelta)
                        (finalIndex T)).posSemidef)
              else
                0) := by
              rw [dif_pos hdelta_pos])

private theorem generic_hhat_positive_delta_range_limit_bound {T : Nat}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Fin T → ι → ℝ) {epsilon : ℝ} (heps : 0 ≤ epsilon) :
    ∃ supportDual : Fin T → ℝ,
      (∀ t : Fin T,
        Filter.Tendsto
          (fun delta : ℝ =>
            if hdelta : 0 < delta then
              dualQuadraticForm (g t)
                (psdMatrixPower
                  ((epsilon + delta) • (1 : GenericSquare ι) +
                    ∑ s : Fin T,
                      if s.1 < (nextIndex t).1 then vectorOuter (g s) else 0)
                  (1 / 2 : ℝ)
                  (generic_regularized_prefix_base_posDef
                    g (add_pos_of_nonneg_of_pos heps hdelta) (nextIndex t)).posSemidef)
            else
              0)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (supportDual t))) ∧
      Filter.Tendsto
        (fun delta : ℝ =>
          if hdelta : 0 < delta then
            genericTrace
              (psdMatrixPower
                ((epsilon + delta) • (1 : GenericSquare ι) +
                  ∑ s : Fin T,
                    if s.1 < (finalIndex T).1 then vectorOuter (g s) else 0)
                (1 / 2 : ℝ)
                (generic_regularized_prefix_base_posDef
                  g (add_pos_of_nonneg_of_pos heps hdelta) (finalIndex T)).posSemidef)
          else
            0)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds
          (genericTrace
            (psdMatrixPower
              (epsilon • (1 : GenericSquare ι) +
                ∑ s : Fin T,
                  if s.1 < (finalIndex T).1 then vectorOuter (g s) else 0)
              (1 / 2 : ℝ)
              (generic_hhat_prefix_posSemidef g heps (finalIndex T))))) ∧
      (∑ t : Fin T, supportDual t) ≤
        2 * genericTrace
          (psdMatrixPower
            (epsilon • (1 : GenericSquare ι) +
              ∑ s : Fin T,
                if s.1 < (finalIndex T).1 then vectorOuter (g s) else 0)
            (1 / 2 : ℝ)
            (generic_hhat_prefix_posSemidef g heps (finalIndex T))) := by
  simpa only [dualQuadraticForm, genericTrace, psdMatrixPower_eq_cfc,
    vectorOuter, Matrix.regularizedPrefixGram, nextIndex, finalIndex] using
    Matrix.sum_dualQuadraticForm_prefixGram_sqrt_le_two_trace g epsilon heps

private theorem generic_algorithm_dual_pointwise_le_hhat_support {T : Nat}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Fin T → ι → ℝ) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (Halg : Fin (T + 1) → GenericSquare ι)
    (alpha : ℝ) (halpha_nonneg : 0 ≤ alpha)
    (hHalg_pd : ∀ t : Fin T, (Halg (nextIndex t)).PosDef)
    (hroot_le : ∀ N : Fin (T + 1),
      psdMatrixPower
          (epsilon • (1 : GenericSquare ι) +
            ∑ s : Fin T,
              if s.1 < N.1 then vectorOuter (g s) else 0)
          (1 / 2 : ℝ) (generic_hhat_prefix_posSemidef g heps N) ≤
        alpha • Halg N)
    (supportDual : Fin T → ℝ)
    (hSupportLimit : ∀ t : Fin T,
      Filter.Tendsto
        (fun delta : ℝ =>
          if hdelta : 0 < delta then
            dualQuadraticForm (g t)
              (psdMatrixPower
                ((epsilon + delta) • (1 : GenericSquare ι) +
                  ∑ s : Fin T,
                    if s.1 < (nextIndex t).1 then vectorOuter (g s) else 0)
                (1 / 2 : ℝ)
                (generic_regularized_prefix_base_posDef
                  g (add_pos_of_nonneg_of_pos heps hdelta) (nextIndex t)).posSemidef)
          else
            0)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (supportDual t)))
    (t : Fin T) :
    dualQuadraticForm (g t) (Halg (nextIndex t)) ≤
      alpha * supportDual t := by
  simpa [dualQuadraticForm, psdMatrixPower_eq_cfc, add_smul, add_assoc,
    add_left_comm, add_comm] using
    (Matrix.dualQuadraticForm_le_mul_of_cfc_sqrt_le_of_regularized_tendsto
      (A := epsilon • (1 : GenericSquare ι) +
        ∑ s : Fin T,
          if s.1 < (nextIndex t).1 then vectorOuter (g s) else 0)
      (B := Halg (nextIndex t)) (g := g t) (alpha := alpha)
      (support := supportDual t)
      (hA := generic_hhat_prefix_posSemidef g heps (nextIndex t))
      (hB := hHalg_pd t)
      (hOuter := by
        simpa [vectorOuter] using
          generic_prefix_outer_le_next_hhat_base g heps t)
      (halpha_nonneg := halpha_nonneg)
      (hroot_le := by
        simpa [psdMatrixPower_eq_cfc] using hroot_le (nextIndex t))
      (hSupportLimit := by
        simpa [dualQuadraticForm, psdMatrixPower_eq_cfc, add_smul, add_assoc,
          add_left_comm, add_comm] using hSupportLimit t))

private theorem generic_algorithm_dual_sum_le_hhat_support_sum {T : Nat}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Fin T → ι → ℝ) {epsilon : ℝ} (heps : 0 ≤ epsilon)
    (Halg : Fin (T + 1) → GenericSquare ι)
    (alpha : ℝ) (halpha_nonneg : 0 ≤ alpha)
    (hHalg_pd : ∀ t : Fin T, (Halg (nextIndex t)).PosDef)
    (hroot_le : ∀ N : Fin (T + 1),
      psdMatrixPower
          (epsilon • (1 : GenericSquare ι) +
            ∑ s : Fin T,
              if s.1 < N.1 then vectorOuter (g s) else 0)
          (1 / 2 : ℝ) (generic_hhat_prefix_posSemidef g heps N) ≤
        alpha • Halg N)
    (supportDual : Fin T → ℝ)
    (hSupportLimit : ∀ t : Fin T,
      Filter.Tendsto
        (fun delta : ℝ =>
          if hdelta : 0 < delta then
            dualQuadraticForm (g t)
              (psdMatrixPower
                ((epsilon + delta) • (1 : GenericSquare ι) +
                  ∑ s : Fin T,
                    if s.1 < (nextIndex t).1 then vectorOuter (g s) else 0)
                (1 / 2 : ℝ)
                (generic_regularized_prefix_base_posDef
                  g (add_pos_of_nonneg_of_pos heps hdelta) (nextIndex t)).posSemidef)
          else
            0)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (supportDual t))) :
    (∑ t : Fin T, dualQuadraticForm (g t) (Halg (nextIndex t))) ≤
      alpha * ∑ t : Fin T, supportDual t := by
  classical
  calc
    (∑ t : Fin T, dualQuadraticForm (g t) (Halg (nextIndex t))) ≤
        ∑ t : Fin T, alpha * supportDual t := by
          exact Finset.sum_le_sum (fun t _ =>
            generic_algorithm_dual_pointwise_le_hhat_support
              g heps Halg alpha halpha_nonneg hHalg_pd hroot_le
              supportDual hSupportLimit t)
    _ = alpha * ∑ t : Fin T, supportDual t := by
          simp [Finset.mul_sum]

private theorem theorem7_hhat_positive_delta_dual_support_limits_exist {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat) :
    ∃ supportDual : Fin T → ℝ,
      ∀ t : Fin T,
        Filter.Tendsto
          (fun delta : ℝ =>
          theorem7_hhat_delta_dual_value_total S run rankBound delta t)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (supportDual t)) := by
  classical
  choose coeff hcoeff_spec hcoeff_zero hcoeff_def using
    theorem7_hhat_delta_dual_value_total_spectral_support S run rankBound
  let supportDual : Fin T → ℝ := fun t =>
    ∑ i : FlatMatrixIndex m n,
      (coeff t i) ^ 2 *
        ((theorem7_hhat_prefix_posSemidef S run rankBound
            (nextIndex t)).1.eigenvalues i) ^ (-(1 / 2 : ℝ))
  refine ⟨supportDual, ?_⟩
  intro t
  let lam : FlatMatrixIndex m n → ℝ := fun i =>
    (theorem7_hhat_prefix_posSemidef S run rankBound
      (nextIndex t)).1.eigenvalues i
  have hlim :
      Filter.Tendsto
        (fun delta : ℝ =>
          ∑ i : FlatMatrixIndex m n,
            (coeff t i) ^ 2 * (lam i + delta) ^ (-(1 / 2 : ℝ)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds
          (∑ i : FlatMatrixIndex m n,
            (coeff t i) ^ 2 * (lam i) ^ (-(1 / 2 : ℝ)))) := by
    exact
      spectral_support_inverse_sqrt_tendsto lam (coeff t)
        (fun i => by
          simpa [lam] using
            (theorem7_hhat_prefix_posSemidef S run rankBound
              (nextIndex t)).eigenvalues_nonneg i)
        (fun i hi => hcoeff_zero t i (by simpa [lam] using hi))
  have heventual :
      (fun delta : ℝ =>
        theorem7_hhat_delta_dual_value_total S run rankBound delta t) =ᶠ[
          nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        (fun delta : ℝ =>
          ∑ i : FlatMatrixIndex m n,
            (coeff t i) ^ 2 * (lam i + delta) ^ (-(1 / 2 : ℝ))) := by
    filter_upwards
      [show Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) by
        exact self_mem_nhdsWithin]
      with delta hdelta
    simpa [lam] using hcoeff_spec t hdelta
  have htarget :
      supportDual t =
        ∑ i : FlatMatrixIndex m n,
          (coeff t i) ^ 2 * (lam i) ^ (-(1 / 2 : ℝ)) := by
    rfl
  rw [htarget]
  exact hlim.congr' heventual.symm

private theorem theorem7_hhat_support_bound_of_regularized_limits {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat)
    (supportDual : Fin T → ℝ)
    (traceLimit : ℝ)
    (hDualLimit : ∀ t : Fin T,
      Filter.Tendsto
        (fun delta : ℝ =>
          theorem7_hhat_delta_dual_value_total S run rankBound delta t)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (supportDual t)))
    (hTraceLimit :
      Filter.Tendsto
        (fun delta : ℝ =>
          theorem7_hhat_delta_trace_value_total S run rankBound delta)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds traceLimit))
    (hEq6RegularizedBound :
      ∀ {delta : ℝ} (hdelta : 0 < delta),
        theorem7_hhat_delta_equation6_bound_prop S run rankBound hdelta) :
    (∑ t : Fin T, supportDual t) ≤ 2 * traceLimit := by
  classical
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  haveI : Filter.NeBot l := by
    simpa [l] using
      (nhdsWithin_Ioi_neBot (a := (0 : ℝ)) (b := 0) (le_refl 0))
  have hsum :
      Filter.Tendsto
        (fun delta : ℝ =>
          ∑ t : Fin T,
            theorem7_hhat_delta_dual_value_total S run rankBound delta t)
        l
        (nhds (∑ t : Fin T, supportDual t)) := by
    simpa [l] using
      (tendsto_finset_sum (s := (Finset.univ : Finset (Fin T)))
        (f := fun t delta =>
          theorem7_hhat_delta_dual_value_total S run rankBound delta t)
        (a := supportDual) (x := l)
        (fun t _ => by simpa [l] using hDualLimit t))
  have hright :
      Filter.Tendsto
        (fun delta : ℝ =>
          2 * theorem7_hhat_delta_trace_value_total S run rankBound delta)
        l
        (nhds (2 * traceLimit)) := by
    exact hTraceLimit.const_mul 2
  have heventual :
      (fun delta : ℝ =>
        ∑ t : Fin T,
          theorem7_hhat_delta_dual_value_total S run rankBound delta t) ≤ᶠ[l]
        (fun delta : ℝ =>
          2 * theorem7_hhat_delta_trace_value_total S run rankBound delta) := by
    filter_upwards
      [show Set.Ioi (0 : ℝ) ∈ l by
        simpa [l] using (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈
          nhdsWithin (0 : ℝ) (Set.Ioi 0))]
      with delta hdelta
    have hdelta_pos : 0 < delta := hdelta
    have hEq6 := hEq6RegularizedBound hdelta_pos
    calc
      (∑ t : Fin T,
        theorem7_hhat_delta_dual_value_total S run rankBound delta t) =
          ∑ t : Fin T,
            dualQuadraticForm (matrixVec (run.gradientAt t))
              (theorem7_hhat_delta_prefix_pd S run rankBound delta hdelta_pos
                (nextIndex t)) := by
            apply Finset.sum_congr rfl
            intro t _
            rw [theorem7_hhat_delta_dual_value_total, dif_pos hdelta_pos]
      _ ≤ 2 * genericTrace
            (theorem7_hhat_delta_prefix_pd S run rankBound delta hdelta_pos
              (finalIndex T)) := by
            simpa [theorem7_hhat_delta_equation6_bound_prop] using hEq6
      _ = 2 * theorem7_hhat_delta_trace_value_total S run rankBound delta := by
            rw [theorem7_hhat_delta_trace_value_total, dif_pos hdelta_pos]
  exact le_of_tendsto_of_tendsto hsum hright heventual

private theorem theorem7_hhat_positive_delta_support_limits_exist {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat) :
    ∃ supportDual : Fin T → ℝ,
      (∀ t : Fin T,
        Filter.Tendsto
          (fun delta : ℝ =>
            theorem7_hhat_delta_dual_value_total S run rankBound delta t)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (supportDual t))) ∧
      Filter.Tendsto
        (fun delta : ℝ =>
          theorem7_hhat_delta_trace_value_total S run rankBound delta)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds
          (genericTrace
            (psdMatrixPower
              ((positiveRankReal rankBound * S.epsilon) •
                  (1 : GenericSquare (FlatMatrixIndex m n)) +
                ∑ s : Fin T,
                  if s.1 < (finalIndex T).1 then
                    vectorOuter (matrixVec (run.gradientAt s)) else 0)
              (1 / 2 : ℝ)
              (theorem7_hhat_prefix_posSemidef S run rankBound (finalIndex T))))) := by
  classical
  obtain ⟨supportDual, hDualLimit⟩ :=
    theorem7_hhat_positive_delta_dual_support_limits_exist S run rankBound
  exact ⟨supportDual, hDualLimit,
    theorem7_hhat_delta_trace_value_total_tendsto S run rankBound⟩

private theorem theorem7_hhat_positive_delta_range_limit_bound {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat)
    (hEq6RegularizedBound :
      ∀ {delta : ℝ} (hdelta : 0 < delta),
        theorem7_hhat_delta_equation6_bound_prop S run rankBound hdelta) :
    ∃ supportDual : Fin T → ℝ,
      (∀ t : Fin T,
        Filter.Tendsto
          (fun delta : ℝ =>
            theorem7_hhat_delta_dual_value_total S run rankBound delta t)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (supportDual t))) ∧
      Filter.Tendsto
        (fun delta : ℝ =>
          theorem7_hhat_delta_trace_value_total S run rankBound delta)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds
          (genericTrace
            (psdMatrixPower
              ((positiveRankReal rankBound * S.epsilon) •
                  (1 : GenericSquare (FlatMatrixIndex m n)) +
                ∑ s : Fin T,
                  if s.1 < (finalIndex T).1 then
                    vectorOuter (matrixVec (run.gradientAt s)) else 0)
              (1 / 2 : ℝ)
              (theorem7_hhat_prefix_posSemidef S run rankBound (finalIndex T))))) ∧
      (∑ t : Fin T, supportDual t) ≤
        2 * genericTrace
          (psdMatrixPower
            ((positiveRankReal rankBound * S.epsilon) •
                (1 : GenericSquare (FlatMatrixIndex m n)) +
              ∑ s : Fin T,
                if s.1 < (finalIndex T).1 then
                  vectorOuter (matrixVec (run.gradientAt s)) else 0)
            (1 / 2 : ℝ)
            (theorem7_hhat_prefix_posSemidef S run rankBound (finalIndex T))) := by
  classical
  obtain ⟨supportDual, hDualLimit, hTraceLimit⟩ :=
    theorem7_hhat_positive_delta_support_limits_exist S run rankBound
  refine ⟨supportDual, hDualLimit, hTraceLimit, ?_⟩
  exact
    theorem7_hhat_support_bound_of_regularized_limits
      S run rankBound supportDual
      (genericTrace
        (psdMatrixPower
          ((positiveRankReal rankBound * S.epsilon) •
              (1 : GenericSquare (FlatMatrixIndex m n)) +
            ∑ s : Fin T,
              if s.1 < (finalIndex T).1 then
                vectorOuter (matrixVec (run.gradientAt s)) else 0)
          (1 / 2 : ℝ)
          (theorem7_hhat_prefix_posSemidef S run rankBound (finalIndex T))))
      hDualLimit hTraceLimit hEq6RegularizedBound

/- The tempting endpoint
   `dual_Halg(g) <= sqrt(r) * dual_Hhat_delta(g)` eventually in `delta`
   is not a valid replacement for the singular support limit.  Even in the
   scalar equality case, the positive-delta inverse value approaches the
   support value from below.  The private Theorem 7 endpoint must therefore
   prove a direct support/pseudoinverse comparison, not this stronger
   eventual comparison. -/
private theorem theorem7_eventual_regularized_transfer_scalar_obstruction :
    ¬ (∀ delta : ℝ, 0 < delta →
      (1 : ℝ) ≤ (1 + delta) ^ (-(1 / 2 : ℝ))) := by
  intro h
  have h1 := h 1 (by norm_num)
  have hpow : (1 + (1 : ℝ)) ^ (-(1 / 2 : ℝ)) = (Real.sqrt 2)⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1 + 1) (1 / 2 : ℝ)]
    rw [← Real.sqrt_eq_rpow]
    norm_num
  rw [hpow] at h1
  have hsqrt_gt_one : 1 < Real.sqrt 2 := by
    have hsq : (1 : ℝ)^2 < (Real.sqrt 2)^2 := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    nlinarith [Real.sqrt_nonneg 2]
  have hinv_lt_one : (Real.sqrt 2)⁻¹ < 1 := by
    exact inv_lt_one_of_one_lt₀ hsqrt_gt_one
  linarith

private theorem theorem7_algorithm_dual_pointwise_le_sqrt_rank_hhat_support
    {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat)
    (hEq5 : ∀ N : Fin (T + 1),
      psdMatrixPower
          ((positiveRankReal rankBound * S.epsilon) •
              (1 : GenericSquare (FlatMatrixIndex m n)) +
            ∑ s : Fin T,
              if s.1 < N.1 then vectorOuter (matrixVec (run.gradientAt s)) else 0)
          (1 / 2 : ℝ)
          (theorem7_hhat_prefix_posSemidef S run rankBound N) ≤
        Real.sqrt (positiveRankReal rankBound) •
          ((matrixPower (run.leftAccumulator N) (1 / 4 : ℝ)
              (run.leftAccumulator_psd N)) ⊗ₖ
            (matrixPower (run.rightAccumulator N) (1 / 4 : ℝ)
              (run.rightAccumulator_psd N))))
    (supportDual : Fin T → ℝ)
    (hSupportLimit : ∀ t : Fin T,
      Filter.Tendsto
        (fun delta : ℝ =>
          theorem7_hhat_delta_dual_value_total S run rankBound delta t)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (supportDual t)))
    (t : Fin T) :
    dualQuadraticForm (matrixVec (run.gradientAt t))
      ((matrixPower (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
          (run.leftAccumulator_psd (nextIndex t))) ⊗ₖ
        (matrixPower (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
          (run.rightAccumulator_psd (nextIndex t)))) ≤
      Real.sqrt (positiveRankReal rankBound) * supportDual t := by
  classical
  have hSupportTransfer :
      dualQuadraticForm (matrixVec (run.gradientAt t))
        ((matrixPower (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
            (run.leftAccumulator_psd (nextIndex t))) ⊗ₖ
          (matrixPower (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
            (run.rightAccumulator_psd (nextIndex t)))) ≤
        Real.sqrt (positiveRankReal rankBound) * supportDual t := by
    -- Correct remaining inverse-order support endpoint: combine Eq. (5) at
    -- `nextIndex t` with the pseudoinverse/support interpretation identified
    -- by `hSupportLimit`.  The stronger eventual regularized comparison is
    -- false in scalar equality cases; see
    -- `theorem7_eventual_regularized_transfer_scalar_obstruction`.
    obtain ⟨coeff, hcoeff_spec, hcoeff_zero, hcoeff_def⟩ :=
      theorem7_hhat_delta_dual_value_total_spectral_support S run rankBound t
    let supportValue : ℝ :=
      ∑ i : FlatMatrixIndex m n,
        coeff i ^ 2 *
          ((theorem7_hhat_prefix_posSemidef S run rankBound
              (nextIndex t)).1.eigenvalues i) ^ (-(1 / 2 : ℝ))
    let lam : FlatMatrixIndex m n → ℝ := fun i =>
      (theorem7_hhat_prefix_posSemidef S run rankBound
        (nextIndex t)).1.eigenvalues i
    have hSpectralLimit :
        Filter.Tendsto
          (fun delta : ℝ =>
            theorem7_hhat_delta_dual_value_total S run rankBound delta t)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds supportValue) := by
      have hlim :
          Filter.Tendsto
            (fun delta : ℝ =>
              ∑ i : FlatMatrixIndex m n,
                coeff i ^ 2 * (lam i + delta) ^ (-(1 / 2 : ℝ)))
            (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhds
              (∑ i : FlatMatrixIndex m n,
                coeff i ^ 2 * (lam i) ^ (-(1 / 2 : ℝ)))) := by
        exact
          spectral_support_inverse_sqrt_tendsto lam coeff
            (fun i => by
              simpa [lam] using
                (theorem7_hhat_prefix_posSemidef S run rankBound
                  (nextIndex t)).eigenvalues_nonneg i)
            (fun i hi => hcoeff_zero i (by simpa [lam] using hi))
      have heventual :
          (fun delta : ℝ =>
            theorem7_hhat_delta_dual_value_total S run rankBound delta t) =ᶠ[
              nhdsWithin (0 : ℝ) (Set.Ioi 0)]
            (fun delta : ℝ =>
              ∑ i : FlatMatrixIndex m n,
                coeff i ^ 2 * (lam i + delta) ^ (-(1 / 2 : ℝ))) := by
        filter_upwards
          [show Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) by
            exact self_mem_nhdsWithin]
          with delta hdelta
        simpa [lam] using hcoeff_spec hdelta
      have htarget :
          supportValue =
            ∑ i : FlatMatrixIndex m n,
              coeff i ^ 2 * (lam i) ^ (-(1 / 2 : ℝ)) := by
        rfl
      rw [htarget]
      exact hlim.congr' heventual.symm
    have hSupportEq : supportDual t = supportValue := by
      exact tendsto_nhds_unique (hSupportLimit t) hSpectralLimit
    let A : GenericSquare (FlatMatrixIndex m n) :=
      theorem7_hhat_prefix_base S run rankBound (nextIndex t)
    let Halg : GenericSquare (FlatMatrixIndex m n) :=
      (matrixPower (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
          (run.leftAccumulator_psd (nextIndex t))) ⊗ₖ
        (matrixPower (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
          (run.rightAccumulator_psd (nextIndex t)))
    let alpha : ℝ := Real.sqrt (positiveRankReal rankBound)
    have hApsd : A.PosSemidef := by
      simpa [A, theorem7_hhat_prefix_base] using
        theorem7_hhat_prefix_posSemidef S run rankBound (nextIndex t)
    have hHalg_pd : Halg.PosDef := by
      simpa [Halg] using
        (theorem7_source_flat_update_and_pd_preconditioner S run).2 t
    have halpha_nonneg : 0 ≤ alpha := by
      exact Real.sqrt_nonneg _
    have hroot_le :
        psdMatrixPower A (1 / 2 : ℝ) hApsd ≤ alpha • Halg := by
      simpa [A, Halg, alpha, theorem7_hhat_prefix_base] using hEq5 (nextIndex t)
    have hcoeff_def_A : ∀ i : FlatMatrixIndex m n,
        coeff i =
          ∑ j : FlatMatrixIndex m n, matrixVec (run.gradientAt t) j *
            (hApsd.1.eigenvectorUnitary : GenericSquare (FlatMatrixIndex m n)) j i := by
      intro i
      simpa [A, hApsd, theorem7_hhat_prefix_base] using hcoeff_def i
    have hcoeff_zero_A : ∀ i : FlatMatrixIndex m n,
        hApsd.1.eigenvalues i = 0 → coeff i = 0 := by
      intro i hi
      exact hcoeff_zero i (by simpa [A, hApsd, theorem7_hhat_prefix_base] using hi)
    have hbound :
        dualQuadraticForm (matrixVec (run.gradientAt t)) Halg ≤
          alpha *
            ∑ i : FlatMatrixIndex m n,
              coeff i ^ 2 * (hApsd.1.eigenvalues i) ^ (-(1 / 2 : ℝ)) := by
      exact
        spectral_support_inverse_sqrt_order_dual_bound
          A Halg hApsd hHalg_pd alpha halpha_nonneg
          (matrixVec (run.gradientAt t)) coeff hroot_le hcoeff_def_A hcoeff_zero_A
    have hsupportValue_A :
        supportValue =
          ∑ i : FlatMatrixIndex m n,
            coeff i ^ 2 * (hApsd.1.eigenvalues i) ^ (-(1 / 2 : ℝ)) := by
      rfl
    calc
      dualQuadraticForm (matrixVec (run.gradientAt t))
          ((matrixPower (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
              (run.leftAccumulator_psd (nextIndex t))) ⊗ₖ
            (matrixPower (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
              (run.rightAccumulator_psd (nextIndex t)))) =
          dualQuadraticForm (matrixVec (run.gradientAt t)) Halg := by
            rfl
      _ ≤ alpha * supportValue := by
            simpa [hsupportValue_A] using hbound
      _ = Real.sqrt (positiveRankReal rankBound) * supportDual t := by
            simpa [alpha, hSupportEq]
  exact hSupportTransfer

private theorem theorem7_algorithm_dual_sum_le_sqrt_rank_hhat_support_sum {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat)
    (hEq5 : ∀ N : Fin (T + 1),
      psdMatrixPower
          ((positiveRankReal rankBound * S.epsilon) •
              (1 : GenericSquare (FlatMatrixIndex m n)) +
            ∑ s : Fin T,
              if s.1 < N.1 then vectorOuter (matrixVec (run.gradientAt s)) else 0)
          (1 / 2 : ℝ)
          (theorem7_hhat_prefix_posSemidef S run rankBound N) ≤
        Real.sqrt (positiveRankReal rankBound) •
          ((matrixPower (run.leftAccumulator N) (1 / 4 : ℝ)
              (run.leftAccumulator_psd N)) ⊗ₖ
            (matrixPower (run.rightAccumulator N) (1 / 4 : ℝ)
              (run.rightAccumulator_psd N))))
    (supportDual : Fin T → ℝ)
    (hSupportLimit : ∀ t : Fin T,
      Filter.Tendsto
        (fun delta : ℝ =>
          theorem7_hhat_delta_dual_value_total S run rankBound delta t)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (supportDual t))) :
    (∑ t : Fin T,
      dualQuadraticForm (matrixVec (run.gradientAt t))
        ((matrixPower (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
            (run.leftAccumulator_psd (nextIndex t))) ⊗ₖ
          (matrixPower (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
            (run.rightAccumulator_psd (nextIndex t))))) ≤
      Real.sqrt (positiveRankReal rankBound) *
        ∑ t : Fin T, supportDual t := by
  classical
  calc
    (∑ t : Fin T,
      dualQuadraticForm (matrixVec (run.gradientAt t))
        ((matrixPower (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
            (run.leftAccumulator_psd (nextIndex t))) ⊗ₖ
          (matrixPower (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
            (run.rightAccumulator_psd (nextIndex t))))) ≤
        ∑ t : Fin T,
          Real.sqrt (positiveRankReal rankBound) * supportDual t := by
            exact Finset.sum_le_sum (fun t _ =>
              theorem7_algorithm_dual_pointwise_le_sqrt_rank_hhat_support
                S run rankBound hEq5 supportDual hSupportLimit t)
    _ = Real.sqrt (positiveRankReal rankBound) *
        ∑ t : Fin T, supportDual t := by
          simp [Finset.mul_sum]

/- Corrected private endpoint for Source Theorem 7, Eq. (5)/(6).

   The printed proof applies Lemma 2 to the unregularized hatted matrices and
   then uses Eq. (5) twice.  Under only `epsilon >= 0`, the unregularized hatted
   matrices may be singular, so the faithful Lean endpoint must pass through
   the positive-δ Eq. (6) family and a support/range-limit transfer rather than
   through Lean's total inverse on `theorem7_hhat_prefix`.  This theorem is the
   private bridge authorized by the audit arbiter: it consumes the proved
   regularized Eq. (6) supplier, the Eq. (5) order facts, and the final trace
   transfer, and exposes exactly the algorithmic dual-sum inequality needed by
   the public Theorem 7 proof. -/
private theorem theorem7_positive_delta_range_limit_endpoint_bridge {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat)
    (hEq5 : ∀ N : Fin (T + 1),
      psdMatrixPower
          ((positiveRankReal rankBound * S.epsilon) •
              (1 : GenericSquare (FlatMatrixIndex m n)) +
            ∑ s : Fin T,
              if s.1 < N.1 then vectorOuter (matrixVec (run.gradientAt s)) else 0)
          (1 / 2 : ℝ)
          (theorem7_hhat_prefix_posSemidef S run rankBound N) ≤
        Real.sqrt (positiveRankReal rankBound) •
          ((matrixPower (run.leftAccumulator N) (1 / 4 : ℝ)
              (run.leftAccumulator_psd N)) ⊗ₖ
            (matrixPower (run.rightAccumulator N) (1 / 4 : ℝ)
              (run.rightAccumulator_psd N))))
    (hTraceTransfer :
      2 * Real.sqrt (positiveRankReal rankBound) *
          genericTrace
            (psdMatrixPower
              ((positiveRankReal rankBound * S.epsilon) •
                  (1 : GenericSquare (FlatMatrixIndex m n)) +
                ∑ s : Fin T,
                  if s.1 < (finalIndex T).1 then
                    vectorOuter (matrixVec (run.gradientAt s)) else 0)
              (1 / 2 : ℝ)
              (theorem7_hhat_prefix_posSemidef S run rankBound (finalIndex T))) ≤
        2 * positiveRankReal rankBound *
          genericTrace
            ((matrixPower (run.leftAccumulator (finalIndex T)) (1 / 4 : ℝ)
                (run.leftAccumulator_psd (finalIndex T))) ⊗ₖ
              (matrixPower (run.rightAccumulator (finalIndex T)) (1 / 4 : ℝ)
                (run.rightAccumulator_psd (finalIndex T)))))
    (hEq6RegularizedBound :
      ∀ {delta : ℝ} (hdelta : 0 < delta),
        theorem7_hhat_delta_equation6_bound_prop S run rankBound hdelta) :
    (∑ t : Fin T,
      dualQuadraticForm (matrixVec (run.gradientAt t))
        ((matrixPower (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
            (run.leftAccumulator_psd (nextIndex t))) ⊗ₖ
          (matrixPower (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
            (run.rightAccumulator_psd (nextIndex t))))) ≤
      2 * positiveRankReal rankBound *
        genericTrace
          ((matrixPower (run.leftAccumulator (finalIndex T)) (1 / 4 : ℝ)
              (run.leftAccumulator_psd (finalIndex T))) ⊗ₖ
            (matrixPower (run.rightAccumulator (finalIndex T)) (1 / 4 : ℝ)
              (run.rightAccumulator_psd (finalIndex T)))) := by
  classical
  obtain ⟨supportDual, hSupportLimit, _hTraceLimit, hSupportBound⟩ :=
    theorem7_hhat_positive_delta_range_limit_bound
      S run rankBound hEq6RegularizedBound
  have hDualTransfer :
      (∑ t : Fin T,
        dualQuadraticForm (matrixVec (run.gradientAt t))
          ((matrixPower (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
              (run.leftAccumulator_psd (nextIndex t))) ⊗ₖ
            (matrixPower (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
              (run.rightAccumulator_psd (nextIndex t))))) ≤
        Real.sqrt (positiveRankReal rankBound) *
          ∑ t : Fin T, supportDual t := by
    exact
      theorem7_algorithm_dual_sum_le_sqrt_rank_hhat_support_sum
        S run rankBound hEq5 supportDual hSupportLimit
  have hsqrt_nonneg : 0 ≤ Real.sqrt (positiveRankReal rankBound) := by
    positivity
  have hScaledSupport :
      Real.sqrt (positiveRankReal rankBound) * (∑ t : Fin T, supportDual t) ≤
        Real.sqrt (positiveRankReal rankBound) *
          (2 * genericTrace
            (psdMatrixPower
              ((positiveRankReal rankBound * S.epsilon) •
                  (1 : GenericSquare (FlatMatrixIndex m n)) +
                ∑ s : Fin T,
                  if s.1 < (finalIndex T).1 then
                    vectorOuter (matrixVec (run.gradientAt s)) else 0)
              (1 / 2 : ℝ)
              (theorem7_hhat_prefix_posSemidef S run rankBound (finalIndex T)))) :=
    mul_le_mul_of_nonneg_left hSupportBound hsqrt_nonneg
  have hToHhatTrace :
      (∑ t : Fin T,
        dualQuadraticForm (matrixVec (run.gradientAt t))
          ((matrixPower (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
              (run.leftAccumulator_psd (nextIndex t))) ⊗ₖ
            (matrixPower (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
              (run.rightAccumulator_psd (nextIndex t))))) ≤
        2 * Real.sqrt (positiveRankReal rankBound) *
          genericTrace
            (psdMatrixPower
              ((positiveRankReal rankBound * S.epsilon) •
                  (1 : GenericSquare (FlatMatrixIndex m n)) +
                ∑ s : Fin T,
                  if s.1 < (finalIndex T).1 then
                    vectorOuter (matrixVec (run.gradientAt s)) else 0)
              (1 / 2 : ℝ)
              (theorem7_hhat_prefix_posSemidef S run rankBound (finalIndex T))) := by
    calc
      (∑ t : Fin T,
        dualQuadraticForm (matrixVec (run.gradientAt t))
          ((matrixPower (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
              (run.leftAccumulator_psd (nextIndex t))) ⊗ₖ
            (matrixPower (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
              (run.rightAccumulator_psd (nextIndex t)))))
          ≤ Real.sqrt (positiveRankReal rankBound) *
              ∑ t : Fin T, supportDual t := hDualTransfer
      _ ≤ Real.sqrt (positiveRankReal rankBound) *
            (2 * genericTrace
              (psdMatrixPower
                ((positiveRankReal rankBound * S.epsilon) •
                    (1 : GenericSquare (FlatMatrixIndex m n)) +
                  ∑ s : Fin T,
                    if s.1 < (finalIndex T).1 then
                      vectorOuter (matrixVec (run.gradientAt s)) else 0)
                (1 / 2 : ℝ)
                (theorem7_hhat_prefix_posSemidef S run rankBound (finalIndex T)))) :=
          hScaledSupport
      _ = 2 * Real.sqrt (positiveRankReal rankBound) *
            genericTrace
              (psdMatrixPower
                ((positiveRankReal rankBound * S.epsilon) •
                    (1 : GenericSquare (FlatMatrixIndex m n)) +
                  ∑ s : Fin T,
                    if s.1 < (finalIndex T).1 then
                      vectorOuter (matrixVec (run.gradientAt s)) else 0)
                (1 / 2 : ℝ)
                (theorem7_hhat_prefix_posSemidef S run rankBound (finalIndex T))) := by
          ring
  exact le_trans hToHhatTrace hTraceTransfer

private theorem theorem7_source_dual_sum_le_rank_trace {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat)
    (hrank : ∀ t : Fin T, (run.gradientAt t).rank ≤ rankBound.1) :
    (∑ t : Fin T,
      dualQuadraticForm (matrixVec (run.gradientAt t))
        ((matrixPower (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
            (run.leftAccumulator_psd (nextIndex t))) ⊗ₖ
          (matrixPower (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
            (run.rightAccumulator_psd (nextIndex t))))) ≤
      2 * positiveRankReal rankBound *
        genericTrace
          ((matrixPower (run.leftAccumulator (finalIndex T)) (1 / 4 : ℝ)
              (run.leftAccumulator_psd (finalIndex T))) ⊗ₖ
            (matrixPower (run.rightAccumulator (finalIndex T)) (1 / 4 : ℝ)
              (run.rightAccumulator_psd (finalIndex T)))) := by
  classical
  have hEq5 : ∀ N : Fin (T + 1),
      psdMatrixPower
          ((positiveRankReal rankBound * S.epsilon) •
              (1 : GenericSquare (FlatMatrixIndex m n)) +
            ∑ s : Fin T,
              if s.1 < N.1 then vectorOuter (matrixVec (run.gradientAt s)) else 0)
          (1 / 2 : ℝ)
          (theorem7_hhat_prefix_posSemidef S run rankBound N) ≤
        Real.sqrt (positiveRankReal rankBound) •
          ((matrixPower (run.leftAccumulator N) (1 / 4 : ℝ)
              (run.leftAccumulator_psd N)) ⊗ₖ
            (matrixPower (run.rightAccumulator N) (1 / 4 : ℝ)
              (run.rightAccumulator_psd N))) := by
    intro N
    exact theorem7_hhat_order_from_prefix_rank_domination
      S run rankBound hrank N (theorem7_hhat_prefix_posSemidef S run rankBound N)
  -- Source Eq. (5)/(6): use Lemma 8 on every prefix, operator monotonicity
  -- of the square root, Lemma 2's FTL-BTL potential comparison, and then
  -- transfer the hatted dual norms back to the full Kronecker preconditioner.
  have hTraceTransfer :
      2 * Real.sqrt (positiveRankReal rankBound) *
          genericTrace
            (psdMatrixPower
              ((positiveRankReal rankBound * S.epsilon) •
                  (1 : GenericSquare (FlatMatrixIndex m n)) +
                ∑ s : Fin T,
                  if s.1 < (finalIndex T).1 then
                    vectorOuter (matrixVec (run.gradientAt s)) else 0)
              (1 / 2 : ℝ)
              (theorem7_hhat_prefix_posSemidef S run rankBound (finalIndex T))) ≤
        2 * positiveRankReal rankBound *
          genericTrace
            ((matrixPower (run.leftAccumulator (finalIndex T)) (1 / 4 : ℝ)
                (run.leftAccumulator_psd (finalIndex T))) ⊗ₖ
              (matrixPower (run.rightAccumulator (finalIndex T)) (1 / 4 : ℝ)
                (run.rightAccumulator_psd (finalIndex T)))) := by
    exact theorem7_hhat_final_trace_to_algorithm_trace
      S run rankBound (hEq5 (finalIndex T))
  have hEq6RegularizedBound :
      ∀ {delta : ℝ} (hdelta : 0 < delta),
        theorem7_hhat_delta_equation6_bound_prop S run rankBound hdelta := by
    intro delta hdelta
    exact theorem7_hhat_delta_equation6_bound S run rankBound hdelta
  exact
    theorem7_positive_delta_range_limit_endpoint_bridge
      S run rankBound hEq5 hTraceTransfer hEq6RegularizedBound

private theorem theorem7_source_eta_kron_trace_finish {T m n : Nat}
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun)
    [Nonempty (Fin T)] (rankBound : PosNat) (Wstar : MatrixSpace m n)
    (heta : S.eta = learningRate (run.comparatorRadius Wstar)
      (positiveRankReal rankBound))
    (hDpos : 0 < run.comparatorRadius Wstar) :
    (((run.comparatorRadius Wstar) ^ 2 / (2 * S.eta) +
        S.eta * positiveRankReal rankBound) *
      genericTrace
        ((matrixPower (run.leftAccumulator (finalIndex T)) (1 / 4 : ℝ)
            (run.leftAccumulator_psd (finalIndex T))) ⊗ₖ
          (matrixPower (run.rightAccumulator (finalIndex T)) (1 / 4 : ℝ)
            (run.rightAccumulator_psd (finalIndex T))))) =
      Real.sqrt (2 * positiveRankReal rankBound) *
        run.comparatorRadius Wstar *
        matrixTrace (matrixPower (run.leftAccumulator (finalIndex T)) (1 / 4 : ℝ)
          (run.leftAccumulator_psd (finalIndex T))) *
        matrixTrace (matrixPower (run.rightAccumulator (finalIndex T)) (1 / 4 : ℝ)
          (run.rightAccumulator_psd (finalIndex T))) := by
  classical
  let D : ℝ := run.comparatorRadius Wstar
  let r : ℝ := positiveRankReal rankBound
  let Lpow : SquareMatrix m :=
    matrixPower (run.leftAccumulator (finalIndex T)) (1 / 4 : ℝ)
      (run.leftAccumulator_psd (finalIndex T))
  let Rpow : SquareMatrix n :=
    matrixPower (run.rightAccumulator (finalIndex T)) (1 / 4 : ℝ)
      (run.rightAccumulator_psd (finalIndex T))
  have hetaD : S.eta = SOptLib.sqrtTwoScaleStepSize D r := by
    simpa [D, r, learningRate] using heta
  have hcoef :
      D ^ 2 / (2 * S.eta) + S.eta * r = Real.sqrt (2 * r) * D := by
    rw [hetaD]
    exact SOptLib.sqrtTwoScaleStepSize_balance D r
  calc
    (((run.comparatorRadius Wstar) ^ 2 / (2 * S.eta) +
          S.eta * positiveRankReal rankBound) *
        genericTrace (Lpow ⊗ₖ Rpow))
        = (D ^ 2 / (2 * S.eta) + S.eta * r) *
            (matrixTrace Lpow * matrixTrace Rpow) := by
            rw [genericTrace_kronecker]
    _ = Real.sqrt (2 * r) * D * matrixTrace Lpow * matrixTrace Rpow := by
            rw [hcoef]
            ring
    _ = Real.sqrt (2 * positiveRankReal rankBound) *
          run.comparatorRadius Wstar *
          matrixTrace (matrixPower (run.leftAccumulator (finalIndex T)) (1 / 4 : ℝ)
            (run.leftAccumulator_psd (finalIndex T))) *
          matrixTrace (matrixPower (run.rightAccumulator (finalIndex T)) (1 / 4 : ℝ)
            (run.rightAccumulator_psd (finalIndex T))) := by
            simp [D, r, Lpow, Rpow]

/- Corrected-domain endpoint for Theorem 7.  This records the proof-domain
   facts that the PDF proof uses but does not state in the theorem head. -/
theorem Theorem_7_matrix_regret_corrected_domain
    (S : MatrixAlgorithm1 T m n) (run : S.CorrectedRun) [Nonempty (Fin T)]
    (rankBound : PosNat) (Wstar : MatrixSpace m n)
    (heta : S.eta = learningRate (run.comparatorRadius Wstar) (positiveRankReal rankBound))
    (hrank : ∀ t : Fin T, (run.gradientAt t).rank ≤ rankBound.1) :
    run.regret Wstar ≤
      Real.sqrt (2 * positiveRankReal rankBound) * run.comparatorRadius Wstar *
        matrixTrace (matrixPower (run.leftAccumulator (finalIndex T)) (1 / 4 : ℝ)
          (run.leftAccumulator_psd (finalIndex T))) *
        matrixTrace (matrixPower (run.rightAccumulator (finalIndex T)) (1 / 4 : ℝ)
          (run.rightAccumulator_psd (finalIndex T))) := by
  classical
  let D := run.comparatorRadius Wstar
  by_cases hD0 : D = 0
  · have hD0_run : run.comparatorRadius Wstar = 0 := by
      simpa [D] using hD0
    have hiter : ∀ t : Fin T, run.iterate (currentIndex t) = Wstar := by
      intro t
      have hle :
          frobeniusNorm (run.iterate (currentIndex t) - Wstar) ≤
            run.comparatorRadius Wstar := by
        dsimp [MatrixAlgorithm1.CorrectedRun.comparatorRadius, finiteMax]
        exact Finset.le_sup'
          (fun t : Fin T => frobeniusNorm (run.iterate (currentIndex t) - Wstar))
          (Finset.mem_univ t)
      have hnorm_le_zero :
          frobeniusNorm (run.iterate (currentIndex t) - Wstar) ≤ 0 := by
        simpa [hD0_run] using hle
      have hnorm_eq_zero :
          frobeniusNorm (run.iterate (currentIndex t) - Wstar) = 0 := by
        have hnonneg :
            0 ≤ frobeniusNorm (run.iterate (currentIndex t) - Wstar) := by
          unfold frobeniusNorm
          exact Real.sqrt_nonneg _
        exact le_antisymm hnorm_le_zero hnonneg
      have hsumsq_zero :
          (∑ i : Fin m, ∑ j : Fin n,
            (run.iterate (currentIndex t) - Wstar) i j *
              (run.iterate (currentIndex t) - Wstar) i j) = 0 := by
        have hsumsq_nonneg :
            0 ≤ (∑ i : Fin m, ∑ j : Fin n,
              (run.iterate (currentIndex t) - Wstar) i j *
                (run.iterate (currentIndex t) - Wstar) i j) := by
          exact Finset.sum_nonneg (by
            intro i _hi
            exact Finset.sum_nonneg (by
              intro j _hj
              exact mul_self_nonneg _))
        have hsqrt_sq := Real.sq_sqrt hsumsq_nonneg
        have hsqrt_eq :
            (Real.sqrt (∑ i : Fin m, ∑ j : Fin n,
              (run.iterate (currentIndex t) - Wstar) i j *
                (run.iterate (currentIndex t) - Wstar) i j)) = 0 := by
          simpa [frobeniusNorm] using hnorm_eq_zero
        rw [← hsqrt_sq]
        rw [hsqrt_eq]
        norm_num
      have hentry_zero : ∀ i : Fin m, ∀ j : Fin n,
          (run.iterate (currentIndex t) - Wstar) i j = 0 := by
        intro i j
        have hrow_zero :
            (∑ j : Fin n,
              (run.iterate (currentIndex t) - Wstar) i j *
                (run.iterate (currentIndex t) - Wstar) i j) = 0 := by
          have hrow_nonneg : ∀ i : Fin m, 0 ≤ (∑ j : Fin n,
              (run.iterate (currentIndex t) - Wstar) i j *
                (run.iterate (currentIndex t) - Wstar) i j) := by
            intro i
            exact Finset.sum_nonneg (by
              intro j _hj
              exact mul_self_nonneg _)
          exact (Finset.sum_eq_zero_iff_of_nonneg (by
            intro i _hi
            exact hrow_nonneg i)).mp hsumsq_zero i (Finset.mem_univ i)
        have hsq_zero :
            (run.iterate (currentIndex t) - Wstar) i j *
              (run.iterate (currentIndex t) - Wstar) i j = 0 := by
          exact (Finset.sum_eq_zero_iff_of_nonneg (by
            intro j _hj
            exact mul_self_nonneg _)).mp hrow_zero j (Finset.mem_univ j)
        exact mul_self_eq_zero.mp hsq_zero
      ext i j
      have h := hentry_zero i j
      simpa using sub_eq_zero.mp h
    have hreg : run.regret Wstar = 0 := by
      unfold MatrixAlgorithm1.CorrectedRun.regret
      simp [hiter]
    rw [hreg, hD0_run]
    norm_num
  · have hD_nonneg : 0 ≤ D := by
      let t0 : Fin T := Classical.choice (inferInstance : Nonempty (Fin T))
      have hnorm_nonneg :
          0 ≤ frobeniusNorm (run.iterate (currentIndex t0) - Wstar) := by
        unfold frobeniusNorm
        exact Real.sqrt_nonneg _
      have hle :
          frobeniusNorm (run.iterate (currentIndex t0) - Wstar) ≤ D := by
        dsimp [D, MatrixAlgorithm1.CorrectedRun.comparatorRadius, finiteMax]
        exact Finset.le_sup'
          (fun t : Fin T => frobeniusNorm (run.iterate (currentIndex t) - Wstar))
          (Finset.mem_univ t0)
      exact le_trans hnorm_nonneg hle
    have hDpos : 0 < run.comparatorRadius Wstar := by
      have hDpos_local : 0 < D := lt_of_le_of_ne hD_nonneg (Ne.symm hD0)
      simpa [D] using hDpos_local
    have heta_pos : 0 < S.eta := by
      rw [heta]
      exact learningRate_pos_of_pos hDpos (positiveRankReal_pos rankBound)
    have hconvRegret :
        run.regret Wstar ≤ ∑ t : Fin T,
          vectorDot (matrixVec (run.gradientAt t))
            (matrixVec (run.iterate (currentIndex t)) - matrixVec Wstar) := by
      let idx : ℕ → Fin T := fun s =>
        if h : s - 1 < T then
          ⟨s - 1, h⟩
        else
          Classical.choice (inferInstance : Nonempty (Fin T))
      let toEuc : (FlatMatrixIndex m n → ℝ) →
          EuclideanSpace ℝ (FlatMatrixIndex m n) :=
        (EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ).symm
      let unvecLin : EuclideanSpace ℝ (FlatMatrixIndex m n) →ₗ[ℝ]
          MatrixSpace m n :=
        { toFun := fun v i j => (EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ v) (i, j)
          map_add' := by
            intro x y
            ext i j
            simp
          map_smul' := by
            intro a x
            ext i j
            simp }
      let lossNat : ℕ → EuclideanSpace ℝ (FlatMatrixIndex m n) → ℝ :=
        fun s v => S.loss (idx s) (unvecLin v)
      let x : ℕ → EuclideanSpace ℝ (FlatMatrixIndex m n) :=
        fun s => toEuc (matrixVec (run.iterate (currentIndex (idx s))))
      let g : ℕ → EuclideanSpace ℝ (FlatMatrixIndex m n) :=
        fun s => toEuc (matrixVec (run.gradientAt (idx s)))
      let xStar : EuclideanSpace ℝ (FlatMatrixIndex m n) :=
        toEuc (matrixVec Wstar)
      have hconv : ∀ s ∈ Finset.Icc 1 T, ConvexOn ℝ Set.univ (lossNat s) := by
        intro s _hs
        have hcomp := (S.loss_convex (idx s)).comp_linearMap unvecLin
        simpa [lossNat, unvecLin, Function.comp_def] using hcomp
      have hx : ∀ s ∈ Finset.Icc 1 T,
          x s ∈ (Set.univ : Set (EuclideanSpace ℝ (FlatMatrixIndex m n))) := by
        intro s _hs
        simp
      have hxStar :
          xStar ∈ (Set.univ : Set (EuclideanSpace ℝ (FlatMatrixIndex m n))) := by
        simp
      have hgrad : ∀ s ∈ Finset.Icc 1 T,
          HasGradientWithinAt (lossNat s) (g s) Set.univ (x s) := by
        intro s _hs
        simpa [lossNat, x, g, toEuc, unvecLin] using
          theorem7_flattened_loss_gradient_bridge S run (idx s)
      have hfinite := finite_horizon_convex_regret_le_gradient_inner_sum
        (F := (Set.univ : Set (EuclideanSpace ℝ (FlatMatrixIndex m n))))
        (loss := lossNat) (x := x) (g := g) (T := T) (xStar := xStar)
        hconv hx hxStar hgrad
      have hsum_loss_x :
          (∑ s ∈ Finset.Icc 1 T, lossNat s (x s)) =
            ∑ t : Fin T, S.loss t (run.iterate (currentIndex t)) := by
        simpa [lossNat, x, idx, toEuc, unvecLin, matrixVec] using
          (sum_Icc_one_matrix_fin_reindex (T := T)
            (F := fun t : Fin T => S.loss t (run.iterate (currentIndex t))))
      have hsum_loss_star :
          (∑ s ∈ Finset.Icc 1 T, lossNat s xStar) =
            ∑ t : Fin T, S.loss t Wstar := by
        simpa [lossNat, xStar, idx, toEuc, unvecLin, matrixVec] using
          (sum_Icc_one_matrix_fin_reindex (T := T)
            (F := fun t : Fin T => S.loss t Wstar))
      have hleft :
          (∑ s ∈ Finset.Icc 1 T, lossNat s (x s)) -
              (∑ s ∈ Finset.Icc 1 T, lossNat s xStar) =
            run.regret Wstar := by
        rw [hsum_loss_x, hsum_loss_star]
        unfold MatrixAlgorithm1.CorrectedRun.regret
        rw [Finset.sum_sub_distrib]
      have hsum_rhs :
          (∑ s ∈ Finset.Icc 1 T, inner ℝ (g s) (x s - xStar)) =
            ∑ t : Fin T,
              vectorDot (matrixVec (run.gradientAt t))
                (matrixVec (run.iterate (currentIndex t)) - matrixVec Wstar) := by
        have hterm :
            (∑ s ∈ Finset.Icc 1 T, inner ℝ (g s) (x s - xStar)) =
              ∑ s ∈ Finset.Icc 1 T,
                vectorDot (matrixVec (run.gradientAt (idx s)))
                  (matrixVec (run.iterate (currentIndex (idx s))) - matrixVec Wstar) := by
          apply Finset.sum_congr rfl
          intro s hs
          simpa [g, x, xStar, toEuc] using
            (euclidean_inner_sub_eq_vectorDot
              (matrixVec (run.gradientAt (idx s)))
              (matrixVec (run.iterate (currentIndex (idx s))))
              (matrixVec Wstar))
        rw [hterm]
        simpa [idx] using
          (sum_Icc_one_matrix_fin_reindex (T := T)
            (F := fun t : Fin T =>
              vectorDot (matrixVec (run.gradientAt t))
                (matrixVec (run.iterate (currentIndex t)) - matrixVec Wstar)))
      calc
        run.regret Wstar =
            (∑ s ∈ Finset.Icc 1 T, lossNat s (x s)) -
              (∑ s ∈ Finset.Icc 1 T, lossNat s xStar) := hleft.symm
        _ ≤ ∑ s ∈ Finset.Icc 1 T, inner ℝ (g s) (x s - xStar) := hfinite
        _ = ∑ t : Fin T,
              vectorDot (matrixVec (run.gradientAt t))
                (matrixVec (run.iterate (currentIndex t)) - matrixVec Wstar) := hsum_rhs
    let w : Fin (T + 1) → FlatMatrixIndex m n → ℝ :=
      fun t => matrixVec (run.iterate t)
    let g : Fin T → FlatMatrixIndex m n → ℝ :=
      fun t => matrixVec (run.gradientAt t)
    let H : Fin T → GenericSquare (FlatMatrixIndex m n) := fun t =>
      (matrixPower (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
          (run.leftAccumulator_psd (nextIndex t))) ⊗ₖ
        (matrixPower (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
          (run.rightAccumulator_psd (nextIndex t)))
    let wstar : FlatMatrixIndex m n → ℝ := matrixVec Wstar
    have hflat := theorem7_source_flat_update_and_pd_preconditioner S run
    have hOMD :
        ∑ t : Fin T, vectorDot (matrixVec (run.gradientAt t))
          (matrixVec (run.iterate (currentIndex t)) - matrixVec Wstar) ≤
          (1 / (2 * S.eta)) *
            ∑ t : Fin T,
              (quadraticForm
                  (matrixVec (run.iterate (currentIndex t)) - matrixVec Wstar)
                  (H t) -
                quadraticForm
                  (matrixVec (run.iterate (nextIndex t)) - matrixVec Wstar)
                  (H t)) +
            (S.eta / 2) *
              ∑ t : Fin T, dualQuadraticForm (matrixVec (run.gradientAt t)) (H t) := by
      simpa [w, g, H, wstar] using
        (finite_index_adaptive_omd_regret (T := T) (ι := FlatMatrixIndex m n)
          S.eta heta_pos w g H wstar hflat.1 hflat.2)
    have hsource_pre_eq3 :
        run.regret Wstar ≤
          (1 / (2 * S.eta)) *
            ∑ t : Fin T,
              (quadraticForm
                  (matrixVec (run.iterate (currentIndex t)) - matrixVec Wstar)
                  (H t) -
                quadraticForm
                  (matrixVec (run.iterate (nextIndex t)) - matrixVec Wstar)
                  (H t)) +
            (S.eta / 2) *
              ∑ t : Fin T, dualQuadraticForm (matrixVec (run.gradientAt t)) (H t) :=
      le_trans hconvRegret hOMD
    let HT : GenericSquare (FlatMatrixIndex m n) :=
      (matrixPower (run.leftAccumulator (finalIndex T)) (1 / 4 : ℝ)
          (run.leftAccumulator_psd (finalIndex T))) ⊗ₖ
        (matrixPower (run.rightAccumulator (finalIndex T)) (1 / 4 : ℝ)
          (run.rightAccumulator_psd (finalIndex T)))
    have hfirst :
        (∑ t : Fin T,
          (quadraticForm
              (matrixVec (run.iterate (currentIndex t)) - matrixVec Wstar)
              (H t) -
            quadraticForm
              (matrixVec (run.iterate (nextIndex t)) - matrixVec Wstar)
              (H t))) ≤
          (run.comparatorRadius Wstar) ^ 2 * genericTrace HT := by
      simpa [H, HT] using
        theorem7_source_first_term_le_radius_sq_trace S run Wstar
    have hdual :
        (∑ t : Fin T, dualQuadraticForm (matrixVec (run.gradientAt t)) (H t)) ≤
          2 * positiveRankReal rankBound * genericTrace HT := by
      simpa [H, HT] using
        theorem7_source_dual_sum_le_rank_trace S run rankBound hrank
    have hfirst_scaled :
        (1 / (2 * S.eta)) *
          (∑ t : Fin T,
            (quadraticForm
                (matrixVec (run.iterate (currentIndex t)) - matrixVec Wstar)
                (H t) -
              quadraticForm
                (matrixVec (run.iterate (nextIndex t)) - matrixVec Wstar)
                (H t))) ≤
          (1 / (2 * S.eta)) *
            ((run.comparatorRadius Wstar) ^ 2 * genericTrace HT) := by
      exact mul_le_mul_of_nonneg_left hfirst
        (div_nonneg zero_le_one (mul_nonneg (by norm_num) (le_of_lt heta_pos)))
    have hdual_scaled :
        (S.eta / 2) *
          (∑ t : Fin T, dualQuadraticForm (matrixVec (run.gradientAt t)) (H t)) ≤
          (S.eta / 2) *
            (2 * positiveRankReal rankBound * genericTrace HT) := by
      exact mul_le_mul_of_nonneg_left hdual
        (div_nonneg (le_of_lt heta_pos) (by norm_num))
    have hsource_eq4 :
        run.regret Wstar ≤
          (((run.comparatorRadius Wstar) ^ 2 / (2 * S.eta) +
              S.eta * positiveRankReal rankBound) * genericTrace HT) := by
      calc
        run.regret Wstar ≤
            (1 / (2 * S.eta)) *
              (∑ t : Fin T,
                (quadraticForm
                    (matrixVec (run.iterate (currentIndex t)) - matrixVec Wstar)
                    (H t) -
                  quadraticForm
                    (matrixVec (run.iterate (nextIndex t)) - matrixVec Wstar)
                    (H t))) +
              (S.eta / 2) *
                (∑ t : Fin T, dualQuadraticForm (matrixVec (run.gradientAt t)) (H t)) :=
            hsource_pre_eq3
        _ ≤
            (1 / (2 * S.eta)) *
              ((run.comparatorRadius Wstar) ^ 2 * genericTrace HT) +
            (S.eta / 2) *
              (2 * positiveRankReal rankBound * genericTrace HT) := by
            exact add_le_add hfirst_scaled hdual_scaled
        _ =
            (((run.comparatorRadius Wstar) ^ 2 / (2 * S.eta) +
                S.eta * positiveRankReal rankBound) * genericTrace HT) := by
            ring
    have hfinish :=
      theorem7_source_eta_kron_trace_finish S run rankBound Wstar heta hDpos
    exact le_trans hsource_eq4 (le_of_eq (by simpa [HT] using hfinish))

private theorem theorem10_source_eta_tensor_trace_finish {k T : Nat}
    (S : TensorAlgorithm2 k T) (run : S.CorrectedRun)
    [Nonempty (Fin k)] [Nonempty (Fin T)]
    (rankBound : Fin k → PosNat) (Wstar : TensorSpace S.dims)
    (heta : S.eta = learningRate (run.comparatorRadius Wstar)
      (TensorAlgorithm2.rankGeometricMean rankBound))
    (hDpos : 0 < run.comparatorRadius Wstar) :
    (((run.comparatorRadius Wstar) ^ 2 / (2 * S.eta) +
        S.eta * TensorAlgorithm2.rankGeometricMean rankBound) *
      genericTrace
        (tensorKronecker (fun i : Fin k =>
          matrixPower (run.accumulator i (finalIndex T))
            (1 / ((2 : ℝ) * (k : ℝ))) (run.accumulator_psd i (finalIndex T))))) =
      Real.sqrt (2 * TensorAlgorithm2.rankGeometricMean rankBound) *
        run.comparatorRadius Wstar *
        (∏ i : Fin k,
          matrixTrace (matrixPower (run.accumulator i (finalIndex T))
            (1 / ((2 : ℝ) * (k : ℝ))) (run.accumulator_psd i (finalIndex T)))) := by
  classical
  let D : ℝ := run.comparatorRadius Wstar
  let r : ℝ := TensorAlgorithm2.rankGeometricMean rankBound
  let Hpow : (i : Fin k) → SquareMatrix (S.dims i) := fun i =>
    matrixPower (run.accumulator i (finalIndex T))
      (1 / ((2 : ℝ) * (k : ℝ))) (run.accumulator_psd i (finalIndex T))
  have hrpos : 0 < r := by
    dsimp [r, TensorAlgorithm2.rankGeometricMean]
    exact Real.rpow_pos_of_pos
      (Finset.prod_pos (fun i _ => positiveRankReal_pos (rankBound i))) _
  have hsqrt_pos : 0 < Real.sqrt (2 * r) := by
    exact Real.sqrt_pos.2 (mul_pos (by norm_num) hrpos)
  have hsqrt_ne : Real.sqrt (2 * r) ≠ 0 := ne_of_gt hsqrt_pos
  have hsqrt_sq : Real.sqrt (2 * r) ^ 2 = 2 * r := by
    exact Real.sq_sqrt (le_of_lt (mul_pos (by norm_num) hrpos))
  have hetaD : S.eta = D / Real.sqrt (2 * r) := by
    simpa [D, r, learningRate] using heta
  have hcoef :
      D ^ 2 / (2 * S.eta) + S.eta * r = Real.sqrt (2 * r) * D := by
    rw [hetaD]
    field_simp [hsqrt_ne]
    nlinarith [hsqrt_sq]
  calc
    (((run.comparatorRadius Wstar) ^ 2 / (2 * S.eta) +
          S.eta * TensorAlgorithm2.rankGeometricMean rankBound) *
        genericTrace (tensorKronecker Hpow))
        = (D ^ 2 / (2 * S.eta) + S.eta * r) *
            (∏ i : Fin k, matrixTrace (Hpow i)) := by
            rw [genericTrace_tensorKronecker_eq_prod_trace Hpow]
    _ = Real.sqrt (2 * r) * D *
          (∏ i : Fin k, matrixTrace (Hpow i)) := by
            rw [hcoef]
    _ = Real.sqrt (2 * TensorAlgorithm2.rankGeometricMean rankBound) *
          run.comparatorRadius Wstar *
          (∏ i : Fin k,
            matrixTrace (matrixPower (run.accumulator i (finalIndex T))
              (1 / ((2 : ℝ) * (k : ℝ))) (run.accumulator_psd i (finalIndex T)))) := by
            simp [D, r, Hpow]

/- Corrected-domain endpoint for Theorem 10. -/
theorem Theorem_10_tensor_regret_corrected_domain (S : TensorAlgorithm2 k T)
    (run : S.CorrectedRun)
    [Nonempty (Fin k)] [Nonempty (Fin T)]
    (rankBound : Fin k → PosNat) (Wstar : TensorSpace S.dims)
    (heta : S.eta = learningRate (run.comparatorRadius Wstar)
      (TensorAlgorithm2.rankGeometricMean rankBound))
    (hrank : ∀ i : Fin k, ∀ t : Fin T,
      (matricization (run.gradientAt t) i).rank ≤ (rankBound i).1) :
    let r : ℝ := TensorAlgorithm2.rankGeometricMean rankBound
    run.regret Wstar ≤
      Real.sqrt (2 * r) * run.comparatorRadius Wstar *
        (∏ i : Fin k,
          matrixTrace (matrixPower (run.accumulator i (finalIndex T))
            (1 / ((2 : ℝ) * (k : ℝ))) (run.accumulator_psd i (finalIndex T)))) := by
  classical
  have hconvRegret :
      run.regret Wstar ≤ ∑ t : Fin T,
        vectorDot ( (run.gradientAt t))
          ( (run.iterate (currentIndex t)) -  Wstar) := by
    let idx : ℕ → Fin T := fun s =>
      if h : s - 1 < T then
        ⟨s - 1, h⟩
      else
        Classical.choice (inferInstance : Nonempty (Fin T))
    let toEuc : (MultiIndex S.dims → ℝ) →
        EuclideanSpace ℝ (MultiIndex S.dims) :=
      (EuclideanSpace.equiv (MultiIndex S.dims) ℝ).symm
    let unvecLin : EuclideanSpace ℝ (MultiIndex S.dims) →ₗ[ℝ]
        TensorSpace S.dims :=
      { toFun := fun v idx => (EuclideanSpace.equiv (MultiIndex S.dims) ℝ v) idx
        map_add' := by
          intro x y
          ext idx
          simp
        map_smul' := by
          intro a x
          ext idx
          simp }
    let lossNat : ℕ → EuclideanSpace ℝ (MultiIndex S.dims) → ℝ :=
      fun s v => S.loss (idx s) (unvecLin v)
    let x : ℕ → EuclideanSpace ℝ (MultiIndex S.dims) :=
      fun s => toEuc ( (run.iterate (currentIndex (idx s))))
    let g : ℕ → EuclideanSpace ℝ (MultiIndex S.dims) :=
      fun s => toEuc ( (run.gradientAt (idx s)))
    let xStar : EuclideanSpace ℝ (MultiIndex S.dims) :=
      toEuc ( Wstar)
    have hconv : ∀ s ∈ Finset.Icc 1 T, ConvexOn ℝ Set.univ (lossNat s) := by
      intro s _hs
      have hcomp := (S.loss_convex (idx s)).comp_linearMap unvecLin
      simpa [lossNat, unvecLin, Function.comp_def] using hcomp
    have hx : ∀ s ∈ Finset.Icc 1 T,
        x s ∈ (Set.univ : Set (EuclideanSpace ℝ (MultiIndex S.dims))) := by
      intro s _hs
      simp
    have hxStar :
        xStar ∈ (Set.univ : Set (EuclideanSpace ℝ (MultiIndex S.dims))) := by
      simp
    have hgrad : ∀ s ∈ Finset.Icc 1 T,
        HasGradientWithinAt (lossNat s) (g s) Set.univ (x s) := by
      intro s _hs
      simpa [lossNat, x, g, toEuc, unvecLin] using
        theorem10_flattened_loss_gradient_bridge S run (idx s)
    have hfinite := finite_horizon_convex_regret_le_gradient_inner_sum
      (F := (Set.univ : Set (EuclideanSpace ℝ (MultiIndex S.dims))))
      (loss := lossNat) (x := x) (g := g) (T := T) (xStar := xStar)
      hconv hx hxStar hgrad
    have hsum_loss_x :
        (∑ s ∈ Finset.Icc 1 T, lossNat s (x s)) =
          ∑ t : Fin T, S.loss t (run.iterate (currentIndex t)) := by
      simpa [lossNat, x, idx, toEuc, unvecLin] using
        (sum_Icc_one_matrix_fin_reindex (T := T)
          (F := fun t : Fin T => S.loss t (run.iterate (currentIndex t))))
    have hsum_loss_star :
        (∑ s ∈ Finset.Icc 1 T, lossNat s xStar) =
          ∑ t : Fin T, S.loss t Wstar := by
      simpa [lossNat, xStar, idx, toEuc, unvecLin] using
        (sum_Icc_one_matrix_fin_reindex (T := T)
          (F := fun t : Fin T => S.loss t Wstar))
    have hleft :
        (∑ s ∈ Finset.Icc 1 T, lossNat s (x s)) -
            (∑ s ∈ Finset.Icc 1 T, lossNat s xStar) =
          run.regret Wstar := by
      rw [hsum_loss_x, hsum_loss_star]
      unfold TensorAlgorithm2.CorrectedRun.regret
      rw [Finset.sum_sub_distrib]
    have hsum_rhs :
        (∑ s ∈ Finset.Icc 1 T, inner ℝ (g s) (x s - xStar)) =
          ∑ t : Fin T,
            vectorDot ( (run.gradientAt t))
              ( (run.iterate (currentIndex t)) -  Wstar) := by
      have hterm :
          (∑ s ∈ Finset.Icc 1 T, inner ℝ (g s) (x s - xStar)) =
            ∑ s ∈ Finset.Icc 1 T,
              vectorDot ( (run.gradientAt (idx s)))
                ( (run.iterate (currentIndex (idx s))) -  Wstar) := by
        apply Finset.sum_congr rfl
        intro s hs
        simpa [g, x, xStar, toEuc] using
          (euclidean_inner_sub_eq_vectorDot
            ( (run.gradientAt (idx s)))
            ( (run.iterate (currentIndex (idx s))))
            ( Wstar))
      rw [hterm]
      simpa [idx] using
        (sum_Icc_one_matrix_fin_reindex (T := T)
          (F := fun t : Fin T =>
            vectorDot ( (run.gradientAt t))
              ( (run.iterate (currentIndex t)) -  Wstar)))
    calc
      run.regret Wstar =
          (∑ s ∈ Finset.Icc 1 T, lossNat s (x s)) -
            (∑ s ∈ Finset.Icc 1 T, lossNat s xStar) := hleft.symm
      _ ≤ ∑ s ∈ Finset.Icc 1 T, inner ℝ (g s) (x s - xStar) := hfinite
      _ = ∑ t : Fin T,
            vectorDot ( (run.gradientAt t))
              ( (run.iterate (currentIndex t)) -  Wstar) := hsum_rhs
  by_cases hD0 : run.comparatorRadius Wstar = 0
  · have hiter : ∀ t : Fin T, run.iterate (currentIndex t) = Wstar := by
      intro t
      have hle :
          tensorFrobeniusNorm (run.iterate (currentIndex t) - Wstar) ≤
            run.comparatorRadius Wstar := by
        dsimp [TensorAlgorithm2.CorrectedRun.comparatorRadius, finiteMax]
        exact Finset.le_sup'
          (fun t : Fin T => tensorFrobeniusNorm (run.iterate (currentIndex t) - Wstar))
          (Finset.mem_univ t)
      have hnorm_le_zero :
          tensorFrobeniusNorm (run.iterate (currentIndex t) - Wstar) ≤ 0 := by
        simpa [hD0] using hle
      have hnorm_eq_zero :
          tensorFrobeniusNorm (run.iterate (currentIndex t) - Wstar) = 0 := by
        have hnonneg :
            0 ≤ tensorFrobeniusNorm (run.iterate (currentIndex t) - Wstar) := by
          unfold tensorFrobeniusNorm
          exact Real.sqrt_nonneg _
        exact le_antisymm hnorm_le_zero hnonneg
      have hsumsq_zero :
          (∑ idx : MultiIndex S.dims,
            (run.iterate (currentIndex t) - Wstar) idx *
              (run.iterate (currentIndex t) - Wstar) idx) = 0 := by
        have hsumsq_nonneg :
            0 ≤ (∑ idx : MultiIndex S.dims,
              (run.iterate (currentIndex t) - Wstar) idx *
                (run.iterate (currentIndex t) - Wstar) idx) := by
          exact Finset.sum_nonneg (by
            intro idx _hidx
            exact mul_self_nonneg _)
        have hsqrt_sq := Real.sq_sqrt hsumsq_nonneg
        have hsqrt_eq :
            Real.sqrt (∑ idx : MultiIndex S.dims,
              (run.iterate (currentIndex t) - Wstar) idx *
                (run.iterate (currentIndex t) - Wstar) idx) = 0 := by
          simpa [tensorFrobeniusNorm] using hnorm_eq_zero
        rw [← hsqrt_sq]
        rw [hsqrt_eq]
        norm_num
      have hentry_zero : ∀ idx : MultiIndex S.dims,
          (run.iterate (currentIndex t) - Wstar) idx = 0 := by
        intro idx
        have hsq_zero :
            (run.iterate (currentIndex t) - Wstar) idx *
              (run.iterate (currentIndex t) - Wstar) idx = 0 := by
          exact (Finset.sum_eq_zero_iff_of_nonneg (by
            intro idx _hidx
            exact mul_self_nonneg _)).mp hsumsq_zero idx (Finset.mem_univ idx)
        exact mul_self_eq_zero.mp hsq_zero
      ext idx
      have h := hentry_zero idx
      simpa using sub_eq_zero.mp h
    have hsum_zero :
        (∑ t : Fin T,
          vectorDot ( (run.gradientAt t))
            ( (run.iterate (currentIndex t)) -  Wstar)) = 0 := by
      simp [hiter, vectorDot]
    have hreg_nonpos : run.regret Wstar ≤ 0 := by
      simpa [hsum_zero] using hconvRegret
    simpa [hD0] using hreg_nonpos
  · have hD_nonneg : 0 ≤ run.comparatorRadius Wstar := by
      let t0 : Fin T := Classical.choice (inferInstance : Nonempty (Fin T))
      have hnorm_nonneg :
          0 ≤ tensorFrobeniusNorm (run.iterate (currentIndex t0) - Wstar) := by
        unfold tensorFrobeniusNorm
        exact Real.sqrt_nonneg _
      have hle :
          tensorFrobeniusNorm (run.iterate (currentIndex t0) - Wstar) ≤
            run.comparatorRadius Wstar := by
        dsimp [TensorAlgorithm2.CorrectedRun.comparatorRadius, finiteMax]
        exact Finset.le_sup'
          (fun t : Fin T => tensorFrobeniusNorm (run.iterate (currentIndex t) - Wstar))
          (Finset.mem_univ t0)
      exact le_trans hnorm_nonneg hle
    have hDpos : 0 < run.comparatorRadius Wstar :=
      lt_of_le_of_ne hD_nonneg (Ne.symm hD0)
    have hr_pos : 0 < TensorAlgorithm2.rankGeometricMean rankBound := by
      dsimp [TensorAlgorithm2.rankGeometricMean]
      exact Real.rpow_pos_of_pos
        (Finset.prod_pos (fun i _ => positiveRankReal_pos (rankBound i))) _
    have heta_pos : 0 < S.eta := by
      rw [heta]
      exact learningRate_pos_of_pos hDpos hr_pos
    let w : Fin (T + 1) → MultiIndex S.dims → ℝ :=
      fun t =>  (run.iterate t)
    let g : Fin T → MultiIndex S.dims → ℝ :=
      fun t =>  (run.gradientAt t)
    let H : Fin T → GenericSquare (MultiIndex S.dims) := fun t =>
      tensorKronecker (fun i : Fin k =>
        matrixPower (run.accumulator i (nextIndex t))
          (1 / ((2 : ℝ) * (k : ℝ))) (run.accumulator_psd i (nextIndex t)))
    let wstar : MultiIndex S.dims → ℝ :=  Wstar
    have hflat := theorem10_source_flat_update_and_pd_preconditioner S run
    have hOMD :
        ∑ t : Fin T, vectorDot ( (run.gradientAt t))
          ( (run.iterate (currentIndex t)) -  Wstar) ≤
          (1 / (2 * S.eta)) *
            ∑ t : Fin T,
              (quadraticForm
                  ( (run.iterate (currentIndex t)) -  Wstar)
                  (H t) -
                quadraticForm
                  ( (run.iterate (nextIndex t)) -  Wstar)
                  (H t)) +
            (S.eta / 2) *
              ∑ t : Fin T, dualQuadraticForm ( (run.gradientAt t)) (H t) := by
      simpa [w, g, H, wstar] using
        (finite_index_adaptive_omd_regret (T := T) (ι := MultiIndex S.dims)
          S.eta heta_pos w g H wstar hflat.2 hflat.1)
    have hsource_pre_eq3 :
        run.regret Wstar ≤
          (1 / (2 * S.eta)) *
            ∑ t : Fin T,
              (quadraticForm
                  ( (run.iterate (currentIndex t)) -  Wstar)
                  (H t) -
                quadraticForm
                  ( (run.iterate (nextIndex t)) -  Wstar)
                  (H t)) +
            (S.eta / 2) *
              ∑ t : Fin T, dualQuadraticForm ( (run.gradientAt t)) (H t) :=
      le_trans hconvRegret hOMD
    let HT : GenericSquare (MultiIndex S.dims) :=
      tensorKronecker (fun i : Fin k =>
        matrixPower (run.accumulator i (finalIndex T))
          (1 / ((2 : ℝ) * (k : ℝ))) (run.accumulator_psd i (finalIndex T)))
    have hFirst :
        (∑ t : Fin T,
          (quadraticForm
              ( (run.iterate (currentIndex t)) -  Wstar)
              (H t) -
            quadraticForm
              ( (run.iterate (nextIndex t)) -  Wstar)
              (H t))) ≤
          (run.comparatorRadius Wstar) ^ 2 * genericTrace HT := by
      simpa [H, HT, finalIndex] using
        theorem10_source_first_term_le_radius_sq_trace S run Wstar
    have hfirst_scaled :
        (1 / (2 * S.eta)) *
            (∑ t : Fin T,
              (quadraticForm
                  ( (run.iterate (currentIndex t)) -  Wstar)
                  (H t) -
                quadraticForm
                  ( (run.iterate (nextIndex t)) -  Wstar)
                  (H t))) ≤
          (1 / (2 * S.eta)) *
            ((run.comparatorRadius Wstar) ^ 2 * genericTrace HT) := by
      have hcoef_nonneg : 0 ≤ 1 / (2 * S.eta) := by
        positivity
      exact mul_le_mul_of_nonneg_left hFirst hcoef_nonneg
    have hsource_after_first :
        run.regret Wstar ≤
          (1 / (2 * S.eta)) *
              ((run.comparatorRadius Wstar) ^ 2 * genericTrace HT) +
            (S.eta / 2) *
              ∑ t : Fin T, dualQuadraticForm ( (run.gradientAt t)) (H t) := by
      exact le_trans hsource_pre_eq3 (add_le_add hfirst_scaled le_rfl)
    have hTraceProduct :
        genericTrace HT =
          ∏ i : Fin k,
            matrixTrace (matrixPower (run.accumulator i (finalIndex T))
              (1 / ((2 : ℝ) * (k : ℝ))) (run.accumulator_psd i (finalIndex T))) := by
      simpa [HT, finalIndex] using
        genericTrace_tensorKronecker_eq_prod_trace
          (fun i : Fin k =>
            matrixPower (run.accumulator i ⟨T, Nat.lt_succ_self T⟩)
              (1 / ((2 : ℝ) * (k : ℝ)))
              (run.accumulator_psd i ⟨T, Nat.lt_succ_self T⟩))
    have hEq5 : ∀ N : Fin (T + 1),
        psdMatrixPower
            (S.epsilon • (1 : GenericSquare (MultiIndex S.dims)) +
              ∑ s : Fin T,
                if s.1 < N.1 then vectorOuter ( (run.gradientAt s)) else 0)
            (1 / 2 : ℝ) (theorem10_hhat_prefix_posSemidef S run N) ≤
          Real.sqrt (TensorAlgorithm2.rankGeometricMean rankBound) •
            tensorKronecker
              (fun i : Fin k =>
                matrixPower (run.accumulator i N)
                  (1 / ((2 : ℝ) * (k : ℝ))) (run.accumulator_psd i N)) := by
      intro N
      exact theorem10_tensor_hhat_order_from_prefix_rank_domination
        S run rankBound hrank N
    let gTensor : Fin T → MultiIndex S.dims → ℝ :=
      fun t =>  (run.gradientAt t)
    let HalgFull : Fin (T + 1) → GenericSquare (MultiIndex S.dims) := fun N =>
      tensorKronecker
        (fun i : Fin k =>
          matrixPower (run.accumulator i N)
            (1 / ((2 : ℝ) * (k : ℝ))) (run.accumulator_psd i N))
    let r : ℝ := TensorAlgorithm2.rankGeometricMean rankBound
    obtain ⟨supportDual, hSupportLimit, _hTraceLimit, hSupportBound⟩ :=
      generic_hhat_positive_delta_range_limit_bound
        (T := T) (ι := MultiIndex S.dims) gTensor S.epsilon_nonneg
    have halpha_nonneg : 0 ≤ Real.sqrt r := by
      positivity
    have hHalg_pd : ∀ t : Fin T, (HalgFull (nextIndex t)).PosDef := by
      intro t
      simpa [HalgFull, H] using hflat.1 t
    have hroot_le : ∀ N : Fin (T + 1),
        psdMatrixPower
            (S.epsilon • (1 : GenericSquare (MultiIndex S.dims)) +
              ∑ s : Fin T,
                if s.1 < N.1 then vectorOuter (gTensor s) else 0)
            (1 / 2 : ℝ) (generic_hhat_prefix_posSemidef gTensor S.epsilon_nonneg N) ≤
          Real.sqrt r • HalgFull N := by
      intro N
      have hpow :
          psdMatrixPower
              (S.epsilon • (1 : GenericSquare (MultiIndex S.dims)) +
                ∑ s : Fin T,
                  if s.1 < N.1 then vectorOuter (gTensor s) else 0)
              (1 / 2 : ℝ) (generic_hhat_prefix_posSemidef gTensor S.epsilon_nonneg N) =
            psdMatrixPower
              (S.epsilon • (1 : GenericSquare (MultiIndex S.dims)) +
                ∑ s : Fin T,
                  if s.1 < N.1 then vectorOuter ( (run.gradientAt s)) else 0)
              (1 / 2 : ℝ) (theorem10_hhat_prefix_posSemidef S run N) := by
        exact psdMatrixPower_congr (by simp [gTensor]) (1 / 2 : ℝ) _ _
      calc
        psdMatrixPower
            (S.epsilon • (1 : GenericSquare (MultiIndex S.dims)) +
              ∑ s : Fin T,
                if s.1 < N.1 then vectorOuter (gTensor s) else 0)
            (1 / 2 : ℝ) (generic_hhat_prefix_posSemidef gTensor S.epsilon_nonneg N) =
            psdMatrixPower
              (S.epsilon • (1 : GenericSquare (MultiIndex S.dims)) +
                ∑ s : Fin T,
                  if s.1 < N.1 then vectorOuter ( (run.gradientAt s)) else 0)
              (1 / 2 : ℝ) (theorem10_hhat_prefix_posSemidef S run N) := hpow
        _ ≤ Real.sqrt r • HalgFull N := by
            simpa [HalgFull, r] using hEq5 N
    have hDualTransfer :
        (∑ t : Fin T, dualQuadraticForm ( (run.gradientAt t)) (H t)) ≤
          Real.sqrt r * ∑ t : Fin T, supportDual t := by
      simpa [gTensor, H, HalgFull, r] using
        generic_algorithm_dual_sum_le_hhat_support_sum
          (T := T) (ι := MultiIndex S.dims) gTensor S.epsilon_nonneg
          HalgFull (Real.sqrt r) halpha_nonneg hHalg_pd hroot_le
          supportDual hSupportLimit
    let HhatT : GenericSquare (MultiIndex S.dims) :=
      psdMatrixPower
        (S.epsilon • (1 : GenericSquare (MultiIndex S.dims)) +
          ∑ s : Fin T,
            if s.1 < (finalIndex T).1 then vectorOuter (gTensor s) else 0)
        (1 / 2 : ℝ)
        (generic_hhat_prefix_posSemidef gTensor S.epsilon_nonneg (finalIndex T))
    have hroot_final : HhatT ≤ Real.sqrt r • HT := by
      have hpow :
          HhatT =
            psdMatrixPower
              (S.epsilon • (1 : GenericSquare (MultiIndex S.dims)) +
                ∑ s : Fin T,
                  if s.1 < (finalIndex T).1 then
                    vectorOuter ( (run.gradientAt s)) else 0)
              (1 / 2 : ℝ) (theorem10_hhat_prefix_posSemidef S run (finalIndex T)) := by
        exact psdMatrixPower_congr (by simp [HhatT, gTensor]) (1 / 2 : ℝ) _ _
      calc
        HhatT =
            psdMatrixPower
              (S.epsilon • (1 : GenericSquare (MultiIndex S.dims)) +
                ∑ s : Fin T,
                  if s.1 < (finalIndex T).1 then
                    vectorOuter ( (run.gradientAt s)) else 0)
              (1 / 2 : ℝ) (theorem10_hhat_prefix_posSemidef S run (finalIndex T)) := hpow
        _ ≤ Real.sqrt r • HT := by
            simpa [HT, HalgFull, r] using hEq5 (finalIndex T)
    have hTrace_le : genericTrace HhatT ≤ Real.sqrt r * genericTrace HT := by
      have hmono : genericTrace HhatT ≤ genericTrace (Real.sqrt r • HT) :=
        genericTrace_mono_of_matrix_le hroot_final
      have htrace_smul :
          genericTrace (Real.sqrt r • HT) = Real.sqrt r * genericTrace HT := by
        simp [genericTrace]
      simpa [htrace_smul] using hmono
    have hScaledSupport :
        Real.sqrt r * (∑ t : Fin T, supportDual t) ≤
          Real.sqrt r * (2 * genericTrace HhatT) :=
      mul_le_mul_of_nonneg_left hSupportBound halpha_nonneg
    have hTraceScaled :
        Real.sqrt r * (2 * genericTrace HhatT) ≤
          Real.sqrt r * (2 * (Real.sqrt r * genericTrace HT)) := by
      have htwo : 0 ≤ (2 : ℝ) := by norm_num
      have hinner :
          2 * genericTrace HhatT ≤ 2 * (Real.sqrt r * genericTrace HT) :=
        mul_le_mul_of_nonneg_left hTrace_le htwo
      exact mul_le_mul_of_nonneg_left hinner halpha_nonneg
    have hsqrt_mul : Real.sqrt r * Real.sqrt r = r := by
      have hsqrt_sq : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt (le_of_lt hr_pos)
      nlinarith
    have hdual :
        (∑ t : Fin T, dualQuadraticForm ( (run.gradientAt t)) (H t)) ≤
          2 * r * genericTrace HT := by
      calc
        (∑ t : Fin T, dualQuadraticForm ( (run.gradientAt t)) (H t)) ≤
            Real.sqrt r * ∑ t : Fin T, supportDual t := hDualTransfer
        _ ≤ Real.sqrt r * (2 * genericTrace HhatT) := hScaledSupport
        _ ≤ Real.sqrt r * (2 * (Real.sqrt r * genericTrace HT)) := hTraceScaled
        _ = 2 * (Real.sqrt r * Real.sqrt r) * genericTrace HT := by
            ring
        _ = 2 * r * genericTrace HT := by
            rw [hsqrt_mul]
    have hdual_scaled :
        (S.eta / 2) *
          (∑ t : Fin T, dualQuadraticForm ( (run.gradientAt t)) (H t)) ≤
          (S.eta / 2) * (2 * r * genericTrace HT) := by
      exact mul_le_mul_of_nonneg_left hdual
        (div_nonneg (le_of_lt heta_pos) (by norm_num))
    have hsource_eq4 :
        run.regret Wstar ≤
          (((run.comparatorRadius Wstar) ^ 2 / (2 * S.eta) +
              S.eta * r) * genericTrace HT) := by
      calc
        run.regret Wstar ≤
            (1 / (2 * S.eta)) *
                ((run.comparatorRadius Wstar) ^ 2 * genericTrace HT) +
              (S.eta / 2) *
                ∑ t : Fin T, dualQuadraticForm ( (run.gradientAt t)) (H t) :=
            hsource_after_first
        _ ≤
            (1 / (2 * S.eta)) *
                ((run.comparatorRadius Wstar) ^ 2 * genericTrace HT) +
              (S.eta / 2) * (2 * r * genericTrace HT) := by
            exact add_le_add le_rfl hdual_scaled
        _ =
            (((run.comparatorRadius Wstar) ^ 2 / (2 * S.eta) +
                S.eta * r) * genericTrace HT) := by
            ring
    have hfinish :=
      theorem10_source_eta_tensor_trace_finish S run rankBound Wstar heta hDpos
    exact le_trans hsource_eq4 (le_of_eq (by simpa [HT, r] using hfinish))

private theorem theorem13_leftAccumulator_current_le_next {T m n : Nat}
    (S : DiagonalAlgorithm3 T m n) (run : S.CorrectedRun) (t : Fin T) :
    run.leftAccumulator (currentIndex t) ≤ run.leftAccumulator (nextIndex t) := by
  classical
  rw [Matrix.le_iff]
  have hstate :
      (run.state (nextIndex t)).L =
        (run.state (currentIndex t)).L +
          diagonalPart (matrixGramLeft (run.gradientAt t)) := by
    have hL := congrArg SOptLib.TwoSidedMatrixPreconditionerState.L (run.step t)
    simpa [DiagonalAlgorithm3.stepState, matrixGramLeft] using hL
  have hgram : (diagonalPart (matrixGramLeft (run.gradientAt t))).PosSemidef := by
    exact diagonalPart_posSemidef_of_posSemidef
      (by
        simpa [matrixGramLeft] using
          (Matrix.PosSemidef.one.mul_mul_conjTranspose_same (B := run.gradientAt t)))
  change
    (run.leftAccumulator (nextIndex t) -
        run.leftAccumulator (currentIndex t)).PosSemidef
  simpa [DiagonalAlgorithm3.CorrectedRun.leftAccumulator, hstate] using hgram

private theorem theorem13_rightAccumulator_current_le_next {T m n : Nat}
    (S : DiagonalAlgorithm3 T m n) (run : S.CorrectedRun) (t : Fin T) :
    run.rightAccumulator (currentIndex t) ≤ run.rightAccumulator (nextIndex t) := by
  classical
  rw [Matrix.le_iff]
  have hstate :
      (run.state (nextIndex t)).R =
        (run.state (currentIndex t)).R +
          diagonalPart (matrixGramRight (run.gradientAt t)) := by
    have hR := congrArg SOptLib.TwoSidedMatrixPreconditionerState.R (run.step t)
    simpa [DiagonalAlgorithm3.stepState, matrixGramRight] using hR
  have hgram : (diagonalPart (matrixGramRight (run.gradientAt t))).PosSemidef := by
    exact diagonalPart_posSemidef_of_posSemidef
      (by
        simpa [matrixGramRight] using
          (Matrix.PosSemidef.one.conjTranspose_mul_mul_same (B := run.gradientAt t)))
  change
    (run.rightAccumulator (nextIndex t) -
        run.rightAccumulator (currentIndex t)).PosSemidef
  simpa [DiagonalAlgorithm3.CorrectedRun.rightAccumulator, hstate] using hgram

private theorem theorem13_diagonal_leftAccumulator_eq_prefix_sum {T m n : Nat}
    (S : DiagonalAlgorithm3 T m n) (run : S.CorrectedRun) (N : Fin (T + 1)) :
    run.leftAccumulator N =
      S.epsilon • (1 : SquareMatrix m) +
        ∑ s : Fin T,
          if s.1 < N.1 then diagonalPart (matrixGramLeft (run.gradientAt s)) else 0 := by
  classical
  induction N using Fin.induction with
  | zero =>
      change (run.state ⟨0, Nat.succ_pos T⟩).L =
        S.epsilon • (1 : SquareMatrix m) +
          ∑ s : Fin T,
            if s.1 < 0 then diagonalPart (matrixGramLeft (run.gradientAt s)) else 0
      rw [run.initial]
      simp [DiagonalAlgorithm3.initialState]
  | succ t ih =>
      have hstep :
          (run.state (nextIndex t)).L =
            (run.state (currentIndex t)).L +
              diagonalPart (matrixGramLeft (run.gradientAt t)) := by
        rw [run.step t]
        simp [DiagonalAlgorithm3.stepState]
      have hsum :=
        fin_prefix_sum_succ_addCommMonoid
          (fun s : Fin T => diagonalPart (matrixGramLeft (run.gradientAt s))) t.2
      change (run.state (nextIndex t)).L =
        S.epsilon • (1 : SquareMatrix m) +
          ∑ s : Fin T,
            if s.1 < t.1 + 1 then
              diagonalPart (matrixGramLeft (run.gradientAt s)) else 0
      rw [hstep]
      rw [hsum]
      change
        (run.state (currentIndex t)).L +
            diagonalPart (matrixGramLeft (run.gradientAt t)) =
          S.epsilon • (1 : SquareMatrix m) +
            ((∑ s : Fin T,
                if s.1 < t.1 then
                  diagonalPart (matrixGramLeft (run.gradientAt s)) else 0) +
              diagonalPart (matrixGramLeft (run.gradientAt t)))
      have hih :
          (run.state (currentIndex t)).L =
            S.epsilon • (1 : SquareMatrix m) +
              ∑ s : Fin T,
                if s.1 < t.1 then
                  diagonalPart (matrixGramLeft (run.gradientAt s)) else 0 := by
        simpa [DiagonalAlgorithm3.CorrectedRun.leftAccumulator, currentIndex] using ih
      rw [hih]
      abel

private theorem theorem13_diagonal_rightAccumulator_eq_prefix_sum {T m n : Nat}
    (S : DiagonalAlgorithm3 T m n) (run : S.CorrectedRun) (N : Fin (T + 1)) :
    run.rightAccumulator N =
      S.epsilon • (1 : SquareMatrix n) +
        ∑ s : Fin T,
          if s.1 < N.1 then diagonalPart (matrixGramRight (run.gradientAt s)) else 0 := by
  classical
  induction N using Fin.induction with
  | zero =>
      change (run.state ⟨0, Nat.succ_pos T⟩).R =
        S.epsilon • (1 : SquareMatrix n) +
          ∑ s : Fin T,
            if s.1 < 0 then diagonalPart (matrixGramRight (run.gradientAt s)) else 0
      rw [run.initial]
      simp [DiagonalAlgorithm3.initialState]
  | succ t ih =>
      have hstep :
          (run.state (nextIndex t)).R =
            (run.state (currentIndex t)).R +
              diagonalPart (matrixGramRight (run.gradientAt t)) := by
        rw [run.step t]
        simp [DiagonalAlgorithm3.stepState]
      have hsum :=
        fin_prefix_sum_succ_addCommMonoid
          (fun s : Fin T => diagonalPart (matrixGramRight (run.gradientAt s))) t.2
      change (run.state (nextIndex t)).R =
        S.epsilon • (1 : SquareMatrix n) +
          ∑ s : Fin T,
            if s.1 < t.1 + 1 then
              diagonalPart (matrixGramRight (run.gradientAt s)) else 0
      rw [hstep]
      rw [hsum]
      change
        (run.state (currentIndex t)).R +
            diagonalPart (matrixGramRight (run.gradientAt t)) =
          S.epsilon • (1 : SquareMatrix n) +
            ((∑ s : Fin T,
                if s.1 < t.1 then
                  diagonalPart (matrixGramRight (run.gradientAt s)) else 0) +
              diagonalPart (matrixGramRight (run.gradientAt t)))
      have hih :
          (run.state (currentIndex t)).R =
            S.epsilon • (1 : SquareMatrix n) +
              ∑ s : Fin T,
                if s.1 < t.1 then
                  diagonalPart (matrixGramRight (run.gradientAt s)) else 0 := by
        simpa [DiagonalAlgorithm3.CorrectedRun.rightAccumulator, currentIndex] using ih
      rw [hih]
      abel

private theorem generic_diagonal_of_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : GenericSquare ι} (hA : A.PosSemidef) :
    (Matrix.diagonal (fun i : ι => A i i) : GenericSquare ι).PosSemidef := by
  exact Matrix.PosSemidef.diagonal (fun i => Matrix.PosSemidef.diag_nonneg hA (i := i))

private theorem generic_diagonal_mono_of_matrix_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : GenericSquare ι} (hAB : A ≤ B) :
    (Matrix.diagonal (fun i : ι => A i i) : GenericSquare ι) ≤
      Matrix.diagonal (fun i : ι => B i i) := by
  simpa [Matrix.diagonalPart] using Matrix.diagonalPart_mono hAB

private theorem generic_diagonal_smul_entries {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ℝ) (A : GenericSquare ι) :
    (Matrix.diagonal (fun i : ι => (r • A) i i) : GenericSquare ι) =
      r • Matrix.diagonal (fun i : ι => A i i) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · simp [Matrix.diagonal_apply, hij]

private theorem diagonal_kronecker_eq_kronecker_diagonal_entries {m n : Nat}
    (A : SquareMatrix m) (B : SquareMatrix n) :
    (Matrix.diagonal (fun ij : FlatMatrixIndex m n => (A ⊗ₖ B) ij ij) :
        GenericSquare (FlatMatrixIndex m n)) =
      Matrix.diagonal (fun i : Fin m => A i i) ⊗ₖ
        Matrix.diagonal (fun j : Fin n => B j j) := by
  exact Matrix.diagonal_kroneckerMap_eq_kroneckerMap_diagonal A B

private theorem diagonal_of_psd_half_power_le_half_power_diagonal {n : Nat}
    (A : SquareMatrix n) (hA : A.PosSemidef)
    (hDiag : (Matrix.diagonal (fun i : Fin n => A i i) : SquareMatrix n).PosSemidef) :
    (Matrix.diagonal (fun i : Fin n => (matrixPower A (1 / 2 : ℝ) hA) i i) :
        SquareMatrix n) ≤
      matrixPower (Matrix.diagonal (fun i : Fin n => A i i) : SquareMatrix n)
        (1 / 2 : ℝ) hDiag := by
  simpa only [matrixPower, psdMatrixPower_eq_cfc,
    ← CFC.rpow_eq_cfc_real hA.nonneg, ← CFC.rpow_eq_cfc_real hDiag.nonneg,
    ← CFC.sqrt_eq_rpow] using
      Matrix.diagonal_cfc_sqrt_le_cfc_sqrt_diagonal A hA

private noncomputable def theorem13_diagonal_hhat_prefix_base {T m n : Nat}
    (S : DiagonalAlgorithm3 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat) (N : Fin (T + 1)) :
    GenericSquare (FlatMatrixIndex m n) :=
  Matrix.diagonal (fun ij : FlatMatrixIndex m n =>
    ((positiveRankReal rankBound * S.epsilon) •
        (1 : GenericSquare (FlatMatrixIndex m n)) +
      ∑ s : Fin T,
        if s.1 < N.1 then vectorOuter (matrixVec (run.gradientAt s)) else 0) ij ij)

private theorem theorem13_diagonal_hhat_prefix_posSemidef {T m n : Nat}
    (S : DiagonalAlgorithm3 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat) (N : Fin (T + 1)) :
    (theorem13_diagonal_hhat_prefix_base S run rankBound N).PosSemidef := by
  classical
  have heps : 0 ≤ positiveRankReal rankBound * S.epsilon :=
    mul_nonneg (le_of_lt (positiveRankReal_pos rankBound)) S.epsilon_nonneg
  have hfull :
      ((positiveRankReal rankBound * S.epsilon) •
          (1 : GenericSquare (FlatMatrixIndex m n)) +
        ∑ s : Fin T,
          if s.1 < N.1 then vectorOuter (matrixVec (run.gradientAt s)) else 0).PosSemidef :=
    generic_hhat_prefix_posSemidef
      (T := T) (ι := FlatMatrixIndex m n)
      (fun s : Fin T => matrixVec (run.gradientAt s)) heps N
  simpa [theorem13_diagonal_hhat_prefix_base] using
    generic_diagonal_of_posSemidef hfull

private noncomputable def theorem13_diagonal_hhat_prefix {T m n : Nat}
    (S : DiagonalAlgorithm3 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat) (N : Fin (T + 1)) :
    GenericSquare (FlatMatrixIndex m n) :=
  psdMatrixPower (theorem13_diagonal_hhat_prefix_base S run rankBound N)
    (1 / 2 : ℝ) (theorem13_diagonal_hhat_prefix_posSemidef S run rankBound N)

private theorem theorem13_diagonal_hhat_base_le_rank_algorithm_half {T m n : Nat}
    (S : DiagonalAlgorithm3 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat)
    (hrank : ∀ t : Fin T, (run.gradientAt t).rank ≤ rankBound.1)
    (N : Fin (T + 1)) :
    theorem13_diagonal_hhat_prefix_base S run rankBound N ≤
      positiveRankReal rankBound •
        ((matrixPower (run.leftAccumulator N) (1 / 2 : ℝ)
            (run.leftAccumulator_psd N)) ⊗ₖ
          (matrixPower (run.rightAccumulator N) (1 / 2 : ℝ)
            (run.rightAccumulator_psd N))) := by
  classical
  let Gmask : Fin T → MatrixSpace m n :=
    fun s => if s.1 < N.1 then run.gradientAt s else 0
  have hrankMask : ∀ t : Fin T, (Gmask t).rank ≤ rankBound.1 := by
    intro t
    by_cases ht : t.1 < N.1
    · simpa [Gmask, ht] using hrank t
    · have hzero : (Gmask t).rank = 0 := by
        simp [Gmask, ht, Matrix.rank_zero]
      rw [hzero]
      exact Nat.zero_le rankBound.1
  have hVecMask :
      (∑ s : Fin T, vectorOuter (matrixVec (Gmask s))) =
        ∑ s : Fin T,
          if s.1 < N.1 then vectorOuter (matrixVec (run.gradientAt s)) else 0 := by
    refine Finset.sum_congr rfl ?_
    intro s _hs
    by_cases ht : s.1 < N.1
    · simp [Gmask, ht]
    · ext i j
      simp [Gmask, ht, matrixVec, vectorOuter]
  have hLeftMask :
      (∑ s : Fin T, diagonalPart (matrixGramLeft (Gmask s))) =
        ∑ s : Fin T,
          if s.1 < N.1 then diagonalPart (matrixGramLeft (run.gradientAt s)) else 0 := by
    refine Finset.sum_congr rfl ?_
    intro s _hs
    by_cases ht : s.1 < N.1
    · simp [Gmask, ht]
    · simp [Gmask, ht, diagonalPart, matrixGramLeft, Matrix.mul_apply]
  have hRightMask :
      (∑ s : Fin T, diagonalPart (matrixGramRight (Gmask s))) =
        ∑ s : Fin T,
          if s.1 < N.1 then diagonalPart (matrixGramRight (run.gradientAt s)) else 0 := by
    refine Finset.sum_congr rfl ?_
    intro s _hs
    by_cases ht : s.1 < N.1
    · simp [Gmask, ht]
    · simp [Gmask, ht, diagonalPart, matrixGramRight, Matrix.mul_apply]
  have hLeftAccDiag :
      S.epsilon • (1 : SquareMatrix m) +
          ∑ s : Fin T, diagonalPart (matrixGramLeft (Gmask s)) =
        run.leftAccumulator N := by
    rw [hLeftMask]
    exact (theorem13_diagonal_leftAccumulator_eq_prefix_sum S run N).symm
  have hRightAccDiag :
      S.epsilon • (1 : SquareMatrix n) +
          ∑ s : Fin T, diagonalPart (matrixGramRight (Gmask s)) =
        run.rightAccumulator N := by
    rw [hRightMask]
    exact (theorem13_diagonal_rightAccumulator_eq_prefix_sum S run N).symm
  have hLemma8 :=
    Lemma_8_matrix_rank_domination Gmask rankBound S.epsilon hrankMask S.epsilon_nonneg
  have hLemma8_prefix :
      S.epsilon • (1 : GenericSquare (FlatMatrixIndex m n)) +
          (1 / positiveRankReal rankBound) •
            (∑ s : Fin T,
              if s.1 < N.1 then vectorOuter (matrixVec (run.gradientAt s)) else 0) ≤
        (matrixPower
            (S.epsilon • (1 : SquareMatrix m) +
              ∑ s : Fin T, matrixGramLeft (Gmask s))
            (1 / 2 : ℝ) (accumulated_matrix_left_psd_from_epsilon
              Gmask S.epsilon S.epsilon_nonneg) ⊗ₖ
          matrixPower
            (S.epsilon • (1 : SquareMatrix n) +
              ∑ s : Fin T, matrixGramRight (Gmask s))
            (1 / 2 : ℝ) (accumulated_matrix_right_psd_from_epsilon
              Gmask S.epsilon S.epsilon_nonneg)) := by
    simpa [hVecMask] using hLemma8
  have hsource_diagonal_bridge :
      theorem13_diagonal_hhat_prefix_base S run rankBound N ≤
        positiveRankReal rankBound •
          ((matrixPower (run.leftAccumulator N) (1 / 2 : ℝ)
              (run.leftAccumulator_psd N)) ⊗ₖ
            (matrixPower (run.rightAccumulator N) (1 / 2 : ℝ)
              (run.rightAccumulator_psd N))) := by
    let r : ℝ := positiveRankReal rankBound
    let M : GenericSquare (FlatMatrixIndex m n) :=
      ∑ s : Fin T,
        if s.1 < N.1 then vectorOuter (matrixVec (run.gradientAt s)) else 0
    let base : GenericSquare (FlatMatrixIndex m n) :=
      S.epsilon • (1 : GenericSquare (FlatMatrixIndex m n)) + (1 / r) • M
    let Lbase : SquareMatrix m :=
      S.epsilon • (1 : SquareMatrix m) + ∑ s : Fin T, matrixGramLeft (Gmask s)
    let Rbase : SquareMatrix n :=
      S.epsilon • (1 : SquareMatrix n) + ∑ s : Fin T, matrixGramRight (Gmask s)
    let Lhalf : SquareMatrix m :=
      matrixPower Lbase (1 / 2 : ℝ)
        (accumulated_matrix_left_psd_from_epsilon Gmask S.epsilon S.epsilon_nonneg)
    let Rhalf : SquareMatrix n :=
      matrixPower Rbase (1 / 2 : ℝ)
        (accumulated_matrix_right_psd_from_epsilon Gmask S.epsilon S.epsilon_nonneg)
    let Kfull : GenericSquare (FlatMatrixIndex m n) := Lhalf ⊗ₖ Rhalf
    let Lalg : SquareMatrix m :=
      matrixPower (run.leftAccumulator N) (1 / 2 : ℝ) (run.leftAccumulator_psd N)
    let Ralg : SquareMatrix n :=
      matrixPower (run.rightAccumulator N) (1 / 2 : ℝ) (run.rightAccumulator_psd N)
    have hrpos : 0 < r := by
      simpa [r] using positiveRankReal_pos rankBound
    have hrnonneg : 0 ≤ r := le_of_lt hrpos
    have hprefix : base ≤ Kfull := by
      simpa [base, Kfull, Lbase, Rbase, Lhalf, Rhalf, M, r] using hLemma8_prefix
    have hscaled : r • base ≤ r • Kfull :=
      smul_le_smul_of_nonneg_left hprefix hrnonneg
    have hscaled_left :
        r • base =
          (r * S.epsilon) • (1 : GenericSquare (FlatMatrixIndex m n)) + M := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [base, M, one_div, smul_add, smul_smul, Matrix.one_apply, hrpos.ne']
        field_simp [hrpos.ne']
      · simp [base, M, one_div, smul_add, smul_smul, Matrix.one_apply, hij, hrpos.ne']
    have hraw_le :
        ((positiveRankReal rankBound * S.epsilon) •
            (1 : GenericSquare (FlatMatrixIndex m n)) + M) ≤ r • Kfull := by
      simpa [r] using hscaled_left ▸ hscaled
    have hdiag_from_lemma8 :
        theorem13_diagonal_hhat_prefix_base S run rankBound N ≤
          Matrix.diagonal (fun ij : FlatMatrixIndex m n => (r • Kfull) ij ij) := by
      simpa [theorem13_diagonal_hhat_prefix_base, M, r] using
        generic_diagonal_mono_of_matrix_le hraw_le
    have hLbase_psd :
        Lbase.PosSemidef := by
      simpa [Lbase] using
        accumulated_matrix_left_psd_from_epsilon Gmask S.epsilon S.epsilon_nonneg
    have hRbase_psd :
        Rbase.PosSemidef := by
      simpa [Rbase] using
        accumulated_matrix_right_psd_from_epsilon Gmask S.epsilon S.epsilon_nonneg
    have hLdiag_psd :
        (Matrix.diagonal (fun i : Fin m => Lbase i i) : SquareMatrix m).PosSemidef := by
      simpa using generic_diagonal_of_posSemidef (A := Lbase) hLbase_psd
    have hRdiag_psd :
        (Matrix.diagonal (fun i : Fin n => Rbase i i) : SquareMatrix n).PosSemidef := by
      simpa using generic_diagonal_of_posSemidef (A := Rbase) hRbase_psd
    have hLdiag_eq :
        (Matrix.diagonal (fun i : Fin m => Lbase i i) : SquareMatrix m) =
          run.leftAccumulator N := by
      rw [← hLeftAccDiag]
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Lbase, diagonalPart, Matrix.diagonal_apply, Matrix.sum_apply]
      · simp [Lbase, diagonalPart, Matrix.diagonal_apply, Matrix.sum_apply, hij]
    have hRdiag_eq :
        (Matrix.diagonal (fun i : Fin n => Rbase i i) : SquareMatrix n) =
          run.rightAccumulator N := by
      rw [← hRightAccDiag]
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Rbase, diagonalPart, Matrix.diagonal_apply, Matrix.sum_apply]
      · simp [Rbase, diagonalPart, Matrix.diagonal_apply, Matrix.sum_apply, hij]
    have hLsqrt_le :
        (Matrix.diagonal (fun i : Fin m => Lhalf i i) : SquareMatrix m) ≤ Lalg := by
      have hraw :=
        diagonal_of_psd_half_power_le_half_power_diagonal Lbase hLbase_psd hLdiag_psd
      have hpow :
          matrixPower (Matrix.diagonal (fun i : Fin m => Lbase i i) : SquareMatrix m)
              (1 / 2 : ℝ) hLdiag_psd =
            Lalg := by
        simpa [matrixPower, Lalg] using
          psdMatrixPower_congr hLdiag_eq (1 / 2 : ℝ) hLdiag_psd
            (run.leftAccumulator_psd N)
      calc
        (Matrix.diagonal (fun i : Fin m => Lhalf i i) : SquareMatrix m) ≤
            matrixPower
              (Matrix.diagonal (fun i : Fin m => Lbase i i) : SquareMatrix m)
              (1 / 2 : ℝ) hLdiag_psd := by
              simpa [Lhalf, Lbase] using hraw
        _ = Lalg := hpow
    have hRsqrt_le :
        (Matrix.diagonal (fun i : Fin n => Rhalf i i) : SquareMatrix n) ≤ Ralg := by
      have hraw :=
        diagonal_of_psd_half_power_le_half_power_diagonal Rbase hRbase_psd hRdiag_psd
      have hpow :
          matrixPower (Matrix.diagonal (fun i : Fin n => Rbase i i) : SquareMatrix n)
              (1 / 2 : ℝ) hRdiag_psd =
            Ralg := by
        simpa [matrixPower, Ralg] using
          psdMatrixPower_congr hRdiag_eq (1 / 2 : ℝ) hRdiag_psd
            (run.rightAccumulator_psd N)
      calc
        (Matrix.diagonal (fun i : Fin n => Rhalf i i) : SquareMatrix n) ≤
            matrixPower
              (Matrix.diagonal (fun i : Fin n => Rbase i i) : SquareMatrix n)
              (1 / 2 : ℝ) hRdiag_psd := by
              simpa [Rhalf, Rbase] using hraw
        _ = Ralg := hpow
    have hLdiag_half_psd :
        (Matrix.diagonal (fun i : Fin m => Lhalf i i) : SquareMatrix m).PosSemidef := by
      have hLhalf_psd : Lhalf.PosSemidef := by
        simpa [Lhalf, Lbase] using
          matrixPower_posSemidef Lbase (1 / 2 : ℝ) hLbase_psd
      simpa using generic_diagonal_of_posSemidef (A := Lhalf) hLhalf_psd
    have hRdiag_half_psd :
        (Matrix.diagonal (fun i : Fin n => Rhalf i i) : SquareMatrix n).PosSemidef := by
      have hRhalf_psd : Rhalf.PosSemidef := by
        simpa [Rhalf, Rbase] using
          matrixPower_posSemidef Rbase (1 / 2 : ℝ) hRbase_psd
      simpa using generic_diagonal_of_posSemidef (A := Rhalf) hRhalf_psd
    have hdiagK_le :
        (Matrix.diagonal (fun ij : FlatMatrixIndex m n => Kfull ij ij) :
            GenericSquare (FlatMatrixIndex m n)) ≤
          Lalg ⊗ₖ Ralg := by
      calc
        (Matrix.diagonal (fun ij : FlatMatrixIndex m n => Kfull ij ij) :
            GenericSquare (FlatMatrixIndex m n)) =
            Matrix.diagonal (fun i : Fin m => Lhalf i i) ⊗ₖ
              Matrix.diagonal (fun j : Fin n => Rhalf j j) := by
              simpa [Kfull] using
                diagonal_kronecker_eq_kronecker_diagonal_entries Lhalf Rhalf
        _ ≤ Lalg ⊗ₖ Ralg := by
              exact Lemma_3_iv_kron_order_preserving Lalg
                (Matrix.diagonal (fun i : Fin m => Lhalf i i))
                Ralg (Matrix.diagonal (fun j : Fin n => Rhalf j j))
                hLdiag_half_psd hRdiag_half_psd hLsqrt_le hRsqrt_le
    have hdiag_scaled_le :
        Matrix.diagonal (fun ij : FlatMatrixIndex m n => (r • Kfull) ij ij) ≤
          r • (Lalg ⊗ₖ Ralg) := by
      calc
        Matrix.diagonal (fun ij : FlatMatrixIndex m n => (r • Kfull) ij ij) =
            r • Matrix.diagonal (fun ij : FlatMatrixIndex m n => Kfull ij ij) := by
              exact generic_diagonal_smul_entries r Kfull
        _ ≤ r • (Lalg ⊗ₖ Ralg) := by
              exact smul_le_smul_of_nonneg_left hdiagK_le hrnonneg
    exact le_trans hdiag_from_lemma8 (by
      simpa [Lalg, Ralg, r] using hdiag_scaled_le)
  exact hsource_diagonal_bridge

private theorem theorem13_diagonal_hhat_order_from_prefix_rank_domination {T m n : Nat}
    (S : DiagonalAlgorithm3 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat)
    (hrank : ∀ t : Fin T, (run.gradientAt t).rank ≤ rankBound.1)
    (N : Fin (T + 1)) :
    theorem13_diagonal_hhat_prefix S run rankBound N ≤
      Real.sqrt (positiveRankReal rankBound) •
        ((matrixPower (run.leftAccumulator N) (1 / 4 : ℝ)
            (run.leftAccumulator_psd N)) ⊗ₖ
          (matrixPower (run.rightAccumulator N) (1 / 4 : ℝ)
            (run.rightAccumulator_psd N))) := by
  classical
  let r : ℝ := positiveRankReal rankBound
  let Dbase : GenericSquare (FlatMatrixIndex m n) :=
    theorem13_diagonal_hhat_prefix_base S run rankBound N
  let full : GenericSquare (FlatMatrixIndex m n) :=
    (matrixPower (run.leftAccumulator N) (1 / 2 : ℝ)
        (run.leftAccumulator_psd N)) ⊗ₖ
      (matrixPower (run.rightAccumulator N) (1 / 2 : ℝ)
        (run.rightAccumulator_psd N))
  let H : GenericSquare (FlatMatrixIndex m n) :=
    (matrixPower (run.leftAccumulator N) (1 / 4 : ℝ)
        (run.leftAccumulator_psd N)) ⊗ₖ
      (matrixPower (run.rightAccumulator N) (1 / 4 : ℝ)
        (run.rightAccumulator_psd N))
  have hrpos : 0 < r := by
    simpa [r] using positiveRankReal_pos rankBound
  have hrnonneg : 0 ≤ r := le_of_lt hrpos
  have hDbase_psd : Dbase.PosSemidef := by
    simpa [Dbase] using theorem13_diagonal_hhat_prefix_posSemidef S run rankBound N
  have hLhalf_psd :
      (matrixPower (run.leftAccumulator N) (1 / 2 : ℝ)
        (run.leftAccumulator_psd N)).PosSemidef :=
    matrixPower_posSemidef (run.leftAccumulator N) (1 / 2 : ℝ)
      (run.leftAccumulator_psd N)
  have hRhalf_psd :
      (matrixPower (run.rightAccumulator N) (1 / 2 : ℝ)
        (run.rightAccumulator_psd N)).PosSemidef :=
    matrixPower_posSemidef (run.rightAccumulator N) (1 / 2 : ℝ)
      (run.rightAccumulator_psd N)
  have hfull_psd : full.PosSemidef := by
    simpa [full] using
      Lemma_3_iv_kron_psd
        (matrixPower (run.leftAccumulator N) (1 / 2 : ℝ)
          (run.leftAccumulator_psd N))
        (matrixPower (run.rightAccumulator N) (1 / 2 : ℝ)
          (run.rightAccumulator_psd N))
        hLhalf_psd hRhalf_psd
  have hscaled_psd : (r • full).PosSemidef :=
    hfull_psd.smul hrnonneg
  have hbase_le : Dbase ≤ r • full := by
    simpa [Dbase, full, r] using
      theorem13_diagonal_hhat_base_le_rank_algorithm_half S run rankBound hrank N
  have hroot_raw :
      psdMatrixPower Dbase (1 / 2 : ℝ) hDbase_psd ≤
        psdMatrixPower (r • full) (1 / 2 : ℝ) hscaled_psd := by
    exact generic_operator_monotone_powers Dbase (r • full) (1 / 2 : ℝ)
      hDbase_psd hscaled_psd hbase_le (by norm_num) (by norm_num)
  have hfull_half_to_H :
      psdMatrixPower full (1 / 2 : ℝ) hfull_psd = H := by
    let Lhalf : SquareMatrix m :=
      matrixPower (run.leftAccumulator N) (1 / 2 : ℝ)
        (run.leftAccumulator_psd N)
    let Rhalf : SquareMatrix n :=
      matrixPower (run.rightAccumulator N) (1 / 2 : ℝ)
        (run.rightAccumulator_psd N)
    let Lquarter : SquareMatrix m :=
      matrixPower (run.leftAccumulator N) (1 / 4 : ℝ)
        (run.leftAccumulator_psd N)
    let Rquarter : SquareMatrix n :=
      matrixPower (run.rightAccumulator N) (1 / 4 : ℝ)
        (run.rightAccumulator_psd N)
    have hpow_kron :
        psdMatrixPower full (1 / 2 : ℝ) hfull_psd =
          matrixPower Lhalf (1 / 2 : ℝ) hLhalf_psd ⊗ₖ
            matrixPower Rhalf (1 / 2 : ℝ) hRhalf_psd := by
      have hkron_psd :
          (Lhalf ⊗ₖ Rhalf).PosSemidef :=
        Lemma_3_iv_kron_psd Lhalf Rhalf hLhalf_psd hRhalf_psd
      calc
        psdMatrixPower full (1 / 2 : ℝ) hfull_psd =
            psdMatrixPower (Lhalf ⊗ₖ Rhalf) (1 / 2 : ℝ) hkron_psd := by
              have hfull_eq : full = Lhalf ⊗ₖ Rhalf := by
                rfl
              exact psdMatrixPower_congr hfull_eq (1 / 2 : ℝ) hfull_psd hkron_psd
        _ = matrixPower Lhalf (1 / 2 : ℝ) hLhalf_psd ⊗ₖ
              matrixPower Rhalf (1 / 2 : ℝ) hRhalf_psd := by
              exact psdMatrixPower_kronecker Lhalf Rhalf (1 / 2 : ℝ)
                hLhalf_psd hRhalf_psd
    have hLquarter :
        matrixPower Lhalf (1 / 2 : ℝ) hLhalf_psd = Lquarter := by
      simpa [matrixPower, Lhalf, Lquarter] using
        psdMatrixPower_half_half_eq_quarter
          (run.leftAccumulator N) (run.leftAccumulator_psd N) hLhalf_psd
    have hRquarter :
        matrixPower Rhalf (1 / 2 : ℝ) hRhalf_psd = Rquarter := by
      simpa [matrixPower, Rhalf, Rquarter] using
        psdMatrixPower_half_half_eq_quarter
          (run.rightAccumulator N) (run.rightAccumulator_psd N) hRhalf_psd
    calc
      psdMatrixPower full (1 / 2 : ℝ) hfull_psd =
          matrixPower Lhalf (1 / 2 : ℝ) hLhalf_psd ⊗ₖ
            matrixPower Rhalf (1 / 2 : ℝ) hRhalf_psd := hpow_kron
      _ = Lquarter ⊗ₖ Rquarter := by
          rw [hLquarter, hRquarter]
      _ = H := by
          rfl
  calc
    theorem13_diagonal_hhat_prefix S run rankBound N =
        psdMatrixPower Dbase (1 / 2 : ℝ) hDbase_psd := by
          exact psdMatrixPower_congr (by simp [Dbase]) (1 / 2 : ℝ)
            (theorem13_diagonal_hhat_prefix_posSemidef S run rankBound N) hDbase_psd
    _ ≤ psdMatrixPower (r • full) (1 / 2 : ℝ) hscaled_psd := hroot_raw
    _ = Real.sqrt r • H := by
      calc
        psdMatrixPower (r • full) (1 / 2 : ℝ) hscaled_psd =
            r ^ (1 / 2 : ℝ) • psdMatrixPower full (1 / 2 : ℝ) hfull_psd := by
              exact psdMatrixPower_smul_nonneg r (1 / 2 : ℝ) full hfull_psd
                hrnonneg hscaled_psd
        _ = Real.sqrt r • H := by
              rw [hfull_half_to_H]
              simp [Real.sqrt_eq_rpow]
    _ = Real.sqrt (positiveRankReal rankBound) •
        ((matrixPower (run.leftAccumulator N) (1 / 4 : ℝ)
            (run.leftAccumulator_psd N)) ⊗ₖ
          (matrixPower (run.rightAccumulator N) (1 / 4 : ℝ)
            (run.rightAccumulator_psd N))) := by
      simp [H, r]

private theorem theorem13_leftAccumulator_eq_diagonal_diag {T m n : Nat}
    (S : DiagonalAlgorithm3 T m n) (run : S.CorrectedRun) (u : Fin (T + 1)) :
    run.leftAccumulator u =
      Matrix.diagonal (fun i : Fin m => run.leftAccumulator u i i) := by
  classical
  induction u using Fin.induction with
  | zero =>
      change (run.state ⟨0, Nat.succ_pos T⟩).L =
        Matrix.diagonal (fun i : Fin m => (run.state ⟨0, Nat.succ_pos T⟩).L i i)
      rw [run.initial]
      ext i j
      by_cases hij : i = j
      · subst j
        simp [DiagonalAlgorithm3.initialState]
      · simp [DiagonalAlgorithm3.initialState, Matrix.diagonal_apply, hij]
  | succ t ih =>
      change (run.state (nextIndex t)).L =
        Matrix.diagonal (fun i : Fin m => (run.state (nextIndex t)).L i i)
      rw [run.step t]
      ext i j
      by_cases hij : i = j
      · subst j
        simp [DiagonalAlgorithm3.stepState]
      · have ih_entry : (run.state (currentIndex t)).L i j = 0 := by
          have h := congr_fun (congr_fun ih i) j
          simpa [DiagonalAlgorithm3.CorrectedRun.leftAccumulator,
            Matrix.diagonal_apply, hij] using h
        simp [DiagonalAlgorithm3.stepState, diagonalPart, Matrix.diagonal_apply,
          hij, ih_entry]

private theorem theorem13_rightAccumulator_eq_diagonal_diag {T m n : Nat}
    (S : DiagonalAlgorithm3 T m n) (run : S.CorrectedRun) (u : Fin (T + 1)) :
    run.rightAccumulator u =
      Matrix.diagonal (fun i : Fin n => run.rightAccumulator u i i) := by
  classical
  induction u using Fin.induction with
  | zero =>
      change (run.state ⟨0, Nat.succ_pos T⟩).R =
        Matrix.diagonal (fun i : Fin n => (run.state ⟨0, Nat.succ_pos T⟩).R i i)
      rw [run.initial]
      ext i j
      by_cases hij : i = j
      · subst j
        simp [DiagonalAlgorithm3.initialState]
      · simp [DiagonalAlgorithm3.initialState, Matrix.diagonal_apply, hij]
  | succ t ih =>
      change (run.state (nextIndex t)).R =
        Matrix.diagonal (fun i : Fin n => (run.state (nextIndex t)).R i i)
      rw [run.step t]
      ext i j
      by_cases hij : i = j
      · subst j
        simp [DiagonalAlgorithm3.stepState]
      · have ih_entry : (run.state (currentIndex t)).R i j = 0 := by
          have h := congr_fun (congr_fun ih i) j
          simpa [DiagonalAlgorithm3.CorrectedRun.rightAccumulator,
            Matrix.diagonal_apply, hij] using h
        simp [DiagonalAlgorithm3.stepState, diagonalPart, Matrix.diagonal_apply,
          hij, ih_entry]

private theorem theorem13_powered_kron_preconditioner_current_le_next {T m n : Nat}
    (S : DiagonalAlgorithm3 T m n) (run : S.CorrectedRun) (t : Fin T) :
    ((matrixPower (run.leftAccumulator (currentIndex t)) (1 / 4 : ℝ)
        (run.leftAccumulator_psd (currentIndex t))) ⊗ₖ
      (matrixPower (run.rightAccumulator (currentIndex t)) (1 / 4 : ℝ)
        (run.rightAccumulator_psd (currentIndex t)))) ≤
    ((matrixPower (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
        (run.leftAccumulator_psd (nextIndex t))) ⊗ₖ
      (matrixPower (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
        (run.rightAccumulator_psd (nextIndex t)))) := by
  classical
  let Lcur : SquareMatrix m := run.leftAccumulator (currentIndex t)
  let Lnext : SquareMatrix m := run.leftAccumulator (nextIndex t)
  let Rcur : SquareMatrix n := run.rightAccumulator (currentIndex t)
  let Rnext : SquareMatrix n := run.rightAccumulator (nextIndex t)
  let LcurPow : SquareMatrix m :=
    matrixPower Lcur (1 / 4 : ℝ) (run.leftAccumulator_psd (currentIndex t))
  let LnextPow : SquareMatrix m :=
    matrixPower Lnext (1 / 4 : ℝ) (run.leftAccumulator_psd (nextIndex t))
  let RcurPow : SquareMatrix n :=
    matrixPower Rcur (1 / 4 : ℝ) (run.rightAccumulator_psd (currentIndex t))
  let RnextPow : SquareMatrix n :=
    matrixPower Rnext (1 / 4 : ℝ) (run.rightAccumulator_psd (nextIndex t))
  have hLpow_le : LcurPow ≤ LnextPow := by
    simpa [Lcur, Lnext, LcurPow, LnextPow] using
      (Lemma_6_operator_monotone_powers
        (run.leftAccumulator (currentIndex t))
        (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
        (run.leftAccumulator_psd (currentIndex t))
        (run.leftAccumulator_psd (nextIndex t))
        (theorem13_leftAccumulator_current_le_next S run t)
        (by norm_num) (by norm_num))
  have hRpow_le : RcurPow ≤ RnextPow := by
    simpa [Rcur, Rnext, RcurPow, RnextPow] using
      (Lemma_6_operator_monotone_powers
        (run.rightAccumulator (currentIndex t))
        (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
        (run.rightAccumulator_psd (currentIndex t))
        (run.rightAccumulator_psd (nextIndex t))
        (theorem13_rightAccumulator_current_le_next S run t)
        (by norm_num) (by norm_num))
  have hLcurPow_psd : LcurPow.PosSemidef := by
    simpa [Lcur, LcurPow] using
      matrixPower_posSemidef (run.leftAccumulator (currentIndex t)) (1 / 4 : ℝ)
        (run.leftAccumulator_psd (currentIndex t))
  have hRcurPow_psd : RcurPow.PosSemidef := by
    simpa [Rcur, RcurPow] using
      matrixPower_posSemidef (run.rightAccumulator (currentIndex t)) (1 / 4 : ℝ)
        (run.rightAccumulator_psd (currentIndex t))
  simpa [Lcur, Lnext, Rcur, Rnext, LcurPow, LnextPow, RcurPow, RnextPow] using
    (Lemma_3_iv_kron_order_preserving LnextPow LcurPow RnextPow RcurPow
      hLcurPow_psd hRcurPow_psd hLpow_le hRpow_le)

private theorem theorem13_powered_kron_preconditioner_increment_psd {T m n : Nat}
    (S : DiagonalAlgorithm3 T m n) (run : S.CorrectedRun) (t : Fin T) :
    (((matrixPower (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
        (run.leftAccumulator_psd (nextIndex t))) ⊗ₖ
      (matrixPower (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
        (run.rightAccumulator_psd (nextIndex t)))) -
    ((matrixPower (run.leftAccumulator (currentIndex t)) (1 / 4 : ℝ)
        (run.leftAccumulator_psd (currentIndex t))) ⊗ₖ
      (matrixPower (run.rightAccumulator (currentIndex t)) (1 / 4 : ℝ)
        (run.rightAccumulator_psd (currentIndex t))))).PosSemidef := by
  exact Matrix.le_iff.mp
    (theorem13_powered_kron_preconditioner_current_le_next S run t)

private theorem theorem13_matrixVec_current_sub_finiteMax_le_comparatorRadiusInfinity
    {T m n : Nat} (S : DiagonalAlgorithm3 T m n) (run : S.CorrectedRun)
    [Nonempty (Fin T)] [Nonempty (FlatMatrixIndex m n)]
    (Wstar : MatrixSpace m n) (t : Fin T) :
    (finiteMax fun ij : FlatMatrixIndex m n =>
      |(matrixVec (run.iterate (currentIndex t)) - matrixVec Wstar) ij|) ≤
      run.comparatorRadiusInfinity Wstar := by
  classical
  have htime :
      matrixEntrywiseSupNorm (run.iterate (currentIndex t) - Wstar) ≤
        run.comparatorRadiusInfinity Wstar := by
    dsimp [DiagonalAlgorithm3.CorrectedRun.comparatorRadiusInfinity, finiteMax]
    exact Finset.le_sup'
      (fun t : Fin T => matrixEntrywiseSupNorm (run.iterate (currentIndex t) - Wstar))
      (Finset.mem_univ t)
  simpa [matrixEntrywiseSupNorm, matrixVec, Pi.sub_apply] using htime

private theorem theorem13_diagonal_metric_increment_quadratic_le_infinity_radius_sq_trace
    {T m n : Nat} (S : DiagonalAlgorithm3 T m n) (run : S.CorrectedRun)
    [Nonempty (Fin T)] [Nonempty (FlatMatrixIndex m n)]
    (Wstar : MatrixSpace m n) (t : Fin T) :
    let metric : Fin (T + 1) → GenericSquare (FlatMatrixIndex m n) := fun u =>
      (matrixPower (run.leftAccumulator u) (1 / 4 : ℝ)
          (run.leftAccumulator_psd u)) ⊗ₖ
        (matrixPower (run.rightAccumulator u) (1 / 4 : ℝ)
          (run.rightAccumulator_psd u))
    let Hext : Fin (T + 1) → GenericSquare (FlatMatrixIndex m n) := fun u =>
      if u.val = 0 then 0 else metric u
    quadraticForm (matrixVec (run.iterate (currentIndex t)) - matrixVec Wstar)
        (Hext (nextIndex t) - Hext (currentIndex t)) ≤
      (run.comparatorRadiusInfinity Wstar) ^ 2 *
        genericTrace (Hext (nextIndex t) - Hext (currentIndex t)) := by
  classical
  intro metric Hext
  let x : FlatMatrixIndex m n → ℝ :=
    matrixVec (run.iterate (currentIndex t)) - matrixVec Wstar
  let M : GenericSquare (FlatMatrixIndex m n) := Hext (nextIndex t) - Hext (currentIndex t)
  have hMpsd : M.PosSemidef := by
    have hnext : Hext (nextIndex t) = metric (nextIndex t) := by
      simp [Hext, nextIndex]
    by_cases ht0 : t.val = 0
    · have hcur : Hext (currentIndex t) = 0 := by
        simp [Hext, currentIndex, ht0]
      have hmetric_psd : (metric (nextIndex t)).PosSemidef := by
        exact (matrixPower_posSemidef (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
          (run.leftAccumulator_psd (nextIndex t))).kronecker
          (matrixPower_posSemidef (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
            (run.rightAccumulator_psd (nextIndex t)))
      simpa [M, hnext, hcur] using hmetric_psd
    · have hcur : Hext (currentIndex t) = metric (currentIndex t) := by
        simp [Hext, currentIndex, ht0]
      simpa [M, hnext, hcur, metric] using
        theorem13_powered_kron_preconditioner_increment_psd S run t
  have hMdiag : M = Matrix.diagonal (fun ij : FlatMatrixIndex m n => M ij ij) := by
    have hmetric_diag : ∀ u : Fin (T + 1),
        metric u = Matrix.diagonal (fun ij : FlatMatrixIndex m n => metric u ij ij) := by
      intro u
      have hL :
          ∃ d : Fin m → ℝ,
            matrixPower (run.leftAccumulator u) (1 / 4 : ℝ)
              (run.leftAccumulator_psd u) = Matrix.diagonal d :=
        exists_diagonal_matrixPower_of_eq_diagonal
          (run.leftAccumulator u) (1 / 4 : ℝ) (run.leftAccumulator_psd u)
          (theorem13_leftAccumulator_eq_diagonal_diag S run u)
      have hR :
          ∃ d : Fin n → ℝ,
            matrixPower (run.rightAccumulator u) (1 / 4 : ℝ)
              (run.rightAccumulator_psd u) = Matrix.diagonal d :=
        exists_diagonal_matrixPower_of_eq_diagonal
          (run.rightAccumulator u) (1 / 4 : ℝ) (run.rightAccumulator_psd u)
          (theorem13_rightAccumulator_eq_diagonal_diag S run u)
      simpa [metric] using
        kronecker_eq_diagonal_diag_of_exists_diagonal
          (matrixPower (run.leftAccumulator u) (1 / 4 : ℝ)
            (run.leftAccumulator_psd u))
          (matrixPower (run.rightAccumulator u) (1 / 4 : ℝ)
            (run.rightAccumulator_psd u)) hL hR
    have hzero_diag :
        (0 : GenericSquare (FlatMatrixIndex m n)) =
          Matrix.diagonal
            (fun ij : FlatMatrixIndex m n =>
              (0 : GenericSquare (FlatMatrixIndex m n)) ij ij) := by
      ext ij kl
      by_cases h : ij = kl
      · subst kl
        simp
      · simp [Matrix.diagonal_apply, h]
    have hHext_diag : ∀ u : Fin (T + 1),
        Hext u = Matrix.diagonal (fun ij : FlatMatrixIndex m n => Hext u ij ij) := by
      intro u
      by_cases hu : u.val = 0
      · have hz : Hext u = 0 := by
          dsimp [Hext]
          rw [if_pos hu]
        rw [hz]
        exact hzero_diag
      · have hm : Hext u = metric u := by
          dsimp [Hext]
          rw [if_neg hu]
        rw [hm]
        exact hmetric_diag u
    simpa [M] using
      matrix_sub_eq_diagonal_diag_of_eq_diagonal_diag
        (Hext (nextIndex t)) (Hext (currentIndex t))
        (hHext_diag (nextIndex t)) (hHext_diag (currentIndex t))
  have hdiagBound :
      quadraticForm x M ≤ (finiteMax fun ij : FlatMatrixIndex m n => |x ij|) ^ 2 *
          genericTrace M :=
    quadraticForm_eq_diagonal_le_finiteMax_sq_mul_trace x M hMdiag hMpsd
  have hDmax :
      (finiteMax fun ij : FlatMatrixIndex m n => |x ij|) ≤
        run.comparatorRadiusInfinity Wstar := by
    simpa [x] using
      theorem13_matrixVec_current_sub_finiteMax_le_comparatorRadiusInfinity
        S run Wstar t
  have hxMax_nonneg : 0 ≤ (finiteMax fun ij : FlatMatrixIndex m n => |x ij|) := by
    let ij0 : FlatMatrixIndex m n :=
      Classical.choice (inferInstance : Nonempty (FlatMatrixIndex m n))
    have hij0 :
        |x ij0| ≤ (finiteMax fun ij : FlatMatrixIndex m n => |x ij|) := by
      dsimp [finiteMax]
      exact Finset.le_sup' (fun ij : FlatMatrixIndex m n => |x ij|)
        (Finset.mem_univ ij0)
    exact le_trans (abs_nonneg (x ij0)) hij0
  have hD_nonneg : 0 ≤ run.comparatorRadiusInfinity Wstar :=
    le_trans hxMax_nonneg hDmax
  have hsq :
      (finiteMax fun ij : FlatMatrixIndex m n => |x ij|) ^ 2 ≤
        (run.comparatorRadiusInfinity Wstar) ^ 2 := by
    exact sq_le_sq.mpr
      (by simpa [abs_of_nonneg hxMax_nonneg, abs_of_nonneg hD_nonneg] using hDmax)
  have htrace_nonneg : 0 ≤ genericTrace M :=
    genericTrace_nonneg_of_posSemidef M hMpsd
  calc
    quadraticForm (matrixVec (run.iterate (currentIndex t)) - matrixVec Wstar)
        (Hext (nextIndex t) - Hext (currentIndex t)) =
        quadraticForm x M := by rfl
    _ ≤ (finiteMax fun ij : FlatMatrixIndex m n => |x ij|) ^ 2 *
          genericTrace M := hdiagBound
    _ ≤ (run.comparatorRadiusInfinity Wstar) ^ 2 * genericTrace M := by
          exact mul_le_mul_of_nonneg_right hsq htrace_nonneg

private theorem theorem13_source_first_term_le_infinity_radius_sq_trace {T m n : Nat}
    (S : DiagonalAlgorithm3 T m n) (run : S.CorrectedRun)
    [Nonempty (Fin T)] [Nonempty (FlatMatrixIndex m n)] (Wstar : MatrixSpace m n) :
    (∑ t : Fin T,
      (quadraticForm
          (matrixVec (run.iterate (currentIndex t)) - matrixVec Wstar)
          ((matrixPower (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
              (run.leftAccumulator_psd (nextIndex t))) ⊗ₖ
            (matrixPower (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
              (run.rightAccumulator_psd (nextIndex t)))) -
        quadraticForm
          (matrixVec (run.iterate (nextIndex t)) - matrixVec Wstar)
          ((matrixPower (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
              (run.leftAccumulator_psd (nextIndex t))) ⊗ₖ
            (matrixPower (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
              (run.rightAccumulator_psd (nextIndex t)))))) ≤
      (run.comparatorRadiusInfinity Wstar) ^ 2 *
        genericTrace
          ((matrixPower (run.leftAccumulator (finalIndex T)) (1 / 4 : ℝ)
              (run.leftAccumulator_psd (finalIndex T))) ⊗ₖ
            (matrixPower (run.rightAccumulator (finalIndex T)) (1 / 4 : ℝ)
              (run.rightAccumulator_psd (finalIndex T)))) := by
  classical
  let metric : Fin (T + 1) → GenericSquare (FlatMatrixIndex m n) := fun u =>
    (matrixPower (run.leftAccumulator u) (1 / 4 : ℝ)
        (run.leftAccumulator_psd u)) ⊗ₖ
      (matrixPower (run.rightAccumulator u) (1 / 4 : ℝ)
        (run.rightAccumulator_psd u))
  let Hext : Fin (T + 1) → GenericSquare (FlatMatrixIndex m n) := fun u =>
    if u.val = 0 then 0 else metric u
  have hTpos : 0 < T := by
    rcases ‹Nonempty (Fin T)› with ⟨t⟩
    exact Nat.lt_of_le_of_lt (Nat.zero_le t.val) t.isLt
  have hTne : T ≠ 0 := Nat.ne_of_gt hTpos
  have hHext0 : Hext ⟨0, Nat.zero_lt_succ T⟩ = 0 := by
    simp [Hext]
  have hHextInc : ∀ t : Fin T,
      (Hext (nextIndex t) - Hext (currentIndex t)).PosSemidef := by
    intro t
    have hnext : Hext (nextIndex t) = metric (nextIndex t) := by
      simp [Hext, nextIndex]
    by_cases ht0 : t.val = 0
    · have hcur : Hext (currentIndex t) = 0 := by
        simp [Hext, currentIndex, ht0]
      have hmetric_psd : (metric (nextIndex t)).PosSemidef := by
        exact (matrixPower_posSemidef (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
          (run.leftAccumulator_psd (nextIndex t))).kronecker
          (matrixPower_posSemidef (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
            (run.rightAccumulator_psd (nextIndex t)))
      simpa [hnext, hcur] using hmetric_psd
    · have hcur : Hext (currentIndex t) = metric (currentIndex t) := by
        simp [Hext, currentIndex, ht0]
      simpa [hnext, hcur, metric] using
        theorem13_powered_kron_preconditioner_increment_psd S run t
  have hHextFinalPSD : (Hext ⟨T, Nat.lt_succ_self T⟩).PosSemidef := by
    have hmetric_psd : (metric ⟨T, Nat.lt_succ_self T⟩).PosSemidef := by
      exact (matrixPower_posSemidef (run.leftAccumulator ⟨T, Nat.lt_succ_self T⟩)
        (1 / 4 : ℝ) (run.leftAccumulator_psd ⟨T, Nat.lt_succ_self T⟩)).kronecker
        (matrixPower_posSemidef (run.rightAccumulator ⟨T, Nat.lt_succ_self T⟩)
          (1 / 4 : ℝ) (run.rightAccumulator_psd ⟨T, Nat.lt_succ_self T⟩))
    simpa [Hext, metric, hTne] using hmetric_psd
  have hIncBound : ∀ t : Fin T,
      quadraticForm
          ((fun u : Fin (T + 1) =>
            matrixVec (run.iterate u) - matrixVec Wstar) (currentIndex t))
          (Hext (nextIndex t) - Hext (currentIndex t)) ≤
        (run.comparatorRadiusInfinity Wstar) ^ 2 *
          genericTrace (Hext (nextIndex t) - Hext (currentIndex t)) := by
    intro t
    simpa [metric, Hext] using
      theorem13_diagonal_metric_increment_quadratic_le_infinity_radius_sq_trace
        S run Wstar t
  have htelescope :=
    finite_changing_metric_quadratic_telescope_le_trace_of_increment_bound
      (T := T) (ι := FlatMatrixIndex m n)
      (x := fun u : Fin (T + 1) => matrixVec (run.iterate u) - matrixVec Wstar)
      (H := Hext) (D := run.comparatorRadiusInfinity Wstar)
      hHext0 hHextInc hHextFinalPSD hIncBound
  simpa [Hext, metric, nextIndex, finalIndex, hTne] using htelescope

private theorem theorem13_source_eta_kron_trace_finish {T m n : Nat}
    (S : DiagonalAlgorithm3 T m n) (run : S.CorrectedRun)
    [Nonempty (Fin T)] [Nonempty (FlatMatrixIndex m n)]
    (rankBound : PosNat) (Wstar : MatrixSpace m n)
    (heta : S.eta = learningRate (run.comparatorRadiusInfinity Wstar)
      (positiveRankReal rankBound))
    (hDpos : 0 < run.comparatorRadiusInfinity Wstar) :
    (((run.comparatorRadiusInfinity Wstar) ^ 2 / (2 * S.eta) +
        S.eta * positiveRankReal rankBound) *
      genericTrace
        ((matrixPower (run.leftAccumulator (finalIndex T)) (1 / 4 : ℝ)
            (run.leftAccumulator_psd (finalIndex T))) ⊗ₖ
          (matrixPower (run.rightAccumulator (finalIndex T)) (1 / 4 : ℝ)
            (run.rightAccumulator_psd (finalIndex T))))) =
      Real.sqrt (2 * positiveRankReal rankBound) *
        run.comparatorRadiusInfinity Wstar *
        matrixTrace (matrixPower (run.leftAccumulator (finalIndex T)) (1 / 4 : ℝ)
          (run.leftAccumulator_psd (finalIndex T))) *
        matrixTrace (matrixPower (run.rightAccumulator (finalIndex T)) (1 / 4 : ℝ)
          (run.rightAccumulator_psd (finalIndex T))) := by
  classical
  let D : ℝ := run.comparatorRadiusInfinity Wstar
  let r : ℝ := positiveRankReal rankBound
  let Lpow : SquareMatrix m :=
    matrixPower (run.leftAccumulator (finalIndex T)) (1 / 4 : ℝ)
      (run.leftAccumulator_psd (finalIndex T))
  let Rpow : SquareMatrix n :=
    matrixPower (run.rightAccumulator (finalIndex T)) (1 / 4 : ℝ)
      (run.rightAccumulator_psd (finalIndex T))
  have hrpos : 0 < r := by
    simpa [r] using positiveRankReal_pos rankBound
  have hsqrt_pos : 0 < Real.sqrt (2 * r) := by
    exact Real.sqrt_pos.2 (mul_pos (by norm_num) hrpos)
  have hsqrt_ne : Real.sqrt (2 * r) ≠ 0 := ne_of_gt hsqrt_pos
  have hsqrt_sq : Real.sqrt (2 * r) ^ 2 = 2 * r := by
    exact Real.sq_sqrt (le_of_lt (mul_pos (by norm_num) hrpos))
  have hetaD : S.eta = D / Real.sqrt (2 * r) := by
    simpa [D, r, learningRate] using heta
  have hcoef :
      D ^ 2 / (2 * S.eta) + S.eta * r = Real.sqrt (2 * r) * D := by
    rw [hetaD]
    field_simp [hsqrt_ne]
    nlinarith [hsqrt_sq]
  calc
    (((run.comparatorRadiusInfinity Wstar) ^ 2 / (2 * S.eta) +
          S.eta * positiveRankReal rankBound) *
        genericTrace (Lpow ⊗ₖ Rpow))
        = (D ^ 2 / (2 * S.eta) + S.eta * r) *
            (matrixTrace Lpow * matrixTrace Rpow) := by
            rw [genericTrace_kronecker]
    _ = Real.sqrt (2 * r) * D * matrixTrace Lpow * matrixTrace Rpow := by
            rw [hcoef]
            ring
    _ = Real.sqrt (2 * positiveRankReal rankBound) *
          run.comparatorRadiusInfinity Wstar *
          matrixTrace (matrixPower (run.leftAccumulator (finalIndex T)) (1 / 4 : ℝ)
            (run.leftAccumulator_psd (finalIndex T))) *
          matrixTrace (matrixPower (run.rightAccumulator (finalIndex T)) (1 / 4 : ℝ)
            (run.rightAccumulator_psd (finalIndex T))) := by
            simp [D, r, Lpow, Rpow]

private theorem psdMatrixPower_diagonal_nonneg_generic {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (s : ℝ) (hd : ∀ i, 0 ≤ d i)
    (hD : (Matrix.diagonal d : GenericSquare ι).PosSemidef) :
    psdMatrixPower (Matrix.diagonal d : GenericSquare ι) s hD =
      Matrix.diagonal (fun i : ι => (d i) ^ s) := by
  classical
  rw [psdMatrixPower_eq_cfc]
  exact cfc_rpow_diagonal_nonneg d s hd

private theorem scalar_sq_rpow_neg_half_le_sqrt_increment
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    b * (a + b) ^ (-(1 / 2 : ℝ)) ≤
      2 * ((a + b) ^ (1 / 2 : ℝ) - a ^ (1 / 2 : ℝ)) := by
  exact mul_add_rpow_neg_half_le_two_mul_sub_rpow_half_of_nonneg a b ha hb

private theorem scalar_diagonal_square_root_telescope {T : Nat}
    (g : Fin T → ℝ) (a : ℝ) (ha : 0 ≤ a) :
    (∑ t : Fin T,
      g t ^ 2 *
        (a + ∑ s : Fin T, if s.1 < t.1 + 1 then g s ^ 2 else 0) ^
          (-(1 / 2 : ℝ))) ≤
      2 *
        (a + ∑ s : Fin T, if s.1 < T then g s ^ 2 else 0) ^
          (1 / 2 : ℝ) := by
  exact sum_sq_mul_prefix_add_rpow_neg_half_le_two_mul_terminal_rpow_half g a ha

private theorem spectral_coeff_zero_of_diagonal_current_sq_le {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (d g : ι → ℝ) (hcurrent : ∀ j, g j ^ 2 ≤ d j)
    (A : GenericSquare ι) (hdiag : A = Matrix.diagonal d)
    (hA : A.PosSemidef)
    (i : ι) (hi : hA.1.eigenvalues i = 0) :
    (∑ j : ι,
      g j * (hA.1.eigenvectorUnitary : GenericSquare ι) j i) = 0 := by
  simpa [hdiag] using
    (Matrix.spectral_coeff_eq_zero_of_sq_le_diagonal_of_eigenvalue_eq_zero
      d g hcurrent i (by simpa [hdiag] using hi))

private theorem theorem13_diagonal_hhat_spectral_support_bound {T m n : Nat}
    (S : DiagonalAlgorithm3 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat) :
    ∃ supportDual : Fin T → ℝ,
      (∀ t : Fin T,
        ∃ coeff : FlatMatrixIndex m n → ℝ,
          supportDual t =
            ∑ i : FlatMatrixIndex m n,
              coeff i ^ 2 *
                ((theorem13_diagonal_hhat_prefix_posSemidef S run rankBound
                    (nextIndex t)).1.eigenvalues i) ^ (-(1 / 2 : ℝ)) ∧
          (∀ i : FlatMatrixIndex m n,
            coeff i =
              ∑ j : FlatMatrixIndex m n,
                matrixVec (run.gradientAt t) j *
                  ((theorem13_diagonal_hhat_prefix_posSemidef S run rankBound
                    (nextIndex t)).1.eigenvectorUnitary :
                      GenericSquare (FlatMatrixIndex m n)) j i) ∧
          (∀ i : FlatMatrixIndex m n,
            (theorem13_diagonal_hhat_prefix_posSemidef S run rankBound
              (nextIndex t)).1.eigenvalues i = 0 →
              coeff i = 0)) ∧
      (∑ t : Fin T, supportDual t) ≤
        2 * genericTrace
          (theorem13_diagonal_hhat_prefix S run rankBound (finalIndex T)) := by
  simpa only [theorem13_diagonal_hhat_prefix, genericTrace, psdMatrixPower_eq_cfc,
    theorem13_diagonal_hhat_prefix_base, vectorOuter, nextIndex, finalIndex,
    Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.sum_apply,
    Matrix.ite_apply, Matrix.zero_apply, Matrix.vecMulVec_apply, smul_eq_mul,
    if_pos rfl, if_true, mul_one, pow_two, Matrix.trace] using
    (Matrix.diagonalPrefixGram_spectralSupport_sum_le_two_trace
      (g := fun t : Fin T => matrixVec (run.gradientAt t))
      (a := positiveRankReal rankBound * S.epsilon)
      (mul_nonneg (le_of_lt (positiveRankReal_pos rankBound)) S.epsilon_nonneg))

private theorem theorem13_source_dual_sum_le_rank_trace {T m n : Nat}
    (S : DiagonalAlgorithm3 T m n) (run : S.CorrectedRun)
    (rankBound : PosNat)
    (hrank : ∀ t : Fin T, (run.gradientAt t).rank ≤ rankBound.1) :
    (∑ t : Fin T,
      dualQuadraticForm (matrixVec (run.gradientAt t))
        ((matrixPower (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
            (run.leftAccumulator_psd (nextIndex t))) ⊗ₖ
          (matrixPower (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
            (run.rightAccumulator_psd (nextIndex t))))) ≤
      2 * positiveRankReal rankBound *
        genericTrace
          ((matrixPower (run.leftAccumulator (finalIndex T)) (1 / 4 : ℝ)
              (run.leftAccumulator_psd (finalIndex T))) ⊗ₖ
            (matrixPower (run.rightAccumulator (finalIndex T)) (1 / 4 : ℝ)
              (run.rightAccumulator_psd (finalIndex T)))) := by
  classical
  let Halg : Fin (T + 1) → GenericSquare (FlatMatrixIndex m n) := fun N =>
    (matrixPower (run.leftAccumulator N) (1 / 4 : ℝ)
        (run.leftAccumulator_psd N)) ⊗ₖ
      (matrixPower (run.rightAccumulator N) (1 / 4 : ℝ)
        (run.rightAccumulator_psd N))
  let r : ℝ := positiveRankReal rankBound
  have hflat := theorem13_flattened_algorithm3_update_and_pd_preconditioner S run
  have hr_pos : 0 < r := by
    simpa [r] using positiveRankReal_pos rankBound
  have hHalg_pd : ∀ t : Fin T, (Halg (nextIndex t)).PosDef := by
    intro t
    simpa [Halg] using hflat.2 t
  have hroot_le : ∀ N : Fin (T + 1),
      theorem13_diagonal_hhat_prefix S run rankBound N ≤
        Real.sqrt r • Halg N := by
    intro N
    simpa [Halg, r] using
      theorem13_diagonal_hhat_order_from_prefix_rank_domination
        S run rankBound hrank N
  have hDiagonalSupportEndpoint :
      (∑ t : Fin T, dualQuadraticForm (matrixVec (run.gradientAt t)) (Halg (nextIndex t))) ≤
        2 * r * genericTrace (Halg (finalIndex T)) := by
    obtain ⟨supportDual, hSupportSpectral, hSupportBound⟩ :=
      theorem13_diagonal_hhat_spectral_support_bound S run rankBound
    let alpha : ℝ := Real.sqrt r
    have halpha_nonneg : 0 ≤ alpha := by
      exact Real.sqrt_nonneg r
    have hDualTransfer :
        (∑ t : Fin T,
          dualQuadraticForm (matrixVec (run.gradientAt t)) (Halg (nextIndex t))) ≤
          alpha * ∑ t : Fin T, supportDual t := by
      calc
        (∑ t : Fin T,
          dualQuadraticForm (matrixVec (run.gradientAt t)) (Halg (nextIndex t))) ≤
            ∑ t : Fin T, alpha * supportDual t := by
              refine Finset.sum_le_sum ?_
              intro t _ht
              obtain ⟨coeff, hsupport_eq, hcoeff_def, hcoeff_zero⟩ :=
                hSupportSpectral t
              let A : GenericSquare (FlatMatrixIndex m n) :=
                theorem13_diagonal_hhat_prefix_base S run rankBound (nextIndex t)
              let hApsd : A.PosSemidef :=
                theorem13_diagonal_hhat_prefix_posSemidef S run rankBound
                  (nextIndex t)
              have hroot_le_t :
                  psdMatrixPower A (1 / 2 : ℝ) hApsd ≤
                    alpha • Halg (nextIndex t) := by
                simpa [A, hApsd, alpha, theorem13_diagonal_hhat_prefix] using
                  hroot_le (nextIndex t)
              have hcoeff_def_A : ∀ i : FlatMatrixIndex m n,
                  coeff i =
                    ∑ j : FlatMatrixIndex m n,
                      matrixVec (run.gradientAt t) j *
                        (hApsd.1.eigenvectorUnitary :
                          GenericSquare (FlatMatrixIndex m n)) j i := by
                intro i
                simpa [A, hApsd] using hcoeff_def i
              have hcoeff_zero_A : ∀ i : FlatMatrixIndex m n,
                  hApsd.1.eigenvalues i = 0 → coeff i = 0 := by
                intro i hi
                exact hcoeff_zero i (by simpa [A, hApsd] using hi)
              have hbound :
                  dualQuadraticForm (matrixVec (run.gradientAt t))
                      (Halg (nextIndex t)) ≤
                    alpha *
                      ∑ i : FlatMatrixIndex m n,
                        coeff i ^ 2 *
                          (hApsd.1.eigenvalues i) ^ (-(1 / 2 : ℝ)) := by
                exact
                  spectral_support_inverse_sqrt_order_dual_bound
                    A (Halg (nextIndex t)) hApsd (hHalg_pd t)
                    alpha halpha_nonneg (matrixVec (run.gradientAt t)) coeff
                    hroot_le_t hcoeff_def_A hcoeff_zero_A
              have hsupport_eq_A :
                  supportDual t =
                    ∑ i : FlatMatrixIndex m n,
                      coeff i ^ 2 *
                        (hApsd.1.eigenvalues i) ^ (-(1 / 2 : ℝ)) := by
                simpa [A, hApsd] using hsupport_eq
              calc
                dualQuadraticForm (matrixVec (run.gradientAt t))
                    (Halg (nextIndex t)) ≤
                    alpha *
                      ∑ i : FlatMatrixIndex m n,
                        coeff i ^ 2 *
                          (hApsd.1.eigenvalues i) ^ (-(1 / 2 : ℝ)) := hbound
                _ = alpha * supportDual t := by
                    rw [hsupport_eq_A]
        _ = alpha * ∑ t : Fin T, supportDual t := by
              simp [Finset.mul_sum]
    have hTrace_le :
        genericTrace
            (theorem13_diagonal_hhat_prefix S run rankBound (finalIndex T)) ≤
          alpha * genericTrace (Halg (finalIndex T)) := by
      have hmono :
          genericTrace
              (theorem13_diagonal_hhat_prefix S run rankBound (finalIndex T)) ≤
            genericTrace (alpha • Halg (finalIndex T)) := by
        simpa [alpha] using
          genericTrace_mono_of_matrix_le (hroot_le (finalIndex T))
      have htrace_smul :
          genericTrace (alpha • Halg (finalIndex T)) =
            alpha * genericTrace (Halg (finalIndex T)) := by
        simp [genericTrace]
      simpa [htrace_smul] using hmono
    have hScaledSupport :
        alpha * (∑ t : Fin T, supportDual t) ≤
          alpha *
            (2 * genericTrace
              (theorem13_diagonal_hhat_prefix S run rankBound (finalIndex T))) :=
      mul_le_mul_of_nonneg_left hSupportBound halpha_nonneg
    have hTraceScaled :
        alpha *
            (2 * genericTrace
              (theorem13_diagonal_hhat_prefix S run rankBound (finalIndex T))) ≤
          alpha * (2 * (alpha * genericTrace (Halg (finalIndex T)))) := by
      have htwo : 0 ≤ (2 : ℝ) := by norm_num
      have hinner :
          2 * genericTrace
              (theorem13_diagonal_hhat_prefix S run rankBound (finalIndex T)) ≤
            2 * (alpha * genericTrace (Halg (finalIndex T))) :=
        mul_le_mul_of_nonneg_left hTrace_le htwo
      exact mul_le_mul_of_nonneg_left hinner halpha_nonneg
    have hsqrt_mul : alpha * alpha = r := by
      have hsqrt_sq : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt (le_of_lt hr_pos)
      simpa [alpha, pow_two] using hsqrt_sq
    calc
      (∑ t : Fin T,
        dualQuadraticForm (matrixVec (run.gradientAt t)) (Halg (nextIndex t))) ≤
          alpha * ∑ t : Fin T, supportDual t := hDualTransfer
      _ ≤ alpha *
            (2 * genericTrace
              (theorem13_diagonal_hhat_prefix S run rankBound (finalIndex T))) :=
          hScaledSupport
      _ ≤ alpha * (2 * (alpha * genericTrace (Halg (finalIndex T)))) :=
          hTraceScaled
      _ = 2 * (alpha * alpha) * genericTrace (Halg (finalIndex T)) := by
          ring
      _ = 2 * r * genericTrace (Halg (finalIndex T)) := by
          rw [hsqrt_mul]
  simpa [Halg, r, finalIndex] using hDiagonalSupportEndpoint

/- Corrected-domain endpoint for Theorem 13. -/
theorem Theorem_13_diagonal_matrix_regret_corrected_domain
    (S : DiagonalAlgorithm3 T m n) (run : S.CorrectedRun)
    [Nonempty (Fin T)] [Nonempty (FlatMatrixIndex m n)]
    (rankBound : PosNat) (Wstar : MatrixSpace m n)
    (heta : S.eta = learningRate (run.comparatorRadiusInfinity Wstar)
      (positiveRankReal rankBound))
    (hrank : ∀ t : Fin T, (run.gradientAt t).rank ≤ rankBound.1) :
    run.regret Wstar ≤
      Real.sqrt (2 * positiveRankReal rankBound) * run.comparatorRadiusInfinity Wstar *
        matrixTrace (matrixPower (run.leftAccumulator (finalIndex T)) (1 / 4 : ℝ)
          (run.leftAccumulator_psd (finalIndex T))) *
        matrixTrace (matrixPower (run.rightAccumulator (finalIndex T)) (1 / 4 : ℝ)
          (run.rightAccumulator_psd (finalIndex T))) := by
  classical
  let D := run.comparatorRadiusInfinity Wstar
  by_cases hD0 : D = 0
  · have hD0_run : run.comparatorRadiusInfinity Wstar = 0 := by
      simpa [D] using hD0
    have hiter : ∀ t : Fin T, run.iterate (currentIndex t) = Wstar := by
      intro t
      ext i j
      have htime_le :
          matrixEntrywiseSupNorm (run.iterate (currentIndex t) - Wstar) ≤
            run.comparatorRadiusInfinity Wstar := by
        dsimp [DiagonalAlgorithm3.CorrectedRun.comparatorRadiusInfinity, finiteMax]
        exact Finset.le_sup'
          (fun t : Fin T => matrixEntrywiseSupNorm (run.iterate (currentIndex t) - Wstar))
          (Finset.mem_univ t)
      have htime_le_zero :
          matrixEntrywiseSupNorm (run.iterate (currentIndex t) - Wstar) ≤ 0 := by
        simpa [hD0_run] using htime_le
      have hentry_le :
          |(run.iterate (currentIndex t) - Wstar) i j| ≤
            matrixEntrywiseSupNorm (run.iterate (currentIndex t) - Wstar) := by
        dsimp [matrixEntrywiseSupNorm, finiteMax]
        exact Finset.le_sup'
          (fun ij : FlatMatrixIndex m n =>
            |(run.iterate (currentIndex t) - Wstar) ij.1 ij.2|)
          (Finset.mem_univ (i, j))
      have habs_zero :
          |(run.iterate (currentIndex t) - Wstar) i j| = 0 := by
        exact le_antisymm (le_trans hentry_le htime_le_zero) (abs_nonneg _)
      have hentry_zero :
          (run.iterate (currentIndex t) - Wstar) i j = 0 := by
        exact abs_eq_zero.mp habs_zero
      simpa using sub_eq_zero.mp hentry_zero
    have hreg : run.regret Wstar = 0 := by
      unfold DiagonalAlgorithm3.CorrectedRun.regret
      simp [hiter]
    rw [hreg, hD0_run]
    norm_num
  · have hD_nonneg : 0 ≤ D := by
      let t0 : Fin T := Classical.choice (inferInstance : Nonempty (Fin T))
      let ij0 : FlatMatrixIndex m n :=
        Classical.choice (inferInstance : Nonempty (FlatMatrixIndex m n))
      have hentry_nonneg :
          0 ≤ |(run.iterate (currentIndex t0) - Wstar) ij0.1 ij0.2| := abs_nonneg _
      have hentry_le :
          |(run.iterate (currentIndex t0) - Wstar) ij0.1 ij0.2| ≤
            matrixEntrywiseSupNorm (run.iterate (currentIndex t0) - Wstar) := by
        dsimp [matrixEntrywiseSupNorm, finiteMax]
        exact Finset.le_sup'
          (fun ij : FlatMatrixIndex m n =>
            |(run.iterate (currentIndex t0) - Wstar) ij.1 ij.2|)
          (Finset.mem_univ ij0)
      have hnorm_nonneg :
          0 ≤ matrixEntrywiseSupNorm (run.iterate (currentIndex t0) - Wstar) :=
        le_trans hentry_nonneg hentry_le
      have hle :
          matrixEntrywiseSupNorm (run.iterate (currentIndex t0) - Wstar) ≤ D := by
        dsimp [D, DiagonalAlgorithm3.CorrectedRun.comparatorRadiusInfinity, finiteMax]
        exact Finset.le_sup'
          (fun t : Fin T => matrixEntrywiseSupNorm (run.iterate (currentIndex t) - Wstar))
          (Finset.mem_univ t0)
      exact le_trans hnorm_nonneg hle
    have hDpos : 0 < run.comparatorRadiusInfinity Wstar := by
      have hDpos_local : 0 < D := lt_of_le_of_ne hD_nonneg (Ne.symm hD0)
      simpa [D] using hDpos_local
    have heta_pos : 0 < S.eta := by
      rw [heta]
      exact learningRate_pos_of_pos hDpos (positiveRankReal_pos rankBound)
    have hconvRegret :
        run.regret Wstar ≤ ∑ t : Fin T,
          vectorDot (matrixVec (run.gradientAt t))
            (matrixVec (run.iterate (currentIndex t)) - matrixVec Wstar) := by
      let idx : ℕ → Fin T := fun s =>
        if h : s - 1 < T then
          ⟨s - 1, h⟩
        else
          Classical.choice (inferInstance : Nonempty (Fin T))
      let toEuc : (FlatMatrixIndex m n → ℝ) →
          EuclideanSpace ℝ (FlatMatrixIndex m n) :=
        (EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ).symm
      let unvecLin : EuclideanSpace ℝ (FlatMatrixIndex m n) →ₗ[ℝ]
          MatrixSpace m n :=
        { toFun := fun v i j => (EuclideanSpace.equiv (FlatMatrixIndex m n) ℝ v) (i, j)
          map_add' := by
            intro x y
            ext i j
            simp
          map_smul' := by
            intro a x
            ext i j
            simp }
      let lossNat : ℕ → EuclideanSpace ℝ (FlatMatrixIndex m n) → ℝ :=
        fun s v => S.loss (idx s) (unvecLin v)
      let x : ℕ → EuclideanSpace ℝ (FlatMatrixIndex m n) :=
        fun s => toEuc (matrixVec (run.iterate (currentIndex (idx s))))
      let g : ℕ → EuclideanSpace ℝ (FlatMatrixIndex m n) :=
        fun s => toEuc (matrixVec (run.gradientAt (idx s)))
      let xStar : EuclideanSpace ℝ (FlatMatrixIndex m n) :=
        toEuc (matrixVec Wstar)
      have hconv : ∀ s ∈ Finset.Icc 1 T, ConvexOn ℝ Set.univ (lossNat s) := by
        intro s _hs
        have hcomp := (S.loss_convex (idx s)).comp_linearMap unvecLin
        simpa [lossNat, unvecLin, Function.comp_def] using hcomp
      have hx : ∀ s ∈ Finset.Icc 1 T,
          x s ∈ (Set.univ : Set (EuclideanSpace ℝ (FlatMatrixIndex m n))) := by
        intro s _hs
        simp
      have hxStar :
          xStar ∈ (Set.univ : Set (EuclideanSpace ℝ (FlatMatrixIndex m n))) := by
        simp
      have hgrad : ∀ s ∈ Finset.Icc 1 T,
          HasGradientWithinAt (lossNat s) (g s) Set.univ (x s) := by
        intro s _hs
        simpa [lossNat, x, g, toEuc, unvecLin] using
          theorem13_flattened_loss_gradient_bridge S run (idx s)
      have hfinite := finite_horizon_convex_regret_le_gradient_inner_sum
        (F := (Set.univ : Set (EuclideanSpace ℝ (FlatMatrixIndex m n))))
        (loss := lossNat) (x := x) (g := g) (T := T) (xStar := xStar)
        hconv hx hxStar hgrad
      have hsum_loss_x :
          (∑ s ∈ Finset.Icc 1 T, lossNat s (x s)) =
            ∑ t : Fin T, S.loss t (run.iterate (currentIndex t)) := by
        simpa [lossNat, x, idx, toEuc, unvecLin, matrixVec] using
          (sum_Icc_one_matrix_fin_reindex (T := T)
            (F := fun t : Fin T => S.loss t (run.iterate (currentIndex t))))
      have hsum_loss_star :
          (∑ s ∈ Finset.Icc 1 T, lossNat s xStar) =
            ∑ t : Fin T, S.loss t Wstar := by
        simpa [lossNat, xStar, idx, toEuc, unvecLin, matrixVec] using
          (sum_Icc_one_matrix_fin_reindex (T := T)
            (F := fun t : Fin T => S.loss t Wstar))
      have hleft :
          (∑ s ∈ Finset.Icc 1 T, lossNat s (x s)) -
              (∑ s ∈ Finset.Icc 1 T, lossNat s xStar) =
            run.regret Wstar := by
        rw [hsum_loss_x, hsum_loss_star]
        unfold DiagonalAlgorithm3.CorrectedRun.regret
        rw [Finset.sum_sub_distrib]
      have hsum_rhs :
          (∑ s ∈ Finset.Icc 1 T, inner ℝ (g s) (x s - xStar)) =
            ∑ t : Fin T,
              vectorDot (matrixVec (run.gradientAt t))
                (matrixVec (run.iterate (currentIndex t)) - matrixVec Wstar) := by
        have hterm :
            (∑ s ∈ Finset.Icc 1 T, inner ℝ (g s) (x s - xStar)) =
              ∑ s ∈ Finset.Icc 1 T,
                vectorDot (matrixVec (run.gradientAt (idx s)))
                  (matrixVec (run.iterate (currentIndex (idx s))) - matrixVec Wstar) := by
          apply Finset.sum_congr rfl
          intro s hs
          simpa [g, x, xStar, toEuc] using
            (euclidean_inner_sub_eq_vectorDot
              (matrixVec (run.gradientAt (idx s)))
              (matrixVec (run.iterate (currentIndex (idx s))))
              (matrixVec Wstar))
        rw [hterm]
        simpa [idx] using
          (sum_Icc_one_matrix_fin_reindex (T := T)
            (F := fun t : Fin T =>
              vectorDot (matrixVec (run.gradientAt t))
                (matrixVec (run.iterate (currentIndex t)) - matrixVec Wstar)))
      calc
        run.regret Wstar =
            (∑ s ∈ Finset.Icc 1 T, lossNat s (x s)) -
              (∑ s ∈ Finset.Icc 1 T, lossNat s xStar) := hleft.symm
        _ ≤ ∑ s ∈ Finset.Icc 1 T, inner ℝ (g s) (x s - xStar) := hfinite
        _ = ∑ t : Fin T,
              vectorDot (matrixVec (run.gradientAt t))
                (matrixVec (run.iterate (currentIndex t)) - matrixVec Wstar) := hsum_rhs
    let w : Fin (T + 1) → FlatMatrixIndex m n → ℝ :=
      fun t => matrixVec (run.iterate t)
    let g : Fin T → FlatMatrixIndex m n → ℝ :=
      fun t => matrixVec (run.gradientAt t)
    let H : Fin T → GenericSquare (FlatMatrixIndex m n) := fun t =>
      (matrixPower (run.leftAccumulator (nextIndex t)) (1 / 4 : ℝ)
          (run.leftAccumulator_psd (nextIndex t))) ⊗ₖ
        (matrixPower (run.rightAccumulator (nextIndex t)) (1 / 4 : ℝ)
          (run.rightAccumulator_psd (nextIndex t)))
    let wstar : FlatMatrixIndex m n → ℝ := matrixVec Wstar
    have hflat := theorem13_flattened_algorithm3_update_and_pd_preconditioner S run
    have hOMD :
        ∑ t : Fin T, vectorDot (matrixVec (run.gradientAt t))
          (matrixVec (run.iterate (currentIndex t)) - matrixVec Wstar) ≤
          (1 / (2 * S.eta)) *
            ∑ t : Fin T,
              (quadraticForm
                  (matrixVec (run.iterate (currentIndex t)) - matrixVec Wstar)
                  (H t) -
                quadraticForm
                  (matrixVec (run.iterate (nextIndex t)) - matrixVec Wstar)
                  (H t)) +
            (S.eta / 2) *
              ∑ t : Fin T, dualQuadraticForm (matrixVec (run.gradientAt t)) (H t) := by
      simpa [w, g, H, wstar] using
        (finite_index_adaptive_omd_regret (T := T) (ι := FlatMatrixIndex m n)
          S.eta heta_pos w g H wstar hflat.1 hflat.2)
    have hsource_pre_eq3 :
        run.regret Wstar ≤
          (1 / (2 * S.eta)) *
            ∑ t : Fin T,
              (quadraticForm
                  (matrixVec (run.iterate (currentIndex t)) - matrixVec Wstar)
                  (H t) -
                quadraticForm
                  (matrixVec (run.iterate (nextIndex t)) - matrixVec Wstar)
                  (H t)) +
            (S.eta / 2) *
              ∑ t : Fin T, dualQuadraticForm (matrixVec (run.gradientAt t)) (H t) :=
      le_trans hconvRegret hOMD
    let HT : GenericSquare (FlatMatrixIndex m n) :=
      (matrixPower (run.leftAccumulator (finalIndex T)) (1 / 4 : ℝ)
          (run.leftAccumulator_psd (finalIndex T))) ⊗ₖ
        (matrixPower (run.rightAccumulator (finalIndex T)) (1 / 4 : ℝ)
          (run.rightAccumulator_psd (finalIndex T)))
    have hremaining_after_omd :
          run.regret Wstar ≤
            Real.sqrt (2 * positiveRankReal rankBound) * run.comparatorRadiusInfinity Wstar *
              matrixTrace (matrixPower (run.leftAccumulator (finalIndex T)) (1 / 4 : ℝ)
                (run.leftAccumulator_psd (finalIndex T))) *
              matrixTrace (matrixPower (run.rightAccumulator (finalIndex T)) (1 / 4 : ℝ)
                (run.rightAccumulator_psd (finalIndex T))) := by
      have hfirst :
            (∑ t : Fin T,
              (quadraticForm
                  (matrixVec (run.iterate (currentIndex t)) - matrixVec Wstar)
                  (H t) -
                quadraticForm
                  (matrixVec (run.iterate (nextIndex t)) - matrixVec Wstar)
                  (H t))) ≤
              (run.comparatorRadiusInfinity Wstar) ^ 2 * genericTrace HT := by
        simpa [H, HT, finalIndex] using
          theorem13_source_first_term_le_infinity_radius_sq_trace S run Wstar
      have hdual :
            (∑ t : Fin T, dualQuadraticForm (matrixVec (run.gradientAt t)) (H t)) ≤
              2 * positiveRankReal rankBound * genericTrace HT := by
        simpa [H, HT, finalIndex] using
          theorem13_source_dual_sum_le_rank_trace S run rankBound hrank
      have hfirst_scaled :
            (1 / (2 * S.eta)) *
              (∑ t : Fin T,
                (quadraticForm
                    (matrixVec (run.iterate (currentIndex t)) - matrixVec Wstar)
                    (H t) -
                  quadraticForm
                    (matrixVec (run.iterate (nextIndex t)) - matrixVec Wstar)
                    (H t))) ≤
              (1 / (2 * S.eta)) *
                ((run.comparatorRadiusInfinity Wstar) ^ 2 * genericTrace HT) := by
          exact mul_le_mul_of_nonneg_left hfirst
            (div_nonneg zero_le_one (mul_nonneg (by norm_num) (le_of_lt heta_pos)))
      have hdual_scaled :
            (S.eta / 2) *
              (∑ t : Fin T, dualQuadraticForm (matrixVec (run.gradientAt t)) (H t)) ≤
              (S.eta / 2) *
                (2 * positiveRankReal rankBound * genericTrace HT) := by
          exact mul_le_mul_of_nonneg_left hdual
            (div_nonneg (le_of_lt heta_pos) (by norm_num))
      have hsource_eq4 :
            run.regret Wstar ≤
              (((run.comparatorRadiusInfinity Wstar) ^ 2 / (2 * S.eta) +
                  S.eta * positiveRankReal rankBound) * genericTrace HT) := by
          calc
            run.regret Wstar ≤
                (1 / (2 * S.eta)) *
                  (∑ t : Fin T,
                    (quadraticForm
                        (matrixVec (run.iterate (currentIndex t)) - matrixVec Wstar)
                        (H t) -
                      quadraticForm
                        (matrixVec (run.iterate (nextIndex t)) - matrixVec Wstar)
                        (H t))) +
                  (S.eta / 2) *
                    (∑ t : Fin T, dualQuadraticForm (matrixVec (run.gradientAt t)) (H t)) :=
                hsource_pre_eq3
            _ ≤
                (1 / (2 * S.eta)) *
                  ((run.comparatorRadiusInfinity Wstar) ^ 2 * genericTrace HT) +
                (S.eta / 2) *
                  (2 * positiveRankReal rankBound * genericTrace HT) := by
                exact add_le_add hfirst_scaled hdual_scaled
            _ =
                (((run.comparatorRadiusInfinity Wstar) ^ 2 / (2 * S.eta) +
                    S.eta * positiveRankReal rankBound) * genericTrace HT) := by
                ring
      have hfinish :=
          theorem13_source_eta_kron_trace_finish S run rankBound Wstar heta hDpos
      exact le_trans hsource_eq4 (le_of_eq (by simpa [HT] using hfinish))
    exact hremaining_after_omd

structure CorrectedDomainTheoremBoundary where
  source_endpoint : String
  corrected_endpoint : String
  source_issue : String

/- Non-masquerading boundary record for book JSON key_lemmas.Theorem_7_matrix_regret. -/
def Theorem_7_matrix_regret_boundary : CorrectedDomainTheoremBoundary where
  source_endpoint := "Theorem_7_matrix_regret"
  corrected_endpoint := "Theorem_7_matrix_regret_corrected_domain"
  source_issue :=
    "Algorithm 1 prints gradients and negative fractional powers; the theorem head does not state differentiability or strict positive-definite accumulator domains."

/- Source issue record for Theorem 7 Eq. (6), source/original_source.txt
   lines 520-547.  The checked zero-prefix theorem exhibits the missing
   strict-positive domain at epsilon = 0, while the corrected endpoint uses
   the proved positive-delta support-limit route. -/
def Theorem_7_equation6_source_domain_boundary : CorrectedDomainTheoremBoundary where
  source_endpoint := "Theorem_7_matrix_regret Eq. (6)"
  corrected_endpoint := "theorem7_source_dual_sum_le_rank_trace"
  source_issue :=
    "The checked theorem7_hhat_prefix_zero_not_posDef_at_epsilon_zero proves that, whenever FlatMatrixIndex m n is nonempty, the actual theorem7_hhat_prefix at N = 0 is not PosDef when epsilon = 0, so the paper's unregularized Lemma 2 invocation lacks its required domain. The corrected theorem7_source_dual_sum_le_rank_trace endpoint instead uses the positive-delta Eq. (6) proof and checked support-limit bridge."

/- Non-masquerading boundary record for book JSON main_theorem.Theorem_10_tensor_regret. -/
def Theorem_10_tensor_regret_boundary : CorrectedDomainTheoremBoundary where
  source_endpoint := "Theorem_10_tensor_regret"
  corrected_endpoint := "Theorem_10_tensor_regret_corrected_domain"
  source_issue :=
    "Algorithm 2 prints tensor gradients and inverse mode powers; the corrected target carries the corresponding trajectory evidence explicitly."

/- Non-masquerading boundary record for book JSON key_lemmas.Theorem_13_diagonal_matrix_regret. -/
def Theorem_13_diagonal_matrix_regret_boundary : CorrectedDomainTheoremBoundary where
  source_endpoint := "Theorem_13_diagonal_matrix_regret"
  corrected_endpoint := "Theorem_13_diagonal_matrix_regret_corrected_domain"
  source_issue :=
    "Appendix A inherits the matrix proof's strict preconditioner domain while the printed theorem head only states rank and comparator-radius data."

end Shampoo
