import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Order.Filter.Cofinite
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import SOptLib.Glue.Analysis
import SOptLib.Glue.Calculus
import SOptLib.Model.Iterates

/-!
# The second Heavy-Ball riddle

Phase 0 object layer for the Heavy-Ball formalization campaign. The declarations
below model the source objects from `book/HeavyBallSecondRiddle.json`: admissible
objectives in `F_{q,1}`, the deterministic Heavy-Ball update, generated
trajectories, prescribed two-point certificates, interpolation residuals, the
closed parameter box, record maps, and the infinite/finite centered energies.

The theorem bodies are proof obligations for later phases; no proof-contingency
regularity assumptions are added to the paper-facing theorem heads.

## Source-to-declaration coverage

* `HB-A`: `HB_A_exact_separation`
* `HB-B`: `HB_B_uniform_linear_convergence`
* `HB-C`: `HB_C_no_common_record_energy`
* `HB-BOX`: `HB_BOX_uniform_absence_and_convergence`
* `HB-RECORD-GENERAL`: `HB_RECORD_GENERAL_conditional_obstruction`
* `HB-ENERGY-INFINITE`: `HB_ENERGY_INFINITE_centered_energy`
* `HB-ENERGY-FINITE`: `HB_ENERGY_FINITE_centered_energy`
* Algorithmic spine `(HB)`: `hbSuccessor`, `hbStateMap`, `hbStateProcess`,
  `hbIterate`, `hbInitialCenteredState`, `hbCenteredStateAt`, `hbCenteredMap`,
  and `hbCenteredEnergyFinite`.
* D5-D9 dynamics layer: `hbTransferDomain`, `hbTransferFunction`,
  `hbTransferUnitCircle`, `hbMultiplier`, `hbCenteredNonlinearity`,
  `hbFreeResponse`, `hbPlantResponse`, `hbLoopRepresentation`,
  the D9 conditional/finite-prefix continuation objects, and the
  source-facing D5-D9 theorem heads.
-/

open scoped BigOperators
open Filter

namespace HeavyBallSecondRiddle

noncomputable section

/-- The Euclidean space `R^d` used by the source. -/
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Source parameter domain
`D = {0 < q < 1, 0 <= b < 1, 0 < a < 2(1+b)}`. -/
def ParameterDomain (q a b : ℝ) : Prop :=
  0 < q ∧ q < 1 ∧ 0 ≤ b ∧ b < 1 ∧ 0 < a ∧ a < 2 * (1 + b)

theorem parameterDomain_q_pos {q a b : ℝ} (h : ParameterDomain q a b) : 0 < q := h.1

theorem parameterDomain_q_lt_one {q a b : ℝ} (h : ParameterDomain q a b) : q < 1 := h.2.1

theorem parameterDomain_one_sub_q_pos {q a b : ℝ} (h : ParameterDomain q a b) :
    0 < 1 - q := by
  linarith [parameterDomain_q_lt_one h]

/-- The closed box from HB-B/HB-BOX. -/
def HB_Box (q a b : ℝ) : Prop :=
  |q - (1 / 100 : ℝ)| ≤ (1 / 100000 : ℝ) ∧
    |a - (113 / 50 : ℝ)| ≤ (1 / 100000 : ℝ) ∧
    |b - (3 / 5 : ℝ)| ≤ (1 / 100000 : ℝ)

def qStar : ℝ := 1 / 100
def aStar : ℝ := 113 / 50
def bStar : ℝ := 3 / 5

def HB_C : ℝ := (10 : ℝ) ^ (14 : ℕ)
def HB_N : ℕ := 4800000000000000
def HB_contraction : ℝ := 1 - (HB_C)⁻¹
def HB_D10_free_energy_constant : ℝ := 1 + 200 * (610000 : ℝ) ^ 2

theorem HB_central_parameters_in_domain : ParameterDomain qStar aStar bStar := by
  unfold ParameterDomain qStar aStar bStar
  norm_num

theorem HB_box_subset_domain {q a b : ℝ} (hbox : HB_Box q a b) :
    ParameterDomain q a b := by
  unfold HB_Box ParameterDomain at *
  rcases hbox with ⟨hqbox, habox, hbbox⟩
  have hq := abs_le.mp hqbox
  have ha := abs_le.mp habox
  have hb := abs_le.mp hbbox
  exact ⟨by nlinarith [hq.1], by nlinarith [hq.2],
    by nlinarith [hb.1], by nlinarith [hb.2],
    by nlinarith [ha.1], by nlinarith [ha.2, hb.1]⟩

/-- Canonical source class `F_{q,1}(R^d)`.

The gradient is Mathlib's selected `gradient`; it is not a free oracle/witness
field. The proposition fields are exactly the stated objective assumptions:
global differentiability, `q`-strong convexity, and `1`-Lipschitz gradient. -/
structure AdmissibleObjective (q : ℝ) (d : ℕ) where
  f : Vec d → ℝ
  differentiable : ∀ x, DifferentiableAt ℝ f x
  strongConvex_lower :
    ∀ x y : Vec d,
      f y ≥ f x + inner ℝ (gradient f x) (y - x) + (q / 2) * ‖y - x‖ ^ 2
  gradient_lipschitz :
    ∀ x y : Vec d, ‖gradient f y - gradient f x‖ ≤ ‖y - x‖

theorem HB_admissible_objective_hasGradientAt
    {q : ℝ} {d : ℕ} (hf : AdmissibleObjective q d) (x : Vec d) :
    HasGradientAt hf.f (gradient hf.f x) x := by
  exact (hf.differentiable x).hasGradientAt

private theorem admissible_objective_coercive_tail
    {q : ℝ} {d : ℕ} (hq : 0 < q) (hf : AdmissibleObjective q d) :
    ∃ R : ℝ, dist (0 : Vec d) 0 ≤ R ∧
      ∀ x : Vec d, x ∈ Set.univ → R ≤ dist x 0 → hf.f 0 ≤ hf.f x := by
  classical
  let g0 : Vec d := gradient hf.f (0 : Vec d)
  let G : ℝ := ‖g0‖
  refine ⟨max 0 (2 * G / q), ?_, ?_⟩
  · have hG_nonneg : 0 ≤ G := norm_nonneg g0
    have hdiv_nonneg : 0 ≤ 2 * G / q := by
      positivity
    rw [dist_self]
    exact le_max_of_le_right hdiv_nonneg
  · intro x _ hxR
    have hxnormR : max 0 (2 * G / q) ≤ ‖x‖ := by
      simpa [dist_eq_norm] using hxR
    have hR_le_norm : 2 * G / q ≤ ‖x‖ :=
      le_trans (le_max_right 0 (2 * G / q)) hxnormR
    have hG_nonneg : 0 ≤ G := norm_nonneg g0
    have hxnorm_nonneg : 0 ≤ ‖x‖ := norm_nonneg x
    have hinner_lower : -(G * ‖x‖) ≤ inner ℝ g0 x := by
      have h := real_inner_le_norm (-g0) x
      have hneg : -inner ℝ g0 x ≤ G * ‖x‖ := by
        simpa [G, g0] using h
      linarith
    have hquad_dom : G * ‖x‖ ≤ (q / 2) * ‖x‖ ^ 2 := by
      have hq_nonneg : 0 ≤ q := le_of_lt hq
      have hmul :=
        mul_le_mul_of_nonneg_right hR_le_norm hq_nonneg
      have htwoG_le : 2 * G ≤ q * ‖x‖ := by
        have hq_ne : q ≠ 0 := ne_of_gt hq
        have hleft : (2 * G / q) * q = 2 * G := by
          field_simp [hq_ne]
        nlinarith
      nlinarith [htwoG_le, hxnorm_nonneg]
    have hnonneg :
        0 ≤ inner ℝ g0 x + (q / 2) * ‖x‖ ^ 2 := by
      nlinarith
    have hstrong :
        hf.f (0 : Vec d) + inner ℝ g0 x + (q / 2) * ‖x‖ ^ 2 ≤ hf.f x := by
      have h := hf.strongConvex_lower (0 : Vec d) x
      simpa [g0] using h
    nlinarith

private theorem admissible_objective_exists_minimizer
    {q : ℝ} {d : ℕ} (hq : 0 < q) (hf : AdmissibleObjective q d) :
    ∃ x : Vec d, ∀ y : Vec d, hf.f x ≤ hf.f y := by
  classical
  have hcont : Continuous hf.f :=
    continuous_iff_continuousAt.mpr (fun x => (hf.differentiable x).continuousAt)
  obtain ⟨xmin, _hxmin, hxmin_minOn⟩ :=
    exists_isMinOn_of_closed_coercive_closedBall
      (X := Set.univ) isClosed_univ (0 : Vec d) (0 : Vec d) (by simp)
      hf.f hcont.continuousOn (admissible_objective_coercive_tail hq hf)
  refine ⟨xmin, ?_⟩
  intro y
  exact hxmin_minOn trivial

private theorem gradient_eq_zero_of_admissible_global_min
    {q : ℝ} {d : ℕ} (hf : AdmissibleObjective q d) {x : Vec d}
    (hmin : ∀ y : Vec d, hf.f x ≤ hf.f y) :
    gradient hf.f x = 0 := by
  have hgrad : HasGradientAt hf.f (gradient hf.f x) x :=
    HB_admissible_objective_hasGradientAt hf x
  have hzero_eq_grad : (0 : Vec d) = gradient hf.f x := by
    refine
      eq_gradient_of_hasGradientAt_of_affine_minorant_touch
        (F := hf.f) (g := gradient hf.f x) (a := (0 : Vec d))
        (x0 := x) (c := -hf.f x) hgrad ?_ ?_
    · intro y
      simpa using hmin y
    · simp
  exact hzero_eq_grad.symm

private theorem admissible_objective_minimizers_equal
    {q : ℝ} {d : ℕ} (hq : 0 < q) (hf : AdmissibleObjective q d)
    {x y : Vec d} (hx : ∀ z : Vec d, hf.f x ≤ hf.f z)
    (hy : ∀ z : Vec d, hf.f y ≤ hf.f z) :
    x = y := by
  have hygrad : gradient hf.f y = 0 :=
    gradient_eq_zero_of_admissible_global_min hf hy
  have hstrong :
      hf.f y + (q / 2) * ‖x - y‖ ^ 2 ≤ hf.f x := by
    have h := hf.strongConvex_lower y x
    simpa [hygrad] using h
  have hquad_nonpos : (q / 2) * ‖x - y‖ ^ 2 ≤ 0 := by
    nlinarith [hx y]
  have hnorm_sq_zero : ‖x - y‖ ^ 2 = 0 := by
    have hqhalf_pos : 0 < q / 2 := by positivity
    have hsq_nonneg : 0 ≤ ‖x - y‖ ^ 2 := sq_nonneg _
    nlinarith
  have hnorm_zero : ‖x - y‖ = 0 := by
    nlinarith [norm_nonneg (x - y), hnorm_sq_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)

theorem HB_admissible_objective_existsUnique_minimizer
    {q : ℝ} {d : ℕ} (hq : 0 < q) (hf : AdmissibleObjective q d) :
    ∃! x : Vec d, ∀ y : Vec d, hf.f x ≤ hf.f y := by
  obtain ⟨xmin, hmin⟩ := admissible_objective_exists_minimizer hq hf
  refine ⟨xmin, hmin, ?_⟩
  intro y hy
  exact admissible_objective_minimizers_equal hq hf hy hmin

/-- The paper's `x_*`, selected canonically from the admissible objective. -/
def objectiveMinimizer {q : ℝ} {d : ℕ} (hq : 0 < q)
    (hf : AdmissibleObjective q d) : Vec d :=
  Classical.choose (HB_admissible_objective_existsUnique_minimizer hq hf)

theorem objectiveMinimizer_is_min
    {q : ℝ} {d : ℕ} (hq : 0 < q) (hf : AdmissibleObjective q d) :
    ∀ y : Vec d, hf.f (objectiveMinimizer hq hf) ≤ hf.f y :=
  (Classical.choose_spec (HB_admissible_objective_existsUnique_minimizer hq hf)).1

theorem objectiveMinimizer_unique
    {q : ℝ} {d : ℕ} (hq : 0 < q) (hf : AdmissibleObjective q d)
    {x : Vec d} (hx : ∀ y : Vec d, hf.f x ≤ hf.f y) :
    x = objectiveMinimizer hq hf := by
  exact
    ((Classical.choose_spec
      (HB_admissible_objective_existsUnique_minimizer hq hf)).2 x hx)

/-- The paper's `f_* = f(x_*)`. -/
def objectiveMinimum {q : ℝ} {d : ℕ} (hq : 0 < q)
    (hf : AdmissibleObjective q d) : ℝ :=
  hf.f (objectiveMinimizer hq hf)

/-- The source successor formula `(L)`,
`w = (1+b)v - b u - a grad f(v)`. -/
def hbSuccessor {q : ℝ} {d : ℕ} (a b : ℝ)
    (hf : AdmissibleObjective q d) (u v : Vec d) : Vec d :=
  (1 + b) • v - b • u - a • gradient hf.f v

theorem hbSuccessor_eq_successor_form
    {q : ℝ} {d : ℕ} (a b : ℝ) (hf : AdmissibleObjective q d)
    (u v : Vec d) :
    hbSuccessor a b hf u v = (1 + b) • v - b • u - a • gradient hf.f v := by
  rfl

theorem hbSuccessor_eq_fixed_objective_update
    {q : ℝ} {d : ℕ} (a b : ℝ) (hf : AdmissibleObjective q d)
    (u v : Vec d) :
    hbSuccessor a b hf u v = v - a • gradient hf.f v + b • (v - u) := by
  unfold hbSuccessor
  simp [sub_eq_add_neg, add_smul, one_smul, add_assoc, add_left_comm, add_comm]

/-- Two-state Heavy-Ball state `(x_{t-1}, x_t)`. -/
abbrev HBState (d : ℕ) := Vec d × Vec d

/-- The canonical one-step state map generated by the Heavy-Ball successor. -/
def hbStateMap {q : ℝ} {d : ℕ} (a b : ℝ)
    (hf : AdmissibleObjective q d) (Y : HBState d) : HBState d :=
  (Y.2, hbSuccessor a b hf Y.1 Y.2)

/-- The generated deterministic Heavy-Ball state process from `(x_{-1}, x_0)`. -/
def hbStateProcess {q : ℝ} {d : ℕ} (a b : ℝ)
    (hf : AdmissibleObjective q d) (xMinusOne xZero : Vec d) :
    ℕ → Unit → HBState d :=
  SOptLib.recursiveIterateProcess (Ω := Unit) (P := HBState d)
    (xMinusOne, xZero) (fun _ Y _ => hbStateMap a b hf Y)

/-- The generated deterministic Heavy-Ball state at time `t`. -/
def hbStateAt {q : ℝ} {d : ℕ} (a b : ℝ)
    (hf : AdmissibleObjective q d) (xMinusOne xZero : Vec d) (t : ℕ) :
    HBState d :=
  hbStateProcess a b hf xMinusOne xZero t ()

/-- The source output iterate `x_t`. -/
def hbIterate {q : ℝ} {d : ℕ} (a b : ℝ)
    (hf : AdmissibleObjective q d) (xMinusOne xZero : Vec d) (t : ℕ) :
    Vec d :=
  (hbStateAt a b hf xMinusOne xZero t).2

theorem hbStateAt_zero {q : ℝ} {d : ℕ} (a b : ℝ)
    (hf : AdmissibleObjective q d) (xMinusOne xZero : Vec d) :
    hbStateAt a b hf xMinusOne xZero 0 = (xMinusOne, xZero) := by
  rfl

theorem hbStateAt_succ {q : ℝ} {d : ℕ} (a b : ℝ)
    (hf : AdmissibleObjective q d) (xMinusOne xZero : Vec d) (t : ℕ) :
    hbStateAt a b hf xMinusOne xZero (t + 1) =
      hbStateMap a b hf (hbStateAt a b hf xMinusOne xZero t) := by
  rfl

theorem hbIterate_zero {q : ℝ} {d : ℕ} (a b : ℝ)
    (hf : AdmissibleObjective q d) (xMinusOne xZero : Vec d) :
    hbIterate a b hf xMinusOne xZero 0 = xZero := by
  rfl

/-- Centered state norm squared, the source norm-square on pairs. -/
def centeredStateNormSq {d : ℕ} (Y : HBState d) : ℝ :=
  ‖Y.1‖ ^ 2 + ‖Y.2‖ ^ 2

/-- The centered two-state update `T_f`. -/
def hbCenteredMap {q : ℝ} {d : ℕ} (hq : 0 < q) (a b : ℝ)
    (hf : AdmissibleObjective q d) (Y : HBState d) : HBState d :=
  let xStar := objectiveMinimizer hq hf
  (Y.2, hbSuccessor a b hf (xStar + Y.1) (xStar + Y.2) - xStar)

/-- Initial centered state `(x_{-1}-x_*, x_0-x_*)`.

Book source: `definitions/HB-centered-state-sequence` says `Y_t=(x_{t-1},x_t)`
after translating the minimizer and minimum to zero. This declaration performs
the undoing of that translation for arbitrary source coordinates. -/
def hbInitialCenteredState {q : ℝ} {d : ℕ} (hq : 0 < q)
    (hf : AdmissibleObjective q d) (xMinusOne xZero : Vec d) : HBState d :=
  let xStar := objectiveMinimizer hq hf
  (xMinusOne - xStar, xZero - xStar)

/-- Centered generated state sequence `Y_t` driven by the source map `T_f`.

This is the D10/D11 state sequence, not the uncentered actual pair
`(x_{t-1}, x_t)`. -/
def hbCenteredStateAt {q : ℝ} {d : ℕ} (hq : 0 < q) (a b : ℝ)
    (hf : AdmissibleObjective q d) (xMinusOne xZero : Vec d) (t : ℕ) :
    HBState d :=
  (hbCenteredMap hq a b hf)^[t]
    (hbInitialCenteredState hq hf xMinusOne xZero)

theorem hbCenteredStateAt_zero {q : ℝ} {d : ℕ} (hq : 0 < q) (a b : ℝ)
    (hf : AdmissibleObjective q d) (xMinusOne xZero : Vec d) :
    hbCenteredStateAt hq a b hf xMinusOne xZero 0 =
      hbInitialCenteredState hq hf xMinusOne xZero := by
  rfl

theorem hbCenteredStateAt_succ {q : ℝ} {d : ℕ} (hq : 0 < q) (a b : ℝ)
    (hf : AdmissibleObjective q d) (xMinusOne xZero : Vec d) (t : ℕ) :
    hbCenteredStateAt hq a b hf xMinusOne xZero (t + 1) =
      hbCenteredMap hq a b hf
        (hbCenteredStateAt hq a b hf xMinusOne xZero t) := by
  simpa [hbCenteredStateAt, Nat.succ_eq_add_one] using
    (Function.iterate_succ_apply' (hbCenteredMap hq a b hf) t
      (hbInitialCenteredState hq hf xMinusOne xZero))

/-- Bridge from the source centered map orbit back to the generated actual
trajectory with `x_*` subtracted. This is a proof obligation, not a primitive
assumption. -/
theorem hbCenteredStateAt_eq_centered_hbStateAt {q : ℝ} {d : ℕ}
    (hq : 0 < q) (a b : ℝ) (hf : AdmissibleObjective q d)
    (xMinusOne xZero : Vec d) (t : ℕ) :
    let xStar := objectiveMinimizer hq hf
    hbCenteredStateAt hq a b hf xMinusOne xZero t =
      ((hbStateAt a b hf xMinusOne xZero t).1 - xStar,
        (hbStateAt a b hf xMinusOne xZero t).2 - xStar) := by
  let xStar := objectiveMinimizer hq hf
  have hstep : ∀ u v : Vec d,
      hbCenteredMap hq a b hf (u - xStar, v - xStar) =
        (v - xStar, hbSuccessor a b hf u v - xStar) := by
    intro u v
    simp [hbCenteredMap, xStar, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  induction t with
  | zero =>
      simp [hbCenteredStateAt_zero, hbInitialCenteredState, hbStateAt_zero, xStar]
  | succ t ih =>
      rw [hbCenteredStateAt_succ, hbStateAt_succ]
      rw [ih]
      cases hY : hbStateAt a b hf xMinusOne xZero t with
      | mk u v =>
          simpa [hbStateMap, hY] using hstep u v

/-- Infinite centered trajectory energy `E_f(Y)=sum ||T_f^jY||^2`. -/
def hbCenteredEnergyInfinite {q : ℝ} {d : ℕ} (hq : 0 < q) (a b : ℝ)
    (hf : AdmissibleObjective q d) (Y : HBState d) : ℝ :=
  ∑' j : ℕ, centeredStateNormSq
    ((hbCenteredMap hq a b hf)^[j] Y)

/-- Finite centered trajectory energy
`E_{f,N}(Y)=sum_{k=0}^{N-1} ||T_f^kY||^2`. -/
def hbCenteredEnergyFinite {q : ℝ} {d : ℕ} (hq : 0 < q) (a b : ℝ)
    (hf : AdmissibleObjective q d) (N : ℕ) (Y : HBState d) : ℝ :=
  ∑ k ∈ Finset.range N,
    centeredStateNormSq ((hbCenteredMap hq a b hf)^[k] Y)

theorem hbCenteredEnergy_iterate_zero {q : ℝ} {d : ℕ} (hq : 0 < q) (a b : ℝ)
    (hf : AdmissibleObjective q d) (Y : HBState d) :
    (hbCenteredMap hq a b hf)^[0] Y = Y := by
  rfl

theorem hbCenteredEnergy_iterate_succ {q : ℝ} {d : ℕ} (hq : 0 < q) (a b : ℝ)
    (hf : AdmissibleObjective q d) (n : ℕ) (Y : HBState d) :
    (hbCenteredMap hq a b hf)^[n + 1] Y =
      hbCenteredMap hq a b hf ((hbCenteredMap hq a b hf)^[n] Y) := by
  simpa [Nat.succ_eq_add_one] using
    (Function.iterate_succ_apply' (hbCenteredMap hq a b hf) n Y)

/-- The scalar terms of the infinite centered energy series
`||T_f^j Y||^2`. -/
def hbCenteredOrbitEnergyTerm {q : ℝ} {d : ℕ} (hq : 0 < q) (a b : ℝ)
    (hf : AdmissibleObjective q d) (Y : HBState d) (j : ℕ) : ℝ :=
  centeredStateNormSq ((hbCenteredMap hq a b hf)^[j] Y)

theorem hbCenteredOrbitEnergyTerm_def {q : ℝ} {d : ℕ} (hq : 0 < q) (a b : ℝ)
    (hf : AdmissibleObjective q d) (Y : HBState d) (j : ℕ) :
    hbCenteredOrbitEnergyTerm hq a b hf Y j =
      centeredStateNormSq ((hbCenteredMap hq a b hf)^[j] Y) := by
  rfl

/-- Source-facing convergence boundary for `E_f(Y)`: the centered orbit energy
series is summable before its `tsum` value is used. -/
def hbCenteredOrbitSummable {q : ℝ} {d : ℕ} (hq : 0 < q) (a b : ℝ)
    (hf : AdmissibleObjective q d) (Y : HBState d) : Prop :=
  Summable (hbCenteredOrbitEnergyTerm hq a b hf Y)

/-- The source infinite energy value is the sum of the convergent centered orbit
energy series. -/
def hbCenteredOrbitHasEnergy {q : ℝ} {d : ℕ} (hq : 0 < q) (a b : ℝ)
    (hf : AdmissibleObjective q d) (Y : HBState d) : Prop :=
  HasSum (hbCenteredOrbitEnergyTerm hq a b hf Y)
    (hbCenteredEnergyInfinite hq a b hf Y)

/-- Tail terms `||T_f^{j+N} Y||^2` used in the source D10/D11 tail estimate. -/
def hbCenteredTailEnergyTerm {q : ℝ} {d : ℕ} (hq : 0 < q) (a b : ℝ)
    (hf : AdmissibleObjective q d) (N : ℕ) (Y : HBState d) (j : ℕ) : ℝ :=
  hbCenteredOrbitEnergyTerm hq a b hf Y (j + N)

/-- Source-facing convergence boundary for a centered tail energy series. -/
def hbCenteredTailSummable {q : ℝ} {d : ℕ} (hq : 0 < q) (a b : ℝ)
    (hf : AdmissibleObjective q d) (N : ℕ) (Y : HBState d) : Prop :=
  Summable (hbCenteredTailEnergyTerm hq a b hf N Y)

/-- The real value of the centered tail energy, used only after the tail
summability boundary has been stated. -/
def hbCenteredTailEnergy {q : ℝ} {d : ℕ} (hq : 0 < q) (a b : ℝ)
    (hf : AdmissibleObjective q d) (N : ℕ) (Y : HBState d) : ℝ :=
  ∑' j : ℕ, hbCenteredTailEnergyTerm hq a b hf N Y j

/-- The tail energy value is the sum of its convergent series. -/
def hbCenteredTailHasEnergy {q : ℝ} {d : ℕ} (hq : 0 < q) (a b : ℝ)
    (hf : AdmissibleObjective q d) (N : ℕ) (Y : HBState d) : Prop :=
  HasSum (hbCenteredTailEnergyTerm hq a b hf N Y)
    (hbCenteredTailEnergy hq a b hf N Y)

/-- Source statement that the continuous partial sums defining `E_f` converge
uniformly on every bounded centered-state set. -/
def hbCenteredEnergyPartialSumsUniformOnBounded
    {q : ℝ} {d : ℕ} (hq : 0 < q) (a b : ℝ)
    (hf : AdmissibleObjective q d) : Prop :=
  ∀ R : ℝ, 0 ≤ R →
    TendstoUniformlyOn
      (fun N Y => hbCenteredEnergyFinite hq a b hf N Y)
      (hbCenteredEnergyInfinite hq a b hf)
      atTop
      {Y : HBState d | centeredStateNormSq Y ≤ R}

/-- Four indices `*,0,1,2` for interpolation/record data. -/
inductive RecordIndex
  | star
  | zero
  | one
  | two
  deriving DecidableEq, Fintype

/-- Finite interpolation data `(x_i,g_i,F_i)`. -/
structure FiniteData (d : ℕ) where
  x : RecordIndex → Vec d
  g : RecordIndex → Vec d
  F : RecordIndex → ℝ

/-- The ordered interpolation residual `(I)`. -/
def interpolationResidual {d : ℕ} (q : ℝ) (data : FiniteData d)
    (i j : RecordIndex) : ℝ :=
  data.F i - data.F j - inner ℝ (data.g j) (data.x i - data.x j) -
    ((‖data.g i - data.g j‖ ^ 2 + q * ‖data.x i - data.x j‖ ^ 2 -
        2 * q * inner ℝ (data.g i - data.g j) (data.x i - data.x j)) /
      (2 * (1 - q)))

def FiniteDataRealizable {d : ℕ} (q : ℝ) (data : FiniteData d) : Prop :=
  ∃ hf : AdmissibleObjective q d,
    ∀ i : RecordIndex,
      hf.f (data.x i) = data.F i ∧ gradient hf.f (data.x i) = data.g i

private theorem hb_shifted_model_gap_identity
    {q : ℝ} {d : ℕ} (hf : AdmissibleObjective q d) (x y : Vec d) :
    (hf.f x - (q / 2) * ‖x‖ ^ 2) - (hf.f y - (q / 2) * ‖y‖ ^ 2) -
          inner ℝ (gradient hf.f y - q • y) (x - y) =
      (hf.f x - hf.f y - inner ℝ (gradient hf.f y) (x - y)) -
        (q / 2) * ‖x - y‖ ^ 2 := by
  have hquad :
      (q / 2) * ‖x - y‖ ^ 2 =
        (q / 2) * (‖x‖ ^ 2 - ‖y‖ ^ 2) -
          inner ℝ (q • y) (x - y) := by
    rw [norm_sub_sq_real, inner_sub_right]
    have hqyx : inner ℝ (q • y) x = q * inner ℝ y x := by
      exact real_inner_smul_left y x q
    have hqyy : inner ℝ (q • y) y = q * ‖y‖ ^ 2 := by
      calc
        inner ℝ (q • y) y = q * inner ℝ y y := real_inner_smul_left y y q
        _ = q * ‖y‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
    rw [hqyx, hqyy, real_inner_comm y x]
    ring
  rw [inner_sub_left]
  have hqinner :
      inner ℝ (q • y) (x - y) = q * inner ℝ y (x - y) :=
    real_inner_smul_left y (x - y) q
  rw [hqinner]
  have hquad' := hquad
  rw [hqinner] at hquad'
  nlinarith only [hquad']

private theorem hb_shifted_support_and_smooth_upper
    {q : ℝ} {d : ℕ} (hf : AdmissibleObjective q d) (x y : Vec d) :
    0 ≤
        (hf.f x - (q / 2) * ‖x‖ ^ 2) -
          (hf.f y - (q / 2) * ‖y‖ ^ 2) -
            inner ℝ (gradient hf.f y - q • y) (x - y) ∧
      (hf.f x - (q / 2) * ‖x‖ ^ 2) -
          (hf.f y - (q / 2) * ‖y‖ ^ 2) -
            inner ℝ (gradient hf.f y - q • y) (x - y) ≤
        ((1 - q) / 2) * ‖x - y‖ ^ 2 := by
  have hgap_identity := hb_shifted_model_gap_identity hf x y
  have hstrong := hf.strongConvex_lower y x
  have hstrong_gap :
      (q / 2) * ‖x - y‖ ^ 2 ≤
        hf.f x - hf.f y - inner ℝ (gradient hf.f y) (x - y) := by
    linarith only [hstrong]
  have hsmooth_carrier :=
    Convex.carrier_smooth_quadratic_upper_bound_of_hasGradientWithinAt_lipschitz
      (X := Set.univ)
      (f := fun z : {x : Vec d // x ∈ Set.univ} => hf.f z.1)
      (F := hf.f)
      (grad := fun z : {x : Vec d // x ∈ Set.univ} => gradient hf.f z.1)
      (L := (1 : ℝ))
      (convex_univ)
      (by intro z hz; rfl)
      (by
        intro z
        simpa [hasGradientWithinAt_univ] using
          (HB_admissible_objective_hasGradientAt hf z.1))
      (by
        intro a b
        simpa [one_mul] using hf.gradient_lipschitz a.1 b.1)
      ⟨x, by simp⟩ ⟨y, by simp⟩
  have hsmooth_gap :
      hf.f x - hf.f y - inner ℝ (gradient hf.f y) (x - y) ≤
        (1 / 2 : ℝ) * ‖x - y‖ ^ 2 := by
    simpa using hsmooth_carrier
  constructor
  · rw [hgap_identity]
    linarith only [hstrong_gap]
  · rw [hgap_identity]
    have hcoef :
        (1 / 2 : ℝ) * ‖x - y‖ ^ 2 - (q / 2) * ‖x - y‖ ^ 2 =
          ((1 - q) / 2) * ‖x - y‖ ^ 2 := by
      ring
    linarith only [hsmooth_gap, hcoef]

private theorem hb_cocoercive_of_support_and_smooth_upper {d : ℕ}
    {psi : Vec d → ℝ} {p : Vec d → Vec d} {L : ℝ} (hL : 0 < L)
    (hsupport : ∀ x y : Vec d, 0 ≤ psi x - psi y - inner ℝ (p y) (x - y))
    (hupper :
      ∀ x y : Vec d,
        psi x - psi y - inner ℝ (p y) (x - y) ≤ (L / 2) * ‖x - y‖ ^ 2)
    (u v : Vec d) :
    (1 / (2 * L)) * ‖p u - p v‖ ^ 2 ≤
      psi u - psi v - inner ℝ (p v) (u - v) := by
  let r : Vec d := p u - p v
  let z : Vec d := u - (1 / L) • r
  have hstep :
      psi v + inner ℝ (p v) (z - v) ≤
        psi u + inner ℝ (p u) (z - u) + (L / 2) * ‖z - u‖ ^ 2 := by
    have hsupport_zv := hsupport z v
    have hupper_zu := hupper z u
    linarith only [hsupport_zv, hupper_zu]
  have hzinv_pos : 0 < (1 / L : ℝ) := one_div_pos.mpr hL
  have hnorm_zu :
      ‖z - u‖ ^ 2 = (1 / L) ^ 2 * ‖r‖ ^ 2 := by
    have hzu : z - u = -((1 / L) • r) := by
      simp [z, sub_eq_add_neg, add_assoc]
    rw [hzu, norm_neg, norm_smul]
    rw [Real.norm_eq_abs, abs_of_pos hzinv_pos]
    ring
  have hmain :
      psi v + inner ℝ (p v) (u - v) + (1 / L) * ‖r‖ ^ 2 ≤
        psi u + (L / 2) * ((1 / L) ^ 2 * ‖r‖ ^ 2) := by
    have hzv : z - v = (u - v) - (1 / L) • r := by
      simp [z, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    have hzu : z - u = -((1 / L) • r) := by
      simp [z, sub_eq_add_neg, add_assoc]
    have hleft :
        inner ℝ (p v) (z - v) =
          inner ℝ (p v) (u - v) - (1 / L) * inner ℝ (p v) r := by
      rw [hzv, inner_sub_right, inner_smul_right]
    have hright :
        inner ℝ (p u) (z - u) = - (1 / L) * inner ℝ (p u) r := by
      rw [hzu, inner_neg_right, inner_smul_right]
      ring
    have hrnorm :
        inner ℝ (p u) r - inner ℝ (p v) r = ‖r‖ ^ 2 := by
      have hpu : p u = r + p v := by
        simp [r, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      rw [hpu, inner_add_left, real_inner_self_eq_norm_sq]
      ring
    have hrnorm_scaled :
        (1 / L) * inner ℝ (p u) r - (1 / L) * inner ℝ (p v) r =
          (1 / L) * ‖r‖ ^ 2 := by
      calc
        (1 / L) * inner ℝ (p u) r - (1 / L) * inner ℝ (p v) r =
            (1 / L) * (inner ℝ (p u) r - inner ℝ (p v) r) := by ring
        _ = (1 / L) * ‖r‖ ^ 2 := by rw [hrnorm]
    have hstep' := hstep
    rw [hleft, hright, hnorm_zu] at hstep'
    linarith only [hstep', hrnorm_scaled]
  have hL_ne : L ≠ 0 := ne_of_gt hL
  have hcoef :
      (L / 2) * ((1 / L) ^ 2 * ‖r‖ ^ 2) =
        (1 / (2 * L)) * ‖r‖ ^ 2 := by
    field_simp [hL_ne]
  rw [hcoef] at hmain
  have hcoef_one :
      (1 / L) * ‖r‖ ^ 2 =
        2 * ((1 / (2 * L)) * ‖r‖ ^ 2) := by
    field_simp [hL_ne]
  rw [hcoef_one] at hmain
  change (1 / (2 * L)) * ‖r‖ ^ 2 ≤
    psi u - psi v - inner ℝ (p v) (u - v)
  linarith only [hmain]

private theorem hb_interpolation_shifted_cocoercive
    {q : ℝ} {d : ℕ} (hq0 : 0 < q) (hq1 : q < 1)
    (hf : AdmissibleObjective q d)
    (u v : Vec d) :
    (1 / (2 * (1 - q))) *
          ‖(gradient hf.f u - q • u) - (gradient hf.f v - q • v)‖ ^ 2 ≤
      (hf.f u - (q / 2) * ‖u‖ ^ 2) -
          (hf.f v - (q / 2) * ‖v‖ ^ 2) -
        inner ℝ (gradient hf.f v - q • v) (u - v) := by
  let psi := fun z : Vec d => hf.f z - (q / 2) * ‖z‖ ^ 2
  let p := fun z : Vec d => gradient hf.f z - q • z
  have hL : 0 < 1 - q := by
    linarith only [hq1]
  have hsupport :
      ∀ x y : Vec d, 0 ≤ psi x - psi y - inner ℝ (p y) (x - y) := by
    intro x y
    simpa [psi, p] using (hb_shifted_support_and_smooth_upper hf x y).1
  have hupper :
      ∀ x y : Vec d,
        psi x - psi y - inner ℝ (p y) (x - y) ≤
          ((1 - q) / 2) * ‖x - y‖ ^ 2 := by
    intro x y
    simpa [psi, p] using (hb_shifted_support_and_smooth_upper hf x y).2
  let L : ℝ := 1 - q
  have hL' : 0 < L := by
    dsimp [L]
    exact hL
  simpa [L, p, psi] using
    hb_cocoercive_of_support_and_smooth_upper
      (d := d) (psi := psi) (p := p) (L := L)
      hL' hsupport hupper u v

private theorem hb_interpolation_residual_nonneg_of_shifted_cocoercive
    {q : ℝ} {d : ℕ} (hq0 : 0 < q) (hq1 : q < 1) (data : FiniteData d)
    (i j : RecordIndex)
    (hci :
      (1 / (2 * (1 - q))) *
          ‖(data.g i - q • data.x i) - (data.g j - q • data.x j)‖ ^ 2 ≤
        (data.F i - (q / 2) * ‖data.x i‖ ^ 2) -
            (data.F j - (q / 2) * ‖data.x j‖ ^ 2) -
          inner ℝ (data.g j - q • data.x j)
            (data.x i - data.x j)) :
    0 ≤ interpolationResidual q data i j := by
  let dx : Vec d := data.x i - data.x j
  let dg : Vec d := data.g i - data.g j
  have hnorm_shift :
      ‖(data.g i - q • data.x i) - (data.g j - q • data.x j)‖ ^ 2 =
        ‖dg‖ ^ 2 + q ^ 2 * ‖dx‖ ^ 2 -
          2 * q * inner ℝ dg dx := by
    have hvec :
        (data.g i - q • data.x i) - (data.g j - q • data.x j) =
          dg - q • dx := by
      simp [dx, dg, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [hvec, norm_sub_sq_real, inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos hq0]
    ring
  have hnorm_x :
      (q / 2) * (‖data.x i‖ ^ 2 - ‖data.x j‖ ^ 2) -
          inner ℝ (q • data.x j) dx =
        (q / 2) * ‖dx‖ ^ 2 := by
    have hbase :
        ‖data.x i - data.x j‖ ^ 2 =
          ‖data.x i‖ ^ 2 + ‖data.x j‖ ^ 2 -
            2 * inner ℝ (data.x i) (data.x j) := by
      rw [norm_sub_sq_real]
      ring
    dsimp [dx]
    rw [hbase, inner_smul_left, inner_sub_right]
    simp
    rw [real_inner_comm (data.x i) (data.x j)]
    ring
  have hrewrite :
      (data.F i - (q / 2) * ‖data.x i‖ ^ 2) -
            (data.F j - (q / 2) * ‖data.x j‖ ^ 2) -
          inner ℝ (data.g j - q • data.x j) dx -
          (1 / (2 * (1 - q))) *
            ‖(data.g i - q • data.x i) -
              (data.g j - q • data.x j)‖ ^ 2 =
        interpolationResidual q data i j := by
    have hnorm_x' :
        -(q / 2) * ‖data.x i‖ ^ 2 + (q / 2) * ‖data.x j‖ ^ 2 +
            inner ℝ (q • data.x j) (data.x i - data.x j) =
          -(q / 2) * ‖data.x i - data.x j‖ ^ 2 := by
      have hnorm_x'' :
          (q / 2) * (‖data.x i‖ ^ 2 - ‖data.x j‖ ^ 2) -
              inner ℝ (q • data.x j) (data.x i - data.x j) =
            (q / 2) * ‖data.x i - data.x j‖ ^ 2 := by
        simpa [dx] using hnorm_x
      nlinarith [hnorm_x'']
    calc
      (data.F i - (q / 2) * ‖data.x i‖ ^ 2) -
            (data.F j - (q / 2) * ‖data.x j‖ ^ 2) -
          inner ℝ (data.g j - q • data.x j) dx -
          (1 / (2 * (1 - q))) *
            ‖(data.g i - q • data.x i) -
              (data.g j - q • data.x j)‖ ^ 2 =
        data.F i - data.F j - inner ℝ (data.g j) (data.x i - data.x j) -
          (q / 2) * ‖data.x i - data.x j‖ ^ 2 -
          (1 / (2 * (1 - q))) *
            (‖data.g i - data.g j‖ ^ 2 +
              q ^ 2 * ‖data.x i - data.x j‖ ^ 2 -
              2 * q * inner ℝ (data.g i - data.g j)
                (data.x i - data.x j)) := by
          rw [hnorm_shift, inner_sub_left]
          dsimp [dx, dg]
          nlinarith [hnorm_x']
      _ = interpolationResidual q data i j := by
        dsimp [interpolationResidual]
        have hqpos : 0 < 1 - q := by linarith
        field_simp [ne_of_gt hqpos]
        ring
  have hnonneg :
      0 ≤
        (data.F i - (q / 2) * ‖data.x i‖ ^ 2) -
            (data.F j - (q / 2) * ‖data.x j‖ ^ 2) -
          inner ℝ (data.g j - q • data.x j) dx -
          (1 / (2 * (1 - q))) *
            ‖(data.g i - q • data.x i) -
              (data.g j - q • data.x j)‖ ^ 2 := by
    have hqpos : 0 < 1 - q := by linarith
    nlinarith [hci]
  rw [hrewrite] at hnonneg
  exact hnonneg

private def shiftedGradient (q : ℝ) {d : ℕ} (data : FiniteData d)
    (i : RecordIndex) : Vec d :=
  data.g i - q • data.x i

private def shiftedValue (q : ℝ) {d : ℕ} (data : FiniteData d)
    (i : RecordIndex) : ℝ :=
  data.F i - (q / 2) * ‖data.x i‖ ^ 2

private def quadraticPiece (q ell : ℝ) {d : ℕ} (data : FiniteData d)
    (i : RecordIndex) (p : Vec d) : ℝ :=
  inner ℝ p (data.x i) - shiftedValue q data i +
    (1 / (2 * ell)) * ‖p - shiftedGradient q data i‖ ^ 2

private theorem quadratic_piece_active_at_shifted_gradient
    {q ell : ℝ} {d : ℕ} (hq1 : q < 1) (ell_pos : 0 < ell)
    (hell : ell = 1 - q) (data : FiniteData d)
    (hres : ∀ i j : RecordIndex, 0 ≤ interpolationResidual q data i j) :
    ∀ i j : RecordIndex,
      quadraticPiece q ell data i (shiftedGradient q data i) -
          quadraticPiece q ell data j (shiftedGradient q data i) =
        interpolationResidual q data j i := by
  intro i j
  have hnorm_shift :
      ‖shiftedGradient q data i - shiftedGradient q data j‖ ^ 2 =
        ‖data.g i - data.g j‖ ^ 2 +
            q ^ 2 * ‖data.x i - data.x j‖ ^ 2 -
          2 * q * inner ℝ (data.g i - data.g j)
            (data.x i - data.x j) := by
    have hvec :
        shiftedGradient q data i - shiftedGradient q data j =
          (data.g i - data.g j) - q • (data.x i - data.x j) := by
      simp [shiftedGradient, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [hvec, norm_sub_sq_real, inner_smul_right, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hnorm_x :
      (q / 2) * (‖data.x i‖ ^ 2 - ‖data.x j‖ ^ 2) -
          inner ℝ (q • data.x i) (data.x i - data.x j) =
        -(q / 2) * ‖data.x i - data.x j‖ ^ 2 := by
    rw [norm_sub_sq_real, inner_sub_right]
    rw [real_inner_smul_left, real_inner_smul_left]
    simp only [real_inner_self_eq_norm_sq]
    ring
  have hrewrite :
      quadraticPiece q ell data i (shiftedGradient q data i) -
          quadraticPiece q ell data j (shiftedGradient q data i) =
        data.F j - data.F i -
            inner ℝ (data.g i) (data.x j - data.x i) -
          (q / 2) * ‖data.x i - data.x j‖ ^ 2 -
          (1 / (2 * ell)) *
            (‖data.g i - data.g j‖ ^ 2 +
                q ^ 2 * ‖data.x i - data.x j‖ ^ 2 -
              2 * q * inner ℝ (data.g i - data.g j)
                (data.x i - data.x j)) := by
    unfold quadraticPiece shiftedValue
    simp [sub_self, norm_zero]
    rw [hnorm_shift]
    dsimp [shiftedGradient]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
    have hnorm_x' := hnorm_x
    rw [inner_sub_right, real_inner_smul_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq] at hnorm_x'
    simp at hnorm_x' ⊢
    have hinner_g :
        inner ℝ (data.g i) (data.x i - data.x j) =
          -inner ℝ (data.g i) (data.x j - data.x i) := by
      rw [inner_sub_right, inner_sub_right]
      ring
    nlinarith [hnorm_x', hinner_g]
  rw [hrewrite]
  unfold interpolationResidual
  rw [hell]
  have hell_ne : 1 - q ≠ 0 := ne_of_gt (by linarith)
  field_simp [hell_ne]
  rw [norm_sub_rev (data.g j) (data.g i),
    norm_sub_rev (data.x j) (data.x i)]
  have hinner_rev :
      inner ℝ (data.g j - data.g i) (data.x j - data.x i) =
        inner ℝ (data.g i - data.g j) (data.x i - data.x j) := by
    have hgj : data.g j - data.g i = -(data.g i - data.g j) := by
      abel
    have hxj : data.x j - data.x i = -(data.x i - data.x j) := by
      abel
    rw [hgj, hxj, inner_neg_left, inner_neg_right]
    simp
  rw [hinner_rev]
  ring

private theorem quadratic_piece_image_nonempty
    {q ell : ℝ} {d : ℕ} (data : FiniteData d) (p : Vec d) :
    (Finset.univ.image (fun i => quadraticPiece q ell data i p)).Nonempty := by
  classical
  exact ⟨quadraticPiece q ell data RecordIndex.star p, by simp⟩

private noncomputable def quadraticEnvelope
    (q ell : ℝ) {d : ℕ} (data : FiniteData d) (p : Vec d) : ℝ :=
  (Finset.univ.image (fun i => quadraticPiece q ell data i p)).max'
    (quadratic_piece_image_nonempty data p)

private theorem quadratic_envelope_active_at_shifted_gradient
    {q ell : ℝ} {d : ℕ} (hq1 : q < 1) (ell_pos : 0 < ell)
    (hell : ell = 1 - q) (data : FiniteData d)
    (hres : ∀ i j : RecordIndex, 0 ≤ interpolationResidual q data i j) :
    ∀ i : RecordIndex,
      quadraticEnvelope q ell data (shiftedGradient q data i) =
        quadraticPiece q ell data i (shiftedGradient q data i) := by
  intro i
  have hle :
      ∀ j : RecordIndex,
        quadraticPiece q ell data j (shiftedGradient q data i) ≤
          quadraticPiece q ell data i (shiftedGradient q data i) := by
    intro j
    have hdiff :=
      quadratic_piece_active_at_shifted_gradient
        hq1 ell_pos hell data hres i j
    have hnonneg := hres j i
    linarith
  apply le_antisymm
  · unfold quadraticEnvelope
    apply Finset.max'_le
    intro value hvalue
    rcases Finset.mem_image.mp hvalue with ⟨j, _hj, rfl⟩
    exact hle j
  · unfold quadraticEnvelope
    exact Finset.le_max'
      (Finset.univ.image
        (fun j => quadraticPiece q ell data j
          (shiftedGradient q data i)))
      (quadraticPiece q ell data i (shiftedGradient q data i))
      (by simp)

private theorem quadratic_envelope_coercive_lower_tail
    {q ell : ℝ} {d : ℕ} (ell_pos : 0 < ell) (data : FiniteData d)
    (x : Vec d) :
    ∀ B : ℝ, ∃ R : ℝ,
      ‖(0 : Vec d) - shiftedGradient q data RecordIndex.star‖ ≤ R ∧
        ∀ p : Vec d, p ∈ (Set.univ : Set (Vec d)) →
          R ≤ ‖p - shiftedGradient q data RecordIndex.star‖ →
            B ≤ quadraticEnvelope q ell data p - inner ℝ x p := by
  intro B
  let z : Vec d := shiftedGradient q data RecordIndex.star
  let a : ℝ := 1 / (2 * ell)
  let g : Vec d := data.x RecordIndex.star - x
  let ell' : Vec d →L[ℝ] ℝ := InnerProductSpace.toDual ℝ (Vec d) g
  let c : ℝ := -shiftedValue q data RecordIndex.star
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hF_lower :
      ∀ p : Vec d, p ∈ (Set.univ : Set (Vec d)) →
        a * ‖p - z‖ ^ 2 + ell' p + c + 0 ≤
          quadraticEnvelope q ell data p - inner ℝ x p := by
    intro p hp
    have hpiece :
        quadraticPiece q ell data RecordIndex.star p ≤
          quadraticEnvelope q ell data p := by
      unfold quadraticEnvelope
      exact Finset.le_max'
        (Finset.univ.image (fun i => quadraticPiece q ell data i p))
        (quadraticPiece q ell data RecordIndex.star p)
        (by simp)
    have hmodel :
        a * ‖p - z‖ ^ 2 + ell' p + c + 0 =
          quadraticPiece q ell data RecordIndex.star p - inner ℝ x p := by
      dsimp [a, z, g, ell', c]
      unfold quadraticPiece
      simp only [InnerProductSpace.toDual_apply_apply, inner_sub_left]
      rw [real_inner_comm (data.x RecordIndex.star) p]
      ring
    rw [hmodel]
    linarith
  obtain ⟨R0, hR0_nonneg, hR0_tail⟩ :=
    exists_nonneg_forall_le_quadratic_sub_linear_of_pos
      (a := a) ha ‖ell'‖ (ell' z + c) B
  let R : ℝ := max R0 ‖(0 : Vec d) - z‖
  refine ⟨R, ?_, ?_⟩
  · dsimp [R]
    exact le_max_right _ _
  · intro p hp hfar
    have hR0_le_R : R0 ≤ R := by
      dsimp [R]
      exact le_max_left _ _
    have hR0_le_norm : R0 ≤ ‖p - z‖ := le_trans hR0_le_R hfar
    have hscalar :
        B ≤ a * ‖p - z‖ ^ 2 - ‖ell'‖ * ‖p - z‖ +
            (ell' z + c) :=
      hR0_tail ‖p - z‖ hR0_le_norm
    have hell_abs : |ell' (p - z)| ≤ ‖ell'‖ * ‖p - z‖ := by
      simpa [Real.norm_eq_abs] using ell'.le_opNorm (p - z)
    have hell_lower : -(‖ell'‖ * ‖p - z‖) ≤ ell' (p - z) := by
      have hneg_abs : -ell' (p - z) ≤ |ell' (p - z)| := neg_le_abs _
      linarith
    have hell_decomp : ell' p = ell' z + ell' (p - z) := by
      rw [map_sub]
      abel
    have hlinear :
        ell' z + c - ‖ell'‖ * ‖p - z‖ ≤ ell' p + c := by
      nlinarith
    have hmodel :
        B ≤ a * ‖p - z‖ ^ 2 + ell' p + c + 0 := by
      nlinarith
    exact le_trans hmodel (hF_lower p hp)

private theorem quadraticEnvelope_four_eq_max
    {q ell : ℝ} {d : ℕ} (data : FiniteData d) (p : Vec d) :
    quadraticEnvelope q ell data p =
      max (quadraticPiece q ell data RecordIndex.star p)
        (max (quadraticPiece q ell data RecordIndex.zero p)
          (max (quadraticPiece q ell data RecordIndex.one p)
            (quadraticPiece q ell data RecordIndex.two p))) := by
  unfold quadraticEnvelope
  apply le_antisymm
  · apply Finset.max'_le
    intro value hvalue
    rcases Finset.mem_image.mp hvalue with ⟨i, _hi, rfl⟩
    cases i <;> simp
  · apply max_le
    · exact Finset.le_max'
        (Finset.univ.image (fun i => quadraticPiece q ell data i p))
        (quadraticPiece q ell data RecordIndex.star p)
        (by simp)
    · apply max_le
      · exact Finset.le_max'
          (Finset.univ.image (fun i => quadraticPiece q ell data i p))
          (quadraticPiece q ell data RecordIndex.zero p)
          (by simp)
      · apply max_le
        · exact Finset.le_max'
            (Finset.univ.image (fun i => quadraticPiece q ell data i p))
            (quadraticPiece q ell data RecordIndex.one p)
            (by simp)
        · exact Finset.le_max'
            (Finset.univ.image (fun i => quadraticPiece q ell data i p))
            (quadraticPiece q ell data RecordIndex.two p)
            (by simp)
private theorem quadratic_envelope_continuous
    {q ell : ℝ} {d : ℕ} (data : FiniteData d) :
    Continuous (quadraticEnvelope q ell data) := by
  have henv_eq :
      quadraticEnvelope q ell data =
        fun p : Vec d =>
          max (quadraticPiece q ell data RecordIndex.star p)
            (max (quadraticPiece q ell data RecordIndex.zero p)
              (max (quadraticPiece q ell data RecordIndex.one p)
                (quadraticPiece q ell data RecordIndex.two p))) := by
    funext p
    exact quadraticEnvelope_four_eq_max data p
  rw [henv_eq]
  have hpiece_cont :
      ∀ i : RecordIndex, Continuous (quadraticPiece q ell data i) := by
    intro i
    unfold quadraticPiece
    exact
      ((continuous_id.inner continuous_const).sub continuous_const).add
        (continuous_const.mul
          ((continuous_id.sub continuous_const).norm.pow 2))
  exact
    (hpiece_cont RecordIndex.star).max
      ((hpiece_cont RecordIndex.zero).max
        ((hpiece_cont RecordIndex.one).max (hpiece_cont RecordIndex.two)))

private theorem norm_midpoint_sub_sq_eq
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p r z : E) :
    ‖(1 / 2 : ℝ) • (p + r) - z‖ ^ 2 =
      (‖p - z‖ ^ 2 + ‖r - z‖ ^ 2) / 2 -
        (1 / 4 : ℝ) * ‖p - r‖ ^ 2 := by
  have hvec :
      (1 / 2 : ℝ) • (p + r) - z =
        (1 / 2 : ℝ) • ((p - z) + (r - z)) := by
    module
  have hdiff : (p - z) - (r - z) = p - r := by
    module
  rw [hvec, ← hdiff, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num), mul_pow]
  rw [norm_add_sq_real (p - z) (r - z),
    norm_sub_sq_real (p - z) (r - z)]
  ring

private theorem quadraticPiece_midpoint_eq
    {q ell : ℝ} {d : ℕ} (data : FiniteData d) (i : RecordIndex)
    (p r : Vec d) :
    quadraticPiece q ell data i ((1 / 2 : ℝ) • (p + r)) =
      (quadraticPiece q ell data i p + quadraticPiece q ell data i r) / 2 -
        (1 / (8 * ell)) * ‖p - r‖ ^ 2 := by
  unfold quadraticPiece
  rw [norm_midpoint_sub_sq_eq]
  simp [smul_add, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right]
  ring

private theorem quadratic_envelope_midpoint_strong
    {q ell : ℝ} {d : ℕ} (ell_pos : 0 < ell) (data : FiniteData d) :
    ∀ p r : Vec d,
      quadraticEnvelope q ell data ((1 / 2 : ℝ) • (p + r)) ≤
        (quadraticEnvelope q ell data p +
            quadraticEnvelope q ell data r) / 2 -
          (1 / (8 * ell)) * ‖p - r‖ ^ 2 := by
  intro p r
  apply Finset.max'_le
  intro value hvalue
  rcases Finset.mem_image.mp hvalue with ⟨i, _hi, rfl⟩
  have hpi :
      quadraticPiece q ell data i p ≤ quadraticEnvelope q ell data p := by
    unfold quadraticEnvelope
    exact Finset.le_max'
      (Finset.univ.image (fun j => quadraticPiece q ell data j p))
      (quadraticPiece q ell data i p)
      (by simp)
  have hri :
      quadraticPiece q ell data i r ≤ quadraticEnvelope q ell data r := by
    unfold quadraticEnvelope
    exact Finset.le_max'
      (Finset.univ.image (fun j => quadraticPiece q ell data j r))
      (quadraticPiece q ell data i r)
      (by simp)
  have hnorm :
      ‖(1 / 2 : ℝ) • (p + r) - shiftedGradient q data i‖ ^ 2 =
        (‖p - shiftedGradient q data i‖ ^ 2 +
            ‖r - shiftedGradient q data i‖ ^ 2) / 2 -
          (1 / 4 : ℝ) * ‖p - r‖ ^ 2 := by
    exact norm_midpoint_sub_sq_eq p r (shiftedGradient q data i)
  have hpiece :
      quadraticPiece q ell data i ((1 / 2 : ℝ) • (p + r)) =
        (quadraticPiece q ell data i p +
            quadraticPiece q ell data i r) / 2 -
          (1 / (8 * ell)) * ‖p - r‖ ^ 2 := by
    exact quadraticPiece_midpoint_eq data i p r
  rw [hpiece]
  nlinarith

private theorem norm_affine_combination_sub_sq_eq
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (t : ℝ) (p r z : E) :
    ‖((1 - t) • p + t • r) - z‖ ^ 2 =
      (1 - t) * ‖p - z‖ ^ 2 + t * ‖r - z‖ ^ 2 -
        t * (1 - t) * ‖p - r‖ ^ 2 := by
  have hvec :
      ((1 - t) • p + t • r) - z =
        (1 - t) • (p - z) + t • (r - z) := by
    module
  rw [hvec, norm_add_sq_real, norm_smul, norm_smul,
    Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
  simp [inner_smul_left, inner_smul_right]
  have hnorm :
      ‖p - r‖ ^ 2 =
        ‖p - z‖ ^ 2 - 2 * inner ℝ (p - z) (r - z) +
          ‖r - z‖ ^ 2 := by
    have hvec' : p - r = (p - z) - (r - z) := by
      module
    rw [hvec', norm_sub_sq_real]
  rw [hnorm]
  ring

private theorem quadraticPiece_affine_combination_eq
    {q ell : ℝ} {d : ℕ} (data : FiniteData d) (t : ℝ)
    (p r : Vec d) (i : RecordIndex) :
    quadraticPiece q ell data i ((1 - t) • p + t • r) =
      (1 - t) * quadraticPiece q ell data i p +
        t * quadraticPiece q ell data i r -
          (t * (1 - t) / (2 * ell)) * ‖p - r‖ ^ 2 := by
  unfold quadraticPiece
  rw [norm_affine_combination_sub_sq_eq]
  simp [smul_add, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right]
  ring

private theorem quadratic_envelope_strong_convex
    {q ell : ℝ} {d : ℕ} (ell_pos : 0 < ell) (data : FiniteData d) :
    ∀ {t : ℝ} {p r : Vec d}, 0 ≤ t → t ≤ 1 →
      quadraticEnvelope q ell data ((1 - t) • p + t • r) ≤
        (1 - t) * quadraticEnvelope q ell data p +
          t * quadraticEnvelope q ell data r -
            (t * (1 - t) / (2 * ell)) * ‖p - r‖ ^ 2 := by
  intro t p r ht0 ht1
  apply Finset.max'_le
  intro value hvalue
  rcases Finset.mem_image.mp hvalue with ⟨i, _hi, rfl⟩
  have hpi :
      quadraticPiece q ell data i p ≤ quadraticEnvelope q ell data p := by
    unfold quadraticEnvelope
    exact Finset.le_max'
      (Finset.univ.image (fun j => quadraticPiece q ell data j p))
      (quadraticPiece q ell data i p) (by simp)
  have hri :
      quadraticPiece q ell data i r ≤ quadraticEnvelope q ell data r := by
    unfold quadraticEnvelope
    exact Finset.le_max'
      (Finset.univ.image (fun j => quadraticPiece q ell data j r))
      (quadraticPiece q ell data i r) (by simp)
  have hpiece :=
    quadraticPiece_affine_combination_eq (q := q) (ell := ell) data t p r i
  rw [hpiece]
  nlinarith

private theorem quadratic_envelope_tilted_minimizer
    {q ell : ℝ} {d : ℕ} (ell_pos : 0 < ell) (data : FiniteData d)
    (x : Vec d) :
    ∃! p : Vec d, ∀ r : Vec d,
        quadraticEnvelope q ell data p - inner ℝ x p ≤
        quadraticEnvelope q ell data r - inner ℝ x r := by
  classical
  have hFcont :
      Continuous (fun p : Vec d =>
        quadraticEnvelope q ell data p - inner ℝ x p) := by
    exact (quadratic_envelope_continuous data).sub
      (continuous_const.inner continuous_id)
  have htail : ∃ R : ℝ,
      dist (0 : Vec d) (shiftedGradient q data RecordIndex.star) ≤ R ∧
      ∀ p : Vec d, p ∈ (Set.univ : Set (Vec d)) →
        R ≤ dist p (shiftedGradient q data RecordIndex.star) →
          quadraticEnvelope q ell data 0 - inner ℝ x 0 ≤
            quadraticEnvelope q ell data p - inner ℝ x p := by
    obtain ⟨R, hR, hRtail⟩ :=
      quadratic_envelope_coercive_lower_tail ell_pos data x
        (quadraticEnvelope q ell data 0 - inner ℝ x 0)
    have hR0 : dist (0 : Vec d) (shiftedGradient q data RecordIndex.star) ≤ R := by
      simpa [dist_eq_norm] using hR
    refine ⟨R, ?_, ?_⟩
    · exact hR0
    · intro p hp hfar
      exact hRtail p hp hfar
  obtain ⟨p, hp_univ, hp_min⟩ :=
    exists_isMinOn_of_closed_coercive_closedBall
      (X := Set.univ) isClosed_univ (0 : Vec d)
      (shiftedGradient q data RecordIndex.star) (by simp)
      (fun p : Vec d => quadraticEnvelope q ell data p - inner ℝ x p)
      hFcont.continuousOn htail
  refine ⟨p, ?_, ?_⟩
  · intro r
    have h := hp_min (show r ∈ (Set.univ : Set (Vec d)) by trivial)
    exact h
  · intro r hr
    have hpr := hr p
    have hpr' :
        quadraticEnvelope q ell data p - inner ℝ x p ≤
          quadraticEnvelope q ell data r - inner ℝ x r :=
      hp_min (show r ∈ (Set.univ : Set (Vec d)) by trivial)
    have hpmid :
        quadraticEnvelope q ell data p - inner ℝ x p ≤
          quadraticEnvelope q ell data ((1 / 2 : ℝ) • (p + r)) -
            inner ℝ x ((1 / 2 : ℝ) • (p + r)) :=
      hp_min
        (show ((1 / 2 : ℝ) • (p + r)) ∈ (Set.univ : Set (Vec d)) by trivial)
    have hmid := quadratic_envelope_strong_convex (q := q) ell_pos data
      (t := (1 / 2 : ℝ)) (p := p) (r := r) (by norm_num) (by norm_num)
    have hinner :
        inner ℝ x ((1 / 2 : ℝ) • (p + r)) =
          (inner ℝ x p + inner ℝ x r) / 2 := by
      simp [inner_add_right, inner_smul_right]
      ring
    have hmidvec :
        (1 - (1 / 2 : ℝ)) • p + (1 / 2 : ℝ) • r =
          (1 / 2 : ℝ) • (p + r) := by
      module
    rw [hmidvec] at hmid
    rw [hinner] at hpmid
    have hcoef :
        0 < (1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)) / (2 * ell) := by
      positivity
    have hnorm_zero : ‖p - r‖ ^ 2 = 0 := by
      nlinarith [hmid, hpr, hpr', hpmid, hcoef]
    have hnorm : ‖p - r‖ = 0 := by
      nlinarith [norm_nonneg (p - r)]
    exact (sub_eq_zero.mp (norm_eq_zero.mp hnorm)).symm

private noncomputable def quadraticEnvelopeArgmin
    {q ell : ℝ} {d : ℕ} (ell_pos : 0 < ell) (data : FiniteData d)
    (x : Vec d) : Vec d :=
  Classical.choose (quadratic_envelope_tilted_minimizer (q := q) ell_pos data x)

private theorem quadraticEnvelopeArgmin_is_min
    {q ell : ℝ} {d : ℕ} (ell_pos : 0 < ell) (data : FiniteData d)
    (x : Vec d) :
    ∀ r : Vec d,
      quadraticEnvelope q ell data (quadraticEnvelopeArgmin (q := q) ell_pos data x) -
          inner ℝ x (quadraticEnvelopeArgmin (q := q) ell_pos data x) ≤
        quadraticEnvelope q ell data r - inner ℝ x r :=
  (Classical.choose_spec
    (quadratic_envelope_tilted_minimizer (q := q) ell_pos data x)).1

private theorem quadratic_envelope_tilted_support
    {q ell : ℝ} {d : ℕ} (ell_pos : 0 < ell) (data : FiniteData d)
    (x r : Vec d) :
    quadraticEnvelope q ell data r - inner ℝ x r ≥
      quadraticEnvelope q ell data (quadraticEnvelopeArgmin (q := q) ell_pos data x) -
          inner ℝ x (quadraticEnvelopeArgmin (q := q) ell_pos data x) +
        (1 / (2 * ell)) *
          ‖r - quadraticEnvelopeArgmin (q := q) ell_pos data x‖ ^ 2 := by
  let p : Vec d := quadraticEnvelopeArgmin (q := q) ell_pos data x
  have hpmin :
      ∀ u : Vec d,
        quadraticEnvelope q ell data p - inner ℝ x p ≤
          quadraticEnvelope q ell data u - inner ℝ x u := by
    intro u
    exact quadraticEnvelopeArgmin_is_min (q := q) ell_pos data x u
  have hsecant :
      ∀ s : ℝ, 0 < s → s ≤ 1 →
        (‖r - p‖ ^ 2 / (2 * ell)) * (1 - s) ≤
          (quadraticEnvelope q ell data r - inner ℝ x r) -
            (quadraticEnvelope q ell data p - inner ℝ x p) := by
    intro s hs hs1
    have hmix := quadratic_envelope_strong_convex (q := q) ell_pos data
      (t := s) (p := p) (r := r) (le_of_lt hs) hs1
    have hmin := hpmin ((1 - s) • p + s • r)
    have hinner :
        inner ℝ x ((1 - s) • p + s • r) =
          (1 - s) * inner ℝ x p + s * inner ℝ x r := by
      simp [inner_add_right, inner_smul_right]
    rw [hinner] at hmin
    have hnorm : ‖p - r‖ ^ 2 = ‖r - p‖ ^ 2 := by
      rw [norm_sub_rev]
    rw [hnorm] at hmix
    have hpen :
        s * (1 - s) / (2 * ell) * ‖r - p‖ ^ 2 =
          s * ((‖r - p‖ ^ 2 / (2 * ell)) * (1 - s)) := by
      ring
    have hineq :
        s * ((‖r - p‖ ^ 2 / (2 * ell)) * (1 - s)) ≤
          s * ((quadraticEnvelope q ell data r - inner ℝ x r) -
            (quadraticEnvelope q ell data p - inner ℝ x p)) := by
      nlinarith [hmix, hmin, hpen]
    exact le_of_mul_le_mul_left hineq hs
  have hsupport :=
    le_of_forall_pos_le_one_mul_one_sub_le (A := ‖r - p‖ ^ 2 / (2 * ell))
      (B := (quadraticEnvelope q ell data r - inner ℝ x r) -
        (quadraticEnvelope q ell data p - inner ℝ x p)) hsecant
  dsimp [p] at hsupport ⊢
  ring_nf at hsupport ⊢
  linarith

private theorem quadratic_envelope_argmin_lipschitz
    {q ell : ℝ} {d : ℕ} (ell_pos : 0 < ell) (data : FiniteData d)
    (x y : Vec d) :
    ‖quadraticEnvelopeArgmin (q := q) ell_pos data x -
        quadraticEnvelopeArgmin (q := q) ell_pos data y‖ ≤
      ell * ‖x - y‖ := by
  let px : Vec d := quadraticEnvelopeArgmin (q := q) ell_pos data x
  let py : Vec d := quadraticEnvelopeArgmin (q := q) ell_pos data y
  have hxy := quadratic_envelope_tilted_support (q := q) ell_pos data x py
  have hyx := quadratic_envelope_tilted_support (q := q) ell_pos data y px
  change
    quadraticEnvelope q ell data py - inner ℝ x py ≥
      quadraticEnvelope q ell data px - inner ℝ x px +
        (1 / (2 * ell)) * ‖py - px‖ ^ 2 at hxy
  change
    quadraticEnvelope q ell data px - inner ℝ y px ≥
      quadraticEnvelope q ell data py - inner ℝ y py +
        (1 / (2 * ell)) * ‖px - py‖ ^ 2 at hyx
  have hnorm : ‖py - px‖ ^ 2 = ‖px - py‖ ^ 2 := by
    rw [norm_sub_rev]
  rw [hnorm] at hxy
  have hinner_id :
      inner ℝ x px - inner ℝ x py +
          (inner ℝ y py - inner ℝ y px) =
        inner ℝ (x - y) (px - py) := by
    simp [inner_sub_left, inner_sub_right]
    ring
  have hcoef :
      2 * (1 / (2 * ell)) * ‖px - py‖ ^ 2 =
        ‖px - py‖ ^ 2 / ell := by
    field_simp [ne_of_gt ell_pos]
  have hinner :
      ‖px - py‖ ^ 2 / ell ≤ inner ℝ (x - y) (px - py) := by
    nlinarith [hxy, hyx, hinner_id, hcoef]
  have hcs :
      inner ℝ (x - y) (px - py) ≤ ‖x - y‖ * ‖px - py‖ :=
    real_inner_le_norm (x - y) (px - py)
  have hquad :
      ‖px - py‖ ^ 2 ≤ ell * (‖x - y‖ * ‖px - py‖) := by
    have hmul := (div_le_iff₀ ell_pos).mp hinner
    have hell_nonneg : 0 ≤ ell := le_of_lt ell_pos
    have hmul' :=
      mul_le_mul_of_nonneg_left hcs hell_nonneg
    nlinarith
  by_cases hzero : ‖px - py‖ = 0
  · change ‖px - py‖ ≤ ell * ‖x - y‖
    rw [hzero]
    exact mul_nonneg (le_of_lt ell_pos) (norm_nonneg _)
  · have hpos : 0 < ‖px - py‖ := norm_pos_iff.mpr (by
      intro heq
      exact hzero (by simp [heq]))
    have hprod :
        ‖px - py‖ * ‖px - py‖ ≤
          (ell * ‖x - y‖) * ‖px - py‖ := by
      nlinarith [hquad]
    have hcancel := le_of_mul_le_mul_right hprod hpos
    dsimp [px, py] at hcancel ⊢
    change ‖px - py‖ ≤ ell * ‖x - y‖
    exact hcancel

private noncomputable def quadraticEnvelopeConjugate
    {q ell : ℝ} {d : ℕ} (ell_pos : 0 < ell) (data : FiniteData d)
    (x : Vec d) : ℝ :=
  inner ℝ x (quadraticEnvelopeArgmin (q := q) ell_pos data x) -
    quadraticEnvelope q ell data (quadraticEnvelopeArgmin (q := q) ell_pos data x)

private theorem quadratic_envelope_conjugate_remainder
    {q ell : ℝ} {d : ℕ} (ell_pos : 0 < ell) (data : FiniteData d)
    (x v : Vec d) :
    0 ≤
        quadraticEnvelopeConjugate (q := q) ell_pos data (x + v) -
          quadraticEnvelopeConjugate (q := q) ell_pos data x -
            inner ℝ (quadraticEnvelopeArgmin (q := q) ell_pos data x) v ∧
      quadraticEnvelopeConjugate (q := q) ell_pos data (x + v) -
          quadraticEnvelopeConjugate (q := q) ell_pos data x -
            inner ℝ (quadraticEnvelopeArgmin (q := q) ell_pos data x) v ≤
        ell * ‖v‖ ^ 2 := by
  let px : Vec d := quadraticEnvelopeArgmin (q := q) ell_pos data x
  let py : Vec d := quadraticEnvelopeArgmin (q := q) ell_pos data (x + v)
  have hminy :=
    quadraticEnvelopeArgmin_is_min (q := q) ell_pos data (x + v) px
  have hsupport :=
    quadratic_envelope_tilted_support (q := q) ell_pos data x py
  change
    quadraticEnvelope q ell data py - inner ℝ (x + v) py ≤
      quadraticEnvelope q ell data px - inner ℝ (x + v) px at hminy
  change
    quadraticEnvelope q ell data py - inner ℝ x py ≥
      quadraticEnvelope q ell data px - inner ℝ x px +
        (1 / (2 * ell)) * ‖py - px‖ ^ 2 at hsupport
  have hinner_v :
      inner ℝ (x + v) py = inner ℝ x py + inner ℝ v py := by
    simp [inner_add_left]
  have hlower :
      0 ≤
        (inner ℝ (x + v) py - quadraticEnvelope q ell data py) -
          (inner ℝ x px - quadraticEnvelope q ell data px) -
            inner ℝ px v := by
    have hinner_px_v :
        inner ℝ px v = inner ℝ v px := by
      exact (real_inner_comm px v).symm
    have hinner_v_px :
        inner ℝ (x + v) px = inner ℝ x px + inner ℝ v px := by
      simp [inner_add_left]
    rw [hinner_v, hinner_v_px] at hminy
    rw [hinner_v]
    rw [hinner_px_v]
    nlinarith [hminy]
  have hinner_x :
      inner ℝ x py - inner ℝ x px = inner ℝ x (py - px) := by
    rw [inner_sub_right]
  have hinner_v_sub :
      inner ℝ v py - inner ℝ px v = inner ℝ v (py - px) := by
    rw [← real_inner_comm px v, ← inner_sub_right]
  have hupper :
      (inner ℝ (x + v) py - quadraticEnvelope q ell data py) -
          (inner ℝ x px - quadraticEnvelope q ell data px) -
            inner ℝ px v ≤
        inner ℝ v (py - px) := by
    have hbase :
        inner ℝ x py - quadraticEnvelope q ell data py -
            (inner ℝ x px - quadraticEnvelope q ell data px) ≤ 0 := by
      have hcoef : 0 ≤ (1 / (2 * ell) : ℝ) := by positivity
      have hnorm : 0 ≤ ‖py - px‖ ^ 2 := sq_nonneg _
      nlinarith [hsupport]
    calc
      (inner ℝ (x + v) py - quadraticEnvelope q ell data py) -
          (inner ℝ x px - quadraticEnvelope q ell data px) -
            inner ℝ px v =
          (inner ℝ x py - quadraticEnvelope q ell data py -
              (inner ℝ x px - quadraticEnvelope q ell data px)) +
            (inner ℝ v py - inner ℝ px v) := by
              rw [hinner_v]
              ring
      _ ≤ 0 + inner ℝ v (py - px) := by
        rw [hinner_v_sub]
        linarith
      _ = inner ℝ v (py - px) := by ring
  have hPL :=
    quadratic_envelope_argmin_lipschitz (q := q) ell_pos data x (x + v)
  have hcs :
      inner ℝ v (py - px) ≤ ‖v‖ * ‖py - px‖ :=
    real_inner_le_norm v (py - px)
  have hupper' :
      inner ℝ v (py - px) ≤ ell * ‖v‖ ^ 2 := by
    change ‖px - py‖ ≤ ell * ‖x - (x + v)‖ at hPL
    have hnorm_argmin :
        ‖x - (x + v)‖ = ‖v‖ := by
      rw [show x - (x + v) = -v by abel, norm_neg]
    rw [hnorm_argmin] at hPL
    have hPL' : ‖py - px‖ ≤ ell * ‖v‖ := by
      simpa [norm_sub_rev] using hPL
    have hmul := mul_le_mul_of_nonneg_left hPL' (norm_nonneg v)
    nlinarith [hcs]
  dsimp [px, py, quadraticEnvelopeConjugate] at hlower hupper hupper' ⊢
  constructor
  · exact hlower
  · linarith [hupper, hupper']

private theorem quadratic_envelope_conjugate_hasGradientAt
    {q ell : ℝ} {d : ℕ} (ell_pos : 0 < ell) (data : FiniteData d)
    (x : Vec d) :
    HasGradientAt (quadraticEnvelopeConjugate (q := q) ell_pos data)
      (quadraticEnvelopeArgmin (q := q) ell_pos data x) x := by
  rw [hasGradientAt_iff_isLittleO_nhds_zero]
  have hO :
      Asymptotics.IsBigO (nhds 0)
          (fun h : Vec d =>
            quadraticEnvelopeConjugate (q := q) ell_pos data (x + h) -
              quadraticEnvelopeConjugate (q := q) ell_pos data x -
                inner ℝ (quadraticEnvelopeArgmin (q := q) ell_pos data x) h)
          (fun h : Vec d => ell * ‖h‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_norm_le
    intro h
    have hh := quadratic_envelope_conjugate_remainder (q := q) ell_pos data x h
    rw [Real.norm_eq_abs, abs_of_nonneg hh.1]
    exact hh.2
  have hlittle :
      (fun h : Vec d => ell * ‖h‖ ^ 2) =o[nhds 0] (fun h : Vec d => h) := by
    simpa using
      (Asymptotics.isLittleO_norm_pow_id (E' := Vec d) (n := 2)
        (by norm_num : (1 : ℕ) < 2)).const_mul_left ell
  exact hO.trans_isLittleO hlittle

private theorem quadratic_envelope_active_argmin_at_shiftedGradient
    {q ell : ℝ} {d : ℕ} (hq1 : q < 1) (ell_pos : 0 < ell)
    (hell : ell = 1 - q) (data : FiniteData d)
    (hres : ∀ i j : RecordIndex, 0 ≤ interpolationResidual q data i j)
    (i : RecordIndex) :
    ∀ r : Vec d,
      quadraticEnvelope q ell data (shiftedGradient q data i) -
          inner ℝ (data.x i) (shiftedGradient q data i) ≤
        quadraticEnvelope q ell data r - inner ℝ (data.x i) r := by
  intro r
  have hactive :=
    quadratic_envelope_active_at_shifted_gradient hq1 ell_pos hell data hres i
  have hpiece_r :
      quadraticPiece q ell data i r ≤ quadraticEnvelope q ell data r := by
    unfold quadraticEnvelope
    exact Finset.le_max'
      (Finset.univ.image (fun j => quadraticPiece q ell data j r))
      (quadraticPiece q ell data i r) (by simp)
  have hpiece_lower :
      quadraticPiece q ell data i (shiftedGradient q data i) -
          inner ℝ (data.x i) (shiftedGradient q data i) ≤
        quadraticPiece q ell data i r - inner ℝ (data.x i) r := by
    unfold quadraticPiece
    have hnorm : 0 ≤ ‖r - shiftedGradient q data i‖ ^ 2 :=
      sq_nonneg _
    have hshiftzero :
        ‖shiftedGradient q data i - shiftedGradient q data i‖ ^ 2 = 0 := by
      simp
    have hcoef : 0 ≤ (1 / (2 * ell) : ℝ) := by positivity
    rw [real_inner_comm (data.x i) r,
      real_inner_comm (data.x i) (shiftedGradient q data i)]
    rw [hshiftzero]
    nlinarith [hnorm, hcoef]
  rw [← hactive] at hpiece_lower
  exact hpiece_lower.trans (sub_le_sub_right hpiece_r _)

private theorem quadratic_envelope_active_sample_spec
    {q ell : ℝ} {d : ℕ} (hq1 : q < 1) (ell_pos : 0 < ell)
    (hell : ell = 1 - q) (data : FiniteData d)
    (hres : ∀ i j : RecordIndex, 0 ≤ interpolationResidual q data i j)
    (i : RecordIndex) :
    quadraticEnvelopeArgmin (q := q) ell_pos data (data.x i) =
        shiftedGradient q data i ∧
      quadraticEnvelopeConjugate (q := q) ell_pos data (data.x i) =
        shiftedValue q data i := by
  have hshiftmin :=
    quadratic_envelope_active_argmin_at_shiftedGradient
      hq1 ell_pos hell data hres i
  have hchoose := Classical.choose_spec
    (quadratic_envelope_tilted_minimizer (q := q) ell_pos data (data.x i))
  have heq :
      shiftedGradient q data i =
        quadraticEnvelopeArgmin (q := q) ell_pos data (data.x i) :=
    hchoose.2 _ hshiftmin
  constructor
  · exact heq.symm
  · unfold quadraticEnvelopeConjugate
    rw [← heq]
    have hactive :=
      quadratic_envelope_active_at_shifted_gradient hq1 ell_pos hell data hres i
    rw [hactive]
    unfold quadraticPiece
    simp [shiftedValue, real_inner_comm]

private theorem finite_data_residual_nonneg_of_admissible_objective
    {q : ℝ} {d : ℕ} (hq0 : 0 < q) (hq1 : q < 1)
    (data : FiniteData d) (hf : AdmissibleObjective q d)
    (hreal :
      ∀ i : RecordIndex,
        hf.f (data.x i) = data.F i ∧ gradient hf.f (data.x i) = data.g i) :
    ∀ i j : RecordIndex, 0 ≤ interpolationResidual q data i j := by
  intro i j
  apply hb_interpolation_residual_nonneg_of_shifted_cocoercive hq0 hq1 data i j
  have hshifted :=
    hb_interpolation_shifted_cocoercive hq0 hq1 hf (data.x i) (data.x j)
  have hi := hreal i
  have hj := hreal j
  simpa [hi.1, hi.2, hj.1, hj.2] using hshifted

theorem HB_INTERPOLATION {q : ℝ} {d : ℕ} (hq0 : 0 < q) (hq1 : q < 1)
    (data : FiniteData d) :
    (∀ i j : RecordIndex, 0 ≤ interpolationResidual q data i j) ↔
      FiniteDataRealizable q data := by
  constructor
  · intro hres
    have hqell_pos : 0 < (1 - q : ℝ) := by linarith
    have hactive := quadratic_piece_active_at_shifted_gradient
      hq1 hqell_pos rfl data hres
    have henv_active := quadratic_envelope_active_at_shifted_gradient
      hq1 hqell_pos rfl data hres
    have hactive_le :
        ∀ i j : RecordIndex,
          quadraticPiece q (1 - q) data j (shiftedGradient q data i) ≤
            quadraticPiece q (1 - q) data i (shiftedGradient q data i) := by
      intro i j
      have hdiff := hactive i j
      have hnonneg := hres j i
      linarith
    clear hactive hactive_le henv_active
    let Hstar : Vec d → ℝ :=
      quadraticEnvelopeConjugate (q := q) hqell_pos data
    let P : Vec d → Vec d :=
      fun x => quadraticEnvelopeArgmin (q := q) hqell_pos data x
    let f : Vec d → ℝ :=
      fun x => Hstar x + (q / 2) * ‖x‖ ^ 2
    have hHgrad : ∀ x : Vec d, HasGradientAt Hstar (P x) x := by
      intro x
      simpa [Hstar, P] using
        (quadratic_envelope_conjugate_hasGradientAt
          (q := q) hqell_pos data x)
    have hfgrad : ∀ x : Vec d, HasGradientAt f (P x + q • x) x := by
      intro x
      have hquad :=
        hasGradientAt_const_mul_norm_sub_sq_centered
          (E := Vec d) q (0 : Vec d) x
      have hsum := (hHgrad x).hasFDerivAt.add hquad.hasFDerivAt
      simpa [f, sub_zero] using hsum.hasGradientAt
    have hgradient : ∀ x : Vec d, gradient f x = P x + q • x := by
      intro x
      exact (hfgrad x).gradient
    have hdiff : ∀ x : Vec d, DifferentiableAt ℝ f x := by
      intro x
      exact (hfgrad x).differentiableAt
    have hstrong :
        ∀ x y : Vec d,
          f y ≥ f x + inner ℝ (gradient f x) (y - x) +
            (q / 2) * ‖y - x‖ ^ 2 := by
      intro x y
      have hrem :=
        (quadratic_envelope_conjugate_remainder
          (q := q) hqell_pos data x (y - x)).1
      have hxy : x + (y - x) = y := by abel
      rw [hxy] at hrem
      change
        0 ≤ Hstar y - Hstar x - inner ℝ (P x) (y - x) at hrem
      have hnorm :
          ‖y‖ ^ 2 =
            ‖x‖ ^ 2 + 2 * inner ℝ x (y - x) + ‖y - x‖ ^ 2 := by
        have hvec : x + (y - x) = y := by abel
        calc
          ‖y‖ ^ 2 = ‖x + (y - x)‖ ^ 2 := by rw [hvec]
          _ = ‖x‖ ^ 2 + 2 * inner ℝ x (y - x) + ‖y - x‖ ^ 2 := by
            rw [norm_add_sq_real]
      have hinner :
          inner ℝ (P x + q • x) (y - x) =
            inner ℝ (P x) (y - x) +
              q * inner ℝ x (y - x) := by
        simp [inner_add_left, inner_smul_left]
      rw [hgradient x, hinner]
      dsimp [f]
      nlinarith [hrem, hnorm]
    have hlip :
        ∀ x y : Vec d,
          ‖gradient f y - gradient f x‖ ≤ ‖y - x‖ := by
      intro x y
      rw [hgradient y, hgradient x]
      have hvec :
          (P y + q • y) - (P x + q • x) =
            (P y - P x) + q • (y - x) := by
        module
      rw [hvec]
      have hP :
          ‖P y - P x‖ ≤ (1 - q) * ‖y - x‖ := by
        simpa [P] using
          (quadratic_envelope_argmin_lipschitz
            (q := q) hqell_pos data y x)
      have hqnorm :
          ‖q • (y - x)‖ = q * ‖y - x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hq0]
      calc
        ‖P y - P x + q • (y - x)‖ ≤
            ‖P y - P x‖ + ‖q • (y - x)‖ := norm_add_le _ _
        _ = ‖P y - P x‖ + q * ‖y - x‖ := by rw [hqnorm]
        _ ≤ (1 - q) * ‖y - x‖ + q * ‖y - x‖ := by
          exact add_le_add hP le_rfl
        _ = ‖y - x‖ := by ring
    let hf : AdmissibleObjective q d :=
      { f := f
        differentiable := hdiff
        strongConvex_lower := hstrong
        gradient_lipschitz := hlip }
    refine ⟨hf, ?_⟩
    intro i
    have hsample :=
      quadratic_envelope_active_sample_spec
        hq1 hqell_pos rfl data hres i
    have hPsample :
        P (data.x i) = shiftedGradient q data i := by
      simpa [P] using hsample.1
    have hfi : f (data.x i) = data.F i := by
      dsimp [f, Hstar]
      rw [hsample.2]
      unfold shiftedValue
      ring
    have hgi : gradient f (data.x i) = data.g i := by
      calc
        gradient f (data.x i) =
            P (data.x i) + q • data.x i := hgradient _
        _ = shiftedGradient q data i + q • data.x i := by
          rw [hPsample]
        _ = data.g i := by
          simp [shiftedGradient]
    exact ⟨hfi, hgi⟩
  · rintro ⟨hf, hreal⟩
    exact finite_data_residual_nonneg_of_admissible_objective
      hq0 hq1 data hf hreal

/-- The feature vector `s_f(u,v)`. -/
def certificateFeature {q : ℝ} {d : ℕ} (hq : 0 < q)
    (hf : AdmissibleObjective q d) (u v : Vec d) (i : Fin 4) : Vec d :=
  if i = 0 then
    u - objectiveMinimizer hq hf
  else if i = 1 then
    gradient hf.f u
  else if i = 2 then
    v - objectiveMinimizer hq hf
  else
    gradient hf.f v

/-- Coefficients `(c0,c1,Q)` of the prescribed two-point certificate. -/
structure PrescribedCertificate where
  c0 : ℝ
  c1 : ℝ
  Q : Matrix (Fin 4) (Fin 4) ℝ
  Q_isSymm : Q.IsSymm

/-- The prescribed family `V_f(u,v)`. -/
def prescribedCertificateValue {q : ℝ} {d : ℕ} (hq : 0 < q)
    (hf : AdmissibleObjective q d) (cert : PrescribedCertificate)
    (u v : Vec d) : ℝ :=
  cert.c0 * (hf.f v - objectiveMinimum hq hf) +
    cert.c1 * (hf.f u - objectiveMinimum hq hf) +
    ∑ i : Fin 4, ∑ j : Fin 4,
      cert.Q i j *
        inner ℝ (certificateFeature hq hf u v i)
          (certificateFeature hq hf u v j)

/-- `L(q,a,b)`: a common prescribed certificate works for every admissible
objective, dimension, and two-state input. -/
def HB_L (q a b : ℝ) : Prop :=
  ∃ hD : ParameterDomain q a b,
    ∃ cert : PrescribedCertificate,
      ∀ (d : ℕ), 1 ≤ d →
        ∀ hf : AdmissibleObjective q d,
          ∀ u v : Vec d,
            let hq := parameterDomain_q_pos hD
            let w := hbSuccessor a b hf u v
            hf.f w - objectiveMinimum hq hf ≤
                prescribedCertificateValue hq hf cert v w ∧
              prescribedCertificateValue hq hf cert v w ≤
                prescribedCertificateValue hq hf cert u v

/-- A nonconstant finite periodic Heavy-Ball orbit generated by the canonical
recurrence from an initial pair. -/
def HB_Cycle (q a b : ℝ) : Prop :=
  ∃ _hD : ParameterDomain q a b,
    ∃ d : ℕ, 1 ≤ d ∧
      ∃ hf : AdmissibleObjective q d,
        ∃ K : ℕ, 2 ≤ K ∧
          ∃ xMinusOne xZero : Vec d,
            (∀ t : ℕ,
              hbIterate a b hf xMinusOne xZero (t + K) =
                hbIterate a b hf xMinusOne xZero t) ∧
            ∃ t : ℕ,
              hbIterate a b hf xMinusOne xZero (t + 1) ≠
                hbIterate a b hf xMinusOne xZero t

/-- `G(q,a,b)`: global convergence of every generated trajectory. -/
def HB_G (q a b : ℝ) : Prop :=
  ∃ hD : ParameterDomain q a b,
    ∀ (d : ℕ), 1 ≤ d →
      ∀ hf : AdmissibleObjective q d,
        ∀ xMinusOne xZero : Vec d,
          Filter.Tendsto
            (fun t : ℕ =>
              ‖hbIterate a b hf xMinusOne xZero t -
                objectiveMinimizer (parameterDomain_q_pos hD) hf‖)
            atTop (nhds 0)

/-- Full two-point record
`O_f(u,v)=(u-x_*,grad f(u),v-x_*,grad f(v),f(u)-f_*,f(v)-f_*)`. -/
structure FullRecord (d : ℕ) where
  uCentered : Vec d
  gradU : Vec d
  vCentered : Vec d
  gradV : Vec d
  gapU : ℝ
  gapV : ℝ

def twoPointRecord {q : ℝ} {d : ℕ} (hq : 0 < q)
    (hf : AdmissibleObjective q d) (u v : Vec d) : FullRecord d where
  uCentered := u - objectiveMinimizer hq hf
  gradU := gradient hf.f u
  vCentered := v - objectiveMinimizer hq hf
  gradV := gradient hf.f v
  gapU := hf.f u - objectiveMinimum hq hf
  gapV := hf.f v - objectiveMinimum hq hf

def RecordMapWorks (q a b : ℝ) (d : ℕ) (Phi : FullRecord d → ℝ) : Prop :=
  ∀ hD : ParameterDomain q a b,
    ∀ hf : AdmissibleObjective q d,
      ∀ u v : Vec d,
        let hq := parameterDomain_q_pos hD
        let w := hbSuccessor a b hf u v
        hf.f w - objectiveMinimum hq hf ≤ Phi (twoPointRecord hq hf v w) ∧
          Phi (twoPointRecord hq hf v w) ≤ Phi (twoPointRecord hq hf u v)

private def fullRecordCertificateFeature {d : ℕ}
    (r : FullRecord d) (i : Fin 4) : Vec d :=
  if i = 0 then
    r.uCentered
  else if i = 1 then
    r.gradU
  else if i = 2 then
    r.vCentered
  else
    r.gradV

private def fullRecordCertificateValue {d : ℕ}
    (cert : PrescribedCertificate) (r : FullRecord d) : ℝ :=
  cert.c0 * r.gapV + cert.c1 * r.gapU +
    ∑ i : Fin 4, ∑ j : Fin 4,
      cert.Q i j *
        inner ℝ (fullRecordCertificateFeature r i)
          (fullRecordCertificateFeature r j)

private theorem fullRecordCertificateFeature_twoPointRecord
    {q : ℝ} {d : ℕ} (hq : 0 < q)
    (hf : AdmissibleObjective q d) (u v : Vec d) :
    ∀ i : Fin 4,
      fullRecordCertificateFeature (twoPointRecord hq hf u v) i =
        certificateFeature hq hf u v i := by
  intro i
  fin_cases i <;>
    simp [fullRecordCertificateFeature, certificateFeature, twoPointRecord]

private theorem fullRecordCertificateValue_twoPointRecord
    {q : ℝ} {d : ℕ} (hq : 0 < q)
    (hf : AdmissibleObjective q d) (cert : PrescribedCertificate)
    (u v : Vec d) :
    fullRecordCertificateValue cert (twoPointRecord hq hf u v) =
      prescribedCertificateValue hq hf cert u v := by
  have hfeature :=
    fullRecordCertificateFeature_twoPointRecord hq hf u v
  unfold fullRecordCertificateValue prescribedCertificateValue
  change
    cert.c0 * (hf.f v - objectiveMinimum hq hf) +
        cert.c1 * (hf.f u - objectiveMinimum hq hf) +
      ∑ i : Fin 4, ∑ j : Fin 4,
        cert.Q i j *
          inner ℝ
            (fullRecordCertificateFeature (twoPointRecord hq hf u v) i)
            (fullRecordCertificateFeature (twoPointRecord hq hf u v) j) =
      cert.c0 * (hf.f v - objectiveMinimum hq hf) +
        cert.c1 * (hf.f u - objectiveMinimum hq hf) +
      ∑ i : Fin 4, ∑ j : Fin 4,
        cert.Q i j *
          inner ℝ (certificateFeature hq hf u v i)
            (certificateFeature hq hf u v j)
  congr 1

private theorem record_map_works_of_HB_L {q a b : ℝ} :
    HB_L q a b →
      ∃ Phi : FullRecord 2 → ℝ, RecordMapWorks q a b 2 Phi := by
  rintro ⟨hD, cert, hworks⟩
  refine ⟨fullRecordCertificateValue cert, ?_⟩
  intro hD' hf u v
  have hqeq :
      parameterDomain_q_pos hD = parameterDomain_q_pos hD' :=
    Subsingleton.elim _ _
  have hcert := hworks 2 (by norm_num) hf u v
  dsimp at hcert
  rw [hqeq] at hcert
  have hsucc :
      fullRecordCertificateValue cert
          (twoPointRecord (parameterDomain_q_pos hD') hf v
            (hbSuccessor a b hf u v)) =
        prescribedCertificateValue (parameterDomain_q_pos hD') hf cert v
          (hbSuccessor a b hf u v) :=
    fullRecordCertificateValue_twoPointRecord
      (parameterDomain_q_pos hD') hf cert v (hbSuccessor a b hf u v)
  have hprev :
      fullRecordCertificateValue cert
          (twoPointRecord (parameterDomain_q_pos hD') hf u v) =
        prescribedCertificateValue (parameterDomain_q_pos hD') hf cert u v :=
    fullRecordCertificateValue_twoPointRecord
      (parameterDomain_q_pos hD') hf cert u v
  constructor
  · simpa [hsucc] using hcert.1
  · simpa [hsucc, hprev] using hcert.2

/-- Matrix action on the Euclidean-space representation of `R^d`. -/
def matrixVec {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (x : Vec d) : Vec d :=
  WithLp.toLp (2 : ENNReal) (S.mulVec x.ofLp)

/-- Real two-vector representing a complex number. -/
def complexAsVec2 (z : ℂ) : Vec 2 :=
  WithLp.toLp (2 : ENNReal) (fun i : Fin 2 => if i = 0 then z.re else z.im)

/-- Real matrix for multiplication by a complex number on `R^2`. -/
def complexMulMatrix (z : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j =>
    if i = (0 : Fin 2) ∧ j = (0 : Fin 2) then z.re
    else if i = (0 : Fin 2) ∧ j = (1 : Fin 2) then -z.im
    else if i = (1 : Fin 2) ∧ j = (0 : Fin 2) then z.im
    else z.re

theorem complexAsVec2_mul (z w : ℂ) :
    complexAsVec2 (z * w) = matrixVec (complexMulMatrix z) (complexAsVec2 w) := by
  ext i
  fin_cases i <;>
    simp [complexAsVec2, matrixVec, complexMulMatrix, Matrix.mulVec,
      Complex.mul_re, Complex.mul_im]
  <;> ring

/-- The rational complex witness `z=(23+199i)/200`. -/
def hbWitnessZ : ℂ := ((23 : ℂ) + (199 : ℂ) * Complex.I) / 200

/-- The source witness expansion factor `R=|z|^2=4013/4000`. -/
def hbWitnessR : ℝ := 4013 / 4000

/-- The source witness value scale `F=41/100`. -/
def hbWitnessF : ℝ := 41 / 100

/-- The source witness gradient multiplier
`eta=(1+b-z-b/z)/a=(1136661-320987i)/1813876`. -/
def hbWitnessEta : ℂ :=
  ((1 + (bStar : ℂ)) - hbWitnessZ - (bStar : ℂ) * hbWitnessZ⁻¹) / (aStar : ℂ)

/-- The real similarity matrix `S` for multiplication by the source witness `z`. -/
def hbWitnessSimilarityMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  complexMulMatrix hbWitnessZ

/-- Complex witness positions indexed by `*,0,1,2`. -/
def hbWitnessComplexX : RecordIndex → ℂ
  | RecordIndex.star => 0
  | RecordIndex.zero => hbWitnessZ⁻¹
  | RecordIndex.one => 1
  | RecordIndex.two => hbWitnessZ

/-- Complex witness gradients indexed by `*,0,1,2`. -/
def hbWitnessComplexG (i : RecordIndex) : ℂ :=
  hbWitnessEta * hbWitnessComplexX i

/-- Source finite data for the rational witness in dimension two. -/
def hbRationalWitnessData : FiniteData 2 where
  x i := complexAsVec2 (hbWitnessComplexX i)
  g i := complexAsVec2 (hbWitnessComplexG i)
  F i := hbWitnessF * Complex.normSq (hbWitnessComplexX i)

private theorem complexAsVec2_norm_sq (z : ℂ) :
    ‖complexAsVec2 z‖ ^ 2 = Complex.normSq z := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [complexAsVec2, Complex.normSq_apply, pow_two]

private theorem complexAsVec2_inner (z w : ℂ) :
    inner ℝ (complexAsVec2 z) (complexAsVec2 w) =
      z.re * w.re + z.im * w.im := by
  rw [PiLp.inner_apply]
  simp [complexAsVec2, PiLp.toLp_apply, Fin.sum_univ_two]
  change w.re * z.re + w.im * z.im = z.re * w.re + z.im * w.im
  ring

private theorem complexAsVec2_sub (z w : ℂ) :
    complexAsVec2 z - complexAsVec2 w = complexAsVec2 (z - w) := by
  ext i
  fin_cases i <;> simp [complexAsVec2]

private theorem complex_as_vec2_witness_action (w : ℂ) :
    complexAsVec2 (hbWitnessZ * w) =
      matrixVec hbWitnessSimilarityMatrix (complexAsVec2 w) := by
  simpa [hbWitnessSimilarityMatrix] using (complexAsVec2_mul hbWitnessZ w)

private theorem rational_witness_residual_table :
    ∀ i j : RecordIndex, 0 ≤ interpolationResidual qStar hbRationalWitnessData i j := by
  intro i j
  cases i <;> cases j
  <;> norm_num [interpolationResidual, hbRationalWitnessData, hbWitnessComplexX,
      hbWitnessComplexG, hbWitnessEta, hbWitnessZ, qStar, aStar, bStar,
      hbWitnessF, complexAsVec2_sub, complexAsVec2_norm_sq, complexAsVec2_inner,
      Complex.normSq_apply, Complex.div_re, Complex.div_im, Complex.inv_re,
      Complex.inv_im]

theorem HB_RATIONAL_WITNESS_exact_data :
    hbWitnessR = Complex.normSq hbWitnessZ ∧
      hbWitnessR > 1 ∧
      hbWitnessF > 0 ∧
      hbWitnessZ ≠ 0 ∧
      hbWitnessEta =
        ((1 + (bStar : ℂ)) - hbWitnessZ - (bStar : ℂ) * hbWitnessZ⁻¹) /
          (aStar : ℂ) ∧
      hbRationalWitnessData.x RecordIndex.star = 0 ∧
      hbRationalWitnessData.g RecordIndex.star = 0 ∧
      hbRationalWitnessData.F RecordIndex.star = 0 ∧
      (∀ i j : RecordIndex,
        0 ≤ interpolationResidual qStar hbRationalWitnessData i j) ∧
      FiniteDataRealizable qStar hbRationalWitnessData ∧
      hbRationalWitnessData.x RecordIndex.two =
        (1 + bStar) • hbRationalWitnessData.x RecordIndex.one -
          bStar • hbRationalWitnessData.x RecordIndex.zero -
            aStar • hbRationalWitnessData.g RecordIndex.one ∧
      hbRationalWitnessData.F RecordIndex.one =
        hbWitnessR * hbRationalWitnessData.F RecordIndex.zero ∧
      hbRationalWitnessData.F RecordIndex.two =
        hbWitnessR * hbRationalWitnessData.F RecordIndex.one ∧
      0 < hbRationalWitnessData.F RecordIndex.zero ∧
      Matrix.transpose hbWitnessSimilarityMatrix * hbWitnessSimilarityMatrix =
        hbWitnessR • (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
      hbRationalWitnessData.x RecordIndex.one =
        matrixVec hbWitnessSimilarityMatrix (hbRationalWitnessData.x RecordIndex.zero) ∧
      hbRationalWitnessData.x RecordIndex.two =
        matrixVec hbWitnessSimilarityMatrix (hbRationalWitnessData.x RecordIndex.one) ∧
      hbRationalWitnessData.g RecordIndex.one =
        matrixVec hbWitnessSimilarityMatrix (hbRationalWitnessData.g RecordIndex.zero) ∧
      hbRationalWitnessData.g RecordIndex.two =
        matrixVec hbWitnessSimilarityMatrix (hbRationalWitnessData.g RecordIndex.one) := by
  have hq0 : 0 < qStar := by
    norm_num [qStar]
  have hq1 : qStar < 1 := by
    norm_num [qStar]
  have hz0 : hbWitnessZ ≠ 0 := by
    intro hz
    have hzr := congrArg Complex.re hz
    norm_num [hbWitnessZ, Complex.div_re, Complex.div_im,
      Complex.normSq_apply] at hzr
  have hR : hbWitnessR = Complex.normSq hbWitnessZ := by
    norm_num [hbWitnessR, hbWitnessZ, Complex.normSq_apply,
      Complex.div_re, Complex.div_im]
  have hRgt : hbWitnessR > 1 := by
    norm_num [hbWitnessR]
  have hFpos : hbWitnessF > 0 := by
    norm_num [hbWitnessF]
  have hEta :
      hbWitnessEta =
        ((1 + (bStar : ℂ)) - hbWitnessZ - (bStar : ℂ) * hbWitnessZ⁻¹) /
          (aStar : ℂ) := by
    rfl
  have hxstar : hbRationalWitnessData.x RecordIndex.star = 0 := by
    ext i
    fin_cases i <;>
      simp [hbRationalWitnessData, hbWitnessComplexX, complexAsVec2]
  have hgstar : hbRationalWitnessData.g RecordIndex.star = 0 := by
    ext i
    fin_cases i <;>
      simp [hbRationalWitnessData, hbWitnessComplexG, hbWitnessComplexX,
        complexAsVec2]
  have hFstar : hbRationalWitnessData.F RecordIndex.star = 0 := by
    simp [hbRationalWitnessData, hbWitnessComplexX, hbWitnessF]
  have hres :
      ∀ i j : RecordIndex, 0 ≤ interpolationResidual qStar hbRationalWitnessData i j :=
    rational_witness_residual_table
  have hreal : FiniteDataRealizable qStar hbRationalWitnessData :=
    (HB_INTERPOLATION hq0 hq1 hbRationalWitnessData).1 hres
  have hupdate :
      hbRationalWitnessData.x RecordIndex.two =
        (1 + bStar) • hbRationalWitnessData.x RecordIndex.one -
          bStar • hbRationalWitnessData.x RecordIndex.zero -
            aStar • hbRationalWitnessData.g RecordIndex.one := by
    ext i
    fin_cases i <;>
      norm_num [hbRationalWitnessData, hbWitnessComplexX, hbWitnessComplexG,
        hbWitnessEta, hbWitnessZ, aStar, bStar, complexAsVec2,
        Complex.div_re, Complex.div_im, Complex.normSq_apply]
  have hzsq : Complex.normSq hbWitnessZ = (4013 / 4000 : ℝ) := by
    norm_num [hbWitnessZ, Complex.normSq_apply, Complex.div_re,
      Complex.div_im]
  have hzinvsq : Complex.normSq hbWitnessZ⁻¹ = (4000 / 4013 : ℝ) := by
    rw [Complex.normSq_inv, hzsq]
    norm_num
  have hF01 :
      hbRationalWitnessData.F RecordIndex.one =
        hbWitnessR * hbRationalWitnessData.F RecordIndex.zero := by
    norm_num [hbRationalWitnessData, hbWitnessComplexX, hbWitnessF,
      hbWitnessR, hzinvsq, hzsq, Complex.normSq_one]
  have hF12 :
      hbRationalWitnessData.F RecordIndex.two =
        hbWitnessR * hbRationalWitnessData.F RecordIndex.one := by
    simp [hbRationalWitnessData, hbWitnessComplexX, hbWitnessF, hzsq, hR]
    ring
  have hF0 : 0 < hbRationalWitnessData.F RecordIndex.zero := by
    simp [hbRationalWitnessData, hbWitnessComplexX, hbWitnessF, hzinvsq]
  have hmatrix :
      Matrix.transpose hbWitnessSimilarityMatrix * hbWitnessSimilarityMatrix =
        hbWitnessR • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [hbWitnessSimilarityMatrix, complexMulMatrix, hbWitnessZ,
        hbWitnessR, Complex.div_re, Complex.div_im, Complex.normSq_apply,
        Matrix.mul_apply, Fin.sum_univ_two]
  have hx01 :
      hbRationalWitnessData.x RecordIndex.one =
        matrixVec hbWitnessSimilarityMatrix
          (hbRationalWitnessData.x RecordIndex.zero) := by
    change complexAsVec2 (1 : ℂ) =
      matrixVec hbWitnessSimilarityMatrix (complexAsVec2 hbWitnessZ⁻¹)
    rw [← complex_as_vec2_witness_action (hbWitnessZ⁻¹)]
    simp [hz0]
  have hx12 :
      hbRationalWitnessData.x RecordIndex.two =
        matrixVec hbWitnessSimilarityMatrix
          (hbRationalWitnessData.x RecordIndex.one) := by
    change complexAsVec2 hbWitnessZ =
      matrixVec hbWitnessSimilarityMatrix (complexAsVec2 (1 : ℂ))
    rw [← complex_as_vec2_witness_action (1 : ℂ)]
    simp
  have hg01 :
      hbRationalWitnessData.g RecordIndex.one =
        matrixVec hbWitnessSimilarityMatrix
          (hbRationalWitnessData.g RecordIndex.zero) := by
    change complexAsVec2 (hbWitnessEta * (1 : ℂ)) =
      matrixVec hbWitnessSimilarityMatrix
        (complexAsVec2 (hbWitnessEta * hbWitnessZ⁻¹))
    rw [← complex_as_vec2_witness_action
      (hbWitnessEta * hbWitnessZ⁻¹)]
    simp [hz0, mul_assoc, mul_comm, mul_left_comm]
  have hg12 :
      hbRationalWitnessData.g RecordIndex.two =
        matrixVec hbWitnessSimilarityMatrix
          (hbRationalWitnessData.g RecordIndex.one) := by
    change complexAsVec2 (hbWitnessEta * hbWitnessZ) =
      matrixVec hbWitnessSimilarityMatrix
        (complexAsVec2 (hbWitnessEta * (1 : ℂ)))
    rw [← complex_as_vec2_witness_action (hbWitnessEta * (1 : ℂ))]
    simp [mul_assoc, mul_comm, mul_left_comm]
  exact ⟨hR, hRgt, hFpos, hz0, hEta, hxstar, hgstar, hFstar, hres, hreal,
    hupdate, hF01, hF12, hF0, hmatrix, hx01, hx12, hg01, hg12⟩

private theorem rational_witness_feature_scale
    (hf : AdmissibleObjective qStar 2)
    (hreal :
      ∀ i : RecordIndex,
        hf.f (hbRationalWitnessData.x i) = hbRationalWitnessData.F i ∧
          gradient hf.f (hbRationalWitnessData.x i) = hbRationalWitnessData.g i)
    (hmin :
      objectiveMinimizer (parameterDomain_q_pos HB_central_parameters_in_domain) hf = 0) :
    ∀ i : Fin 4,
      certificateFeature (parameterDomain_q_pos HB_central_parameters_in_domain) hf
          (hbRationalWitnessData.x RecordIndex.one)
          (hbRationalWitnessData.x RecordIndex.two) i =
        matrixVec hbWitnessSimilarityMatrix
          (certificateFeature (parameterDomain_q_pos HB_central_parameters_in_domain) hf
            (hbRationalWitnessData.x RecordIndex.zero)
            (hbRationalWitnessData.x RecordIndex.one) i) := by
  obtain ⟨hR, hRgt, hFpos, hz0, hEta, hxstar, hgstar, hFstar, hres,
      hrealizable, hupdate, hF01, hF12, hF0, hmatrix, hx01, hx12, hg01, hg12⟩ :=
    HB_RATIONAL_WITNESS_exact_data
  have hg01' := (hreal RecordIndex.one).2
  have hg00' := (hreal RecordIndex.zero).2
  have hg12' := (hreal RecordIndex.two).2
  intro i
  fin_cases i
  · change
      hbRationalWitnessData.x RecordIndex.one -
          objectiveMinimizer (parameterDomain_q_pos HB_central_parameters_in_domain) hf =
        matrixVec hbWitnessSimilarityMatrix
          (hbRationalWitnessData.x RecordIndex.zero -
            objectiveMinimizer (parameterDomain_q_pos HB_central_parameters_in_domain) hf)
    simpa [hmin] using hx01
  · change
      gradient hf.f (hbRationalWitnessData.x RecordIndex.one) =
        matrixVec hbWitnessSimilarityMatrix
          (gradient hf.f (hbRationalWitnessData.x RecordIndex.zero))
    rw [hg01', hg00', hg01]
  · change
      hbRationalWitnessData.x RecordIndex.two -
          objectiveMinimizer (parameterDomain_q_pos HB_central_parameters_in_domain) hf =
        matrixVec hbWitnessSimilarityMatrix
          (hbRationalWitnessData.x RecordIndex.one -
            objectiveMinimizer (parameterDomain_q_pos HB_central_parameters_in_domain) hf)
    simpa [hmin] using hx12
  · change
      gradient hf.f (hbRationalWitnessData.x RecordIndex.two) =
        matrixVec hbWitnessSimilarityMatrix
          (gradient hf.f (hbRationalWitnessData.x RecordIndex.one))
    rw [hg12', hg01', hg12]

private theorem matrix_vec_inner_scale_of_similarity
    {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (R : ℝ)
    (hS : Matrix.transpose S * S = R • (1 : Matrix (Fin d) (Fin d) ℝ))
  (u v : Vec d) :
    inner ℝ (matrixVec S u) (matrixVec S v) = R * inner ℝ u v := by
  simp [matrixVec, PiLp.inner_apply, PiLp.toLp_apply, real_inner_eq_re_inner]
  change
    dotProduct (S.mulVec v.ofLp) (S.mulVec u.ofLp) =
      R * dotProduct v.ofLp u.ofLp
  rw [← Matrix.vecMul_transpose S v.ofLp]
  rw [← Matrix.dotProduct_mulVec v.ofLp (Matrix.transpose S) (S.mulVec u.ofLp)]
  rw [Matrix.mulVec_mulVec]
  rw [hS]
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem rational_witness_objective_gap_scale
    (hf : AdmissibleObjective qStar 2)
    (hreal :
      ∀ i : RecordIndex,
        hf.f (hbRationalWitnessData.x i) = hbRationalWitnessData.F i ∧
          gradient hf.f (hbRationalWitnessData.x i) = hbRationalWitnessData.g i)
    (hmin :
      objectiveMinimizer (parameterDomain_q_pos HB_central_parameters_in_domain) hf = 0) :
    (hf.f (hbRationalWitnessData.x RecordIndex.two) -
          objectiveMinimum (parameterDomain_q_pos HB_central_parameters_in_domain) hf =
        hbWitnessR *
          (hf.f (hbRationalWitnessData.x RecordIndex.one) -
            objectiveMinimum (parameterDomain_q_pos HB_central_parameters_in_domain) hf)) ∧
      (hf.f (hbRationalWitnessData.x RecordIndex.one) -
          objectiveMinimum (parameterDomain_q_pos HB_central_parameters_in_domain) hf =
        hbWitnessR *
          (hf.f (hbRationalWitnessData.x RecordIndex.zero) -
            objectiveMinimum (parameterDomain_q_pos HB_central_parameters_in_domain) hf)) := by
  obtain ⟨hR, hRgt, hFpos, hz0, hEta, hxstar, hgstar, hFstar, hres,
      hrealizable, hupdate, hF01, hF12, hF0, hmatrix, hx01, hx12, hg01, hg12⟩ :=
    HB_RATIONAL_WITNESS_exact_data
  have hfzero : hf.f (0 : Vec 2) = 0 := by
    calc
      hf.f (0 : Vec 2) = hf.f (hbRationalWitnessData.x RecordIndex.star) := by
        rw [hxstar]
      _ = hbRationalWitnessData.F RecordIndex.star := (hreal RecordIndex.star).1
      _ = 0 := hFstar
  have hminval :
      objectiveMinimum (parameterDomain_q_pos HB_central_parameters_in_domain) hf = 0 := by
    simp [objectiveMinimum, hmin, hfzero]
  constructor
  · rw [(hreal RecordIndex.two).1, hminval, hF12,
      (hreal RecordIndex.one).1]
    ring
  · rw [(hreal RecordIndex.one).1, hminval, hF01,
      (hreal RecordIndex.zero).1]
    ring

theorem HB_RATIONAL_WITNESS_certificate_scale
    (hf : AdmissibleObjective qStar 2)
    (hreal :
      ∀ i : RecordIndex,
        hf.f (hbRationalWitnessData.x i) = hbRationalWitnessData.F i ∧
          gradient hf.f (hbRationalWitnessData.x i) = hbRationalWitnessData.g i)
    (hmin :
      objectiveMinimizer (parameterDomain_q_pos HB_central_parameters_in_domain) hf = 0)
    (cert : PrescribedCertificate) :
    prescribedCertificateValue
        (parameterDomain_q_pos HB_central_parameters_in_domain) hf cert
        (hbRationalWitnessData.x RecordIndex.one)
        (hbRationalWitnessData.x RecordIndex.two) =
      hbWitnessR *
        prescribedCertificateValue
          (parameterDomain_q_pos HB_central_parameters_in_domain) hf cert
          (hbRationalWitnessData.x RecordIndex.zero)
          (hbRationalWitnessData.x RecordIndex.one) := by
  obtain ⟨hR, hRgt, hFpos, hz0, hEta, hxstar, hgstar, hFstar, hres,
      hrealizable, hupdate, hF01, hF12, hF0, hmatrix, hx01, hx12, hg01, hg12⟩ :=
    HB_RATIONAL_WITNESS_exact_data
  have hfeature := rational_witness_feature_scale hf hreal hmin
  have hinner :=
    matrix_vec_inner_scale_of_similarity hbWitnessSimilarityMatrix hbWitnessR hmatrix
  have hgap := rational_witness_objective_gap_scale hf hreal hmin
  have hc1 :
      cert.c1 *
          (hf.f (hbRationalWitnessData.x RecordIndex.one) -
            objectiveMinimum (parameterDomain_q_pos HB_central_parameters_in_domain) hf) =
        cert.c1 *
          (hbWitnessR *
            (hf.f (hbRationalWitnessData.x RecordIndex.zero) -
              objectiveMinimum (parameterDomain_q_pos HB_central_parameters_in_domain) hf)) :=
    congrArg
      (fun t : ℝ => cert.c1 * t) hgap.2
  have hvalue :
      cert.c0 *
          (hf.f (hbRationalWitnessData.x RecordIndex.two) -
            objectiveMinimum (parameterDomain_q_pos HB_central_parameters_in_domain) hf) +
        cert.c1 *
          (hf.f (hbRationalWitnessData.x RecordIndex.one) -
            objectiveMinimum (parameterDomain_q_pos HB_central_parameters_in_domain) hf) =
      hbWitnessR *
        (cert.c0 *
            (hf.f (hbRationalWitnessData.x RecordIndex.one) -
              objectiveMinimum (parameterDomain_q_pos HB_central_parameters_in_domain) hf) +
          cert.c1 *
            (hf.f (hbRationalWitnessData.x RecordIndex.zero) -
              objectiveMinimum (parameterDomain_q_pos HB_central_parameters_in_domain) hf)) := by
    calc
      _ =
          cert.c0 *
              (hbWitnessR *
                (hf.f (hbRationalWitnessData.x RecordIndex.one) -
                  objectiveMinimum (parameterDomain_q_pos HB_central_parameters_in_domain) hf)) +
            cert.c1 *
              (hf.f (hbRationalWitnessData.x RecordIndex.one) -
                objectiveMinimum (parameterDomain_q_pos HB_central_parameters_in_domain) hf) := by
        rw [hgap.1]
      _ =
          cert.c0 *
              (hbWitnessR *
                (hf.f (hbRationalWitnessData.x RecordIndex.one) -
                  objectiveMinimum (parameterDomain_q_pos HB_central_parameters_in_domain) hf)) +
            cert.c1 *
              (hbWitnessR *
                (hf.f (hbRationalWitnessData.x RecordIndex.zero) -
                  objectiveMinimum (parameterDomain_q_pos HB_central_parameters_in_domain) hf)) := by
        rw [hc1]
      _ = _ := by ring
  have hquad :
      (∑ i : Fin 4, ∑ j : Fin 4,
        cert.Q i j *
          inner ℝ
            (certificateFeature (parameterDomain_q_pos HB_central_parameters_in_domain) hf
              (hbRationalWitnessData.x RecordIndex.one)
              (hbRationalWitnessData.x RecordIndex.two) i)
            (certificateFeature (parameterDomain_q_pos HB_central_parameters_in_domain) hf
              (hbRationalWitnessData.x RecordIndex.one)
              (hbRationalWitnessData.x RecordIndex.two) j)) =
      hbWitnessR *
        (∑ i : Fin 4, ∑ j : Fin 4,
          cert.Q i j *
            inner ℝ
              (certificateFeature (parameterDomain_q_pos HB_central_parameters_in_domain) hf
                (hbRationalWitnessData.x RecordIndex.zero)
                (hbRationalWitnessData.x RecordIndex.one) i)
              (certificateFeature (parameterDomain_q_pos HB_central_parameters_in_domain) hf
          (hbRationalWitnessData.x RecordIndex.zero)
                (hbRationalWitnessData.x RecordIndex.one) j)) := by
    simp_rw [hfeature, hinner]
    have hsum :
        ∀ f : Fin 4 → Fin 4 → ℝ,
          (∑ i : Fin 4, ∑ j : Fin 4,
            cert.Q i j * (hbWitnessR * f i j)) =
            hbWitnessR *
              (∑ i : Fin 4, ∑ j : Fin 4, cert.Q i j * f i j) := by
      intro f
      calc
        _ =
            ∑ i : Fin 4, ∑ j : Fin 4,
              hbWitnessR * (cert.Q i j * f i j) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ =
            ∑ i : Fin 4, hbWitnessR *
              (∑ j : Fin 4, cert.Q i j * f i j) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
        _ = _ := by
          rw [Finset.mul_sum]
    exact hsum (fun i j =>
      inner ℝ
        (certificateFeature (parameterDomain_q_pos HB_central_parameters_in_domain) hf
          (hbRationalWitnessData.x RecordIndex.zero)
          (hbRationalWitnessData.x RecordIndex.one) i)
        (certificateFeature (parameterDomain_q_pos HB_central_parameters_in_domain) hf
          (hbRationalWitnessData.x RecordIndex.zero)
          (hbRationalWitnessData.x RecordIndex.one) j))
  unfold prescribedCertificateValue
  calc
    _ =
        (cert.c0 *
            (hf.f (hbRationalWitnessData.x RecordIndex.two) -
              objectiveMinimum (parameterDomain_q_pos HB_central_parameters_in_domain) hf) +
          cert.c1 *
            (hf.f (hbRationalWitnessData.x RecordIndex.one) -
              objectiveMinimum (parameterDomain_q_pos HB_central_parameters_in_domain) hf)) +
          ∑ i : Fin 4, ∑ j : Fin 4,
            cert.Q i j *
              inner ℝ
                (certificateFeature (parameterDomain_q_pos HB_central_parameters_in_domain) hf
                  (hbRationalWitnessData.x RecordIndex.one)
                  (hbRationalWitnessData.x RecordIndex.two) i)
                (certificateFeature (parameterDomain_q_pos HB_central_parameters_in_domain) hf
                  (hbRationalWitnessData.x RecordIndex.one)
                  (hbRationalWitnessData.x RecordIndex.two) j) := by
      ring
    _ =
        hbWitnessR *
            (cert.c0 *
                (hf.f (hbRationalWitnessData.x RecordIndex.one) -
                  objectiveMinimum (parameterDomain_q_pos HB_central_parameters_in_domain) hf) +
              cert.c1 *
                (hf.f (hbRationalWitnessData.x RecordIndex.zero) -
                  objectiveMinimum (parameterDomain_q_pos HB_central_parameters_in_domain) hf)) +
          hbWitnessR *
            (∑ i : Fin 4, ∑ j : Fin 4,
              cert.Q i j *
                inner ℝ
                  (certificateFeature (parameterDomain_q_pos HB_central_parameters_in_domain) hf
                    (hbRationalWitnessData.x RecordIndex.zero)
                    (hbRationalWitnessData.x RecordIndex.one) i)
                  (certificateFeature (parameterDomain_q_pos HB_central_parameters_in_domain) hf
                    (hbRationalWitnessData.x RecordIndex.zero)
                    (hbRationalWitnessData.x RecordIndex.one) j)) := by
      rw [hvalue, hquad]
    _ =
        hbWitnessR *
          (cert.c0 *
              (hf.f (hbRationalWitnessData.x RecordIndex.one) -
                objectiveMinimum (parameterDomain_q_pos HB_central_parameters_in_domain) hf) +
            cert.c1 *
              (hf.f (hbRationalWitnessData.x RecordIndex.zero) -
                objectiveMinimum (parameterDomain_q_pos HB_central_parameters_in_domain) hf) +
            ∑ i : Fin 4, ∑ j : Fin 4,
              cert.Q i j *
                inner ℝ
                  (certificateFeature (parameterDomain_q_pos HB_central_parameters_in_domain) hf
                    (hbRationalWitnessData.x RecordIndex.zero)
                    (hbRationalWitnessData.x RecordIndex.one) i)
                  (certificateFeature (parameterDomain_q_pos HB_central_parameters_in_domain) hf
                    (hbRationalWitnessData.x RecordIndex.zero)
                    (hbRationalWitnessData.x RecordIndex.one) j)) := by
      ring

private theorem box_cycle_lag_sum_nonpositive
    {q : ℝ} {d K : ℕ} (hq0 : 0 < q) (hq1 : q < 1) (hK : 0 < K)
    (y g : Fin K → Vec d) (F : Fin K → ℝ)
    (shift : Fin K → Fin K) (hshift : Function.Bijective shift)
    (hci :
      ∀ i : Fin K,
        (1 / (2 * (1 - q))) *
            ‖(g (shift i) - q • y (shift i)) -
              (g i - q • y i)‖ ^ 2 ≤
          (F (shift i) - (q / 2) * ‖y (shift i)‖ ^ 2) -
              (F i - (q / 2) * ‖y i‖ ^ 2) -
            inner ℝ (g i - q • y i)
              (y (shift i) - y i)) :
    ∑ i : Fin K,
        (inner ℝ (g i) (y (shift i) - y i) +
          (‖g (shift i) - g i‖ ^ 2 +
              q * ‖y (shift i) - y i‖ ^ 2 -
              2 * q *
                inner ℝ (g (shift i) - g i) (y (shift i) - y i)) /
            (2 * (1 - q))) ≤ 0 := by
  have hden : 0 < 2 * (1 - q) := by
    linarith
  have hden_ne : 2 * (1 - q) ≠ 0 := ne_of_gt hden
  have hpair :
      ∀ i : Fin K,
        inner ℝ (g i) (y (shift i) - y i) +
            (‖g (shift i) - g i‖ ^ 2 +
                q * ‖y (shift i) - y i‖ ^ 2 -
                2 * q *
                  inner ℝ (g (shift i) - g i) (y (shift i) - y i)) /
              (2 * (1 - q)) ≤
          F (shift i) - F i := by
    intro i
    let dx : Vec d := y (shift i) - y i
    let dg : Vec d := g (shift i) - g i
    have hnorm_shift :
        ‖(g (shift i) - q • y (shift i)) -
              (g i - q • y i)‖ ^ 2 =
          ‖dg‖ ^ 2 + q ^ 2 * ‖dx‖ ^ 2 -
            2 * q * inner ℝ dg dx := by
      have hvec :
          (g (shift i) - q • y (shift i)) -
              (g i - q • y i) =
            dg - q • dx := by
        simp [dx, dg, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      rw [hvec, norm_sub_sq_real, inner_smul_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos hq0]
      ring
    have hnorm_x :
        (q / 2) *
              (‖y (shift i)‖ ^ 2 - ‖y i‖ ^ 2) -
            inner ℝ (q • y i) dx =
          (q / 2) * ‖dx‖ ^ 2 := by
      have hbase :
          ‖y (shift i) - y i‖ ^ 2 =
            ‖y (shift i)‖ ^ 2 + ‖y i‖ ^ 2 -
              2 * inner ℝ (y (shift i)) (y i) := by
        rw [norm_sub_sq_real]
        ring
      dsimp [dx]
      rw [hbase, inner_smul_left, inner_sub_right]
      simp
      rw [real_inner_comm (y (shift i)) (y i)]
      ring
    have htarget :
        inner ℝ (g i) dx +
            (‖dg‖ ^ 2 + q * ‖dx‖ ^ 2 -
                2 * q * inner ℝ dg dx) /
              (2 * (1 - q)) =
          inner ℝ (g i - q • y i) dx +
            (q / 2) *
                (‖y (shift i)‖ ^ 2 - ‖y i‖ ^ 2) +
            ‖(g (shift i) - q • y (shift i)) -
                (g i - q • y i)‖ ^ 2 /
              (2 * (1 - q)) := by
      have hsplit :
          (‖dg‖ ^ 2 + q * ‖dx‖ ^ 2 -
              2 * q * inner ℝ dg dx) /
              (2 * (1 - q)) =
            ‖(g (shift i) - q • y (shift i)) -
                (g i - q • y i)‖ ^ 2 /
                (2 * (1 - q)) +
              (q / 2) * ‖dx‖ ^ 2 := by
        rw [hnorm_shift]
        have hqne : 1 - q ≠ 0 := by linarith
        field_simp [hden_ne, hqne]
        ring
      have hpidentity :
          inner ℝ (g i) dx + (q / 2) * ‖dx‖ ^ 2 =
            inner ℝ (g i - q • y i) dx +
              (q / 2) *
                (‖y (shift i)‖ ^ 2 - ‖y i‖ ^ 2) := by
        have hnorm_x' := hnorm_x
        rw [real_inner_smul_left] at hnorm_x'
        rw [inner_sub_left, real_inner_smul_left]
        nlinarith [hnorm_x']
      calc
        _ = inner ℝ (g i) dx +
              (‖(g (shift i) - q • y (shift i)) -
                  (g i - q • y i)‖ ^ 2 /
                (2 * (1 - q)) +
                (q / 2) * ‖dx‖ ^ 2) := by
          rw [← hsplit]
        _ = (inner ℝ (g i) dx + (q / 2) * ‖dx‖ ^ 2) +
              ‖(g (shift i) - q • y (shift i)) -
                  (g i - q • y i)‖ ^ 2 /
                (2 * (1 - q)) := by ring
        _ = inner ℝ (g i - q • y i) dx +
              (q / 2) *
                (‖y (shift i)‖ ^ 2 - ‖y i‖ ^ 2) +
              ‖(g (shift i) - q • y (shift i)) -
                  (g i - q • y i)‖ ^ 2 /
                (2 * (1 - q)) := by
          rw [hpidentity]
    have hci' := hci i
    have hci_rearr :
        inner ℝ (g i - q • y i) dx +
            (q / 2) *
                (‖y (shift i)‖ ^ 2 - ‖y i‖ ^ 2) +
            ‖(g (shift i) - q • y (shift i)) -
                (g i - q • y i)‖ ^ 2 /
              (2 * (1 - q)) ≤
          F (shift i) - F i := by
      have hdiv :
          ‖(g (shift i) - q • y (shift i)) -
                (g i - q • y i)‖ ^ 2 /
              (2 * (1 - q)) =
            (1 / (2 * (1 - q))) *
              ‖(g (shift i) - q • y (shift i)) -
                (g i - q • y i)‖ ^ 2 := by
        ring
      rw [hdiv]
      nlinarith [hci']
    rw [htarget]
    exact hci_rearr
  have hsum :
    ∑ i : Fin K,
        (inner ℝ (g i) (y (shift i) - y i) +
          (‖g (shift i) - g i‖ ^ 2 +
              q * ‖y (shift i) - y i‖ ^ 2 -
              2 * q *
                inner ℝ (g (shift i) - g i) (y (shift i) - y i)) /
              (2 * (1 - q))) ≤
        ∑ i : Fin K, (F (shift i) - F i) :=
    Finset.sum_le_sum (fun i _ => hpair i)
  have hFshift :
      (∑ i : Fin K, F (shift i)) = ∑ i : Fin K, F i := by
    exact Fintype.sum_bijective shift hshift
      (fun i => F (shift i)) F (fun _ => rfl)
  rw [Finset.sum_sub_distrib, hFshift] at hsum
  linarith

private def cycleFinShift {K : ℕ} [NeZero K] (n : ℕ) (i : Fin K) : Fin K :=
  (ZMod.finEquiv K).symm ((ZMod.finEquiv K i) + n)

private theorem cycleFinShift_bijective {K : ℕ} [NeZero K] (n : ℕ) :
    Function.Bijective (cycleFinShift n : Fin K → Fin K) := by
  let e : Fin K ≃+* ZMod K := ZMod.finEquiv K
  constructor
  · intro i j hij
    apply e.injective
    have h := congrArg e hij
    simpa [cycleFinShift, e] using h
  · intro j
    refine ⟨e.symm (e j - n), ?_⟩
    apply e.injective
    simp [cycleFinShift, e]

private theorem cycleFinShift_val {K : ℕ} [NeZero K] (n : ℕ) (i : Fin K) :
    (cycleFinShift n i).val = (i.val + n) % K := by
  cases K with
  | zero =>
      exact (NeZero.ne 0 rfl).elim
  | succ K =>
      change (i.val + n % (K + 1)) % (K + 1) = (i.val + n) % (K + 1)
      simp [Nat.add_mod, Nat.mod_eq_of_lt i.isLt]

private theorem cycleFinShift_add {K : ℕ} [NeZero K]
    (m n : ℕ) (i : Fin K) :
    cycleFinShift m (cycleFinShift n i) =
      cycleFinShift (n + m) i := by
  apply (ZMod.finEquiv K).injective
  simp [cycleFinShift, add_assoc, add_left_comm, add_comm]

private theorem cycleFinShift_period {K : ℕ} [NeZero K]
    (n : ℕ) (i : Fin K) :
    cycleFinShift (n + K) i = cycleFinShift n i := by
  apply (ZMod.finEquiv K).injective
  simp [cycleFinShift, add_assoc, add_left_comm, add_comm]

private theorem hbStateAt_fst_eq_iterate_pred
    {q : ℝ} {d : ℕ} (a b : ℝ) (hf : AdmissibleObjective q d)
    (xMinusOne xZero : Vec d) {t : ℕ} (ht : 0 < t) :
    (hbStateAt a b hf xMinusOne xZero t).1 =
      hbIterate a b hf xMinusOne xZero (t - 1) := by
  cases t with
  | zero =>
      omega
  | succ t =>
      rw [hbStateAt_succ]
      simp only [hbStateMap, hbIterate]
      congr 1

private theorem hbIterate_succ_eq_successor
    {q : ℝ} {d : ℕ} (a b : ℝ) (hf : AdmissibleObjective q d)
    (xMinusOne xZero : Vec d) (t : ℕ) :
    hbIterate a b hf xMinusOne xZero (t + 1) =
      hbSuccessor a b hf
        (if t = 0 then xMinusOne
          else hbIterate a b hf xMinusOne xZero (t - 1))
        (hbIterate a b hf xMinusOne xZero t) := by
  change (hbStateAt a b hf xMinusOne xZero (t + 1)).2 = _
  rw [hbStateAt_succ]
  simp only [hbStateMap, hbIterate]
  by_cases ht : t = 0
  · subst t
    simp [hbStateAt_zero]
  · rw [hbStateAt_fst_eq_iterate_pred a b hf xMinusOne xZero
      (Nat.pos_of_ne_zero ht)]
    simp [ht, hbIterate]

private theorem hbSuccessor_left_injective
    {q : ℝ} {d : ℕ} (a b : ℝ) (hf : AdmissibleObjective q d)
    (hb : b ≠ 0) {u u' v : Vec d}
    (h : hbSuccessor a b hf u v = hbSuccessor a b hf u' v) :
    u = u' := by
  apply smul_right_injective (Vec d) hb
  have hu :
      b • u =
        ((1 + b) • v - a • gradient hf.f v) -
          hbSuccessor a b hf u v := by
    unfold hbSuccessor
    abel
  have hu' :
      b • u' =
        ((1 + b) • v - a • gradient hf.f v) -
          hbSuccessor a b hf u' v := by
    unfold hbSuccessor
    abel
  calc
    b • u =
        ((1 + b) • v - a • gradient hf.f v) -
          hbSuccessor a b hf u v := hu
    _ =
        ((1 + b) • v - a • gradient hf.f v) -
          hbSuccessor a b hf u' v := by rw [h]
    _ = b • u' := hu'.symm

private theorem hb_cycle_recurrence
    {q : ℝ} {d K : ℕ} [NeZero K] (a b : ℝ)
    (hf : AdmissibleObjective q d) (xMinusOne xZero : Vec d)
    (hK : 2 ≤ K)
    (hperiod :
      ∀ t : ℕ,
        hbIterate a b hf xMinusOne xZero (t + K) =
          hbIterate a b hf xMinusOne xZero t)
    (hpred :
      xMinusOne = hbIterate a b hf xMinusOne xZero (K - 1)) :
    ∀ i : Fin K,
      hbIterate a b hf xMinusOne xZero (cycleFinShift 1 i).val =
        hbSuccessor a b hf
          (hbIterate a b hf xMinusOne xZero (cycleFinShift (K - 1) i).val)
          (hbIterate a b hf xMinusOne xZero i.val) := by
  intro i
  have hiK : i.val < K := i.isLt
  have hnext := cycleFinShift_val (K := K) 1 i
  have hprev := cycleFinShift_val (K := K) (K - 1) i
  by_cases hi0 : i.val = 0
  · have hrec0 :=
      hbIterate_succ_eq_successor a b hf xMinusOne xZero 0
    have hrec0' :
        hbIterate a b hf xMinusOne xZero 1 =
          hbSuccessor a b hf xMinusOne xZero := by
      simpa [hbIterate_zero] using hrec0
    have hnext0 : (i.val + 1) % K = 1 := by
      rw [hi0]
      exact Nat.mod_eq_of_lt (by omega)
    have hprev0 : (i.val + (K - 1)) % K = K - 1 := by
      rw [hi0]
      simp [Nat.mod_eq_of_lt (by omega : K - 1 < K)]
    have hnext_i : (cycleFinShift 1 i).val = 1 := by
      rw [hnext, hnext0]
    have hprev_i : (cycleFinShift (K - 1) i).val = K - 1 := by
      rw [hprev, hprev0]
    rw [hnext_i, hprev_i, hi0]
    calc
      hbIterate a b hf xMinusOne xZero 1 =
          hbSuccessor a b hf xMinusOne xZero := hrec0'
      _ = hbSuccessor a b hf
          (hbIterate a b hf xMinusOne xZero (K - 1)) xZero := by
        exact congrArg (fun u => hbSuccessor a b hf u xZero) hpred
  · by_cases hilast : i.val + 1 = K
    · have hlast : i.val = K - 1 := by omega
      have hrec :=
        hbIterate_succ_eq_successor a b hf xMinusOne xZero (K - 1)
      have hrec' :
          hbIterate a b hf xMinusOne xZero K =
            hbSuccessor a b hf
              (hbIterate a b hf xMinusOne xZero (K - 2))
              (hbIterate a b hf xMinusOne xZero (K - 1)) := by
        have hrec'' := hrec
        simp only [if_neg (by omega : ¬ K - 1 = 0)] at hrec''
        have hleft : K - 1 + 1 = K := Nat.sub_add_cancel (by omega)
        have hright : K - 1 - 1 = K - 2 := by omega
        rw [hleft, hright] at hrec''
        exact hrec''
      have hp0 := hperiod 0
      have hprev_last : ((K - 1) + (K - 1)) % K = K - 2 := by
        rw [show (K - 1) + (K - 1) = K + (K - 2) by omega,
          Nat.add_mod]
        simp [Nat.mod_eq_of_lt (by omega : K - 2 < K)]
      have hnext_last : (cycleFinShift 1 i).val = 0 := by
        rw [hnext, hlast, show K - 1 + 1 = K by omega, Nat.mod_self]
      have hprev_i : (cycleFinShift (K - 1) i).val = K - 2 := by
        rw [hprev, hlast, hprev_last]
      rw [hnext_last, hprev_i, hlast]
      have hp0' :
          hbIterate a b hf xMinusOne xZero K =
            hbIterate a b hf xMinusOne xZero 0 := by
        simpa using hp0
      calc
        hbIterate a b hf xMinusOne xZero 0 =
            hbIterate a b hf xMinusOne xZero K := hp0'.symm
        _ = hbSuccessor a b hf
            (hbIterate a b hf xMinusOne xZero (K - 2))
            (hbIterate a b hf xMinusOne xZero (K - 1)) := hrec'
    · have hi1 : 0 < i.val := by omega
      have hiLast : i.val + 1 < K := by omega
      have hrec :=
        hbIterate_succ_eq_successor a b hf xMinusOne xZero i.val
      have hnext_mid : (i.val + 1) % K = i.val + 1 :=
        Nat.mod_eq_of_lt hiLast
      have hprev_mid : (i.val + (K - 1)) % K = i.val - 1 := by
        rw [show i.val + (K - 1) = K + (i.val - 1) by omega,
          Nat.add_mod]
        simp [Nat.mod_eq_of_lt (by omega : i.val - 1 < K)]
      have hnext_i : (cycleFinShift 1 i).val = i.val + 1 := by
        rw [hnext, hnext_mid]
      have hprev_i : (cycleFinShift (K - 1) i).val = i.val - 1 := by
        rw [hprev, hprev_mid]
      rw [hnext_i, hprev_i]
      have hrec' :
          hbIterate a b hf xMinusOne xZero (i.val + 1) =
            hbSuccessor a b hf
              (hbIterate a b hf xMinusOne xZero (i.val - 1))
              (hbIterate a b hf xMinusOne xZero i.val) := by
        have hrec'' := hrec
        simp only [if_neg (by omega : ¬ i.val = 0)] at hrec''
        exact hrec''
      exact hrec'

private theorem weighted_nonpositive_sum_forces_nonzero_terms_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (zero : ι) (s w : ι → ℝ)
    (hs : ∀ j, 0 ≤ s j) (hw0 : w zero = 0)
    (hw : ∀ j, j ≠ zero → 0 < w j)
    (hsum : ∑ j : ι, s j * w j ≤ 0) :
    ∀ j, j ≠ zero → s j = 0 := by
  have hterm_nonneg : ∀ j, 0 ≤ s j * w j := by
    intro j
    by_cases hj : j = zero
    · subst j
      simp [hw0]
    · exact mul_nonneg (hs j) (le_of_lt (hw j hj))
  have hsum_nonneg : 0 ≤ ∑ j : ι, s j * w j :=
    Finset.sum_nonneg (fun j _ => hterm_nonneg j)
  intro j hj
  have hterm_le :
      s j * w j ≤ ∑ k : ι, s k * w k :=
    Finset.single_le_sum (fun k _ => hterm_nonneg k) (Finset.mem_univ j)
  have hterm_nonpos : s j * w j ≤ 0 := le_trans hterm_le hsum
  have hsj : 0 ≤ s j := hs j
  have hwj : 0 < w j := hw j hj
  nlinarith

private noncomputable def hbCycleRho {K : ℕ} [NeZero K]
    (j i : Fin K) : ℂ :=
  ZMod.stdAddChar (-(ZMod.finEquiv K j * ZMod.finEquiv K i))

private theorem hb_cycle_character_sum
    {K : ℕ} [NeZero K] (u : ZMod K) :
    ∑ i : Fin K, ZMod.stdAddChar (u * ZMod.finEquiv K i) =
      if u = 0 then (K : ℂ) else 0 := by
  let e := ZMod.finEquiv K
  have hsum :
      ∑ z : ZMod K, ZMod.stdAddChar (u * z) =
        if u = 0 then (K : ℂ) else 0 := by
    let m : ZMod K →+ ZMod K := AddMonoidHom.mulLeft u
    have h := AddChar.sum_eq_ite
      ((ZMod.stdAddChar (N := K)).compAddMonoidHom m)
    by_cases hu : u = 0
    · subst u
      have hm : m = 0 := by
        ext z
        simp [m]
      rw [hm] at h
      simpa using h
    · have hm : m ≠ 0 := by
        intro hm
        have hm1 := congrArg (fun f => f 1) hm
        simp [m] at hm1
        exact hu hm1
      have hcomp :
          (ZMod.stdAddChar (N := K)).compAddMonoidHom m ≠ 0 := by
        intro hcomp
        have hcomp1 := congrArg
          (fun f : AddChar (ZMod K) ℂ => f (1 : ZMod K)) hcomp
        have hu1 : ZMod.stdAddChar (N := K) u = 1 := by
          simpa [m] using hcomp1
        have hu0 : u = 0 := by
          apply ZMod.injective_stdAddChar
          simpa using hu1
        exact hu hu0
      rw [if_neg hcomp] at h
      rw [if_neg hu]
      simpa [m] using h
  calc
    ∑ i : Fin K, ZMod.stdAddChar (u * ZMod.finEquiv K i) =
        ∑ z : ZMod K, ZMod.stdAddChar (u * z) := by
      exact Fintype.sum_bijective e e.bijective _ _ (fun i => rfl)
    _ = if u = 0 then (K : ℂ) else 0 := hsum

private theorem hb_cycle_dft_root_orthogonality
    {K : ℕ} [NeZero K] (j l : Fin K) :
    ∑ i : Fin K, hbCycleRho j i * starRingEnd ℂ (hbCycleRho l i) =
      if j = l then (K : ℂ) else 0 := by
  let e := ZMod.finEquiv K
  have hconj (i : Fin K) :
      starRingEnd ℂ (hbCycleRho l i) =
        ZMod.stdAddChar (ZMod.finEquiv K l * ZMod.finEquiv K i) := by
    rw [hbCycleRho, ← AddChar.inv_apply_eq_conj]
    rw [AddChar.map_neg_eq_inv]
    simp
  have hterm (i : Fin K) :
      hbCycleRho j i * starRingEnd ℂ (hbCycleRho l i) =
        ZMod.stdAddChar
          ((ZMod.finEquiv K l - ZMod.finEquiv K j) *
            ZMod.finEquiv K i) := by
    rw [hconj, hbCycleRho, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [hterm]
  rw [hb_cycle_character_sum]
  have hzero :
      ZMod.finEquiv K l - ZMod.finEquiv K j = 0 ↔ j = l := by
    constructor
    · intro h
      have h' : ZMod.finEquiv K l = ZMod.finEquiv K j :=
        sub_eq_zero.mp h
      exact (e.injective h').symm
    · intro h
      subst l
      simp
  simp [hzero]

private noncomputable def hbCycleDftCoord {K : ℕ} [NeZero K]
    (x : Fin K → ℂ) (j : Fin K) : ℂ :=
  ∑ i : Fin K, hbCycleRho j i * x i

private theorem hb_cycle_dft_shift
    {K : ℕ} [NeZero K] (x : Fin K → ℂ) (n : ℕ) (j : Fin K) :
    hbCycleDftCoord (fun i => x (cycleFinShift n i)) j =
      ZMod.stdAddChar (ZMod.finEquiv K j * (n : ZMod K)) *
        hbCycleDftCoord x j := by
  have hshift (i : Fin K) :
      hbCycleRho j i =
        ZMod.stdAddChar (ZMod.finEquiv K j * (n : ZMod K)) *
          hbCycleRho j (cycleFinShift n i) := by
    rw [hbCycleRho, hbCycleRho]
    have he :
        ZMod.finEquiv K (cycleFinShift n i) =
          ZMod.finEquiv K i + n := by
      simp [cycleFinShift]
    rw [he, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  unfold hbCycleDftCoord
  calc
    (∑ i : Fin K, hbCycleRho j i * x (cycleFinShift n i)) =
        ∑ i : Fin K,
          (ZMod.stdAddChar (ZMod.finEquiv K j * (n : ZMod K)) *
            hbCycleRho j (cycleFinShift n i)) * x (cycleFinShift n i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hshift i]
    _ = ZMod.stdAddChar (ZMod.finEquiv K j * (n : ZMod K)) *
          ∑ i : Fin K, hbCycleRho j (cycleFinShift n i) *
            x (cycleFinShift n i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
  have hbij := cycleFinShift_bijective (K := K) n
  have hsum :
      ∑ i : Fin K, hbCycleRho j (cycleFinShift n i) *
          x (cycleFinShift n i) =
        ∑ i : Fin K, hbCycleRho j i * x i := by
    exact Fintype.sum_bijective (cycleFinShift n) hbij
      (fun i => hbCycleRho j (cycleFinShift n i) *
        x (cycleFinShift n i))
      (fun i => hbCycleRho j i * x i) (fun _ => rfl)
  rw [hsum]

private theorem hb_cycle_dft_scalar_recurrence_transfer
    {K : ℕ} [NeZero K] (a b : ℂ) (Y G : Fin K → ℂ)
    (hrec :
      ∀ i : Fin K,
        Y (cycleFinShift 1 i) =
          (1 + b) * Y i - b * Y (cycleFinShift (K - 1) i) - a * G i)
    (ha : a ≠ 0) (j : Fin K) :
    hbCycleDftCoord G j =
      (((1 + b) - ZMod.stdAddChar (ZMod.finEquiv K j) -
          b * ZMod.stdAddChar
            (ZMod.finEquiv K j * ((K - 1 : ℕ) : ZMod K))) / a) *
        hbCycleDftCoord Y j := by
  have hsum :
      hbCycleDftCoord (fun i => Y (cycleFinShift 1 i)) j =
        (1 + b) * hbCycleDftCoord Y j -
          b * hbCycleDftCoord (fun i => Y (cycleFinShift (K - 1) i)) j -
            a * hbCycleDftCoord G j := by
    unfold hbCycleDftCoord
    calc
      (∑ i : Fin K, hbCycleRho j i * Y (cycleFinShift 1 i)) =
          ∑ i : Fin K,
            hbCycleRho j i *
              ((1 + b) * Y i - b * Y (cycleFinShift (K - 1) i) - a * G i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hrec i]
      _ = (1 + b) * (∑ i : Fin K, hbCycleRho j i * Y i) -
            b * (∑ i : Fin K,
              hbCycleRho j i * Y (cycleFinShift (K - 1) i)) -
              a * (∑ i : Fin K, hbCycleRho j i * G i) := by
        simp only [mul_sub, mul_add, Finset.sum_sub_distrib,
          Finset.sum_add_distrib]
        have hmul (c : ℂ) (f : Fin K → ℂ) :
            ∑ i : Fin K, hbCycleRho j i * (c * f i) =
              c * ∑ i : Fin K, hbCycleRho j i * f i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        rw [hmul (1 + b) Y, hmul b (fun i => Y (cycleFinShift (K - 1) i)),
          hmul a G]
  have hnext := hb_cycle_dft_shift Y 1 j
  have hprev := hb_cycle_dft_shift Y (K - 1) j
  have hnext' :
      hbCycleDftCoord (fun i => Y (cycleFinShift 1 i)) j =
        ZMod.stdAddChar (ZMod.finEquiv K j) * hbCycleDftCoord Y j := by
    simpa using hnext
  rw [hnext', hprev] at hsum
  have hsolve :
      a * hbCycleDftCoord G j =
        ((1 + b) - ZMod.stdAddChar (ZMod.finEquiv K j) -
            b * ZMod.stdAddChar
              (ZMod.finEquiv K j * ((K - 1 : ℕ) : ZMod K))) *
          hbCycleDftCoord Y j := by
    linear_combination hsum
  calc
    hbCycleDftCoord G j =
        a⁻¹ * (a * hbCycleDftCoord G j) := by
          symm
          rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
    _ = a⁻¹ *
        (((1 + b) - ZMod.stdAddChar (ZMod.finEquiv K j) -
            b * ZMod.stdAddChar
              (ZMod.finEquiv K j * ((K - 1 : ℕ) : ZMod K))) *
          hbCycleDftCoord Y j) := by rw [hsolve]
    _ = (((1 + b) - ZMod.stdAddChar (ZMod.finEquiv K j) -
          b * ZMod.stdAddChar
            (ZMod.finEquiv K j * ((K - 1 : ℕ) : ZMod K))) / a) *
        hbCycleDftCoord Y j := by
          field_simp

private theorem hb_cycle_zmod_pred {K : ℕ} [NeZero K] :
    ((K - 1 : ℕ) : ZMod K) = -1 := by
  have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr (NeZero.ne K)
  have hsum :
      ((K - 1 : ℕ) : ZMod K) + 1 = 0 := by
    rw [← Nat.cast_one (R := ZMod K), ← Nat.cast_add,
      Nat.sub_add_cancel hK1, ZMod.natCast_self]
  linear_combination hsum

private theorem hb_cycle_dft_prev_character {K : ℕ} [NeZero K] (j : Fin K) :
    ZMod.stdAddChar
        (ZMod.finEquiv K j * ((K - 1 : ℕ) : ZMod K)) =
      starRingEnd ℂ (ZMod.stdAddChar (ZMod.finEquiv K j)) := by
  rw [hb_cycle_zmod_pred]
  have hneg :
      ZMod.finEquiv K j * (-1 : ZMod K) =
        -(ZMod.finEquiv K j) := by ring
  rw [hneg, AddChar.map_neg_eq_inv]
  rw [← AddChar.inv_apply_eq_conj]

private theorem hb_cycle_dft_rho_symm {K : ℕ} [NeZero K]
    (j i : Fin K) : hbCycleRho j i = hbCycleRho i j := by
  rw [hbCycleRho, hbCycleRho]
  congr 2
  ring

private theorem hb_cycle_dft_inversion
    {K : ℕ} [NeZero K] (x : Fin K → ℂ) (i : Fin K) :
    (K : ℂ)⁻¹ *
        ∑ j : Fin K, starRingEnd ℂ (hbCycleRho j i) *
          hbCycleDftCoord x j = x i := by
  have hsum :
      ∑ j : Fin K, starRingEnd ℂ (hbCycleRho j i) *
          hbCycleDftCoord x j =
        (K : ℂ) * x i := by
    simp only [hbCycleDftCoord, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul]
    have hinner (k : Fin K) :
        ∑ j : Fin K, starRingEnd ℂ (hbCycleRho j i) * hbCycleRho j k =
          if k = i then (K : ℂ) else 0 := by
      calc
        ∑ j : Fin K, starRingEnd ℂ (hbCycleRho j i) * hbCycleRho j k =
            ∑ j : Fin K, hbCycleRho k j *
              starRingEnd ℂ (hbCycleRho i j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hb_cycle_dft_rho_symm j k, hb_cycle_dft_rho_symm j i]
          ring
        _ = if k = i then (K : ℂ) else 0 :=
          hb_cycle_dft_root_orthogonality (K := K) k i
    simp_rw [hinner]
    simp
  rw [hsum]
  have hKc : (K : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne K)
  calc
    (K : ℂ)⁻¹ * ((K : ℂ) * x i) =
        ((K : ℂ)⁻¹ * (K : ℂ)) * x i := by ring
    _ = x i := by rw [inv_mul_cancel₀ hKc, one_mul]

private theorem hb_cycle_dft_parseval_complex
    {K : ℕ} [NeZero K] (x z : Fin K → ℂ) :
    (K : ℂ)⁻¹ *
        ∑ j : Fin K, hbCycleDftCoord x j *
          starRingEnd ℂ (hbCycleDftCoord z j) =
      ∑ i : Fin K, x i * starRingEnd ℂ (z i) := by
  have hstar (j : Fin K) :
      starRingEnd ℂ (hbCycleDftCoord z j) =
        ∑ i : Fin K, starRingEnd ℂ (hbCycleRho j i) *
          starRingEnd ℂ (z i) := by
    unfold hbCycleDftCoord
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_mul]
  have hinv (i : Fin K) :
      x i = (K : ℂ)⁻¹ *
        ∑ j : Fin K, starRingEnd ℂ (hbCycleRho j i) *
          hbCycleDftCoord x j :=
    (hb_cycle_dft_inversion x i).symm
  symm
  calc
    ∑ i : Fin K, x i * starRingEnd ℂ (z i) =
        ∑ i : Fin K,
          ((K : ℂ)⁻¹ *
            ∑ j : Fin K, starRingEnd ℂ (hbCycleRho j i) *
              hbCycleDftCoord x j) *
            starRingEnd ℂ (z i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hinv]
    _ = (K : ℂ)⁻¹ *
        ∑ j : Fin K, hbCycleDftCoord x j *
          ∑ i : Fin K, starRingEnd ℂ (hbCycleRho j i) *
            starRingEnd ℂ (z i) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (K : ℂ)⁻¹ *
        ∑ j : Fin K, hbCycleDftCoord x j *
          starRingEnd ℂ (hbCycleDftCoord z j) := by
      apply congrArg (fun w : ℂ => (K : ℂ)⁻¹ * w)
      apply Finset.sum_congr rfl
      intro j hj
      rw [hstar]

private theorem hb_cycle_real_inner_lag_parseval
    {K : ℕ} [NeZero K] (x z : Fin K → ℝ) (n : ℕ) :
    ∑ i : Fin K, x i * (z (cycleFinShift n i) - z i) =
      Complex.re
        ((K : ℂ)⁻¹ *
          ∑ j : Fin K,
            (hbCycleDftCoord (fun i => (x i : ℂ)) j *
                starRingEnd ℂ
                  (ZMod.stdAddChar (ZMod.finEquiv K j * (n : ZMod K))) *
                starRingEnd ℂ (hbCycleDftCoord (fun i => (z i : ℂ)) j) -
              hbCycleDftCoord (fun i => (x i : ℂ)) j *
                starRingEnd ℂ (hbCycleDftCoord (fun i => (z i : ℂ)) j))) := by
  have hparseval :=
    hb_cycle_dft_parseval_complex
      (fun i => (x i : ℂ))
      (fun i => ((z (cycleFinShift n i)) : ℂ))
  have hshift := hb_cycle_dft_shift (fun i => (z i : ℂ)) n
  simp_rw [hshift] at hparseval
  have hparseval0 :=
    hb_cycle_dft_parseval_complex
      (fun i => (x i : ℂ))
      (fun i => ((z i) : ℂ))
  have hreal :
      (∑ i : Fin K, ((x i : ℂ) *
          starRingEnd ℂ ((z (cycleFinShift n i)) : ℂ) -
        (x i : ℂ) * starRingEnd ℂ ((z i) : ℂ))) =
        (∑ i : Fin K, (x i : ℂ) *
          starRingEnd ℂ ((z (cycleFinShift n i)) : ℂ)) -
          ∑ i : Fin K, (x i : ℂ) * starRingEnd ℂ ((z i) : ℂ) := by
    rw [Finset.sum_sub_distrib]
  have hparseval' :
      (K : ℂ)⁻¹ *
          ∑ j : Fin K,
            (hbCycleDftCoord (fun i => (x i : ℂ)) j *
                starRingEnd ℂ
                  (ZMod.stdAddChar (ZMod.finEquiv K j * (n : ZMod K)) *
                    hbCycleDftCoord (fun i => (z i : ℂ)) j) -
              hbCycleDftCoord (fun i => (x i : ℂ)) j *
                starRingEnd ℂ (hbCycleDftCoord (fun i => (z i : ℂ)) j)) =
        ∑ i : Fin K, (x i : ℂ) *
          starRingEnd ℂ ((z (cycleFinShift n i)) : ℂ) -
          ∑ i : Fin K, (x i : ℂ) * starRingEnd ℂ ((z i) : ℂ) := by
    calc
      (K : ℂ)⁻¹ *
          ∑ j : Fin K,
            (hbCycleDftCoord (fun i => (x i : ℂ)) j *
                starRingEnd ℂ
                  (ZMod.stdAddChar (ZMod.finEquiv K j * (n : ZMod K)) *
                    hbCycleDftCoord (fun i => (z i : ℂ)) j) -
              hbCycleDftCoord (fun i => (x i : ℂ)) j *
                starRingEnd ℂ (hbCycleDftCoord (fun i => (z i : ℂ)) j)) =
          (K : ℂ)⁻¹ *
            (∑ j : Fin K,
              hbCycleDftCoord (fun i => (x i : ℂ)) j *
                starRingEnd ℂ
                  (ZMod.stdAddChar (ZMod.finEquiv K j * (n : ZMod K)) *
                    hbCycleDftCoord (fun i => (z i : ℂ)) j) -
              ∑ j : Fin K,
                hbCycleDftCoord (fun i => (x i : ℂ)) j *
                  starRingEnd ℂ (hbCycleDftCoord (fun i => (z i : ℂ)) j)) := by
            rw [Finset.sum_sub_distrib]
      _ =
          (K : ℂ)⁻¹ *
              ∑ j : Fin K,
                hbCycleDftCoord (fun i => (x i : ℂ)) j *
                  starRingEnd ℂ
                    (ZMod.stdAddChar (ZMod.finEquiv K j * (n : ZMod K)) *
                      hbCycleDftCoord (fun i => (z i : ℂ)) j) -
            (K : ℂ)⁻¹ *
              ∑ j : Fin K,
                hbCycleDftCoord (fun i => (x i : ℂ)) j *
                  starRingEnd ℂ (hbCycleDftCoord (fun i => (z i : ℂ)) j) := by
            rw [mul_sub]
      _ =
          ∑ i : Fin K, (x i : ℂ) *
              starRingEnd ℂ ((z (cycleFinShift n i)) : ℂ) -
            ∑ i : Fin K, (x i : ℂ) * starRingEnd ℂ ((z i) : ℂ) := by
            rw [hparseval, hparseval0]
  have hparseval'' :
      (K : ℂ)⁻¹ *
          ∑ j : Fin K,
            (hbCycleDftCoord (fun i => (x i : ℂ)) j *
                starRingEnd ℂ
                  (ZMod.stdAddChar (ZMod.finEquiv K j * (n : ZMod K))) *
                starRingEnd ℂ (hbCycleDftCoord (fun i => (z i : ℂ)) j) -
              hbCycleDftCoord (fun i => (x i : ℂ)) j *
                starRingEnd ℂ (hbCycleDftCoord (fun i => (z i : ℂ)) j)) =
        ∑ i : Fin K, (x i : ℂ) *
          starRingEnd ℂ ((z (cycleFinShift n i)) : ℂ) -
          ∑ i : Fin K, (x i : ℂ) * starRingEnd ℂ ((z i) : ℂ) := by
    simpa [map_mul, mul_assoc] using hparseval'
  have hre := congrArg Complex.re hparseval''
  simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im] at hre
  have hrealR :
      (∑ i : Fin K, x i * z (cycleFinShift n i)) -
          ∑ i : Fin K, x i * z i =
        ∑ i : Fin K, x i * (z (cycleFinShift n i) - z i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hrealR] at hre
  simpa [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im] using hre.symm

private theorem hb_cycle_real_inner_parseval
    {K : ℕ} [NeZero K] (x z : Fin K → ℝ) :
    ∑ i : Fin K, x i * z i =
      Complex.re
        ((K : ℂ)⁻¹ *
          ∑ j : Fin K,
            hbCycleDftCoord (fun i => (x i : ℂ)) j *
              starRingEnd ℂ (hbCycleDftCoord (fun i => (z i : ℂ)) j)) := by
  have hparseval :=
    hb_cycle_dft_parseval_complex
      (fun i => (x i : ℂ))
      (fun i => (z i : ℂ))
  have hre := congrArg Complex.re hparseval
  simpa [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im] using hre.symm

private theorem hb_cycle_real_norm_lag_parseval
    {K : ℕ} [NeZero K] (x : Fin K → ℝ) (n : ℕ) :
    ∑ i : Fin K, (x (cycleFinShift n i) - x i) ^ 2 =
      Complex.re
        ((K : ℂ)⁻¹ *
          ∑ j : Fin K,
            (ZMod.stdAddChar (ZMod.finEquiv K j * (n : ZMod K)) *
                  hbCycleDftCoord (fun i => (x i : ℂ)) j -
                hbCycleDftCoord (fun i => (x i : ℂ)) j) *
              starRingEnd ℂ
                (ZMod.stdAddChar (ZMod.finEquiv K j * (n : ZMod K)) *
                    hbCycleDftCoord (fun i => (x i : ℂ)) j -
                  hbCycleDftCoord (fun i => (x i : ℂ)) j)) := by
  have hparseval :=
    hb_cycle_dft_parseval_complex
      (fun i => ((x (cycleFinShift n i) - x i) : ℂ))
      (fun i => ((x (cycleFinShift n i) - x i) : ℂ))
  have hshift := hb_cycle_dft_shift (fun i => (x i : ℂ)) n
  have hdiff :
      hbCycleDftCoord (fun i => ((x (cycleFinShift n i) - x i) : ℂ)) =
        fun j =>
          ZMod.stdAddChar (ZMod.finEquiv K j * (n : ZMod K)) *
              hbCycleDftCoord (fun i => (x i : ℂ)) j -
            hbCycleDftCoord (fun i => (x i : ℂ)) j := by
    funext j
    unfold hbCycleDftCoord
    simp only [mul_sub, Finset.sum_sub_distrib]
    have hs :
        ∑ i : Fin K, hbCycleRho j i * (x (cycleFinShift n i) : ℂ) =
          ZMod.stdAddChar (ZMod.finEquiv K j * (n : ZMod K)) *
            ∑ i : Fin K, hbCycleRho j i * (x i : ℂ) := by
      simpa [hbCycleDftCoord] using hshift j
    rw [hs]
  rw [hdiff] at hparseval
  have hre := congrArg Complex.re hparseval
  simpa [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, pow_two] using hre.symm

private theorem hb_cycle_real_cross_diff_parseval
    {K : ℕ} [NeZero K] (x z : Fin K → ℝ) (n : ℕ) :
    ∑ i : Fin K,
        (x (cycleFinShift n i) - x i) * (z (cycleFinShift n i) - z i) =
      Complex.re
        ((K : ℂ)⁻¹ *
          ∑ j : Fin K,
            (ZMod.stdAddChar (ZMod.finEquiv K j * (n : ZMod K)) *
                  hbCycleDftCoord (fun i => (x i : ℂ)) j -
                hbCycleDftCoord (fun i => (x i : ℂ)) j) *
              starRingEnd ℂ
                (ZMod.stdAddChar (ZMod.finEquiv K j * (n : ZMod K)) *
                    hbCycleDftCoord (fun i => (z i : ℂ)) j -
                  hbCycleDftCoord (fun i => (z i : ℂ)) j)) := by
  have hparseval :=
    hb_cycle_dft_parseval_complex
      (fun i => ((x (cycleFinShift n i) - x i) : ℂ))
      (fun i => ((z (cycleFinShift n i) - z i) : ℂ))
  have hshiftx := hb_cycle_dft_shift (fun i => (x i : ℂ)) n
  have hshiftz := hb_cycle_dft_shift (fun i => (z i : ℂ)) n
  have hdiffx :
      hbCycleDftCoord
          (fun i => ((x (cycleFinShift n i) - x i) : ℂ)) =
        fun j =>
          ZMod.stdAddChar (ZMod.finEquiv K j * (n : ZMod K)) *
              hbCycleDftCoord (fun i => (x i : ℂ)) j -
            hbCycleDftCoord (fun i => (x i : ℂ)) j := by
    funext j
    unfold hbCycleDftCoord
    simp only [mul_sub, Finset.sum_sub_distrib]
    have hs :
        ∑ i : Fin K, hbCycleRho j i * (x (cycleFinShift n i) : ℂ) =
          ZMod.stdAddChar (ZMod.finEquiv K j * (n : ZMod K)) *
            ∑ i : Fin K, hbCycleRho j i * (x i : ℂ) := by
      simpa [hbCycleDftCoord] using hshiftx j
    rw [hs]
  have hdiffz :
      hbCycleDftCoord
          (fun i => ((z (cycleFinShift n i) - z i) : ℂ)) =
        fun j =>
          ZMod.stdAddChar (ZMod.finEquiv K j * (n : ZMod K)) *
              hbCycleDftCoord (fun i => (z i : ℂ)) j -
            hbCycleDftCoord (fun i => (z i : ℂ)) j := by
    funext j
    unfold hbCycleDftCoord
    simp only [mul_sub, Finset.sum_sub_distrib]
    have hs :
        ∑ i : Fin K, hbCycleRho j i * (z (cycleFinShift n i) : ℂ) =
          ZMod.stdAddChar (ZMod.finEquiv K j * (n : ZMod K)) *
            ∑ i : Fin K, hbCycleRho j i * (z i : ℂ) := by
      simpa [hbCycleDftCoord] using hshiftz j
    rw [hs]
  rw [hdiffx, hdiffz] at hparseval
  have hre := congrArg Complex.re hparseval
  simpa [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im] using hre.symm

private theorem hb_cycle_constant_of_nonzero_dft_zero
    {K d : ℕ} [NeZero K] (y : Fin K → Vec d)
    (hzero :
      ∀ j : Fin K, j ≠ 0 →
        ∀ r : Fin d,
          hbCycleDftCoord (fun i => ((y i).ofLp r : ℂ)) j = 0) :
    ∀ i j : Fin K, y i = y j := by
  intro i j
  ext r
  let X : Fin K → ℂ := fun k => hbCycleDftCoord
    (fun l => ((y l).ofLp r : ℂ)) k
  have hsum (k : Fin K) :
      ∑ l : Fin K, starRingEnd ℂ (hbCycleRho l k) * X l =
        starRingEnd ℂ (hbCycleRho 0 k) * X 0 := by
    rw [Finset.sum_eq_single 0]
    · intro l hl hne
      simp [X, hzero l hne r]
    · simp
  have hinv (k : Fin K) :
      (K : ℂ)⁻¹ * (starRingEnd ℂ (hbCycleRho 0 k) * X 0) =
        ((y k).ofLp r : ℂ) := by
    have h := hb_cycle_dft_inversion
      (fun l => ((y l).ofLp r : ℂ)) k
    rw [show hbCycleDftCoord
      (fun l => ((y l).ofLp r : ℂ)) = X by rfl] at h
    rw [hsum k] at h
    exact h
  have heq : ((y i).ofLp r : ℂ) = ((y j).ofLp r : ℂ) := by
    rw [← hinv i, ← hinv j]
    simp [hbCycleRho]
  exact_mod_cast congrArg Complex.re heq

private theorem hb_cycle_stdAddChar_normSq {K : ℕ} [NeZero K] (u : ZMod K) :
    Complex.normSq (ZMod.stdAddChar u) = 1 := by
  rw [Complex.normSq_eq_norm_sq, ZMod.stdAddChar_apply]
  change ‖(ZMod.toCircle u : ℂ)‖ ^ 2 = 1
  rw [Circle.norm_coe]
  norm_num

private theorem hb_cycle_root_eq_one_iff {K : ℕ} [NeZero K] (j : Fin K) :
    ZMod.stdAddChar (ZMod.finEquiv K j) = 1 ↔ j = 0 := by
  constructor
  · intro h
    have hz : ZMod.finEquiv K j = 0 := by
      apply ZMod.injective_stdAddChar
      simpa using h
    have hz' : ZMod.finEquiv K j = ZMod.finEquiv K 0 := by
      simpa using hz
    exact (ZMod.finEquiv K).injective hz'
  · intro h
    subst j
    simp

private def hbCycleWstar (c : ℝ) : ℝ :=
  (1 + (32 / 25 : ℝ) * c ^ 2 * (1 + c)) *
      (2 * (1 - c) * (1 + (3 / 5 : ℝ) ^ 2 -
          2 * (3 / 5 : ℝ) * c) -
        (113 / 50 : ℝ) * (1 + (1 / 100 : ℝ)) * (1 + 3 / 5 : ℝ) *
          (1 - c) +
        (113 / 50 : ℝ) ^ 2 * (1 / 100 : ℝ)) +
    (1 + c) * (1 + (16 / 25 : ℝ) * c - (32 / 25 : ℝ) * c ^ 3) *
      ((113 / 50 : ℝ) * (1 - 1 / 100 : ℝ) * (1 - 3 / 5 : ℝ))

private theorem hb_cycle_bernstein_degree5_lower_bound
    {m t b0 b1 b2 b3 b4 b5 : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hm0 : m ≤ b0) (hm1 : m ≤ b1) (hm2 : m ≤ b2)
    (hm3 : m ≤ b3) (hm4 : m ≤ b4) (hm5 : m ≤ b5) :
    m ≤
      b0 * (1 - t) ^ 5 +
        5 * b1 * t * (1 - t) ^ 4 +
        10 * b2 * t ^ 2 * (1 - t) ^ 3 +
        10 * b3 * t ^ 3 * (1 - t) ^ 2 +
        5 * b4 * t ^ 4 * (1 - t) +
        b5 * t ^ 5 := by
  have hu : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hsq : 0 ≤ t ^ 2 := by
    simpa [pow_two] using sq_nonneg t
  have hb0 : 0 ≤ (1 - t) ^ 5 := pow_nonneg hu 5
  have hb1 : 0 ≤ 5 * t * (1 - t) ^ 4 := by
    exact mul_nonneg (mul_nonneg (by norm_num) ht0) (pow_nonneg hu 4)
  have hb2 : 0 ≤ 10 * t ^ 2 * (1 - t) ^ 3 := by
    exact mul_nonneg (mul_nonneg (by norm_num) hsq) (pow_nonneg hu 3)
  have hb3 : 0 ≤ 10 * t ^ 3 * (1 - t) ^ 2 := by
    exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ht0 3))
      (pow_nonneg hu 2)
  have hb4 : 0 ≤ 5 * t ^ 4 * (1 - t) := by
    exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ht0 4)) hu
  have hb5 : 0 ≤ t ^ 5 := pow_nonneg ht0 5
  have h0 : 0 ≤ (b0 - m) * (1 - t) ^ 5 :=
    mul_nonneg (sub_nonneg.mpr hm0) hb0
  have h1 : 0 ≤ (b1 - m) * (5 * t * (1 - t) ^ 4) :=
    mul_nonneg (sub_nonneg.mpr hm1) hb1
  have h2 : 0 ≤ (b2 - m) * (10 * t ^ 2 * (1 - t) ^ 3) :=
    mul_nonneg (sub_nonneg.mpr hm2) hb2
  have h3 : 0 ≤ (b3 - m) * (10 * t ^ 3 * (1 - t) ^ 2) :=
    mul_nonneg (sub_nonneg.mpr hm3) hb3
  have h4 : 0 ≤ (b4 - m) * (5 * t ^ 4 * (1 - t)) :=
    mul_nonneg (sub_nonneg.mpr hm4) hb4
  have h5 : 0 ≤ (b5 - m) * t ^ 5 :=
    mul_nonneg (sub_nonneg.mpr hm5) hb5
  have hpart :
      (1 - t) ^ 5 + 5 * t * (1 - t) ^ 4 + 10 * t ^ 2 * (1 - t) ^ 3 +
          10 * t ^ 3 * (1 - t) ^ 2 + 5 * t ^ 4 * (1 - t) + t ^ 5 = 1 := by
    ring
  nlinarith [h0, h1, h2, h3, h4, h5, hpart]

private theorem hb_cycle_central_polynomial_lower_on_unit_interval
    {c : ℝ} (hc : |c| ≤ 1) :
    (557731 / 10 : ℝ) ≤
      19200000 * c ^ 5 + 297600 * c ^ 4 - 25951072 * c ^ 3 +
        11531168 * c ^ 2 - 660 * c + 86725 := by
  have hcl := abs_le.mp hc
  by_cases hneg : c ≤ 0
  · let t : ℝ := c + 1
    have ht0 : 0 ≤ t := by
      dsimp [t]
      linarith [hcl.1]
    have ht1 : t ≤ 1 := by
      dsimp [t]
      linarith
    have hbern :
        19200000 * c ^ 5 + 297600 * c ^ 4 - 25951072 * c ^ 3 +
            11531168 * c ^ 2 - 660 * c + 86725 =
          (93336125 / 5 : ℝ) * (1 - t) ^ 5 +
            5 * (87229513 / 5 : ℝ) * t * (1 - t) ^ 4 +
            10 * (30707893 / 5 : ℝ) * t ^ 2 * (1 - t) ^ 3 +
            10 * (6200529 / 5 : ℝ) * t ^ 3 * (1 - t) ^ 2 +
            5 * (434285 / 5 : ℝ) * t ^ 4 * (1 - t) +
            (433625 / 5 : ℝ) * t ^ 5 := by
      dsimp [t]
      ring
    rw [hbern]
    exact hb_cycle_bernstein_degree5_lower_bound ht0 ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · have hnonneg : 0 ≤ c := le_of_not_ge hneg
    by_cases hhalf : c ≤ 1 / 2
    · let t : ℝ := 2 * c
      have ht0 : 0 ≤ t := by
        dsimp [t]
        linarith
      have ht1 : t ≤ 1 := by
        dsimp [t]
        linarith
      have hbern :
          19200000 * c ^ 5 + 297600 * c ^ 4 - 25951072 * c ^ 3 +
              11531168 * c ^ 2 - 660 * c + 86725 =
            (433625 / 5 : ℝ) * (1 - t) ^ 5 +
              5 * (433295 / 5 : ℝ) * t * (1 - t) ^ 4 +
              10 * (1874361 / 5 : ℝ) * t ^ 2 * (1 - t) ^ 3 +
              10 * (3134881 / 5 : ℝ) * t ^ 3 * (1 - t) ^ 2 +
              5 * (2611513 / 5 : ℝ) * t ^ 4 * (1 - t) +
              (1719515 / 5 : ℝ) * t ^ 5 := by
        dsimp [t]
        ring
      rw [hbern]
      exact hb_cycle_bernstein_degree5_lower_bound ht0 ht1
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · have hhalf' : 1 / 2 ≤ c := le_of_not_ge hhalf
      by_cases hthree : c ≤ 3 / 4
      · let t : ℝ := 4 * c - 2
        have ht0 : 0 ≤ t := by
          dsimp [t]
          linarith
        have ht1 : t ≤ 1 := by
          dsimp [t]
          linarith
        have hbern :
            19200000 * c ^ 5 + 297600 * c ^ 4 - 25951072 * c ^ 3 +
                11531168 * c ^ 2 - 660 * c + 86725 =
              (6878060 / 20 : ℝ) * (1 - t) ^ 5 +
                5 * (5094064 / 20 : ℝ) * t * (1 - t) ^ 4 +
                10 * (2941438 / 20 : ℝ) * t ^ 2 * (1 - t) ^ 3 +
                10 * (1127811 / 20 : ℝ) * t ^ 3 * (1 - t) ^ 2 +
                5 * (1115462 / 20 : ℝ) * t ^ 4 * (1 - t) +
                (5496320 / 20 : ℝ) * t ^ 5 := by
          dsimp [t]
          ring
        rw [hbern]
        exact hb_cycle_bernstein_degree5_lower_bound ht0 ht1
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · have hthree' : 3 / 4 ≤ c := le_of_not_ge hthree
        let t : ℝ := 4 * c - 3
        have ht0 : 0 ≤ t := by
          dsimp [t]
          linarith
        have ht1 : t ≤ 1 := by
          dsimp [t]
          linarith [hcl.2]
        have hbern :
            19200000 * c ^ 5 + 297600 * c ^ 4 - 25951072 * c ^ 3 +
                11531168 * c ^ 2 - 660 * c + 86725 =
              (5496320 / 20 : ℝ) * (1 - t) ^ 5 +
                5 * (9877178 / 20 : ℝ) * t * (1 - t) ^ 4 +
                10 * (18651243 / 20 : ℝ) * t ^ 2 * (1 - t) ^ 3 +
                10 * (34410444 / 20 : ℝ) * t ^ 3 * (1 - t) ^ 2 +
                5 * (60876360 / 20 : ℝ) * t ^ 4 * (1 - t) +
                (103275220 / 20 : ℝ) * t ^ 5 := by
          dsimp [t]
          ring
        rw [hbern]
        exact hb_cycle_bernstein_degree5_lower_bound ht0 ht1
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem hb_cycle_central_w_positive {c : ℝ} (hc : |c| ≤ 1) :
    (557731 / 62500000 : ℝ) ≤ hbCycleWstar c := by
  have hP := hb_cycle_central_polynomial_lower_on_unit_interval hc
  have hW :
      hbCycleWstar c =
        (19200000 * c ^ 5 + 297600 * c ^ 4 - 25951072 * c ^ 3 +
          11531168 * c ^ 2 - 660 * c + 86725) / 6250000 := by
    unfold hbCycleWstar
    ring
  rw [hW]
  nlinarith [hP]

private theorem hb_cycle_dft_transfer_real_imag
    {Z X : ℂ} {A B : ℝ}
    (hZ : Z = ((A : ℂ) - Complex.I * (B : ℂ)) * X) :
    Z.re = A * X.re + B * X.im ∧
      Z.im = A * X.im - B * X.re := by
  constructor
  · rw [hZ]
    simp [Complex.mul_re, Complex.mul_im]
  · rw [hZ]
    simp [Complex.mul_re, Complex.mul_im]
    ring

private theorem hb_cycle_weighted_mode_scalar
    (c s p t u v : ℝ)
    (hsq : s ^ 2 = 1 - c ^ 2)
    (hp :
      p = 8 * c ^ 4 - 8 * c ^ 2 + 1)
    (ht :
      t = (8 * c ^ 3 - 4 * c) * s) :
    let A : ℝ := ((1 + bStar) / aStar) * (1 - c)
    let B : ℝ := ((1 - bStar) / aStar) * s
    let zr : ℝ := A * u + B * v
    let zi : ℝ := A * v - B * u
    let lag : ℝ → ℝ → ℝ :=
      fun lr li =>
        let dxr := lr * u - li * v - u
        let dxi := lr * v + li * u - v
        let dzr := lr * zr - li * zi - zr
        let dzi := lr * zi + li * zr - zi
        (zr * lr + zi * li) * u + (zi * lr - zr * li) * v -
            (zr * u + zi * v) +
          (dzr ^ 2 + dzi ^ 2 + qStar * (dxr ^ 2 + dxi ^ 2) -
              2 * qStar * (dzr * dxr + dzi * dxi)) /
            (2 * (1 - qStar))
    lag c (-s) + (4 / 25 : ℝ) * lag p t =
      (u ^ 2 + v ^ 2) *
        ((1 - c) * hbCycleWstar c /
          (aStar ^ 2 * (1 - qStar))) := by
  dsimp
  rw [hp, ht]
  have hs4 : s ^ 4 = (1 - c ^ 2) ^ 2 := by
    calc
      s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ = (1 - c ^ 2) ^ 2 := by rw [hsq]
  simp only [qStar, aStar, bStar, hbCycleWstar]
  field_simp
  set_option maxRecDepth 100000 in
    ring_nf
  rw [hs4, hsq]
  ring

set_option maxHeartbeats 2000000 in
private theorem hb_cycle_scalar_weighted_mode_identity
    {K : ℕ} [NeZero K] (x z : Fin K → ℝ)
    (htransfer :
      ∀ j : Fin K,
        hbCycleDftCoord (fun i => (z i : ℂ)) j =
          (((((1 + bStar) / aStar) *
                (1 - (ZMod.stdAddChar (ZMod.finEquiv K j)).re) : ℝ) : ℂ) -
            Complex.I *
              ((((1 - bStar) / aStar) *
                (ZMod.stdAddChar (ZMod.finEquiv K j)).im : ℝ) : ℂ)) *
            hbCycleDftCoord (fun i => (x i : ℂ)) j) :
    (∑ i : Fin K,
        (z i * (x (cycleFinShift (K - 1) i) - x i) +
          ((z (cycleFinShift (K - 1) i) - z i) ^ 2 +
              qStar * (x (cycleFinShift (K - 1) i) - x i) ^ 2 -
              2 * qStar *
                (z (cycleFinShift (K - 1) i) - z i) *
                (x (cycleFinShift (K - 1) i) - x i)) /
            (2 * (1 - qStar))) +
      (4 / 25 : ℝ) *
        ∑ i : Fin K,
          (z i * (x (cycleFinShift 4 i) - x i) +
            ((z (cycleFinShift 4 i) - z i) ^ 2 +
                qStar * (x (cycleFinShift 4 i) - x i) ^ 2 -
                2 * qStar *
                  (z (cycleFinShift 4 i) - z i) *
                  (x (cycleFinShift 4 i) - x i)) /
              (2 * (1 - qStar))) =
      ∑ j : Fin K,
        Complex.normSq (hbCycleDftCoord (fun i => (x i : ℂ)) j) *
          ((1 - (ZMod.stdAddChar (ZMod.finEquiv K j)).re) *
              hbCycleWstar (ZMod.stdAddChar (ZMod.finEquiv K j)).re /
            ((K : ℝ) * aStar ^ 2 * (1 - qStar)))) := by
  have hreal_sum (f : Fin K → ℂ) :
      Complex.re ((K : ℂ)⁻¹ * ∑ j : Fin K, f j) =
        ∑ j : Fin K, Complex.re ((K : ℂ)⁻¹ * f j) := by
    classical
    rw [Finset.mul_sum]
    induction (Finset.univ : Finset (Fin K)) using Finset.induction_on with
    | empty =>
        simp
    | @insert j s hjs ih =>
        simp only [Finset.sum_insert hjs, Complex.add_re, ih]
  have hsplit (n : ℕ) :
      (∑ i : Fin K,
          (z i * (x (cycleFinShift n i) - x i) +
            ((z (cycleFinShift n i) - z i) ^ 2 +
                qStar * (x (cycleFinShift n i) - x i) ^ 2 -
                2 * qStar *
                  (z (cycleFinShift n i) - z i) *
                  (x (cycleFinShift n i) - x i)) /
              (2 * (1 - qStar)))) =
        ∑ i : Fin K, z i * (x (cycleFinShift n i) - x i) +
          (∑ i : Fin K, (z (cycleFinShift n i) - z i) ^ 2 +
              qStar * ∑ i : Fin K, (x (cycleFinShift n i) - x i) ^ 2 -
              2 * qStar *
                ∑ i : Fin K,
                  (z (cycleFinShift n i) - z i) *
                    (x (cycleFinShift n i) - x i)) /
            (2 * (1 - qStar)) := by
    rw [Finset.sum_add_distrib, ← Finset.sum_div]
    congr 1
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have hq :
        ∑ i : Fin K, qStar * (x (cycleFinShift n i) - x i) ^ 2 =
          qStar * ∑ i : Fin K, (x (cycleFinShift n i) - x i) ^ 2 := by
      rw [← Finset.mul_sum]
    have hcross :
        ∑ i : Fin K,
            2 * qStar * (z (cycleFinShift n i) - z i) *
                (x (cycleFinShift n i) - x i) =
          2 * qStar *
            ∑ i : Fin K,
              (z (cycleFinShift n i) - z i) *
                (x (cycleFinShift n i) - x i) := by
      calc
        ∑ i : Fin K,
              2 * qStar * (z (cycleFinShift n i) - z i) *
                (x (cycleFinShift n i) - x i) =
            ∑ i : Fin K,
              (2 * qStar) *
                ((z (cycleFinShift n i) - z i) *
                  (x (cycleFinShift n i) - x i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = 2 * qStar *
            ∑ i : Fin K,
              (z (cycleFinShift n i) - z i) *
                (x (cycleFinShift n i) - x i) := by
          rw [Finset.mul_sum]
    rw [hq, hcross]
  have hsum_rearrange
      (A B C D E F G H : Fin K → ℝ) :
      (∑ j : Fin K, A j) +
          ((∑ j : Fin K, B j) + qStar * (∑ j : Fin K, C j) -
              2 * qStar * (∑ j : Fin K, D j)) /
            (2 * (1 - qStar)) +
        (4 / 25 : ℝ) *
          ((∑ j : Fin K, E j) +
            (((∑ j : Fin K, F j) + qStar * (∑ j : Fin K, G j) -
                2 * qStar * (∑ j : Fin K, H j)) /
              (2 * (1 - qStar)))) =
        ∑ j : Fin K,
          ((A j +
              (B j + qStar * C j - 2 * qStar * D j) /
                (2 * (1 - qStar))) +
            (4 / 25 : ℝ) *
              (E j + (F j + qStar * G j - 2 * qStar * H j) /
                (2 * (1 - qStar)))) := by
    have hquot (B C D : Fin K → ℝ) :
        ((∑ j : Fin K, B j) + qStar * (∑ j : Fin K, C j) -
              2 * qStar * (∑ j : Fin K, D j)) /
            (2 * (1 - qStar)) =
          ∑ j : Fin K,
            (B j + qStar * C j - 2 * qStar * D j) /
              (2 * (1 - qStar)) := by
      have hnum :
          ((∑ j : Fin K, B j) + qStar * (∑ j : Fin K, C j) -
              2 * qStar * (∑ j : Fin K, D j)) =
            ∑ j : Fin K, (B j + qStar * C j - 2 * qStar * D j) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      rw [hnum, Finset.sum_div]
    rw [hquot B C D, hquot F G H]
    rw [← Finset.sum_add_distrib]
    rw [← Finset.sum_add_distrib]
    rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
  have hreal_combined
      (A B C D E F G H : Fin K → ℂ) :
      Complex.re ((K : ℂ)⁻¹ * ∑ j : Fin K, A j) +
          (Complex.re ((K : ℂ)⁻¹ * ∑ j : Fin K, B j) +
              qStar * Complex.re ((K : ℂ)⁻¹ * ∑ j : Fin K, C j) -
              2 * qStar * Complex.re ((K : ℂ)⁻¹ * ∑ j : Fin K, D j)) /
            (2 * (1 - qStar)) +
        (4 / 25 : ℝ) *
          (Complex.re ((K : ℂ)⁻¹ * ∑ j : Fin K, E j) +
            (Complex.re ((K : ℂ)⁻¹ * ∑ j : Fin K, F j) +
                qStar * Complex.re ((K : ℂ)⁻¹ * ∑ j : Fin K, G j) -
                2 * qStar * Complex.re ((K : ℂ)⁻¹ * ∑ j : Fin K, H j)) /
              (2 * (1 - qStar))) =
      ∑ j : Fin K,
        ((Complex.re ((K : ℂ)⁻¹ * A j) +
            (Complex.re ((K : ℂ)⁻¹ * B j) +
                qStar * Complex.re ((K : ℂ)⁻¹ * C j) -
                2 * qStar * Complex.re ((K : ℂ)⁻¹ * D j)) /
              (2 * (1 - qStar))) +
          (4 / 25 : ℝ) *
            (Complex.re ((K : ℂ)⁻¹ * E j) +
              (Complex.re ((K : ℂ)⁻¹ * F j) +
                  qStar * Complex.re ((K : ℂ)⁻¹ * G j) -
                  2 * qStar * Complex.re ((K : ℂ)⁻¹ * H j)) /
                (2 * (1 - qStar)))) := by
    rw [hreal_sum A, hreal_sum B, hreal_sum C, hreal_sum D,
      hreal_sum E, hreal_sum F, hreal_sum G, hreal_sum H]
    convert hsum_rearrange
      (fun j => Complex.re ((K : ℂ)⁻¹ * A j))
      (fun j => Complex.re ((K : ℂ)⁻¹ * B j))
      (fun j => Complex.re ((K : ℂ)⁻¹ * C j))
      (fun j => Complex.re ((K : ℂ)⁻¹ * D j))
      (fun j => Complex.re ((K : ℂ)⁻¹ * E j))
      (fun j => Complex.re ((K : ℂ)⁻¹ * F j))
      (fun j => Complex.re ((K : ℂ)⁻¹ * G j))
      (fun j => Complex.re ((K : ℂ)⁻¹ * H j)) using 1
  have hinnerPrev :=
    hb_cycle_real_inner_lag_parseval z x (K - 1)
  have hinnerFour :=
    hb_cycle_real_inner_lag_parseval z x 4
  have hnormZPrev :=
    hb_cycle_real_norm_lag_parseval z (K - 1)
  have hnormZFour :=
    hb_cycle_real_norm_lag_parseval z 4
  have hnormXPrev :=
    hb_cycle_real_norm_lag_parseval x (K - 1)
  have hnormXFour :=
    hb_cycle_real_norm_lag_parseval x 4
  have hcrossPrev :=
    hb_cycle_real_cross_diff_parseval z x (K - 1)
  have hcrossFour :=
    hb_cycle_real_cross_diff_parseval z x 4
  rw [hsplit (K - 1), hsplit 4]
  rw [hinnerPrev, hinnerFour, hnormZPrev, hnormZFour,
    hnormXPrev, hnormXFour, hcrossPrev, hcrossFour]
  have halphaFour (j : Fin K) :
      ZMod.stdAddChar (ZMod.finEquiv K j * ((4 : ℕ) : ZMod K)) =
        (ZMod.stdAddChar (ZMod.finEquiv K j)) ^ 4 := by
    have harg :
        ZMod.finEquiv K j * ((4 : ℕ) : ZMod K) =
          ZMod.finEquiv K j + ZMod.finEquiv K j +
            ZMod.finEquiv K j + ZMod.finEquiv K j := by ring
    rw [harg, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
      AddChar.map_add_eq_mul]
    ring
  have hcombined := hreal_combined
    (fun j : Fin K =>
      hbCycleDftCoord (fun i => (z i : ℂ)) j *
          starRingEnd ℂ (ZMod.stdAddChar
            (ZMod.finEquiv K j * ((K - 1 : ℕ) : ZMod K))) *
          starRingEnd ℂ (hbCycleDftCoord (fun i => (x i : ℂ)) j) -
        hbCycleDftCoord (fun i => (z i : ℂ)) j *
          starRingEnd ℂ (hbCycleDftCoord (fun i => (x i : ℂ)) j))
    (fun j : Fin K =>
      (ZMod.stdAddChar
          (ZMod.finEquiv K j * ((K - 1 : ℕ) : ZMod K)) *
          hbCycleDftCoord (fun i => (z i : ℂ)) j -
        hbCycleDftCoord (fun i => (z i : ℂ)) j) *
        starRingEnd ℂ
          (ZMod.stdAddChar
            (ZMod.finEquiv K j * ((K - 1 : ℕ) : ZMod K)) *
            hbCycleDftCoord (fun i => (z i : ℂ)) j -
          hbCycleDftCoord (fun i => (z i : ℂ)) j))
    (fun j : Fin K =>
      (ZMod.stdAddChar
          (ZMod.finEquiv K j * ((K - 1 : ℕ) : ZMod K)) *
          hbCycleDftCoord (fun i => (x i : ℂ)) j -
        hbCycleDftCoord (fun i => (x i : ℂ)) j) *
        starRingEnd ℂ
          (ZMod.stdAddChar
            (ZMod.finEquiv K j * ((K - 1 : ℕ) : ZMod K)) *
            hbCycleDftCoord (fun i => (x i : ℂ)) j -
          hbCycleDftCoord (fun i => (x i : ℂ)) j))
    (fun j : Fin K =>
      (ZMod.stdAddChar
          (ZMod.finEquiv K j * ((K - 1 : ℕ) : ZMod K)) *
          hbCycleDftCoord (fun i => (z i : ℂ)) j -
        hbCycleDftCoord (fun i => (z i : ℂ)) j) *
        starRingEnd ℂ
          (ZMod.stdAddChar
            (ZMod.finEquiv K j * ((K - 1 : ℕ) : ZMod K)) *
            hbCycleDftCoord (fun i => (x i : ℂ)) j -
          hbCycleDftCoord (fun i => (x i : ℂ)) j))
    (fun j : Fin K =>
      hbCycleDftCoord (fun i => (z i : ℂ)) j *
          starRingEnd ℂ (ZMod.stdAddChar
            (ZMod.finEquiv K j * ((4 : ℕ) : ZMod K))) *
          starRingEnd ℂ (hbCycleDftCoord (fun i => (x i : ℂ)) j) -
        hbCycleDftCoord (fun i => (z i : ℂ)) j *
          starRingEnd ℂ (hbCycleDftCoord (fun i => (x i : ℂ)) j))
    (fun j : Fin K =>
      (ZMod.stdAddChar
          (ZMod.finEquiv K j * ((4 : ℕ) : ZMod K)) *
          hbCycleDftCoord (fun i => (z i : ℂ)) j -
        hbCycleDftCoord (fun i => (z i : ℂ)) j) *
        starRingEnd ℂ
          (ZMod.stdAddChar
            (ZMod.finEquiv K j * ((4 : ℕ) : ZMod K)) *
            hbCycleDftCoord (fun i => (z i : ℂ)) j -
          hbCycleDftCoord (fun i => (z i : ℂ)) j))
    (fun j : Fin K =>
      (ZMod.stdAddChar
          (ZMod.finEquiv K j * ((4 : ℕ) : ZMod K)) *
          hbCycleDftCoord (fun i => (x i : ℂ)) j -
        hbCycleDftCoord (fun i => (x i : ℂ)) j) *
        starRingEnd ℂ
          (ZMod.stdAddChar
            (ZMod.finEquiv K j * ((4 : ℕ) : ZMod K)) *
            hbCycleDftCoord (fun i => (x i : ℂ)) j -
          hbCycleDftCoord (fun i => (x i : ℂ)) j))
    (fun j : Fin K =>
      (ZMod.stdAddChar
          (ZMod.finEquiv K j * ((4 : ℕ) : ZMod K)) *
          hbCycleDftCoord (fun i => (z i : ℂ)) j -
        hbCycleDftCoord (fun i => (z i : ℂ)) j) *
        starRingEnd ℂ
          (ZMod.stdAddChar
            (ZMod.finEquiv K j * ((4 : ℕ) : ZMod K)) *
            hbCycleDftCoord (fun i => (x i : ℂ)) j -
          hbCycleDftCoord (fun i => (x i : ℂ)) j))
  rw [hcombined]
  apply Finset.sum_congr rfl
  intro j hj
  have hz := htransfer j
  have hbridge := hb_cycle_dft_transfer_real_imag hz
  have hZre := hbridge.1
  have hZim := hbridge.2
  rw [hb_cycle_dft_prev_character, halphaFour j]
  simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im]
  rw [hZre, hZim]
  have hnorm :
      (ZMod.stdAddChar (ZMod.finEquiv K j)).re ^ 2 +
          (ZMod.stdAddChar (ZMod.finEquiv K j)).im ^ 2 = 1 := by
    have h := hb_cycle_stdAddChar_normSq
      (K := K) (ZMod.finEquiv K j)
    simpa [Complex.normSq_apply, pow_two] using h
  have hsq :
      (ZMod.stdAddChar (ZMod.finEquiv K j)).im ^ 2 =
        1 - (ZMod.stdAddChar (ZMod.finEquiv K j)).re ^ 2 := by
    nlinarith [hnorm]
  have hpow4_re :
      ((ZMod.stdAddChar (ZMod.finEquiv K j)) ^ 4).re =
        8 * (ZMod.stdAddChar (ZMod.finEquiv K j)).re ^ 4 -
          8 * (ZMod.stdAddChar (ZMod.finEquiv K j)).re ^ 2 + 1 := by
    simp [pow_succ, Complex.mul_re, Complex.mul_im]
    have hmul := congrArg
      (fun t : ℝ =>
        t * (ZMod.stdAddChar (ZMod.finEquiv K j)).re ^ 2) hsq
    have hmul2 := congrArg (fun t : ℝ => t ^ 2) hsq
    ring_nf at hmul hmul2 ⊢
    linarith [hmul, hmul2]
  have hpow4_im :
      ((ZMod.stdAddChar (ZMod.finEquiv K j)) ^ 4).im =
        (8 * (ZMod.stdAddChar (ZMod.finEquiv K j)).re ^ 3 -
          4 * (ZMod.stdAddChar (ZMod.finEquiv K j)).re) *
          (ZMod.stdAddChar (ZMod.finEquiv K j)).im := by
    simp [pow_succ, Complex.mul_re, Complex.mul_im]
    have hmul := congrArg
      (fun t : ℝ =>
        t * (ZMod.stdAddChar (ZMod.finEquiv K j)).re *
          (ZMod.stdAddChar (ZMod.finEquiv K j)).im) hsq
    ring_nf at hmul ⊢
    linarith [hmul]
  have hstar_re :
      (starRingEnd ℂ (ZMod.stdAddChar (ZMod.finEquiv K j))).re =
        (ZMod.stdAddChar (ZMod.finEquiv K j)).re := by
    simp [Complex.conj_re]
  have hstar_im :
      (starRingEnd ℂ (ZMod.stdAddChar (ZMod.finEquiv K j))).im =
        -(ZMod.stdAddChar (ZMod.finEquiv K j)).im := by
    simp [Complex.conj_im]
  have hpow4_star_re :
      (starRingEnd ℂ (ZMod.stdAddChar (ZMod.finEquiv K j)) ^ 4).re =
        8 * (ZMod.stdAddChar (ZMod.finEquiv K j)).re ^ 4 -
          8 * (ZMod.stdAddChar (ZMod.finEquiv K j)).re ^ 2 + 1 := by
    simp [pow_succ, Complex.mul_re, Complex.mul_im, hstar_re, hstar_im]
    have hmul := congrArg
      (fun t : ℝ =>
        t * (ZMod.stdAddChar (ZMod.finEquiv K j)).re ^ 2) hsq
    have hmul2 := congrArg (fun t : ℝ => t ^ 2) hsq
    ring_nf at hmul hmul2 ⊢
    linarith [hmul, hmul2]
  have hpow4_star_im :
      (starRingEnd ℂ (ZMod.stdAddChar (ZMod.finEquiv K j)) ^ 4).im =
        -((8 * (ZMod.stdAddChar (ZMod.finEquiv K j)).re ^ 3 -
            4 * (ZMod.stdAddChar (ZMod.finEquiv K j)).re) *
          (ZMod.stdAddChar (ZMod.finEquiv K j)).im) := by
    simp [pow_succ, Complex.mul_re, Complex.mul_im, hstar_re, hstar_im]
    have hmul := congrArg
      (fun t : ℝ =>
        t * (ZMod.stdAddChar (ZMod.finEquiv K j)).re *
          (ZMod.stdAddChar (ZMod.finEquiv K j)).im) hsq
    ring_nf at hmul ⊢
    linarith [hmul]
  simp [Complex.conj_re, Complex.conj_im, hpow4_re, hpow4_im,
    hstar_re, hstar_im, hpow4_star_re, hpow4_star_im]
  have hscalar :=
    hb_cycle_weighted_mode_scalar
      (ZMod.stdAddChar (ZMod.finEquiv K j)).re
      (ZMod.stdAddChar (ZMod.finEquiv K j)).im
      (8 * (ZMod.stdAddChar (ZMod.finEquiv K j)).re ^ 4 -
        8 * (ZMod.stdAddChar (ZMod.finEquiv K j)).re ^ 2 + 1)
      ((8 * (ZMod.stdAddChar (ZMod.finEquiv K j)).re ^ 3 -
          4 * (ZMod.stdAddChar (ZMod.finEquiv K j)).re) *
        (ZMod.stdAddChar (ZMod.finEquiv K j)).im)
      (hbCycleDftCoord (fun i => (x i : ℂ)) j).re
      (hbCycleDftCoord (fun i => (x i : ℂ)) j).im
      hsq (by rfl) (by rfl)
  have hscaled := congrArg
    (fun r : ℝ => (K : ℝ)⁻¹ * r) hscalar
  calc
    _ = (K : ℝ)⁻¹ *
        (((hbCycleDftCoord (fun i => (x i : ℂ)) j).re ^ 2 +
            (hbCycleDftCoord (fun i => (x i : ℂ)) j).im ^ 2) *
          ((1 - (ZMod.stdAddChar (ZMod.finEquiv K j)).re) *
            hbCycleWstar (ZMod.stdAddChar (ZMod.finEquiv K j)).re /
            (aStar ^ 2 * (1 - qStar)))) := by
      set_option maxRecDepth 100000 in
        convert hscaled using 1 <;> ring
    _ = _ := by
      have hK : (K : ℝ) ≠ 0 := by
        exact_mod_cast (NeZero.ne K)
      field_simp [hK]

theorem HB_ALL_FREQUENCY_CYCLE_EXCLUSION :
    ¬ HB_Cycle qStar aStar bStar := by
  rintro ⟨hD, d, hd, hf, K, hK, xMinusOne, xZero, hperiod, t, hneq⟩
  letI : NeZero K := ⟨by omega⟩
  let y : Fin K → Vec d :=
    fun i => hbIterate aStar bStar hf xMinusOne xZero i.val
  let g : Fin K → Vec d :=
    fun i => gradient hf.f (y i)
  let F : Fin K → ℝ :=
    fun i => hf.f (y i)
  have hq0 : 0 < qStar := by
    norm_num [qStar]
  have hq1 : qStar < 1 := by
    norm_num [qStar]
  have hlag (n : ℕ) :
      ∑ i : Fin K,
          (inner ℝ (g i) (y (cycleFinShift n i) - y i) +
            (‖g (cycleFinShift n i) - g i‖ ^ 2 +
                qStar * ‖y (cycleFinShift n i) - y i‖ ^ 2 -
                2 * qStar *
                  inner ℝ (g (cycleFinShift n i) - g i)
                    (y (cycleFinShift n i) - y i)) /
              (2 * (1 - qStar))) ≤ 0 := by
    apply box_cycle_lag_sum_nonpositive (d := d) (K := K)
      hq0 hq1 (by omega) y g F (cycleFinShift n) (cycleFinShift_bijective n)
    intro i
    exact hb_interpolation_shifted_cocoercive hq0 hq1 hf
      (y (cycleFinShift n i)) (y i)
  have hlagMinusOne := hlag (K - 1)
  have hlagFour := hlag 4
  have hpred :
      xMinusOne = hbIterate aStar bStar hf xMinusOne xZero (K - 1) := by
    have hrec0 :=
      hbIterate_succ_eq_successor aStar bStar hf xMinusOne xZero 0
    have hrecK :=
      hbIterate_succ_eq_successor aStar bStar hf xMinusOne xZero K
    have hp0 := hperiod 0
    have hp1 := hperiod 1
    have hrec0' :
        hbIterate aStar bStar hf xMinusOne xZero 1 =
          hbSuccessor aStar bStar hf xMinusOne xZero := by
      simpa [hbIterate_zero] using hrec0
    have hrecK' :
        hbIterate aStar bStar hf xMinusOne xZero (K + 1) =
          hbSuccessor aStar bStar hf
            (hbIterate aStar bStar hf xMinusOne xZero (K - 1))
            (hbIterate aStar bStar hf xMinusOne xZero K) := by
      simpa [show K ≠ 0 by omega] using hrecK
    have hp0' :
        hbIterate aStar bStar hf xMinusOne xZero K = xZero := by
      simpa [hbIterate_zero] using hp0
    have hp1' :
        hbIterate aStar bStar hf xMinusOne xZero (K + 1) =
          hbIterate aStar bStar hf xMinusOne xZero 1 := by
      simpa [Nat.add_comm] using hp1
    apply hbSuccessor_left_injective aStar bStar hf (by norm_num [bStar])
    calc
      hbSuccessor aStar bStar hf xMinusOne xZero =
          hbIterate aStar bStar hf xMinusOne xZero 1 := hrec0'.symm
      _ = hbIterate aStar bStar hf xMinusOne xZero (K + 1) := hp1'.symm
      _ = hbSuccessor aStar bStar hf
          (hbIterate aStar bStar hf xMinusOne xZero (K - 1))
          (hbIterate aStar bStar hf xMinusOne xZero K) := hrecK'
      _ = hbSuccessor aStar bStar hf
          (hbIterate aStar bStar hf xMinusOne xZero (K - 1)) xZero := by
        rw [hp0']
  have hcyclicRecurrence :
      ∀ i : Fin K,
        y (cycleFinShift 1 i) =
          hbSuccessor aStar bStar hf
            (y (cycleFinShift (K - 1) i)) (y i) := by
    intro i
    dsimp [y]
    exact hb_cycle_recurrence aStar bStar hf xMinusOne xZero hK
      hperiod hpred i
  have hcyclicRecurrence_expanded :
      ∀ i : Fin K,
        y (cycleFinShift 1 i) =
          (1 + bStar) • y i -
            bStar • y (cycleFinShift (K - 1) i) -
            aStar • g i := by
    intro i
    have h := hcyclicRecurrence i
    simpa [hbSuccessor, g] using h
  have htransfer (j : Fin K) (r : Fin d) :
      hbCycleDftCoord (fun i => ((g i).ofLp r : ℂ)) j =
        (((1 + (bStar : ℂ)) - ZMod.stdAddChar (ZMod.finEquiv K j) -
            (bStar : ℂ) * ZMod.stdAddChar
              (ZMod.finEquiv K j * ((K - 1 : ℕ) : ZMod K))) /
          (aStar : ℂ)) *
          hbCycleDftCoord (fun i => ((y i).ofLp r : ℂ)) j := by
    apply hb_cycle_dft_scalar_recurrence_transfer
      (a := (aStar : ℂ)) (b := (bStar : ℂ))
      (Y := fun i => ((y i).ofLp r : ℂ))
      (G := fun i => ((g i).ofLp r : ℂ))
    · intro i
      have h :=
        congrArg (fun v : Vec d => (v.ofLp r : ℂ))
          (hcyclicRecurrence_expanded i)
      simpa [PiLp.smul_apply] using h
    · norm_num [aStar]
  have htransfer_uv (j : Fin K) (r : Fin d) :
      hbCycleDftCoord (fun i => ((g i).ofLp r : ℂ)) j =
        (((((1 + bStar) / aStar) *
              (1 - (ZMod.stdAddChar (ZMod.finEquiv K j)).re) : ℝ) : ℂ) -
          Complex.I *
            ((((1 - bStar) / aStar) *
              (ZMod.stdAddChar (ZMod.finEquiv K j)).im : ℝ) : ℂ)) *
          hbCycleDftCoord (fun i => ((y i).ofLp r : ℂ)) j := by
    have h := htransfer j r
    rw [hb_cycle_dft_prev_character] at h
    have hcoeff :
        (((1 + (bStar : ℂ)) - ZMod.stdAddChar (ZMod.finEquiv K j) -
            (bStar : ℂ) *
              starRingEnd ℂ (ZMod.stdAddChar (ZMod.finEquiv K j))) /
          (aStar : ℂ)) =
          (((((1 + bStar) / aStar) *
                (1 - (ZMod.stdAddChar (ZMod.finEquiv K j)).re) : ℝ) : ℂ) -
            Complex.I *
              ((((1 - bStar) / aStar) *
                (ZMod.stdAddChar (ZMod.finEquiv K j)).im : ℝ) : ℂ)) := by
      apply Complex.ext <;>
        simp [Complex.div_re, Complex.div_im, Complex.mul_re,
          Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.add_re,
          Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]
      · field_simp [aStar]
        ring
      · field_simp [aStar]
        ring
    rw [hcoeff] at h
    exact h
  have hinner_coord (u v : Vec d) :
      inner ℝ u v = ∑ r : Fin d, (u.ofLp r) * (v.ofLp r) := by
    rw [PiLp.inner_apply]
    simp [PiLp.toLp_apply, real_inner_eq_re_inner, mul_comm]
  have hnorm_coord (u : Vec d) :
      ‖u‖ ^ 2 = ∑ r : Fin d, (u.ofLp r) ^ 2 := by
    simpa [PiLp.toLp_apply] using EuclideanSpace.real_norm_sq_eq u
  have hlag_coord (n : ℕ) :
      (∑ i : Fin K,
          (inner ℝ (g i) (y (cycleFinShift n i) - y i) +
            (‖g (cycleFinShift n i) - g i‖ ^ 2 +
                qStar * ‖y (cycleFinShift n i) - y i‖ ^ 2 -
                2 * qStar *
                  inner ℝ (g (cycleFinShift n i) - g i)
                    (y (cycleFinShift n i) - y i)) /
              (2 * (1 - qStar)))) =
        ∑ r : Fin d, ∑ i : Fin K,
          ((g i).ofLp r *
              ((y (cycleFinShift n i)).ofLp r - (y i).ofLp r) +
            (((g (cycleFinShift n i)).ofLp r - (g i).ofLp r) ^ 2 +
                qStar *
                  ((y (cycleFinShift n i)).ofLp r - (y i).ofLp r) ^ 2 -
                2 * qStar *
                  ((g (cycleFinShift n i)).ofLp r - (g i).ofLp r) *
                    ((y (cycleFinShift n i)).ofLp r - (y i).ofLp r)) /
              (2 * (1 - qStar))) := by
    calc
      _ = ∑ i : Fin K, ∑ r : Fin d,
          ((g i).ofLp r *
              ((y (cycleFinShift n i)).ofLp r - (y i).ofLp r) +
            (((g (cycleFinShift n i)).ofLp r - (g i).ofLp r) ^ 2 +
                qStar *
                  ((y (cycleFinShift n i)).ofLp r - (y i).ofLp r) ^ 2 -
                2 * qStar *
                  ((g (cycleFinShift n i)).ofLp r - (g i).ofLp r) *
                    ((y (cycleFinShift n i)).ofLp r - (y i).ofLp r)) /
              (2 * (1 - qStar))) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi1 := hinner_coord (g i)
          (y (cycleFinShift n i) - y i)
        have hn1 := hnorm_coord (g (cycleFinShift n i) - g i)
        have hn2 := hnorm_coord (y (cycleFinShift n i) - y i)
        have hi2 := hinner_coord
          (g (cycleFinShift n i) - g i)
          (y (cycleFinShift n i) - y i)
        rw [hi1, hn1, hn2, hi2]
        simp only [WithLp.ofLp_sub, PiLp.toLp_apply]
        have hfrac :
            (∑ r : Fin d,
                ((g (cycleFinShift n i)).ofLp - (g i).ofLp) r ^ 2 +
              qStar *
                ∑ r : Fin d,
                  ((y (cycleFinShift n i)).ofLp - (y i).ofLp) r ^ 2 -
              2 * qStar *
                ∑ r : Fin d,
                  ((g (cycleFinShift n i)).ofLp - (g i).ofLp) r *
                    ((y (cycleFinShift n i)).ofLp - (y i).ofLp) r) /
              (2 * (1 - qStar)) =
            ∑ r : Fin d,
              (((g (cycleFinShift n i)).ofLp - (g i).ofLp) r ^ 2 +
                  qStar *
                    ((y (cycleFinShift n i)).ofLp - (y i).ofLp) r ^ 2 -
                  2 * qStar *
                    ((g (cycleFinShift n i)).ofLp - (g i).ofLp) r *
                      ((y (cycleFinShift n i)).ofLp - (y i).ofLp) r) /
                (2 * (1 - qStar)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro r hr
          ring_nf
        rw [hfrac, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro r hr
        simp only [Pi.sub_apply]
      _ = ∑ r : Fin d, ∑ i : Fin K,
          ((g i).ofLp r *
              ((y (cycleFinShift n i)).ofLp r - (y i).ofLp r) +
            (((g (cycleFinShift n i)).ofLp r - (g i).ofLp r) ^ 2 +
                qStar *
                  ((y (cycleFinShift n i)).ofLp r - (y i).ofLp r) ^ 2 -
                2 * qStar *
                  ((g (cycleFinShift n i)).ofLp r - (g i).ofLp r) *
                    ((y (cycleFinShift n i)).ofLp r - (y i).ofLp r)) /
              (2 * (1 - qStar))) := by
        rw [Finset.sum_comm]
  let lagCoord (r : Fin d) (n : ℕ) : ℝ :=
    ∑ i : Fin K,
      ((g i).ofLp r *
          ((y (cycleFinShift n i)).ofLp r - (y i).ofLp r) +
        (((g (cycleFinShift n i)).ofLp r - (g i).ofLp r) ^ 2 +
              qStar * ((y (cycleFinShift n i)).ofLp r - (y i).ofLp r) ^ 2 -
            2 * qStar * ((g (cycleFinShift n i)).ofLp r - (g i).ofLp r) *
              ((y (cycleFinShift n i)).ofLp r - (y i).ofLp r)) /
          (2 * (1 - qStar)))
  have hcoord_scalar (r : Fin d) :
      lagCoord r (K - 1) + (4 / 25 : ℝ) * lagCoord r 4 =
        ∑ j : Fin K,
          Complex.normSq
              (hbCycleDftCoord (fun i => ((y i).ofLp r : ℂ)) j) *
            ((1 - (ZMod.stdAddChar (ZMod.finEquiv K j)).re) *
                hbCycleWstar (ZMod.stdAddChar (ZMod.finEquiv K j)).re /
              ((K : ℝ) * aStar ^ 2 * (1 - qStar))) := by
    dsimp [lagCoord]
    simpa using
      hb_cycle_scalar_weighted_mode_identity
        (x := fun i => (y i).ofLp r)
        (z := fun i => (g i).ofLp r)
        (htransfer := fun j => htransfer_uv j r)
  have hcoord_prev_le :
      ∑ r : Fin d, lagCoord r (K - 1) ≤ 0 := by
    have h := hlagMinusOne
    rw [hlag_coord (K - 1)] at h
    simpa [lagCoord] using h
  have hcoord_four_le :
      ∑ r : Fin d, lagCoord r 4 ≤ 0 := by
    have h := hlagFour
    rw [hlag_coord 4] at h
    simpa [lagCoord] using h
  have hcoord_combined_le :
      (∑ r : Fin d, lagCoord r (K - 1)) +
          (4 / 25 : ℝ) * ∑ r : Fin d, lagCoord r 4 ≤ 0 := by
    linarith
  have hmode_eq :
      (∑ r : Fin d, lagCoord r (K - 1)) +
          (4 / 25 : ℝ) * ∑ r : Fin d, lagCoord r 4 =
        ∑ j : Fin K,
          (∑ r : Fin d,
            Complex.normSq
              (hbCycleDftCoord (fun i => ((y i).ofLp r : ℂ)) j)) *
            ((1 - (ZMod.stdAddChar (ZMod.finEquiv K j)).re) *
                hbCycleWstar (ZMod.stdAddChar (ZMod.finEquiv K j)).re /
              ((K : ℝ) * aStar ^ 2 * (1 - qStar))) := by
    calc
      _ = ∑ r : Fin d, (lagCoord r (K - 1) +
          (4 / 25 : ℝ) * lagCoord r 4) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      _ = ∑ r : Fin d, ∑ j : Fin K,
          Complex.normSq
              (hbCycleDftCoord (fun i => ((y i).ofLp r : ℂ)) j) *
            ((1 - (ZMod.stdAddChar (ZMod.finEquiv K j)).re) *
                hbCycleWstar (ZMod.stdAddChar (ZMod.finEquiv K j)).re /
              ((K : ℝ) * aStar ^ 2 * (1 - qStar))) := by
        apply Finset.sum_congr rfl
        intro r hr
        exact hcoord_scalar r
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        rw [← Finset.sum_mul]
  let modeEnergy : Fin K → ℝ := fun j =>
    ∑ r : Fin d,
      Complex.normSq
        (hbCycleDftCoord (fun i => ((y i).ofLp r : ℂ)) j)
  let modeWeight : Fin K → ℝ := fun j =>
    ((1 - (ZMod.stdAddChar (ZMod.finEquiv K j)).re) *
        hbCycleWstar (ZMod.stdAddChar (ZMod.finEquiv K j)).re /
      ((K : ℝ) * aStar ^ 2 * (1 - qStar)))
  have hmode_le :
      ∑ j : Fin K, modeEnergy j * modeWeight j ≤ 0 := by
    change
      ∑ j : Fin K,
          (∑ r : Fin d,
            Complex.normSq
              (hbCycleDftCoord (fun i => ((y i).ofLp r : ℂ)) j)) *
            ((1 - (ZMod.stdAddChar (ZMod.finEquiv K j)).re) *
                hbCycleWstar (ZMod.stdAddChar (ZMod.finEquiv K j)).re /
              ((K : ℝ) * aStar ^ 2 * (1 - qStar))) ≤ 0
    rw [← hmode_eq]
    exact hcoord_combined_le
  have hmode_nonneg : ∀ j : Fin K, 0 ≤ modeEnergy j := by
    intro j
    dsimp [modeEnergy]
    exact Finset.sum_nonneg (fun r _ => Complex.normSq_nonneg _)
  have hweight_zero : modeWeight 0 = 0 := by
    dsimp [modeWeight]
    have hroot :
        ZMod.stdAddChar (ZMod.finEquiv K 0) = (1 : ℂ) :=
      (hb_cycle_root_eq_one_iff (K := K) 0).2 rfl
    rw [hroot]
    norm_num
  have hweight_pos : ∀ j : Fin K, j ≠ 0 → 0 < modeWeight j := by
    intro j hj
    let omega : ℂ := ZMod.stdAddChar (ZMod.finEquiv K j)
    have hnorm :
        omega.re ^ 2 + omega.im ^ 2 = 1 := by
      have h := hb_cycle_stdAddChar_normSq
        (K := K) (ZMod.finEquiv K j)
      simpa [omega, Complex.normSq_apply, pow_two] using h
    have hcos_le : omega.re ≤ 1 := by
      nlinarith [sq_nonneg omega.im]
    have hcos_ne : omega.re ≠ 1 := by
      intro hcos
      have him : omega.im = 0 := by
        nlinarith [sq_nonneg omega.im]
      have hroot : omega = (1 : ℂ) := by
        apply Complex.ext <;> simp [hcos, him]
      have : j = 0 := (hb_cycle_root_eq_one_iff (K := K) j).mp hroot
      exact hj this
    have hcos_lt : omega.re < 1 :=
      lt_of_le_of_ne hcos_le hcos_ne
    have habs : |omega.re| ≤ 1 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg omega.im]
    have hW : 0 < hbCycleWstar omega.re := by
      have h := hb_cycle_central_w_positive habs
      nlinarith
    have hden : 0 < (K : ℝ) * aStar ^ 2 * (1 - qStar) := by
      have hKpos : 0 < (K : ℝ) := by
        exact_mod_cast (show 0 < K by omega)
      have ha : 0 < aStar := by
        norm_num [aStar]
      have hq : 0 < 1 - qStar := by
        norm_num [qStar]
      exact mul_pos (mul_pos hKpos (sq_pos_of_pos ha)) hq
    dsimp [modeWeight, omega]
    exact div_pos (mul_pos (sub_pos.mpr hcos_lt) hW) hden
  have hmode_zero :
      ∀ j : Fin K, j ≠ 0 → modeEnergy j = 0 :=
    weighted_nonpositive_sum_forces_nonzero_terms_zero
      (zero := (0 : Fin K)) modeEnergy modeWeight
      hmode_nonneg hweight_zero hweight_pos hmode_le
  have hzero_dft :
      ∀ j : Fin K, j ≠ 0 →
        ∀ r : Fin d,
          hbCycleDftCoord (fun i => ((y i).ofLp r : ℂ)) j = 0 := by
    intro j hj r
    have hsumzero : modeEnergy j = 0 := hmode_zero j hj
    have hle :
        Complex.normSq
            (hbCycleDftCoord (fun i => ((y i).ofLp r : ℂ)) j) ≤
          modeEnergy j := by
      dsimp [modeEnergy]
      exact Finset.single_le_sum
        (s := Finset.univ)
        (f := fun r' : Fin d =>
          Complex.normSq
            (hbCycleDftCoord (fun i => ((y i).ofLp r' : ℂ)) j))
        (by
          intro r' _hr'
          exact Complex.normSq_nonneg _)
        (Finset.mem_univ r)
    have hz :
        Complex.normSq
            (hbCycleDftCoord (fun i => ((y i).ofLp r : ℂ)) j) = 0 := by
      have hn :=
        Complex.normSq_nonneg
          (hbCycleDftCoord (fun i => ((y i).ofLp r : ℂ)) j)
      linarith
    exact Complex.normSq_eq_zero.mp hz
  have hconstant : ∀ i j : Fin K, y i = y j :=
    hb_cycle_constant_of_nonzero_dft_zero y hzero_dft
  have hiterate_mod (n : ℕ) :
      hbIterate aStar bStar hf xMinusOne xZero n =
        hbIterate aStar bStar hf xMinusOne xZero (n % K) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
        by_cases hn : n < K
        · rw [Nat.mod_eq_of_lt hn]
        · have hKn : K ≤ n := by omega
          have hsub : n - K < n := by omega
          have hmod_sub : (n - K) % K = n % K := by
            calc
              (n - K) % K = ((n - K) + K) % K := by
                simp [Nat.add_mod]
              _ = n % K := by rw [Nat.sub_add_cancel hKn]
          calc
            hbIterate aStar bStar hf xMinusOne xZero n =
                hbIterate aStar bStar hf xMinusOne xZero ((n - K) + K) := by
                  rw [Nat.sub_add_cancel hKn]
            _ = hbIterate aStar bStar hf xMinusOne xZero (n - K) :=
              hperiod (n - K)
            _ = hbIterate aStar bStar hf xMinusOne xZero ((n - K) % K) :=
              ih (n - K) hsub
            _ = hbIterate aStar bStar hf xMinusOne xZero (n % K) := by
              rw [hmod_sub]
  have hiterate_constant (n : ℕ) :
      hbIterate aStar bStar hf xMinusOne xZero n =
        hbIterate aStar bStar hf xMinusOne xZero 0 := by
    let i : Fin K := ⟨n % K, Nat.mod_lt _ (by omega)⟩
    calc
      hbIterate aStar bStar hf xMinusOne xZero n =
          hbIterate aStar bStar hf xMinusOne xZero (n % K) :=
        hiterate_mod n
      _ = y i := by
        rfl
      _ = y 0 := hconstant i 0
      _ = hbIterate aStar bStar hf xMinusOne xZero 0 := by
        rfl
  apply hneq
  calc
    hbIterate aStar bStar hf xMinusOne xZero (t + 1) =
        hbIterate aStar bStar hf xMinusOne xZero 0 :=
      hiterate_constant (t + 1)
    _ = hbIterate aStar bStar hf xMinusOne xZero t :=
      (hiterate_constant t).symm

/-- The shifted smoothness constant `L_0=1-q` from D1. -/
def hbL0 (q : ℝ) : ℝ := 1 - q

/-- The centered nonlinear term
`D(x)=grad f(x_*+x)-q x` used in the loop analysis. -/
def hbCenteredNonlinearity {q : ℝ} {d : ℕ} (hq : 0 < q)
    (hf : AdmissibleObjective q d) (x : Vec d) : Vec d :=
  gradient hf.f (objectiveMinimizer hq hf + x) - q • x

private theorem gradient_objectiveMinimizer_eq_zero {q : ℝ} {d : ℕ} (hq : 0 < q)
    (hf : AdmissibleObjective q d) :
    gradient hf.f (objectiveMinimizer hq hf) = 0 := by
  let xStar := objectiveMinimizer hq hf
  have hmin : ∀ y : Vec d, hf.f xStar ≤ hf.f y := by
    simpa [xStar] using objectiveMinimizer_is_min hq hf
  have hgrad : HasGradientAt hf.f (gradient hf.f xStar) xStar :=
    HB_admissible_objective_hasGradientAt hf xStar
  have hzero_eq_grad : (0 : Vec d) = gradient hf.f xStar := by
    refine
      eq_gradient_of_hasGradientAt_of_affine_minorant_touch
        (F := hf.f) (g := gradient hf.f xStar) (a := (0 : Vec d))
        (x0 := xStar) (c := -hf.f xStar) hgrad ?_ ?_
    · intro x
      simpa using hmin x
    · simp
  simpa [xStar] using hzero_eq_grad.symm

theorem hbCenteredNonlinearity_zero {q : ℝ} {d : ℕ} (hq : 0 < q)
    (hf : AdmissibleObjective q d) :
    hbCenteredNonlinearity hq hf 0 = 0 := by
  simp [hbCenteredNonlinearity, gradient_objectiveMinimizer_eq_zero hq hf]

private theorem half_norm_sub_sq_eq_half_norm_sq_sub_inner {d : ℕ}
    (u v : Vec d) :
    (1 / 2 : ℝ) * ‖u - v‖ ^ 2 =
      (1 / 2 : ℝ) * (‖u‖ ^ 2 - ‖v‖ ^ 2) - inner ℝ v (u - v) := by
  rw [norm_sub_sq_real]
  rw [inner_sub_right, real_inner_comm u v, real_inner_self_eq_norm_sq]
  ring

private theorem shifted_potential_support_and_upper {q : ℝ} {d : ℕ}
    (hf : AdmissibleObjective q d) (u v : Vec d) :
    let psi := fun z : Vec d => hf.f z - (q / 2) * ‖z‖ ^ 2
    let p := fun z : Vec d => gradient hf.f z - q • z
    0 ≤ psi u - psi v - inner ℝ (p v) (u - v) ∧
      psi u - psi v - inner ℝ (p v) (u - v) ≤
        ((1 - q) / 2) * ‖u - v‖ ^ 2 := by
  dsimp
  have hquad :
      (q / 2) * ‖u - v‖ ^ 2 =
        (q / 2) * (‖u‖ ^ 2 - ‖v‖ ^ 2) - inner ℝ (q • v) (u - v) := by
    have hbase := half_norm_sub_sq_eq_half_norm_sq_sub_inner u v
    calc
      (q / 2) * ‖u - v‖ ^ 2 =
          q * ((1 / 2 : ℝ) * ‖u - v‖ ^ 2) := by ring
      _ = q * ((1 / 2 : ℝ) * (‖u‖ ^ 2 - ‖v‖ ^ 2) -
            inner ℝ v (u - v)) := by rw [hbase]
      _ = (q / 2) * (‖u‖ ^ 2 - ‖v‖ ^ 2) -
            inner ℝ (q • v) (u - v) := by
          rw [inner_smul_left]
          simp
          ring
  have hB_eq :
      (hf.f u - (q / 2) * ‖u‖ ^ 2) -
          (hf.f v - (q / 2) * ‖v‖ ^ 2) -
            inner ℝ (gradient hf.f v - q • v) (u - v) =
        (hf.f u - hf.f v - inner ℝ (gradient hf.f v) (u - v)) -
          (q / 2) * ‖u - v‖ ^ 2 := by
    rw [inner_sub_left]
    nlinarith [hquad]
  have hstrong := hf.strongConvex_lower v u
  have hstrong_gap :
      (q / 2) * ‖u - v‖ ^ 2 ≤
        hf.f u - hf.f v - inner ℝ (gradient hf.f v) (u - v) := by
    linarith
  have hsmooth_carrier :=
    Convex.carrier_smooth_quadratic_upper_bound_of_hasGradientWithinAt_lipschitz
      (X := Set.univ)
      (f := fun z : {x : Vec d // x ∈ Set.univ} => hf.f z.1)
      (F := hf.f)
      (grad := fun z : {x : Vec d // x ∈ Set.univ} => gradient hf.f z.1)
      (L := (1 : ℝ))
      (convex_univ)
      (by intro z hz; rfl)
      (by
        intro z
        simpa [hasGradientWithinAt_univ] using
          (HB_admissible_objective_hasGradientAt hf z.1))
      (by
        intro x y
        simpa [one_mul] using hf.gradient_lipschitz x.1 y.1)
      ⟨u, by simp⟩ ⟨v, by simp⟩
  have hsmooth_gap :
      hf.f u - hf.f v - inner ℝ (gradient hf.f v) (u - v) ≤
        (1 / 2 : ℝ) * ‖u - v‖ ^ 2 := by
    simpa using hsmooth_carrier
  constructor
  · rw [hB_eq]
    linarith
  · rw [hB_eq]
    nlinarith [hsmooth_gap]

private theorem admissible_gradient_strong_monotone {q : ℝ} {d : ℕ}
    (hf : AdmissibleObjective q d) (u v : Vec d) :
    q * ‖u - v‖ ^ 2 ≤
      inner ℝ (gradient hf.f u - gradient hf.f v) (u - v) := by
  have h₁ := hf.strongConvex_lower v u
  have h₂ := hf.strongConvex_lower u v
  have hgap₁ :
      (q / 2) * ‖u - v‖ ^ 2 ≤
        hf.f u - hf.f v - inner ℝ (gradient hf.f v) (u - v) := by
    linarith
  have hgap₂ :
      (q / 2) * ‖u - v‖ ^ 2 ≤
        hf.f v - hf.f u + inner ℝ (gradient hf.f u) (u - v) := by
    have hnorm : ‖v - u‖ = ‖u - v‖ := by simpa using norm_sub_rev v u
    have hinner : inner ℝ (gradient hf.f u) (v - u) =
        -inner ℝ (gradient hf.f u) (u - v) := by
      rw [show v - u = -(u - v) by abel, inner_neg_right]
    rw [hnorm, hinner] at h₂
    linarith
  have hsum :
      (hf.f u - hf.f v - inner ℝ (gradient hf.f v) (u - v)) +
          (hf.f v - hf.f u + inner ℝ (gradient hf.f u) (u - v)) =
        inner ℝ (gradient hf.f u - gradient hf.f v) (u - v) := by
    rw [inner_sub_left]
    ring
  nlinarith [hgap₁, hgap₂, hsum]

private theorem bregman_gap_ge_half_grad_diff_sq_of_support_upper {d : ℕ}
    {psi : Vec d → ℝ} {p : Vec d → Vec d} {L : ℝ} (hL : 0 < L)
    (hsupport : ∀ x y : Vec d, 0 ≤ psi x - psi y - inner ℝ (p y) (x - y))
    (hupper :
      ∀ x y : Vec d,
        psi x - psi y - inner ℝ (p y) (x - y) ≤ (L / 2) * ‖x - y‖ ^ 2)
    (u v : Vec d) :
    (1 / (2 * L)) * ‖p u - p v‖ ^ 2 ≤
      psi u - psi v - inner ℝ (p v) (u - v) := by
  let r : Vec d := p u - p v
  let z : Vec d := u - (1 / L) • r
  have hsupport_zv := hsupport z v
  have hupper_zu := hupper z u
  have hstep :
      psi v + inner ℝ (p v) (z - v) ≤
        psi u + inner ℝ (p u) (z - u) + (L / 2) * ‖z - u‖ ^ 2 := by
    linarith
  have hzinv_pos : 0 < (1 / L : ℝ) := one_div_pos.mpr hL
  have hnorm_zu :
      ‖z - u‖ ^ 2 = (1 / L) ^ 2 * ‖r‖ ^ 2 := by
    have hzu : z - u = -((1 / L) • r) := by
      simp [z, sub_eq_add_neg, add_assoc]
    rw [hzu, norm_neg, norm_smul]
    rw [Real.norm_eq_abs, abs_of_pos hzinv_pos]
    ring
  have hmain :
      psi v + inner ℝ (p v) (u - v) + (1 / L) * ‖r‖ ^ 2 ≤
        psi u + (L / 2) * ((1 / L) ^ 2 * ‖r‖ ^ 2) := by
    have hzv : z - v = (u - v) - (1 / L) • r := by
      simp [z, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    have hzu : z - u = -((1 / L) • r) := by
      simp [z, sub_eq_add_neg, add_assoc]
    have hleft :
        inner ℝ (p v) (z - v) =
          inner ℝ (p v) (u - v) - (1 / L) * inner ℝ (p v) r := by
      rw [hzv, inner_sub_right, inner_smul_right]
    have hright :
        inner ℝ (p u) (z - u) = - (1 / L) * inner ℝ (p u) r := by
      rw [hzu, inner_neg_right, inner_smul_right]
      ring
    have hrnorm :
        inner ℝ (p u) r - inner ℝ (p v) r = ‖r‖ ^ 2 := by
      have hpu : p u = r + p v := by
        simp [r, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      rw [hpu, inner_add_left, real_inner_self_eq_norm_sq]
      ring
    have hstep' := hstep
    rw [hleft, hright, hnorm_zu] at hstep'
    nlinarith [hstep', hrnorm]
  have hL_ne : L ≠ 0 := ne_of_gt hL
  have hcoef :
      (L / 2) * ((1 / L) ^ 2 * ‖r‖ ^ 2) =
        (1 / (2 * L)) * ‖r‖ ^ 2 := by
    field_simp [hL_ne]
  rw [hcoef] at hmain
  have hcoef_one :
      (1 / L) * ‖r‖ ^ 2 =
        2 * ((1 / (2 * L)) * ‖r‖ ^ 2) := by
    field_simp [hL_ne]
  rw [hcoef_one] at hmain
  change (1 / (2 * L)) * ‖r‖ ^ 2 ≤
    psi u - psi v - inner ℝ (p v) (u - v)
  nlinarith [hmain]

private theorem gradient_lipschitz_of_support_upper {d : ℕ}
    {psi : Vec d → ℝ} {p : Vec d → Vec d} {L : ℝ} (hL : 0 < L)
    (hsupport : ∀ x y : Vec d, 0 ≤ psi x - psi y - inner ℝ (p y) (x - y))
    (hupper :
      ∀ x y : Vec d,
        psi x - psi y - inner ℝ (p y) (x - y) ≤ (L / 2) * ‖x - y‖ ^ 2)
    (u v : Vec d) :
    ‖p u - p v‖ ≤ L * ‖u - v‖ := by
  let r : Vec d := p u - p v
  let dx : Vec d := u - v
  have hgap_uv :=
    bregman_gap_ge_half_grad_diff_sq_of_support_upper
      (d := d) (psi := psi) (p := p) hL hsupport hupper u v
  have hgap_vu :=
    bregman_gap_ge_half_grad_diff_sq_of_support_upper
      (d := d) (psi := psi) (p := p) hL hsupport hupper v u
  have hsum :
      (psi u - psi v - inner ℝ (p v) (u - v)) +
          (psi v - psi u - inner ℝ (p u) (v - u)) =
        inner ℝ r dx := by
    change
      (psi u - psi v - inner ℝ (p v) (u - v)) +
          (psi v - psi u - inner ℝ (p u) (v - u)) =
        inner ℝ (p u - p v) (u - v)
    rw [show v - u = -(u - v) by abel, inner_neg_right, inner_sub_left]
    ring
  have hsumineq :
      (1 / L) * ‖r‖ ^ 2 ≤ inner ℝ r dx := by
    have htwo :
        2 * ((1 / (2 * L)) * ‖r‖ ^ 2) ≤
          (psi u - psi v - inner ℝ (p v) (u - v)) +
            (psi v - psi u - inner ℝ (p u) (v - u)) := by
      have hgap_vu' :
          1 / (2 * L) * ‖p u - p v‖ ^ 2 ≤
            psi v - psi u - inner ℝ (p u) (v - u) := by
        simpa [norm_sub_rev] using hgap_vu
      change 2 * ((1 / (2 * L)) * ‖p u - p v‖ ^ 2) ≤
        (psi u - psi v - inner ℝ (p v) (u - v)) +
          (psi v - psi u - inner ℝ (p u) (v - u))
      nlinarith [hgap_uv, hgap_vu']
    have hcoef :
        2 * ((1 / (2 * L)) * ‖r‖ ^ 2) = (1 / L) * ‖r‖ ^ 2 := by
      have hL_ne : L ≠ 0 := ne_of_gt hL
      field_simp [hL_ne]
    rw [← hcoef, ← hsum]
    exact htwo
  have hcoco : ‖r‖ ^ 2 ≤ L * inner ℝ r dx := by
    have hmul := mul_le_mul_of_nonneg_left hsumineq (le_of_lt hL)
    have hcoef : L * ((1 / L) * ‖r‖ ^ 2) = ‖r‖ ^ 2 := by
      have hL_ne : L ≠ 0 := ne_of_gt hL
      field_simp [hL_ne]
    nlinarith [hmul, hcoef]
  have hinner_le : inner ℝ r dx ≤ ‖r‖ * ‖dx‖ := real_inner_le_norm r dx
  have hnorm_sq_le : ‖r‖ ^ 2 ≤ L * (‖r‖ * ‖dx‖) := by
    exact hcoco.trans (mul_le_mul_of_nonneg_left hinner_le (le_of_lt hL))
  by_cases hr : ‖r‖ = 0
  · change ‖r‖ ≤ L * ‖dx‖
    rw [hr]
    positivity
  · have hrpos : 0 < ‖r‖ := lt_of_le_of_ne (norm_nonneg r) (Ne.symm hr)
    change ‖r‖ ≤ L * ‖dx‖
    have hmul : ‖r‖ * ‖r‖ ≤ ‖r‖ * (L * ‖dx‖) := by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hnorm_sq_le
    exact le_of_mul_le_mul_left hmul hrpos

private theorem shifted_gradient_lipschitz_of_q_lt_one {q : ℝ} {d : ℕ}
    (hf : AdmissibleObjective q d) (hq1 : q < 1) (u v : Vec d) :
    ‖(gradient hf.f u - q • u) - (gradient hf.f v - q • v)‖ ≤
      (1 - q) * ‖u - v‖ := by
  let psi := fun z : Vec d => hf.f z - (q / 2) * ‖z‖ ^ 2
  let p := fun z : Vec d => gradient hf.f z - q • z
  have hL : 0 < 1 - q := by linarith
  have hsupport :
      ∀ x y : Vec d, 0 ≤ psi x - psi y - inner ℝ (p y) (x - y) := by
    intro x y
    exact (shifted_potential_support_and_upper hf x y).1
  have hupper :
      ∀ x y : Vec d,
        psi x - psi y - inner ℝ (p y) (x - y) ≤
          ((1 - q) / 2) * ‖x - y‖ ^ 2 := by
    intro x y
    exact (shifted_potential_support_and_upper hf x y).2
  simpa [p] using
    gradient_lipschitz_of_support_upper
      (d := d) (psi := psi) (p := p) (L := 1 - q)
      hL hsupport hupper u v

private theorem shifted_gradient_residual_zero_of_one_le_q {q : ℝ} {d : ℕ}
    (hf : AdmissibleObjective q d) (hqge : 1 ≤ q) (u v : Vec d) :
    (gradient hf.f u - q • u) - (gradient hf.f v - q • v) = 0 := by
  let r : Vec d := gradient hf.f u - gradient hf.f v
  let dx : Vec d := u - v
  have hmono :
      q * ‖dx‖ ^ 2 ≤ inner ℝ r dx := by
    simpa [r, dx] using admissible_gradient_strong_monotone hf u v
  have hlip : ‖r‖ ≤ ‖dx‖ := by
    simpa [r, dx] using hf.gradient_lipschitz v u
  have hlip_sq : ‖r‖ ^ 2 ≤ ‖dx‖ ^ 2 := by
    nlinarith [hlip, norm_nonneg r, norm_nonneg dx]
  have hq_nonneg : 0 ≤ q := by linarith
  have hnorm_res_nonpos : ‖r - q • dx‖ ^ 2 ≤ 0 := by
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hq_nonneg]
    have hmono_scaled : q * (q * ‖dx‖ ^ 2) ≤ q * inner ℝ r dx :=
      mul_le_mul_of_nonneg_left hmono hq_nonneg
    have hq_sq_ge_one : 1 ≤ q ^ 2 := by nlinarith
    have hdx_q_bound : ‖dx‖ ^ 2 ≤ q ^ 2 * ‖dx‖ ^ 2 :=
      by simpa using mul_le_mul_of_nonneg_right hq_sq_ge_one (sq_nonneg ‖dx‖)
    nlinarith [hlip_sq, hmono_scaled, hdx_q_bound]
  have hnorm_res_eq : ‖r - q • dx‖ = 0 := by
    have hsq_nonneg : 0 ≤ ‖r - q • dx‖ ^ 2 := sq_nonneg _
    nlinarith
  have hvec : r - q • dx = 0 := norm_eq_zero.mp hnorm_res_eq
  simpa [r, dx, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hvec

private theorem eq_of_one_lt_admissible_q {q : ℝ} {d : ℕ}
    (hf : AdmissibleObjective q d) (hqgt : 1 < q) (u v : Vec d) :
    u = v := by
  let r : Vec d := gradient hf.f u - gradient hf.f v
  let dx : Vec d := u - v
  have hmono :
      q * ‖dx‖ ^ 2 ≤ inner ℝ r dx := by
    simpa [r, dx] using admissible_gradient_strong_monotone hf u v
  have hlip : ‖r‖ ≤ ‖dx‖ := by
    simpa [r, dx] using hf.gradient_lipschitz v u
  have hinner_le : inner ℝ r dx ≤ ‖r‖ * ‖dx‖ := real_inner_le_norm r dx
  have hnorm_mul : ‖r‖ * ‖dx‖ ≤ ‖dx‖ * ‖dx‖ :=
    mul_le_mul_of_nonneg_right hlip (norm_nonneg dx)
  have hinner_le_sq : inner ℝ r dx ≤ ‖dx‖ ^ 2 := by
    nlinarith [hinner_le, hnorm_mul]
  have hq_le_one_on_sq : q * ‖dx‖ ^ 2 ≤ ‖dx‖ ^ 2 :=
    hmono.trans hinner_le_sq
  have hdx_sq_zero : ‖dx‖ ^ 2 = 0 := by
    nlinarith [hq_le_one_on_sq, hqgt, sq_nonneg ‖dx‖]
  have hdx_zero : dx = 0 := by
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hdx_sq_zero)
  exact sub_eq_zero.mp hdx_zero

theorem hbCenteredNonlinearity_lipschitz_from_zero {q : ℝ} {d : ℕ}
    (hq : 0 < q) (hf : AdmissibleObjective q d) (x : Vec d) :
    ‖hbCenteredNonlinearity hq hf x‖ ≤ hbL0 q * ‖x‖ := by
  let xStar := objectiveMinimizer hq hf
  by_cases hq1 : q < 1
  · have hshift :=
      shifted_gradient_lipschitz_of_q_lt_one hf hq1 (xStar + x) xStar
    simpa [hbCenteredNonlinearity, hbL0, xStar, sub_eq_add_neg, add_smul,
      add_assoc, add_left_comm, add_comm, gradient_objectiveMinimizer_eq_zero hq hf] using hshift
  · have hqge : 1 ≤ q := le_of_not_gt hq1
    by_cases hqeq : q = 1
    · have hres :=
        shifted_gradient_residual_zero_of_one_le_q hf hqge (xStar + x) xStar
      subst q
      have hcenter_zero : hbCenteredNonlinearity hq hf x = 0 := by
        unfold hbCenteredNonlinearity
        have hres' := hres
        rw [one_smul, gradient_objectiveMinimizer_eq_zero hq hf] at hres'
        have hnorm :
            gradient hf.f (xStar + x) - (xStar + x) - (0 - (1 : ℝ) • xStar) =
              gradient hf.f (xStar + x) - x := by
          simp [one_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          abel
        have hres'' : gradient hf.f (xStar + x) - x = 0 := hnorm ▸ hres'
        simpa [xStar, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hres''
      simp [hcenter_zero, hbL0]
    · have hqgt : 1 < q := lt_of_le_of_ne hqge (Ne.symm hqeq)
      have hxStar_eq : xStar + x = xStar :=
        eq_of_one_lt_admissible_q hf hqgt (xStar + x) xStar
      have hxzero : x = 0 := by
        have hsub := congrArg (fun y : Vec d => y - xStar) hxStar_eq
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub
      simp [hxzero, hbCenteredNonlinearity_zero, hbL0]

/-- Denominator of the D5 Heavy-Ball plant. -/
def hbTransferDenominator (q a b : ℝ) (z : ℂ) : ℂ :=
  z ^ 2 - ((1 + b - a * q : ℝ) : ℂ) * z + (b : ℂ)

/-- The non-pole domain of the D5 Heavy-Ball plant. -/
def hbTransferDomain (q a b : ℝ) (z : ℂ) : Prop :=
  hbTransferDenominator q a b z ≠ 0

/-- The transformed Heavy-Ball transfer function
`G(z)=-az/(z^2-(1+b-aq)z+b)`, defined only away from poles. -/
def hbTransferFunction (q a b : ℝ)
    (z : {z : ℂ // hbTransferDomain q a b z}) : ℂ :=
  -((a : ℂ) * (z : ℂ)) / hbTransferDenominator q a b (z : ℂ)

theorem hbTransferFunction_eq (q a b : ℝ)
    (z : {z : ℂ // hbTransferDomain q a b z}) :
    hbTransferFunction q a b z =
      -((a : ℂ) * (z : ℂ)) /
        ((z : ℂ) ^ 2 - ((1 + b - a * q : ℝ) : ℂ) * (z : ℂ) + (b : ℂ)) := by
  rfl

/-- Source pole condition for the D5 plant. -/
def hbPlantPolesInsideUnitDisk (q a b : ℝ) : Prop :=
  ∀ z : ℂ, hbTransferDenominator q a b z = 0 → ‖z‖ < 1

theorem hbTransferDomain_of_unit_norm {q a b : ℝ}
    (hD : ParameterDomain q a b) {z : ℂ} (hz : ‖z‖ = 1) :
    hbTransferDomain q a b z := by
  unfold hbTransferDomain
  intro hroot
  rcases hD with ⟨hq0, hq1, hb0, hb1, ha0, ha_upper⟩
  have hnorm : z.re ^ 2 + z.im ^ 2 = 1 := by
    have hsq : ‖z‖ ^ 2 = (1 : ℝ) := by
      rw [hz]
      norm_num
    have hns : Complex.normSq z = (1 : ℝ) := by
      rw [Complex.normSq_eq_norm_sq, hsq]
    simpa [Complex.normSq_apply, pow_two] using hns
  have hre : z.re ^ 2 - z.im ^ 2 - (1 + b - a * q) * z.re + b = 0 := by
    have h := congrArg Complex.re hroot
    unfold hbTransferDenominator at h
    simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, pow_two] at h
    nlinarith
  have him_factor : z.im * (2 * z.re - (1 + b - a * q)) = 0 := by
    have h := congrArg Complex.im hroot
    unfold hbTransferDenominator at h
    simp [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, pow_two] at h
    nlinarith
  have him : z.im = 0 := by
    rcases mul_eq_zero.mp him_factor with hz_im | hfactor
    · exact hz_im
    · have hcoef : 1 + b - a * q = 2 * z.re := by
        nlinarith [hfactor]
      have hcoef_mul : (1 + b - a * q) * z.re = 2 * z.re ^ 2 := by
        rw [hcoef]
        ring
      have hb_eq_one : b = 1 := by
        nlinarith [hre, hnorm, hcoef_mul]
      nlinarith [hb_eq_one, hb1]
  have hsq_re : z.re ^ 2 = 1 := by
    nlinarith [hnorm, him]
  rcases sq_eq_one_iff.mp hsq_re with hreal | hreal
  · have haq_zero : a * q = 0 := by
      nlinarith [hre, him, hreal]
    have haq_pos : 0 < a * q := mul_pos ha0 hq0
    nlinarith [haq_zero, haq_pos]
  · have haq_eq : a * q = 2 * (1 + b) := by
      nlinarith [hre, him, hreal]
    have haq_lt_a : a * q < a := by
      simpa using (mul_lt_mul_of_pos_left hq1 ha0)
    have haq_lt : a * q < 2 * (1 + b) := lt_trans haq_lt_a ha_upper
    nlinarith [haq_eq, haq_lt]

private theorem hbPlantPolesInsideUnitDisk_of_parameterDomain {q a b : ℝ}
    (hD : ParameterDomain q a b) :
    hbPlantPolesInsideUnitDisk q a b := by
  unfold hbPlantPolesInsideUnitDisk
  intro z hroot
  by_contra hnot
  rcases hD with ⟨hq0, hq1, hb0, hb1, ha0, ha_upper⟩
  have haq_pos : 0 < a * q := mul_pos ha0 hq0
  have haq_lt_a : a * q < a := by
    simpa using (mul_lt_mul_of_pos_left hq1 ha0)
  have haq_lt : a * q < 2 * (1 + b) := lt_trans haq_lt_a ha_upper
  have hnorm_ge : 1 ≤ ‖z‖ := le_of_not_gt hnot
  have hnorm_sq_ge : 1 ≤ ‖z‖ ^ 2 := by
    have hnorm_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
    nlinarith
  have hnormSq : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    simpa [Complex.normSq_apply, pow_two] using (Complex.normSq_eq_norm_sq z)
  have hcoords_ge : 1 ≤ z.re ^ 2 + z.im ^ 2 := by
    nlinarith [hnorm_sq_ge, hnormSq]
  have hre : z.re ^ 2 - z.im ^ 2 - (1 + b - a * q) * z.re + b = 0 := by
    have h := congrArg Complex.re hroot
    unfold hbTransferDenominator at h
    simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, pow_two] at h
    nlinarith
  have him_factor : z.im * (2 * z.re - (1 + b - a * q)) = 0 := by
    have h := congrArg Complex.im hroot
    unfold hbTransferDenominator at h
    simp [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, pow_two] at h
    nlinarith
  rcases mul_eq_zero.mp him_factor with him | hfactor
  · have hre_sq_ge : 1 ≤ z.re ^ 2 := by
      nlinarith [hcoords_ge, him]
    have habs : 1 ≤ |z.re| := (one_le_sq_iff_one_le_abs z.re).mp hre_sq_ge
    by_cases hx_nonneg : 0 ≤ z.re
    · have hx_ge1 : 1 ≤ z.re := by
        simpa [abs_of_nonneg hx_nonneg] using habs
      have hx_pos : 0 < z.re := lt_of_lt_of_le zero_lt_one hx_ge1
      have hC_lt : 1 + b - a * q < 1 + b := by nlinarith [haq_pos]
      have hroot_eq : z.re ^ 2 + b = (1 + b - a * q) * z.re := by
        nlinarith [hre, him]
      have hleft_le : (1 + b) * z.re ≤ z.re ^ 2 + b := by
        have hx_minus_one : 0 ≤ z.re - 1 := by linarith
        have hx_minus_b : 0 ≤ z.re - b := by linarith
        have hfac : 0 ≤ (z.re - 1) * (z.re - b) :=
          mul_nonneg hx_minus_one hx_minus_b
        nlinarith [hfac]
      have hright_lt : (1 + b - a * q) * z.re < (1 + b) * z.re :=
        mul_lt_mul_of_pos_right hC_lt hx_pos
      nlinarith [hroot_eq, hleft_le, hright_lt]
    · have hx_le0 : z.re ≤ 0 := le_of_lt (lt_of_not_ge hx_nonneg)
      have hx_le_neg1 : z.re ≤ -1 := by
        have hneg : 1 ≤ -z.re := by
          simpa [abs_of_nonpos hx_le0] using habs
        linarith
      have hx_neg : z.re < 0 := by linarith
      have hC_gt : -(1 + b) < 1 + b - a * q := by nlinarith [haq_lt]
      have hroot_eq : z.re ^ 2 + b = (1 + b - a * q) * z.re := by
        nlinarith [hre, him]
      have hleft_le : (-(1 + b)) * z.re ≤ z.re ^ 2 + b := by
        have hx_plus_one : z.re + 1 ≤ 0 := by linarith
        have hx_plus_b : z.re + b ≤ 0 := by linarith
        have hfac : 0 ≤ (z.re + 1) * (z.re + b) :=
          mul_nonneg_of_nonpos_of_nonpos hx_plus_one hx_plus_b
        nlinarith [hfac]
      have hright_lt : (1 + b - a * q) * z.re < (-(1 + b)) * z.re :=
        mul_lt_mul_of_neg_right hC_gt hx_neg
      nlinarith [hroot_eq, hleft_le, hright_lt]
  · have hcoef : 1 + b - a * q = 2 * z.re := by
      nlinarith [hfactor]
    have hcoef_mul : (1 + b - a * q) * z.re = 2 * z.re ^ 2 := by
      rw [hcoef]
      ring
    have hb_eq_normSq : b = z.re ^ 2 + z.im ^ 2 := by
      nlinarith [hre, hcoef_mul]
    nlinarith [hb_eq_normSq, hcoords_ge, hb1]

/-- Unit-circle specialization of the D5 plant, using the source pole exclusion. -/
def hbTransferUnitCircle (q a b : ℝ) (hD : ParameterDomain q a b)
    (z : ℂ) (hz : ‖z‖ = 1) : ℂ :=
  hbTransferFunction q a b ⟨z, hbTransferDomain_of_unit_norm hD hz⟩

/-- Free homogeneous response of the centered linear Heavy-Ball recurrence. -/
def hbFreeResponse {d : ℕ} (q a b : ℝ) (xMinusOne xZero : Vec d) :
    ℕ → Vec d
  | 0 => xZero
  | 1 => (1 + b - a * q) • xZero - b • xMinusOne
  | n + 2 =>
      (1 + b - a * q) • hbFreeResponse q a b xMinusOne xZero (n + 1) -
        b • hbFreeResponse q a b xMinusOne xZero n

/-- The causal plant response `G input` with zero initial centered state. -/
def hbPlantResponse {d : ℕ} (q a b : ℝ) (input : ℕ → Vec d) :
    ℕ → Vec d
  | 0 => 0
  | 1 => -a • input 0
  | n + 2 =>
      (1 + b - a * q) • hbPlantResponse q a b input (n + 1) -
        b • hbPlantResponse q a b input n - a • input (n + 1)

/-- Strict causality of the zero-state plant response: time `n` depends only
on inputs at times strictly before `n`. -/
def hbPlantStrictlyCausal (q a b : ℝ) : Prop :=
  ∀ {d : ℕ} (u v : ℕ → Vec d) (n : ℕ),
    (∀ k : ℕ, k < n → u k = v k) →
      hbPlantResponse q a b u n = hbPlantResponse q a b v n

/-- Source strict-causality marker for the D5 plant, exposed through the
time-domain plant response rather than a tautological rational identity. -/
def hbTransferStrictlyCausal (q a b : ℝ) : Prop :=
  hbPlantStrictlyCausal q a b

private theorem hbPlantResponse_strictlyCausal (q a b : ℝ) :
    hbTransferStrictlyCausal q a b := by
  unfold hbTransferStrictlyCausal hbPlantStrictlyCausal
  intro d u v n hprefix
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simp [hbPlantResponse]
      | succ n =>
          cases n with
          | zero =>
              have h0 : u 0 = v 0 := hprefix 0 (by omega)
              simp [hbPlantResponse, h0]
          | succ n =>
              have hprev1 :
                  hbPlantResponse q a b u (n + 1) =
                    hbPlantResponse q a b v (n + 1) := by
                exact ih (n + 1) (by omega) (by
                  intro k hk
                  exact hprefix k (by omega))
              have hprev0 :
                  hbPlantResponse q a b u n = hbPlantResponse q a b v n := by
                exact ih n (by omega) (by
                  intro k hk
                  exact hprefix k (by omega))
              have hinput : u (n + 1) = v (n + 1) := hprefix (n + 1) (by omega)
              simp [hbPlantResponse, hprev1, hprev0, hinput]

/-- Centered generated iterate sequence `x_t-x_*`. -/
def hbCenteredIterate {q : ℝ} {d : ℕ} (hq : 0 < q) (a b : ℝ)
    (hf : AdmissibleObjective q d) (xMinusOne xZero : Vec d) (t : ℕ) :
    Vec d :=
  (hbCenteredStateAt hq a b hf xMinusOne xZero t).2

private theorem hbCenteredIterate_forced_recurrence {q : ℝ} {d : ℕ}
    (hq : 0 < q) (a b : ℝ)
    (hf : AdmissibleObjective q d) (xMinusOne xZero : Vec d) (n : ℕ) :
    hbCenteredIterate hq a b hf xMinusOne xZero (n + 2) =
      (1 + b - a * q) • hbCenteredIterate hq a b hf xMinusOne xZero (n + 1) -
        b • hbCenteredIterate hq a b hf xMinusOne xZero n -
          a • hbCenteredNonlinearity hq hf
            (hbCenteredIterate hq a b hf xMinusOne xZero (n + 1)) := by
  let xStar := objectiveMinimizer hq hf
  have hprev :
      (hbCenteredStateAt hq a b hf xMinusOne xZero (n + 1)).1 =
        hbCenteredIterate hq a b hf xMinusOne xZero n := by
    simp [hbCenteredIterate, hbCenteredStateAt_succ, hbCenteredMap]
  unfold hbCenteredIterate
  rw [hbCenteredStateAt_succ]
  simp [hbCenteredMap, hbSuccessor, hbCenteredNonlinearity, hprev, xStar,
    hbCenteredIterate, sub_eq_add_neg, add_smul, smul_add, smul_sub,
    sub_smul, one_smul, smul_smul, add_assoc, add_left_comm, add_comm]
  abel

/-- Variation-of-constants identity `x=e+GD(x)` for a generated trajectory. -/
def hbLoopRepresentation {q : ℝ} {d : ℕ} (hq : 0 < q) (a b : ℝ)
    (hf : AdmissibleObjective q d) (xMinusOne xZero : Vec d) : Prop :=
  let xStar := objectiveMinimizer hq hf
  let x := hbCenteredIterate hq a b hf xMinusOne xZero
  let e := hbFreeResponse q a b (xMinusOne - xStar) (xZero - xStar)
  let input := fun t : ℕ => hbCenteredNonlinearity hq hf (x t)
  ∀ t : ℕ, x t = e t + hbPlantResponse q a b input t

private theorem hbLoopRepresentation_generated {q : ℝ} {d : ℕ}
    (hq : 0 < q) (a b : ℝ)
    (hf : AdmissibleObjective q d) (xMinusOne xZero : Vec d) :
    hbLoopRepresentation hq a b hf xMinusOne xZero := by
  let xStar := objectiveMinimizer hq hf
  let x := hbCenteredIterate hq a b hf xMinusOne xZero
  let e := hbFreeResponse q a b (xMinusOne - xStar) (xZero - xStar)
  let input := fun t : ℕ => hbCenteredNonlinearity hq hf (x t)
  change ∀ t : ℕ, x t = e t + hbPlantResponse q a b input t
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      cases t with
      | zero =>
          simp [x, e, xStar, hbCenteredIterate, hbCenteredStateAt, hbInitialCenteredState,
            hbFreeResponse, hbPlantResponse]
      | succ t =>
          cases t with
          | zero =>
              simp [x, e, input, hbCenteredIterate, hbCenteredStateAt_succ,
                hbCenteredStateAt_zero, hbCenteredMap, hbInitialCenteredState,
                hbFreeResponse, hbPlantResponse, hbSuccessor, hbCenteredNonlinearity,
                xStar, sub_eq_add_neg, add_smul, smul_add, smul_sub, sub_smul,
                one_smul, smul_smul, add_assoc, add_left_comm, add_comm]
              abel
          | succ t =>
              have hxrec :
                  x (t + 2) =
                    (1 + b - a * q) • x (t + 1) -
                      b • x t - a • input (t + 1) := by
                simpa [x, input] using
                  hbCenteredIterate_forced_recurrence hq a b hf xMinusOne xZero t
              have ih1 :
                  x (t + 1) =
                    e (t + 1) + hbPlantResponse q a b input (t + 1) :=
                ih (t + 1) (by omega)
              have ih0 :
                  x t = e t + hbPlantResponse q a b input t :=
                ih t (by omega)
              rw [hxrec, ih1, ih0]
              change
                (1 + b - a * q) •
                      (e (t + 1) + hbPlantResponse q a b input (t + 1)) -
                    b • (e t + hbPlantResponse q a b input t) -
                      a • input (t + 1) =
                  ((1 + b - a * q) • e (t + 1) - b • e t) +
                    ((1 + b - a * q) • hbPlantResponse q a b input (t + 1) -
                      b • hbPlantResponse q a b input t - a • input (t + 1))
              simp [sub_eq_add_neg, smul_add]
              abel

/-- Multiplier constant `epsilon=10^-5`. -/
def hbMultiplierEpsilon : ℝ := 1 / 100000

/-- Finite-lag multiplier `M(z)=epsilon+(1-z^{-1})+4/25(1-z^4)`. -/
def hbMultiplier (z : ℂ) : ℂ :=
  (hbMultiplierEpsilon : ℂ) + (1 - z⁻¹) + ((4 / 25 : ℝ) : ℂ) * (1 - z ^ 4)

/-- Time-domain action of the finite-lag multiplier on a bilateral sequence. -/
def hbMultiplierTimeDomain {d : ℕ} (s : ℤ → Vec d) (t : ℤ) : Vec d :=
  hbMultiplierEpsilon • s t + (s t - s (t - 1)) +
    (4 / 25 : ℝ) • (s t - s (t + 4))

/-- The D1-D4 supply inequality for the shifted nonlinearity and multiplier. -/
def hbSupplyInequality {q : ℝ} {d : ℕ} (hq : 0 < q)
    (hf : AdmissibleObjective q d) (τ : ℝ) (x : ℤ → Vec d) : Prop :=
  let p := fun t : ℤ => τ • hbCenteredNonlinearity hq hf (x t)
  let s := fun t : ℤ => hbL0 q • x t - p t
  0 ≤ ∑' t : ℤ, inner ℝ (p t) (hbMultiplierTimeDomain s t)

/-- Frequency variable `r=1-c`. -/
def frequencyR (c : ℝ) : ℝ := 1 - c

def frequencyJ (q a b c : ℝ) : ℝ :=
  2 * (1 - c) * (1 + b ^ 2 - 2 * b * c) -
    a * (1 + q) * (1 + b) * (1 - c) + a ^ 2 * q

def frequencyA (q a b : ℝ) : ℝ := a * (1 - q) * (1 - b)

def frequencyS (c : ℝ) : ℝ := 1 + (32 / 25 : ℝ) * c ^ 2 * (1 + c)

def frequencyK (c : ℝ) : ℝ :=
  (1 + c) * (1 + (16 / 25 : ℝ) * c - (32 / 25 : ℝ) * c ^ 3)

def frequencyW (q a b c : ℝ) : ℝ :=
  frequencyS c * frequencyJ q a b c + frequencyK c * frequencyA q a b

/-- The real polynomial `d(c)` appearing in the frequency numerator. -/
def frequencyD (q a b c : ℝ) : ℝ :=
  let r := frequencyR c
  (-(a ^ 2 * q) + (a * (1 + q) * (1 + b) - 2 * (1 - b) ^ 2) * r) -
      4 * b * r ^ 2

/-- The positive denominator polynomial `T(c)=a^2|h-q|^2`. -/
def frequencyT (q a b c : ℝ) : ℝ :=
  let r := frequencyR c
  a ^ 2 * q ^ 2 + (2 * (1 - b) ^ 2 - 2 * a * q * (1 + b)) * r +
    4 * b * r ^ 2

/-- The frequency numerator `N=-r W(c)+epsilon d(c)`. -/
def frequencyNumerator (q a b c : ℝ) : ℝ :=
  -(frequencyR c) * frequencyW q a b c + hbMultiplierEpsilon * frequencyD q a b c

private theorem bernstein_degree5_lower_bound
    {m t b0 b1 b2 b3 b4 b5 : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hm0 : m ≤ b0) (hm1 : m ≤ b1) (hm2 : m ≤ b2)
    (hm3 : m ≤ b3) (hm4 : m ≤ b4) (hm5 : m ≤ b5) :
    m ≤
      b0 * (1 - t) ^ 5 +
        5 * b1 * t * (1 - t) ^ 4 +
        10 * b2 * t ^ 2 * (1 - t) ^ 3 +
        10 * b3 * t ^ 3 * (1 - t) ^ 2 +
        5 * b4 * t ^ 4 * (1 - t) +
        b5 * t ^ 5 := by
  have hu : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hsq : 0 ≤ t ^ 2 := by
    simpa [pow_two] using sq_nonneg t
  have hb0 : 0 ≤ (1 - t) ^ 5 := pow_nonneg hu 5
  have hb1 : 0 ≤ 5 * t * (1 - t) ^ 4 := by
    exact mul_nonneg (mul_nonneg (by norm_num) ht0) (pow_nonneg hu 4)
  have hb2 : 0 ≤ 10 * t ^ 2 * (1 - t) ^ 3 := by
    exact mul_nonneg (mul_nonneg (by norm_num) hsq) (pow_nonneg hu 3)
  have hb3 : 0 ≤ 10 * t ^ 3 * (1 - t) ^ 2 := by
    exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ht0 3))
      (pow_nonneg hu 2)
  have hb4 : 0 ≤ 5 * t ^ 4 * (1 - t) := by
    exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ht0 4)) hu
  have hb5 : 0 ≤ t ^ 5 := pow_nonneg ht0 5
  have h0 : 0 ≤ (b0 - m) * (1 - t) ^ 5 :=
    mul_nonneg (sub_nonneg.mpr hm0) hb0
  have h1 : 0 ≤ (b1 - m) * (5 * t * (1 - t) ^ 4) :=
    mul_nonneg (sub_nonneg.mpr hm1) hb1
  have h2 : 0 ≤ (b2 - m) * (10 * t ^ 2 * (1 - t) ^ 3) :=
    mul_nonneg (sub_nonneg.mpr hm2) hb2
  have h3 : 0 ≤ (b3 - m) * (10 * t ^ 3 * (1 - t) ^ 2) :=
    mul_nonneg (sub_nonneg.mpr hm3) hb3
  have h4 : 0 ≤ (b4 - m) * (5 * t ^ 4 * (1 - t)) :=
    mul_nonneg (sub_nonneg.mpr hm4) hb4
  have h5 : 0 ≤ (b5 - m) * t ^ 5 :=
    mul_nonneg (sub_nonneg.mpr hm5) hb5
  have hpart :
      (1 - t) ^ 5 + 5 * t * (1 - t) ^ 4 + 10 * t ^ 2 * (1 - t) ^ 3 +
          10 * t ^ 3 * (1 - t) ^ 2 + 5 * t ^ 4 * (1 - t) + t ^ 5 = 1 := by
    ring
  nlinarith [h0, h1, h2, h3, h4, h5, hpart]

private theorem central_polynomial_lower_on_unit_interval {c : ℝ} (hc : |c| ≤ 1) :
    (557731 / 10 : ℝ) ≤
      19200000 * c ^ 5 + 297600 * c ^ 4 - 25951072 * c ^ 3 +
        11531168 * c ^ 2 - 660 * c + 86725 := by
  have hcl := abs_le.mp hc
  by_cases hneg : c ≤ 0
  · let t : ℝ := c + 1
    have ht0 : 0 ≤ t := by
      dsimp [t]
      linarith [hcl.1]
    have ht1 : t ≤ 1 := by
      dsimp [t]
      linarith
    have hbern :
        19200000 * c ^ 5 + 297600 * c ^ 4 - 25951072 * c ^ 3 +
            11531168 * c ^ 2 - 660 * c + 86725 =
          (93336125 / 5 : ℝ) * (1 - t) ^ 5 +
            5 * (87229513 / 5 : ℝ) * t * (1 - t) ^ 4 +
            10 * (30707893 / 5 : ℝ) * t ^ 2 * (1 - t) ^ 3 +
            10 * (6200529 / 5 : ℝ) * t ^ 3 * (1 - t) ^ 2 +
            5 * (434285 / 5 : ℝ) * t ^ 4 * (1 - t) +
            (433625 / 5 : ℝ) * t ^ 5 := by
      dsimp [t]
      ring
    rw [hbern]
    exact bernstein_degree5_lower_bound ht0 ht1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · have hnonneg : 0 ≤ c := le_of_not_ge hneg
    by_cases hhalf : c ≤ 1 / 2
    · let t : ℝ := 2 * c
      have ht0 : 0 ≤ t := by
        dsimp [t]
        linarith
      have ht1 : t ≤ 1 := by
        dsimp [t]
        linarith
      have hbern :
          19200000 * c ^ 5 + 297600 * c ^ 4 - 25951072 * c ^ 3 +
              11531168 * c ^ 2 - 660 * c + 86725 =
            (433625 / 5 : ℝ) * (1 - t) ^ 5 +
              5 * (433295 / 5 : ℝ) * t * (1 - t) ^ 4 +
              10 * (1874361 / 5 : ℝ) * t ^ 2 * (1 - t) ^ 3 +
              10 * (3134881 / 5 : ℝ) * t ^ 3 * (1 - t) ^ 2 +
              5 * (2611513 / 5 : ℝ) * t ^ 4 * (1 - t) +
              (1719515 / 5 : ℝ) * t ^ 5 := by
        dsimp [t]
        ring
      rw [hbern]
      exact bernstein_degree5_lower_bound ht0 ht1
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · have hhalf' : 1 / 2 ≤ c := le_of_not_ge hhalf
      by_cases hthree : c ≤ 3 / 4
      · let t : ℝ := 4 * c - 2
        have ht0 : 0 ≤ t := by
          dsimp [t]
          linarith
        have ht1 : t ≤ 1 := by
          dsimp [t]
          linarith
        have hbern :
            19200000 * c ^ 5 + 297600 * c ^ 4 - 25951072 * c ^ 3 +
                11531168 * c ^ 2 - 660 * c + 86725 =
              (6878060 / 20 : ℝ) * (1 - t) ^ 5 +
                5 * (5094064 / 20 : ℝ) * t * (1 - t) ^ 4 +
                10 * (2941438 / 20 : ℝ) * t ^ 2 * (1 - t) ^ 3 +
                10 * (1127811 / 20 : ℝ) * t ^ 3 * (1 - t) ^ 2 +
                5 * (1115462 / 20 : ℝ) * t ^ 4 * (1 - t) +
                (5496320 / 20 : ℝ) * t ^ 5 := by
          dsimp [t]
          ring
        rw [hbern]
        exact bernstein_degree5_lower_bound ht0 ht1
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · have hthree' : 3 / 4 ≤ c := le_of_not_ge hthree
        let t : ℝ := 4 * c - 3
        have ht0 : 0 ≤ t := by
          dsimp [t]
          linarith
        have ht1 : t ≤ 1 := by
          dsimp [t]
          linarith [hcl.2]
        have hbern :
            19200000 * c ^ 5 + 297600 * c ^ 4 - 25951072 * c ^ 3 +
                11531168 * c ^ 2 - 660 * c + 86725 =
              (5496320 / 20 : ℝ) * (1 - t) ^ 5 +
                5 * (9877178 / 20 : ℝ) * t * (1 - t) ^ 4 +
                10 * (18651243 / 20 : ℝ) * t ^ 2 * (1 - t) ^ 3 +
                10 * (34410444 / 20 : ℝ) * t ^ 3 * (1 - t) ^ 2 +
                5 * (60876360 / 20 : ℝ) * t ^ 4 * (1 - t) +
                (103275220 / 20 : ℝ) * t ^ 5 := by
          dsimp [t]
          ring
        rw [hbern]
        exact bernstein_degree5_lower_bound ht0 ht1
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem HB_CENTRAL_W_POSITIVITY {c : ℝ} (hc : |c| ≤ 1) :
    (557731 / 62500000 : ℝ) ≤ frequencyW qStar aStar bStar c := by
  have hP := central_polynomial_lower_on_unit_interval hc
  have hW :
      frequencyW qStar aStar bStar c =
        (19200000 * c ^ 5 + 297600 * c ^ 4 - 25951072 * c ^ 3 +
          11531168 * c ^ 2 - 660 * c + 86725) / 6250000 := by
    unfold frequencyW frequencyS frequencyJ frequencyK frequencyA qStar aStar bStar
    ring_nf
  rw [hW]
  nlinarith [hP]

private theorem hb_box_parameter_ranges {q a b : ℝ} (hbox : HB_Box q a b) :
    (99 / 10000 : ℝ) < q ∧ q < (11 / 1000 : ℝ) ∧
      (9 / 4 : ℝ) < a ∧ a < (23 / 10 : ℝ) ∧
      (59 / 100 : ℝ) < b ∧ b < (61 / 100 : ℝ) := by
  unfold HB_Box at hbox
  rcases hbox with ⟨hqbox, habox, hbbox⟩
  have hq := abs_le.mp hqbox
  have ha := abs_le.mp habox
  have hb := abs_le.mp hbbox
  exact ⟨by nlinarith [hq.1], by nlinarith [hq.2],
    by nlinarith [ha.1], by nlinarith [ha.2],
    by nlinarith [hb.1], by nlinarith [hb.2]⟩

private theorem frequencySK_unit_interval_bounds {c : ℝ} (hc : |c| ≤ 1) :
    |frequencyS c| ≤ 4 ∧ |frequencyK c| ≤ 6 := by
  have hcl := abs_le.mp hc
  have hc2 : c ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (c - 1), sq_nonneg (c + 1)]
  have hprod0 : 0 ≤ c ^ 2 * (1 + c) :=
    mul_nonneg (sq_nonneg c) (by linarith)
  have hprod2 : c ^ 2 * (1 + c) ≤ 2 := by
    calc
      c ^ 2 * (1 + c) ≤ 1 * (1 + c) := by
        exact mul_le_mul_of_nonneg_right hc2 (by linarith)
      _ ≤ 1 * 2 := by
        exact mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
      _ = 2 := by norm_num
  have h1 : |1 + c| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith
  have habs0 : 0 ≤ |c| := abs_nonneg c
  have habs_sq : |c| ^ 2 ≤ 1 := by
    have hmul : |c| * (1 - |c|) ≥ 0 :=
      mul_nonneg habs0 (sub_nonneg.mpr hc)
    nlinarith
  have habs_cube : |c| ^ 3 ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_right habs_sq habs0
    nlinarith [hc]
  have hlin : |(16 / 25 : ℝ) * c| ≤ 16 / 25 := by
    calc
      |(16 / 25 : ℝ) * c| = (16 / 25 : ℝ) * |c| := by
        rw [abs_mul]
        norm_num
      _ ≤ 16 / 25 := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hc (by norm_num : 0 ≤ (16 / 25 : ℝ)))
  have hcub : |(32 / 25 : ℝ) * c ^ 3| ≤ 32 / 25 := by
    calc
      |(32 / 25 : ℝ) * c ^ 3| =
          (32 / 25 : ℝ) * |c| ^ 3 := by
            rw [abs_mul, abs_pow]
            norm_num
      _ ≤ 32 / 25 := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left habs_cube (by norm_num : 0 ≤ (32 / 25 : ℝ)))
  have hinner :
      |1 + (16 / 25 : ℝ) * c - (32 / 25 : ℝ) * c ^ 3| ≤ 73 / 25 := by
    have htri :
        |1 + (16 / 25 : ℝ) * c - (32 / 25 : ℝ) * c ^ 3| ≤
          |1 + (16 / 25 : ℝ) * c| + |(32 / 25 : ℝ) * c ^ 3| := by
      simpa only [sub_zero, zero_sub, abs_neg, abs_zero, neg_neg] using
        (abs_sub_le (1 + (16 / 25 : ℝ) * c) 0
          ((32 / 25 : ℝ) * c ^ 3))
    calc
      |1 + (16 / 25 : ℝ) * c - (32 / 25 : ℝ) * c ^ 3| ≤
          |1 + (16 / 25 : ℝ) * c| + |(32 / 25 : ℝ) * c ^ 3| :=
        htri
      _ ≤ (|1| + |(16 / 25 : ℝ) * c|) + |(32 / 25 : ℝ) * c ^ 3| := by
        exact add_le_add (abs_add_le _ _) (le_refl _)
      _ ≤ 73 / 25 := by
        norm_num at hlin hcub ⊢
        linarith
  constructor
  · rw [abs_le]
    constructor
    · unfold frequencyS
      nlinarith
    · unfold frequencyS
      nlinarith
  · unfold frequencyK
    calc
      |(1 + c) * (1 + (16 / 25 : ℝ) * c - (32 / 25 : ℝ) * c ^ 3)| =
          |1 + c| * |1 + (16 / 25 : ℝ) * c - (32 / 25 : ℝ) * c ^ 3| := by
            rw [abs_mul]
      _ ≤ 2 * (73 / 25) := by gcongr
      _ ≤ 6 := by norm_num

private theorem frequencyA_box_perturbation_bound {q a b : ℝ} (hbox : HB_Box q a b) :
    |frequencyA q a b - frequencyA qStar aStar bStar| ≤ (4 / 100000 : ℝ) := by
  rcases hb_box_parameter_ranges hbox with ⟨hqlo, hqhi, halo, hahi, hblo, hbhi⟩
  have hqdiff : |q - qStar| ≤ (1 / 100000 : ℝ) := by
    simpa [qStar] using hbox.1
  have hadiff : |a - aStar| ≤ (1 / 100000 : ℝ) := by
    simpa [aStar] using hbox.2.1
  have hbdiff : |b - bStar| ≤ (1 / 100000 : ℝ) := by
    simpa [bStar] using hbox.2.2
  have h1mb_nonneg : 0 ≤ 1 - b := by linarith
  have h1mb_le : 1 - b ≤ 41 / 100 := by linarith
  have haq_nonneg : 0 ≤ a * (1 - b) :=
    mul_nonneg (by linarith) h1mb_nonneg
  have haq_le : a * (1 - b) ≤ 1 := by
    calc
      a * (1 - b) ≤ (23 / 10 : ℝ) * (1 - b) := by
        exact mul_le_mul_of_nonneg_right (le_of_lt hahi) h1mb_nonneg
      _ ≤ (23 / 10 : ℝ) * (41 / 100) := by
        exact mul_le_mul_of_nonneg_left h1mb_le (by norm_num)
      _ ≤ 1 := by norm_num
  have hqcoef_nonneg : 0 ≤ (1 - qStar) * (1 - b) := by
    exact mul_nonneg (by norm_num [qStar]) h1mb_nonneg
  have hqcoef_le : (1 - qStar) * (1 - b) ≤ 1 / 2 := by
    calc
      (1 - qStar) * (1 - b) ≤ (1 : ℝ) * (1 - b) := by
        exact mul_le_mul_of_nonneg_right (by norm_num [qStar]) h1mb_nonneg
      _ ≤ (1 : ℝ) * (41 / 100 : ℝ) := by
        exact mul_le_mul_of_nonneg_left h1mb_le (by norm_num)
      _ ≤ 1 / 2 := by norm_num
  have hbcoef_nonneg : 0 ≤ aStar * (1 - qStar) := by norm_num [aStar, qStar]
  have hbcoef_le : aStar * (1 - qStar) ≤ 5 / 2 := by norm_num [aStar, qStar]
  have htq : |a * (1 - b) * (q - qStar)| ≤ (1 / 100000 : ℝ) := by
    calc
      |a * (1 - b) * (q - qStar)| =
          (a * (1 - b)) * |q - qStar| := by
            rw [abs_mul, abs_of_nonneg haq_nonneg]
      _ ≤ 1 * (1 / 100000 : ℝ) := by
        exact mul_le_mul haq_le hqdiff (abs_nonneg _) (by norm_num)
      _ = (1 / 100000 : ℝ) := by ring
  have hta :
      |(1 - qStar) * (1 - b) * (a - aStar)| ≤ (1 / 200000 : ℝ) := by
    calc
      |(1 - qStar) * (1 - b) * (a - aStar)| =
          ((1 - qStar) * (1 - b)) * |a - aStar| := by
            rw [abs_mul, abs_of_nonneg hqcoef_nonneg]
      _ ≤ (1 / 2 : ℝ) * (1 / 100000 : ℝ) := by
        exact mul_le_mul hqcoef_le hadiff (abs_nonneg _) (by norm_num)
      _ = (1 / 200000 : ℝ) := by ring
  have htb :
      |aStar * (1 - qStar) * (bStar - b)| ≤ (5 / 2 : ℝ) * (1 / 100000 : ℝ) := by
    calc
      |aStar * (1 - qStar) * (bStar - b)| =
          (aStar * (1 - qStar)) * |bStar - b| := by
            rw [abs_mul, abs_of_nonneg hbcoef_nonneg]
      _ ≤ (5 / 2 : ℝ) * (1 / 100000 : ℝ) := by
        exact mul_le_mul hbcoef_le (by simpa [abs_sub_comm] using hbdiff)
          (abs_nonneg _) (by norm_num)
  have hdecomp :
      frequencyA q a b - frequencyA qStar aStar bStar =
        -(a * (1 - b) * (q - qStar)) +
          ((1 - qStar) * (1 - b) * (a - aStar)) +
            (aStar * (1 - qStar) * (bStar - b)) := by
    unfold frequencyA
    ring
  have htri :
      |-(a * (1 - b) * (q - qStar)) +
          ((1 - qStar) * (1 - b) * (a - aStar)) +
            (aStar * (1 - qStar) * (bStar - b))| ≤
        |a * (1 - b) * (q - qStar)| +
          |(1 - qStar) * (1 - b) * (a - aStar)| +
            |aStar * (1 - qStar) * (bStar - b)| := by
    calc
      |-(a * (1 - b) * (q - qStar)) +
          ((1 - qStar) * (1 - b) * (a - aStar)) +
            (aStar * (1 - qStar) * (bStar - b))| ≤
          |-(a * (1 - b) * (q - qStar)) +
              ((1 - qStar) * (1 - b) * (a - aStar))| +
            |aStar * (1 - qStar) * (bStar - b)| := abs_add_le _ _
      _ ≤
          (|-(a * (1 - b) * (q - qStar))| +
              |(1 - qStar) * (1 - b) * (a - aStar)|) +
            |aStar * (1 - qStar) * (bStar - b)| := by
        exact add_le_add (abs_add_le _ _) (le_refl _)
      _ = |a * (1 - b) * (q - qStar)| +
          |(1 - qStar) * (1 - b) * (a - aStar)| +
            |aStar * (1 - qStar) * (bStar - b)| := by
        rw [abs_neg]
  rw [hdecomp]
  calc
    |-(a * (1 - b) * (q - qStar)) +
        ((1 - qStar) * (1 - b) * (a - aStar)) +
          (aStar * (1 - qStar) * (bStar - b))| ≤
        |a * (1 - b) * (q - qStar)| +
          |(1 - qStar) * (1 - b) * (a - aStar)| +
            |aStar * (1 - qStar) * (bStar - b)| := htri
    _ ≤ (4 / 100000 : ℝ) := by
      nlinarith [htq, hta, htb]

private theorem frequencyJ_box_perturbation_bound {q a b c : ℝ}
    (hbox : HB_Box q a b) (hc : |c| ≤ 1) :
    |frequencyJ q a b c - frequencyJ qStar aStar bStar c| ≤
      (35 / 100000 : ℝ) := by
  rcases hb_box_parameter_ranges hbox with ⟨hqlo, hqhi, halo, hahi, hblo, hbhi⟩
  have hcl := abs_le.mp hc
  have hqdiff : |q - qStar| ≤ (1 / 100000 : ℝ) := by
    simpa [qStar] using hbox.1
  have hadiff : |a - aStar| ≤ (1 / 100000 : ℝ) := by
    simpa [aStar] using hbox.2.1
  have hbdiff : |b - bStar| ≤ (1 / 100000 : ℝ) := by
    simpa [bStar] using hbox.2.2
  have h1mc_nonneg : 0 ≤ 1 - c := by linarith
  have h1mc_le : 1 - c ≤ 2 := by linarith
  have h1pb_nonneg : 0 ≤ 1 + b := by linarith
  have ha_nonneg : 0 ≤ a := by linarith
  have ha2_le : a ^ 2 ≤ (23 / 10 : ℝ) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left (le_of_lt hahi) ha_nonneg
    have hmul' := mul_le_mul_of_nonneg_right (le_of_lt hahi) (by norm_num : 0 ≤ (23 / 10 : ℝ))
    nlinarith
  have hqprod_nonneg : 0 ≤ a * (1 + b) * (1 - c) :=
    mul_nonneg (mul_nonneg ha_nonneg h1pb_nonneg) h1mc_nonneg
  have hqprod_le :
      a * (1 + b) * (1 - c) ≤
        (23 / 10 : ℝ) * (161 / 100 : ℝ) * 2 := by
    calc
      a * (1 + b) * (1 - c) ≤
          (23 / 10 : ℝ) * (1 + b) * (1 - c) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_of_lt hahi) h1pb_nonneg) h1mc_nonneg
      _ ≤ (23 / 10 : ℝ) * (161 / 100 : ℝ) * (1 - c) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith [hbhi]) (by norm_num : 0 ≤ (23 / 10 : ℝ)))
          h1mc_nonneg
      _ ≤ (23 / 10 : ℝ) * (161 / 100 : ℝ) * 2 := by
        exact mul_le_mul_of_nonneg_left h1mc_le (by norm_num)
  have hqcoef :
      |a ^ 2 - a * (1 + b) * (1 - c)| ≤ (13 : ℝ) := by
    have htri :
        |a ^ 2 - a * (1 + b) * (1 - c)| ≤
          |a ^ 2| + |a * (1 + b) * (1 - c)| := by
      simpa only [sub_zero, zero_sub, abs_neg, abs_zero, neg_neg] using
        (abs_sub_le (a ^ 2) 0 (a * (1 + b) * (1 - c)))
    calc
      |a ^ 2 - a * (1 + b) * (1 - c)| ≤
          |a ^ 2| + |a * (1 + b) * (1 - c)| := htri
      _ = a ^ 2 + a * (1 + b) * (1 - c) := by
        rw [abs_of_nonneg (sq_nonneg a), abs_of_nonneg hqprod_nonneg]
      _ ≤ (23 / 10 : ℝ) ^ 2 +
          (23 / 10 : ℝ) * (161 / 100 : ℝ) * 2 := by
        exact add_le_add ha2_le hqprod_le
      _ ≤ 13 := by norm_num
  have hP_nonneg : 0 ≤ (1 + qStar) * (1 + b) * (1 - c) := by
    exact mul_nonneg (mul_nonneg (by norm_num [qStar]) h1pb_nonneg) h1mc_nonneg
  have hP_le :
      (1 + qStar) * (1 + b) * (1 - c) ≤
        (101 / 100 : ℝ) * (161 / 100 : ℝ) * 2 := by
    calc
      (1 + qStar) * (1 + b) * (1 - c) ≤
          (101 / 100 : ℝ) * (1 + b) * (1 - c) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by norm_num [qStar]) h1pb_nonneg) h1mc_nonneg
      _ ≤ (101 / 100 : ℝ) * (161 / 100 : ℝ) * (1 - c) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith [hbhi]) (by norm_num : 0 ≤ (101 / 100 : ℝ)))
          h1mc_nonneg
      _ ≤ (101 / 100 : ℝ) * (161 / 100 : ℝ) * 2 := by
        exact mul_le_mul_of_nonneg_left h1mc_le (by norm_num)
  have hQ_nonneg : 0 ≤ qStar * (a + aStar) := by
    exact mul_nonneg (by norm_num [qStar]) (by norm_num [aStar]; linarith [halo])
  have haastar_le : a + aStar ≤ (456 / 100 : ℝ) := by
    norm_num [aStar]
    linarith [hahi]
  have hQ_le : qStar * (a + aStar) ≤ (1 / 100 : ℝ) * (456 / 100 : ℝ) := by
    calc
      qStar * (a + aStar) ≤ (1 / 100 : ℝ) * (a + aStar) := by
        exact mul_le_mul_of_nonneg_right (by norm_num [qStar])
          (by norm_num [aStar]; linarith [halo])
      _ ≤ (1 / 100 : ℝ) * (456 / 100 : ℝ) := by
        exact mul_le_mul_of_nonneg_left haastar_le
          (by norm_num)
  have hacoef :
      |qStar * (a + aStar) - (1 + qStar) * (1 + b) * (1 - c)| ≤
        (4 : ℝ) := by
    have htri :
        |qStar * (a + aStar) - (1 + qStar) * (1 + b) * (1 - c)| ≤
          |qStar * (a + aStar)| + |(1 + qStar) * (1 + b) * (1 - c)| := by
      simpa only [sub_zero, zero_sub, abs_neg, abs_zero, neg_neg] using
        (abs_sub_le (qStar * (a + aStar)) 0
          ((1 + qStar) * (1 + b) * (1 - c)))
    calc
      |qStar * (a + aStar) - (1 + qStar) * (1 + b) * (1 - c)| ≤
          |qStar * (a + aStar)| + |(1 + qStar) * (1 + b) * (1 - c)| := htri
      _ = qStar * (a + aStar) + (1 + qStar) * (1 + b) * (1 - c) := by
        rw [abs_of_nonneg hQ_nonneg, abs_of_nonneg hP_nonneg]
      _ ≤ (1 / 100 : ℝ) * (456 / 100 : ℝ) +
          (101 / 100 : ℝ) * (161 / 100 : ℝ) * 2 := by
        exact add_le_add hQ_le hP_le
      _ ≤ 4 := by norm_num
  have hbb_nonneg : 0 ≤ b + bStar := by
    norm_num [bStar]
    linarith [hblo]
  have hbb_le : b + bStar ≤ (121 / 100 : ℝ) := by
    norm_num [bStar]
    linarith [hbhi]
  have hbc_abs :
      |b + bStar - 2 * c| ≤ (321 / 100 : ℝ) := by
    have htri :
        |b + bStar - 2 * c| ≤ |b + bStar| + |2 * c| := by
      simpa only [sub_zero, zero_sub, abs_neg, abs_zero, neg_neg] using
        (abs_sub_le (b + bStar) 0 (2 * c))
    have hcabs : |c| ≤ 1 := hc
    calc
      |b + bStar - 2 * c| ≤ |b + bStar| + |2 * c| := htri
      _ = (b + bStar) + 2 * |c| := by
        rw [abs_of_nonneg hbb_nonneg, abs_mul]
        norm_num
      _ ≤ (121 / 100 : ℝ) + 2 * 1 := by
        exact add_le_add hbb_le (mul_le_mul_of_nonneg_left hcabs (by norm_num))
      _ = (321 / 100 : ℝ) := by norm_num
  have hfirst_nonneg : 0 ≤ 2 * (1 - c) * |b + bStar - 2 * c| :=
    mul_nonneg (mul_nonneg (by norm_num) h1mc_nonneg) (abs_nonneg _)
  have hfirst_le :
      2 * (1 - c) * |b + bStar - 2 * c| ≤
        4 * (321 / 100 : ℝ) := by
    calc
      2 * (1 - c) * |b + bStar - 2 * c| ≤
          2 * 2 * |b + bStar - 2 * c| := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h1mc_le (by norm_num)) (abs_nonneg _)
      _ ≤ 4 * (321 / 100 : ℝ) := by
        nlinarith [hbc_abs]
  have hsecond_nonneg :
      0 ≤ aStar * (1 + qStar) * (1 - c) := by
    exact mul_nonneg (mul_nonneg (by norm_num [aStar]) (by norm_num [qStar]))
      h1mc_nonneg
  have hsecond_le :
      aStar * (1 + qStar) * (1 - c) ≤
        (113 / 50 : ℝ) * (101 / 100 : ℝ) * 2 := by
    calc
      aStar * (1 + qStar) * (1 - c) =
          (113 / 50 : ℝ) * (101 / 100 : ℝ) * (1 - c) := by
            norm_num [aStar, qStar]
      _ ≤ (113 / 50 : ℝ) * (101 / 100 : ℝ) * 2 := by
        exact mul_le_mul_of_nonneg_left h1mc_le (by norm_num)
  have hbcoef :
      |2 * (1 - c) * (b + bStar - 2 * c) -
          aStar * (1 + qStar) * (1 - c)| ≤ (18 : ℝ) := by
    have hfirst_abs :
        |2 * (1 - c) * (b + bStar - 2 * c)| ≤
          2 * (1 - c) * |b + bStar - 2 * c| := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) h1mc_nonneg)]
    have htri :
        |2 * (1 - c) * (b + bStar - 2 * c) -
            aStar * (1 + qStar) * (1 - c)| ≤
          |2 * (1 - c) * (b + bStar - 2 * c)| +
            |aStar * (1 + qStar) * (1 - c)| := by
      simpa only [sub_zero, zero_sub, abs_neg, abs_zero, neg_neg] using
        (abs_sub_le (2 * (1 - c) * (b + bStar - 2 * c)) 0
          (aStar * (1 + qStar) * (1 - c)))
    calc
      |2 * (1 - c) * (b + bStar - 2 * c) -
          aStar * (1 + qStar) * (1 - c)| ≤
          |2 * (1 - c) * (b + bStar - 2 * c)| +
            |aStar * (1 + qStar) * (1 - c)| := htri
      _ ≤ 2 * (1 - c) * |b + bStar - 2 * c| +
          aStar * (1 + qStar) * (1 - c) := by
        exact add_le_add hfirst_abs (le_of_eq (abs_of_nonneg hsecond_nonneg))
      _ ≤ 4 * (321 / 100 : ℝ) +
          (113 / 50 : ℝ) * (101 / 100 : ℝ) * 2 := by
        exact add_le_add hfirst_le hsecond_le
      _ ≤ 18 := by norm_num
  have htq :
      |(q - qStar) * (a ^ 2 - a * (1 + b) * (1 - c))| ≤
        (13 / 100000 : ℝ) := by
    calc
      |(q - qStar) * (a ^ 2 - a * (1 + b) * (1 - c))| =
          |q - qStar| * |a ^ 2 - a * (1 + b) * (1 - c)| := by
            rw [abs_mul]
      _ ≤ (1 / 100000 : ℝ) * 13 := by
        exact mul_le_mul hqdiff hqcoef (abs_nonneg _) (by norm_num)
      _ = (13 / 100000 : ℝ) := by norm_num
  have hta :
      |(a - aStar) *
          (qStar * (a + aStar) - (1 + qStar) * (1 + b) * (1 - c))| ≤
        (4 / 100000 : ℝ) := by
    calc
      |(a - aStar) *
          (qStar * (a + aStar) - (1 + qStar) * (1 + b) * (1 - c))| =
          |a - aStar| *
            |qStar * (a + aStar) - (1 + qStar) * (1 + b) * (1 - c)| := by
              rw [abs_mul]
      _ ≤ (1 / 100000 : ℝ) * 4 := by
        exact mul_le_mul hadiff hacoef (abs_nonneg _) (by norm_num)
      _ = (4 / 100000 : ℝ) := by norm_num
  have htb :
      |(b - bStar) *
          (2 * (1 - c) * (b + bStar - 2 * c) -
            aStar * (1 + qStar) * (1 - c))| ≤
        (18 / 100000 : ℝ) := by
    calc
      |(b - bStar) *
          (2 * (1 - c) * (b + bStar - 2 * c) -
            aStar * (1 + qStar) * (1 - c))| =
          |b - bStar| *
            |2 * (1 - c) * (b + bStar - 2 * c) -
              aStar * (1 + qStar) * (1 - c)| := by
              rw [abs_mul]
      _ ≤ (1 / 100000 : ℝ) * 18 := by
        exact mul_le_mul hbdiff hbcoef (abs_nonneg _) (by norm_num)
      _ = (18 / 100000 : ℝ) := by norm_num
  have hdecomp :
      frequencyJ q a b c - frequencyJ qStar aStar bStar c =
        (q - qStar) * (a ^ 2 - a * (1 + b) * (1 - c)) +
          (a - aStar) *
            (qStar * (a + aStar) - (1 + qStar) * (1 + b) * (1 - c)) +
            (b - bStar) *
              (2 * (1 - c) * (b + bStar - 2 * c) -
                aStar * (1 + qStar) * (1 - c)) := by
    unfold frequencyJ
    ring
  have htri :
      |(q - qStar) * (a ^ 2 - a * (1 + b) * (1 - c)) +
          (a - aStar) *
            (qStar * (a + aStar) - (1 + qStar) * (1 + b) * (1 - c)) +
            (b - bStar) *
              (2 * (1 - c) * (b + bStar - 2 * c) -
                aStar * (1 + qStar) * (1 - c))| ≤
        |(q - qStar) * (a ^ 2 - a * (1 + b) * (1 - c))| +
          |(a - aStar) *
            (qStar * (a + aStar) - (1 + qStar) * (1 + b) * (1 - c))| +
          |(b - bStar) *
            (2 * (1 - c) * (b + bStar - 2 * c) -
              aStar * (1 + qStar) * (1 - c))| := by
    calc
      |(q - qStar) * (a ^ 2 - a * (1 + b) * (1 - c)) +
          (a - aStar) *
            (qStar * (a + aStar) - (1 + qStar) * (1 + b) * (1 - c)) +
            (b - bStar) *
              (2 * (1 - c) * (b + bStar - 2 * c) -
                aStar * (1 + qStar) * (1 - c))| ≤
          |(q - qStar) * (a ^ 2 - a * (1 + b) * (1 - c)) +
              (a - aStar) *
                (qStar * (a + aStar) - (1 + qStar) * (1 + b) * (1 - c))| +
            |(b - bStar) *
              (2 * (1 - c) * (b + bStar - 2 * c) -
                aStar * (1 + qStar) * (1 - c))| := abs_add_le _ _
      _ ≤
          (|(q - qStar) * (a ^ 2 - a * (1 + b) * (1 - c))| +
              |(a - aStar) *
                (qStar * (a + aStar) - (1 + qStar) * (1 + b) * (1 - c))|) +
            |(b - bStar) *
              (2 * (1 - c) * (b + bStar - 2 * c) -
                aStar * (1 + qStar) * (1 - c))| := by
        exact add_le_add (abs_add_le _ _) (le_refl _)
      _ = |(q - qStar) * (a ^ 2 - a * (1 + b) * (1 - c))| +
          |(a - aStar) *
            (qStar * (a + aStar) - (1 + qStar) * (1 + b) * (1 - c))| +
          |(b - bStar) *
            (2 * (1 - c) * (b + bStar - 2 * c) -
              aStar * (1 + qStar) * (1 - c))| := by ring
  rw [hdecomp]
  calc
    |(q - qStar) * (a ^ 2 - a * (1 + b) * (1 - c)) +
        (a - aStar) *
          (qStar * (a + aStar) - (1 + qStar) * (1 + b) * (1 - c)) +
          (b - bStar) *
            (2 * (1 - c) * (b + bStar - 2 * c) -
              aStar * (1 + qStar) * (1 - c))| ≤
        |(q - qStar) * (a ^ 2 - a * (1 + b) * (1 - c))| +
          |(a - aStar) *
            (qStar * (a + aStar) - (1 + qStar) * (1 + b) * (1 - c))| +
          |(b - bStar) *
            (2 * (1 - c) * (b + bStar - 2 * c) -
              aStar * (1 + qStar) * (1 - c))| := htri
    _ ≤ (35 / 100000 : ℝ) := by
      nlinarith [htq, hta, htb]

private theorem frequencyW_box_deviation_bound {q a b c : ℝ}
    (hbox : HB_Box q a b) (hc : |c| ≤ 1) :
    |frequencyW q a b c - frequencyW qStar aStar bStar c| ≤
      (41 / 25000 : ℝ) := by
  have hJ := frequencyJ_box_perturbation_bound hbox hc
  have hA := frequencyA_box_perturbation_bound hbox
  have hSK := frequencySK_unit_interval_bounds hc
  have hdecomp :
      frequencyW q a b c - frequencyW qStar aStar bStar c =
        frequencyS c * (frequencyJ q a b c - frequencyJ qStar aStar bStar c) +
          frequencyK c * (frequencyA q a b - frequencyA qStar aStar bStar) := by
    unfold frequencyW
    ring
  rw [hdecomp]
  have hS :
      |frequencyS c * (frequencyJ q a b c - frequencyJ qStar aStar bStar c)| ≤
        (4 : ℝ) * (35 / 100000 : ℝ) := by
    calc
      |frequencyS c * (frequencyJ q a b c - frequencyJ qStar aStar bStar c)| =
          |frequencyS c| *
            |frequencyJ q a b c - frequencyJ qStar aStar bStar c| := by
              rw [abs_mul]
      _ ≤ (4 : ℝ) * (35 / 100000 : ℝ) := by
        exact mul_le_mul hSK.1 hJ (abs_nonneg _) (by norm_num)
  have hK :
      |frequencyK c * (frequencyA q a b - frequencyA qStar aStar bStar)| ≤
        (6 : ℝ) * (4 / 100000 : ℝ) := by
    calc
      |frequencyK c * (frequencyA q a b - frequencyA qStar aStar bStar)| =
          |frequencyK c| * |frequencyA q a b - frequencyA qStar aStar bStar| := by
            rw [abs_mul]
      _ ≤ (6 : ℝ) * (4 / 100000 : ℝ) := by
        exact mul_le_mul hSK.2 hA (abs_nonneg _) (by norm_num)
  calc
    |frequencyS c * (frequencyJ q a b c - frequencyJ qStar aStar bStar c) +
        frequencyK c * (frequencyA q a b - frequencyA qStar aStar bStar)| ≤
        |frequencyS c * (frequencyJ q a b c - frequencyJ qStar aStar bStar c)| +
          |frequencyK c * (frequencyA q a b - frequencyA qStar aStar bStar)| := by
      exact abs_add_le _ _
    _ ≤ (41 / 25000 : ℝ) := by
      nlinarith [hS, hK]

theorem HB_BOX_W_MARGIN {q a b c : ℝ} (hbox : HB_Box q a b) (hc : |c| ≤ 1) :
    (3 / 500 : ℝ) < frequencyW q a b c := by
  have hcenter := HB_CENTRAL_W_POSITIVITY hc
  have hdev := frequencyW_box_deviation_bound hbox hc
  have hdev_lower :
      frequencyW qStar aStar bStar c - (41 / 25000 : ℝ) ≤ frequencyW q a b c := by
    have h := (abs_le.mp hdev).1
    linarith
  nlinarith [hcenter, hdev_lower]

theorem HB_FREQUENCY_W_def {q a b c : ℝ} :
    frequencyW q a b c =
      frequencyS c * frequencyJ q a b c + frequencyK c * frequencyA q a b := by
  rfl

private theorem box_cycle_weighted_mode_scalar
    {q a b : ℝ} (c s p t u v : ℝ)
    (hq1 : q < 1) (ha : a ≠ 0)
    (hsq : s ^ 2 = 1 - c ^ 2)
    (hp :
      p = 8 * c ^ 4 - 8 * c ^ 2 + 1)
    (ht :
      t = (8 * c ^ 3 - 4 * c) * s) :
    let A : ℝ := ((1 + b) / a) * (1 - c)
    let B : ℝ := ((1 - b) / a) * s
    let zr : ℝ := A * u + B * v
    let zi : ℝ := A * v - B * u
    let lag : ℝ → ℝ → ℝ :=
      fun lr li =>
        let dxr := lr * u - li * v - u
        let dxi := lr * v + li * u - v
        let dzr := lr * zr - li * zi - zr
        let dzi := lr * zi + li * zr - zi
        (zr * lr + zi * li) * u + (zi * lr - zr * li) * v -
            (zr * u + zi * v) +
          (dzr ^ 2 + dzi ^ 2 + q * (dxr ^ 2 + dxi ^ 2) -
              2 * q * (dzr * dxr + dzi * dxi)) /
            (2 * (1 - q))
    lag c (-s) + (4 / 25 : ℝ) * lag p t =
      (u ^ 2 + v ^ 2) *
        ((1 - c) * frequencyW q a b c /
          (a ^ 2 * (1 - q))) := by
  dsimp
  rw [hp, ht]
  have hs4 : s ^ 4 = (1 - c ^ 2) ^ 2 := by
    calc
      s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ = (1 - c ^ 2) ^ 2 := by rw [hsq]
  have hqne : 1 - q ≠ 0 := by linarith
  unfold frequencyW frequencyS frequencyJ frequencyK frequencyA
  field_simp [ha, hqne]
  set_option maxRecDepth 100000 in
    ring_nf
  rw [hs4, hsq]
  ring

set_option maxHeartbeats 2000000 in
private theorem box_cycle_weighted_mode_identity
    {K : ℕ} [NeZero K] (x z : Fin K → ℝ)
    (hq1 : q < 1) (ha : a ≠ 0)
    (htransfer :
      ∀ j : Fin K,
        hbCycleDftCoord (fun i => (z i : ℂ)) j =
          (((((1 + b) / a) *
                (1 - (ZMod.stdAddChar (ZMod.finEquiv K j)).re) : ℝ) : ℂ) -
            Complex.I *
              ((((1 - b) / a) *
                (ZMod.stdAddChar (ZMod.finEquiv K j)).im : ℝ) : ℂ)) *
            hbCycleDftCoord (fun i => (x i : ℂ)) j) :
    (∑ i : Fin K,
        (z i * (x (cycleFinShift (K - 1) i) - x i) +
          ((z (cycleFinShift (K - 1) i) - z i) ^ 2 +
              q * (x (cycleFinShift (K - 1) i) - x i) ^ 2 -
              2 * q *
                (z (cycleFinShift (K - 1) i) - z i) *
                (x (cycleFinShift (K - 1) i) - x i)) /
            (2 * (1 - q))) +
      (4 / 25 : ℝ) *
        ∑ i : Fin K,
          (z i * (x (cycleFinShift 4 i) - x i) +
            ((z (cycleFinShift 4 i) - z i) ^ 2 +
                q * (x (cycleFinShift 4 i) - x i) ^ 2 -
                2 * q *
                  (z (cycleFinShift 4 i) - z i) *
                  (x (cycleFinShift 4 i) - x i)) /
              (2 * (1 - q))) =
      ∑ j : Fin K,
        Complex.normSq (hbCycleDftCoord (fun i => (x i : ℂ)) j) *
          ((1 - (ZMod.stdAddChar (ZMod.finEquiv K j)).re) *
              frequencyW q a b (ZMod.stdAddChar (ZMod.finEquiv K j)).re /
            ((K : ℝ) * a ^ 2 * (1 - q)))) := by
  have hreal_sum (f : Fin K → ℂ) :
      Complex.re ((K : ℂ)⁻¹ * ∑ j : Fin K, f j) =
        ∑ j : Fin K, Complex.re ((K : ℂ)⁻¹ * f j) := by
    classical
    rw [Finset.mul_sum]
    induction (Finset.univ : Finset (Fin K)) using Finset.induction_on with
    | empty =>
        simp
    | @insert j s hjs ih =>
        simp only [Finset.sum_insert hjs, Complex.add_re, ih]
  have hsplit (n : ℕ) :
      (∑ i : Fin K,
          (z i * (x (cycleFinShift n i) - x i) +
            ((z (cycleFinShift n i) - z i) ^ 2 +
                q * (x (cycleFinShift n i) - x i) ^ 2 -
                2 * q *
                  (z (cycleFinShift n i) - z i) *
                  (x (cycleFinShift n i) - x i)) /
              (2 * (1 - q)))) =
        ∑ i : Fin K, z i * (x (cycleFinShift n i) - x i) +
          (∑ i : Fin K, (z (cycleFinShift n i) - z i) ^ 2 +
              q * ∑ i : Fin K, (x (cycleFinShift n i) - x i) ^ 2 -
              2 * q *
                ∑ i : Fin K,
                  (z (cycleFinShift n i) - z i) *
                    (x (cycleFinShift n i) - x i)) /
            (2 * (1 - q)) := by
    rw [Finset.sum_add_distrib, ← Finset.sum_div]
    congr 1
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have hq :
        ∑ i : Fin K, q * (x (cycleFinShift n i) - x i) ^ 2 =
          q * ∑ i : Fin K, (x (cycleFinShift n i) - x i) ^ 2 := by
      rw [← Finset.mul_sum]
    have hcross :
        ∑ i : Fin K,
            2 * q * (z (cycleFinShift n i) - z i) *
                (x (cycleFinShift n i) - x i) =
          2 * q *
            ∑ i : Fin K,
              (z (cycleFinShift n i) - z i) *
                (x (cycleFinShift n i) - x i) := by
      calc
        ∑ i : Fin K,
              2 * q * (z (cycleFinShift n i) - z i) *
                (x (cycleFinShift n i) - x i) =
            ∑ i : Fin K,
              (2 * q) *
                ((z (cycleFinShift n i) - z i) *
                  (x (cycleFinShift n i) - x i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = 2 * q *
            ∑ i : Fin K,
              (z (cycleFinShift n i) - z i) *
                (x (cycleFinShift n i) - x i) := by
          rw [Finset.mul_sum]
    rw [hq, hcross]
  have hsum_rearrange
      (A B C D E F G H : Fin K → ℝ) :
      (∑ j : Fin K, A j) +
          ((∑ j : Fin K, B j) + q * (∑ j : Fin K, C j) -
              2 * q * (∑ j : Fin K, D j)) /
            (2 * (1 - q)) +
        (4 / 25 : ℝ) *
          ((∑ j : Fin K, E j) +
            (((∑ j : Fin K, F j) + q * (∑ j : Fin K, G j) -
                2 * q * (∑ j : Fin K, H j)) /
              (2 * (1 - q)))) =
        ∑ j : Fin K,
          ((A j +
              (B j + q * C j - 2 * q * D j) /
                (2 * (1 - q))) +
            (4 / 25 : ℝ) *
              (E j + (F j + q * G j - 2 * q * H j) /
                (2 * (1 - q)))) := by
    have hquot (B C D : Fin K → ℝ) :
        ((∑ j : Fin K, B j) + q * (∑ j : Fin K, C j) -
              2 * q * (∑ j : Fin K, D j)) /
            (2 * (1 - q)) =
          ∑ j : Fin K,
            (B j + q * C j - 2 * q * D j) /
              (2 * (1 - q)) := by
      have hnum :
          ((∑ j : Fin K, B j) + q * (∑ j : Fin K, C j) -
              2 * q * (∑ j : Fin K, D j)) =
            ∑ j : Fin K, (B j + q * C j - 2 * q * D j) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      rw [hnum, Finset.sum_div]
    rw [hquot B C D, hquot F G H]
    rw [← Finset.sum_add_distrib]
    rw [← Finset.sum_add_distrib]
    rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
  have hreal_combined
      (A B C D E F G H : Fin K → ℂ) :
      Complex.re ((K : ℂ)⁻¹ * ∑ j : Fin K, A j) +
          (Complex.re ((K : ℂ)⁻¹ * ∑ j : Fin K, B j) +
              q * Complex.re ((K : ℂ)⁻¹ * ∑ j : Fin K, C j) -
              2 * q * Complex.re ((K : ℂ)⁻¹ * ∑ j : Fin K, D j)) /
            (2 * (1 - q)) +
        (4 / 25 : ℝ) *
          (Complex.re ((K : ℂ)⁻¹ * ∑ j : Fin K, E j) +
            (Complex.re ((K : ℂ)⁻¹ * ∑ j : Fin K, F j) +
                q * Complex.re ((K : ℂ)⁻¹ * ∑ j : Fin K, G j) -
                2 * q * Complex.re ((K : ℂ)⁻¹ * ∑ j : Fin K, H j)) /
              (2 * (1 - q))) =
      ∑ j : Fin K,
        ((Complex.re ((K : ℂ)⁻¹ * A j) +
            (Complex.re ((K : ℂ)⁻¹ * B j) +
                q * Complex.re ((K : ℂ)⁻¹ * C j) -
                2 * q * Complex.re ((K : ℂ)⁻¹ * D j)) /
              (2 * (1 - q))) +
          (4 / 25 : ℝ) *
            (Complex.re ((K : ℂ)⁻¹ * E j) +
              (Complex.re ((K : ℂ)⁻¹ * F j) +
                  q * Complex.re ((K : ℂ)⁻¹ * G j) -
                  2 * q * Complex.re ((K : ℂ)⁻¹ * H j)) /
                (2 * (1 - q)))) := by
    rw [hreal_sum A, hreal_sum B, hreal_sum C, hreal_sum D,
      hreal_sum E, hreal_sum F, hreal_sum G, hreal_sum H]
    convert hsum_rearrange
      (fun j => Complex.re ((K : ℂ)⁻¹ * A j))
      (fun j => Complex.re ((K : ℂ)⁻¹ * B j))
      (fun j => Complex.re ((K : ℂ)⁻¹ * C j))
      (fun j => Complex.re ((K : ℂ)⁻¹ * D j))
      (fun j => Complex.re ((K : ℂ)⁻¹ * E j))
      (fun j => Complex.re ((K : ℂ)⁻¹ * F j))
      (fun j => Complex.re ((K : ℂ)⁻¹ * G j))
      (fun j => Complex.re ((K : ℂ)⁻¹ * H j)) using 1
  have hinnerPrev :=
    hb_cycle_real_inner_lag_parseval z x (K - 1)
  have hinnerFour :=
    hb_cycle_real_inner_lag_parseval z x 4
  have hnormZPrev :=
    hb_cycle_real_norm_lag_parseval z (K - 1)
  have hnormZFour :=
    hb_cycle_real_norm_lag_parseval z 4
  have hnormXPrev :=
    hb_cycle_real_norm_lag_parseval x (K - 1)
  have hnormXFour :=
    hb_cycle_real_norm_lag_parseval x 4
  have hcrossPrev :=
    hb_cycle_real_cross_diff_parseval z x (K - 1)
  have hcrossFour :=
    hb_cycle_real_cross_diff_parseval z x 4
  rw [hsplit (K - 1), hsplit 4]
  rw [hinnerPrev, hinnerFour, hnormZPrev, hnormZFour,
    hnormXPrev, hnormXFour, hcrossPrev, hcrossFour]
  have halphaFour (j : Fin K) :
      ZMod.stdAddChar (ZMod.finEquiv K j * ((4 : ℕ) : ZMod K)) =
        (ZMod.stdAddChar (ZMod.finEquiv K j)) ^ 4 := by
    have harg :
        ZMod.finEquiv K j * ((4 : ℕ) : ZMod K) =
          ZMod.finEquiv K j + ZMod.finEquiv K j +
            ZMod.finEquiv K j + ZMod.finEquiv K j := by ring
    rw [harg, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
      AddChar.map_add_eq_mul]
    ring
  have hcombined := hreal_combined
    (fun j : Fin K =>
      hbCycleDftCoord (fun i => (z i : ℂ)) j *
          starRingEnd ℂ (ZMod.stdAddChar
            (ZMod.finEquiv K j * ((K - 1 : ℕ) : ZMod K))) *
          starRingEnd ℂ (hbCycleDftCoord (fun i => (x i : ℂ)) j) -
        hbCycleDftCoord (fun i => (z i : ℂ)) j *
          starRingEnd ℂ (hbCycleDftCoord (fun i => (x i : ℂ)) j))
    (fun j : Fin K =>
      (ZMod.stdAddChar
          (ZMod.finEquiv K j * ((K - 1 : ℕ) : ZMod K)) *
          hbCycleDftCoord (fun i => (z i : ℂ)) j -
        hbCycleDftCoord (fun i => (z i : ℂ)) j) *
        starRingEnd ℂ
          (ZMod.stdAddChar
            (ZMod.finEquiv K j * ((K - 1 : ℕ) : ZMod K)) *
            hbCycleDftCoord (fun i => (z i : ℂ)) j -
          hbCycleDftCoord (fun i => (z i : ℂ)) j))
    (fun j : Fin K =>
      (ZMod.stdAddChar
          (ZMod.finEquiv K j * ((K - 1 : ℕ) : ZMod K)) *
          hbCycleDftCoord (fun i => (x i : ℂ)) j -
        hbCycleDftCoord (fun i => (x i : ℂ)) j) *
        starRingEnd ℂ
          (ZMod.stdAddChar
            (ZMod.finEquiv K j * ((K - 1 : ℕ) : ZMod K)) *
            hbCycleDftCoord (fun i => (x i : ℂ)) j -
          hbCycleDftCoord (fun i => (x i : ℂ)) j))
    (fun j : Fin K =>
      (ZMod.stdAddChar
          (ZMod.finEquiv K j * ((K - 1 : ℕ) : ZMod K)) *
          hbCycleDftCoord (fun i => (z i : ℂ)) j -
        hbCycleDftCoord (fun i => (z i : ℂ)) j) *
        starRingEnd ℂ
          (ZMod.stdAddChar
            (ZMod.finEquiv K j * ((K - 1 : ℕ) : ZMod K)) *
            hbCycleDftCoord (fun i => (x i : ℂ)) j -
          hbCycleDftCoord (fun i => (x i : ℂ)) j))
    (fun j : Fin K =>
      hbCycleDftCoord (fun i => (z i : ℂ)) j *
          starRingEnd ℂ (ZMod.stdAddChar
            (ZMod.finEquiv K j * ((4 : ℕ) : ZMod K))) *
          starRingEnd ℂ (hbCycleDftCoord (fun i => (x i : ℂ)) j) -
        hbCycleDftCoord (fun i => (z i : ℂ)) j *
          starRingEnd ℂ (hbCycleDftCoord (fun i => (x i : ℂ)) j))
    (fun j : Fin K =>
      (ZMod.stdAddChar
          (ZMod.finEquiv K j * ((4 : ℕ) : ZMod K)) *
          hbCycleDftCoord (fun i => (z i : ℂ)) j -
        hbCycleDftCoord (fun i => (z i : ℂ)) j) *
        starRingEnd ℂ
          (ZMod.stdAddChar
            (ZMod.finEquiv K j * ((4 : ℕ) : ZMod K)) *
            hbCycleDftCoord (fun i => (z i : ℂ)) j -
          hbCycleDftCoord (fun i => (z i : ℂ)) j))
    (fun j : Fin K =>
      (ZMod.stdAddChar
          (ZMod.finEquiv K j * ((4 : ℕ) : ZMod K)) *
          hbCycleDftCoord (fun i => (x i : ℂ)) j -
        hbCycleDftCoord (fun i => (x i : ℂ)) j) *
        starRingEnd ℂ
          (ZMod.stdAddChar
            (ZMod.finEquiv K j * ((4 : ℕ) : ZMod K)) *
            hbCycleDftCoord (fun i => (x i : ℂ)) j -
          hbCycleDftCoord (fun i => (x i : ℂ)) j))
    (fun j : Fin K =>
      (ZMod.stdAddChar
          (ZMod.finEquiv K j * ((4 : ℕ) : ZMod K)) *
          hbCycleDftCoord (fun i => (z i : ℂ)) j -
        hbCycleDftCoord (fun i => (z i : ℂ)) j) *
        starRingEnd ℂ
          (ZMod.stdAddChar
            (ZMod.finEquiv K j * ((4 : ℕ) : ZMod K)) *
            hbCycleDftCoord (fun i => (x i : ℂ)) j -
          hbCycleDftCoord (fun i => (x i : ℂ)) j))
  rw [hcombined]
  apply Finset.sum_congr rfl
  intro j hj
  have hz := htransfer j
  have hbridge := hb_cycle_dft_transfer_real_imag hz
  have hZre := hbridge.1
  have hZim := hbridge.2
  rw [hb_cycle_dft_prev_character, halphaFour j]
  simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im]
  rw [hZre, hZim]
  have hnorm :
      (ZMod.stdAddChar (ZMod.finEquiv K j)).re ^ 2 +
          (ZMod.stdAddChar (ZMod.finEquiv K j)).im ^ 2 = 1 := by
    have h := hb_cycle_stdAddChar_normSq
      (K := K) (ZMod.finEquiv K j)
    simpa [Complex.normSq_apply, pow_two] using h
  have hsq :
      (ZMod.stdAddChar (ZMod.finEquiv K j)).im ^ 2 =
        1 - (ZMod.stdAddChar (ZMod.finEquiv K j)).re ^ 2 := by
    nlinarith [hnorm]
  have hpow4_re :
      ((ZMod.stdAddChar (ZMod.finEquiv K j)) ^ 4).re =
        8 * (ZMod.stdAddChar (ZMod.finEquiv K j)).re ^ 4 -
          8 * (ZMod.stdAddChar (ZMod.finEquiv K j)).re ^ 2 + 1 := by
    simp [pow_succ, Complex.mul_re, Complex.mul_im]
    have hmul := congrArg
      (fun t : ℝ =>
        t * (ZMod.stdAddChar (ZMod.finEquiv K j)).re ^ 2) hsq
    have hmul2 := congrArg (fun t : ℝ => t ^ 2) hsq
    ring_nf at hmul hmul2 ⊢
    linarith [hmul, hmul2]
  have hpow4_im :
      ((ZMod.stdAddChar (ZMod.finEquiv K j)) ^ 4).im =
        (8 * (ZMod.stdAddChar (ZMod.finEquiv K j)).re ^ 3 -
          4 * (ZMod.stdAddChar (ZMod.finEquiv K j)).re) *
          (ZMod.stdAddChar (ZMod.finEquiv K j)).im := by
    simp [pow_succ, Complex.mul_re, Complex.mul_im]
    have hmul := congrArg
      (fun t : ℝ =>
        t * (ZMod.stdAddChar (ZMod.finEquiv K j)).re *
          (ZMod.stdAddChar (ZMod.finEquiv K j)).im) hsq
    ring_nf at hmul ⊢
    linarith [hmul]
  have hstar_re :
      (starRingEnd ℂ (ZMod.stdAddChar (ZMod.finEquiv K j))).re =
        (ZMod.stdAddChar (ZMod.finEquiv K j)).re := by
    simp [Complex.conj_re]
  have hstar_im :
      (starRingEnd ℂ (ZMod.stdAddChar (ZMod.finEquiv K j))).im =
        -(ZMod.stdAddChar (ZMod.finEquiv K j)).im := by
    simp [Complex.conj_im]
  have hpow4_star_re :
      (starRingEnd ℂ (ZMod.stdAddChar (ZMod.finEquiv K j)) ^ 4).re =
        8 * (ZMod.stdAddChar (ZMod.finEquiv K j)).re ^ 4 -
          8 * (ZMod.stdAddChar (ZMod.finEquiv K j)).re ^ 2 + 1 := by
    simp [pow_succ, Complex.mul_re, Complex.mul_im, hstar_re, hstar_im]
    have hmul := congrArg
      (fun t : ℝ =>
        t * (ZMod.stdAddChar (ZMod.finEquiv K j)).re ^ 2) hsq
    have hmul2 := congrArg (fun t : ℝ => t ^ 2) hsq
    ring_nf at hmul hmul2 ⊢
    linarith [hmul, hmul2]
  have hpow4_star_im :
      (starRingEnd ℂ (ZMod.stdAddChar (ZMod.finEquiv K j)) ^ 4).im =
        -((8 * (ZMod.stdAddChar (ZMod.finEquiv K j)).re ^ 3 -
            4 * (ZMod.stdAddChar (ZMod.finEquiv K j)).re) *
          (ZMod.stdAddChar (ZMod.finEquiv K j)).im) := by
    simp [pow_succ, Complex.mul_re, Complex.mul_im, hstar_re, hstar_im]
    have hmul := congrArg
      (fun t : ℝ =>
        t * (ZMod.stdAddChar (ZMod.finEquiv K j)).re *
          (ZMod.stdAddChar (ZMod.finEquiv K j)).im) hsq
    ring_nf at hmul ⊢
    linarith [hmul]
  simp [Complex.conj_re, Complex.conj_im, hpow4_re, hpow4_im,
    hstar_re, hstar_im, hpow4_star_re, hpow4_star_im]
  have hscalar :=
    box_cycle_weighted_mode_scalar
      (q := q) (a := a) (b := b)
      (ZMod.stdAddChar (ZMod.finEquiv K j)).re
      (ZMod.stdAddChar (ZMod.finEquiv K j)).im
      (8 * (ZMod.stdAddChar (ZMod.finEquiv K j)).re ^ 4 -
        8 * (ZMod.stdAddChar (ZMod.finEquiv K j)).re ^ 2 + 1)
      ((8 * (ZMod.stdAddChar (ZMod.finEquiv K j)).re ^ 3 -
          4 * (ZMod.stdAddChar (ZMod.finEquiv K j)).re) *
        (ZMod.stdAddChar (ZMod.finEquiv K j)).im)
      (hbCycleDftCoord (fun i => (x i : ℂ)) j).re
      (hbCycleDftCoord (fun i => (x i : ℂ)) j).im
      hq1 ha hsq (by rfl) (by rfl)
  have hscaled := congrArg
    (fun r : ℝ => (K : ℝ)⁻¹ * r) hscalar
  calc
    _ = (K : ℝ)⁻¹ *
        (((hbCycleDftCoord (fun i => (x i : ℂ)) j).re ^ 2 +
            (hbCycleDftCoord (fun i => (x i : ℂ)) j).im ^ 2) *
          ((1 - (ZMod.stdAddChar (ZMod.finEquiv K j)).re) *
            frequencyW q a b (ZMod.stdAddChar (ZMod.finEquiv K j)).re /
            (a ^ 2 * (1 - q)))) := by
      set_option maxRecDepth 100000 in
        convert hscaled using 1 <;> ring
    _ = _ := by
      have hK : (K : ℝ) ≠ 0 := by
        exact_mod_cast (NeZero.ne K)
      field_simp [hK]

private theorem frequency_t_factorization_and_pos {q a b c : ℝ}
    (hD : ParameterDomain q a b) (hc : |c| ≤ 1) :
    0 < frequencyT q a b c := by
  rcases hD with ⟨hq_pos, hq_lt, hb_nonneg, hb_lt, ha_pos, ha_lt⟩
  have hcr := abs_le.mp hc
  let r := frequencyR c
  have hr_nonneg : 0 ≤ r := by
    dsimp [r, frequencyR]
    linarith
  have hr_le_two : r ≤ 2 := by
    dsimp [r, frequencyR]
    linarith
  have hfactor :
      frequencyT q a b c =
        (a * q - (1 + b) * r) ^ 2 +
          (1 - b) ^ 2 * r * (2 - r) := by
    dsimp [frequencyT, r]
    ring
  rw [hfactor]
  by_cases hr_zero : r = 0
  · have haq_pos : 0 < a * q := mul_pos ha_pos hq_pos
    rw [hr_zero]
    nlinarith
  · have hr_pos : 0 < r := lt_of_le_of_ne hr_nonneg (Ne.symm hr_zero)
    by_cases hr_two : r = 2
    · have haq_lt : a * q < 2 * (1 + b) := by
        have haq_lt_a : a * q < a := by
          simpa using mul_lt_mul_of_pos_left hq_lt ha_pos
        exact lt_trans haq_lt_a ha_lt
      rw [hr_two]
      nlinarith
    · have htwo_sub_pos : 0 < 2 - r :=
        sub_pos.mpr (lt_of_le_of_ne hr_le_two hr_two)
      have h1mb_pos : 0 < 1 - b := sub_pos.mpr hb_lt
      have hprod_pos : 0 < (1 - b) ^ 2 * r * (2 - r) := by
        positivity
      nlinarith [sq_nonneg (a * q - (1 + b) * r)]

private theorem unit_circle_real_imag_square_relation {z : ℂ} {c : ℝ}
    (hz : ‖z‖ = 1) (hzc : z.re = c) :
    z.im ^ 2 = 1 - c ^ 2 := by
  have hnorm : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hz]
    norm_num
  rw [Complex.normSq_apply] at hnorm
  rw [hzc] at hnorm
  nlinarith

private theorem transfer_denominator_normSq_eq_frequency_t
    {q a b c : ℝ} {z : ℂ}
    (hz : ‖z‖ = 1) (hzc : z.re = c) :
    Complex.normSq (hbTransferDenominator q a b z) =
      frequencyT q a b c := by
  have himsq : z.im ^ 2 = 1 - c ^ 2 :=
    unit_circle_real_imag_square_relation hz hzc
  unfold hbTransferDenominator
  rw [Complex.normSq_apply]
  simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, pow_two]
  rw [hzc]
  dsimp [frequencyT, frequencyR]
  have himfour : z.im ^ 4 = (1 - c ^ 2) ^ 2 := by
    calc
      z.im ^ 4 = (z.im ^ 2) ^ 2 := by ring
      _ = (1 - c ^ 2) ^ 2 := by rw [himsq]
  ring_nf at ⊢
  rw [himsq, himfour]
  ring

private theorem frequency_scaled_realpart_algebra
    {q a b c : ℝ} {z : ℂ}
    (hD : ParameterDomain q a b) (hz : ‖z‖ = 1) (hzc : z.re = c) :
    frequencyT q a b c *
        Complex.re
          (hbMultiplier z *
            (((hbL0 q : ℝ) : ℂ) * hbTransferUnitCircle q a b hD z hz - 1)) =
      hbMultiplierEpsilon * frequencyD q a b c -
        frequencyR c * frequencyS c * frequencyJ q a b c -
          frequencyR c * frequencyK c * frequencyA q a b := by
  have hdomain : hbTransferDomain q a b z :=
    hbTransferDomain_of_unit_norm hD hz
  have hden_ne : hbTransferDenominator q a b z ≠ 0 := hdomain
  have hnorm_den :
      Complex.normSq (hbTransferDenominator q a b z) =
        frequencyT q a b c :=
    transfer_denominator_normSq_eq_frequency_t hz hzc
  have hnum :
      (((hbL0 q : ℝ) : ℂ) * hbTransferUnitCircle q a b hD z hz - 1) =
        (-(((hbL0 q : ℝ) : ℂ) * ((a : ℂ) * z)) -
            hbTransferDenominator q a b z) /
          hbTransferDenominator q a b z := by
    rw [hbTransferUnitCircle, hbTransferFunction_eq]
    change
      (((hbL0 q : ℝ) : ℂ) * (-((a : ℂ) * z) /
          hbTransferDenominator q a b z) - 1) =
        (-(((hbL0 q : ℝ) : ℂ) * ((a : ℂ) * z)) -
            hbTransferDenominator q a b z) /
          hbTransferDenominator q a b z
    field_simp [hden_ne]
  rw [hnum, ← mul_div_assoc, Complex.div_re, hnorm_den]
  have hnorm_z : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hz]
    norm_num
  have hnorm_z' : z.re ^ 2 + z.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using hnorm_z
  have hc : |c| ≤ 1 := by
    rw [← hzc]
    rw [abs_le]
    constructor <;> nlinarith [hnorm_z', sq_nonneg z.im]
  have hT : 0 < frequencyT q a b c :=
    frequency_t_factorization_and_pos hD hc
  field_simp [ne_of_gt hT]
  have himsq : z.im ^ 2 = 1 - c ^ 2 :=
    unit_circle_real_imag_square_relation hz hzc
  have himfour : z.im ^ 4 = (1 - c ^ 2) ^ 2 := by
    calc
      z.im ^ 4 = (z.im ^ 2) ^ 2 := by ring
      _ = (1 - c ^ 2) ^ 2 := by rw [himsq]
  have himsix : z.im ^ 6 = (1 - c ^ 2) ^ 3 := by
    calc
      z.im ^ 6 = (z.im ^ 2) ^ 3 := by ring
      _ = (1 - c ^ 2) ^ 3 := by rw [himsq]
  have himeight : z.im ^ 8 = (1 - c ^ 2) ^ 4 := by
    calc
      z.im ^ 8 = (z.im ^ 2) ^ 4 := by ring
      _ = (1 - c ^ 2) ^ 4 := by rw [himsq]
  simp [hbMultiplier, hbTransferDenominator, hbL0, Complex.mul_re,
    Complex.mul_im, Complex.inv_re, Complex.inv_im, hnorm_z, hzc,
    pow_succ, frequencyD, frequencyR, frequencyS, frequencyJ, frequencyK,
    frequencyA]
  ring_nf at ⊢
  rw [himsq, himfour, himsix, himeight]
  ring

theorem HB_FREQUENCY_NUMERATOR_ALGEBRA {q a b c : ℝ}
    (hD : ParameterDomain q a b) (hc : |c| ≤ 1) :
    let r := frequencyR c
    frequencyNumerator q a b c =
        hbMultiplierEpsilon * frequencyD q a b c -
          r * frequencyS c * frequencyJ q a b c -
            r * frequencyK c * frequencyA q a b ∧
      0 < frequencyT q a b c ∧
      (∀ z : ℂ,
        (hz : ‖z‖ = 1) →
          z.re = c →
            Complex.re
              (hbMultiplier z *
                (((hbL0 q : ℝ) : ℂ) * hbTransferUnitCircle q a b hD z hz - 1)) =
              frequencyNumerator q a b c / frequencyT q a b c) := by
  dsimp
  have hfirst :
      frequencyNumerator q a b c =
        hbMultiplierEpsilon * frequencyD q a b c -
          frequencyR c * frequencyS c * frequencyJ q a b c -
            frequencyR c * frequencyK c * frequencyA q a b := by
    unfold frequencyNumerator frequencyW
    ring
  constructor
  · exact hfirst
  constructor
  · exact frequency_t_factorization_and_pos hD hc
  · intro z hz hzc
    have hT : 0 < frequencyT q a b c :=
      frequency_t_factorization_and_pos hD hc
    have hscaled := frequency_scaled_realpart_algebra hD hz hzc
    rw [hfirst]
    apply (eq_div_iff (ne_of_gt hT)).2
    simpa [mul_comm] using hscaled

theorem HB_BOX_ENDPOINT_RANGES {q a b : ℝ} (hbox : HB_Box q a b) :
    (99 / 10000 : ℝ) < q ∧ q < (11 / 1000 : ℝ) ∧
      (9 / 4 : ℝ) < a ∧ a < (23 / 10 : ℝ) ∧
      (59 / 100 : ℝ) < b ∧ b < (61 / 100 : ℝ) ∧
      a * (1 + q) * (1 + b) < 4 ∧
      (1 / 20 : ℝ) < a ^ 2 * q ∧
      a ^ 2 * q ^ 2 < (1 / 1000 : ℝ) ∧
      2 * (1 - b) ^ 2 + 8 * b < 6 := by
  unfold HB_Box at hbox
  rcases hbox with ⟨hqbox, habox, hbbox⟩
  have hq := abs_le.mp hqbox
  have ha := abs_le.mp habox
  have hb := abs_le.mp hbbox
  have hq_low : (99 / 10000 : ℝ) < q := by nlinarith [hq.1]
  have hq_high : q < (11 / 1000 : ℝ) := by nlinarith [hq.2]
  have ha_low : (9 / 4 : ℝ) < a := by nlinarith [ha.1]
  have ha_high : a < (23 / 10 : ℝ) := by nlinarith [ha.2]
  have hb_low : (59 / 100 : ℝ) < b := by nlinarith [hb.1]
  have hb_high : b < (61 / 100 : ℝ) := by nlinarith [hb.2]
  refine ⟨hq_low, hq_high, ha_low, ha_high, hb_low, hb_high, ?_, ?_, ?_, ?_⟩
  · calc
      a * (1 + q) * (1 + b) <
          (23 / 10 : ℝ) * (1 + 11 / 1000) * (1 + 61 / 100) := by
        gcongr
      _ < 4 := by norm_num
  · nlinarith [ha_low, hq_low, ha_high, hq_high]
  · calc
      a ^ 2 * q ^ 2 < ((23 / 10 : ℝ) ^ 2) * ((11 / 1000 : ℝ) ^ 2) := by
        gcongr
      _ < (1 / 1000 : ℝ) := by norm_num
  · nlinarith [hb_low, hb_high]

theorem HB_BOX_CYCLE_FOURIER_EXCLUSION {q a b : ℝ} (hbox : HB_Box q a b) :
    ¬ HB_Cycle q a b := by
  rintro ⟨hD, d, hd, hf, K, hK, xMinusOne, xZero, hperiod, t, hneq⟩
  letI : NeZero K := ⟨by omega⟩
  let y : Fin K → Vec d :=
    fun i => hbIterate a b hf xMinusOne xZero i.val
  let g : Fin K → Vec d :=
    fun i => gradient hf.f (y i)
  let F : Fin K → ℝ :=
    fun i => hf.f (y i)
  have hq0 : 0 < q := parameterDomain_q_pos hD
  have hq1 : q < 1 := parameterDomain_q_lt_one hD
  have ha_pos : 0 < a := hD.2.2.2.2.1
  have ha : a ≠ 0 := ne_of_gt ha_pos
  have hlag (n : ℕ) :
      ∑ i : Fin K,
          (inner ℝ (g i) (y (cycleFinShift n i) - y i) +
            (‖g (cycleFinShift n i) - g i‖ ^ 2 +
                q * ‖y (cycleFinShift n i) - y i‖ ^ 2 -
                2 * q *
                  inner ℝ (g (cycleFinShift n i) - g i)
                    (y (cycleFinShift n i) - y i)) /
              (2 * (1 - q))) ≤ 0 := by
    apply box_cycle_lag_sum_nonpositive (d := d) (K := K)
      hq0 hq1 (by omega) y g F (cycleFinShift n) (cycleFinShift_bijective n)
    intro i
    exact hb_interpolation_shifted_cocoercive hq0 hq1 hf
      (y (cycleFinShift n i)) (y i)
  have hlagMinusOne := hlag (K - 1)
  have hlagFour := hlag 4
  have hpred :
      xMinusOne = hbIterate a b hf xMinusOne xZero (K - 1) := by
    have hrec0 :=
      hbIterate_succ_eq_successor a b hf xMinusOne xZero 0
    have hrecK :=
      hbIterate_succ_eq_successor a b hf xMinusOne xZero K
    have hp0 := hperiod 0
    have hp1 := hperiod 1
    have hrec0' :
        hbIterate a b hf xMinusOne xZero 1 =
          hbSuccessor a b hf xMinusOne xZero := by
      simpa [hbIterate_zero] using hrec0
    have hrecK' :
        hbIterate a b hf xMinusOne xZero (K + 1) =
          hbSuccessor a b hf
            (hbIterate a b hf xMinusOne xZero (K - 1))
            (hbIterate a b hf xMinusOne xZero K) := by
      simpa [show K ≠ 0 by omega] using hrecK
    have hp0' :
        hbIterate a b hf xMinusOne xZero K = xZero := by
      simpa [hbIterate_zero] using hp0
    have hp1' :
        hbIterate a b hf xMinusOne xZero (K + 1) =
          hbIterate a b hf xMinusOne xZero 1 := by
      simpa [Nat.add_comm] using hp1
    have hbpos : 0 < b := by
      nlinarith [(HB_BOX_ENDPOINT_RANGES hbox).2.2.2.2.1]
    apply hbSuccessor_left_injective a b hf (ne_of_gt hbpos)
    calc
      hbSuccessor a b hf xMinusOne xZero =
          hbIterate a b hf xMinusOne xZero 1 := hrec0'.symm
      _ = hbIterate a b hf xMinusOne xZero (K + 1) := hp1'.symm
      _ = hbSuccessor a b hf
          (hbIterate a b hf xMinusOne xZero (K - 1))
          (hbIterate a b hf xMinusOne xZero K) := hrecK'
      _ = hbSuccessor a b hf
          (hbIterate a b hf xMinusOne xZero (K - 1)) xZero := by
        rw [hp0']
  have hcyclicRecurrence :
      ∀ i : Fin K,
        y (cycleFinShift 1 i) =
          hbSuccessor a b hf
            (y (cycleFinShift (K - 1) i)) (y i) := by
    intro i
    dsimp [y]
    exact hb_cycle_recurrence a b hf xMinusOne xZero hK
      hperiod hpred i
  have hcyclicRecurrence_expanded :
      ∀ i : Fin K,
        y (cycleFinShift 1 i) =
          (1 + b) • y i -
            b • y (cycleFinShift (K - 1) i) -
            a • g i := by
    intro i
    have h := hcyclicRecurrence i
    simpa [hbSuccessor, g] using h
  have htransfer (j : Fin K) (r : Fin d) :
      hbCycleDftCoord (fun i => ((g i).ofLp r : ℂ)) j =
        (((1 + (b : ℂ)) - ZMod.stdAddChar (ZMod.finEquiv K j) -
            (b : ℂ) * ZMod.stdAddChar
              (ZMod.finEquiv K j * ((K - 1 : ℕ) : ZMod K))) /
          (a : ℂ)) *
          hbCycleDftCoord (fun i => ((y i).ofLp r : ℂ)) j := by
    apply hb_cycle_dft_scalar_recurrence_transfer
      (a := (a : ℂ)) (b := (b : ℂ))
      (Y := fun i => ((y i).ofLp r : ℂ))
      (G := fun i => ((g i).ofLp r : ℂ))
    · intro i
      have h :=
        congrArg (fun v : Vec d => (v.ofLp r : ℂ))
          (hcyclicRecurrence_expanded i)
      simpa [PiLp.smul_apply] using h
    · exact_mod_cast ha
  have htransfer_uv (j : Fin K) (r : Fin d) :
      hbCycleDftCoord (fun i => ((g i).ofLp r : ℂ)) j =
        (((((1 + b) / a) *
              (1 - (ZMod.stdAddChar (ZMod.finEquiv K j)).re) : ℝ) : ℂ) -
          Complex.I *
            ((((1 - b) / a) *
              (ZMod.stdAddChar (ZMod.finEquiv K j)).im : ℝ) : ℂ)) *
          hbCycleDftCoord (fun i => ((y i).ofLp r : ℂ)) j := by
    have h := htransfer j r
    rw [hb_cycle_dft_prev_character] at h
    have hcoeff :
        (((1 + (b : ℂ)) - ZMod.stdAddChar (ZMod.finEquiv K j) -
            (b : ℂ) *
              starRingEnd ℂ (ZMod.stdAddChar (ZMod.finEquiv K j))) /
          (a : ℂ)) =
          (((((1 + b) / a) *
                (1 - (ZMod.stdAddChar (ZMod.finEquiv K j)).re) : ℝ) : ℂ) -
            Complex.I *
              ((((1 - b) / a) *
                (ZMod.stdAddChar (ZMod.finEquiv K j)).im : ℝ) : ℂ)) := by
      apply Complex.ext <;>
        simp [Complex.div_re, Complex.div_im, Complex.mul_re,
          Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.add_re,
          Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]
      · field_simp [ha]
        ring
      · field_simp [ha]
        ring
    rw [hcoeff] at h
    exact h
  have hinner_coord (u v : Vec d) :
      inner ℝ u v = ∑ r : Fin d, (u.ofLp r) * (v.ofLp r) := by
    rw [PiLp.inner_apply]
    simp [PiLp.toLp_apply, real_inner_eq_re_inner, mul_comm]
  have hnorm_coord (u : Vec d) :
      ‖u‖ ^ 2 = ∑ r : Fin d, (u.ofLp r) ^ 2 := by
    simpa [PiLp.toLp_apply] using EuclideanSpace.real_norm_sq_eq u
  have hlag_coord (n : ℕ) :
      (∑ i : Fin K,
          (inner ℝ (g i) (y (cycleFinShift n i) - y i) +
            (‖g (cycleFinShift n i) - g i‖ ^ 2 +
                q * ‖y (cycleFinShift n i) - y i‖ ^ 2 -
                2 * q *
                  inner ℝ (g (cycleFinShift n i) - g i)
                    (y (cycleFinShift n i) - y i)) /
              (2 * (1 - q)))) =
        ∑ r : Fin d, ∑ i : Fin K,
          ((g i).ofLp r *
              ((y (cycleFinShift n i)).ofLp r - (y i).ofLp r) +
            (((g (cycleFinShift n i)).ofLp r - (g i).ofLp r) ^ 2 +
                q *
                  ((y (cycleFinShift n i)).ofLp r - (y i).ofLp r) ^ 2 -
                2 * q *
                  ((g (cycleFinShift n i)).ofLp r - (g i).ofLp r) *
                    ((y (cycleFinShift n i)).ofLp r - (y i).ofLp r)) /
              (2 * (1 - q))) := by
    calc
      _ = ∑ i : Fin K, ∑ r : Fin d,
          ((g i).ofLp r *
              ((y (cycleFinShift n i)).ofLp r - (y i).ofLp r) +
            (((g (cycleFinShift n i)).ofLp r - (g i).ofLp r) ^ 2 +
                q *
                  ((y (cycleFinShift n i)).ofLp r - (y i).ofLp r) ^ 2 -
                2 * q *
                  ((g (cycleFinShift n i)).ofLp r - (g i).ofLp r) *
                    ((y (cycleFinShift n i)).ofLp r - (y i).ofLp r)) /
              (2 * (1 - q))) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi1 := hinner_coord (g i)
          (y (cycleFinShift n i) - y i)
        have hn1 := hnorm_coord (g (cycleFinShift n i) - g i)
        have hn2 := hnorm_coord (y (cycleFinShift n i) - y i)
        have hi2 := hinner_coord
          (g (cycleFinShift n i) - g i)
          (y (cycleFinShift n i) - y i)
        rw [hi1, hn1, hn2, hi2]
        simp only [WithLp.ofLp_sub, PiLp.toLp_apply]
        have hfrac :
            (∑ r : Fin d,
                ((g (cycleFinShift n i)).ofLp - (g i).ofLp) r ^ 2 +
              q *
                ∑ r : Fin d,
                  ((y (cycleFinShift n i)).ofLp - (y i).ofLp) r ^ 2 -
              2 * q *
                ∑ r : Fin d,
                  ((g (cycleFinShift n i)).ofLp - (g i).ofLp) r *
                    ((y (cycleFinShift n i)).ofLp - (y i).ofLp) r) /
              (2 * (1 - q)) =
            ∑ r : Fin d,
              (((g (cycleFinShift n i)).ofLp - (g i).ofLp) r ^ 2 +
                  q *
                    ((y (cycleFinShift n i)).ofLp - (y i).ofLp) r ^ 2 -
                  2 * q *
                    ((g (cycleFinShift n i)).ofLp - (g i).ofLp) r *
                    ((y (cycleFinShift n i)).ofLp - (y i).ofLp) r) /
                (2 * (1 - q)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro r hr
          ring_nf
        rw [hfrac, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro r hr
        simp only [Pi.sub_apply]
      _ = ∑ r : Fin d, ∑ i : Fin K,
          ((g i).ofLp r *
              ((y (cycleFinShift n i)).ofLp r - (y i).ofLp r) +
            (((g (cycleFinShift n i)).ofLp r - (g i).ofLp r) ^ 2 +
                q *
                  ((y (cycleFinShift n i)).ofLp r - (y i).ofLp r) ^ 2 -
                2 * q *
                  ((g (cycleFinShift n i)).ofLp r - (g i).ofLp r) *
                    ((y (cycleFinShift n i)).ofLp r - (y i).ofLp r)) /
              (2 * (1 - q))) := by
        rw [Finset.sum_comm]
  let lagCoord (r : Fin d) (n : ℕ) : ℝ :=
    ∑ i : Fin K,
      ((g i).ofLp r *
          ((y (cycleFinShift n i)).ofLp r - (y i).ofLp r) +
        (((g (cycleFinShift n i)).ofLp r - (g i).ofLp r) ^ 2 +
              q * ((y (cycleFinShift n i)).ofLp r - (y i).ofLp r) ^ 2 -
            2 * q * ((g (cycleFinShift n i)).ofLp r - (g i).ofLp r) *
              ((y (cycleFinShift n i)).ofLp r - (y i).ofLp r)) /
          (2 * (1 - q)))
  have hcoord_scalar (r : Fin d) :
      lagCoord r (K - 1) + (4 / 25 : ℝ) * lagCoord r 4 =
        ∑ j : Fin K,
          Complex.normSq
              (hbCycleDftCoord (fun i => ((y i).ofLp r : ℂ)) j) *
            ((1 - (ZMod.stdAddChar (ZMod.finEquiv K j)).re) *
                frequencyW q a b (ZMod.stdAddChar (ZMod.finEquiv K j)).re /
              ((K : ℝ) * a ^ 2 * (1 - q))) := by
    dsimp [lagCoord]
    simpa using
      box_cycle_weighted_mode_identity
        (q := q) (a := a) (b := b)
        (x := fun i => (y i).ofLp r)
        (z := fun i => (g i).ofLp r)
        hq1 ha (htransfer := fun j => htransfer_uv j r)
  have hcoord_prev_le :
      ∑ r : Fin d, lagCoord r (K - 1) ≤ 0 := by
    have h := hlagMinusOne
    rw [hlag_coord (K - 1)] at h
    simpa [lagCoord] using h
  have hcoord_four_le :
      ∑ r : Fin d, lagCoord r 4 ≤ 0 := by
    have h := hlagFour
    rw [hlag_coord 4] at h
    simpa [lagCoord] using h
  have hcoord_combined_le :
      (∑ r : Fin d, lagCoord r (K - 1)) +
          (4 / 25 : ℝ) * ∑ r : Fin d, lagCoord r 4 ≤ 0 := by
    linarith
  have hmode_eq :
      (∑ r : Fin d, lagCoord r (K - 1)) +
          (4 / 25 : ℝ) * ∑ r : Fin d, lagCoord r 4 =
        ∑ j : Fin K,
          (∑ r : Fin d,
            Complex.normSq
              (hbCycleDftCoord (fun i => ((y i).ofLp r : ℂ)) j)) *
            ((1 - (ZMod.stdAddChar (ZMod.finEquiv K j)).re) *
                frequencyW q a b (ZMod.stdAddChar (ZMod.finEquiv K j)).re /
              ((K : ℝ) * a ^ 2 * (1 - q))) := by
    calc
      _ = ∑ r : Fin d, (lagCoord r (K - 1) +
          (4 / 25 : ℝ) * lagCoord r 4) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      _ = ∑ r : Fin d, ∑ j : Fin K,
          Complex.normSq
              (hbCycleDftCoord (fun i => ((y i).ofLp r : ℂ)) j) *
            ((1 - (ZMod.stdAddChar (ZMod.finEquiv K j)).re) *
                frequencyW q a b (ZMod.stdAddChar (ZMod.finEquiv K j)).re /
              ((K : ℝ) * a ^ 2 * (1 - q))) := by
        apply Finset.sum_congr rfl
        intro r hr
        exact hcoord_scalar r
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        rw [← Finset.sum_mul]
  let modeEnergy : Fin K → ℝ := fun j =>
    ∑ r : Fin d,
      Complex.normSq
        (hbCycleDftCoord (fun i => ((y i).ofLp r : ℂ)) j)
  let modeWeight : Fin K → ℝ := fun j =>
    ((1 - (ZMod.stdAddChar (ZMod.finEquiv K j)).re) *
        frequencyW q a b (ZMod.stdAddChar (ZMod.finEquiv K j)).re /
      ((K : ℝ) * a ^ 2 * (1 - q)))
  have hmode_le :
      ∑ j : Fin K, modeEnergy j * modeWeight j ≤ 0 := by
    change
      ∑ j : Fin K,
          (∑ r : Fin d,
            Complex.normSq
              (hbCycleDftCoord (fun i => ((y i).ofLp r : ℂ)) j)) *
            ((1 - (ZMod.stdAddChar (ZMod.finEquiv K j)).re) *
                frequencyW q a b (ZMod.stdAddChar (ZMod.finEquiv K j)).re /
              ((K : ℝ) * a ^ 2 * (1 - q))) ≤ 0
    rw [← hmode_eq]
    exact hcoord_combined_le
  have hmode_nonneg : ∀ j : Fin K, 0 ≤ modeEnergy j := by
    intro j
    dsimp [modeEnergy]
    exact Finset.sum_nonneg (fun r _ => Complex.normSq_nonneg _)
  have hweight_zero : modeWeight 0 = 0 := by
    dsimp [modeWeight]
    have hroot :
        ZMod.stdAddChar (ZMod.finEquiv K 0) = (1 : ℂ) :=
      (hb_cycle_root_eq_one_iff (K := K) 0).2 rfl
    rw [hroot]
    norm_num
  have hweight_pos : ∀ j : Fin K, j ≠ 0 → 0 < modeWeight j := by
    intro j hj
    let omega : ℂ := ZMod.stdAddChar (ZMod.finEquiv K j)
    have hnorm :
        omega.re ^ 2 + omega.im ^ 2 = 1 := by
      have h := hb_cycle_stdAddChar_normSq
        (K := K) (ZMod.finEquiv K j)
      simpa [omega, Complex.normSq_apply, pow_two] using h
    have hcos_le : omega.re ≤ 1 := by
      nlinarith [sq_nonneg omega.im]
    have hcos_ne : omega.re ≠ 1 := by
      intro hcos
      have him : omega.im = 0 := by
        nlinarith [sq_nonneg omega.im]
      have hroot : omega = (1 : ℂ) := by
        apply Complex.ext <;> simp [hcos, him]
      have : j = 0 := (hb_cycle_root_eq_one_iff (K := K) j).mp hroot
      exact hj this
    have hcos_lt : omega.re < 1 :=
      lt_of_le_of_ne hcos_le hcos_ne
    have habs : |omega.re| ≤ 1 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg omega.im]
    have hW : 0 < frequencyW q a b omega.re := by
      have h := HB_BOX_W_MARGIN hbox habs
      nlinarith
    have hden : 0 < (K : ℝ) * a ^ 2 * (1 - q) := by
      have hKpos : 0 < (K : ℝ) := by
        exact_mod_cast (show 0 < K by omega)
      have hq : 0 < 1 - q := sub_pos.mpr hq1
      exact mul_pos (mul_pos hKpos (sq_pos_of_pos ha_pos)) hq
    dsimp [modeWeight, omega]
    exact div_pos (mul_pos (sub_pos.mpr hcos_lt) hW) hden
  have hmode_zero :
      ∀ j : Fin K, j ≠ 0 → modeEnergy j = 0 :=
    weighted_nonpositive_sum_forces_nonzero_terms_zero
      (zero := (0 : Fin K)) modeEnergy modeWeight
      hmode_nonneg hweight_zero hweight_pos hmode_le
  have hzero_dft :
      ∀ j : Fin K, j ≠ 0 →
        ∀ r : Fin d,
          hbCycleDftCoord (fun i => ((y i).ofLp r : ℂ)) j = 0 := by
    intro j hj r
    have hsumzero : modeEnergy j = 0 := hmode_zero j hj
    have hle :
        Complex.normSq
            (hbCycleDftCoord (fun i => ((y i).ofLp r : ℂ)) j) ≤
          modeEnergy j := by
      dsimp [modeEnergy]
      exact Finset.single_le_sum
        (s := Finset.univ)
        (f := fun r' : Fin d =>
          Complex.normSq
            (hbCycleDftCoord (fun i => ((y i).ofLp r' : ℂ)) j))
        (by
          intro r' _hr'
          exact Complex.normSq_nonneg _)
        (Finset.mem_univ r)
    have hz :
        Complex.normSq
            (hbCycleDftCoord (fun i => ((y i).ofLp r : ℂ)) j) = 0 := by
      have hn :=
        Complex.normSq_nonneg
          (hbCycleDftCoord (fun i => ((y i).ofLp r : ℂ)) j)
      linarith
    exact Complex.normSq_eq_zero.mp hz
  have hconstant : ∀ i j : Fin K, y i = y j :=
    hb_cycle_constant_of_nonzero_dft_zero y hzero_dft
  have hiterate_mod (n : ℕ) :
      hbIterate a b hf xMinusOne xZero n =
        hbIterate a b hf xMinusOne xZero (n % K) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
        by_cases hn : n < K
        · rw [Nat.mod_eq_of_lt hn]
        · have hKn : K ≤ n := by omega
          have hsub : n - K < n := by omega
          have hmod_sub : (n - K) % K = n % K := by
            calc
              (n - K) % K = ((n - K) + K) % K := by
                simp [Nat.add_mod]
              _ = n % K := by rw [Nat.sub_add_cancel hKn]
          calc
            hbIterate a b hf xMinusOne xZero n =
                hbIterate a b hf xMinusOne xZero ((n - K) + K) := by
                  rw [Nat.sub_add_cancel hKn]
            _ = hbIterate a b hf xMinusOne xZero (n - K) :=
              hperiod (n - K)
            _ = hbIterate a b hf xMinusOne xZero ((n - K) % K) :=
              ih (n - K) hsub
            _ = hbIterate a b hf xMinusOne xZero (n % K) := by
              rw [hmod_sub]
  have hiterate_constant (n : ℕ) :
      hbIterate a b hf xMinusOne xZero n =
        hbIterate a b hf xMinusOne xZero 0 := by
    let i : Fin K := ⟨n % K, Nat.mod_lt _ (by omega)⟩
    calc
      hbIterate a b hf xMinusOne xZero n =
          hbIterate a b hf xMinusOne xZero (n % K) :=
        hiterate_mod n
      _ = y i := by
        rfl
      _ = y 0 := hconstant i 0
      _ = hbIterate a b hf xMinusOne xZero 0 := by
        rfl
  apply hneq
  calc
    hbIterate a b hf xMinusOne xZero (t + 1) =
        hbIterate a b hf xMinusOne xZero 0 :=
      hiterate_constant (t + 1)
    _ = hbIterate a b hf xMinusOne xZero t :=
      (hiterate_constant t).symm

theorem HB_DYNAMICS_LOOP_REPRESENTATION {q a b : ℝ}
    (hD : ParameterDomain q a b) :
    b < 1 ∧
      0 < a * q ∧ a * q < 2 * (1 + b) ∧
      (∀ z : {z : ℂ // hbTransferDomain q a b z},
        hbTransferFunction q a b z =
          -((a : ℂ) * (z : ℂ)) /
            ((z : ℂ) ^ 2 - ((1 + b - a * q : ℝ) : ℂ) * (z : ℂ) + (b : ℂ))) ∧
      (∀ z : ℂ, ‖z‖ = 1 → hbTransferDomain q a b z) ∧
      hbTransferStrictlyCausal q a b ∧
      hbPlantPolesInsideUnitDisk q a b ∧
      (∀ {d : ℕ} (hf : AdmissibleObjective q d) (xMinusOne xZero : Vec d),
        hbLoopRepresentation (parameterDomain_q_pos hD) a b hf xMinusOne xZero) := by
  rcases hD with ⟨hq0, hq1, hb0, hb1, ha0, ha_upper⟩
  have hD' : ParameterDomain q a b := ⟨hq0, hq1, hb0, hb1, ha0, ha_upper⟩
  have haq_pos : 0 < a * q := mul_pos ha0 hq0
  have haq_lt_a : a * q < a := by
    simpa using (mul_lt_mul_of_pos_left hq1 ha0)
  have haq_lt : a * q < 2 * (1 + b) := lt_trans haq_lt_a ha_upper
  refine ⟨hb1, haq_pos, haq_lt, ?_, ?_, hbPlantResponse_strictlyCausal q a b, ?_⟩
  · intro z
    exact hbTransferFunction_eq q a b z
  · intro z hz
    exact hbTransferDomain_of_unit_norm hD' hz
  · refine ⟨hbPlantPolesInsideUnitDisk_of_parameterDomain hD', ?_⟩
    intro d hf xMinusOne xZero
    exact hbLoopRepresentation_generated (parameterDomain_q_pos hD') a b hf xMinusOne xZero

private theorem bilateral_l2_shift_and_inner_summability
    {d : ℕ} {u v : ℤ → Vec d} (hu : Summable (fun t : ℤ => ‖u t‖ ^ 2))
    (hv : Summable (fun t : ℤ => ‖v t‖ ^ 2)) (ell : ℤ) :
    Summable (fun t : ℤ => ‖u (t + ell)‖ ^ 2) ∧
      Summable (fun t : ℤ => ‖v (t + ell)‖ ^ 2) ∧
      Summable (fun t : ℤ => |inner ℝ (u t) (v (t + ell))|) := by
  have hu_shift : Summable (fun t : ℤ => ‖u (t + ell)‖ ^ 2) := by
    simpa [Function.comp_def, Equiv.coe_addRight] using
      (Equiv.addRight ell).summable_iff.mpr hu
  have hv_shift : Summable (fun t : ℤ => ‖v (t + ell)‖ ^ 2) := by
    simpa [Function.comp_def, Equiv.coe_addRight] using
      (Equiv.addRight ell).summable_iff.mpr hv
  have hmajorant :
      Summable (fun t : ℤ =>
        (‖u t‖ ^ 2 + ‖v (t + ell)‖ ^ 2) / 2) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (hu.add hv_shift).const_smul (1 / 2 : ℝ)
  have habs :
      Summable (fun t : ℤ => |inner ℝ (u t) (v (t + ell))|) :=
    Summable.of_nonneg_of_le
      (fun t => abs_nonneg _)
      (fun t => by
        have hinner :=
          abs_real_inner_le_norm (u t) (v (t + ell))
        nlinarith [sq_nonneg (‖u t‖ - ‖v (t + ell)‖)])
      hmajorant
  exact ⟨hu_shift, hv_shift, habs⟩

private theorem hb_centered_potential_bounds
    {q : ℝ} {d : ℕ} (hq0 : 0 < q)
    (hf : AdmissibleObjective q d) (u : Vec d) :
    0 ≤
        (hf.f (objectiveMinimizer hq0 hf + u) - hf.f (objectiveMinimizer hq0 hf)) -
          (q / 2) * ‖u‖ ^ 2 ∧
      (hf.f (objectiveMinimizer hq0 hf + u) - hf.f (objectiveMinimizer hq0 hf)) -
          (q / 2) * ‖u‖ ^ 2 ≤
        (hbL0 q / 2) * ‖u‖ ^ 2 := by
  let xStar := objectiveMinimizer hq0 hf
  have h := shifted_potential_support_and_upper hf (xStar + u) xStar
  have hgrad0 : gradient hf.f xStar = 0 := by
    simpa [xStar] using gradient_objectiveMinimizer_eq_zero hq0 hf
  have hdiff : xStar + u - xStar = u := by
    abel
  have hnorm : ‖xStar + u‖ ^ 2 - ‖xStar‖ ^ 2 =
      ‖u‖ ^ 2 + 2 * inner ℝ xStar u := by
    rw [norm_add_sq_real]
    ring
  have hinner :
      inner ℝ (gradient hf.f xStar - q • xStar) u =
        -(q * inner ℝ xStar u) := by
    rw [hgrad0, inner_sub_left, inner_zero_left, inner_smul_left]
    simp only [zero_sub]
    simpa [mul_comm]
  rw [hdiff] at h
  have hrewrite :
      (hf.f (xStar + u) - q / 2 * ‖xStar + u‖ ^ 2) -
          (hf.f xStar - q / 2 * ‖xStar‖ ^ 2) -
        inner ℝ (gradient hf.f xStar - q • xStar) u =
      (hf.f (xStar + u) - hf.f xStar) - (q / 2) * ‖u‖ ^ 2 := by
    nlinarith [hnorm, hinner]
  have hlow :
      0 ≤ (hf.f (xStar + u) - hf.f xStar) - (q / 2) * ‖u‖ ^ 2 := by
    rw [← hrewrite]
    exact h.1
  have hupper :
      (hf.f (xStar + u) - hf.f xStar) - (q / 2) * ‖u‖ ^ 2 ≤
        ((1 - q) / 2) * ‖u‖ ^ 2 := by
    rw [← hrewrite]
    exact h.2
  exact ⟨hlow, by simpa [hbL0] using hupper⟩

private theorem hb_centered_interpolation_shifted_cocoercive
    {q : ℝ} {d : ℕ} (hq0 : 0 < q) (hq1 : q < 1)
    (hf : AdmissibleObjective q d) (u v : Vec d) :
    (1 / (2 * (1 - q))) *
          ‖hbCenteredNonlinearity hq0 hf u -
            hbCenteredNonlinearity hq0 hf v‖ ^ 2 ≤
      ((hf.f (objectiveMinimizer hq0 hf + u) - hf.f (objectiveMinimizer hq0 hf)) -
          (q / 2) * ‖u‖ ^ 2) -
        ((hf.f (objectiveMinimizer hq0 hf + v) - hf.f (objectiveMinimizer hq0 hf)) -
          (q / 2) * ‖v‖ ^ 2) -
        inner ℝ (hbCenteredNonlinearity hq0 hf v) (u - v) := by
  let xStar := objectiveMinimizer hq0 hf
  have h := hb_interpolation_shifted_cocoercive hq0 hq1 hf
    (xStar + u) (xStar + v)
  have hnorm :
      ‖xStar + u‖ ^ 2 - ‖xStar + v‖ ^ 2 =
        ‖u‖ ^ 2 - ‖v‖ ^ 2 + 2 * inner ℝ xStar (u - v) := by
    rw [norm_add_sq_real, norm_add_sq_real]
    rw [inner_sub_right]
    ring
  have hgrad :
      (gradient hf.f (xStar + u) - q • (xStar + u)) -
          (gradient hf.f (xStar + v) - q • (xStar + v)) =
        hbCenteredNonlinearity hq0 hf u -
          hbCenteredNonlinearity hq0 hf v := by
    simp [hbCenteredNonlinearity, xStar, sub_eq_add_neg, add_smul,
      smul_add, add_assoc, add_left_comm, add_comm]
    abel
  have hinner :
      inner ℝ (gradient hf.f (xStar + v) - q • (xStar + v)) (u - v) =
        inner ℝ (hbCenteredNonlinearity hq0 hf v) (u - v) -
          q * inner ℝ xStar (u - v) := by
    have hvec :
        gradient hf.f (xStar + v) - q • (xStar + v) =
          hbCenteredNonlinearity hq0 hf v - q • xStar := by
      simp [hbCenteredNonlinearity, xStar, sub_eq_add_neg, smul_add]
      abel
    rw [hvec, inner_sub_left, inner_smul_left]
    simp [mul_comm]
  have hdiff : xStar + u - (xStar + v) = u - v := by
    abel
  rw [hgrad, hdiff, hinner] at h
  refine h.trans_eq ?_
  dsimp [xStar]
  nlinarith [hnorm]

set_option maxHeartbeats 2000000 in
private theorem hb_bilateral_lag_supply_nonnegative
    {q : ℝ} {d : ℕ} (hq0 : 0 < q) (hq1 : q < 1)
    (hf : AdmissibleObjective q d) (τ : ℝ)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (x : ℤ → Vec d) (hxs : Summable (fun t : ℤ => ‖x t‖ ^ 2))
    (ell : ℤ) :
    0 ≤ ∑' t : ℤ,
      inner ℝ (τ • hbCenteredNonlinearity hq0 hf (x t))
        (((hbL0 q) • x t - τ • hbCenteredNonlinearity hq0 hf (x t)) -
          ((hbL0 q) • x (t + ell) -
            τ • hbCenteredNonlinearity hq0 hf (x (t + ell)))) := by
  let D := fun t : ℤ => hbCenteredNonlinearity hq0 hf (x t)
  let p := fun t : ℤ => τ • D t
  let s := fun t : ℤ => hbL0 q • x t - p t
  let psi := fun y : Vec d =>
    (hf.f (objectiveMinimizer hq0 hf + y) - hf.f (objectiveMinimizer hq0 hf)) -
      (q / 2) * ‖y‖ ^ 2
  let phi := fun t : ℤ => hbL0 q * τ * psi (x t) - (1 / 2) * ‖p t‖ ^ 2
  have hL : 0 ≤ hbL0 q := by
    dsimp [hbL0]
    linarith
  have hDnorm : ∀ t : ℤ, ‖D t‖ ≤ hbL0 q * ‖x t‖ := by
    intro t
    exact hbCenteredNonlinearity_lipschitz_from_zero hq0 hf (x t)
  have hDsq : Summable (fun t : ℤ => ‖D t‖ ^ 2) := by
    have hmajorD : Summable (fun t : ℤ =>
        (hbL0 q) ^ 2 * ‖x t‖ ^ 2) := by
      have hscale := hxs.const_smul (hbL0 q ^ 2)
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hscale
    exact Summable.of_nonneg_of_le
      (fun t => sq_nonneg (‖D t‖))
      (fun t => by
        have hright : 0 ≤ hbL0 q * ‖x t‖ :=
          mul_nonneg hL (norm_nonneg _)
        simpa [mul_pow] using
          (sq_le_sq₀ (norm_nonneg _) hright).2 (hDnorm t))
      hmajorD
  have hp_sq : Summable (fun t : ℤ => ‖p t‖ ^ 2) := by
    have hscale := hDsq.const_smul (τ ^ 2)
    have hτabs : |τ| = τ := abs_of_nonneg hτ0
    simpa [p, norm_smul, Real.norm_eq_abs, sq_abs, hτabs, pow_two,
      mul_assoc, mul_left_comm, mul_comm] using hscale
  have hs_sq : Summable (fun t : ℤ => ‖s t‖ ^ 2) := by
    have hxscaled : Summable (fun t : ℤ =>
        2 * (hbL0 q) ^ 2 * ‖x t‖ ^ 2) := by
      have h := hxs.const_smul (2 * (hbL0 q) ^ 2)
      simpa [smul_eq_mul] using h
    have hpscaled : Summable (fun t : ℤ => 2 * ‖p t‖ ^ 2) := by
      have h := hp_sq.const_smul (2 : ℝ)
      simpa [smul_eq_mul] using h
    have hmajor : Summable (fun t : ℤ =>
        2 * (hbL0 q) ^ 2 * ‖x t‖ ^ 2 + 2 * ‖p t‖ ^ 2) :=
      hxscaled.add hpscaled
    apply Summable.of_nonneg_of_le (fun t => sq_nonneg (‖s t‖))
    · intro t
      have hnorm := SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq
        ((hbL0 q) • x t) (-p t)
      simpa [s, sub_eq_add_neg, norm_smul, Real.norm_eq_abs, sq_abs,
        pow_two, mul_assoc, mul_left_comm, mul_comm] using hnorm
    · have hL_abs : |hbL0 q| = hbL0 q := abs_of_nonneg hL
      simpa [hL_abs, pow_two, mul_assoc, mul_left_comm, mul_comm] using hmajor
  have hpsi : Summable (fun t : ℤ => psi (x t)) := by
    apply Summable.of_nonneg_of_le
      (fun t => (hb_centered_potential_bounds hq0 hf (x t)).1)
    · intro t
      exact (hb_centered_potential_bounds hq0 hf (x t)).2
    · have hscale := hxs.const_smul (hbL0 q / 2)
      simpa [psi, pow_two, mul_assoc, mul_left_comm, mul_comm] using hscale
  have hphi : Summable phi := by
    have hleft := hpsi.const_smul (hbL0 q * τ)
    have hright := hp_sq.const_smul (1 / 2 : ℝ)
    simpa [phi] using hleft.sub hright
  have hlag_abs :
      Summable (fun t : ℤ =>
        |inner ℝ (p t) (s (t + ell))|) := by
    exact (bilateral_l2_shift_and_inner_summability hp_sq hs_sq ell).2.2
  have hzero_abs :
      Summable (fun t : ℤ => |inner ℝ (p t) (s t)|) := by
    have h := (bilateral_l2_shift_and_inner_summability hp_sq hs_sq 0).2.2
    simpa using h
  have hlag :
      Summable (fun t : ℤ => inner ℝ (p t) (s (t + ell))) :=
    hlag_abs.of_abs
  have hzero :
      Summable (fun t : ℤ => inner ℝ (p t) (s t)) :=
    hzero_abs.of_abs
  have hdiff_s :
      Summable (fun t : ℤ =>
        inner ℝ (p t) (s (t + ell) - s t)) := by
    have hsub := hlag.sub hzero
    simpa [inner_sub_right] using hsub
  have hphi_shift :
      Summable (fun t : ℤ => phi (t + ell)) := by
    simpa [Function.comp_def, Equiv.coe_addRight] using
      (Equiv.addRight ell).summable_iff.mpr hphi
  have hphi_reindex :
      (∑' t : ℤ, phi (t + ell)) = ∑' t : ℤ, phi t := by
    simpa [Function.comp_def, Equiv.coe_addRight] using
      (Equiv.addRight ell).tsum_eq phi
  have hpoint :
      ∀ t : ℤ,
        inner ℝ (p t) (s (t + ell) - s t) ≤
          phi (t + ell) - phi t := by
    intro t
    have hcoco := hb_centered_interpolation_shifted_cocoercive
      hq0 hq1 hf (x (t + ell)) (x t)
    have hnonneg :
        0 ≤ τ * (1 - τ) / 2 *
          ‖D (t + ell) - D t‖ ^ 2 := by
      have hτcomp : 0 ≤ 1 - τ := sub_nonneg.mpr hτ1
      exact mul_nonneg
        (mul_nonneg (mul_nonneg hτ0 hτcomp) (by norm_num))
        (sq_nonneg _)
    have hidentity :
        (phi (t + ell) - phi t) -
            inner ℝ (p t) (s (t + ell) - s t) =
          τ * hbL0 q *
              (psi (x (t + ell)) - psi (x t) -
                inner ℝ (D t) (x (t + ell) - x t)) -
            (τ ^ 2 / 2) * ‖D (t + ell) - D t‖ ^ 2 := by
      have hτabs : |τ| = τ := abs_of_nonneg hτ0
      have hDcomm :
          inner ℝ (D (t + ell)) (D t) =
            inner ℝ (D t) (D (t + ell)) := by
        rw [real_inner_comm]
      dsimp [phi, p, s]
      rw [norm_sub_sq_real]
      simp [inner_smul_left, inner_smul_right, inner_sub_right,
        norm_sub_sq_real, norm_smul, Real.norm_eq_abs, sq_abs, hτabs,
        D, pow_two, mul_assoc, mul_left_comm, mul_comm]
      rw [hDcomm]
      ring
    have hLpos : 0 < hbL0 q := by
      dsimp [hbL0]
      linarith
    have hcoco' :
        1 / (2 * hbL0 q) * ‖D (t + ell) - D t‖ ^ 2 ≤
          psi (x (t + ell)) - psi (x t) -
            inner ℝ (D t) (x (t + ell) - x t) := by
      simpa [D, psi, hbL0] using hcoco
    have hscaled0 := mul_le_mul_of_nonneg_left hcoco'
      (mul_nonneg hτ0 hL)
    have hscaled :
        τ / 2 * ‖D (t + ell) - D t‖ ^ 2 ≤
          τ * hbL0 q *
            (psi (x (t + ell)) - psi (x t) -
              inner ℝ (D t) (x (t + ell) - x t)) := by
      calc
        τ / 2 * ‖D (t + ell) - D t‖ ^ 2 =
            τ * hbL0 q *
              (1 / (2 * hbL0 q) * ‖D (t + ell) - D t‖ ^ 2) := by
                field_simp [ne_of_gt hLpos]
        _ ≤ _ := hscaled0
    have hnonneg_diff :
        0 ≤ (phi (t + ell) - phi t) -
          inner ℝ (p t) (s (t + ell) - s t) := by
      rw [hidentity]
      nlinarith [hscaled, hnonneg]
    linarith
  have hsum := hdiff_s.tsum_le_tsum hpoint (hphi_shift.sub hphi)
  rw [Summable.tsum_sub hphi_shift hphi, hphi_reindex] at hsum
  have hforward_eq :
      (∑' t : ℤ, inner ℝ (p t) (s t - s (t + ell))) =
        - (∑' t : ℤ, inner ℝ (p t) (s (t + ell) - s t)) := by
    calc
      (∑' t : ℤ, inner ℝ (p t) (s t - s (t + ell))) =
          ∑' t : ℤ, -inner ℝ (p t) (s (t + ell) - s t) := by
            apply tsum_congr
            intro t
            simp only [inner_sub_right]
            ring
      _ = - (∑' t : ℤ, inner ℝ (p t) (s (t + ell) - s t)) := by
            rw [tsum_neg]
  have hforward_nonneg :
      0 ≤ ∑' t : ℤ, inner ℝ (p t) (s t - s (t + ell)) := by
    rw [hforward_eq]
    linarith
  simpa [p, s] using hforward_nonneg

set_option maxHeartbeats 2000000 in
private theorem hb_bilateral_zero_lag_supply_nonnegative
    {q : ℝ} {d : ℕ} (hq0 : 0 < q) (hq1 : q < 1)
    (hf : AdmissibleObjective q d) (τ : ℝ)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (x : ℤ → Vec d) (hxs : Summable (fun t : ℤ => ‖x t‖ ^ 2)) :
    0 ≤ ∑' t : ℤ,
      inner ℝ (τ • hbCenteredNonlinearity hq0 hf (x t))
        (hbL0 q • x t - τ • hbCenteredNonlinearity hq0 hf (x t)) := by
  let D := fun t : ℤ => hbCenteredNonlinearity hq0 hf (x t)
  let p := fun t : ℤ => τ • D t
  let s := fun t : ℤ => hbL0 q • x t - p t
  have hL : 0 ≤ hbL0 q := by
    dsimp [hbL0]
    linarith
  have hDnorm : ∀ t : ℤ, ‖D t‖ ≤ hbL0 q * ‖x t‖ := by
    intro t
    exact hbCenteredNonlinearity_lipschitz_from_zero hq0 hf (x t)
  have hDsq : Summable (fun t : ℤ => ‖D t‖ ^ 2) := by
    have hmajorD : Summable (fun t : ℤ =>
        (hbL0 q) ^ 2 * ‖x t‖ ^ 2) := by
      have hscale := hxs.const_smul (hbL0 q ^ 2)
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hscale
    exact Summable.of_nonneg_of_le
      (fun t => sq_nonneg (‖D t‖))
      (fun t => by
        have hright : 0 ≤ hbL0 q * ‖x t‖ :=
          mul_nonneg hL (norm_nonneg _)
        simpa [mul_pow] using
          (sq_le_sq₀ (norm_nonneg _) hright).2 (hDnorm t))
      hmajorD
  have hp_sq : Summable (fun t : ℤ => ‖p t‖ ^ 2) := by
    have hscale := hDsq.const_smul (τ ^ 2)
    have hτabs : |τ| = τ := abs_of_nonneg hτ0
    simpa [p, norm_smul, Real.norm_eq_abs, sq_abs, hτabs, pow_two,
      mul_assoc, mul_left_comm, mul_comm] using hscale
  have hs_sq : Summable (fun t : ℤ => ‖s t‖ ^ 2) := by
    have hxscaled : Summable (fun t : ℤ =>
        2 * (hbL0 q) ^ 2 * ‖x t‖ ^ 2) := by
      have h := hxs.const_smul (2 * (hbL0 q) ^ 2)
      simpa [smul_eq_mul] using h
    have hpscaled : Summable (fun t : ℤ => 2 * ‖p t‖ ^ 2) := by
      have h := hp_sq.const_smul (2 : ℝ)
      simpa [smul_eq_mul] using h
    have hmajor : Summable (fun t : ℤ =>
        2 * (hbL0 q) ^ 2 * ‖x t‖ ^ 2 + 2 * ‖p t‖ ^ 2) :=
      hxscaled.add hpscaled
    apply Summable.of_nonneg_of_le (fun t => sq_nonneg (‖s t‖))
    · intro t
      have hnorm := SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq
        ((hbL0 q) • x t) (-p t)
      simpa [s, sub_eq_add_neg, norm_smul, Real.norm_eq_abs, sq_abs,
        pow_two, mul_assoc, mul_left_comm, mul_comm] using hnorm
    · have hL_abs : |hbL0 q| = hbL0 q := abs_of_nonneg hL
      simpa [hL_abs, pow_two, mul_assoc, mul_left_comm, mul_comm] using hmajor
  have hzero_abs :
      Summable (fun t : ℤ => |inner ℝ (p t) (s t)|) := by
    have h := (bilateral_l2_shift_and_inner_summability hp_sq hs_sq 0).2.2
    simpa using h
  have hzero :
      Summable (fun t : ℤ => inner ℝ (p t) (s t)) :=
    hzero_abs.of_abs
  have hpoint : ∀ t : ℤ, 0 ≤ inner ℝ (p t) (s t) := by
    intro t
    let psi := fun y : Vec d =>
      (hf.f (objectiveMinimizer hq0 hf + y) - hf.f (objectiveMinimizer hq0 hf)) -
        (q / 2) * ‖y‖ ^ 2
    have hforward := hb_centered_interpolation_shifted_cocoercive
      hq0 hq1 hf (x t) 0
    have hreverse := hb_centered_interpolation_shifted_cocoercive
      hq0 hq1 hf 0 (x t)
    have hforward' :
        1 / (2 * (1 - q)) * ‖D t‖ ^ 2 ≤ psi (x t) := by
      simpa [D, psi, hbCenteredNonlinearity_zero hq0 hf, sub_eq_add_neg,
        inner_neg_right] using hforward
    have hreverse' :
        1 / (2 * (1 - q)) * ‖D t‖ ^ 2 ≤
          -psi (x t) + inner ℝ (D t) (x t) := by
      simpa [D, psi, hbCenteredNonlinearity_zero hq0 hf, sub_eq_add_neg,
        inner_neg_right] using hreverse
    have hden : 0 < 1 - q := sub_pos.mpr hq1
    have hsum := add_le_add hforward' hreverse'
    have hco0 :
        1 / (1 - q) * ‖D t‖ ^ 2 ≤ inner ℝ (D t) (x t) := by
      calc
        1 / (1 - q) * ‖D t‖ ^ 2 =
            (1 / (2 * (1 - q)) * ‖D t‖ ^ 2) +
              (1 / (2 * (1 - q)) * ‖D t‖ ^ 2) := by
                field_simp [ne_of_gt hden]
                ring
        _ ≤ psi (x t) + (-psi (x t) + inner ℝ (D t) (x t)) := hsum
        _ = inner ℝ (D t) (x t) := by ring
    have hco1 := mul_le_mul_of_nonneg_left hco0 (le_of_lt hden)
    have hco :
        ‖D t‖ ^ 2 ≤ hbL0 q * inner ℝ (D t) (x t) := by
      calc
        ‖D t‖ ^ 2 =
            (1 - q) * (1 / (1 - q) * ‖D t‖ ^ 2) := by
              field_simp [ne_of_gt hden]
        _ ≤ (1 - q) * inner ℝ (D t) (x t) := hco1
        _ = hbL0 q * inner ℝ (D t) (x t) := by simp [hbL0]
    have hinner :
        inner ℝ (p t) (s t) =
          τ * hbL0 q * inner ℝ (D t) (x t) -
            τ ^ 2 * ‖D t‖ ^ 2 := by
      simp only [p, s, inner_sub_right, real_inner_smul_left,
        real_inner_smul_right,
        real_inner_self_eq_norm_sq]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ0]
      ring
    have hgap : 0 ≤ hbL0 q * inner ℝ (D t) (x t) - ‖D t‖ ^ 2 :=
      sub_nonneg.mpr hco
    have hfirst :
        0 ≤ τ * (hbL0 q * inner ℝ (D t) (x t) - ‖D t‖ ^ 2) :=
      mul_nonneg hτ0 hgap
    have hsecond :
        0 ≤ τ * (1 - τ) * ‖D t‖ ^ 2 := by
      exact mul_nonneg
        (mul_nonneg hτ0 (sub_nonneg.mpr hτ1))
        (sq_nonneg _)
    rw [hinner]
    nlinarith [hfirst, hsecond]
  exact tsum_nonneg hpoint

set_option maxHeartbeats 2000000 in
private theorem hb_multiplier_time_domain_tsum_nonnegative_of_zero_and_lags
    {q : ℝ} {d : ℕ} (hq0 : 0 < q) (hq1 : q < 1)
    (hf : AdmissibleObjective q d) (τ : ℝ)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (x : ℤ → Vec d) (hxs : Summable (fun t : ℤ => ‖x t‖ ^ 2)) :
    0 ≤ ∑' t : ℤ,
      inner ℝ (τ • hbCenteredNonlinearity hq0 hf (x t))
        (hbMultiplierEpsilon •
            (hbL0 q • x t - τ • hbCenteredNonlinearity hq0 hf (x t)) +
          ((hbL0 q • x t - τ • hbCenteredNonlinearity hq0 hf (x t)) -
            (hbL0 q • x (t - 1) -
              τ • hbCenteredNonlinearity hq0 hf (x (t - 1)))) +
          (4 / 25 : ℝ) •
            ((hbL0 q • x t - τ • hbCenteredNonlinearity hq0 hf (x t)) -
              (hbL0 q • x (t + 4) -
                τ • hbCenteredNonlinearity hq0 hf (x (t + 4))))) := by
  let D := fun t : ℤ => hbCenteredNonlinearity hq0 hf (x t)
  let p := fun t : ℤ => τ • D t
  let s := fun t : ℤ => hbL0 q • x t - p t
  let A := fun t : ℤ => inner ℝ (p t) (s t)
  let B := fun t : ℤ => inner ℝ (p t) (s t - s (t + (-1)))
  let C := fun t : ℤ => inner ℝ (p t) (s t - s (t + 4))
  have hL : 0 ≤ hbL0 q := by
    dsimp [hbL0]
    linarith
  have hDnorm : ∀ t : ℤ, ‖D t‖ ≤ hbL0 q * ‖x t‖ := by
    intro t
    exact hbCenteredNonlinearity_lipschitz_from_zero hq0 hf (x t)
  have hDsq : Summable (fun t : ℤ => ‖D t‖ ^ 2) := by
    have hmajorD : Summable (fun t : ℤ =>
        (hbL0 q) ^ 2 * ‖x t‖ ^ 2) := by
      have hscale := hxs.const_smul (hbL0 q ^ 2)
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hscale
    exact Summable.of_nonneg_of_le
      (fun t => sq_nonneg (‖D t‖))
      (fun t => by
        have hright : 0 ≤ hbL0 q * ‖x t‖ :=
          mul_nonneg hL (norm_nonneg _)
        simpa [mul_pow] using
          (sq_le_sq₀ (norm_nonneg _) hright).2 (hDnorm t))
      hmajorD
  have hp_sq : Summable (fun t : ℤ => ‖p t‖ ^ 2) := by
    have hscale := hDsq.const_smul (τ ^ 2)
    have hτabs : |τ| = τ := abs_of_nonneg hτ0
    simpa [p, norm_smul, Real.norm_eq_abs, sq_abs, hτabs, pow_two,
      mul_assoc, mul_left_comm, mul_comm] using hscale
  have hs_sq : Summable (fun t : ℤ => ‖s t‖ ^ 2) := by
    have hxscaled : Summable (fun t : ℤ =>
        2 * (hbL0 q) ^ 2 * ‖x t‖ ^ 2) := by
      have h := hxs.const_smul (2 * (hbL0 q) ^ 2)
      simpa [smul_eq_mul] using h
    have hpscaled : Summable (fun t : ℤ => 2 * ‖p t‖ ^ 2) := by
      have h := hp_sq.const_smul (2 : ℝ)
      simpa [smul_eq_mul] using h
    have hmajor : Summable (fun t : ℤ =>
        2 * (hbL0 q) ^ 2 * ‖x t‖ ^ 2 + 2 * ‖p t‖ ^ 2) :=
      hxscaled.add hpscaled
    apply Summable.of_nonneg_of_le (fun t => sq_nonneg (‖s t‖))
    · intro t
      have hnorm := SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq
        ((hbL0 q) • x t) (-p t)
      simpa [s, sub_eq_add_neg, norm_smul, Real.norm_eq_abs, sq_abs,
        pow_two, mul_assoc, mul_left_comm, mul_comm] using hnorm
    · have hL_abs : |hbL0 q| = hbL0 q := abs_of_nonneg hL
      simpa [hL_abs, pow_two, mul_assoc, mul_left_comm, mul_comm] using hmajor
  have hA : Summable A := by
    have h := (bilateral_l2_shift_and_inner_summability hp_sq hs_sq 0).2.2
    simpa [A] using h.of_abs
  have hneg_shift : Summable
      (fun t : ℤ => inner ℝ (p t) (s (t + (-1)))) := by
    have h := (bilateral_l2_shift_and_inner_summability hp_sq hs_sq (-1)).2.2
    exact h.of_abs
  have hfour_shift : Summable
      (fun t : ℤ => inner ℝ (p t) (s (t + 4))) := by
    have h := (bilateral_l2_shift_and_inner_summability hp_sq hs_sq 4).2.2
    exact h.of_abs
  have hB : Summable B := by
    have h := hA.sub hneg_shift
    simpa [A, B, inner_sub_right] using h
  have hC : Summable C := by
    have h := hA.sub hfour_shift
    simpa [A, C, inner_sub_right] using h
  have hA_nonneg : 0 ≤ ∑' t : ℤ, A t := by
    simpa [A, p, s, D] using
      (hb_bilateral_zero_lag_supply_nonnegative
        hq0 hq1 hf τ hτ0 hτ1 x hxs)
  have hB_nonneg : 0 ≤ ∑' t : ℤ, B t := by
    simpa [B, p, s, D] using
      (hb_bilateral_lag_supply_nonnegative
        hq0 hq1 hf τ hτ0 hτ1 x hxs (-1))
  have hC_nonneg : 0 ≤ ∑' t : ℤ, C t := by
    simpa [C, p, s, D] using
      (hb_bilateral_lag_supply_nonnegative
        hq0 hq1 hf τ hτ0 hτ1 x hxs 4)
  have hE : Summable (fun t : ℤ => hbMultiplierEpsilon * A t) :=
    Summable.mul_left _ hA
  have hCscaled : Summable
      (fun t : ℤ => (4 / 25 : ℝ) * C t) :=
    Summable.mul_left _ hC
  have hsum :
      0 ≤ ∑' t : ℤ,
        (hbMultiplierEpsilon * A t + B t + (4 / 25 : ℝ) * C t) := by
    have hrewrite :
        (∑' t : ℤ, (hbMultiplierEpsilon * A t + B t +
            (4 / 25 : ℝ) * C t)) =
          hbMultiplierEpsilon * (∑' t : ℤ, A t) +
            (∑' t : ℤ, B t) +
            (4 / 25 : ℝ) * (∑' t : ℤ, C t) := by
      rw [Summable.tsum_add (hE.add hB) hCscaled]
      rw [Summable.tsum_add hE hB]
      rw [hA.tsum_mul_left, hC.tsum_mul_left]
    rw [hrewrite]
    have heps : 0 ≤ hbMultiplierEpsilon := by
      norm_num [hbMultiplierEpsilon]
    have hcoef : 0 ≤ (4 / 25 : ℝ) := by norm_num
    exact add_nonneg
      (add_nonneg (mul_nonneg heps hA_nonneg) hB_nonneg)
      (mul_nonneg hcoef hC_nonneg)
  have hterm :
      (∑' t : ℤ,
        inner ℝ (p t)
          (hbMultiplierEpsilon • s t + (s t - s (t + (-1))) +
            (4 / 25 : ℝ) • (s t - s (t + 4)))) =
        ∑' t : ℤ,
          (hbMultiplierEpsilon * A t + B t + (4 / 25 : ℝ) * C t) := by
    apply tsum_congr
    intro t
    simp [A, B, C, real_inner_smul_right, inner_add_right,
      inner_sub_right]
  have hnonneg :
      0 ≤ ∑' t : ℤ,
        inner ℝ (p t)
          (hbMultiplierEpsilon • s t + (s t - s (t + (-1))) +
            (4 / 25 : ℝ) • (s t - s (t + 4))) := by
    rw [hterm]
    exact hsum
  simpa [p, s, D, sub_eq_add_neg] using hnonneg

set_option maxHeartbeats 2000000 in
private theorem frequency_scalar_margin_on_box {q a b c : ℝ}
    (hbox : HB_Box q a b) (hc : |c| ≤ 1) :
    frequencyNumerator q a b c / frequencyT q a b c ≤ -(1 / 2000 : ℝ) := by
  let hD := HB_box_subset_domain hbox
  rcases HB_BOX_ENDPOINT_RANGES hbox with
    ⟨hqlo, hqhi, halo, hahi, hblo, hbhi, hprod, ha2q, ha2q2, hbexpr⟩
  have hq0 : 0 < q := parameterDomain_q_pos hD
  have hb0 : 0 ≤ b := hD.2.2.1
  have ha0 : 0 < a := hD.2.2.2.2.1
  let r : ℝ := frequencyR c
  have hr0 : 0 ≤ r := by
    dsimp [r, frequencyR]
    linarith [abs_le.mp hc]
  have hr2 : r ≤ 2 := by
    dsimp [r, frequencyR]
    linarith [abs_le.mp hc]
  have hrsq : r ^ 2 ≤ 2 * r := by
    nlinarith [sq_nonneg (r - 1)]
  have hW : (3 / 500 : ℝ) < frequencyW q a b c :=
    HB_BOX_W_MARGIN hbox hc
  have hWr :
      (3 / 500 : ℝ) * r ≤ frequencyW q a b c * r :=
    mul_le_mul_of_nonneg_right (le_of_lt hW) hr0
  have hcoef :
      a * (1 + q) * (1 + b) - 2 * (1 - b) ^ 2 ≤ 4 := by
    nlinarith [hprod, sq_nonneg (1 - b)]
  have hcoef_r :
      (a * (1 + q) * (1 + b) - 2 * (1 - b) ^ 2) * r ≤ 4 * r :=
    mul_le_mul_of_nonneg_right hcoef hr0
  have heps_a2q :
      (1 / 2000000 : ℝ) < hbMultiplierEpsilon * (a ^ 2 * q) := by
    have heps : 0 < hbMultiplierEpsilon := by
      norm_num [hbMultiplierEpsilon]
    have h := mul_lt_mul_of_pos_left ha2q heps
    norm_num [hbMultiplierEpsilon] at h ⊢
    nlinarith
  have hnonneg_b : 0 ≤ hbMultiplierEpsilon * (4 * b * r ^ 2) := by
    have heps : 0 ≤ hbMultiplierEpsilon := by
      norm_num [hbMultiplierEpsilon]
    positivity
  have hnum_lower :
      (149 / 25000 : ℝ) * r + (1 / 2000000 : ℝ) <
        -(frequencyNumerator q a b c) := by
    have heps : 0 < hbMultiplierEpsilon := by
      norm_num [hbMultiplierEpsilon]
    have hterm :
        -hbMultiplierEpsilon *
            ((a * (1 + q) * (1 + b) - 2 * (1 - b) ^ 2) * r) ≥
          -hbMultiplierEpsilon * (4 * r) := by
      simpa [mul_assoc] using
        (neg_le_neg
          (mul_le_mul_of_nonneg_left hcoef_r (le_of_lt heps)))
    have hexpand :
        frequencyNumerator q a b c =
          -r * frequencyW q a b c +
            hbMultiplierEpsilon *
              (-(a ^ 2 * q) +
              (a * (1 + q) * (1 + b) - 2 * (1 - b) ^ 2) * r -
                4 * b * r ^ 2) := by
      dsimp [frequencyNumerator, frequencyD, frequencyR, r]
    have hD_upper :
        hbMultiplierEpsilon *
              (-(a ^ 2 * q) +
                (a * (1 + q) * (1 + b) - 2 * (1 - b) ^ 2) * r -
                4 * b * r ^ 2) ≤
            -hbMultiplierEpsilon * (a ^ 2 * q) +
              hbMultiplierEpsilon * (4 * r) := by
      nlinarith [hterm, hnonneg_b]
    have hminus :
        -hbMultiplierEpsilon *
              (-(a ^ 2 * q) +
                (a * (1 + q) * (1 + b) - 2 * (1 - b) ^ 2) * r -
                4 * b * r ^ 2) ≥
            hbMultiplierEpsilon * (a ^ 2 * q) -
              hbMultiplierEpsilon * (4 * r) := by
      nlinarith [hD_upper]
    have hstrict :
        (149 / 25000 : ℝ) * r + (1 / 2000000 : ℝ) <
          (3 / 500 : ℝ) * r +
            hbMultiplierEpsilon * (a ^ 2 * q) -
              hbMultiplierEpsilon * (4 * r) := by
      norm_num [hbMultiplierEpsilon] at heps_a2q ⊢
      nlinarith [heps_a2q]
    calc
      (149 / 25000 : ℝ) * r + (1 / 2000000 : ℝ) <
          r * frequencyW q a b c -
            hbMultiplierEpsilon *
              (-(a ^ 2 * q) +
                (a * (1 + q) * (1 + b) - 2 * (1 - b) ^ 2) * r -
                4 * b * r ^ 2) := by
        exact lt_of_lt_of_le hstrict (by
          nlinarith [hWr, hminus])
      _ = -(frequencyNumerator q a b c) := by
        rw [hexpand]
        ring
  have hTcoef :
      2 * (1 - b) ^ 2 - 2 * a * q * (1 + b) + 8 * b < 6 := by
    have haq : 0 ≤ 2 * a * q * (1 + b) := by
      have h1pb : 0 ≤ 1 + b := by linarith
      positivity
    nlinarith [hbexpr, haq]
  have hTcoef_r :
      (2 * (1 - b) ^ 2 - 2 * a * q * (1 + b) + 8 * b) * r ≤ 6 * r :=
    mul_le_mul_of_nonneg_right (le_of_lt hTcoef) hr0
  have hquad :
      4 * b * r ^ 2 ≤ 8 * b * r := by
    have h4b : 0 ≤ 4 * b := by nlinarith [hb0]
    calc
      4 * b * r ^ 2 ≤ (4 * b) * (2 * r) := by
        exact mul_le_mul_of_nonneg_left hrsq h4b
      _ = 8 * b * r := by
        rw [mul_assoc]
        ring
  have hT_upper :
      frequencyT q a b c < 6 * r + (1 / 1000 : ℝ) := by
    change
      a ^ 2 * q ^ 2 +
          (2 * (1 - b) ^ 2 - 2 * a * q * (1 + b)) * r +
            4 * b * r ^ 2 <
        6 * r + (1 / 1000 : ℝ)
    nlinarith [ha2q2, hTcoef_r, hquad]
  have hT : 0 < frequencyT q a b c :=
    frequency_t_factorization_and_pos hD hc
  have hTdiv :
      frequencyT q a b c / 2000 <
        (149 / 25000 : ℝ) * r + (1 / 2000000 : ℝ) := by
    have h1 := div_lt_div_of_pos_right hT_upper (by norm_num : (0 : ℝ) < 2000)
    nlinarith
  have hNdiv :
      frequencyT q a b c / 2000 < -(frequencyNumerator q a b c) :=
    lt_trans hTdiv hnum_lower
  apply (div_le_iff₀ hT).2
  nlinarith

theorem HB_DYNAMICS_SUPPLY_FREQUENCY {q a b : ℝ}
    (hbox : HB_Box q a b) :
    let hD := HB_box_subset_domain hbox
    (∀ {d : ℕ} (hf : AdmissibleObjective q d),
      hbCenteredNonlinearity (parameterDomain_q_pos hD) hf 0 = 0 ∧
        ∀ x : Vec d,
          ‖hbCenteredNonlinearity (parameterDomain_q_pos hD) hf x‖ ≤
            hbL0 q * ‖x‖) ∧
      (∀ {d : ℕ} (hf : AdmissibleObjective q d) (τ : ℝ),
        0 ≤ τ → τ ≤ 1 →
          ∀ x : ℤ → Vec d,
            Summable (fun t : ℤ => ‖x t‖ ^ 2) →
              hbSupplyInequality (parameterDomain_q_pos hD) hf τ x) ∧
      hbPlantPolesInsideUnitDisk q a b ∧
      (∀ z : ℂ,
        (hz : ‖z‖ = 1) →
          Complex.re
            (hbMultiplier z *
              (((hbL0 q : ℝ) : ℂ) * hbTransferUnitCircle q a b hD z hz - 1)) ≤
            -(1 / 2000 : ℝ)) := by
  dsimp
  let hD := HB_box_subset_domain hbox
  have hq0 : 0 < q := parameterDomain_q_pos hD
  have hq1 : q < 1 := parameterDomain_q_lt_one hD
  refine ⟨?_, ?_, hbPlantPolesInsideUnitDisk_of_parameterDomain hD, ?_⟩
  · intro d hf
    exact ⟨hbCenteredNonlinearity_zero hq0 hf, fun x =>
      hbCenteredNonlinearity_lipschitz_from_zero hq0 hf x⟩
  · intro d hf τ hτ0 hτ1 x hxs
    unfold hbSupplyInequality
    dsimp
    exact hb_multiplier_time_domain_tsum_nonnegative_of_zero_and_lags
      hq0 hq1 hf τ hτ0 hτ1 x hxs
  · intro z hz
    let c : ℝ := z.re
    have hc : |c| ≤ 1 := by
      rw [show c = z.re from rfl]
      rw [abs_le]
      have hnorm : z.re ^ 2 + z.im ^ 2 = 1 := by
        have h := Complex.normSq_eq_norm_sq z
        rw [hz] at h
        simpa [Complex.normSq_apply, pow_two] using h
      constructor <;> nlinarith [hnorm, sq_nonneg z.im]
    have hmargin := frequency_scalar_margin_on_box hbox hc
    have hquot := (HB_FREQUENCY_NUMERATOR_ALGEBRA hD hc).2.2 z hz (by rfl)
    calc
      Complex.re
          (hbMultiplier z *
            (((hbL0 q : ℝ) : ℂ) * hbTransferUnitCircle q a b hD z hz - 1)) =
          frequencyNumerator q a b c / frequencyT q a b c := hquot
      _ ≤ -(1 / 2000 : ℝ) := by simpa [c] using hmargin

/-- One-sided square-summability, the membership predicate for the source
`ell_2` sequence space. -/
def hbSequenceInL2 {d : ℕ} (x : ℕ → Vec d) : Prop :=
  Summable (fun t : ℕ => ‖x t‖ ^ 2)

/-- Bilateral square-summability, used for the multiplier sequence space. -/
def hbBilateralSequenceInL2 {d : ℕ} (x : ℤ → Vec d) : Prop :=
  Summable (fun t : ℤ => ‖x t‖ ^ 2)

/-- Scalar energy of a centered one-sided sequence. -/
def hbSequenceEnergy {d : ℕ} (x : ℕ → Vec d) : ℝ :=
  ∑' t : ℕ, ‖x t‖ ^ 2

/-- The paper's one-sided `ell_2` norm, named as a square-root of energy. -/
def hbSequenceL2Norm {d : ℕ} (x : ℕ → Vec d) : ℝ :=
  Real.sqrt (hbSequenceEnergy x)

/-- Scalar energy of a bilateral sequence. -/
def hbBilateralSequenceEnergy {d : ℕ} (x : ℤ → Vec d) : ℝ :=
  ∑' t : ℤ, ‖x t‖ ^ 2

/-- The paper's bilateral `ell_2` norm. -/
def hbBilateralSequenceL2Norm {d : ℕ} (x : ℤ → Vec d) : ℝ :=
  Real.sqrt (hbBilateralSequenceEnergy x)

/-- A real constant is an admissible `ell_2` gain for the zero-state plant only
when it maps every square-summable input to a square-summable output and
then satisfies the norm inequality. -/
def hbPlantL2GainBound (q a b C : ℝ) : Prop :=
  0 ≤ C ∧
    ∀ {d : ℕ} (input : ℕ → Vec d),
      hbSequenceInL2 input →
        hbSequenceInL2 (hbPlantResponse q a b input) ∧
          hbSequenceL2Norm (hbPlantResponse q a b input) ≤
            C * hbSequenceL2Norm input

/-- A real constant is an admissible `ell_2` gain for the finite-lag multiplier
only when the multiplier output is again square-summable and then satisfies the
norm inequality. -/
def hbMultiplierL2GainBound (C : ℝ) : Prop :=
  0 ≤ C ∧
    ∀ {d : ℕ} (s : ℤ → Vec d),
      hbBilateralSequenceInL2 s →
        hbBilateralSequenceInL2 (fun t : ℤ => hbMultiplierTimeDomain s t) ∧
          hbBilateralSequenceL2Norm (fun t : ℤ => hbMultiplierTimeDomain s t) ≤
            C * hbBilateralSequenceL2Norm s

/-- The canonical operator norm/gain `g=||G||` of the zero-state plant on
one-sided square-summable inputs. -/
def hbPlantL2Gain (q a b : ℝ) : ℝ :=
  sInf {C : ℝ | hbPlantL2GainBound q a b C}

/-- The canonical operator norm/gain `m=||M||` of the finite-lag multiplier
on bilateral square-summable sequences. -/
def hbMultiplierL2Gain : ℝ :=
  sInf {C : ℝ | hbMultiplierL2GainBound C}

private theorem hb_bilateral_l2_norm_add_le
    {d : ℕ} {u v : ℤ → Vec d}
    (hu : Summable (fun t : ℤ => ‖u t‖ ^ 2))
    (hv : Summable (fun t : ℤ => ‖v t‖ ^ 2)) :
    Summable (fun t : ℤ => ‖u t + v t‖ ^ 2) ∧
      hbBilateralSequenceL2Norm (fun t : ℤ => u t + v t) ≤
        hbBilateralSequenceL2Norm u + hbBilateralSequenceL2Norm v := by
  have hcross_abs :
      Summable (fun t : ℤ => |inner ℝ (u t) (v t)|) := by
    simpa using
      (bilateral_l2_shift_and_inner_summability hu hv 0).2.2
  have hcross :
      Summable (fun t : ℤ => inner ℝ (u t) (v t)) :=
    hcross_abs.of_abs
  have hdiag_u :
      Summable (fun t : ℤ => inner ℝ (u t) (u t)) := by
    simpa [real_inner_self_eq_norm_sq] using hu
  have hsum :
      Summable (fun t : ℤ =>
        ‖u t‖ ^ 2 + 2 * inner ℝ (u t) (v t) + ‖v t‖ ^ 2) := by
    have hscaled := Summable.mul_left (2 : ℝ) hcross
    simpa [add_assoc] using (hu.add hscaled).add hv
  have hout :
      Summable (fun t : ℤ => ‖u t + v t‖ ^ 2) := by
    have heq :
        (fun t : ℤ => ‖u t + v t‖ ^ 2) =
          (fun t : ℤ =>
            ‖u t‖ ^ 2 + 2 * inner ℝ (u t) (v t) + ‖v t‖ ^ 2) := by
      funext t
      exact norm_add_sq_real (u t) (v t)
    rw [heq]
    exact hsum
  let fu : ℤ → NNReal := fun t => ⟨‖u t‖, norm_nonneg _⟩
  let fv : ℤ → NNReal := fun t => ⟨‖v t‖, norm_nonneg _⟩
  have hfu : Summable (fun t : ℤ => fu t ^ (2 : ℝ)) := by
    rw [← NNReal.summable_coe]
    simpa [fu, Real.rpow_two] using hu
  have hfv : Summable (fun t : ℤ => fv t ^ (2 : ℝ)) := by
    rw [← NNReal.summable_coe]
    simpa [fv, Real.rpow_two] using hv
  have hholder :=
    NNReal.summable_and_inner_le_Lp_mul_Lq_tsum
      (Real.HolderConjugate.two_two) hfu hfv
  have hmul :
      Summable (fun t : ℤ => (fu t : ℝ) * (fv t : ℝ)) := by
    have hmul' :
        Summable (fun t : ℤ => ((fu t * fv t : NNReal) : ℝ)) :=
      NNReal.summable_coe.mpr hholder.1
    simpa using hmul'
  have hmul_bound :
      ∑' t : ℤ, (fu t : ℝ) * (fv t : ℝ) ≤
        (∑' t : ℤ, (fu t ^ (2 : ℝ) : ℝ)) ^ (1 / (2 : ℝ)) *
          (∑' t : ℤ, (fv t ^ (2 : ℝ) : ℝ)) ^ (1 / (2 : ℝ)) := by
    exact_mod_cast hholder.2
  have hcross_bound :
      ∑' t : ℤ, inner ℝ (u t) (v t) ≤
        hbBilateralSequenceL2Norm u * hbBilateralSequenceL2Norm v := by
    have hpoint :
        ∀ t : ℤ, inner ℝ (u t) (v t) ≤
          (fu t : ℝ) * (fv t : ℝ) := by
      intro t
      exact le_trans (le_abs_self _) (abs_real_inner_le_norm (u t) (v t))
    have hle := hcross.tsum_le_tsum hpoint hmul
    have hle' := hle.trans hmul_bound
    simpa [fu, fv, hbBilateralSequenceL2Norm, hbBilateralSequenceEnergy,
      Real.sqrt_eq_rpow, Real.rpow_two] using hle'
  have hU_nonneg : 0 ≤ ∑' t : ℤ, ‖u t‖ ^ 2 :=
    tsum_nonneg fun t => sq_nonneg _
  have hV_nonneg : 0 ≤ ∑' t : ℤ, ‖v t‖ ^ 2 :=
    tsum_nonneg fun t => sq_nonneg _
  have henergy :
      (∑' t : ℤ, ‖u t + v t‖ ^ 2) ≤
        (Real.sqrt (∑' t : ℤ, ‖u t‖ ^ 2) +
          Real.sqrt (∑' t : ℤ, ‖v t‖ ^ 2)) ^ 2 := by
    have hcross_sum :
        (∑' t : ℤ, (‖u t‖ ^ 2 + 2 * inner ℝ (u t) (v t) + ‖v t‖ ^ 2)) =
          (∑' t : ℤ, ‖u t‖ ^ 2) +
            2 * (∑' t : ℤ, inner ℝ (u t) (v t)) +
            (∑' t : ℤ, ‖v t‖ ^ 2) := by
      rw [Summable.tsum_add (hu.add (Summable.mul_left (2 : ℝ) hcross)) hv]
      rw [Summable.tsum_add hu (Summable.mul_left (2 : ℝ) hcross)]
      rw [tsum_mul_left]
    rw [show (∑' t : ℤ, ‖u t + v t‖ ^ 2) =
        (∑' t : ℤ, (‖u t‖ ^ 2 + 2 * inner ℝ (u t) (v t) + ‖v t‖ ^ 2)) by
          apply tsum_congr
          intro t
          exact norm_add_sq_real (u t) (v t)]
    rw [hcross_sum]
    have hcross_bound' :
        (∑' t : ℤ, inner ℝ (u t) (v t)) ≤
          Real.sqrt (∑' t : ℤ, ‖u t‖ ^ 2) *
            Real.sqrt (∑' t : ℤ, ‖v t‖ ^ 2) := by
      simpa [hbBilateralSequenceL2Norm, hbBilateralSequenceEnergy] using hcross_bound
    nlinarith [hcross_bound', Real.sq_sqrt hU_nonneg, Real.sq_sqrt hV_nonneg]
  have hnorm :
      hbBilateralSequenceL2Norm (fun t : ℤ => u t + v t) ≤
        hbBilateralSequenceL2Norm u + hbBilateralSequenceL2Norm v := by
    unfold hbBilateralSequenceL2Norm hbBilateralSequenceEnergy at *
    have hsqrt := Real.sqrt_le_sqrt henergy
    have hsum_nonneg :
        0 ≤ Real.sqrt (∑' t : ℤ, ‖u t‖ ^ 2) +
          Real.sqrt (∑' t : ℤ, ‖v t‖ ^ 2) := by positivity
    have hsquare :
        Real.sqrt (
            (Real.sqrt (∑' t : ℤ, ‖u t‖ ^ 2) +
              Real.sqrt (∑' t : ℤ, ‖v t‖ ^ 2)) ^ 2) =
          Real.sqrt (∑' t : ℤ, ‖u t‖ ^ 2) +
            Real.sqrt (∑' t : ℤ, ‖v t‖ ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hsum_nonneg]
    rw [hsquare] at hsqrt
    exact hsqrt
  exact ⟨hout, hnorm⟩

private theorem hb_bilateral_inner_tsum_le_l2_mul_l2
    {d : ℕ} {u v : ℤ → Vec d}
    (hu : Summable (fun t : ℤ => ‖u t‖ ^ 2))
    (hv : Summable (fun t : ℤ => ‖v t‖ ^ 2)) :
    Summable (fun t : ℤ => inner ℝ (u t) (v t)) ∧
      (∑' t : ℤ, inner ℝ (u t) (v t)) ≤
        hbBilateralSequenceL2Norm u * hbBilateralSequenceL2Norm v := by
  have hcross_abs :
      Summable (fun t : ℤ => |inner ℝ (u t) (v t)|) := by
    simpa using
      (bilateral_l2_shift_and_inner_summability hu hv 0).2.2
  have hcross :
      Summable (fun t : ℤ => inner ℝ (u t) (v t)) :=
    hcross_abs.of_abs
  let fu : ℤ → NNReal := fun t => ⟨‖u t‖, norm_nonneg _⟩
  let fv : ℤ → NNReal := fun t => ⟨‖v t‖, norm_nonneg _⟩
  have hfu : Summable (fun t : ℤ => fu t ^ (2 : ℝ)) := by
    rw [← NNReal.summable_coe]
    simpa [fu, Real.rpow_two] using hu
  have hfv : Summable (fun t : ℤ => fv t ^ (2 : ℝ)) := by
    rw [← NNReal.summable_coe]
    simpa [fv, Real.rpow_two] using hv
  have hholder :=
    NNReal.summable_and_inner_le_Lp_mul_Lq_tsum
      (Real.HolderConjugate.two_two) hfu hfv
  have hmul :
      Summable (fun t : ℤ => (fu t : ℝ) * (fv t : ℝ)) := by
    have hmul' :
        Summable (fun t : ℤ => ((fu t * fv t : NNReal) : ℝ)) :=
      NNReal.summable_coe.mpr hholder.1
    simpa using hmul'
  have hmul_bound :
      ∑' t : ℤ, (fu t : ℝ) * (fv t : ℝ) ≤
        (∑' t : ℤ, (fu t ^ (2 : ℝ) : ℝ)) ^ (1 / (2 : ℝ)) *
          (∑' t : ℤ, (fv t ^ (2 : ℝ) : ℝ)) ^ (1 / (2 : ℝ)) := by
    exact_mod_cast hholder.2
  have hpoint :
      ∀ t : ℤ, inner ℝ (u t) (v t) ≤
        (fu t : ℝ) * (fv t : ℝ) := by
    intro t
    exact le_trans (le_abs_self _) (abs_real_inner_le_norm (u t) (v t))
  have hle := hcross.tsum_le_tsum hpoint hmul
  refine ⟨hcross, ?_⟩
  exact (hle.trans hmul_bound).trans_eq (by
    simp [fu, fv, hbBilateralSequenceL2Norm, hbBilateralSequenceEnergy,
      Real.sqrt_eq_rpow, Real.rpow_two])

private theorem hb_bilateral_l2_shift_summable_and_norm_eq
    {d : ℕ} {s : ℤ → Vec d} (hs : Summable (fun t : ℤ => ‖s t‖ ^ 2))
    (ell : ℤ) :
    Summable (fun t : ℤ => ‖s (t + ell)‖ ^ 2) ∧
      hbBilateralSequenceL2Norm (fun t : ℤ => s (t + ell)) =
        hbBilateralSequenceL2Norm s := by
  refine ⟨?_, ?_⟩
  · simpa [Function.comp_def, Equiv.coe_addRight] using
      (Equiv.addRight ell).summable_iff.mpr hs
  · unfold hbBilateralSequenceL2Norm hbBilateralSequenceEnergy
    congr 1
    simpa [Function.comp_def, Equiv.coe_addRight] using
      (Equiv.addRight ell).tsum_eq (fun t : ℤ => ‖s t‖ ^ 2)

private theorem hb_bilateral_l2_smul_summable_and_norm_eq
    {d : ℕ} {s : ℤ → Vec d} (hs : Summable (fun t : ℤ => ‖s t‖ ^ 2))
    (c : ℝ) :
    Summable (fun t : ℤ => ‖c • s t‖ ^ 2) ∧
      hbBilateralSequenceL2Norm (fun t : ℤ => c • s t) =
        |c| * hbBilateralSequenceL2Norm s := by
  have hsum : Summable (fun t : ℤ => c ^ 2 * ‖s t‖ ^ 2) := by
    simpa [smul_eq_mul] using hs.const_smul (c ^ 2)
  have hsq : Summable (fun t : ℤ => ‖c • s t‖ ^ 2) := by
    apply Summable.congr hsum
    intro t
    simp [norm_smul, Real.norm_eq_abs, sq_abs, mul_pow, mul_comm]
  have henergy :
      (∑' t : ℤ, ‖c • s t‖ ^ 2) =
        c ^ 2 * (∑' t : ℤ, ‖s t‖ ^ 2) := by
    calc
      (∑' t : ℤ, ‖c • s t‖ ^ 2) =
          ∑' t : ℤ, c ^ 2 * ‖s t‖ ^ 2 := by
            apply tsum_congr
            intro t
            simp [norm_smul, Real.norm_eq_abs, sq_abs, mul_pow, mul_comm]
      _ = c ^ 2 * (∑' t : ℤ, ‖s t‖ ^ 2) := by
        rw [tsum_mul_left]
  have hnorm :
      hbBilateralSequenceL2Norm (fun t : ℤ => c • s t) =
        |c| * hbBilateralSequenceL2Norm s := by
    unfold hbBilateralSequenceL2Norm hbBilateralSequenceEnergy
    rw [henergy, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  exact ⟨hsq, hnorm⟩

private theorem hb_multiplier_finite_lag_l2_bound
    {d : ℕ} {s : ℤ → Vec d}
    (hs : Summable (fun t : ℤ => ‖s t‖ ^ 2)) :
    Summable (fun t : ℤ => ‖hbMultiplierTimeDomain s t‖ ^ 2) ∧
      hbBilateralSequenceL2Norm (fun t : ℤ => hbMultiplierTimeDomain s t) ≤
        (hbMultiplierEpsilon + 2 + 8 / 25 : ℝ) *
          hbBilateralSequenceL2Norm s := by
  let shift1 : ℤ → Vec d := fun t => s (t + (-1))
  let shift4 : ℤ → Vec d := fun t => s (t + 4)
  let diff1 : ℤ → Vec d := fun t => s t - shift1 t
  let diff4 : ℤ → Vec d := fun t => s t - shift4 t
  let negShift1 : ℤ → Vec d := fun t => -shift1 t
  let negShift4 : ℤ → Vec d := fun t => -shift4 t
  let epsilonPart : ℤ → Vec d :=
    fun t => hbMultiplierEpsilon • s t
  let scaledDiff4 : ℤ → Vec d :=
    fun t => (4 / 25 : ℝ) • diff4 t
  have hshift1 := hb_bilateral_l2_shift_summable_and_norm_eq hs (-1)
  have hshift4 := hb_bilateral_l2_shift_summable_and_norm_eq hs 4
  have hshift1_sq :
      Summable (fun t : ℤ => ‖shift1 t‖ ^ 2) := by
    simpa [shift1] using hshift1.1
  have hshift4_sq :
      Summable (fun t : ℤ => ‖shift4 t‖ ^ 2) := by
    simpa [shift4] using hshift4.1
  have hshift1_norm :
      hbBilateralSequenceL2Norm shift1 =
        hbBilateralSequenceL2Norm s := by
    simpa [shift1] using hshift1.2
  have hshift4_norm :
      hbBilateralSequenceL2Norm shift4 =
        hbBilateralSequenceL2Norm s := by
    simpa [shift4] using hshift4.2
  have hneg1 := hb_bilateral_l2_smul_summable_and_norm_eq hshift1_sq (-1)
  have hneg4 := hb_bilateral_l2_smul_summable_and_norm_eq hshift4_sq (-1)
  have hneg1_sq :
      Summable (fun t : ℤ => ‖negShift1 t‖ ^ 2) := by
    simpa [negShift1] using hneg1.1
  have hneg4_sq :
      Summable (fun t : ℤ => ‖negShift4 t‖ ^ 2) := by
    simpa [negShift4] using hneg4.1
  have hneg1_norm :
      hbBilateralSequenceL2Norm negShift1 =
        hbBilateralSequenceL2Norm shift1 := by
    simpa [negShift1] using hneg1.2
  have hneg4_norm :
      hbBilateralSequenceL2Norm negShift4 =
        hbBilateralSequenceL2Norm shift4 := by
    simpa [negShift4] using hneg4.2
  have hdiff1_tri := hb_bilateral_l2_norm_add_le hs hneg1_sq
  have hdiff4_tri := hb_bilateral_l2_norm_add_le hs hneg4_sq
  have hdiff1_sq :
      Summable (fun t : ℤ => ‖diff1 t‖ ^ 2) := by
    simpa [diff1, negShift1, sub_eq_add_neg] using hdiff1_tri.1
  have hdiff4_sq :
      Summable (fun t : ℤ => ‖diff4 t‖ ^ 2) := by
    simpa [diff4, negShift4, sub_eq_add_neg] using hdiff4_tri.1
  have hdiff1_bound :
      hbBilateralSequenceL2Norm diff1 ≤
        2 * hbBilateralSequenceL2Norm s := by
    calc
      hbBilateralSequenceL2Norm diff1 =
          hbBilateralSequenceL2Norm
            (fun t : ℤ => s t + negShift1 t) := by
              simp [diff1, negShift1, sub_eq_add_neg]
      _ ≤ hbBilateralSequenceL2Norm s +
            hbBilateralSequenceL2Norm negShift1 := hdiff1_tri.2
      _ = hbBilateralSequenceL2Norm s +
            hbBilateralSequenceL2Norm s := by
              rw [hneg1_norm, hshift1_norm]
      _ = 2 * hbBilateralSequenceL2Norm s := by ring
  have hdiff4_bound :
      hbBilateralSequenceL2Norm diff4 ≤
        2 * hbBilateralSequenceL2Norm s := by
    calc
      hbBilateralSequenceL2Norm diff4 =
          hbBilateralSequenceL2Norm
            (fun t : ℤ => s t + negShift4 t) := by
              simp [diff4, negShift4, sub_eq_add_neg]
      _ ≤ hbBilateralSequenceL2Norm s +
            hbBilateralSequenceL2Norm negShift4 := hdiff4_tri.2
      _ = hbBilateralSequenceL2Norm s +
            hbBilateralSequenceL2Norm s := by
              rw [hneg4_norm, hshift4_norm]
      _ = 2 * hbBilateralSequenceL2Norm s := by ring
  have heps : 0 ≤ hbMultiplierEpsilon := by
    norm_num [hbMultiplierEpsilon]
  have hepsilon := hb_bilateral_l2_smul_summable_and_norm_eq hs
    hbMultiplierEpsilon
  have hepsilon_sq :
      Summable (fun t : ℤ => ‖epsilonPart t‖ ^ 2) := by
    simpa [epsilonPart] using hepsilon.1
  have hepsilon_norm :
      hbBilateralSequenceL2Norm epsilonPart =
        hbMultiplierEpsilon * hbBilateralSequenceL2Norm s := by
    simpa [epsilonPart, abs_of_nonneg heps] using hepsilon.2
  have hscaled4 := hb_bilateral_l2_smul_summable_and_norm_eq hdiff4_sq
    (4 / 25 : ℝ)
  have hscaled4_sq :
      Summable (fun t : ℤ => ‖scaledDiff4 t‖ ^ 2) := by
    simpa [scaledDiff4] using hscaled4.1
  have hscaled4_norm :
      hbBilateralSequenceL2Norm scaledDiff4 =
        (4 / 25 : ℝ) * hbBilateralSequenceL2Norm diff4 := by
    have hcoef : 0 ≤ (4 / 25 : ℝ) := by norm_num
    simpa [scaledDiff4, abs_of_nonneg hcoef] using hscaled4.2
  have htri1 := hb_bilateral_l2_norm_add_le hepsilon_sq hdiff1_sq
  have htri2 := hb_bilateral_l2_norm_add_le htri1.1 hscaled4_sq
  have houtput_eq :
      (fun t : ℤ => hbMultiplierTimeDomain s t) =
        (fun t : ℤ => (epsilonPart t + diff1 t) + scaledDiff4 t) := by
    funext t
    simp [hbMultiplierTimeDomain, epsilonPart, diff1, diff4, scaledDiff4,
      shift1, shift4, sub_eq_add_neg, add_assoc]
  have hout :
      Summable (fun t : ℤ => ‖hbMultiplierTimeDomain s t‖ ^ 2) := by
    have heq_norm :
        (fun t : ℤ => ‖hbMultiplierTimeDomain s t‖ ^ 2) =
          (fun t : ℤ => ‖(epsilonPart t + diff1 t) + scaledDiff4 t‖ ^ 2) := by
      funext t
      rw [congrFun houtput_eq t]
    rw [heq_norm]
    exact htri2.1
  have hscaled4_bound :
      hbBilateralSequenceL2Norm scaledDiff4 ≤
        (4 / 25 : ℝ) * (2 * hbBilateralSequenceL2Norm s) := by
    rw [hscaled4_norm]
    exact mul_le_mul_of_nonneg_left hdiff4_bound (by norm_num)
  have hnorm :
      hbBilateralSequenceL2Norm (fun t : ℤ => hbMultiplierTimeDomain s t) ≤
        (hbMultiplierEpsilon + 2 + 8 / 25 : ℝ) *
          hbBilateralSequenceL2Norm s := by
    calc
      hbBilateralSequenceL2Norm (fun t : ℤ => hbMultiplierTimeDomain s t) =
          hbBilateralSequenceL2Norm
            (fun t : ℤ => (epsilonPart t + diff1 t) + scaledDiff4 t) :=
        congrArg hbBilateralSequenceL2Norm houtput_eq
      _ ≤
          hbBilateralSequenceL2Norm (fun t : ℤ =>
            epsilonPart t + diff1 t) +
            hbBilateralSequenceL2Norm scaledDiff4 := htri2.2
      _ ≤ (hbBilateralSequenceL2Norm epsilonPart +
            hbBilateralSequenceL2Norm diff1) +
            hbBilateralSequenceL2Norm scaledDiff4 := by
              exact add_le_add htri1.2 (le_refl _)
      _ ≤ (hbMultiplierEpsilon * hbBilateralSequenceL2Norm s +
            2 * hbBilateralSequenceL2Norm s) +
            (4 / 25 : ℝ) *
              (2 * hbBilateralSequenceL2Norm s) := by
              rw [hepsilon_norm]
              exact add_le_add
                (add_le_add (le_refl _)
                  hdiff1_bound)
                hscaled4_bound
      _ = (hbMultiplierEpsilon + 2 + 8 / 25 : ℝ) *
          hbBilateralSequenceL2Norm s := by ring
  exact ⟨hout, hnorm⟩

set_option maxHeartbeats 2000000 in
private theorem hb_box_characteristic_roots {q a b : ℝ} (hbox : HB_Box q a b) :
    ∃ r₁ r₂ : ℝ,
      0 < r₂ ∧ r₂ < r₁ ∧ r₁ < 1 ∧
        r₁ + r₂ = 1 + b - a * q ∧
        r₁ * r₂ = b ∧
        r₁ ^ 2 = (1 + b - a * q) * r₁ - b ∧
        r₂ ^ 2 = (1 + b - a * q) * r₂ - b := by
  let hD := HB_box_subset_domain hbox
  rcases HB_BOX_ENDPOINT_RANGES hbox with
    ⟨hqlo, hqhi, halo, hahi, hblo, hbhi, hprod, ha2q, ha2q2, hbexpr⟩
  have hq0 : 0 < q := parameterDomain_q_pos hD
  have ha0 : 0 < a := hD.2.2.2.2.1
  have hb0 : 0 < b := by linarith
  have haq_pos : 0 < a * q := mul_pos ha0 hq0
  have haq_upper : a * q < (253 / 10000 : ℝ) := by
    calc
      a * q < a * (11 / 1000 : ℝ) :=
        mul_lt_mul_of_pos_left hqhi ha0
      _ < (23 / 10 : ℝ) * (11 / 1000 : ℝ) :=
        mul_lt_mul_of_pos_right hahi (by norm_num)
      _ = (253 / 10000 : ℝ) := by norm_num
  let α : ℝ := 1 + b - a * q
  have hα_lower : (391 / 250 : ℝ) < α := by
    dsimp [α]
    nlinarith [hblo, haq_upper]
  have hα_pos : 0 < α := by linarith
  have hα_lt_two : α < 2 := by
    dsimp [α]
    nlinarith [hbhi, haq_pos]
  have hdisc : 0 < α ^ 2 - 4 * b := by
    nlinarith [hα_lower, hbhi, sq_nonneg (α - 391 / 250 : ℝ)]
  let Δ : ℝ := α ^ 2 - 4 * b
  let r₁ : ℝ := (α + Real.sqrt Δ) / 2
  let r₂ : ℝ := (α - Real.sqrt Δ) / 2
  have hΔ : 0 < Δ := by simpa [Δ] using hdisc
  have hsqrt_nonneg : 0 ≤ Real.sqrt Δ := Real.sqrt_nonneg _
  have hsqrt_pos : 0 < Real.sqrt Δ := Real.sqrt_pos.2 hΔ
  have hsqrt_sq : (Real.sqrt Δ) ^ 2 = Δ :=
    Real.sq_sqrt (le_of_lt hΔ)
  have hΔ_lt_α_sq : Δ < α ^ 2 := by
    dsimp [Δ]
    nlinarith [hb0]
  have hsqrt_lt_α : Real.sqrt Δ < α := by
    have hsq : (Real.sqrt Δ) ^ 2 < α ^ 2 := by
      simpa [hsqrt_sq] using hΔ_lt_α_sq
    have habs := abs_lt_of_sq_lt_sq hsq (le_of_lt hα_pos)
    simpa [abs_of_nonneg hsqrt_nonneg] using habs
  have hΔ_lt_two_sub_sq : Δ < (2 - α) ^ 2 := by
    dsimp [Δ]
    nlinarith [haq_pos]
  have hsqrt_lt_two_sub : Real.sqrt Δ < 2 - α := by
    have hsq : (Real.sqrt Δ) ^ 2 < (2 - α) ^ 2 := by
      simpa [hsqrt_sq] using hΔ_lt_two_sub_sq
    have habs := abs_lt_of_sq_lt_sq hsq (by linarith : 0 ≤ 2 - α)
    simpa [abs_of_nonneg hsqrt_nonneg] using habs
  have hr₂_pos : 0 < r₂ := by
    dsimp [r₂]
    linarith
  have hr₂_lt_r₁ : r₂ < r₁ := by
    dsimp [r₂, r₁]
    linarith
  have hr₁_lt_one : r₁ < 1 := by
    dsimp [r₁]
    linarith
  have hrsum : r₁ + r₂ = α := by
    dsimp [r₁, r₂]
    ring
  have hrprod : r₁ * r₂ = b := by
    dsimp [r₁, r₂]
    nlinarith [hsqrt_sq]
  have hroot (r : ℝ) (hr : r = r₁ ∨ r = r₂) :
      r ^ 2 = α * r - b := by
    rcases hr with rfl | rfl
    · calc
        r₁ ^ 2 = (r₁ + r₂) * r₁ - r₁ * r₂ := by ring
        _ = α * r₁ - b := by rw [hrsum, hrprod]
    · calc
        r₂ ^ 2 = (r₁ + r₂) * r₂ - r₁ * r₂ := by ring
        _ = α * r₂ - b := by rw [hrsum, hrprod]
  refine ⟨r₁, r₂, hr₂_pos, hr₂_lt_r₁, hr₁_lt_one, ?_, ?_, ?_, ?_⟩
  · simpa [α] using hrsum
  · exact hrprod
  · simpa [α] using hroot r₁ (Or.inl rfl)
  · simpa [α] using hroot r₂ (Or.inr rfl)

set_option maxHeartbeats 2000000 in
private theorem hb_box_impulse_kernel_data {q a b : ℝ} (hbox : HB_Box q a b) :
    ∃ k : ℕ → ℝ,
      k 0 = 1 ∧
        k 1 = 1 + b - a * q ∧
          (∀ n : ℕ,
            k (n + 2) = (1 + b - a * q) * k (n + 1) - b * k n) ∧
            (∀ n : ℕ, 0 ≤ k n) ∧
              Summable k ∧ a * (∑' n : ℕ, k n) = 1 / q := by
  let hD := HB_box_subset_domain hbox
  have hq0 : 0 < q := parameterDomain_q_pos hD
  obtain ⟨r₁, r₂, hr₂_pos, hr₂_lt_r₁, hr₁_lt_one, hrsum, hrprod,
    hr₁_root, hr₂_root⟩ := hb_box_characteristic_roots hbox
  have hr₁_pos : 0 < r₁ := lt_trans hr₂_pos hr₂_lt_r₁
  have hden_pos : 0 < r₁ - r₂ := sub_pos.mpr hr₂_lt_r₁
  have hone₁_pos : 0 < 1 - r₁ := sub_pos.mpr hr₁_lt_one
  have htwo_lt_one : r₂ < 1 := lt_trans hr₂_lt_r₁ hr₁_lt_one
  have hone₂_pos : 0 < 1 - r₂ := sub_pos.mpr htwo_lt_one
  have hgeo₁ : Summable (fun n : ℕ => r₁ ^ n) :=
    summable_geometric_of_lt_one (le_of_lt hr₁_pos) hr₁_lt_one
  have hgeo₂ : Summable (fun n : ℕ => r₂ ^ n) :=
    summable_geometric_of_lt_one (le_of_lt hr₂_pos) htwo_lt_one
  have hshift₁ : Summable (fun n : ℕ => r₁ ^ (n + 1)) := by
    have h := Summable.mul_left r₁ hgeo₁
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using h
  have hshift₂ : Summable (fun n : ℕ => r₂ ^ (n + 1)) := by
    have h := Summable.mul_left r₂ hgeo₂
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using h
  let k : ℕ → ℝ := fun n => (r₁ ^ (n + 1) - r₂ ^ (n + 1)) / (r₁ - r₂)
  have hk_zero : k 0 = 1 := by
    dsimp [k]
    field_simp [ne_of_gt hden_pos]
  have hk_one : k 1 = r₁ + r₂ := by
    dsimp [k]
    have hden_ne : r₁ - r₂ ≠ 0 := ne_of_gt hden_pos
    apply (div_eq_iff hden_ne).2
    ring
  have hk_rec :
      ∀ n : ℕ,
        k (n + 2) = (r₁ + r₂) * k (n + 1) - (r₁ * r₂) * k n := by
    intro n
    dsimp [k]
    have hden_ne : r₁ - r₂ ≠ 0 := ne_of_gt hden_pos
    have hp₁ :
        r₁ ^ (n + 2 + 1) = r₁ ^ (n + 1) * r₁ ^ 2 := by
      rw [show n + 2 + 1 = (n + 1) + 2 by omega, pow_add]
    have hp₂ :
        r₂ ^ (n + 2 + 1) = r₂ ^ (n + 1) * r₂ ^ 2 := by
      rw [show n + 2 + 1 = (n + 1) + 2 by omega, pow_add]
    have hq₁ :
        r₁ ^ (n + 1 + 1) = r₁ ^ (n + 1) * r₁ := by
      rw [pow_succ]
    have hq₂ :
        r₂ ^ (n + 1 + 1) = r₂ ^ (n + 1) * r₂ := by
      rw [pow_succ]
    rw [hp₁, hp₂, hq₁, hq₂]
    field_simp [hden_ne]
    ring
  have hk_nonneg : ∀ n : ℕ, 0 ≤ k n := by
    intro n
    have hpow : r₂ ^ (n + 1) ≤ r₁ ^ (n + 1) :=
      pow_le_pow_left₀ (le_of_lt hr₂_pos) (le_of_lt hr₂_lt_r₁) _
    exact div_nonneg (sub_nonneg.mpr hpow) (le_of_lt hden_pos)
  have hk_summable : Summable k := by
    have hdiff := hshift₁.sub hshift₂
    have hscaled := Summable.mul_left (r₁ - r₂)⁻¹ hdiff
    apply Summable.congr hscaled
    intro n
    simp [k, div_eq_mul_inv, mul_comm]
  have hsum₁ :
      (∑' n : ℕ, r₁ ^ (n + 1)) = r₁ * (1 - r₁)⁻¹ := by
    calc
      (∑' n : ℕ, r₁ ^ (n + 1)) = ∑' n : ℕ, r₁ * r₁ ^ n := by
        apply tsum_congr
        intro n
        rw [pow_succ]
        ring
      _ = r₁ * (∑' n : ℕ, r₁ ^ n) := by
        rw [hgeo₁.tsum_mul_left]
      _ = r₁ * (1 - r₁)⁻¹ := by
        rw [tsum_geometric_of_lt_one (le_of_lt hr₁_pos) hr₁_lt_one]
  have hsum₂ :
      (∑' n : ℕ, r₂ ^ (n + 1)) = r₂ * (1 - r₂)⁻¹ := by
    calc
      (∑' n : ℕ, r₂ ^ (n + 1)) = ∑' n : ℕ, r₂ * r₂ ^ n := by
        apply tsum_congr
        intro n
        rw [pow_succ]
        ring
      _ = r₂ * (∑' n : ℕ, r₂ ^ n) := by
        rw [hgeo₂.tsum_mul_left]
      _ = r₂ * (1 - r₂)⁻¹ := by
        rw [tsum_geometric_of_lt_one (le_of_lt hr₂_pos) htwo_lt_one]
  have hsum_k :
      (∑' n : ℕ, k n) =
        (r₁ - r₂)⁻¹ *
          ((∑' n : ℕ, r₁ ^ (n + 1)) -
            (∑' n : ℕ, r₂ ^ (n + 1))) := by
    calc
      (∑' n : ℕ, k n) =
          ∑' n : ℕ, (r₁ - r₂)⁻¹ *
            (r₁ ^ (n + 1) - r₂ ^ (n + 1)) := by
              apply tsum_congr
              intro n
              simp [k, div_eq_mul_inv, mul_comm]
      _ = (r₁ - r₂)⁻¹ *
          (∑' n : ℕ, (r₁ ^ (n + 1) - r₂ ^ (n + 1))) := by
            rw [tsum_mul_left]
      _ = (r₁ - r₂)⁻¹ *
          ((∑' n : ℕ, r₁ ^ (n + 1)) -
            (∑' n : ℕ, r₂ ^ (n + 1))) := by
              rw [Summable.tsum_sub hshift₁ hshift₂]
  have hsum_k_formula :
      (∑' n : ℕ, k n) = ((1 - r₁) * (1 - r₂))⁻¹ := by
    rw [hsum_k, hsum₁, hsum₂]
    field_simp [ne_of_gt hden_pos, ne_of_gt hone₁_pos, ne_of_gt hone₂_pos]
    ring
  have hmass_den :
      (1 - r₁) * (1 - r₂) = a * q := by
    calc
      (1 - r₁) * (1 - r₂) =
          1 - (r₁ + r₂) + r₁ * r₂ := by ring
      _ = a * q := by rw [hrsum, hrprod]; ring
  have hmass : a * (∑' n : ℕ, k n) = 1 / q := by
    rw [hsum_k_formula, hmass_den]
    have hD := HB_box_subset_domain hbox
    have ha0 : 0 < a := hD.2.2.2.2.1
    field_simp [ne_of_gt hq0, ne_of_gt ha0]
  refine ⟨k, hk_zero, ?_, ?_, ?_, hk_summable, hmass⟩
  · simpa [hrsum] using hk_one
  · intro n
    simpa [hrsum, hrprod] using hk_rec n
  · exact hk_nonneg

set_option maxHeartbeats 2000000 in
private theorem hbPlantResponse_eq_neg_smul_finset_sum
    {q a b : ℝ} {d : ℕ} (input : ℕ → Vec d) {k : ℕ → ℝ}
    (hk_zero : k 0 = 1)
    (hk_one : k 1 = 1 + b - a * q)
    (hk_rec :
      ∀ n : ℕ,
        k (n + 2) = (1 + b - a * q) * k (n + 1) - b * k n) :
  ∀ n : ℕ,
      hbPlantResponse q a b input n =
        -a • (Finset.sum (Finset.range n)
          (fun j => k (n - 1 - j) • input j)) := by
  let α : ℝ := 1 + b - a * q
  let conv : ℕ → Vec d := fun n =>
    Finset.sum (Finset.range n) (fun j => k (n - 1 - j) • input j)
  have hconv_rec :
      ∀ n : ℕ, conv (n + 2) = α • conv (n + 1) - b • conv n + input (n + 1) := by
    intro n
    have hpoint :
        ∀ j : ℕ, j < n →
          k (n + 1 - j) • input j =
            α • (k (n - j) • input j) -
              b • (k (n - 1 - j) • input j) := by
      intro j hj
      have hidx₀ : n - 1 - j + 2 = n + 1 - j := by omega
      have hidx₁ : n - 1 - j + 1 = n - j := by omega
      have hkernel :
          k (n + 1 - j) =
            α * k (n - j) - b * k (n - 1 - j) := by
        have h := hk_rec (n - 1 - j)
        rw [hidx₀, hidx₁] at h
        simpa [α] using h
      rw [hkernel]
      simp only [sub_smul, smul_smul]
    have hsum :
        Finset.sum (Finset.range n) (fun j =>
            k (n + 1 - j) • input j) =
          α • (Finset.sum (Finset.range n) (fun j => k (n - j) • input j)) -
            b • (Finset.sum (Finset.range n)
              (fun j => k (n - 1 - j) • input j)) := by
      calc
        (Finset.sum (Finset.range n) (fun j => k (n + 1 - j) • input j)) =
            Finset.sum (Finset.range n)
              (fun j => (α * k (n - j) - b * k (n - 1 - j)) • input j) := by
                apply Finset.sum_congr rfl
                intro j hj
                simpa [sub_smul, smul_smul] using
                  hpoint j (Finset.mem_range.mp hj)
        _ = α • (Finset.sum (Finset.range n) (fun j => k (n - j) • input j)) -
              b • (Finset.sum (Finset.range n)
                (fun j => k (n - 1 - j) • input j)) := by
                simp [sub_smul, smul_smul, Finset.smul_sum,
                  mul_comm, mul_left_comm, mul_assoc]
    have hsum' :
        Finset.sum (Finset.range n) (fun j =>
            (α * k (n - j) - b * k (n - 1 - j)) • input j) =
          α • (Finset.sum (Finset.range n) (fun j => k (n - j) • input j)) -
            b • (Finset.sum (Finset.range n)
              (fun j => k (n - 1 - j) • input j)) := by
      calc
        Finset.sum (Finset.range n) (fun j =>
            (α * k (n - j) - b * k (n - 1 - j)) • input j) =
            Finset.sum (Finset.range n)
              (fun j => k (n + 1 - j) • input j) := by
                apply Finset.sum_congr rfl
                intro j hj
                simpa [sub_smul, smul_smul] using
                  (hpoint j (Finset.mem_range.mp hj)).symm
        _ = α • (Finset.sum (Finset.range n) (fun j => k (n - j) • input j)) -
              b • (Finset.sum (Finset.range n)
                (fun j => k (n - 1 - j) • input j)) := hsum
    dsimp [conv]
    calc
      (Finset.sum (Finset.range (n + 2))
          (fun j => k (n + 2 - 1 - j) • input j)) =
          Finset.sum (Finset.range (n + 1))
            (fun j => k (n + 1 - j) • input j) +
            k 0 • input (n + 1) := by
              rw [show n + 2 = (n + 1) + 1 by omega,
                Finset.sum_range_succ]
              simp only [Nat.add_sub_cancel, Nat.sub_self]
      _ = Finset.sum (Finset.range n) (fun j => k (n + 1 - j) • input j) +
            k 1 • input n + k 0 • input (n + 1) := by
              rw [Finset.sum_range_succ]
              simp only [Nat.add_sub_cancel_left]
      _ = Finset.sum (Finset.range n)
            (fun j => (α * k (n - j) - b * k (n - 1 - j)) • input j) +
            α • (k 0 • input n) + k 0 • input (n + 1) := by
              rw [hk_one]
              rw [hsum, hsum']
              simp [α, hk_zero, sub_smul, smul_smul, Finset.smul_sum,
                mul_comm, mul_left_comm, mul_assoc]
      _ = α • (Finset.sum (Finset.range (n + 1))
              (fun j => k (n - j) • input j)) -
            b • (Finset.sum (Finset.range n)
              (fun j => k (n - 1 - j) • input j)) +
              input (n + 1) := by
              rw [hsum', Finset.sum_range_succ]
              simp [hk_zero, sub_smul, smul_add, add_smul, smul_sub, smul_smul,
                Finset.smul_sum, mul_comm, mul_left_comm, mul_assoc]
              abel
  have hresp : ∀ n : ℕ, hbPlantResponse q a b input n = -a • conv n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        cases n with
        | zero =>
            simp [hbPlantResponse, conv]
        | succ n =>
            cases n with
            | zero =>
                simp [hbPlantResponse, conv, hk_zero]
            | succ n =>
                rw [hbPlantResponse, ih (n + 1) (by omega),
                  ih n (by omega), hconv_rec n]
                simp only [conv, smul_add, add_smul, smul_sub, sub_smul,
                  smul_smul, neg_smul]
                module
  intro n
  simpa [conv] using hresp n

private theorem hbPlantResponse_sq_le_lagged_energy
    {q a b : ℝ} {d : ℕ} (input : ℕ → Vec d) {k : ℕ → ℝ}
    (hk_zero : k 0 = 1)
    (hk_one : k 1 = 1 + b - a * q)
    (hk_rec :
      ∀ n : ℕ,
        k (n + 2) = (1 + b - a * q) * k (n + 1) - b * k n)
    (hk_nonneg : ∀ n : ℕ, 0 ≤ k n) (n : ℕ) :
    ‖hbPlantResponse q a b input n‖ ^ 2 ≤
      a ^ 2 *
        (Finset.sum (Finset.range n) (fun j => k (n - 1 - j))) *
          (Finset.sum (Finset.range n)
            (fun j => k (n - 1 - j) * ‖input j‖ ^ 2)) := by
  have hresponse :=
    hbPlantResponse_eq_neg_smul_finset_sum input hk_zero hk_one hk_rec n
  by_cases hn : n = 0
  · subst n
    simp [hbPlantResponse]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let w : ℕ → ℝ := fun j => k (n - 1 - j)
    let W : ℝ := Finset.sum (Finset.range n) w
    have hw_nonneg : ∀ j ∈ Finset.range n, 0 ≤ w j := by
      intro j hj
      exact hk_nonneg (n - 1 - j)
    have hw_pos : 0 < W := by
      dsimp [W]
      apply Finset.sum_pos' hw_nonneg
      refine ⟨n - 1, ?_, ?_⟩
      · exact Finset.mem_range.mpr (by omega)
      · simp [w, hk_zero]
    let qw : ℕ → ℝ := fun j => W⁻¹ * w j
    have hqsum : Finset.sum (Finset.range n) qw = 1 := by
      dsimp [qw, W]
      rw [← Finset.mul_sum]
      exact inv_mul_cancel₀ (ne_of_gt hw_pos)
    have hq_nonneg : ∀ j ∈ Finset.range n, 0 ≤ qw j := by
      intro j hj
      exact mul_nonneg (inv_nonneg.mpr hw_pos.le) (hw_nonneg j hj)
    have hmean :=
      Real.pow_arith_mean_le_arith_mean_pow
        (s := Finset.range n) (w := qw)
        (z := fun j => ‖input j‖) hq_nonneg hqsum
        (fun j _ => norm_nonneg _) 2
    have hnorm :
        ‖Finset.sum (Finset.range n) (fun j => w j • input j)‖ ≤
          Finset.sum (Finset.range n) (fun j => w j * ‖input j‖) := by
      calc
        ‖Finset.sum (Finset.range n) (fun j => w j • input j)‖ ≤
            Finset.sum (Finset.range n)
              (fun j => ‖w j • input j‖) := by
                simpa using
                  (norm_sum_le (s := Finset.range n)
                    (f := fun j => w j • input j))
        _ = Finset.sum (Finset.range n) (fun j => w j * ‖input j‖) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [norm_smul, Real.norm_of_nonneg (hw_nonneg j hj)]
    have hA :
        Finset.sum (Finset.range n) (fun j => w j * ‖input j‖) =
          W * Finset.sum (Finset.range n)
            (fun j => qw j * ‖input j‖) := by
      dsimp [qw]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      field_simp [ne_of_gt hw_pos]
    have hB :
        Finset.sum (Finset.range n) (fun j =>
            qw j * ‖input j‖ ^ 2) =
          W⁻¹ * Finset.sum (Finset.range n)
            (fun j => w j * ‖input j‖ ^ 2) := by
      dsimp [qw]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have hweighted :
        (Finset.sum (Finset.range n) (fun j => w j * ‖input j‖)) ^ 2 ≤
          W * Finset.sum (Finset.range n)
            (fun j => w j * ‖input j‖ ^ 2) := by
      rw [hA]
      have hscaled := mul_le_mul_of_nonneg_left hmean (sq_nonneg W)
      rw [hB] at hscaled
      field_simp [ne_of_gt hw_pos] at hscaled ⊢
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hscaled
    have hsum_sq :
        ‖Finset.sum (Finset.range n) (fun j => w j • input j)‖ ^ 2 ≤
          W * Finset.sum (Finset.range n)
            (fun j => w j * ‖input j‖ ^ 2) := by
      have hsum_nonneg :
          0 ≤ ‖Finset.sum (Finset.range n) (fun j => w j • input j)‖ :=
        norm_nonneg _
      have hnorm_sq :
          ‖Finset.sum (Finset.range n) (fun j => w j • input j)‖ ^ 2 ≤
            (Finset.sum (Finset.range n) (fun j => w j * ‖input j‖)) ^ 2 := by
        nlinarith [hnorm]
      exact hnorm_sq.trans hweighted
    rw [hresponse]
    calc
      ‖-a • Finset.sum (Finset.range n) (fun j => w j • input j)‖ ^ 2 =
          a ^ 2 *
            ‖Finset.sum (Finset.range n) (fun j => w j • input j)‖ ^ 2 := by
              rw [norm_smul, norm_neg, Real.norm_eq_abs, mul_pow, sq_abs]
      _ ≤ a ^ 2 *
          (W * Finset.sum (Finset.range n)
            (fun j => w j * ‖input j‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum_sq (sq_nonneg a)
      _ = a ^ 2 *
          (Finset.sum (Finset.range n) (fun j => k (n - 1 - j))) *
            (Finset.sum (Finset.range n)
              (fun j => k (n - 1 - j) * ‖input j‖ ^ 2)) := by
            dsimp [W, w]
            ring

private theorem hb_triangular_kernel_energy_bound
    {N : ℕ} {k f : ℕ → ℝ} (hk : Summable k)
    (hk_nonneg : ∀ n : ℕ, 0 ≤ k n)
    (hf_nonneg : ∀ n : ℕ, 0 ≤ f n) :
    (Finset.sum (Finset.range N) (fun n =>
        Finset.sum (Finset.range n)
          (fun j => k (n - 1 - j) * f j))) ≤
      (∑' n : ℕ, k n) *
        Finset.sum (Finset.range N) f := by
  have hinner (j : ℕ) (hj : j < N) :
      Finset.sum (Finset.range N) (fun n =>
          if j < n then k (n - 1 - j) else 0) =
        Finset.sum (Finset.range (N - (j + 1))) k := by
    have hfilter :
        (Finset.range N).filter (fun n => j < n) =
          Finset.Ico (j + 1) N := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [← Finset.sum_filter]
    rw [hfilter, Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro m hm
    congr 1
    omega
  have hpad (n : ℕ) (hn : n ≤ N) :
      Finset.sum (Finset.range n) (fun j =>
          k (n - 1 - j) * f j) =
        Finset.sum (Finset.range N) (fun j =>
          if j < n then k (n - 1 - j) * f j else 0) := by
    calc
      Finset.sum (Finset.range n) (fun j =>
          k (n - 1 - j) * f j) =
          Finset.sum (Finset.range n) (fun j =>
            if j < n then k (n - 1 - j) * f j else 0) := by
              apply Finset.sum_congr rfl
              intro j hj'
              simp [Finset.mem_range.mp hj']
      _ = Finset.sum (Finset.range N) (fun j =>
          if j < n then k (n - 1 - j) * f j else 0) := by
            apply Finset.sum_subset (Finset.range_mono hn)
            intro j hj' hjn
            have hjn' : ¬j < n := by
              simpa [Finset.mem_range] using hjn
            simp [hjn']
  have htri :
      (Finset.sum (Finset.range N) (fun n =>
          Finset.sum (Finset.range n)
            (fun j => k (n - 1 - j) * f j))) =
        Finset.sum (Finset.range N) (fun j =>
          Finset.sum (Finset.range N) (fun n =>
            if j < n then k (n - 1 - j) * f j else 0)) := by
    calc
      (Finset.sum (Finset.range N) (fun n =>
          Finset.sum (Finset.range n)
            (fun j => k (n - 1 - j) * f j))) =
          Finset.sum (Finset.range N) (fun n =>
            Finset.sum (Finset.range N) (fun j =>
              if j < n then k (n - 1 - j) * f j else 0)) := by
                apply Finset.sum_congr rfl
                intro n hn
                exact hpad n (Finset.mem_range.mp hn).le
      _ = Finset.sum (Finset.range N) (fun j =>
          Finset.sum (Finset.range N) (fun n =>
            if j < n then k (n - 1 - j) * f j else 0)) := by
            rw [Finset.sum_comm]
  rw [htri]
  have hpoint (j : ℕ) (hj : j ∈ Finset.range N) :
      Finset.sum (Finset.range N) (fun n =>
          if j < n then k (n - 1 - j) * f j else 0) ≤
        (∑' n : ℕ, k n) * f j := by
    have hjN : j < N := Finset.mem_range.mp hj
    have hkernel :
        Finset.sum (Finset.range N) (fun n =>
            if j < n then k (n - 1 - j) else 0) ≤
          ∑' n : ℕ, k n := by
      rw [hinner j hjN]
      exact hk.sum_le_tsum _ (fun n _ => hk_nonneg n)
    calc
      Finset.sum (Finset.range N) (fun n =>
          if j < n then k (n - 1 - j) * f j else 0) =
        Finset.sum (Finset.range N) (fun n =>
          (if j < n then k (n - 1 - j) else 0) * f j) := by
            apply Finset.sum_congr rfl
            intro n hn
            by_cases h : j < n <;> simp [h]
      _ = (Finset.sum (Finset.range N) (fun n =>
          if j < n then k (n - 1 - j) else 0)) * f j := by
            rw [Finset.sum_mul]
      _ ≤ (∑' n : ℕ, k n) * f j :=
        mul_le_mul_of_nonneg_right hkernel (hf_nonneg j)
  calc
    Finset.sum (Finset.range N) (fun j =>
        Finset.sum (Finset.range N) (fun n =>
          if j < n then k (n - 1 - j) * f j else 0)) ≤
      Finset.sum (Finset.range N) (fun j =>
        (∑' n : ℕ, k n) * f j) := by
          apply Finset.sum_le_sum
          intro j hj
          exact hpoint j hj
    _ = (∑' n : ℕ, k n) * Finset.sum (Finset.range N) f := by
      rw [Finset.mul_sum]

private theorem hbPlant_prefix_energy_bound
    {q a b : ℝ} (hbox : HB_Box q a b) {d : ℕ}
    (input : ℕ → Vec d) :
    ∀ N : ℕ,
      Finset.sum (Finset.range N)
          (fun n => ‖hbPlantResponse q a b input n‖ ^ 2) ≤
        (1 / q) ^ 2 *
          Finset.sum (Finset.range N) (fun n => ‖input n‖ ^ 2) := by
  obtain ⟨k, hk_zero, hk_one, hk_rec, hk_nonneg, hk_summable, hmass⟩ :=
    hb_box_impulse_kernel_data hbox
  let K : ℝ := ∑' n : ℕ, k n
  have hmass' : a * K = 1 / q := by
    simpa [K] using hmass
  intro N
  have hpoint (n : ℕ) :
      ‖hbPlantResponse q a b input n‖ ^ 2 ≤
        a ^ 2 * K *
          Finset.sum (Finset.range n)
            (fun j => k (n - 1 - j) * ‖input j‖ ^ 2) := by
    have hW :
        Finset.sum (Finset.range n) (fun j => k (n - 1 - j)) ≤ K := by
      rw [Finset.sum_range_reflect]
      exact hk_summable.sum_le_tsum _ (fun j _ => hk_nonneg j)
    have hinner_nonneg :
        0 ≤ Finset.sum (Finset.range n)
          (fun j => k (n - 1 - j) * ‖input j‖ ^ 2) := by
      apply Finset.sum_nonneg
      intro j hj
      exact mul_nonneg (hk_nonneg (n - 1 - j)) (sq_nonneg _)
    have hweighted :
        a ^ 2 *
            (Finset.sum (Finset.range n) (fun j => k (n - 1 - j))) *
              Finset.sum (Finset.range n)
                (fun j => k (n - 1 - j) * ‖input j‖ ^ 2) ≤
          a ^ 2 * K *
            Finset.sum (Finset.range n)
              (fun j => k (n - 1 - j) * ‖input j‖ ^ 2) := by
      have hmul := mul_le_mul_of_nonneg_right hW hinner_nonneg
      have hmul' := mul_le_mul_of_nonneg_left hmul (sq_nonneg a)
      simpa [mul_assoc] using hmul'
    exact
      (hbPlantResponse_sq_le_lagged_energy input hk_zero hk_one hk_rec
        hk_nonneg n).trans hweighted
  have hsum_point :
      Finset.sum (Finset.range N)
          (fun n => ‖hbPlantResponse q a b input n‖ ^ 2) ≤
        Finset.sum (Finset.range N) (fun n =>
          a ^ 2 * K *
            Finset.sum (Finset.range n)
              (fun j => k (n - 1 - j) * ‖input j‖ ^ 2)) := by
    apply Finset.sum_le_sum
    intro n hn
    exact hpoint n
  have htri := hb_triangular_kernel_energy_bound (N := N) hk_summable hk_nonneg
    (fun n => sq_nonneg (‖input n‖))
  calc
    Finset.sum (Finset.range N)
          (fun n => ‖hbPlantResponse q a b input n‖ ^ 2) ≤
        Finset.sum (Finset.range N) (fun n =>
          a ^ 2 * K *
            Finset.sum (Finset.range n)
              (fun j => k (n - 1 - j) * ‖input j‖ ^ 2)) := hsum_point
    _ = (a ^ 2 * K) *
          Finset.sum (Finset.range N) (fun n =>
            Finset.sum (Finset.range n)
              (fun j => k (n - 1 - j) * ‖input j‖ ^ 2)) := by
            rw [Finset.mul_sum]
    _ ≤ (a ^ 2 * K) *
          (K * Finset.sum (Finset.range N)
            (fun n => ‖input n‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left htri
        (mul_nonneg (sq_nonneg a) (by
          exact tsum_nonneg hk_nonneg))
    _ = (a * K) ^ 2 *
          Finset.sum (Finset.range N) (fun n => ‖input n‖ ^ 2) := by
            ring
    _ = (1 / q) ^ 2 *
          Finset.sum (Finset.range N) (fun n => ‖input n‖ ^ 2) := by
            rw [hmass']

private theorem hbPlant_l2_bound_on_box
    {q a b : ℝ} (hbox : HB_Box q a b) {d : ℕ}
    (input : ℕ → Vec d) :
    hbSequenceInL2 input →
      hbSequenceInL2 (hbPlantResponse q a b input) ∧
        hbSequenceL2Norm (hbPlantResponse q a b input) ≤
          (1 / q) * hbSequenceL2Norm input := by
  intro hinput
  have hinput_summable :
      Summable (fun n : ℕ => ‖input n‖ ^ 2) := by
    simpa [hbSequenceInL2] using hinput
  have hinput_nonneg :
      ∀ n : ℕ, 0 ≤ ‖input n‖ ^ 2 := by
    intro n
    exact sq_nonneg _
  have hprefix_bound (N : ℕ) :
      Finset.sum (Finset.range N)
          (fun n => ‖hbPlantResponse q a b input n‖ ^ 2) ≤
        (1 / q) ^ 2 *
          (∑' n : ℕ, ‖input n‖ ^ 2) := by
    exact
      (hbPlant_prefix_energy_bound hbox input N).trans
        (mul_le_mul_of_nonneg_left
          (hinput_summable.sum_le_tsum _ (fun n _ => hinput_nonneg n))
          (sq_nonneg (1 / q)))
  have houtput_summable :
      Summable (fun n : ℕ => ‖hbPlantResponse q a b input n‖ ^ 2) :=
    summable_of_sum_range_le
      (fun n => sq_nonneg (‖hbPlantResponse q a b input n‖))
      hprefix_bound
  have henergy :
      (∑' n : ℕ, ‖hbPlantResponse q a b input n‖ ^ 2) ≤
        (1 / q) ^ 2 * (∑' n : ℕ, ‖input n‖ ^ 2) :=
    Real.tsum_le_of_sum_range_le
      (fun n => sq_nonneg (‖hbPlantResponse q a b input n‖))
      hprefix_bound
  have hqpos : 0 < (1 / q : ℝ) := by
    exact one_div_pos.mpr (parameterDomain_q_pos (HB_box_subset_domain hbox))
  refine ⟨houtput_summable, ?_⟩
  unfold hbSequenceL2Norm hbSequenceEnergy
  calc
    Real.sqrt (∑' n : ℕ, ‖hbPlantResponse q a b input n‖ ^ 2) ≤
        Real.sqrt ((1 / q) ^ 2 * (∑' n : ℕ, ‖input n‖ ^ 2)) :=
      Real.sqrt_le_sqrt henergy
    _ = (1 / q) * Real.sqrt (∑' n : ℕ, ‖input n‖ ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg (1 / q))]
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hqpos]

/-- Source-derived well-definedness bridge for the plant gain on the box. -/
theorem hbPlantL2Gain_is_bound_on_box {q a b : ℝ} (hbox : HB_Box q a b) :
    hbPlantL2GainBound q a b (hbPlantL2Gain q a b) := by
  let B : ℝ := 1 / q
  let S : Set ℝ := {C : ℝ | hbPlantL2GainBound q a b C}
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact (one_div_pos.mpr
      (parameterDomain_q_pos (HB_box_subset_domain hbox))).le
  have hB_bound : hbPlantL2GainBound q a b B := by
    refine ⟨hB_nonneg, ?_⟩
    intro d input hinput
    simpa [B] using hbPlant_l2_bound_on_box hbox input hinput
  have hS_nonempty : S.Nonempty := by
    refine ⟨B, ?_⟩
    simpa [S] using hB_bound
  have hS_bddBelow : BddBelow S := by
    refine ⟨0, ?_⟩
    intro C hC
    have hC' : hbPlantL2GainBound q a b C := by
      simpa [S] using hC
    exact hC'.1
  have hgain_nonneg : 0 ≤ sInf S := by
    apply le_csInf hS_nonempty
    intro C hC
    have hC' : hbPlantL2GainBound q a b C := by
      simpa [S] using hC
    exact hC'.1
  have hgain_le_B : sInf S ≤ B := by
    apply csInf_le hS_bddBelow
    simpa [S] using hB_bound
  unfold hbPlantL2GainBound hbPlantL2Gain
  constructor
  · simpa [S] using hgain_nonneg
  · intro d input hinput
    have hfinite := hbPlant_l2_bound_on_box hbox input hinput
    refine ⟨hfinite.1, ?_⟩
    have hout_nonneg :
        0 ≤ hbSequenceL2Norm (hbPlantResponse q a b input) :=
      Real.sqrt_nonneg _
    have hin_nonneg : 0 ≤ hbSequenceL2Norm input :=
      Real.sqrt_nonneg _
    by_cases hzero : hbSequenceL2Norm input = 0
    · have hout_le_zero :
          hbSequenceL2Norm (hbPlantResponse q a b input) ≤ 0 := by
        calc
          hbSequenceL2Norm (hbPlantResponse q a b input) ≤
              B * hbSequenceL2Norm input := by
                simpa [B] using hfinite.2
          _ = 0 := by rw [hzero, mul_zero]
      have hout_zero :
          hbSequenceL2Norm (hbPlantResponse q a b input) = 0 :=
        le_antisymm hout_le_zero hout_nonneg
      rw [hzero, mul_zero]
      exact hout_zero.le
    · have hin_pos : 0 < hbSequenceL2Norm input :=
        lt_of_le_of_ne hin_nonneg (Ne.symm hzero)
      have hratio_lower :
          ∀ C ∈ S,
            hbSequenceL2Norm (hbPlantResponse q a b input) /
                hbSequenceL2Norm input ≤ C := by
        intro C hC
        have hC' : hbPlantL2GainBound q a b C := by
          simpa [S] using hC
        have hC_norm := (hC'.2 input hinput).2
        apply (div_le_iff₀ hin_pos).2
        exact hC_norm
      have hratio :
          hbSequenceL2Norm (hbPlantResponse q a b input) /
              hbSequenceL2Norm input ≤ sInf S :=
        le_csInf hS_nonempty hratio_lower
      have hnorm :
          hbSequenceL2Norm (hbPlantResponse q a b input) ≤
            sInf S * hbSequenceL2Norm input :=
        (div_le_iff₀ hin_pos).mp hratio
      simpa [S] using hnorm

/-- Source-derived well-definedness bridge for the finite-lag multiplier gain. -/
theorem hbMultiplierL2Gain_is_bound :
    hbMultiplierL2GainBound hbMultiplierL2Gain := by
  let B : ℝ := hbMultiplierEpsilon + 2 + 8 / 25
  let S : Set ℝ := {C : ℝ | hbMultiplierL2GainBound C}
  have hB_nonneg : 0 ≤ B := by
    norm_num [B, hbMultiplierEpsilon]
  have hB_bound : hbMultiplierL2GainBound B := by
    refine ⟨hB_nonneg, ?_⟩
    intro d s hs
    simpa [B] using hb_multiplier_finite_lag_l2_bound hs
  have hS_nonempty : S.Nonempty := by
    refine ⟨B, ?_⟩
    simpa [S] using hB_bound
  have hS_bddBelow : BddBelow S := by
    refine ⟨0, ?_⟩
    intro C hC
    have hC' : hbMultiplierL2GainBound C := by
      simpa [S] using hC
    exact hC'.1
  have hgain_nonneg : 0 ≤ sInf S := by
    apply le_csInf hS_nonempty
    intro C hC
    have hC' : hbMultiplierL2GainBound C := by
      simpa [S] using hC
    exact hC'.1
  have hgain_le_B : sInf S ≤ B := by
    apply csInf_le hS_bddBelow
    simpa [S] using hB_bound
  have hB_lt_three : B < 3 := by
    norm_num [B, hbMultiplierEpsilon]
  have hgain_lt_three : sInf S < 3 :=
    lt_of_le_of_lt hgain_le_B hB_lt_three
  unfold hbMultiplierL2GainBound hbMultiplierL2Gain
  constructor
  · simpa [S] using hgain_nonneg
  · intro d s hs
    have hfinite := hb_multiplier_finite_lag_l2_bound hs
    refine ⟨hfinite.1, ?_⟩
    have hout_nonneg :
        0 ≤ hbBilateralSequenceL2Norm
          (fun t : ℤ => hbMultiplierTimeDomain s t) :=
      Real.sqrt_nonneg _
    have hin_nonneg : 0 ≤ hbBilateralSequenceL2Norm s :=
      Real.sqrt_nonneg _
    by_cases hzero : hbBilateralSequenceL2Norm s = 0
    · have hout_le_zero :
          hbBilateralSequenceL2Norm
              (fun t : ℤ => hbMultiplierTimeDomain s t) ≤ 0 := by
        calc
          hbBilateralSequenceL2Norm
              (fun t : ℤ => hbMultiplierTimeDomain s t) ≤
              B * hbBilateralSequenceL2Norm s := by
                simpa [B] using hfinite.2
          _ = 0 := by rw [hzero, mul_zero]
      have hout_zero :
          hbBilateralSequenceL2Norm
              (fun t : ℤ => hbMultiplierTimeDomain s t) = 0 :=
        le_antisymm hout_le_zero hout_nonneg
      rw [hzero, mul_zero]
      exact hout_zero.le
    · have hin_pos : 0 < hbBilateralSequenceL2Norm s :=
        lt_of_le_of_ne hin_nonneg (Ne.symm hzero)
      have hratio_lower :
          ∀ C ∈ S,
            hbBilateralSequenceL2Norm
                (fun t : ℤ => hbMultiplierTimeDomain s t) /
                hbBilateralSequenceL2Norm s ≤ C := by
        intro C hC
        have hC' : hbMultiplierL2GainBound C := by
          simpa [S] using hC
        have hC_norm := (hC'.2 s hs).2
        apply (div_le_iff₀ hin_pos).2
        exact hC_norm
      have hratio :
          hbBilateralSequenceL2Norm
              (fun t : ℤ => hbMultiplierTimeDomain s t) /
              hbBilateralSequenceL2Norm s ≤ sInf S :=
        le_csInf hS_nonempty hratio_lower
      have hnorm :
          hbBilateralSequenceL2Norm
              (fun t : ℤ => hbMultiplierTimeDomain s t) ≤
              sInf S * hbBilateralSequenceL2Norm s :=
        (div_le_iff₀ hin_pos).mp hratio
      simpa [S] using hnorm

/-- The source D8/D9 frequency margin `eta=1/2000`. -/
def hbD9Eta : ℝ := 1 / 2000

/-- The source constant `C_0=1+g L_0 m / eta`. -/
def hbD9C0 (q a b : ℝ) : ℝ :=
  1 + hbPlantL2Gain q a b * hbL0 q * hbMultiplierL2Gain / hbD9Eta

/-- The homotopy input `p=tau D(x)` from D9. -/
def hbHomotopyInput {q : ℝ} {d : ℕ} (hq : 0 < q)
    (hf : AdmissibleObjective q d) (τ : ℝ) (x : ℕ → Vec d) :
    ℕ → Vec d :=
  fun t : ℕ => τ • hbCenteredNonlinearity hq hf (x t)

/-- Source D9 loop equation for a homotopy parameter `tau`. -/
def hbHomotopyLoopEquation {q : ℝ} {d : ℕ} (hq : 0 < q) (a b : ℝ)
    (hf : AdmissibleObjective q d) (τ : ℝ) (e x : ℕ → Vec d) : Prop :=
  let input := hbHomotopyInput hq hf τ x
  ∀ t : ℕ, x t = e t + hbPlantResponse q a b input t

/-- Finite-prefix truncation `P_n`: keep times `0,...,n` and zero the tail. -/
def hbFinitePrefix {d : ℕ} (n : ℕ) (x : ℕ → Vec d) : ℕ → Vec d :=
  fun t : ℕ => if t ≤ n then x t else 0

private theorem hbD9_zeroExtension_oneSided_to_bilateral
    {d : ℕ} (x : ℕ → Vec d) (hx : hbSequenceInL2 x) :
    let zext : ℤ → Vec d := Function.extend Int.ofNat x 0
    hbBilateralSequenceInL2 zext ∧
      hbBilateralSequenceL2Norm zext = hbSequenceL2Norm x := by
  dsimp
  let zext : ℤ → Vec d := Function.extend Int.ofNat x 0
  have hnorm_ext :
      (fun t : ℤ => ‖zext t‖ ^ 2) =
        Function.extend Int.ofNat (fun n : ℕ => ‖x n‖ ^ 2) 0 := by
    funext t
    by_cases ht : 0 ≤ t
    · have ht' : t = (t.toNat : ℤ) := Int.eq_natCast_toNat.mpr ht
      rw [ht']
      change
        ‖Function.extend Int.ofNat x 0 (t.toNat : ℤ)‖ ^ 2 =
          Function.extend Int.ofNat (fun n : ℕ => ‖x n‖ ^ 2) 0
            (t.toNat : ℤ)
      have hvec :
          Function.extend Int.ofNat x 0 (t.toNat : ℤ) = x t.toNat :=
        Int.ofNat_injective.extend_apply x 0 (t.toNat)
      have hscalar :
          Function.extend Int.ofNat (fun n : ℕ => ‖x n‖ ^ 2) 0
              (t.toNat : ℤ) =
            ‖x t.toNat‖ ^ 2 :=
        Int.ofNat_injective.extend_apply (fun n : ℕ => ‖x n‖ ^ 2) 0
          (t.toNat)
      rw [hvec, hscalar]
    · have ht' : t < 0 := lt_of_not_ge ht
      have hnot : ¬∃ n : ℕ, (n : ℤ) = t := by
        rintro ⟨n, hn⟩
        apply ht
        rw [← hn]
        exact Int.natCast_nonneg _
      have hvec : Function.extend Int.ofNat x 0 t = 0 :=
        Function.extend_apply' _ _ _ hnot
      have hscalar :
          Function.extend Int.ofNat (fun n : ℕ => ‖x n‖ ^ 2) 0 t = 0 :=
        Function.extend_apply' _ _ _ hnot
      dsimp [zext]
      rw [hvec, hscalar]
      simp
  have hscalar :
      Summable (Function.extend Int.ofNat (fun n : ℕ => ‖x n‖ ^ 2) 0) := by
    exact (summable_extend_zero Int.ofNat_injective).2 hx
  have hzext : Summable (fun t : ℤ => ‖zext t‖ ^ 2) := by
    rw [hnorm_ext]
    exact hscalar
  refine ⟨hzext, ?_⟩
  unfold hbBilateralSequenceL2Norm hbBilateralSequenceEnergy
  rw [hnorm_ext]
  rw [tsum_extend_zero Int.ofNat_injective]
  rfl

private theorem hb_sequence_l2_norm_add_le
    {d : ℕ} {u v : ℕ → Vec d}
    (hu : hbSequenceInL2 u) (hv : hbSequenceInL2 v) :
    hbSequenceInL2 (fun n : ℕ => u n + v n) ∧
      hbSequenceL2Norm (fun n : ℕ => u n + v n) ≤
        hbSequenceL2Norm u + hbSequenceL2Norm v := by
  let zu : ℤ → Vec d := Function.extend Int.ofNat u 0
  let zv : ℤ → Vec d := Function.extend Int.ofNat v 0
  let zsum : ℤ → Vec d := Function.extend Int.ofNat (fun n : ℕ => u n + v n) 0
  have hzu := hbD9_zeroExtension_oneSided_to_bilateral u hu
  have hzv := hbD9_zeroExtension_oneSided_to_bilateral v hv
  have hsum_ext : zsum = fun t : ℤ => zu t + zv t := by
    funext t
    by_cases ht : 0 ≤ t
    · have ht' : t = (t.toNat : ℤ) := Int.eq_natCast_toNat.mpr ht
      have hzsum :
          zsum t = u t.toNat + v t.toNat := by
        calc
          zsum t = zsum (t.toNat : ℤ) := congrArg zsum ht'
          _ = u t.toNat + v t.toNat := by
            change Function.extend Int.ofNat (fun n : ℕ => u n + v n) 0
                (t.toNat : ℤ) = u t.toNat + v t.toNat
            exact Int.ofNat_injective.extend_apply
              (fun n : ℕ => u n + v n) 0 (t.toNat)
      have hzu' : zu t = u t.toNat := by
        calc
          zu t = zu (t.toNat : ℤ) := congrArg zu ht'
          _ = u t.toNat := by
            change Function.extend Int.ofNat u 0 (t.toNat : ℤ) = u t.toNat
            exact Int.ofNat_injective.extend_apply u 0 (t.toNat)
      have hzv' : zv t = v t.toNat := by
        calc
          zv t = zv (t.toNat : ℤ) := congrArg zv ht'
          _ = v t.toNat := by
            change Function.extend Int.ofNat v 0 (t.toNat : ℤ) = v t.toNat
            exact Int.ofNat_injective.extend_apply v 0 (t.toNat)
      rw [hzsum, hzu', hzv']
    · have ht' : t < 0 := lt_of_not_ge ht
      have hnot : ¬∃ n : ℕ, (n : ℤ) = t := by
        rintro ⟨n, hn⟩
        apply ht
        rw [← hn]
        exact Int.natCast_nonneg _
      have hzsum : zsum t = 0 :=
        Function.extend_apply' _ _ _ hnot
      have hzu' : zu t = 0 :=
        Function.extend_apply' _ _ _ hnot
      have hzv' : zv t = 0 :=
        Function.extend_apply' _ _ _ hnot
      rw [hzsum, hzu', hzv']
      simp
  have hsum_b :
      hbBilateralSequenceInL2 (fun t : ℤ => zu t + zv t) ∧
        hbBilateralSequenceL2Norm (fun t : ℤ => zu t + zv t) ≤
          hbBilateralSequenceL2Norm zu + hbBilateralSequenceL2Norm zv :=
    hb_bilateral_l2_norm_add_le hzu.1 hzv.1
  have hsum_z :
      hbBilateralSequenceInL2 zsum ∧
        hbBilateralSequenceL2Norm zsum ≤
          hbBilateralSequenceL2Norm zu + hbBilateralSequenceL2Norm zv := by
    rw [hsum_ext]
    exact hsum_b
  have hsum_one :
      hbSequenceInL2 (fun n : ℕ => u n + v n) := by
    unfold hbSequenceInL2
    apply (summable_extend_zero Int.ofNat_injective).1
    have hnorm :
        (fun t : ℤ => ‖zsum t‖ ^ 2) =
          Function.extend Int.ofNat
            (fun n : ℕ => ‖u n + v n‖ ^ 2) 0 := by
      funext t
      by_cases ht : 0 ≤ t
      · have ht' : t = (t.toNat : ℤ) := Int.eq_natCast_toNat.mpr ht
        have hzsum_nat :
            zsum (t.toNat : ℤ) = u t.toNat + v t.toNat := by
          change Function.extend Int.ofNat (fun n : ℕ => u n + v n) 0
              (t.toNat : ℤ) = u t.toNat + v t.toNat
          exact Int.ofNat_injective.extend_apply
            (fun n : ℕ => u n + v n) 0 (t.toNat)
        calc
          ‖zsum t‖ ^ 2 = ‖zsum (t.toNat : ℤ)‖ ^ 2 :=
            congrArg (fun w : ℤ => ‖zsum w‖ ^ 2) ht'
          _ = ‖u t.toNat + v t.toNat‖ ^ 2 := by rw [hzsum_nat]
          _ = Function.extend Int.ofNat
              (fun n : ℕ => ‖u n + v n‖ ^ 2) 0
              (t.toNat : ℤ) := by
                symm
                exact Int.ofNat_injective.extend_apply
                  (fun n : ℕ => ‖u n + v n‖ ^ 2) 0 (t.toNat)
          _ = Function.extend Int.ofNat
              (fun n : ℕ => ‖u n + v n‖ ^ 2) 0 t := by
                exact congrArg
                  (Function.extend Int.ofNat
                    (fun n : ℕ => ‖u n + v n‖ ^ 2) 0) ht'.symm
      · have ht' : t < 0 := lt_of_not_ge ht
        have hnot : ¬∃ n : ℕ, (n : ℤ) = t := by
          rintro ⟨n, hn⟩
          apply ht
          rw [← hn]
          exact Int.natCast_nonneg _
        have hzsum : zsum t = 0 :=
          Function.extend_apply' _ _ _ hnot
        have hscalar :
            Function.extend Int.ofNat
              (fun n : ℕ => ‖u n + v n‖ ^ 2) 0 t = 0 :=
          Function.extend_apply' _ _ _ hnot
        rw [hzsum, hscalar]
        simp
    rw [← hnorm]
    exact hsum_z.1
  have hnorm_sum :
      hbBilateralSequenceL2Norm zsum =
        hbSequenceL2Norm (fun n : ℕ => u n + v n) :=
    by
      simpa [zsum] using
        (hbD9_zeroExtension_oneSided_to_bilateral
          (fun n : ℕ => u n + v n) hsum_one).2
  have hnorm_u :
      hbBilateralSequenceL2Norm zu = hbSequenceL2Norm u := hzu.2
  have hnorm_v :
      hbBilateralSequenceL2Norm zv = hbSequenceL2Norm v := hzv.2
  refine ⟨hsum_one, ?_⟩
  rw [← hnorm_sum]
  calc
    hbBilateralSequenceL2Norm zsum ≤
        hbBilateralSequenceL2Norm zu + hbBilateralSequenceL2Norm zv := hsum_z.2
    _ = hbSequenceL2Norm u + hbSequenceL2Norm v := by
      rw [hnorm_u, hnorm_v]

private theorem hbHomotopyInput_l2_of_l2
    {q a b : ℝ} (hD : ParameterDomain q a b) {d : ℕ}
    (hf : AdmissibleObjective q d) (τ : ℝ) (hτ0 : 0 ≤ τ)
    (x : ℕ → Vec d) (hx : hbSequenceInL2 x) :
    hbSequenceInL2
      (hbHomotopyInput (parameterDomain_q_pos hD) hf τ x) := by
  have hL : 0 ≤ hbL0 q := by
    dsimp [hbL0]
    linarith [parameterDomain_q_lt_one hD]
  have hDnorm : ∀ t : ℕ,
      ‖hbCenteredNonlinearity (parameterDomain_q_pos hD) hf (x t)‖ ≤
        hbL0 q * ‖x t‖ := by
    intro t
    exact hbCenteredNonlinearity_lipschitz_from_zero
      (parameterDomain_q_pos hD) hf (x t)
  have hmajor :
      Summable (fun t : ℕ => (τ ^ 2 * (hbL0 q) ^ 2) * ‖x t‖ ^ 2) := by
    have hscale := hx.const_smul (τ ^ 2 * (hbL0 q) ^ 2)
    simpa [hbSequenceInL2, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
      using hscale
  unfold hbSequenceInL2 hbHomotopyInput
  exact Summable.of_nonneg_of_le
    (fun t => sq_nonneg (‖τ • hbCenteredNonlinearity
      (parameterDomain_q_pos hD) hf (x t)‖))
    (fun t => by
      have hright : 0 ≤ hbL0 q * ‖x t‖ :=
        mul_nonneg hL (norm_nonneg _)
      have hsq :
          ‖hbCenteredNonlinearity (parameterDomain_q_pos hD) hf (x t)‖ ^ 2 ≤
            (hbL0 q * ‖x t‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) hright).2 (hDnorm t)
      have hscaled :=
        mul_le_mul_of_nonneg_left hsq (sq_nonneg τ)
      have hτabs : |τ| = τ := abs_of_nonneg hτ0
      simpa [norm_smul, Real.norm_eq_abs, hτabs, mul_pow, pow_two,
        mul_assoc, mul_left_comm, mul_comm] using hscaled)
    hmajor

private theorem hbD9_zero_extended_supply_of_l2
    {q a b : ℝ} (hbox : HB_Box q a b) {d : ℕ}
    (hf : AdmissibleObjective q d) (τ : ℝ)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (x : ℕ → Vec d) (hx : hbSequenceInL2 x) :
    let hD := HB_box_subset_domain hbox
    let zext : ℤ → Vec d := Function.extend Int.ofNat x 0
    0 ≤ ∑' t : ℤ,
      inner ℝ
        (τ • hbCenteredNonlinearity (parameterDomain_q_pos hD) hf (zext t))
        (hbMultiplierTimeDomain
          (fun t : ℤ =>
            hbL0 q • zext t -
              τ • hbCenteredNonlinearity (parameterDomain_q_pos hD) hf (zext t))
          t) := by
  dsimp
  let hD := HB_box_subset_domain hbox
  let zext : ℤ → Vec d := Function.extend Int.ofNat x 0
  have hzx : Summable (fun t : ℤ => ‖zext t‖ ^ 2) := by
    have hz := (hbD9_zeroExtension_oneSided_to_bilateral x hx).1
    simpa [zext, hbBilateralSequenceInL2] using hz
  have hsup :=
    (HB_DYNAMICS_SUPPLY_FREQUENCY hbox).2.1 hf τ hτ0 hτ1 zext hzx
  unfold hbSupplyInequality at hsup
  dsimp at hsup
  simpa [hD, zext] using hsup

private theorem hbD9_external_term_upper_bound
    {q a b : ℝ} (hD : ParameterDomain q a b) {d : ℕ}
    (p e : ℤ → Vec d)
    (hp : Summable (fun t : ℤ => ‖p t‖ ^ 2))
    (he : Summable (fun t : ℤ => ‖e t‖ ^ 2)) :
    (∑' t : ℤ, inner ℝ (p t)
      (hbMultiplierTimeDomain (fun t : ℤ => hbL0 q • e t) t)) ≤
      hbL0 q * hbMultiplierL2Gain *
        hbBilateralSequenceL2Norm p * hbBilateralSequenceL2Norm e := by
  have hL : 0 ≤ hbL0 q := by
    dsimp [hbL0]
    linarith [parameterDomain_q_lt_one hD]
  have he_scaled :
      Summable (fun t : ℤ => ‖hbL0 q • e t‖ ^ 2) ∧
        hbBilateralSequenceL2Norm (fun t : ℤ => hbL0 q • e t) =
          hbL0 q * hbBilateralSequenceL2Norm e := by
    simpa [abs_of_nonneg hL] using
      (hb_bilateral_l2_smul_summable_and_norm_eq he (hbL0 q))
  have hm :=
    (hbMultiplierL2Gain_is_bound).2
      (fun t : ℤ => hbL0 q • e t) he_scaled.1
  have hinner :=
    hb_bilateral_inner_tsum_le_l2_mul_l2 hp hm.1
  calc
    (∑' t : ℤ, inner ℝ (p t)
      (hbMultiplierTimeDomain (fun t : ℤ => hbL0 q • e t) t)) ≤
        hbBilateralSequenceL2Norm p *
          hbBilateralSequenceL2Norm
            (fun t : ℤ => hbMultiplierTimeDomain (hbL0 q • e) t) :=
      hinner.2
    _ ≤ hbBilateralSequenceL2Norm p *
          (hbMultiplierL2Gain *
            hbBilateralSequenceL2Norm (fun t : ℤ => hbL0 q • e t)) := by
      exact mul_le_mul_of_nonneg_left hm.2 (Real.sqrt_nonneg _)
    _ = hbL0 q * hbMultiplierL2Gain *
          hbBilateralSequenceL2Norm p * hbBilateralSequenceL2Norm e := by
      rw [he_scaled.2]
      ring

private theorem hbD9_frequency_margin_on_box
    {q a b : ℝ} (hbox : HB_Box q a b) :
    ∀ (z : ℂ) (hz : ‖z‖ = 1),
      Complex.re
        (hbMultiplier z *
          (((hbL0 q : ℝ) : ℂ) *
              hbTransferUnitCircle q a b
                (HB_box_subset_domain hbox) z hz - 1)) ≤
        -hbD9Eta := by
  intro z hz
  have hmargin :=
    (HB_DYNAMICS_SUPPLY_FREQUENCY hbox).2.2.2 z hz
  simpa [hbD9Eta] using hmargin

private theorem hbD9_multiplier_inner_summable_of_l2
    {q : ℝ} {d : ℕ} (p y : ℤ → Vec d)
    (hp : Summable (fun t : ℤ => ‖p t‖ ^ 2))
    (hy : Summable (fun t : ℤ => ‖y t‖ ^ 2)) :
    Summable (fun t : ℤ =>
      inner ℝ (p t)
        (hbMultiplierTimeDomain
          (fun t : ℤ => hbL0 q • y t - p t) t)) := by
  have hscaled :=
    hb_bilateral_l2_smul_summable_and_norm_eq hy (hbL0 q)
  have hneg :=
    hb_bilateral_l2_smul_summable_and_norm_eq hp (-1 : ℝ)
  have hsum :=
    hb_bilateral_l2_norm_add_le hscaled.1 hneg.1
  have hs :
      Summable (fun t : ℤ => ‖hbL0 q • y t - p t‖ ^ 2) := by
    simpa [sub_eq_add_neg] using hsum.1
  have hm := hb_multiplier_finite_lag_l2_bound hs
  exact (hb_bilateral_inner_tsum_le_l2_mul_l2 hp hm.1).1

private theorem hbD9_zero_extension_plant_recurrence
    {q a b : ℝ} {d : ℕ} (p : ℕ → Vec d) :
    ∀ t : ℤ,
      Function.extend Int.ofNat (hbPlantResponse q a b p) 0 (t + 2) =
        (1 + b - a * q) •
            Function.extend Int.ofNat (hbPlantResponse q a b p) 0 (t + 1) -
          b • Function.extend Int.ofNat (hbPlantResponse q a b p) 0 t -
          a • Function.extend Int.ofNat p 0 (t + 1) := by
  intro t
  cases t with
  | ofNat n =>
      change Function.extend Int.ofNat (hbPlantResponse q a b p) 0
          ((n + 2 : ℕ) : ℤ) =
        (1 + b - a * q) •
            Function.extend Int.ofNat (hbPlantResponse q a b p) 0
              ((n + 1 : ℕ) : ℤ) -
          b • Function.extend Int.ofNat (hbPlantResponse q a b p) 0
            (n : ℤ) -
          a • Function.extend Int.ofNat p 0
            ((n + 1 : ℕ) : ℤ)
      have hy2 :
          Function.extend Int.ofNat (hbPlantResponse q a b p) 0
              ((n + 2 : ℕ) : ℤ) =
            hbPlantResponse q a b p (n + 2) :=
        Int.ofNat_injective.extend_apply (hbPlantResponse q a b p) 0 (n + 2)
      have hy1 :
          Function.extend Int.ofNat (hbPlantResponse q a b p) 0
              ((n + 1 : ℕ) : ℤ) =
            hbPlantResponse q a b p (n + 1) :=
        Int.ofNat_injective.extend_apply (hbPlantResponse q a b p) 0 (n + 1)
      have hy0 :
          Function.extend Int.ofNat (hbPlantResponse q a b p) 0
              (n : ℤ) =
            hbPlantResponse q a b p n :=
        Int.ofNat_injective.extend_apply (hbPlantResponse q a b p) 0 n
      have hp1 :
          Function.extend Int.ofNat p 0 ((n + 1 : ℕ) : ℤ) = p (n + 1) :=
        Int.ofNat_injective.extend_apply p 0 (n + 1)
      rw [hy2, hy1, hy0, hp1]
      rw [hbPlantResponse]
  | negSucc n =>
      cases n with
      | zero =>
          have hy1 :
              Function.extend Int.ofNat (hbPlantResponse q a b p) 0 1 =
                hbPlantResponse q a b p 1 :=
            Int.ofNat_injective.extend_apply (hbPlantResponse q a b p) 0 1
          have hy0 :
              Function.extend Int.ofNat (hbPlantResponse q a b p) 0 0 =
                hbPlantResponse q a b p 0 :=
            Int.ofNat_injective.extend_apply (hbPlantResponse q a b p) 0 0
          have hp0 :
              Function.extend Int.ofNat p 0 0 = p 0 :=
            Int.ofNat_injective.extend_apply p 0 0
          have hyneg :
              Function.extend Int.ofNat (hbPlantResponse q a b p) 0 (-1 : ℤ) = 0 :=
            by
              apply Function.extend_apply'
              simp
          change Function.extend Int.ofNat (hbPlantResponse q a b p) 0 1 =
            (1 + b - a * q) •
                Function.extend Int.ofNat (hbPlantResponse q a b p) 0 0 -
              b • Function.extend Int.ofNat (hbPlantResponse q a b p) 0 (-1 : ℤ) -
              a • Function.extend Int.ofNat p 0 0
          rw [hy1, hy0, hyneg, hp0]
          simp [hbPlantResponse]
      | succ n =>
          cases n with
          | zero =>
              have hy0 :
                  Function.extend Int.ofNat (hbPlantResponse q a b p) 0 0 =
                    hbPlantResponse q a b p 0 :=
                Int.ofNat_injective.extend_apply (hbPlantResponse q a b p) 0 0
              have hyneg :
                  Function.extend Int.ofNat (hbPlantResponse q a b p) 0 (-2 : ℤ) = 0 :=
                by
                  apply Function.extend_apply'
                  simp
              have hyneg1 :
                  Function.extend Int.ofNat (hbPlantResponse q a b p) 0 (-1 : ℤ) = 0 :=
                by
                  apply Function.extend_apply'
                  simp
              have hpneg :
                  Function.extend Int.ofNat p 0 (-1 : ℤ) = 0 :=
                by
                  apply Function.extend_apply'
                  simp
              change Function.extend Int.ofNat (hbPlantResponse q a b p) 0 0 =
                (1 + b - a * q) •
                    Function.extend Int.ofNat (hbPlantResponse q a b p) 0 (-1 : ℤ) -
                  b • Function.extend Int.ofNat (hbPlantResponse q a b p) 0 (-2 : ℤ) -
                  a • Function.extend Int.ofNat p 0 (-1 : ℤ)
              rw [hy0, hyneg1, hyneg, hpneg]
              simp [hbPlantResponse]
          | succ n =>
              have hnot (k : ℤ) (hk : k < 0) :
                  ¬∃ x : ℕ, (x : ℤ) = k := by
                rintro ⟨x, hx⟩
                omega
              have hy0 :
                  Function.extend Int.ofNat (hbPlantResponse q a b p) 0
                      (Int.negSucc (n + 2) + 2) = 0 := by
                apply Function.extend_apply'
                exact hnot _ (by omega)
              have hy1 :
                  Function.extend Int.ofNat (hbPlantResponse q a b p) 0
                      (Int.negSucc (n + 2) + 1) = 0 := by
                apply Function.extend_apply'
                exact hnot _ (by omega)
              have hy2 :
                  Function.extend Int.ofNat p 0
                      (Int.negSucc (n + 2) + 1) = 0 := by
                apply Function.extend_apply'
                exact hnot _ (by omega)
              have hy3 :
                  Function.extend Int.ofNat (hbPlantResponse q a b p) 0
                      (Int.negSucc (n + 2)) = 0 := by
                apply Function.extend_apply'
                exact hnot _ (by omega)
              change Function.extend Int.ofNat (hbPlantResponse q a b p) 0
                    (Int.negSucc (n + 2) + 2) =
                (1 + b - a * q) •
                    Function.extend Int.ofNat (hbPlantResponse q a b p) 0
                      (Int.negSucc (n + 2) + 1) -
                  b • Function.extend Int.ofNat (hbPlantResponse q a b p) 0
                    (Int.negSucc (n + 2)) -
                  a • Function.extend Int.ofNat p 0
                    (Int.negSucc (n + 2) + 1)
              rw [hy0, hy1, hy2]
              rw [hy3]
              simp

private theorem hb_tsum_int_odd_enum_real
    (f : ℤ → ℝ) (hf : Summable f) :
    Tendsto
      (fun N : ℕ =>
        ∑ k ∈ Finset.range (2 * N + 1),
          f (Equiv.intEquivNat.symm k))
      atTop (nhds (∑' t : ℤ, f t)) := by
  let e : ℕ ≃ ℤ := Equiv.intEquivNat.symm
  have he : Summable (fun k : ℕ => f (e k)) := by
    simpa [e, Function.comp_def] using e.summable_iff.mpr hf
  have hsum :
      HasSum (fun k : ℕ => f (e k)) (∑' t : ℤ, f t) := by
    rw [← e.tsum_eq f]
    exact he.hasSum
  have hnat :
      Tendsto
        (fun n : ℕ => ∑ k ∈ Finset.range n, f (e k))
        atTop (nhds (∑' t : ℤ, f t)) :=
    hsum.tendsto_sum_nat
  have hodd : Tendsto (fun N : ℕ => 2 * N + 1) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro n
    filter_upwards [eventually_ge_atTop ((n + 1) / 2)] with N hN
    omega
  simpa [e] using hnat.comp hodd

private theorem hb_tsum_int_odd_enum_le
    (f g : ℤ → ℝ) (hf : Summable f) (hg : Summable g)
    (hfg : ∀ N : ℕ,
      (∑ k ∈ Finset.range (2 * N + 1),
        f (Equiv.intEquivNat.symm k)) ≤
      ∑ k ∈ Finset.range (2 * N + 1),
        g (Equiv.intEquivNat.symm k)) :
    (∑' t : ℤ, f t) ≤ ∑' t : ℤ, g t := by
  have hf_lim := hb_tsum_int_odd_enum_real f hf
  have hg_lim := hb_tsum_int_odd_enum_real g hg
  exact le_of_tendsto_of_tendsto hf_lim hg_lim (Eventually.of_forall hfg)

private theorem hb_d9_coercivity_limit_of_window_bounds
    {q : ℝ} {d : ℕ} (p y : ℤ → Vec d)
    (hp : Summable (fun t : ℤ => ‖p t‖ ^ 2))
    (hy : Summable (fun t : ℤ => ‖y t‖ ^ 2))
    (hwindow : ∀ N : ℕ,
      (∑ k ∈ Finset.range (2 * N + 1),
        inner ℝ (p (Equiv.intEquivNat.symm k))
          (hbMultiplierTimeDomain
            (fun t : ℤ => hbL0 q • y t - p t)
            (Equiv.intEquivNat.symm k))) ≤
      ∑ k ∈ Finset.range (2 * N + 1),
        -hbD9Eta * ‖p (Equiv.intEquivNat.symm k)‖ ^ 2) :
    (∑' t : ℤ,
      inner ℝ (p t)
        (hbMultiplierTimeDomain
          (fun t : ℤ => hbL0 q • y t - p t) t)) ≤
      -hbD9Eta * hbBilateralSequenceL2Norm p ^ 2 := by
  have hinner :=
    hbD9_multiplier_inner_summable_of_l2 (q := q) p y hp hy
  have hs_scaled :=
    hb_bilateral_l2_smul_summable_and_norm_eq hy (hbL0 q)
  have hs_neg :=
    hb_bilateral_l2_smul_summable_and_norm_eq hp (-1 : ℝ)
  have hs :
      Summable (fun t : ℤ => ‖hbL0 q • y t - p t‖ ^ 2) := by
    have hsum := hb_bilateral_l2_norm_add_le hs_scaled.1 hs_neg.1
    simpa [sub_eq_add_neg] using hsum.1
  have hm := hb_multiplier_finite_lag_l2_bound hs
  have hinner_bound :=
    hb_bilateral_inner_tsum_le_l2_mul_l2 hp hm.1
  have hneg :
      Summable (fun t : ℤ => -hbD9Eta * ‖p t‖ ^ 2) := by
    simpa using hp.mul_left (-hbD9Eta)
  have hlim :=
    hb_tsum_int_odd_enum_le
      (fun t : ℤ =>
        inner ℝ (p t)
          (hbMultiplierTimeDomain
            (fun u : ℤ => hbL0 q • y u - p u) t))
      (fun t : ℤ => -hbD9Eta * ‖p t‖ ^ 2)
      hinner hneg hwindow
  rw [tsum_mul_left] at hlim
  have henergy_nonneg :
      0 ≤ ∑' t : ℤ, ‖p t‖ ^ 2 :=
    tsum_nonneg (fun t => sq_nonneg _)
  have hnorm_sq :
      hbBilateralSequenceL2Norm p ^ 2 =
        ∑' t : ℤ, ‖p t‖ ^ 2 := by
    unfold hbBilateralSequenceL2Norm hbBilateralSequenceEnergy
    exact Real.sq_sqrt henergy_nonneg
  rw [hnorm_sq]
  exact hlim

private theorem hb_d9_finite_cyclic_coercivity_scalar
    {q a b : ℝ} (hbox : HB_Box q a b)
    {K : ℕ} [NeZero K] (p y : Fin K → ℝ)
    (hrec : ∀ i : Fin K,
      y (cycleFinShift 1 i) =
        (1 + b - a * q) * y i -
          b * y (cycleFinShift (K - 1) i) -
            a * p i) :
    ∑ i : Fin K,
        p i *
          (hbMultiplierEpsilon *
              (hbL0 q * y i - p i) +
            ((hbL0 q * y i - p i) -
              (hbL0 q * y (cycleFinShift (K - 1) i) -
                p (cycleFinShift (K - 1) i))) +
            (4 / 25 : ℝ) *
              ((hbL0 q * y i - p i) -
                (hbL0 q * y (cycleFinShift 4 i) -
                  p (cycleFinShift 4 i)))) ≤
      -hbD9Eta * ∑ i : Fin K, p i ^ 2 := by
  let hD := HB_box_subset_domain hbox
  let α : Fin K → ℂ :=
    fun j => ZMod.stdAddChar (ZMod.finEquiv K j)
  let H : Fin K → ℂ := fun j =>
    (((1 + b - a * q : ℝ) : ℂ) - α j -
      (b : ℂ) * starRingEnd ℂ (α j)) / (a : ℂ)
  have hq0 : 0 < q := parameterDomain_q_pos hD
  have ha0 : 0 < a := hD.2.2.2.2.1
  have ha : a ≠ 0 := ne_of_gt ha0
  have hαnorm (j : Fin K) : ‖α j‖ = 1 := by
    dsimp [α]
    have hsq : ‖ZMod.stdAddChar (ZMod.finEquiv K j)‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq]
      simpa using hb_cycle_stdAddChar_normSq (ZMod.finEquiv K j)
    nlinarith [norm_nonneg (ZMod.stdAddChar (ZMod.finEquiv K j))]
  have hα0 (j : Fin K) : α j ≠ 0 := by
    intro hzero
    have hzero' := congrArg norm hzero
    rw [hαnorm j] at hzero'
    simp at hzero'
  have hHG (j : Fin K) :
      H j * hbTransferUnitCircle q a b hD (α j) (hαnorm j) = 1 := by
    have hdomain :
        hbTransferDomain q a b (α j) :=
      hbTransferDomain_of_unit_norm hD (hαnorm j)
    have hden :
        (α j) ^ 2 - ((1 + b - a * q : ℝ) : ℂ) * α j +
            (b : ℂ) ≠ 0 := by
      change hbTransferDenominator q a b (α j) ≠ 0 at hdomain
      simpa [hbTransferDenominator] using hdomain
    have hden' :
        -(α j * ((1 + b - a * q : ℝ) : ℂ)) +
            (α j) ^ 2 + (b : ℂ) ≠ 0 := by
      convert hden using 1 <;> ring
    dsimp [H, α]
    simp only [starRingEnd_apply]
    rw [← starRingEnd_apply]
    rw [← Complex.inv_eq_conj (hαnorm j)]
    rw [hbTransferUnitCircle, hbTransferFunction_eq]
    simp only [α]
    have hα0' :
        ZMod.stdAddChar (ZMod.finEquiv K j) ≠ 0 := by
      simpa [α] using hα0 j
    have hden'' :
        -(ZMod.stdAddChar (ZMod.finEquiv K j) *
            ((1 + b - a * q : ℝ) : ℂ)) +
            (ZMod.stdAddChar (ZMod.finEquiv K j)) ^ 2 +
              (b : ℂ) ≠ 0 := by
      simpa [α] using hden'
    have hcancel :
        (((((1 + b - a * q : ℝ) : ℂ) -
              ZMod.stdAddChar (ZMod.finEquiv K j) -
              (b : ℂ) * (ZMod.stdAddChar (ZMod.finEquiv K j))⁻¹) /
            (a : ℂ)) *
          (-((a : ℂ) * ZMod.stdAddChar (ZMod.finEquiv K j)))) =
        -(ZMod.stdAddChar (ZMod.finEquiv K j) *
            ((1 + b - a * q : ℝ) : ℂ)) +
          (ZMod.stdAddChar (ZMod.finEquiv K j)) ^ 2 + (b : ℂ) := by
      field_simp [hα0', ha]
      ring
    have hden_eq :
        (ZMod.stdAddChar (ZMod.finEquiv K j)) ^ 2 -
            ((1 + b - a * q : ℝ) : ℂ) *
              ZMod.stdAddChar (ZMod.finEquiv K j) +
            (b : ℂ) =
          -(ZMod.stdAddChar (ZMod.finEquiv K j) *
              ((1 + b - a * q : ℝ) : ℂ)) +
            (ZMod.stdAddChar (ZMod.finEquiv K j)) ^ 2 + (b : ℂ) := by
      ring
    rw [hden_eq]
    calc
      _ =
          (((((1 + b - a * q : ℝ) : ℂ) -
                ZMod.stdAddChar (ZMod.finEquiv K j) -
                (b : ℂ) *
                  (ZMod.stdAddChar (ZMod.finEquiv K j))⁻¹) /
              (a : ℂ)) *
            (-((a : ℂ) * ZMod.stdAddChar (ZMod.finEquiv K j)))) /
            (-(ZMod.stdAddChar (ZMod.finEquiv K j) *
                ((1 + b - a * q : ℝ) : ℂ)) +
              (ZMod.stdAddChar (ZMod.finEquiv K j)) ^ 2 + (b : ℂ)) := by
        ring
      _ = 1 := by
        rw [hcancel, div_self hden'']
  let pc : Fin K → ℂ := fun i => (p i : ℂ)
  let yc : Fin K → ℂ := fun i => (y i : ℂ)
  let sc : Fin K → ℂ :=
    fun i => ((hbL0 q * y i - p i : ℝ) : ℂ)
  let mc : Fin K → ℂ :=
    fun i =>
      ((hbMultiplierEpsilon *
          (hbL0 q * y i - p i) +
        ((hbL0 q * y i - p i) -
          (hbL0 q * y (cycleFinShift (K - 1) i) -
            p (cycleFinShift (K - 1) i))) +
        (4 / 25 : ℝ) *
          ((hbL0 q * y i - p i) -
            (hbL0 q * y (cycleFinShift 4 i) -
              p (cycleFinShift 4 i))) : ℝ) : ℂ)
  have hDft_sub (u v : Fin K → ℂ) (j : Fin K) :
      hbCycleDftCoord (fun i => u i - v i) j =
        hbCycleDftCoord u j - hbCycleDftCoord v j := by
    unfold hbCycleDftCoord
    simp only [Pi.sub_apply, mul_sub]
    rw [Finset.sum_sub_distrib]
  have hDft_add (u v : Fin K → ℂ) (j : Fin K) :
      hbCycleDftCoord (fun i => u i + v i) j =
        hbCycleDftCoord u j + hbCycleDftCoord v j := by
    unfold hbCycleDftCoord
    simp only [Pi.add_apply, mul_add]
    rw [Finset.sum_add_distrib]
  have hDft_smul (c : ℂ) (u : Fin K → ℂ) (j : Fin K) :
      hbCycleDftCoord (fun i => c * u i) j =
        c * hbCycleDftCoord u j := by
    unfold hbCycleDftCoord
    change (∑ i : Fin K, hbCycleRho j i * (c * u i)) =
      c * ∑ i : Fin K, hbCycleRho j i * u i
    calc
      (∑ i : Fin K, hbCycleRho j i * (c * u i)) =
          ∑ i : Fin K, c * (hbCycleRho j i * u i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = c * ∑ i : Fin K, hbCycleRho j i * u i := by
        rw [← Finset.mul_sum]
  have hrecG (i : Fin K) :
      yc (cycleFinShift 1 i) =
        (1 + (b : ℂ)) * yc i -
          (b : ℂ) * yc (cycleFinShift (K - 1) i) -
            (a : ℂ) * (pc i + (q : ℂ) * yc i) := by
    have h := congrArg (fun r : ℝ => (r : ℂ)) (hrec i)
    convert h using 1 <;> simp [pc, yc, sub_eq_add_neg, mul_add, add_mul] <;>
      ring
  have hP (j : Fin K) :
      hbCycleDftCoord pc j = H j * hbCycleDftCoord yc j := by
    have htrans :=
      hb_cycle_dft_scalar_recurrence_transfer
        (a := (a : ℂ)) (b := (b : ℂ))
        (Y := yc)
        (G := fun i => pc i + (q : ℂ) * yc i)
        hrecG (by exact_mod_cast ha) j
    have hsum :
        hbCycleDftCoord pc j + (q : ℂ) * hbCycleDftCoord yc j =
          (((1 + (b : ℂ)) -
              α j -
              (b : ℂ) * starRingEnd ℂ (α j)) /
            (a : ℂ)) *
            hbCycleDftCoord yc j := by
      have hadd :=
        hDft_add pc (fun i => (q : ℂ) * yc i) j
      have hsmul := hDft_smul (q : ℂ) yc j
      rw [hsmul] at hadd
      rw [htrans, hb_cycle_dft_prev_character] at hadd
      simpa [α] using hadd.symm
    dsimp [H]
    calc
      hbCycleDftCoord pc j =
          (hbCycleDftCoord pc j + (q : ℂ) * hbCycleDftCoord yc j) -
            (q : ℂ) * hbCycleDftCoord yc j := by ring
      _ =
          (((1 + (b : ℂ)) - α j -
              (b : ℂ) * starRingEnd ℂ (α j)) / (a : ℂ)) *
              hbCycleDftCoord yc j -
            (q : ℂ) * hbCycleDftCoord yc j := by rw [hsum]
      _ = H j * hbCycleDftCoord yc j := by
        dsimp [H]
        field_simp [ha]
        have hcast :
            ((1 + b - a * q : ℝ) : ℂ) =
              1 + (b : ℂ) - (a : ℂ) * (q : ℂ) := by
          norm_num
        rw [hcast]
        ring
  have hSc (j : Fin K) :
      hbCycleDftCoord sc j =
        ((hbL0 q : ℂ) * hbTransferUnitCircle q a b hD
            (α j) (hαnorm j) - 1) *
          hbCycleDftCoord pc j := by
    have hsc0 :
        hbCycleDftCoord sc j =
          (hbL0 q : ℂ) * hbCycleDftCoord yc j -
            hbCycleDftCoord pc j := by
      have hsub :=
        hDft_sub
          (fun i => (hbL0 q : ℂ) * yc i) pc j
      have hsmul := hDft_smul (hbL0 q : ℂ) yc j
      rw [hsmul] at hsub
      simpa [sc, pc, yc] using hsub
    have hGH :
        hbTransferUnitCircle q a b hD (α j) (hαnorm j) * H j = 1 := by
      rw [mul_comm]
      exact hHG j
    calc
      hbCycleDftCoord sc j =
          (hbL0 q : ℂ) * hbCycleDftCoord yc j -
            hbCycleDftCoord pc j := hsc0
      _ = ((hbL0 q : ℂ) - H j) *
            hbCycleDftCoord yc j := by rw [hP j]; ring
      _ = ((hbL0 q : ℂ) *
            hbTransferUnitCircle q a b hD
              (α j) (hαnorm j) - 1) *
            (H j * hbCycleDftCoord yc j) := by
          have hcoef :
              ((hbL0 q : ℂ) *
                  hbTransferUnitCircle q a b hD
                    (α j) (hαnorm j) - 1) * H j =
                (hbL0 q : ℂ) - H j := by
            calc
              ((hbL0 q : ℂ) *
                    hbTransferUnitCircle q a b hD
                      (α j) (hαnorm j) - 1) * H j =
                  (hbL0 q : ℂ) *
                      (hbTransferUnitCircle q a b hD
                        (α j) (hαnorm j) * H j) - H j := by ring
              _ = (hbL0 q : ℂ) - H j := by rw [hGH]; ring
          rw [← hcoef]
          ring
      _ = ((hbL0 q : ℂ) *
            hbTransferUnitCircle q a b hD
              (α j) (hαnorm j) - 1) *
            hbCycleDftCoord pc j := by rw [hP j]
  have hM (j : Fin K) :
      hbCycleDftCoord mc j =
        hbMultiplier (α j) * hbCycleDftCoord sc j := by
    let sprev : Fin K → ℂ := fun i => sc (cycleFinShift (K - 1) i)
    let sfour : Fin K → ℂ := fun i => sc (cycleFinShift 4 i)
    let mcc : Fin K → ℂ :=
      fun i => (hbMultiplierEpsilon : ℂ) * sc i +
        (sc i - sprev i) +
        (4 / 25 : ℂ) * (sc i - sfour i)
    have hmc_eq : mc = mcc := by
      funext i
      simp [mc, mcc, sprev, sfour, sc, pc, yc]
    have hprev :
        hbCycleDftCoord sprev j =
          starRingEnd ℂ (α j) * hbCycleDftCoord sc j := by
      have h := hb_cycle_dft_shift sc (K - 1) j
      rw [hb_cycle_dft_prev_character] at h
      simpa [sprev, α] using h
    have hfour :
        hbCycleDftCoord sfour j =
          (α j) ^ 4 * hbCycleDftCoord sc j := by
      have h := hb_cycle_dft_shift sc 4 j
      have halphaFour :
          ZMod.stdAddChar (ZMod.finEquiv K j * ((4 : ℕ) : ZMod K)) =
            (ZMod.stdAddChar (ZMod.finEquiv K j)) ^ 4 := by
        have harg :
            ZMod.finEquiv K j * ((4 : ℕ) : ZMod K) =
              ZMod.finEquiv K j + ZMod.finEquiv K j +
                ZMod.finEquiv K j + ZMod.finEquiv K j := by
          ring
        rw [harg, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
          AddChar.map_add_eq_mul]
        ring
      rw [halphaFour] at h
      simpa [sfour, α] using h
    rw [hmc_eq]
    dsimp [mcc]
    rw [hDft_add, hDft_add]
    have hE := hDft_smul (hbMultiplierEpsilon : ℂ) sc j
    have hdiffPrev := hDft_sub sc sprev j
    have hdiffFour := hDft_sub sc sfour j
    rw [hE, hdiffPrev, hDft_smul, hdiffFour, hprev, hfour]
    dsimp [hbMultiplier]
    have hinv :
        (α j)⁻¹ = starRingEnd ℂ (α j) := by
      rw [Complex.inv_eq_conj (hαnorm j)]
    rw [hinv]
    have hfrac : ((4 / 25 : ℝ) : ℂ) = (4 / 25 : ℂ) := by
      norm_num
    rw [hfrac]
    ring
  have hparse :
      ∑ i : Fin K,
          p i *
            (hbMultiplierEpsilon *
                (hbL0 q * y i - p i) +
              ((hbL0 q * y i - p i) -
                (hbL0 q * y (cycleFinShift (K - 1) i) -
                  p (cycleFinShift (K - 1) i))) +
              (4 / 25 : ℝ) *
                ((hbL0 q * y i - p i) -
                  (hbL0 q * y (cycleFinShift 4 i) -
                    p (cycleFinShift 4 i)))) =
        Complex.re
          ((K : ℂ)⁻¹ *
            ∑ j : Fin K,
              hbCycleDftCoord pc j *
                starRingEnd ℂ (hbCycleDftCoord mc j)) := by
    have hmcstar (i : Fin K) :
        starRingEnd ℂ (mc i) =
          ((hbMultiplierEpsilon *
                (hbL0 q * y i - p i) +
              ((hbL0 q * y i - p i) -
                (hbL0 q * y (cycleFinShift (K - 1) i) -
                  p (cycleFinShift (K - 1) i))) +
              (4 / 25 : ℝ) *
                ((hbL0 q * y i - p i) -
                  (hbL0 q * y (cycleFinShift 4 i) -
                    p (cycleFinShift 4 i))) : ℝ) : ℂ) := by
      dsimp [mc]
      simpa only [Complex.conj_ofReal]
    have h :=
      congrArg Complex.re (hb_cycle_dft_parseval_complex pc mc)
    simp_rw [hmcstar] at h
    simpa [pc, mc, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im] using h.symm
  have hmode (j : Fin K) :
      Complex.re
          (hbCycleDftCoord pc j *
            starRingEnd ℂ (hbCycleDftCoord mc j)) ≤
        -hbD9Eta * Complex.normSq (hbCycleDftCoord pc j) := by
    let D : ℂ := hbCycleDftCoord pc j
    let B : ℂ := hbMultiplier (α j)
    let C : ℂ :=
      (hbL0 q : ℂ) *
          hbTransferUnitCircle q a b hD (α j) (hαnorm j) - 1
    have hfactor :
        Complex.re (D * starRingEnd ℂ (B * (C * D))) =
          Complex.re (B * C) * Complex.normSq D := by
      rw [map_mul, map_mul]
      simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
      ring
    have hmargin :
        Complex.re (B * C) ≤ -hbD9Eta := by
      simpa [B, C] using
        hbD9_frequency_margin_on_box hbox (α j) (hαnorm j)
    have hnormsq : 0 ≤ Complex.normSq D :=
      Complex.normSq_nonneg D
    rw [hM j, hSc j]
    change Complex.re (D * starRingEnd ℂ (B * (C * D))) ≤
      -hbD9Eta * Complex.normSq D
    rw [hfactor]
    exact mul_le_mul_of_nonneg_right hmargin hnormsq
  have hreal_sum (f : Fin K → ℂ) :
      Complex.re (∑ j : Fin K, f j) =
        ∑ j : Fin K, Complex.re (f j) := by
    induction (Finset.univ : Finset (Fin K)) using Finset.induction_on with
    | empty =>
        simp
    | @insert j s hjs ih =>
        simp only [Finset.sum_insert hjs, Complex.add_re, ih]
  have hKnat : (K : ℂ) = ((K : ℝ) : ℂ) := by
    norm_num
  have hKinv :
      (K : ℂ)⁻¹ = ((K : ℝ)⁻¹ : ℂ) := by
    rw [← Complex.ofReal_natCast K]
  have hparse_real :
      (∑ i : Fin K,
          p i *
            (hbMultiplierEpsilon *
                (hbL0 q * y i - p i) +
              ((hbL0 q * y i - p i) -
                (hbL0 q * y (cycleFinShift (K - 1) i) -
                  p (cycleFinShift (K - 1) i))) +
              (4 / 25 : ℝ) *
                ((hbL0 q * y i - p i) -
                  (hbL0 q * y (cycleFinShift 4 i) -
                    p (cycleFinShift 4 i))))) =
        (K : ℝ)⁻¹ *
          ∑ j : Fin K,
            Complex.re
              (hbCycleDftCoord pc j *
                starRingEnd ℂ (hbCycleDftCoord mc j)) := by
    calc
      _ = Complex.re
          ((K : ℂ)⁻¹ *
            ∑ j : Fin K,
              hbCycleDftCoord pc j *
                starRingEnd ℂ (hbCycleDftCoord mc j)) := hparse
      _ = (K : ℝ)⁻¹ *
          ∑ j : Fin K,
            Complex.re
              (hbCycleDftCoord pc j *
                starRingEnd ℂ (hbCycleDftCoord mc j)) := by
        rw [hKinv, Complex.mul_re, hreal_sum]
        simp
  have hnorm_term (j : Fin K) :
      Complex.re
          (hbCycleDftCoord pc j *
            starRingEnd ℂ (hbCycleDftCoord pc j)) =
        Complex.normSq (hbCycleDftCoord pc j) := by
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  have henergy :
      ∑ i : Fin K, p i ^ 2 =
        (K : ℝ)⁻¹ *
          ∑ j : Fin K, Complex.normSq (hbCycleDftCoord pc j) := by
    have hpp := hb_cycle_real_inner_parseval p p
    have hpp' :
        ∑ i : Fin K, p i * p i =
          Complex.re
            ((K : ℂ)⁻¹ *
              ∑ j : Fin K,
                hbCycleDftCoord pc j *
                  starRingEnd ℂ (hbCycleDftCoord pc j)) := by
      simpa [pc] using hpp
    calc
      ∑ i : Fin K, p i ^ 2 = ∑ i : Fin K, p i * p i := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = Complex.re
            ((K : ℂ)⁻¹ *
              ∑ j : Fin K,
                hbCycleDftCoord pc j *
                  starRingEnd ℂ (hbCycleDftCoord pc j)) := hpp'
      _ = (K : ℝ)⁻¹ *
          ∑ j : Fin K, Complex.normSq (hbCycleDftCoord pc j) := by
        rw [hKinv, Complex.mul_re, hreal_sum]
        simp_rw [hnorm_term]
        simp
  have hKpos : 0 < (K : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_ne_zero (NeZero.ne K))
  have hmode_sum :
      ∑ j : Fin K,
          Complex.re
            (hbCycleDftCoord pc j *
              starRingEnd ℂ (hbCycleDftCoord mc j)) ≤
        ∑ j : Fin K,
          -hbD9Eta * Complex.normSq (hbCycleDftCoord pc j) :=
    Finset.sum_le_sum (fun j _ => hmode j)
  calc
    ∑ i : Fin K,
        p i *
          (hbMultiplierEpsilon *
              (hbL0 q * y i - p i) +
            ((hbL0 q * y i - p i) -
              (hbL0 q * y (cycleFinShift (K - 1) i) -
                p (cycleFinShift (K - 1) i))) +
            (4 / 25 : ℝ) *
              ((hbL0 q * y i - p i) -
                (hbL0 q * y (cycleFinShift 4 i) -
                  p (cycleFinShift 4 i)))) =
        (K : ℝ)⁻¹ *
          ∑ j : Fin K,
            Complex.re
              (hbCycleDftCoord pc j *
                starRingEnd ℂ (hbCycleDftCoord mc j)) := hparse_real
    _ ≤ (K : ℝ)⁻¹ *
          ∑ j : Fin K,
            -hbD9Eta * Complex.normSq (hbCycleDftCoord pc j) := by
      exact mul_le_mul_of_nonneg_left hmode_sum
        (le_of_lt (inv_pos.mpr hKpos))
    _ = -hbD9Eta * ∑ i : Fin K, p i ^ 2 := by
      rw [Finset.mul_sum, henergy]
      calc
        ∑ i : Fin K,
            (K : ℝ)⁻¹ *
              (-hbD9Eta * Complex.normSq (hbCycleDftCoord pc i)) =
            ∑ i : Fin K,
              (-hbD9Eta * (K : ℝ)⁻¹) *
                Complex.normSq (hbCycleDftCoord pc i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = (-hbD9Eta * (K : ℝ)⁻¹) *
              ∑ i : Fin K, Complex.normSq (hbCycleDftCoord pc i) := by
          rw [Finset.mul_sum]
        _ = -hbD9Eta *
              ((K : ℝ)⁻¹ *
                ∑ i : Fin K, Complex.normSq (hbCycleDftCoord pc i)) := by
          ring

set_option maxHeartbeats 2000000 in
private theorem hb_d9_finite_cyclic_coercivity
    {q a b : ℝ} (hbox : HB_Box q a b)
    {K : ℕ} [NeZero K] {d : ℕ} (p y : Fin K → Vec d)
    (hrec : ∀ i : Fin K,
      y (cycleFinShift 1 i) =
        (1 + b - a * q) • y i -
          b • y (cycleFinShift (K - 1) i) -
            a • p i) :
    ∑ i : Fin K,
        inner ℝ (p i)
          (hbMultiplierEpsilon •
              (hbL0 q • y i - p i) +
            ((hbL0 q • y i - p i) -
              (hbL0 q • y (cycleFinShift (K - 1) i) -
                p (cycleFinShift (K - 1) i))) +
            (4 / 25 : ℝ) •
              ((hbL0 q • y i - p i) -
                (hbL0 q • y (cycleFinShift 4 i) -
                  p (cycleFinShift 4 i)))) ≤
      -hbD9Eta * ∑ i : Fin K, ‖p i‖ ^ 2 := by
  have hinner_coord (u v : Vec d) :
      inner ℝ u v = ∑ r : Fin d, (u.ofLp r) * (v.ofLp r) := by
    rw [PiLp.inner_apply]
    simp [PiLp.toLp_apply, real_inner_eq_re_inner, mul_comm]
  have hnorm_coord (u : Vec d) :
      ‖u‖ ^ 2 = ∑ r : Fin d, (u.ofLp r) ^ 2 := by
    simpa [PiLp.toLp_apply] using EuclideanSpace.real_norm_sq_eq u
  have hrec_coord (r : Fin d) (i : Fin K) :
      (y (cycleFinShift 1 i)).ofLp r =
        (1 + b - a * q) * (y i).ofLp r -
          b * (y (cycleFinShift (K - 1) i)).ofLp r -
            a * (p i).ofLp r := by
    have h := congrArg (fun v : Vec d => v.ofLp r) (hrec i)
    simpa [PiLp.smul_apply] using h
  have hscalar (r : Fin d) :
      ∑ i : Fin K,
          (p i).ofLp r *
            (hbMultiplierEpsilon *
                (hbL0 q * (y i).ofLp r - (p i).ofLp r) +
              ((hbL0 q * (y i).ofLp r - (p i).ofLp r) -
                (hbL0 q * (y (cycleFinShift (K - 1) i)).ofLp r -
                  (p (cycleFinShift (K - 1) i)).ofLp r)) +
              (4 / 25 : ℝ) *
                ((hbL0 q * (y i).ofLp r - (p i).ofLp r) -
                  (hbL0 q * (y (cycleFinShift 4 i)).ofLp r -
                    (p (cycleFinShift 4 i)).ofLp r))) ≤
        -hbD9Eta * ∑ i : Fin K, ((p i).ofLp r) ^ 2 := by
    exact hb_d9_finite_cyclic_coercivity_scalar hbox
      (fun i => (p i).ofLp r) (fun i => (y i).ofLp r)
      (hrec_coord r)
  have hleft :
      ∑ i : Fin K,
          inner ℝ (p i)
            (hbMultiplierEpsilon •
                (hbL0 q • y i - p i) +
              ((hbL0 q • y i - p i) -
                (hbL0 q • y (cycleFinShift (K - 1) i) -
                  p (cycleFinShift (K - 1) i))) +
              (4 / 25 : ℝ) •
                ((hbL0 q • y i - p i) -
                  (hbL0 q • y (cycleFinShift 4 i) -
                    p (cycleFinShift 4 i)))) =
        ∑ r : Fin d, ∑ i : Fin K,
          (p i).ofLp r *
            (hbMultiplierEpsilon *
                (hbL0 q * (y i).ofLp r - (p i).ofLp r) +
              ((hbL0 q * (y i).ofLp r - (p i).ofLp r) -
                (hbL0 q * (y (cycleFinShift (K - 1) i)).ofLp r -
                  (p (cycleFinShift (K - 1) i)).ofLp r)) +
              (4 / 25 : ℝ) *
                ((hbL0 q * (y i).ofLp r - (p i).ofLp r) -
                  (hbL0 q * (y (cycleFinShift 4 i)).ofLp r -
                    (p (cycleFinShift 4 i)).ofLp r))) := by
    calc
      _ = ∑ i : Fin K, ∑ r : Fin d,
          (p i).ofLp r *
            ((hbMultiplierEpsilon •
                (hbL0 q • y i - p i) +
              ((hbL0 q • y i - p i) -
                (hbL0 q • y (cycleFinShift (K - 1) i) -
                  p (cycleFinShift (K - 1) i))) +
              (4 / 25 : ℝ) •
                ((hbL0 q • y i - p i) -
                  (hbL0 q • y (cycleFinShift 4 i) -
                    p (cycleFinShift 4 i)))).ofLp r) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hinner_coord]
      _ = ∑ r : Fin d, ∑ i : Fin K,
          (p i).ofLp r *
            ((hbMultiplierEpsilon •
                (hbL0 q • y i - p i) +
              ((hbL0 q • y i - p i) -
                (hbL0 q • y (cycleFinShift (K - 1) i) -
                  p (cycleFinShift (K - 1) i))) +
              (4 / 25 : ℝ) •
                ((hbL0 q • y i - p i) -
                  (hbL0 q • y (cycleFinShift 4 i) -
                    p (cycleFinShift 4 i)))).ofLp r) := by
          rw [Finset.sum_comm]
      _ = _ := by
          apply Finset.sum_congr rfl
          intro r hr
          apply Finset.sum_congr rfl
          intro i hi
          simp [PiLp.smul_apply, WithLp.ofLp_sub]
  have hsum_scalar :
      ∑ r : Fin d, ∑ i : Fin K,
          (p i).ofLp r *
            (hbMultiplierEpsilon *
                (hbL0 q * (y i).ofLp r - (p i).ofLp r) +
              ((hbL0 q * (y i).ofLp r - (p i).ofLp r) -
                (hbL0 q * (y (cycleFinShift (K - 1) i)).ofLp r -
                  (p (cycleFinShift (K - 1) i)).ofLp r)) +
              (4 / 25 : ℝ) *
                ((hbL0 q * (y i).ofLp r - (p i).ofLp r) -
                  (hbL0 q * (y (cycleFinShift 4 i)).ofLp r -
                    (p (cycleFinShift 4 i)).ofLp r))) ≤
        ∑ r : Fin d, -hbD9Eta * ∑ i : Fin K, ((p i).ofLp r) ^ 2 := by
    exact Finset.sum_le_sum (fun r _ => hscalar r)
  calc
    ∑ i : Fin K,
        inner ℝ (p i)
          (hbMultiplierEpsilon •
              (hbL0 q • y i - p i) +
            ((hbL0 q • y i - p i) -
              (hbL0 q • y (cycleFinShift (K - 1) i) -
                p (cycleFinShift (K - 1) i))) +
            (4 / 25 : ℝ) •
              ((hbL0 q • y i - p i) -
                (hbL0 q • y (cycleFinShift 4 i) -
                  p (cycleFinShift 4 i)))) =
        ∑ r : Fin d, ∑ i : Fin K,
          (p i).ofLp r *
            (hbMultiplierEpsilon *
                (hbL0 q * (y i).ofLp r - (p i).ofLp r) +
              ((hbL0 q * (y i).ofLp r - (p i).ofLp r) -
                (hbL0 q * (y (cycleFinShift (K - 1) i)).ofLp r -
                  (p (cycleFinShift (K - 1) i)).ofLp r)) +
              (4 / 25 : ℝ) *
                ((hbL0 q * (y i).ofLp r - (p i).ofLp r) -
                  (hbL0 q * (y (cycleFinShift 4 i)).ofLp r -
                    (p (cycleFinShift 4 i)).ofLp r))) := by
      exact hleft
    _ ≤ ∑ r : Fin d, -hbD9Eta * ∑ i : Fin K, ((p i).ofLp r) ^ 2 :=
      hsum_scalar
    _ = -hbD9Eta * ∑ i : Fin K, ‖p i‖ ^ 2 := by
      rw [← Finset.mul_sum]
      rw [Finset.sum_comm]
      apply congrArg (fun z : ℝ => -hbD9Eta * z)
      apply Finset.sum_congr rfl
      intro i hi
      exact (hnorm_coord (p i)).symm

private theorem hbD9_quadratic_from_time_domain_coercivity
    {q a b : ℝ} (hD : ParameterDomain q a b) {d : ℕ}
    (p e s r : ℤ → Vec d)
    (hp : Summable (fun t : ℤ => ‖p t‖ ^ 2))
    (he : Summable (fun t : ℤ => ‖e t‖ ^ 2))
    (hr : Summable (fun t : ℤ => ‖r t‖ ^ 2))
    (hmr : Summable
      (fun t : ℤ => ‖hbMultiplierTimeDomain r t‖ ^ 2))
    (hme : Summable
      (fun t : ℤ => ‖hbMultiplierTimeDomain
        (fun t : ℤ => hbL0 q • e t) t‖ ^ 2))
    (hsupply : 0 ≤ ∑' t : ℤ,
      inner ℝ (p t) (hbMultiplierTimeDomain s t))
    (hsplit : ∀ t : ℤ,
      hbMultiplierTimeDomain s t =
        hbMultiplierTimeDomain r t +
          hbMultiplierTimeDomain (fun t : ℤ => hbL0 q • e t) t)
    (hcoercive : (∑' t : ℤ,
      inner ℝ (p t) (hbMultiplierTimeDomain r t)) ≤
        -hbD9Eta * hbBilateralSequenceL2Norm p ^ 2) :
    0 ≤ -hbD9Eta * hbBilateralSequenceL2Norm p ^ 2 +
      hbL0 q * hbMultiplierL2Gain *
        hbBilateralSequenceL2Norm p * hbBilateralSequenceL2Norm e := by
  have hinner_r :=
    hb_bilateral_inner_tsum_le_l2_mul_l2 hp hmr
  have hinner_e :=
    hb_bilateral_inner_tsum_le_l2_mul_l2 hp hme
  have hsum_eq :
      (∑' t : ℤ, inner ℝ (p t)
        (hbMultiplierTimeDomain s t)) =
        (∑' t : ℤ, inner ℝ (p t)
          (hbMultiplierTimeDomain r t)) +
          (∑' t : ℤ, inner ℝ (p t)
            (hbMultiplierTimeDomain (fun t : ℤ => hbL0 q • e t) t)) := by
    calc
      (∑' t : ℤ, inner ℝ (p t)
          (hbMultiplierTimeDomain s t)) =
          ∑' t : ℤ,
            (inner ℝ (p t) (hbMultiplierTimeDomain r t) +
              inner ℝ (p t)
                (hbMultiplierTimeDomain (fun t : ℤ => hbL0 q • e t) t)) := by
        apply tsum_congr
        intro t
        rw [hsplit t, inner_add_right]
      _ = (∑' t : ℤ, inner ℝ (p t)
          (hbMultiplierTimeDomain r t)) +
          (∑' t : ℤ, inner ℝ (p t)
            (hbMultiplierTimeDomain (fun t : ℤ => hbL0 q • e t) t)) := by
        rw [Summable.tsum_add hinner_r.1 hinner_e.1]
  rw [hsum_eq] at hsupply
  have hexternal :=
    hbD9_external_term_upper_bound hD p e hp he
  nlinarith [hsupply, hcoercive, hexternal]

/-- The source D9 quadratic estimate for an already-square-summable loop:
`0 <= -eta ||p||_2^2 + L0 m ||p||_2 ||e||_2`, with `p=tau D(x)`. -/
def hbD9ConditionalQuadraticEstimate (q a b : ℝ)
    (hD : ParameterDomain q a b) : Prop :=
  ∀ {d : ℕ}, 1 ≤ d → ∀ (hf : AdmissibleObjective q d) (τ : ℝ),
    0 ≤ τ → τ ≤ 1 →
      ∀ e x : ℕ → Vec d,
        hbSequenceInL2 e →
          hbSequenceInL2 x →
            hbHomotopyLoopEquation (parameterDomain_q_pos hD) a b hf τ e x →
              let p := hbHomotopyInput (parameterDomain_q_pos hD) hf τ x
              hbSequenceInL2 p ∧
                0 ≤ -(hbD9Eta) * hbSequenceL2Norm p ^ 2 +
                  hbL0 q * hbMultiplierL2Gain *
                    hbSequenceL2Norm p * hbSequenceL2Norm e

/-- The derived D9 gain estimates obtained from the quadratic estimate by the
paper's divide-by-`||p||_2` argument. -/
def hbD9ConditionalGainEstimate (q a b : ℝ)
    (hD : ParameterDomain q a b) : Prop :=
  ∀ {d : ℕ}, 1 ≤ d → ∀ (hf : AdmissibleObjective q d) (τ : ℝ),
    0 ≤ τ → τ ≤ 1 →
      ∀ e x : ℕ → Vec d,
        hbSequenceInL2 e →
          hbSequenceInL2 x →
            hbHomotopyLoopEquation (parameterDomain_q_pos hD) a b hf τ e x →
              let p := hbHomotopyInput (parameterDomain_q_pos hD) hf τ x
              hbSequenceInL2 p ∧
                hbSequenceL2Norm p ≤
                    hbL0 q * hbMultiplierL2Gain * hbSequenceL2Norm e / hbD9Eta ∧
                  hbSequenceL2Norm x ≤ hbD9C0 q a b * hbSequenceL2Norm e

private theorem hbD9ConditionalGainEstimate_of_quadratic
    {q a b : ℝ} (hbox : HB_Box q a b)
    (hquad :
      hbD9ConditionalQuadraticEstimate q a b (HB_box_subset_domain hbox)) :
    hbD9ConditionalGainEstimate q a b (HB_box_subset_domain hbox) := by
  let hD := HB_box_subset_domain hbox
  have hplant : hbPlantL2GainBound q a b (hbPlantL2Gain q a b) :=
    hbPlantL2Gain_is_bound_on_box hbox
  have hmult : hbMultiplierL2GainBound hbMultiplierL2Gain :=
    hbMultiplierL2Gain_is_bound
  have hL : 0 ≤ hbL0 q := by
    dsimp [hbL0]
    linarith [parameterDomain_q_lt_one hD]
  have hEta : 0 < hbD9Eta := by
    norm_num [hbD9Eta]
  unfold hbD9ConditionalGainEstimate
  intro d hd hf τ hτ0 hτ1 e x he hx hloop
  let p : ℕ → Vec d :=
    hbHomotopyInput (parameterDomain_q_pos hD) hf τ x
  have hquad_data :
      hbSequenceInL2 p ∧
        0 ≤ -hbD9Eta * hbSequenceL2Norm p ^ 2 +
          hbL0 q * hbMultiplierL2Gain *
            hbSequenceL2Norm p * hbSequenceL2Norm e := by
    simpa [p] using
      (hquad hd hf τ hτ0 hτ1 e x he hx hloop)
  have hmult_nonneg : 0 ≤ hbMultiplierL2Gain := hmult.1
  have he_nonneg : 0 ≤ hbSequenceL2Norm e := Real.sqrt_nonneg _
  have hrhs_nonneg :
      0 ≤ hbL0 q * hbMultiplierL2Gain * hbSequenceL2Norm e := by
    positivity
  have hp_bound :
      hbSequenceL2Norm p ≤
        hbL0 q * hbMultiplierL2Gain * hbSequenceL2Norm e / hbD9Eta := by
    by_cases hp_zero : hbSequenceL2Norm p = 0
    · rw [hp_zero]
      exact div_nonneg hrhs_nonneg hEta.le
    · have hp_pos : 0 < hbSequenceL2Norm p := by
        exact lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hp_zero)
      have hquad_mul :
          hbD9Eta * hbSequenceL2Norm p ^ 2 ≤
            hbL0 q * hbMultiplierL2Gain *
              hbSequenceL2Norm p * hbSequenceL2Norm e := by
        nlinarith [hquad_data.2]
      have hcancel :
          hbD9Eta * hbSequenceL2Norm p ≤
            hbL0 q * hbMultiplierL2Gain * hbSequenceL2Norm e := by
        by_contra hnot
        have hstrict :
            hbL0 q * hbMultiplierL2Gain * hbSequenceL2Norm e <
              hbD9Eta * hbSequenceL2Norm p :=
          lt_of_not_ge hnot
        have hstrict_mul := mul_lt_mul_of_pos_left hstrict hp_pos
        nlinarith [hquad_mul, hstrict_mul]
      apply (le_div_iff₀ hEta).2
      nlinarith [hcancel]
  have hloop_fun :
      x = fun t : ℕ => e t + hbPlantResponse q a b p t := by
    funext t
    have ht := hloop t
    simpa [hbHomotopyLoopEquation, p] using ht
  have hplant_data :=
    (hplant.2 p hquad_data.1)
  have hx_bound :
      hbSequenceL2Norm x ≤
        hbSequenceL2Norm e +
          hbPlantL2Gain q a b * hbSequenceL2Norm p := by
    rw [hloop_fun]
    have hsum := hb_sequence_l2_norm_add_le he hplant_data.1
    exact hsum.2.trans
      (by
        simpa [add_comm] using
          (add_le_add_right hplant_data.2 (hbSequenceL2Norm e)))
  refine ⟨hquad_data.1, hp_bound, ?_⟩
  dsimp [hbD9C0]
  have hscaled :=
    mul_le_mul_of_nonneg_left hp_bound hplant.1
  have hscaled' :
      hbPlantL2Gain q a b * hbSequenceL2Norm p ≤
        (hbPlantL2Gain q a b * hbL0 q * hbMultiplierL2Gain /
          hbD9Eta) * hbSequenceL2Norm e := by
    calc
      hbPlantL2Gain q a b * hbSequenceL2Norm p ≤
          hbPlantL2Gain q a b *
            (hbL0 q * hbMultiplierL2Gain *
              hbSequenceL2Norm e / hbD9Eta) := hscaled
      _ = (hbPlantL2Gain q a b * hbL0 q * hbMultiplierL2Gain /
          hbD9Eta) * hbSequenceL2Norm e := by ring
  nlinarith [hx_bound, hscaled']

private theorem hb_d9_cyclic_window_data
    {q a b : ℝ} (hbox : HB_Box q a b) {d : ℕ}
    (p y : ℤ → Vec d) (N : ℕ)
    (hrec : ∀ t : ℤ,
      y (t + 2) =
        (1 + b - a * q) • y (t + 1) -
          b • y t - a • p (t + 1)) :
    ∃ (P Y : Fin (2 * N + 1) → Vec d),
      (∀ i : Fin (2 * N + 1),
        Y i = y ((i.val : ℤ) - (N : ℤ))) ∧
      (∀ i : Fin (2 * N + 1),
        Y (cycleFinShift 1 i) =
          (1 + b - a * q) • Y i -
            b • Y (cycleFinShift ((2 * N + 1) - 1) i) -
              a • P i) ∧
      (∀ i : Fin (2 * N + 1),
        0 < i.val → i.val + 1 < 2 * N + 1 →
          P i = p ((i.val : ℤ) - (N : ℤ))) ∧
      (∀ i : Fin (2 * N + 1),
        P i =
          (a⁻¹) •
            ((1 + b - a * q) • Y i -
              b • Y (cycleFinShift ((2 * N + 1) - 1) i) -
              Y (cycleFinShift 1 i))) := by
  let K : ℕ := 2 * N + 1
  letI : NeZero K := ⟨by
    dsimp [K]
    omega⟩
  let Y : Fin K → Vec d :=
    fun i => y ((i.val : ℤ) - (N : ℤ))
  let P : Fin K → Vec d :=
    fun i =>
      (a⁻¹) •
        ((1 + b - a * q) • Y i -
          b • Y (cycleFinShift (K - 1) i) -
            Y (cycleFinShift 1 i))
  have hD := HB_box_subset_domain hbox
  have ha : a ≠ 0 := ne_of_gt hD.2.2.2.2.1
  have hcycle (i : Fin K) :
      Y (cycleFinShift 1 i) =
        (1 + b - a * q) • Y i -
          b • Y (cycleFinShift (K - 1) i) -
            a • P i := by
    dsimp [P]
    simp [smul_sub, smul_add, smul_smul, ha]
  have hinterior (i : Fin K) (hi0 : 0 < i.val)
      (hilast : i.val + 1 < K) :
      P i = p ((i.val : ℤ) - (N : ℤ)) := by
    have hnext : (cycleFinShift 1 i).val = i.val + 1 := by
      rw [cycleFinShift_val]
      exact Nat.mod_eq_of_lt (by omega)
    have hprev : (cycleFinShift (K - 1) i).val = i.val - 1 := by
      rw [cycleFinShift_val]
      have hsum : i.val + (K - 1) = (i.val - 1) + K := by
        dsimp [K]
        omega
      rw [hsum, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    have hraw := hrec ((i.val : ℤ) - (N : ℤ) - 1)
    have harg0 :
        ((i.val : ℤ) - (N : ℤ) - 1) + 1 =
          (i.val : ℤ) - (N : ℤ) := by ring
    have harg1 :
        ((i.val : ℤ) - (N : ℤ) - 1) + 2 =
          ((i.val + 1 : ℕ) : ℤ) - (N : ℤ) := by
      push_cast
      ring
    have hargprev :
        ((i.val : ℤ) - (N : ℤ) - 1) =
          ((i.val - 1 : ℕ) : ℤ) - (N : ℤ) := by
      push_cast
      omega
    rw [harg1, harg0, hargprev] at hraw
    dsimp [P, Y]
    rw [hnext, hprev]
    have hP :
        (a⁻¹) •
            ((1 + b - a * q) •
                y ((i.val : ℤ) - (N : ℤ)) -
              b • y (((i.val - 1 : ℕ) : ℤ) - (N : ℤ)) -
                y (((i.val + 1 : ℕ) : ℤ) - (N : ℤ))) =
          p ((i.val : ℤ) - (N : ℤ)) := by
      have hdiff :
          (1 + b - a * q) •
                y ((i.val : ℤ) - (N : ℤ)) -
              b • y (((i.val - 1 : ℕ) : ℤ) - (N : ℤ)) -
                y (((i.val + 1 : ℕ) : ℤ) - (N : ℤ)) =
            a • p ((i.val : ℤ) - (N : ℤ)) := by
        rw [hraw]
        abel
      rw [hdiff]
      simp [smul_smul, ha]
    exact hP
  refine ⟨P, Y, ?_, hcycle, ?_, ?_⟩
  · intro i
    rfl
  · intro i hi0 hilast
    exact hinterior i hi0 (by simpa [K] using hilast)
  · intro i
    dsimp [P]
    rfl

private theorem hb_d9_cyclic_window_interior_agreement
    {d : ℕ} {N : ℕ}
    (p y : ℤ → Vec d)
    (P Y : Fin (2 * N + 1) → Vec d)
    (hY : ∀ i : Fin (2 * N + 1),
      Y i = y ((i.val : ℤ) - (N : ℤ)))
    (hP : ∀ i : Fin (2 * N + 1),
      0 < i.val → i.val + 1 < 2 * N + 1 →
        P i = p ((i.val : ℤ) - (N : ℤ)))
    (i : Fin (2 * N + 1))
    (hi : 2 ≤ i.val) (hi5 : i.val + 5 < 2 * N + 1) :
    P i = p ((i.val : ℤ) - (N : ℤ)) ∧
      Y (cycleFinShift ((2 * N + 1) - 1) i) =
        y ((i.val : ℤ) - (N : ℤ) - 1) ∧
      P (cycleFinShift ((2 * N + 1) - 1) i) =
        p ((i.val : ℤ) - (N : ℤ) - 1) ∧
      Y (cycleFinShift 4 i) =
        y ((i.val : ℤ) - (N : ℤ) + 4) ∧
      P (cycleFinShift 4 i) =
        p ((i.val : ℤ) - (N : ℤ) + 4) := by
  have hK : 0 < 2 * N + 1 := by omega
  have hprev : (cycleFinShift ((2 * N + 1) - 1) i).val = i.val - 1 := by
    rw [cycleFinShift_val]
    have hsum :
        i.val + ((2 * N + 1) - 1) =
          (i.val - 1) + (2 * N + 1) := by omega
    rw [hsum, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  have hfour : (cycleFinShift 4 i).val = i.val + 4 := by
    rw [cycleFinShift_val]
    exact Nat.mod_eq_of_lt (by omega)
  have hprev_pos : 0 < (i.val - 1 : ℕ) := by omega
  have hprev_last : (i.val - 1) + 1 < 2 * N + 1 := by omega
  have hfour_pos : 0 < i.val + 4 := by omega
  have hfour_last : i.val + 4 + 1 < 2 * N + 1 := by omega
  have hYprev :
      Y (cycleFinShift ((2 * N + 1) - 1) i) =
        y ((i.val : ℤ) - (N : ℤ) - 1) := by
    have h := hY (cycleFinShift ((2 * N + 1) - 1) i)
    simp only [hprev] at h
    rw [h]
    push_cast
    congr 1
    omega
  have hPprev :
      P (cycleFinShift ((2 * N + 1) - 1) i) =
        p ((i.val : ℤ) - (N : ℤ) - 1) := by
    have hprev_pos' :
        0 < (cycleFinShift ((2 * N + 1) - 1) i).val := by
      simpa only [hprev] using hprev_pos
    have hprev_last' :
        (cycleFinShift ((2 * N + 1) - 1) i).val + 1 <
          2 * N + 1 := by
      simpa only [hprev] using hprev_last
    have h := hP (cycleFinShift ((2 * N + 1) - 1) i)
      hprev_pos' hprev_last'
    simp only [hprev] at h
    rw [h]
    push_cast
    congr 1
    omega
  have hYfour :
      Y (cycleFinShift 4 i) =
        y ((i.val : ℤ) - (N : ℤ) + 4) := by
    have h := hY (cycleFinShift 4 i)
    simp only [hfour] at h
    rw [h]
    push_cast
    congr 1
    ring
  have hPfour :
      P (cycleFinShift 4 i) =
        p ((i.val : ℤ) - (N : ℤ) + 4) := by
    have hfour_pos' : 0 < (cycleFinShift 4 i).val := by
      simpa only [hfour] using hfour_pos
    have hfour_last' :
        (cycleFinShift 4 i).val + 1 < 2 * N + 1 := by
      simpa only [hfour] using hfour_last
    have h := hP (cycleFinShift 4 i) hfour_pos' hfour_last'
    simp only [hfour] at h
    rw [h]
    push_cast
    congr 1
    ring
  exact ⟨hP i (by omega) (by omega), hYprev, hPprev, hYfour, hPfour⟩

private theorem hb_d9_endpoint_norms_tendsto_zero
    {d : ℕ} (u : ℤ → Vec d)
    (hu : Summable (fun t : ℤ => ‖u t‖ ^ 2)) :
    Tendsto
        (fun N : ℕ =>
          ‖u (N : ℤ)‖ + ‖u (-((N : ℤ)))‖)
        atTop (nhds 0) := by
  have hpos_sq :
      Summable (fun N : ℕ => ‖u (N : ℤ)‖ ^ 2) :=
    hu.comp_injective Int.ofNat_injective
  have hneg_inj :
      Function.Injective (fun N : ℕ => -((N : ℤ))) := by
    intro m n hmn
    have hmn' : (m : ℤ) = (n : ℤ) := by
      exact neg_injective hmn
    exact Int.ofNat_injective hmn'
  have hneg_sq :
      Summable (fun N : ℕ => ‖u (-((N : ℤ)))‖ ^ 2) :=
    hu.comp_injective hneg_inj
  have hpos :
      Tendsto (fun N : ℕ => ‖u (N : ℤ)‖) atTop (nhds 0) := by
    have hsqrt :
        Tendsto
          (fun N : ℕ => Real.sqrt (‖u (N : ℤ)‖ ^ 2))
          atTop (nhds (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).comp hpos_sq.tendsto_atTop_zero
    simpa using hsqrt
  have hneg :
      Tendsto (fun N : ℕ => ‖u (-((N : ℤ)))‖) atTop (nhds 0) := by
    have hsqrt :
        Tendsto
          (fun N : ℕ => Real.sqrt (‖u (-((N : ℤ)))‖ ^ 2))
          atTop (nhds (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).comp hneg_sq.tendsto_atTop_zero
    simpa using hsqrt
  simpa using hpos.add hneg

private theorem hb_d9_shifted_endpoint_norms_tendsto_zero
    {d : ℕ} (u : ℤ → Vec d)
    (hu : Summable (fun t : ℤ => ‖u t‖ ^ 2)) (c : ℤ) :
    Tendsto
        (fun N : ℕ =>
          ‖u ((N : ℤ) + c)‖ + ‖u (-((N : ℤ)) + c)‖)
        atTop (nhds 0) := by
  have hshift :=
    hb_bilateral_l2_shift_summable_and_norm_eq hu c
  simpa [add_comm] using
    (hb_d9_endpoint_norms_tendsto_zero (fun t : ℤ => u (t + c)) hshift.1)

private theorem hb_d9_endpoint_window_norms_tendsto_zero
    {d : ℕ} (u : ℤ → Vec d)
    (hu : Summable (fun t : ℤ => ‖u t‖ ^ 2)) :
    Tendsto
        (fun N : ℕ =>
          ∑ i : Fin 9,
            (‖u ((N : ℤ) + ((i.val : ℤ) - 4))‖ +
              ‖u (-((N : ℤ)) + ((i.val : ℤ) - 4))‖))
        atTop (nhds 0) := by
  have hzero :
      (∑ i : Fin 9, (0 : ℝ)) = 0 := by simp
  rw [← hzero]
  refine tendsto_finset_sum (Finset.univ : Finset (Fin 9))
    (fun i _ => ?_)
  · simpa using
    (hb_d9_shifted_endpoint_norms_tendsto_zero
      (u := u) (hu := hu) (c := ((i.val : ℤ) - 4)))

private def hb_d9_endpoint_window
    {d : ℕ} (u : ℤ → Vec d) (c : ℤ) (N : ℕ) : ℝ :=
  ∑ i : Fin 9,
    (‖u ((N : ℤ) + c + ((i.val : ℤ) - 4))‖ +
      ‖u (-((N : ℤ)) + c + ((i.val : ℤ) - 4))‖)

private theorem hb_d9_endpoint_window_tendsto_zero
    {d : ℕ} (u : ℤ → Vec d)
    (hu : Summable (fun t : ℤ => ‖u t‖ ^ 2)) (c : ℤ) :
    Tendsto (fun N : ℕ => hb_d9_endpoint_window u c N)
      atTop (nhds 0) := by
  simpa [hb_d9_endpoint_window, add_assoc, add_left_comm, add_comm] using
    (hb_d9_endpoint_window_norms_tendsto_zero
      (u := fun t : ℤ => u (t + c)) (hu := by
        exact (hb_bilateral_l2_shift_summable_and_norm_eq hu c).1))

private theorem hb_d9_endpoint_window_nonneg
    {d : ℕ} (u : ℤ → Vec d) (c : ℤ) (N : ℕ) :
    0 ≤ hb_d9_endpoint_window u c N := by
  unfold hb_d9_endpoint_window
  positivity

private theorem hb_d9_endpoint_le_window
    {d : ℕ} (u : ℤ → Vec d) (c₀ c : ℤ)
    (hc : c₀ - 4 ≤ c ∧ c ≤ c₀ + 4) (N : ℕ) :
    ‖u ((N : ℤ) + c)‖ ≤ hb_d9_endpoint_window u c₀ N ∧
      ‖u (-((N : ℤ)) + c)‖ ≤ hb_d9_endpoint_window u c₀ N := by
  have hx : 0 ≤ c - c₀ + 4 := by omega
  have hx' : c - c₀ + 4 ≤ 8 := by omega
  have hxcast : ((Int.toNat (c - c₀ + 4) : ℕ) : ℤ) = c - c₀ + 4 :=
    Int.toNat_of_nonneg hx
  have hxltZ :
      (((Int.toNat (c - c₀ + 4) : ℕ) : ℤ)) < 9 := by
    rw [hxcast]
    omega
  have hxlt : Int.toNat (c - c₀ + 4) < 9 := by
    exact_mod_cast hxltZ
  let j : Fin 9 := ⟨Int.toNat (c - c₀ + 4), hxlt⟩
  have hjval : (j.val : ℤ) = c - c₀ + 4 := by
    dsimp [j]
    exact hxcast
  have hsum :
      ‖u ((N : ℤ) + c₀ + ((j.val : ℤ) - 4))‖ +
          ‖u (-((N : ℤ)) + c₀ + ((j.val : ℤ) - 4))‖ ≤
        hb_d9_endpoint_window u c₀ N := by
    unfold hb_d9_endpoint_window
    simpa using
      (Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin 9)))
        (f := fun i : Fin 9 =>
          ‖u ((N : ℤ) + c₀ + ((i.val : ℤ) - 4))‖ +
            ‖u (-((N : ℤ)) + c₀ + ((i.val : ℤ) - 4))‖)
        (fun i hi => by positivity) (Finset.mem_univ j))
  have hsum' :
      ‖u ((N : ℤ) + c)‖ + ‖u (-((N : ℤ)) + c)‖ ≤
        hb_d9_endpoint_window u c₀ N := by
    simpa [hjval] using hsum
  have hpos :
      ‖u ((N : ℤ) + c)‖ ≤ hb_d9_endpoint_window u c₀ N := by
    have h := le_trans
      (le_add_of_nonneg_right (norm_nonneg (u (-((N : ℤ)) + c)))) hsum'
    exact h
  have hneg :
      ‖u (-((N : ℤ)) + c)‖ ≤ hb_d9_endpoint_window u c₀ N := by
    have h := le_trans
      (le_add_of_nonneg_left (norm_nonneg (u ((N : ℤ) + c)))) hsum'
    exact h
  exact ⟨hpos, hneg⟩

private def hb_d9_endpoint_envelope
    {d : ℕ} (u : ℤ → Vec d) (N : ℕ) : ℝ :=
  hb_d9_endpoint_window u (-3) N + hb_d9_endpoint_window u 3 N

private theorem hb_d9_endpoint_envelope_nonneg
    {d : ℕ} (u : ℤ → Vec d) (N : ℕ) :
    0 ≤ hb_d9_endpoint_envelope u N := by
  unfold hb_d9_endpoint_envelope
  exact add_nonneg
    (hb_d9_endpoint_window_nonneg u (-3) N)
    (hb_d9_endpoint_window_nonneg u 3 N)

private theorem hb_d9_endpoint_envelope_tendsto_zero
    {d : ℕ} (u : ℤ → Vec d)
    (hu : Summable (fun t : ℤ => ‖u t‖ ^ 2)) :
    Tendsto (fun N : ℕ => hb_d9_endpoint_envelope u N)
      atTop (nhds 0) := by
  unfold hb_d9_endpoint_envelope
  simpa using
    (hb_d9_endpoint_window_tendsto_zero u hu (-3)).add
      (hb_d9_endpoint_window_tendsto_zero u hu 3)

private theorem hb_d9_endpoint_le_envelope
    {d : ℕ} (u : ℤ → Vec d) (N : ℕ) {c : ℤ}
    (hc : -7 ≤ c ∧ c ≤ 7) :
    ‖u ((N : ℤ) + c)‖ ≤ hb_d9_endpoint_envelope u N ∧
      ‖u (-((N : ℤ)) + c)‖ ≤ hb_d9_endpoint_envelope u N := by
  by_cases hcle : c ≤ 1
  · have hwin := hb_d9_endpoint_le_window u (-3) c (by omega) N
    have hle :
        hb_d9_endpoint_window u (-3) N ≤
          hb_d9_endpoint_envelope u N := by
      unfold hb_d9_endpoint_envelope
      exact le_add_of_nonneg_right
        (hb_d9_endpoint_window_nonneg u 3 N)
    exact ⟨hwin.1.trans hle, hwin.2.trans hle⟩
  · have hwin := hb_d9_endpoint_le_window u 3 c (by omega) N
    have hle :
        hb_d9_endpoint_window u 3 N ≤
          hb_d9_endpoint_envelope u N := by
      unfold hb_d9_endpoint_envelope
      exact le_add_of_nonneg_left
        (hb_d9_endpoint_window_nonneg u (-3) N)
    exact ⟨hwin.1.trans hle, hwin.2.trans hle⟩

private theorem hb_d9_odd_window_reindex
    (f : ℤ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range (2 * N + 1),
      f (Equiv.intEquivNat.symm k)) =
      ∑ i : Fin (2 * N + 1), f ((i.val : ℤ) - (N : ℤ)) := by
  have hK : 0 < 2 * N + 1 := by omega
  have hmap :
      ∀ i : Fin (2 * N + 1),
        Equiv.intEquivNat ((i.val : ℤ) - (N : ℤ)) < 2 * N + 1 := by
    intro i
    have hlow :
        -(N : ℤ) ≤ (i.val : ℤ) - (N : ℤ) := by omega
    have hhigh :
        (i.val : ℤ) - (N : ℤ) ≤ (N : ℤ) := by omega
    cases h : ((i.val : ℤ) - (N : ℤ)) with
    | ofNat n =>
        have hnZ : (n : ℤ) ≤ (N : ℤ) := by
          simpa [h] using hhigh
        have hn : n ≤ N := by exact_mod_cast hnZ
        have he :
            Equiv.intEquivNat (Int.ofNat n) = 2 * n := by
          change Nat.bit false n = 2 * n
          simp [Nat.bit_false]
        rw [he]
        omega
    | negSucc n =>
        have hnZ : -(N : ℤ) ≤ Int.negSucc n := by
          rw [← h]
          exact hlow
        have hn : n < N := by omega
        have he :
            Equiv.intEquivNat (Int.negSucc n) = 2 * n + 1 := by
          change Nat.bit true n = 2 * n + 1
          simp [Nat.bit_true]
        rw [he]
        omega
  let σ : Fin (2 * N + 1) → Fin (2 * N + 1) :=
    fun i => ⟨Equiv.intEquivNat ((i.val : ℤ) - (N : ℤ)), hmap i⟩
  have hσ : Function.Bijective σ := by
    constructor
    · intro i j hij
      apply Fin.ext
      have hij' : (σ i).val = (σ j).val := congrArg Fin.val hij
      have hback :
          Equiv.intEquivNat.symm (σ i).val =
            Equiv.intEquivNat.symm (σ j).val :=
        congrArg (fun k : ℕ => Equiv.intEquivNat.symm k) hij'
      have hback' :
          (i.val : ℤ) - (N : ℤ) =
            (j.val : ℤ) - (N : ℤ) := by
        simpa [σ] using hback
      omega
    · intro j
      let t : ℤ := Equiv.intEquivNat.symm j.val
      have hlow :
          -(N : ℤ) ≤ t := by
        dsimp [t]
        cases h : Equiv.intEquivNat.symm j.val with
        | ofNat n =>
            have hn0 : (0 : ℤ) ≤ (n : ℤ) := Int.ofNat_nonneg n
            exact le_trans (by omega) hn0
        | negSucc n =>
            have hj : j.val < 2 * N + 1 := j.isLt
            have hj_eq :
                Equiv.intEquivNat (Int.negSucc n) = j.val := by
              rw [← h]
              exact Equiv.apply_symm_apply _ _
            have he :
                Equiv.intEquivNat (Int.negSucc n) = 2 * n + 1 := by
              change Nat.bit true n = 2 * n + 1
              simp [Nat.bit_true]
            rw [he] at hj_eq
            omega
      have hhigh :
          t ≤ (N : ℤ) := by
        dsimp [t]
        cases h : Equiv.intEquivNat.symm j.val with
        | ofNat n =>
            have hj : j.val < 2 * N + 1 := j.isLt
            have hj_eq :
                Equiv.intEquivNat (Int.ofNat n) = j.val := by
              rw [← h]
              exact Equiv.apply_symm_apply _ _
            have he :
                Equiv.intEquivNat (Int.ofNat n) = 2 * n := by
              change Nat.bit false n = 2 * n
              simp [Nat.bit_false]
            rw [he] at hj_eq
            have hn : n ≤ N := by omega
            have hnZ : (n : ℤ) ≤ (N : ℤ) := by exact_mod_cast hn
            simpa using hnZ
        | negSucc n =>
            omega
      have ht_nonneg : 0 ≤ t + (N : ℤ) := by omega
      have ht_cast :
          (((t + (N : ℤ)).toNat : ℕ) : ℤ) = t + (N : ℤ) :=
        Int.toNat_of_nonneg ht_nonneg
      have ht_lt :
          (t + (N : ℤ)).toNat < 2 * N + 1 := by
        have ht_lt' :
            (((t + (N : ℤ)).toNat : ℕ) : ℤ) <
              (2 * N + 1 : ℕ) := by
          rw [ht_cast]
          omega
        exact_mod_cast ht_lt'
      let i : Fin (2 * N + 1) :=
        ⟨(t + (N : ℤ)).toNat, ht_lt⟩
      refine ⟨i, ?_⟩
      apply Fin.ext
      have hi_eq :
          (i.val : ℤ) - (N : ℤ) = t := by
        dsimp [i]
        rw [ht_cast]
        ring
      have hσi :
          (σ i).val = j.val := by
        dsimp [σ]
        rw [hi_eq]
        exact Equiv.apply_symm_apply _ _
      exact hσi
  calc
    (∑ k ∈ Finset.range (2 * N + 1),
        f (Equiv.intEquivNat.symm k)) =
        ∑ i : Fin (2 * N + 1),
          f (Equiv.intEquivNat.symm i.val) := by
      symm
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Finset.mem_range] at hk
      have hk' : k ≤ 2 * N := by omega
      simp [hk']
    _ = ∑ i : Fin (2 * N + 1),
          f ((i.val : ℤ) - (N : ℤ)) := by
      have hsum := Fintype.sum_bijective σ hσ
        (fun i : Fin (2 * N + 1) =>
          f ((i.val : ℤ) - (N : ℤ)))
        (fun i : Fin (2 * N + 1) =>
          f (Equiv.intEquivNat.symm i.val))
        (by
          intro i
          dsimp [σ]
          rw [Equiv.symm_apply_apply])
      exact hsum.symm

private theorem hb_d9_boundary_card_le_seven (N : ℕ) :
    (Finset.univ.filter (fun i : Fin (2 * N + 1) =>
      ¬ (2 ≤ i.val ∧ i.val + 5 < 2 * N + 1))).card ≤ 7 := by
  let K : ℕ := 2 * N + 1
  let B : Finset (Fin K) :=
    Finset.univ.filter (fun i : Fin K =>
      ¬ (2 ≤ i.val ∧ i.val + 5 < K))
  let f : Fin K → Fin 7 :=
    fun i =>
      ⟨(if i.val < 2 then i.val else 2 + (i.val + 5 - K)) % 7,
        Nat.mod_lt _ (by norm_num)⟩
  have hf_inj : Set.InjOn f B := by
    intro i hi j hj hij
    have hiB : ¬ (2 ≤ i.val ∧ i.val + 5 < K) :=
      (Finset.mem_filter.mp hi).2
    have hjB : ¬ (2 ≤ j.val ∧ j.val + 5 < K) :=
      (Finset.mem_filter.mp hj).2
    by_cases hi0 : i.val < 2
    · by_cases hj0 : j.val < 2
      · apply Fin.ext
        have hvals := congrArg Fin.val hij
        simpa [f, hi0, hj0,
          Nat.mod_eq_of_lt (show i.val < 7 by omega),
          Nat.mod_eq_of_lt (show j.val < 7 by omega)] using hvals
      · have hjlow : 2 ≤ j.val := by omega
        have hjhigh : j.val + 5 - K ≤ 4 := by
          have hjlt : j.val < K := j.isLt
          omega
        have hjf : 2 + (j.val + 5 - K) < 7 := by omega
        have hjmod :
            (2 + (j.val + 5 - K)) % 7 = 2 + (j.val + 5 - K) :=
          Nat.mod_eq_of_lt hjf
        have hvals := congrArg Fin.val hij
        simp [f, hi0, hj0, hjmod] at hvals
        omega
    · have hilow : 2 ≤ i.val := by omega
      have hilast : K ≤ i.val + 5 := by
        by_contra hnot
        exact hiB ⟨hilow, by omega⟩
      have hilow' : 0 ≤ i.val + 5 - K := by omega
      have hihigh : i.val + 5 - K ≤ 4 := by
        have hilt : i.val < K := i.isLt
        omega
      have hif : 2 + (i.val + 5 - K) < 7 := by omega
      have himod :
          (2 + (i.val + 5 - K)) % 7 = 2 + (i.val + 5 - K) :=
        Nat.mod_eq_of_lt hif
      by_cases hj0 : j.val < 2
      · have hvals := congrArg Fin.val hij
        simp [f, hi0, hj0, himod] at hvals
        omega
      · have hjlow : 2 ≤ j.val := by omega
        have hjlast : K ≤ j.val + 5 := by
          by_contra hnot
          exact hjB ⟨hjlow, by omega⟩
        have hjhigh : j.val + 5 - K ≤ 4 := by
          have hjlt : j.val < K := j.isLt
          omega
        have hjf : 2 + (j.val + 5 - K) < 7 := by omega
        have hjmod :
            (2 + (j.val + 5 - K)) % 7 = 2 + (j.val + 5 - K) :=
          Nat.mod_eq_of_lt hjf
        have hvals := congrArg Fin.val hij
        simp [f, hi0, hj0, himod, hjmod] at hvals
        apply Fin.ext
        omega
  have himage :
      (B.image f).card = B.card :=
    Finset.card_image_iff.mpr hf_inj
  have hsub : B.image f ⊆ (Finset.univ : Finset (Fin 7)) :=
    Finset.subset_univ _
  have hcard : B.card ≤ 7 := by
    rw [← himage]
    calc
      (B.image f).card ≤ (Finset.univ : Finset (Fin 7)).card :=
        Finset.card_le_card hsub
      _ = 7 := by simp
  change B.card ≤ 7
  exact hcard

private theorem hb_d9_sum_difference_on_filter
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (keep : ι → Prop) [DecidablePred keep]
    (F G : ι → ℝ)
    (hEq : ∀ i ∈ s, ¬ keep i → F i = G i) :
    |∑ i ∈ s, F i - ∑ i ∈ s, G i| ≤
      ∑ i ∈ s.filter keep, |F i| + ∑ i ∈ s.filter keep, |G i| := by
  have hsplitF :
      (∑ i ∈ s, F i) =
        (∑ i ∈ s.filter keep, F i) +
          (∑ i ∈ s.filter (fun i => ¬ keep i), F i) := by
    symm
    exact Finset.sum_filter_add_sum_filter_not s keep F
  have hsplitG :
      (∑ i ∈ s, G i) =
        (∑ i ∈ s.filter keep, G i) +
          (∑ i ∈ s.filter (fun i => ¬ keep i), G i) := by
    symm
    exact Finset.sum_filter_add_sum_filter_not s keep G
  have hEqsum :
      (∑ i ∈ s.filter (fun i => ¬ keep i), F i) =
        ∑ i ∈ s.filter (fun i => ¬ keep i), G i := by
    apply Finset.sum_congr rfl
    intro i hi
    apply hEq i (Finset.mem_filter.mp hi).1
    exact (Finset.mem_filter.mp hi).2
  rw [hsplitF, hsplitG, hEqsum]
  calc
    |(∑ i ∈ s.filter keep, F i) +
          (∑ i ∈ s.filter (fun i => ¬ keep i), G i) -
        ((∑ i ∈ s.filter keep, G i) +
          (∑ i ∈ s.filter (fun i => ¬ keep i), G i))| ≤
        |∑ i ∈ s.filter keep, F i -
          ∑ i ∈ s.filter keep, G i| := by
            apply le_of_eq
            congr 1
            ring
    _ ≤ |∑ i ∈ s.filter keep, F i| +
          |∑ i ∈ s.filter keep, G i| := by
        simpa using
        (abs_sub_le
          (∑ i ∈ s.filter keep, F i)
          0
          (∑ i ∈ s.filter keep, G i))
    _ ≤ ∑ i ∈ s.filter keep, |F i| +
          ∑ i ∈ s.filter keep, |G i| := by
      exact add_le_add
        (by
          simpa using
            (Finset.abs_sum_le_sum_abs F (s.filter keep)))
        (by
          simpa using
            (Finset.abs_sum_le_sum_abs G (s.filter keep)))

private def hb_d9_boundary_error_constant (q a b : ℝ) : ℝ :=
  let A : ℝ :=
    ‖(a⁻¹ : ℝ)‖ *
      (‖(1 + b - a * q : ℝ)‖ + ‖(b : ℝ)‖ + 1)
  let B : ℝ := ‖(hbL0 q : ℝ)‖ + A + 1
  let H : ℝ :=
    ‖(hbMultiplierEpsilon : ℝ)‖ + 2 +
      2 * ‖(4 / 25 : ℝ)‖
  7 * (H * B + A * H * B + hbD9Eta * A ^ 2 + hbD9Eta)

private theorem hb_d9_cyclic_window_boundary_error_ordered
    {q a b : ℝ} (hbox : HB_Box q a b) {d : ℕ}
    (p y : ℤ → Vec d)
    (hp : Summable (fun t : ℤ => ‖p t‖ ^ 2))
    (hy : Summable (fun t : ℤ => ‖y t‖ ^ 2)) (N : ℕ)
    (hrec : ∀ t : ℤ,
      y (t + 2) =
        (1 + b - a * q) • y (t + 1) -
          b • y t - a • p (t + 1)) :
    ∃ errN : ℝ, 0 ≤ errN ∧
      (∑ i : Fin (2 * N + 1),
        inner ℝ (p ((i.val : ℤ) - (N : ℤ)))
          (hbMultiplierTimeDomain
            (fun t : ℤ => hbL0 q • y t - p t)
            ((i.val : ℤ) - (N : ℤ)))) ≤
      (∑ i : Fin (2 * N + 1),
        -hbD9Eta * ‖p ((i.val : ℤ) - (N : ℤ))‖ ^ 2) + errN ∧
      errN ≤ hb_d9_boundary_error_constant q a b *
        (hb_d9_endpoint_envelope p N + hb_d9_endpoint_envelope y N) ^ 2 := by
  classical
  rcases hb_d9_cyclic_window_data hbox p y N hrec with
    ⟨P, Y, hY, hcycle, hP, hPform⟩
  let boundary : Fin (2 * N + 1) → Prop :=
    fun i => ¬ (2 ≤ i.val ∧ i.val + 5 < 2 * N + 1)
  let rawL : Fin (2 * N + 1) → ℝ :=
    fun i =>
      inner ℝ (p ((i.val : ℤ) - (N : ℤ)))
        (hbMultiplierTimeDomain
          (fun t : ℤ => hbL0 q • y t - p t)
          ((i.val : ℤ) - (N : ℤ)))
  let cycL : Fin (2 * N + 1) → ℝ :=
    fun i =>
      inner ℝ (P i)
        (hbMultiplierEpsilon •
            (hbL0 q • Y i - P i) +
          ((hbL0 q • Y i - P i) -
            (hbL0 q • Y (cycleFinShift ((2 * N + 1) - 1) i) -
              P (cycleFinShift ((2 * N + 1) - 1) i))) +
          (4 / 25 : ℝ) •
            ((hbL0 q • Y i - P i) -
              (hbL0 q • Y (cycleFinShift 4 i) -
                P (cycleFinShift 4 i))))
  let rawR : Fin (2 * N + 1) → ℝ :=
    fun i => -hbD9Eta * ‖p ((i.val : ℤ) - (N : ℤ))‖ ^ 2
  let cycR : Fin (2 * N + 1) → ℝ :=
    fun i => -hbD9Eta * ‖P i‖ ^ 2
  let errL : ℝ :=
    ∑ i ∈ (Finset.univ.filter boundary), |rawL i| +
      ∑ i ∈ (Finset.univ.filter boundary), |cycL i|
  let errR : ℝ :=
    ∑ i ∈ (Finset.univ.filter boundary), |cycR i| +
      ∑ i ∈ (Finset.univ.filter boundary), |rawR i|
  let E : ℕ → ℝ :=
    fun n => hb_d9_endpoint_envelope p n + hb_d9_endpoint_envelope y n
  have hE_nonneg (n : ℕ) : 0 ≤ E n := by
    dsimp [E]
    exact add_nonneg
      (hb_d9_endpoint_envelope_nonneg p n)
      (hb_d9_endpoint_envelope_nonneg y n)
  have hE_tendsto : Tendsto E atTop (nhds 0) := by
    dsimp [E]
    simpa using
      (hb_d9_endpoint_envelope_tendsto_zero p hp).add
        (hb_d9_endpoint_envelope_tendsto_zero y hy)
  have hraw_endpoint
      (u : ℤ → Vec d) (i : Fin (2 * N + 1))
      (hbi : boundary i) (c : ℤ)
      (hc : -1 ≤ c ∧ c ≤ 4) :
      ‖u (((i.val : ℤ) - (N : ℤ)) + c)‖ ≤
        hb_d9_endpoint_envelope u N := by
    dsimp [boundary] at hbi
    by_cases hleft : i.val < 2
    · have hwin := hb_d9_endpoint_le_envelope u N
        (c := (i.val : ℤ) + c) (by omega)
      have harg :
          ((i.val : ℤ) - (N : ℤ)) + c =
            -((N : ℤ)) + ((i.val : ℤ) + c) := by ring
      rw [harg]
      exact hwin.2
    · have hiright : 2 * N + 1 ≤ i.val + 5 := by
        by_contra hnot
        exact hbi ⟨by omega, by omega⟩
      let r : ℤ := (i.val : ℤ) - (2 * N + 1 : ℕ)
      have hr : -5 ≤ r ∧ r ≤ 0 := by
        dsimp [r]
        omega
      have hwin := hb_d9_endpoint_le_envelope u N
        (c := r + 1 + c) (by omega)
      have harg :
          ((i.val : ℤ) - (N : ℤ)) + c =
            (N : ℤ) + (r + 1 + c) := by
        dsimp [r]
        push_cast
        ring
      rw [harg]
      exact hwin.1
  have hpE (n : ℕ) :
      hb_d9_endpoint_envelope p n ≤ E n := by
    dsimp [E]
    exact le_add_of_nonneg_right
      (hb_d9_endpoint_envelope_nonneg y n)
  have hyE (n : ℕ) :
      hb_d9_endpoint_envelope y n ≤ E n := by
    dsimp [E]
    exact le_add_of_nonneg_left
      (hb_d9_endpoint_envelope_nonneg p n)
  let near : Fin (2 * N + 1) → Prop :=
    fun j => j.val < 8 ∨ j.val + 8 ≥ 2 * N + 1
  have hYnear (j : Fin (2 * N + 1)) (hj : near j) :
      ‖Y j‖ ≤ E N := by
    dsimp [near] at hj
    by_cases hleft : j.val < 8
    · have hwin := hb_d9_endpoint_le_envelope y N
        (c := (j.val : ℤ)) (by omega)
      have harg :
          ((j.val : ℤ) - (N : ℤ)) =
            -((N : ℤ)) + (j.val : ℤ) := by ring
      rw [hY j, harg]
      exact hwin.2.trans (hyE N)
    · have hiright : 2 * N + 1 ≤ j.val + 8 := by omega
      let r : ℤ := (j.val : ℤ) - (2 * N + 1 : ℕ)
      have hr : -8 ≤ r ∧ r ≤ 0 := by
        dsimp [r]
        omega
      have hwin := hb_d9_endpoint_le_envelope y N
        (c := r + 1) (by omega)
      have harg :
          ((j.val : ℤ) - (N : ℤ)) =
            (N : ℤ) + (r + 1) := by
        dsimp [r]
        push_cast
        ring
      rw [hY j, harg]
      exact hwin.1.trans (hyE N)
  have hnear_forward (i : Fin (2 * N + 1)) (hbi : boundary i)
      (k : ℕ) (hk : k ≤ 5) : near (cycleFinShift k i) := by
    dsimp [boundary] at hbi
    dsimp [near]
    rw [cycleFinShift_val]
    by_cases hsmall : 2 * N + 1 ≤ 5
    · have hlt : (i.val + k) % (2 * N + 1) < 8 := by
        have hm := Nat.mod_lt (i.val + k) (by omega : 0 < 2 * N + 1)
        omega
      omega
    · by_cases hleft : i.val < 2
      · have hK : 6 ≤ 2 * N + 1 := by omega
        have hlt : i.val + k < 2 * N + 1 := by omega
        rw [Nat.mod_eq_of_lt hlt]
        omega
      · have hiright : 2 * N + 1 ≤ i.val + 5 := by
          by_contra hnot
          exact hbi ⟨by omega, by omega⟩
        by_cases hlt : i.val + k < 2 * N + 1
        · rw [Nat.mod_eq_of_lt hlt]
          omega
        · have hsub :
              (i.val + k) % (2 * N + 1) =
                (i.val + k - (2 * N + 1)) % (2 * N + 1) := by
            rw [Nat.mod_eq_sub_mod (by omega)]
          rw [hsub]
          by_cases hlt' : i.val + k - (2 * N + 1) <
              2 * N + 1
          · rw [Nat.mod_eq_of_lt hlt']
            omega
          · omega
  have hnear_prev (i : Fin (2 * N + 1)) (hbi : boundary i) :
      near (cycleFinShift ((2 * N + 1) - 1) i) := by
    dsimp [boundary] at hbi
    dsimp [near]
    rw [cycleFinShift_val]
    by_cases hi0 : i.val = 0
    · simp only [hi0, Nat.zero_add]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · have hi_pos : 1 ≤ i.val := by omega
      have hsum :
          i.val + 2 * N =
            (i.val - 1) + (2 * N + 1) := by omega
      rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      by_cases hleft : i.val < 2
      · omega
      · have hiright : 2 * N + 1 ≤ i.val + 5 := by
          by_contra hnot
          exact hbi ⟨by omega, by omega⟩
        omega
  have hnear_prevprev (i : Fin (2 * N + 1)) (hbi : boundary i) :
      near (cycleFinShift ((2 * N + 1) - 2) i) := by
    dsimp [boundary] at hbi
    dsimp [near]
    rw [cycleFinShift_val]
    by_cases hsmall : 2 * N + 1 ≤ 8
    · have hm := Nat.mod_lt
        (i.val + ((2 * N + 1) - 2)) (by omega : 0 < 2 * N + 1)
      omega
    · by_cases hi0 : i.val = 0
      · simp only [hi0, Nat.zero_add]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      · by_cases hi1 : i.val = 1
        · have hsum :
              i.val + ((2 * N + 1) - 2) =
                (2 * N + 1) - 1 := by omega
          rw [hsum, Nat.mod_eq_of_lt (by omega)]
          omega
        · have hi2 : 2 ≤ i.val := by omega
          have hsum :
              i.val + ((2 * N + 1) - 2) =
                (i.val - 2) + (2 * N + 1) := by omega
          rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          have hiright : 2 * N + 1 ≤ i.val + 5 := by
            by_contra hnot
            exact hbi ⟨by omega, by omega⟩
          omega
  have hnear_next_prev (i : Fin (2 * N + 1)) (hbi : boundary i) :
      near (cycleFinShift 1 (cycleFinShift ((2 * N + 1) - 1) i)) := by
    rw [cycleFinShift_add]
    have hperiod :
        (2 * N + 1 - 1) + 1 = 0 + (2 * N + 1) := by omega
    rw [hperiod, cycleFinShift_period]
    have hzero : cycleFinShift 0 i = i := by
      simp [cycleFinShift]
    rw [hzero]
    dsimp [near, boundary] at hbi ⊢
    omega
  have hnear_self (i : Fin (2 * N + 1)) (hbi : boundary i) :
      near i := by
    dsimp [near, boundary] at hbi ⊢
    omega
  let A : ℝ :=
    ‖(a⁻¹ : ℝ)‖ *
      (‖(1 + b - a * q : ℝ)‖ + ‖(b : ℝ)‖ + 1)
  have hPbound (j : Fin (2 * N + 1))
      (hj : near j)
      (hjprev : near (cycleFinShift ((2 * N + 1) - 1) j))
      (hjnext : near (cycleFinShift 1 j)) :
      ‖P j‖ ≤ A * E N := by
    have hyj := hYnear j hj
    have hyprev := hYnear
      (cycleFinShift ((2 * N + 1) - 1) j) hjprev
    have hynext := hYnear (cycleFinShift 1 j) hjnext
    have hinside :
        ‖(1 + b - a * q) • Y j -
              b • Y (cycleFinShift ((2 * N + 1) - 1) j) -
              Y (cycleFinShift 1 j)‖ ≤
          ‖(1 + b - a * q)‖ * ‖Y j‖ +
            ‖(b : ℝ)‖ *
              ‖Y (cycleFinShift ((2 * N + 1) - 1) j)‖ +
            ‖Y (cycleFinShift 1 j)‖ := by
      calc
        ‖(1 + b - a * q) • Y j -
              b • Y (cycleFinShift ((2 * N + 1) - 1) j) -
              Y (cycleFinShift 1 j)‖ ≤
            ‖(1 + b - a * q) • Y j -
                b • Y (cycleFinShift ((2 * N + 1) - 1) j)‖ +
              ‖Y (cycleFinShift 1 j)‖ := norm_sub_le _ _
        _ ≤
            (‖(1 + b - a * q) • Y j‖ +
                ‖b • Y (cycleFinShift ((2 * N + 1) - 1) j)‖) +
              ‖Y (cycleFinShift 1 j)‖ := by
          gcongr
          exact norm_sub_le _ _
        _ = ‖(1 + b - a * q)‖ * ‖Y j‖ +
            ‖(b : ℝ)‖ *
              ‖Y (cycleFinShift ((2 * N + 1) - 1) j)‖ +
            ‖Y (cycleFinShift 1 j)‖ := by
          rw [norm_smul, norm_smul]
    have hinside' :
        ‖(1 + b - a * q)‖ * ‖Y j‖ +
            ‖(b : ℝ)‖ *
              ‖Y (cycleFinShift ((2 * N + 1) - 1) j)‖ +
            ‖Y (cycleFinShift 1 j)‖ ≤
          (‖(1 + b - a * q)‖ + ‖(b : ℝ)‖ + 1) * E N := by
      calc
        ‖(1 + b - a * q)‖ * ‖Y j‖ +
              ‖(b : ℝ)‖ *
                ‖Y (cycleFinShift ((2 * N + 1) - 1) j)‖ +
              ‖Y (cycleFinShift 1 j)‖ ≤
            ‖(1 + b - a * q)‖ * E N +
              ‖(b : ℝ)‖ * E N + 1 * E N := by
          have h1 :=
            mul_le_mul_of_nonneg_left hyj
              (norm_nonneg (1 + b - a * q : ℝ))
          have h2 :=
            mul_le_mul_of_nonneg_left hyprev
              (norm_nonneg (b : ℝ))
          have h3 : ‖Y (cycleFinShift 1 j)‖ ≤ 1 * E N := by
            simpa using hynext
          exact add_le_add (add_le_add h1 h2) h3
        _ = (‖(1 + b - a * q)‖ + ‖(b : ℝ)‖ + 1) * E N := by ring
    rw [hPform j, norm_smul]
    calc
      ‖(a⁻¹ : ℝ)‖ *
          ‖(1 + b - a * q) • Y j -
            b • Y (cycleFinShift ((2 * N + 1) - 1) j) -
            Y (cycleFinShift 1 j)‖ ≤
          ‖(a⁻¹ : ℝ)‖ *
            ((‖(1 + b - a * q)‖ + ‖(b : ℝ)‖ + 1) * E N) :=
        mul_le_mul_of_nonneg_left (hinside.trans hinside')
          (norm_nonneg (a⁻¹ : ℝ))
      _ = A * E N := by
        dsimp [A]
        ring
  have hprevprev_index (i : Fin (2 * N + 1)) :
      cycleFinShift ((2 * N + 1) - 1)
          (cycleFinShift ((2 * N + 1) - 1) i) =
        cycleFinShift ((2 * N + 1) - 2) i := by
    by_cases hN : N = 0
    · subst N
      simp [cycleFinShift]
    · have hNpos : 1 ≤ N := by omega
      rw [cycleFinShift_add]
      have hsum :
          (2 * N + 1 - 1) + (2 * N + 1 - 1) =
            (2 * N + 1 - 2) + (2 * N + 1) := by omega
      rw [hsum, cycleFinShift_period]
  have hprev_four_index (i : Fin (2 * N + 1)) :
      cycleFinShift ((2 * N + 1) - 1) (cycleFinShift 4 i) =
        cycleFinShift 3 i := by
    rw [cycleFinShift_add]
    have hsum :
        4 + (2 * N + 1 - 1) = 3 + (2 * N + 1) := by omega
    rw [hsum, cycleFinShift_period]
  have hnext_four_index (i : Fin (2 * N + 1)) :
      cycleFinShift 1 (cycleFinShift 4 i) =
        cycleFinShift 5 i := by
    rw [cycleFinShift_add]
  let L : ℝ := ‖(hbL0 q : ℝ)‖
  let B : ℝ := L + A + 1
  let H : ℝ :=
    ‖(hbMultiplierEpsilon : ℝ)‖ + 2 +
      2 * ‖(4 / 25 : ℝ)‖
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    positivity
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hH_nonneg : 0 ≤ H := by
    dsimp [H]
    positivity
  have hz_bound (u v : Vec d)
      (hu : ‖u‖ ≤ E N) (hv : ‖v‖ ≤ A * E N) :
      ‖hbL0 q • u - v‖ ≤ B * E N := by
    have hnorm :
        ‖hbL0 q • u - v‖ ≤
          ‖(hbL0 q : ℝ)‖ * ‖u‖ + ‖v‖ := by
      calc
        ‖hbL0 q • u - v‖ ≤ ‖hbL0 q • u‖ + ‖v‖ :=
          norm_sub_le _ _
        _ = ‖(hbL0 q : ℝ)‖ * ‖u‖ + ‖v‖ := by
          rw [norm_smul]
    have hfirst :
        ‖(hbL0 q : ℝ)‖ * ‖u‖ ≤ L * E N := by
      dsimp [L]
      exact mul_le_mul_of_nonneg_left hu
        (norm_nonneg (hbL0 q : ℝ))
    exact hnorm.trans
      (by
        calc
          ‖(hbL0 q : ℝ)‖ * ‖u‖ + ‖v‖ ≤
              L * E N + A * E N := add_le_add hfirst hv
          _ ≤ B * E N := by
            dsimp [B]
            ring_nf
            linarith [hE_nonneg N]
      )
  have hz_raw_bound (u v : Vec d)
      (hu : ‖u‖ ≤ E N) (hv : ‖v‖ ≤ E N) :
      ‖hbL0 q • u - v‖ ≤ B * E N := by
    have hnorm :
        ‖hbL0 q • u - v‖ ≤
          ‖(hbL0 q : ℝ)‖ * ‖u‖ + ‖v‖ := by
      calc
        ‖hbL0 q • u - v‖ ≤ ‖hbL0 q • u‖ + ‖v‖ :=
          norm_sub_le _ _
        _ = ‖(hbL0 q : ℝ)‖ * ‖u‖ + ‖v‖ := by
          rw [norm_smul]
    have hfirst :
        ‖(hbL0 q : ℝ)‖ * ‖u‖ ≤ L * E N := by
      dsimp [L]
      exact mul_le_mul_of_nonneg_left hu
        (norm_nonneg (hbL0 q : ℝ))
    exact hnorm.trans
      (by
        calc
          ‖(hbL0 q : ℝ)‖ * ‖u‖ + ‖v‖ ≤
              L * E N + E N := add_le_add hfirst hv
          _ ≤ B * E N := by
            dsimp [B]
            calc
              L * E N + E N ≤ L * E N + E N + A * E N :=
                le_add_of_nonneg_right (mul_nonneg hA_nonneg (hE_nonneg N))
              _ = (L + A + 1) * E N := by ring)
  have hmult_bound (z₀ z₁ z₄ : Vec d)
      (h₀ : ‖z₀‖ ≤ B * E N) (h₁ : ‖z₁‖ ≤ B * E N)
      (h₄ : ‖z₄‖ ≤ B * E N) :
      ‖hbMultiplierEpsilon • z₀ + (z₀ - z₁) +
          (4 / 25 : ℝ) • (z₀ - z₄)‖ ≤ H * B * E N := by
    have hD : 0 ≤ B * E N := mul_nonneg hB_nonneg (hE_nonneg N)
    have hnorm :
        ‖hbMultiplierEpsilon • z₀ + (z₀ - z₁) +
            (4 / 25 : ℝ) • (z₀ - z₄)‖ ≤
          ‖(hbMultiplierEpsilon : ℝ)‖ * ‖z₀‖ +
            (‖z₀‖ + ‖z₁‖) +
              ‖(4 / 25 : ℝ)‖ * (‖z₀‖ + ‖z₄‖) := by
      calc
        ‖hbMultiplierEpsilon • z₀ + (z₀ - z₁) +
            (4 / 25 : ℝ) • (z₀ - z₄)‖ ≤
            ‖hbMultiplierEpsilon • z₀ + (z₀ - z₁)‖ +
              ‖(4 / 25 : ℝ) • (z₀ - z₄)‖ := norm_add_le _ _
        _ ≤ (‖hbMultiplierEpsilon • z₀‖ + ‖z₀ - z₁‖) +
              ‖(4 / 25 : ℝ) • (z₀ - z₄)‖ := by
          gcongr
          exact norm_add_le _ _
        _ ≤ ‖(hbMultiplierEpsilon : ℝ)‖ * ‖z₀‖ +
              (‖z₀‖ + ‖z₁‖) +
                ‖(4 / 25 : ℝ)‖ * (‖z₀‖ + ‖z₄‖) := by
          calc
            (‖hbMultiplierEpsilon • z₀‖ + ‖z₀ - z₁‖) +
                ‖(4 / 25 : ℝ) • (z₀ - z₄)‖ =
              ‖(hbMultiplierEpsilon : ℝ)‖ * ‖z₀‖ +
                ‖z₀ - z₁‖ +
              ‖(4 / 25 : ℝ)‖ * ‖z₀ - z₄‖ := by
              rw [norm_smul, norm_smul]
            _ ≤ ‖(hbMultiplierEpsilon : ℝ)‖ * ‖z₀‖ +
                (‖z₀‖ + ‖z₁‖) +
                ‖(4 / 25 : ℝ)‖ * (‖z₀‖ + ‖z₄‖) := by
              have hdiff1 := norm_sub_le z₀ z₁
              have hdiff4 := norm_sub_le z₀ z₄
              have hdiff4' := mul_le_mul_of_nonneg_left hdiff4
                (norm_nonneg (4 / 25 : ℝ))
              exact add_le_add (add_le_add (le_refl _) hdiff1) hdiff4'
    have h0 := mul_le_mul_of_nonneg_left h₀
      (norm_nonneg (hbMultiplierEpsilon : ℝ))
    have h1 : ‖z₀‖ + ‖z₁‖ ≤ B * E N + B * E N :=
      add_le_add h₀ h₁
    have h4 : ‖z₀‖ + ‖z₄‖ ≤ B * E N + B * E N :=
      add_le_add h₀ h₄
    have hterm4 := mul_le_mul_of_nonneg_left h4
      (norm_nonneg (4 / 25 : ℝ))
    have hsum :
        ‖(hbMultiplierEpsilon : ℝ)‖ * ‖z₀‖ +
            (‖z₀‖ + ‖z₁‖) +
              ‖(4 / 25 : ℝ)‖ * (‖z₀‖ + ‖z₄‖) ≤
          ‖(hbMultiplierEpsilon : ℝ)‖ * (B * E N) +
            ((B * E N) + (B * E N)) +
              ‖(4 / 25 : ℝ)‖ * ((B * E N) + (B * E N)) := by
      exact add_le_add (add_le_add h0 h1) hterm4
    calc
      _ ≤ ‖(hbMultiplierEpsilon : ℝ)‖ * (B * E N) +
            ((B * E N) + (B * E N)) +
              ‖(4 / 25 : ℝ)‖ * ((B * E N) + (B * E N)) :=
        hnorm.trans hsum
      _ = H * B * E N := by
        dsimp [H]
        ring
  have hrawL_bound (i : Fin (2 * N + 1)) (hbi : boundary i) :
      |rawL i| ≤ H * B * (E N) ^ 2 := by
    let t : ℤ := (i.val : ℤ) - (N : ℤ)
    have hp0 : ‖p t‖ ≤ E N := by
      have h := (hraw_endpoint p i hbi 0 (by omega)).trans (hpE N)
      simpa [t] using h
    have hp_prev : ‖p (t - 1)‖ ≤ E N := by
      have h := (hraw_endpoint p i hbi (-1) (by omega)).trans (hpE N)
      simpa [t, sub_eq_add_neg] using h
    have hp_four : ‖p (t + 4)‖ ≤ E N := by
      have h := (hraw_endpoint p i hbi 4 (by omega)).trans (hpE N)
      simpa [t] using h
    have hy0 : ‖y t‖ ≤ E N := by
      have h := (hraw_endpoint y i hbi 0 (by omega)).trans (hyE N)
      simpa [t] using h
    have hy_prev : ‖y (t - 1)‖ ≤ E N := by
      have h := (hraw_endpoint y i hbi (-1) (by omega)).trans (hyE N)
      simpa [t, sub_eq_add_neg] using h
    have hy_four : ‖y (t + 4)‖ ≤ E N := by
      have h := (hraw_endpoint y i hbi 4 (by omega)).trans (hyE N)
      simpa [t] using h
    have hz0 :
        ‖hbL0 q • y t - p t‖ ≤ B * E N :=
      hz_raw_bound (y t) (p t) hy0 hp0
    have hz_prev :
        ‖hbL0 q • y (t - 1) - p (t - 1)‖ ≤ B * E N :=
      hz_raw_bound (y (t - 1)) (p (t - 1)) hy_prev hp_prev
    have hz_four :
        ‖hbL0 q • y (t + 4) - p (t + 4)‖ ≤ B * E N :=
      hz_raw_bound (y (t + 4)) (p (t + 4)) hy_four hp_four
    have hm :
        ‖hbMultiplierTimeDomain
            (fun t : ℤ => hbL0 q • y t - p t) t‖ ≤
          H * B * E N := by
      simpa [hbMultiplierTimeDomain, t] using
        hmult_bound
          (hbL0 q • y t - p t)
          (hbL0 q • y (t - 1) - p (t - 1))
          (hbL0 q • y (t + 4) - p (t + 4))
          hz0 hz_prev hz_four
    have hinner :=
      abs_real_inner_le_norm (p t)
        (hbMultiplierTimeDomain
          (fun t : ℤ => hbL0 q • y t - p t) t)
    have hprod :
        ‖p t‖ *
            ‖hbMultiplierTimeDomain
              (fun t : ℤ => hbL0 q • y t - p t) t‖ ≤
          E N * (H * B * E N) := by
      exact mul_le_mul hp0 hm
        (norm_nonneg
          (hbMultiplierTimeDomain
            (fun t : ℤ => hbL0 q • y t - p t) t))
        (hE_nonneg N)
    calc
      |rawL i| =
          |inner ℝ (p t)
            (hbMultiplierTimeDomain
              (fun t : ℤ => hbL0 q • y t - p t) t)| := by
        dsimp [rawL, t]
      _ ≤ ‖p t‖ *
          ‖hbMultiplierTimeDomain
            (fun t : ℤ => hbL0 q • y t - p t) t‖ := hinner
      _ ≤ E N * (H * B * E N) := hprod
      _ = H * B * (E N) ^ 2 := by ring
  have hrawR_bound (i : Fin (2 * N + 1)) (hbi : boundary i) :
      |rawR i| ≤ hbD9Eta * (E N) ^ 2 := by
    let t : ℤ := (i.val : ℤ) - (N : ℤ)
    have hp0 : ‖p t‖ ≤ E N := by
      have h := (hraw_endpoint p i hbi 0 (by omega)).trans (hpE N)
      simpa [t] using h
    have heta : 0 ≤ hbD9Eta := by norm_num [hbD9Eta]
    have hsq : ‖p t‖ ^ 2 ≤ (E N) ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _) (hE_nonneg N)).2 hp0
    have hmul := mul_le_mul_of_nonneg_left hsq heta
    dsimp [rawR, t]
    rw [abs_of_nonpos]
    · simpa using hmul
    · simpa [neg_mul] using
        (neg_nonpos.mpr (mul_nonneg heta (sq_nonneg (‖p t‖))))
  have heta : 0 ≤ hbD9Eta := by norm_num [hbD9Eta]
  have hcycL_bound (i : Fin (2 * N + 1)) (hbi : boundary i) :
      |cycL i| ≤ A * H * B * (E N) ^ 2 := by
    have hPi : ‖P i‖ ≤ A * E N := by
      exact hPbound i
        (hnear_self i hbi)
        (hnear_prev i hbi)
        (by
          simpa using hnear_forward i hbi 1 (by omega))
    have hPprev :
        ‖P (cycleFinShift ((2 * N + 1) - 1) i)‖ ≤ A * E N := by
      refine hPbound (cycleFinShift ((2 * N + 1) - 1) i)
        (hnear_prev i hbi) ?_ (hnear_next_prev i hbi)
      rw [hprevprev_index i]
      exact hnear_prevprev i hbi
    have hPfour :
        ‖P (cycleFinShift 4 i)‖ ≤ A * E N := by
      refine hPbound (cycleFinShift 4 i) ?_ ?_ ?_
      · exact hnear_forward i hbi 4 (by omega)
      · rw [hprev_four_index i]
        exact hnear_forward i hbi 3 (by omega)
      · rw [hnext_four_index i]
        exact hnear_forward i hbi 5 (by omega)
    have hY0 : ‖Y i‖ ≤ E N :=
      hYnear i (hnear_self i hbi)
    have hYprev :
        ‖Y (cycleFinShift ((2 * N + 1) - 1) i)‖ ≤ E N :=
      hYnear (cycleFinShift ((2 * N + 1) - 1) i)
        (hnear_prev i hbi)
    have hYfour : ‖Y (cycleFinShift 4 i)‖ ≤ E N :=
      hYnear (cycleFinShift 4 i)
        (hnear_forward i hbi 4 (by omega))
    have hz0 :
        ‖hbL0 q • Y i - P i‖ ≤ B * E N :=
      hz_bound (Y i) (P i) hY0 hPi
    have hzprev :
        ‖hbL0 q • Y (cycleFinShift ((2 * N + 1) - 1) i) -
            P (cycleFinShift ((2 * N + 1) - 1) i)‖ ≤ B * E N :=
      hz_bound
        (Y (cycleFinShift ((2 * N + 1) - 1) i))
        (P (cycleFinShift ((2 * N + 1) - 1) i))
        hYprev hPprev
    have hzfour :
        ‖hbL0 q • Y (cycleFinShift 4 i) -
            P (cycleFinShift 4 i)‖ ≤ B * E N :=
      hz_bound (Y (cycleFinShift 4 i)) (P (cycleFinShift 4 i))
        hYfour hPfour
    have hm :
        ‖hbMultiplierEpsilon • (hbL0 q • Y i - P i) +
            ((hbL0 q • Y i - P i) -
              (hbL0 q • Y (cycleFinShift ((2 * N + 1) - 1) i) -
                P (cycleFinShift ((2 * N + 1) - 1) i))) +
            (4 / 25 : ℝ) •
              ((hbL0 q • Y i - P i) -
                (hbL0 q • Y (cycleFinShift 4 i) -
                  P (cycleFinShift 4 i)))‖ ≤
          H * B * E N := by
      exact hmult_bound
        (hbL0 q • Y i - P i)
        (hbL0 q • Y (cycleFinShift ((2 * N + 1) - 1) i) -
          P (cycleFinShift ((2 * N + 1) - 1) i))
        (hbL0 q • Y (cycleFinShift 4 i) - P (cycleFinShift 4 i))
        hz0 hzprev hzfour
    have hinner :=
      abs_real_inner_le_norm (P i)
        (hbMultiplierEpsilon • (hbL0 q • Y i - P i) +
          ((hbL0 q • Y i - P i) -
            (hbL0 q • Y (cycleFinShift ((2 * N + 1) - 1) i) -
              P (cycleFinShift ((2 * N + 1) - 1) i))) +
          (4 / 25 : ℝ) •
            ((hbL0 q • Y i - P i) -
              (hbL0 q • Y (cycleFinShift 4 i) -
                P (cycleFinShift 4 i))))
    have hprod :
        ‖P i‖ *
            ‖hbMultiplierEpsilon • (hbL0 q • Y i - P i) +
              ((hbL0 q • Y i - P i) -
                (hbL0 q • Y (cycleFinShift ((2 * N + 1) - 1) i) -
                  P (cycleFinShift ((2 * N + 1) - 1) i))) +
          (4 / 25 : ℝ) •
                ((hbL0 q • Y i - P i) -
                  (hbL0 q • Y (cycleFinShift 4 i) -
                    P (cycleFinShift 4 i)))‖ ≤
          A * E N * (H * B * E N) := by
      apply mul_le_mul hPi hm
      · positivity
      · exact mul_nonneg hA_nonneg (hE_nonneg N)
    calc
      |cycL i| =
          |inner ℝ (P i)
            (hbMultiplierEpsilon • (hbL0 q • Y i - P i) +
              ((hbL0 q • Y i - P i) -
                (hbL0 q • Y (cycleFinShift ((2 * N + 1) - 1) i) -
                  P (cycleFinShift ((2 * N + 1) - 1) i))) +
              (4 / 25 : ℝ) •
                ((hbL0 q • Y i - P i) -
                  (hbL0 q • Y (cycleFinShift 4 i) -
                    P (cycleFinShift 4 i))))| := by
        rfl
      _ ≤ ‖P i‖ *
          ‖hbMultiplierEpsilon • (hbL0 q • Y i - P i) +
            ((hbL0 q • Y i - P i) -
              (hbL0 q • Y (cycleFinShift ((2 * N + 1) - 1) i) -
                P (cycleFinShift ((2 * N + 1) - 1) i))) +
            (4 / 25 : ℝ) •
              ((hbL0 q • Y i - P i) -
                (hbL0 q • Y (cycleFinShift 4 i) -
                  P (cycleFinShift 4 i)))‖ := hinner
      _ ≤ A * E N * (H * B * E N) := hprod
      _ = A * H * B * (E N) ^ 2 := by ring
  have hcycR_bound (i : Fin (2 * N + 1)) (hbi : boundary i) :
      |cycR i| ≤ hbD9Eta * A ^ 2 * (E N) ^ 2 := by
    have hPi : ‖P i‖ ≤ A * E N := by
      exact hPbound i
        (hnear_self i hbi)
        (hnear_prev i hbi)
        (by
          simpa using hnear_forward i hbi 1 (by omega))
    have hAE_nonneg : 0 ≤ A * E N :=
      mul_nonneg hA_nonneg (hE_nonneg N)
    have hsq : ‖P i‖ ^ 2 ≤ (A * E N) ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _) hAE_nonneg).2 hPi
    have heta : 0 ≤ hbD9Eta := by norm_num [hbD9Eta]
    have hmul := mul_le_mul_of_nonneg_left hsq heta
    dsimp [cycR]
    rw [abs_of_nonpos]
    · calc
        -(-hbD9Eta * ‖P i‖ ^ 2) = hbD9Eta * ‖P i‖ ^ 2 := by ring
        _ ≤ hbD9Eta * (A * E N) ^ 2 := hmul
        _ = hbD9Eta * A ^ 2 * (E N) ^ 2 := by ring
    · simpa [neg_mul] using
        (neg_nonpos.mpr (mul_nonneg heta (sq_nonneg (‖P i‖))))
  let S : Finset (Fin (2 * N + 1)) :=
    Finset.univ.filter boundary
  have hScard : S.card ≤ 7 := by
    dsimp [S, boundary]
    exact hb_d9_boundary_card_le_seven N
  have hScard_real : (S.card : ℝ) ≤ 7 := by
    exact_mod_cast hScard
  have hsum_rawL :
      (∑ i ∈ S, |rawL i|) ≤
        7 * (H * B * (E N) ^ 2) := by
    have h :=
      Finset.sum_le_card_nsmul S (fun i => |rawL i|)
        (H * B * (E N) ^ 2) (by
          intro i hi
          exact hrawL_bound i (Finset.mem_filter.mp hi).2)
    have hcard :
        (S.card : ℝ) * (H * B * (E N) ^ 2) ≤
          7 * (H * B * (E N) ^ 2) := by
      exact mul_le_mul_of_nonneg_right hScard_real
        (mul_nonneg (mul_nonneg hH_nonneg hB_nonneg)
          (sq_nonneg (E N)))
    have hsum_card :
        (∑ i ∈ S, |rawL i|) ≤
          (S.card : ℝ) * (H * B * (E N) ^ 2) := by
      simpa [nsmul_eq_mul] using h
    exact hsum_card.trans hcard
  have hsum_cycL :
      (∑ i ∈ S, |cycL i|) ≤
        7 * (A * H * B * (E N) ^ 2) := by
    have h :=
      Finset.sum_le_card_nsmul S (fun i => |cycL i|)
        (A * H * B * (E N) ^ 2) (by
          intro i hi
          exact hcycL_bound i (Finset.mem_filter.mp hi).2)
    have hcard :
        (S.card : ℝ) * (A * H * B * (E N) ^ 2) ≤
          7 * (A * H * B * (E N) ^ 2) := by
      exact mul_le_mul_of_nonneg_right hScard_real
        (mul_nonneg (mul_nonneg (mul_nonneg hA_nonneg hH_nonneg)
          hB_nonneg) (sq_nonneg (E N)))
    have hsum_card :
        (∑ i ∈ S, |cycL i|) ≤
          (S.card : ℝ) * (A * H * B * (E N) ^ 2) := by
      simpa [nsmul_eq_mul] using h
    exact hsum_card.trans hcard
  have hsum_cycR :
      (∑ i ∈ S, |cycR i|) ≤
        7 * (hbD9Eta * A ^ 2 * (E N) ^ 2) := by
    have h :=
      Finset.sum_le_card_nsmul S (fun i => |cycR i|)
        (hbD9Eta * A ^ 2 * (E N) ^ 2) (by
          intro i hi
          exact hcycR_bound i (Finset.mem_filter.mp hi).2)
    have hcard :
        (S.card : ℝ) * (hbD9Eta * A ^ 2 * (E N) ^ 2) ≤
          7 * (hbD9Eta * A ^ 2 * (E N) ^ 2) := by
      exact mul_le_mul_of_nonneg_right hScard_real
        (mul_nonneg (mul_nonneg heta (sq_nonneg A))
          (sq_nonneg (E N)))
    have hsum_card :
        (∑ i ∈ S, |cycR i|) ≤
          (S.card : ℝ) * (hbD9Eta * A ^ 2 * (E N) ^ 2) := by
      simpa [nsmul_eq_mul] using h
    exact hsum_card.trans hcard
  have hsum_rawR :
      (∑ i ∈ S, |rawR i|) ≤
        7 * (hbD9Eta * (E N) ^ 2) := by
    have h :=
      Finset.sum_le_card_nsmul S (fun i => |rawR i|)
        (hbD9Eta * (E N) ^ 2) (by
          intro i hi
          exact hrawR_bound i (Finset.mem_filter.mp hi).2)
    have hcard :
        (S.card : ℝ) * (hbD9Eta * (E N) ^ 2) ≤
          7 * (hbD9Eta * (E N) ^ 2) := by
      exact mul_le_mul_of_nonneg_right hScard_real
        (mul_nonneg heta (sq_nonneg (E N)))
    have hsum_card :
        (∑ i ∈ S, |rawR i|) ≤
          (S.card : ℝ) * (hbD9Eta * (E N) ^ 2) := by
      simpa [nsmul_eq_mul] using h
    exact hsum_card.trans hcard
  have herr_bound :
      errL + errR ≤
        7 * (H * B + A * H * B + hbD9Eta * A ^ 2 + hbD9Eta) *
          (E N) ^ 2 := by
    have hL := add_le_add hsum_rawL hsum_cycL
    have hR := add_le_add hsum_cycR hsum_rawR
    dsimp [errL, errR, S] at hL hR ⊢
    nlinarith
  refine ⟨errL + errR, ?_, ?_⟩
  · dsimp [errL, errR]
    positivity
  · have hEqL :
        ∀ i ∈ (Finset.univ : Finset (Fin (2 * N + 1))),
          ¬ boundary i → rawL i = cycL i := by
      intro i hi hnot
      have hinterior : 2 ≤ i.val ∧ i.val + 5 < 2 * N + 1 := by
        by_contra hbad
        exact hnot hbad
      rcases hb_d9_cyclic_window_interior_agreement p y P Y hY hP i
          hinterior.1 hinterior.2 with
        ⟨hPi, hYprev, hPprev, hYfour, hPfour⟩
      have hYprev' :
          Y (cycleFinShift (2 * N) i) =
            y ((i.val : ℤ) - (N : ℤ) - 1) := by
        simpa using hYprev
      have hPprev' :
          P (cycleFinShift (2 * N) i) =
            p ((i.val : ℤ) - (N : ℤ) - 1) := by
        simpa using hPprev
      dsimp [rawL, cycL, hbMultiplierTimeDomain]
      rw [hPi, hY i, hYprev', hPprev', hYfour, hPfour]
    have hEqR :
        ∀ i ∈ (Finset.univ : Finset (Fin (2 * N + 1))),
          ¬ boundary i → cycR i = rawR i := by
      intro i hi hnot
      have hinterior : 2 ≤ i.val ∧ i.val + 5 < 2 * N + 1 := by
        by_contra hbad
        exact hnot hbad
      have hPi :=
        (hb_d9_cyclic_window_interior_agreement p y P Y hY hP i
          hinterior.1 hinterior.2).1
      dsimp [cycR, rawR]
      rw [hPi]
    have hdiffL :=
      hb_d9_sum_difference_on_filter
        (s := (Finset.univ : Finset (Fin (2 * N + 1))))
        (keep := boundary) rawL cycL hEqL
    have hdiffR :=
      hb_d9_sum_difference_on_filter
        (s := (Finset.univ : Finset (Fin (2 * N + 1))))
        (keep := boundary) cycR rawR hEqR
    have hraw_le_cyc :
        (∑ i : Fin (2 * N + 1), rawL i) ≤
          (∑ i : Fin (2 * N + 1), cycL i) + errL := by
      have h := (abs_le.mp hdiffL).2
      dsimp [errL] at h ⊢
      linarith
    have hcyc_le_raw :
        (∑ i : Fin (2 * N + 1), cycR i) ≤
          (∑ i : Fin (2 * N + 1), rawR i) + errR := by
      have h := (abs_le.mp hdiffR).2
      dsimp [errR] at h ⊢
      linarith
    have hcyc :
        (∑ i : Fin (2 * N + 1), cycL i) ≤
          ∑ i : Fin (2 * N + 1), cycR i := by
      have h := hb_d9_finite_cyclic_coercivity hbox P Y hcycle
      rw [Finset.mul_sum] at h
      simpa [cycL, cycR] using h
    constructor
    · calc
        (∑ i : Fin (2 * N + 1), rawL i) ≤
            (∑ i : Fin (2 * N + 1), cycL i) + errL := hraw_le_cyc
        _ ≤ (∑ i : Fin (2 * N + 1), cycR i) + errL :=
          add_le_add_left hcyc errL
        _ ≤ ((∑ i : Fin (2 * N + 1), rawR i) + errR) + errL :=
          add_le_add_left hcyc_le_raw errL
        _ = (∑ i : Fin (2 * N + 1), rawR i) + (errL + errR) := by ring
    · exact herr_bound

private theorem hb_d9_coercivity_limit_of_vanishing_window_error
    {q : ℝ} {d : ℕ} (p y : ℤ → Vec d)
    (hp : Summable (fun t : ℤ => ‖p t‖ ^ 2))
    (hy : Summable (fun t : ℤ => ‖y t‖ ^ 2))
    (err : ℕ → ℝ)
    (hwindow : ∀ N : ℕ,
      (∑ k ∈ Finset.range (2 * N + 1),
        inner ℝ (p (Equiv.intEquivNat.symm k))
          (hbMultiplierTimeDomain
            (fun t : ℤ => hbL0 q • y t - p t)
            (Equiv.intEquivNat.symm k))) ≤
      (∑ k ∈ Finset.range (2 * N + 1),
        -hbD9Eta * ‖p (Equiv.intEquivNat.symm k)‖ ^ 2) +
        err N)
    (herr : Tendsto err atTop (nhds 0)) :
    (∑' t : ℤ,
      inner ℝ (p t)
        (hbMultiplierTimeDomain
          (fun t : ℤ => hbL0 q • y t - p t) t)) ≤
      -hbD9Eta * hbBilateralSequenceL2Norm p ^ 2 := by
  have hinner :=
    hbD9_multiplier_inner_summable_of_l2 (q := q) p y hp hy
  have hneg :
      Summable (fun t : ℤ => -hbD9Eta * ‖p t‖ ^ 2) := by
    simpa using hp.mul_left (-hbD9Eta)
  have hleft_lim :=
    hb_tsum_int_odd_enum_real
      (fun t : ℤ =>
        inner ℝ (p t)
          (hbMultiplierTimeDomain
            (fun u : ℤ => hbL0 q • y u - p u) t))
      hinner
  have hright_lim :=
    (hb_tsum_int_odd_enum_real
      (fun t : ℤ => -hbD9Eta * ‖p t‖ ^ 2) hneg).add herr
  have hright_lim' :
      Tendsto
        (fun N : ℕ =>
          (∑ k ∈ Finset.range (2 * N + 1),
            -hbD9Eta * ‖p (Equiv.intEquivNat.symm k)‖ ^ 2) +
            err N)
        atTop (nhds (∑' t : ℤ, -hbD9Eta * ‖p t‖ ^ 2)) := by
    simpa using hright_lim
  have hlim :
      (∑' t : ℤ,
        inner ℝ (p t)
          (hbMultiplierTimeDomain
            (fun t : ℤ => hbL0 q • y t - p t) t)) ≤
        (∑' t : ℤ, -hbD9Eta * ‖p t‖ ^ 2) := by
    exact le_of_tendsto_of_tendsto hleft_lim hright_lim'
      (Eventually.of_forall hwindow)
  rw [tsum_mul_left] at hlim
  have henergy_nonneg :
      0 ≤ ∑' t : ℤ, ‖p t‖ ^ 2 :=
    tsum_nonneg (fun t => sq_nonneg _)
  have hnorm_sq :
      hbBilateralSequenceL2Norm p ^ 2 =
        ∑' t : ℤ, ‖p t‖ ^ 2 := by
    unfold hbBilateralSequenceL2Norm hbBilateralSequenceEnergy
    exact Real.sq_sqrt henergy_nonneg
  rw [hnorm_sq]
  exact hlim

private theorem hb_d9_coercivity_of_zero_extended_recurrence
    {q a b : ℝ} {d : ℕ} (p y : ℤ → Vec d)
    (hp : Summable (fun t : ℤ => ‖p t‖ ^ 2))
    (hy : Summable (fun t : ℤ => ‖y t‖ ^ 2))
    (hwindow : ∃ err : ℕ → ℝ,
      (∀ N : ℕ, 0 ≤ err N ∧
        (∑ i : Fin (2 * N + 1),
          inner ℝ (p ((i.val : ℤ) - (N : ℤ)))
            (hbMultiplierTimeDomain
              (fun t : ℤ => hbL0 q • y t - p t)
              ((i.val : ℤ) - (N : ℤ)))) ≤
        (∑ i : Fin (2 * N + 1),
          -hbD9Eta * ‖p ((i.val : ℤ) - (N : ℤ))‖ ^ 2) + err N) ∧
      Tendsto err atTop (nhds 0)) :
    (∑' t : ℤ,
      inner ℝ (p t)
        (hbMultiplierTimeDomain
          (fun t : ℤ => hbL0 q • y t - p t) t)) ≤
      -hbD9Eta * hbBilateralSequenceL2Norm p ^ 2 := by
  rcases hwindow with ⟨err, herr, herr_lim⟩
  let fl : ℤ → ℝ :=
    fun t =>
      inner ℝ (p t)
        (hbMultiplierTimeDomain
          (fun u : ℤ => hbL0 q • y u - p u) t)
  let fr : ℤ → ℝ := fun t => -hbD9Eta * ‖p t‖ ^ 2
  have hwindow' : ∀ N : ℕ,
      (∑ k ∈ Finset.range (2 * N + 1),
        fl (Equiv.intEquivNat.symm k)) ≤
      (∑ k ∈ Finset.range (2 * N + 1),
        fr (Equiv.intEquivNat.symm k)) + err N := by
    intro N
    have hl := hb_d9_odd_window_reindex fl N
    have hr := hb_d9_odd_window_reindex fr N
    calc
      (∑ k ∈ Finset.range (2 * N + 1),
          fl (Equiv.intEquivNat.symm k)) =
          ∑ i : Fin (2 * N + 1),
            fl ((i.val : ℤ) - (N : ℤ)) := hl
      _ ≤ (∑ i : Fin (2 * N + 1),
            fr ((i.val : ℤ) - (N : ℤ))) + err N := by
        simpa [fl, fr] using (herr N).2
      _ = (∑ k ∈ Finset.range (2 * N + 1),
            fr (Equiv.intEquivNat.symm k)) + err N := by
        rw [← hr]
  exact hb_d9_coercivity_limit_of_vanishing_window_error
    p y hp hy err hwindow' herr_lim

/-- D9 conditional estimates, before continuation has proved that the new
trajectory is square-summable. The surface keeps the source quadratic estimate
and the norm estimates separate so later proofs cannot silently skip the D9
well-definedness boundary. -/
def hbD9ConditionalEstimate (q a b : ℝ)
    (hD : ParameterDomain q a b) : Prop :=
  hbD9ConditionalQuadraticEstimate q a b hD ∧
    hbD9ConditionalGainEstimate q a b hD

/-- The D9 admissibility condition for one homotopy continuation step. -/
def hbD9ContinuationStepAdmissible (q a b δ : ℝ) : Prop :=
  0 < δ ∧ hbD9C0 q a b * δ * hbPlantL2Gain q a b * hbL0 q ≤ 1 / 2

/-- D9 finite-prefix continuation: strict causality gives finite prefixes,
prefix bounds are established first, and only then square-summability follows. -/
def hbD9FinitePrefixContinuation (q a b : ℝ)
    (hD : ParameterDomain q a b) : Prop :=
  ∀ {d : ℕ}, 1 ≤ d → ∀ (hf : AdmissibleObjective q d) (τ δ : ℝ),
    0 ≤ τ → τ ≤ 1 → τ + δ ≤ 1 →
      hbD9ContinuationStepAdmissible q a b δ →
        ∀ e x : ℕ → Vec d,
          hbSequenceInL2 e →
            hbHomotopyLoopEquation (parameterDomain_q_pos hD) a b hf (τ + δ) e x →
              (∀ n : ℕ,
                hbSequenceInL2 (hbFinitePrefix n x) ∧
                  hbSequenceL2Norm (hbFinitePrefix n x) ≤
                    2 * hbD9C0 q a b * hbSequenceL2Norm e) ∧
                hbSequenceInL2 x

/-- The fixed finite homotopy schedule described after the D9 prefix argument. -/
def hbD9GlobalContinuationSchedule (q a b : ℝ) : Prop :=
  hbPlantL2Gain q a b = 0 ∨
    ∃ J : ℕ, 1 ≤ J ∧
      hbD9ContinuationStepAdmissible q a b ((J : ℝ)⁻¹)

/-- The post-continuation D9 conclusion: every homotopy-loop solution with
square-summable external input is itself in `ell_2` and satisfies the sharp
`C_0` gain. -/
def hbD9LoopConclusion (q a b : ℝ)
    (hD : ParameterDomain q a b) : Prop :=
  ∀ {d : ℕ}, 1 ≤ d → ∀ (hf : AdmissibleObjective q d) (τ : ℝ),
    0 ≤ τ → τ ≤ 1 →
      ∀ e x : ℕ → Vec d,
        hbSequenceInL2 e →
          hbHomotopyLoopEquation (parameterDomain_q_pos hD) a b hf τ e x →
            hbSequenceInL2 x ∧
              hbSequenceL2Norm x ≤ hbD9C0 q a b * hbSequenceL2Norm e

/-- The explicit numerical D9 consequence used by the later total-energy
estimate: after continuation has established `x ∈ ell_2`, `g<101` and `m<3`
give the displayed `610000` gain. -/
def hbD9ExplicitConstantConclusion (q a b : ℝ)
    (hD : ParameterDomain q a b) : Prop :=
  hbPlantL2Gain q a b < 101 ∧
    hbMultiplierL2Gain < 3 ∧
      ∀ {d : ℕ}, 1 ≤ d → ∀ (hf : AdmissibleObjective q d) (τ : ℝ),
        0 ≤ τ → τ ≤ 1 →
          ∀ e x : ℕ → Vec d,
            hbSequenceInL2 e →
              hbHomotopyLoopEquation (parameterDomain_q_pos hD) a b hf τ e x →
                hbSequenceInL2 x ∧
                  hbSequenceL2Norm x ≤ 610000 * hbSequenceL2Norm e

/-- D9 causal-continuation conclusion: every finite homotopy loop solution has
the source square-summability/gain conclusion. -/
def hbCausalContinuationConclusion (q a b : ℝ)
    (hD : ParameterDomain q a b) : Prop :=
  hbPlantL2GainBound q a b (hbPlantL2Gain q a b) ∧
    hbMultiplierL2GainBound hbMultiplierL2Gain ∧
      hbD9ConditionalEstimate q a b hD ∧
        hbD9FinitePrefixContinuation q a b hD ∧
          hbD9GlobalContinuationSchedule q a b ∧
            hbD9LoopConclusion q a b hD ∧
              hbD9ExplicitConstantConclusion q a b hD

private theorem hb_d9_conditional_quadratic_estimate_of_l2_loop
    {q a b : ℝ} (hbox : HB_Box q a b) :
    hbD9ConditionalQuadraticEstimate q a b
      (HB_box_subset_domain hbox) := by
  let hD := HB_box_subset_domain hbox
  have hplant :
      hbPlantL2GainBound q a b (hbPlantL2Gain q a b) :=
    hbPlantL2Gain_is_bound_on_box hbox
  unfold hbD9ConditionalQuadraticEstimate
  intro d hd hf τ hτ0 hτ1 e x he hx hloop
  let p₀ : ℕ → Vec d :=
    hbHomotopyInput (parameterDomain_q_pos hD) hf τ x
  let p : ℤ → Vec d := Function.extend Int.ofNat p₀ 0
  let e' : ℤ → Vec d := Function.extend Int.ofNat e 0
  let x' : ℤ → Vec d := Function.extend Int.ofNat x 0
  let y₀ : ℕ → Vec d := hbPlantResponse q a b p₀
  let y : ℤ → Vec d := Function.extend Int.ofNat y₀ 0
  have hp₀ : hbSequenceInL2 p₀ := by
    exact hbHomotopyInput_l2_of_l2 hD hf τ hτ0 x hx
  have he' : Summable (fun t : ℤ => ‖e' t‖ ^ 2) := by
    have h := (hbD9_zeroExtension_oneSided_to_bilateral e he).1
    simpa [e', hbBilateralSequenceInL2] using h
  have hp : Summable (fun t : ℤ => ‖p t‖ ^ 2) := by
    have h := (hbD9_zeroExtension_oneSided_to_bilateral p₀ hp₀).1
    simpa [p, hbBilateralSequenceInL2] using h
  have hy₀ : hbSequenceInL2 y₀ :=
    (hplant.2 p₀ hp₀).1
  have hy : Summable (fun t : ℤ => ‖y t‖ ^ 2) := by
    have h := (hbD9_zeroExtension_oneSided_to_bilateral y₀ hy₀).1
    simpa [y, hbBilateralSequenceInL2] using h
  have hrec :
      ∀ t : ℤ,
        y (t + 2) =
          (1 + b - a * q) • y (t + 1) -
            b • y t - a • p (t + 1) := by
    intro t
    simpa [y, p] using hbD9_zero_extension_plant_recurrence p₀ t
  let data : ∀ N : ℕ, ∃ errN : ℝ, 0 ≤ errN ∧
      (∑ i : Fin (2 * N + 1),
        inner ℝ (p ((i.val : ℤ) - (N : ℤ)))
          (hbMultiplierTimeDomain
            (fun t : ℤ => hbL0 q • y t - p t)
            ((i.val : ℤ) - (N : ℤ)))) ≤
      (∑ i : Fin (2 * N + 1),
        -hbD9Eta * ‖p ((i.val : ℤ) - (N : ℤ))‖ ^ 2) + errN ∧
      errN ≤ hb_d9_boundary_error_constant q a b *
        (hb_d9_endpoint_envelope p N + hb_d9_endpoint_envelope y N) ^ 2 :=
    fun N => hb_d9_cyclic_window_boundary_error_ordered
      hbox p y hp hy N hrec
  let err : ℕ → ℝ := fun N => Classical.choose (data N)
  have herr (N : ℕ) := Classical.choose_spec (data N)
  have hwindow : ∃ err : ℕ → ℝ,
      (∀ N : ℕ, 0 ≤ err N ∧
        (∑ i : Fin (2 * N + 1),
          inner ℝ (p ((i.val : ℤ) - (N : ℤ)))
            (hbMultiplierTimeDomain
              (fun t : ℤ => hbL0 q • y t - p t)
              ((i.val : ℤ) - (N : ℤ)))) ≤
        (∑ i : Fin (2 * N + 1),
          -hbD9Eta * ‖p ((i.val : ℤ) - (N : ℤ))‖ ^ 2) + err N) ∧
      Tendsto err atTop (nhds 0) := by
    refine ⟨err, ?_, ?_⟩
    · intro N
      exact ⟨(herr N).1, (herr N).2.1⟩
    · have hE :
          Tendsto
            (fun N : ℕ =>
              hb_d9_endpoint_envelope p N +
                hb_d9_endpoint_envelope y N)
            atTop (nhds 0) := by
        simpa using
          (hb_d9_endpoint_envelope_tendsto_zero p hp).add
            (hb_d9_endpoint_envelope_tendsto_zero y hy)
      have hE2 :
          Tendsto
            (fun N : ℕ =>
              (hb_d9_endpoint_envelope p N +
                hb_d9_endpoint_envelope y N) ^ 2)
            atTop (nhds 0) :=
        by
          convert hE.pow 2 using 1 <;> norm_num
      have hupper :
          Tendsto
            (fun N : ℕ =>
              hb_d9_boundary_error_constant q a b *
                (hb_d9_endpoint_envelope p N +
                  hb_d9_endpoint_envelope y N) ^ 2)
            atTop (nhds 0) := by
        have hconst :
            Tendsto
              (fun _ : ℕ => hb_d9_boundary_error_constant q a b)
              atTop (nhds (hb_d9_boundary_error_constant q a b)) :=
          tendsto_const_nhds
        convert hconst.mul hE2 using 1 <;> norm_num
      apply
        tendsto_of_tendsto_of_tendsto_of_le_of_le
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ))
            atTop (nhds 0))
          hupper
      · intro N
        exact (herr N).1
      · intro N
        exact (herr N).2.2
  let r : ℤ → Vec d := fun t => hbL0 q • y t - p t
  let s : ℤ → Vec d := fun t => hbL0 q • x' t - p t
  have hr : Summable (fun t : ℤ => ‖r t‖ ^ 2) := by
    have hscaled :=
      hb_bilateral_l2_smul_summable_and_norm_eq hy (hbL0 q)
    have hneg :=
      hb_bilateral_l2_smul_summable_and_norm_eq hp (-1 : ℝ)
    have hsum := hb_bilateral_l2_norm_add_le hscaled.1 hneg.1
    simpa [r, sub_eq_add_neg] using hsum.1
  have hme :
      Summable
        (fun t : ℤ => ‖hbMultiplierTimeDomain
          (fun t : ℤ => hbL0 q • e' t) t‖ ^ 2) := by
    have hscaled :=
      hb_bilateral_l2_smul_summable_and_norm_eq he' (hbL0 q)
    exact (hbMultiplierL2Gain_is_bound).2
      (fun t : ℤ => hbL0 q • e' t) hscaled.1 |>.1
  have hmr :
      Summable
        (fun t : ℤ => ‖hbMultiplierTimeDomain r t‖ ^ 2) :=
    (hb_multiplier_finite_lag_l2_bound hr).1
  have hx_split : ∀ t : ℤ, x' t = e' t + y t := by
    intro t
    cases t with
    | ofNat n =>
        dsimp [x', e', y]
        have hx0 :
            Function.extend Int.ofNat x 0 (n : ℤ) = x n :=
          Int.ofNat_injective.extend_apply x 0 n
        have he0 :
            Function.extend Int.ofNat e 0 (n : ℤ) = e n :=
          Int.ofNat_injective.extend_apply e 0 n
        have hy0 :
            Function.extend Int.ofNat y₀ 0 (n : ℤ) = y₀ n :=
          Int.ofNat_injective.extend_apply y₀ 0 n
        rw [hx0, he0, hy0]
        simpa [hbHomotopyLoopEquation, p₀, y₀] using hloop n
    | negSucc n =>
        have hx0 :
            Function.extend Int.ofNat x 0 (Int.negSucc n) = 0 := by
          apply Function.extend_apply'
          simp
        have he0 :
            Function.extend Int.ofNat e 0 (Int.negSucc n) = 0 := by
          apply Function.extend_apply'
          simp
        have hy0 :
            Function.extend Int.ofNat y₀ 0 (Int.negSucc n) = 0 := by
          apply Function.extend_apply'
          simp
        simpa [x', e', y, hx0, he0, hy0]
  have hsplit : ∀ t : ℤ,
      hbMultiplierTimeDomain s t =
        hbMultiplierTimeDomain r t +
          hbMultiplierTimeDomain
            (fun t : ℤ => hbL0 q • e' t) t := by
    intro t
    have hs :
        s t = r t + hbL0 q • e' t := by
      dsimp [s, r]
      rw [hx_split t, smul_add]
      abel
    have hs_all : ∀ u : ℤ, s u = r u + hbL0 q • e' u := by
      intro u
      dsimp [s, r]
      rw [hx_split u, smul_add]
      abel
    dsimp [hbMultiplierTimeDomain]
    rw [hs_all t, hs_all (t - 1), hs_all (t + 4)]
    simp only [smul_add, smul_sub, smul_neg, neg_smul]
    abel
  have hp_form :
      p = fun t : ℤ =>
        τ • hbCenteredNonlinearity (parameterDomain_q_pos hD) hf (x' t) := by
    funext t
    cases t with
    | ofNat n =>
        change Function.extend Int.ofNat p₀ 0 (n : ℤ) =
          τ • hbCenteredNonlinearity (parameterDomain_q_pos hD) hf
            (Function.extend Int.ofNat x 0 (n : ℤ))
        have hp0 :
            Function.extend Int.ofNat p₀ 0 (n : ℤ) = p₀ n :=
          Int.ofNat_injective.extend_apply p₀ 0 n
        have hx0 :
            Function.extend Int.ofNat x 0 (n : ℤ) = x n :=
          Int.ofNat_injective.extend_apply x 0 n
        rw [hp0, hx0]
        rfl
    | negSucc n =>
        change Function.extend Int.ofNat p₀ 0 (Int.negSucc n) =
          τ • hbCenteredNonlinearity (parameterDomain_q_pos hD) hf
            (Function.extend Int.ofNat x 0 (Int.negSucc n))
        have hp0 :
            Function.extend Int.ofNat p₀ 0 (Int.negSucc n) = 0 := by
          apply Function.extend_apply'
          simp
        have hx0 :
            Function.extend Int.ofNat x 0 (Int.negSucc n) = 0 := by
          apply Function.extend_apply'
          simp
        rw [hp0, hx0]
        simp [hbCenteredNonlinearity_zero (parameterDomain_q_pos hD) hf]
  have hsupply :
      0 ≤ ∑' t : ℤ, inner ℝ (p t)
        (hbMultiplierTimeDomain s t) := by
    have h :=
      hbD9_zero_extended_supply_of_l2 hbox hf τ hτ0 hτ1 x hx
    dsimp [s]
    rw [hp_form]
    simpa [x', hbHomotopyLoopEquation] using h
  have hcoercive :
      (∑' t : ℤ, inner ℝ (p t)
        (hbMultiplierTimeDomain r t)) ≤
        -hbD9Eta * hbBilateralSequenceL2Norm p ^ 2 :=
    hb_d9_coercivity_of_zero_extended_recurrence
      (q := q) (a := a) (b := b) p y hp hy hwindow
  have hquad :=
    hbD9_quadratic_from_time_domain_coercivity
      hD p e' s r hp he' hr hmr hme hsupply hsplit hcoercive
  have he_norm :
      hbBilateralSequenceL2Norm e' = hbSequenceL2Norm e := by
    simpa [e'] using
      (hbD9_zeroExtension_oneSided_to_bilateral e he).2
  have hp_norm :
      hbBilateralSequenceL2Norm p = hbSequenceL2Norm p₀ := by
    simpa [p] using
      (hbD9_zeroExtension_oneSided_to_bilateral p₀ hp₀).2
  refine ⟨hp₀, ?_⟩
  rw [hp_norm, he_norm] at hquad
  simpa [p₀] using hquad

private theorem hb_d9_l2_of_uniform_finite_prefix_bound
    {d : ℕ} (x : ℕ → Vec d) (K : ℝ)
    (hbound : ∀ n : ℕ,
      hbSequenceL2Norm (hbFinitePrefix n x) ≤ K) :
    hbSequenceInL2 x := by
  have hK : 0 ≤ K := by
    exact le_trans (Real.sqrt_nonneg _) (hbound 0)
  have hprefix_energy :
      ∀ n : ℕ,
        hbSequenceEnergy (hbFinitePrefix n x) =
          ∑ i ∈ Finset.range (n + 1), ‖x i‖ ^ 2 := by
    intro n
    unfold hbSequenceEnergy
    rw [tsum_eq_sum (s := Finset.range (n + 1))
      (fun i hi => by
        have hni : n < i := by
          simpa [Finset.mem_range] using hi
        simp [hbFinitePrefix, not_le.mpr hni])]
    apply Finset.sum_congr rfl
    intro i hi
    have hin : i ≤ n := by
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    simp [hbFinitePrefix, hin]
  have hprefix_bound :
      ∀ n : ℕ, (∑ i ∈ Finset.range n, ‖x i‖ ^ 2) ≤ K ^ 2 := by
    intro n
    have hsq :
        hbSequenceL2Norm (hbFinitePrefix n x) ^ 2 ≤ K ^ 2 :=
      (sq_le_sq₀ (Real.sqrt_nonneg _) hK).2 (hbound n)
    have henergy_nonneg :
        0 ≤ hbSequenceEnergy (hbFinitePrefix n x) := by
      unfold hbSequenceEnergy
      exact tsum_nonneg (fun i => sq_nonneg (‖hbFinitePrefix n x i‖))
    have hfull :
        (∑ i ∈ Finset.range (n + 1), ‖x i‖ ^ 2) ≤ K ^ 2 := by
      rw [← hprefix_energy n]
      calc
        hbSequenceEnergy (hbFinitePrefix n x) =
            hbSequenceL2Norm (hbFinitePrefix n x) ^ 2 := by
          unfold hbSequenceL2Norm
          rw [Real.sq_sqrt henergy_nonneg]
        _ ≤ K ^ 2 := hsq
    exact
      (Finset.sum_le_sum_of_subset_of_nonneg
        ((Finset.range_subset_range).2 (Nat.le_succ n))
        (fun i _ _ => sq_nonneg (‖x i‖))).trans hfull
  exact summable_of_sum_range_le
    (fun i => sq_nonneg (‖x i‖)) hprefix_bound

private theorem hbPlantResponse_zero_input
    {d : ℕ} (q a b : ℝ) :
    ∀ t : ℕ, hbPlantResponse q a b (fun _ : ℕ => (0 : Vec d)) t = 0 := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      cases t with
      | zero =>
          simp [hbPlantResponse]
      | succ t =>
          cases t with
          | zero =>
              simp [hbPlantResponse]
          | succ t =>
              have hprev1 :
                  hbPlantResponse q a b (fun _ : ℕ => (0 : Vec d)) (t + 1) = 0 :=
                ih (t + 1) (by omega)
              have hprev0 :
                  hbPlantResponse q a b (fun _ : ℕ => (0 : Vec d)) t = 0 :=
                ih t (by omega)
              simp [hbPlantResponse, hprev1, hprev0]

private theorem hbD9C0_ge_one_of_gain_bounds
    {q a b : ℝ} (hD : ParameterDomain q a b)
    (hplant : hbPlantL2GainBound q a b (hbPlantL2Gain q a b))
    (hmult : hbMultiplierL2GainBound hbMultiplierL2Gain) :
    1 ≤ hbD9C0 q a b := by
  have hL : 0 ≤ hbL0 q := by
    dsimp [hbL0]
    linarith [parameterDomain_q_lt_one hD]
  have hEta : 0 < hbD9Eta := by
    norm_num [hbD9Eta]
  have hg : 0 ≤ hbPlantL2Gain q a b := hplant.1
  have hm : 0 ≤ hbMultiplierL2Gain := hmult.1
  have hprod :
      0 ≤ hbPlantL2Gain q a b * hbL0 q * hbMultiplierL2Gain :=
    mul_nonneg (mul_nonneg hg hL) hm
  have hterm :
      0 ≤ hbPlantL2Gain q a b * hbL0 q * hbMultiplierL2Gain / hbD9Eta := by
    exact div_nonneg hprod hEta.le
  dsimp [hbD9C0]
  linarith

private theorem hb_d9_loop_conclusion_tau_zero
    {q a b : ℝ} (hD : ParameterDomain q a b)
    (hplant : hbPlantL2GainBound q a b (hbPlantL2Gain q a b))
    (hmult : hbMultiplierL2GainBound hbMultiplierL2Gain)
    {d : ℕ} (hf : AdmissibleObjective q d) :
    ∀ e x : ℕ → Vec d,
      hbSequenceInL2 e →
        hbHomotopyLoopEquation (parameterDomain_q_pos hD) a b hf 0 e x →
          hbSequenceInL2 x ∧
            hbSequenceL2Norm x ≤ hbD9C0 q a b * hbSequenceL2Norm e := by
  intro e x he hloop
  have hx_eq : x = e := by
    funext t
    have hp_zero :
        hbHomotopyInput (parameterDomain_q_pos hD) hf 0 x =
          (fun _ : ℕ => (0 : Vec d)) := by
      funext s
      simp [hbHomotopyInput]
    have hzero :
        hbPlantResponse q a b
            (hbHomotopyInput (parameterDomain_q_pos hD) hf 0 x) t = 0 := by
      rw [hp_zero]
      exact hbPlantResponse_zero_input (d := d) q a b t
    have ht := hloop t
    simpa [hbHomotopyLoopEquation, hzero] using ht
  subst x
  constructor
  · exact he
  · have hC := hbD9C0_ge_one_of_gain_bounds hD hplant hmult
    have he_nonneg : 0 ≤ hbSequenceL2Norm e := Real.sqrt_nonneg _
    calc
      hbSequenceL2Norm e = 1 * hbSequenceL2Norm e := by ring
      _ ≤ hbD9C0 q a b * hbSequenceL2Norm e :=
        mul_le_mul_of_nonneg_right hC he_nonneg

private def hbCausalLoopState {q : ℝ} {d : ℕ} (hq : 0 < q)
    (a b : ℝ) (hf : AdmissibleObjective q d) (τ : ℝ)
    (r : ℕ → Vec d) : ℕ → Vec d × Vec d × Vec d
  | 0 => (r 0, 0, 0)
  | n + 1 =>
      let s := hbCausalLoopState hq a b hf τ r n
      let pnext :=
        (1 + b - a * q) • s.2.1 - b • s.2.2 -
          a • (τ • hbCenteredNonlinearity hq hf s.1)
      (r (n + 1) + pnext, pnext, s.2.1)

private def hbCausalLoopSolution {q : ℝ} {d : ℕ} (hq : 0 < q)
    (a b : ℝ) (hf : AdmissibleObjective q d) (τ : ℝ)
    (r : ℕ → Vec d) : ℕ → Vec d :=
  fun n => (hbCausalLoopState hq a b hf τ r n).1

private theorem hbCausalLoopState_plant_response
    {q a b : ℝ} {d : ℕ} (hq : 0 < q)
    (hf : AdmissibleObjective q d) (τ : ℝ) (r : ℕ → Vec d) :
    ∀ n : ℕ,
      (hbCausalLoopState hq a b hf τ r n).2.1 =
        hbPlantResponse q a b
          (hbHomotopyInput hq hf τ (hbCausalLoopSolution hq a b hf τ r)) n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simp [hbCausalLoopState, hbCausalLoopSolution, hbPlantResponse]
      | succ n =>
          cases n with
          | zero =>
              simp [hbCausalLoopState, hbCausalLoopSolution, hbPlantResponse,
                hbHomotopyInput]
          | succ n =>
              have hp1 := ih (n + 1) (by omega)
              have hp0 := ih n (by omega)
              change
                (1 + b - a * q) •
                      (hbCausalLoopState hq a b hf τ r (n + 1)).2.1 -
                    b • (hbCausalLoopState hq a b hf τ r n).2.1 -
                    a • (τ • hbCenteredNonlinearity hq hf
                      (hbCausalLoopSolution hq a b hf τ r (n + 1))) =
                  hbPlantResponse q a b
                    (hbHomotopyInput hq hf τ
                      (hbCausalLoopSolution hq a b hf τ r)) (n + 2)
              rw [hbPlantResponse, hp1, hp0]
              rfl

private theorem hbCausalLoopSolution_loop_equation
    {q a b : ℝ} {d : ℕ} (hq : 0 < q)
    (hf : AdmissibleObjective q d) (τ : ℝ) (r : ℕ → Vec d) :
    hbHomotopyLoopEquation hq a b hf τ r
      (hbCausalLoopSolution hq a b hf τ r) := by
  intro n
  have hp :=
    hbCausalLoopState_plant_response (q := q) (a := a) (b := b)
      hq hf τ r n
  have hy :
      hbCausalLoopSolution hq a b hf τ r n =
        r n + (hbCausalLoopState hq a b hf τ r n).2.1 := by
    cases n with
    | zero =>
        simp [hbCausalLoopSolution, hbCausalLoopState]
    | succ n =>
        simp [hbCausalLoopSolution, hbCausalLoopState]
  rw [hy, hp]

private theorem hbFinitePrefix_in_l2
    {d : ℕ} (n : ℕ) (x : ℕ → Vec d) :
    hbSequenceInL2 (hbFinitePrefix n x) := by
  unfold hbSequenceInL2
  apply summable_of_ne_finset_zero (s := Finset.range (n + 1))
  intro m hm
  have hmn : n < m := by
    have hnot : ¬ m < n + 1 := by
      simpa [Finset.mem_range] using hm
    omega
  simp [hbFinitePrefix, not_le.mpr hmn]

private theorem hb_sequence_l2_norm_smul_of_nonneg
    {d : ℕ} {c : ℝ} (hc : 0 ≤ c) (x : ℕ → Vec d) :
    hbSequenceL2Norm (fun n => c • x n) =
      c * hbSequenceL2Norm x := by
  have henergy :
      hbSequenceEnergy (fun n => c • x n) =
        c ^ 2 * hbSequenceEnergy x := by
    unfold hbSequenceEnergy
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, mul_pow]
  unfold hbSequenceL2Norm
  rw [henergy, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs,
    abs_of_nonneg hc]

private theorem hb_centered_nonlinearity_l2_bound
    {q a b : ℝ} (hD : ParameterDomain q a b) {d : ℕ}
    (hf : AdmissibleObjective q d) (x : ℕ → Vec d)
    (hx : hbSequenceInL2 x) :
    hbSequenceInL2
      (fun n => hbCenteredNonlinearity (parameterDomain_q_pos hD) hf (x n)) ∧
      hbSequenceL2Norm
          (fun n => hbCenteredNonlinearity (parameterDomain_q_pos hD) hf (x n)) ≤
        hbL0 q * hbSequenceL2Norm x := by
  let D : ℕ → Vec d :=
    fun n => hbCenteredNonlinearity (parameterDomain_q_pos hD) hf (x n)
  have hL : 0 ≤ hbL0 q := by
    dsimp [hbL0]
    linarith [parameterDomain_q_lt_one hD]
  have hmajor :
      Summable (fun n : ℕ => (hbL0 q * ‖x n‖) ^ 2) := by
    have hs :
        Summable (fun n : ℕ => (hbL0 q) ^ 2 * ‖x n‖ ^ 2) :=
      (show Summable (fun n : ℕ => ‖x n‖ ^ 2) from hx).const_smul
        ((hbL0 q) ^ 2)
    convert hs using 1
    · funext n
      ring
  have hmajor' :
      Summable (fun n : ℕ => (hbL0 q) ^ 2 * ‖x n‖ ^ 2) := by
    exact
      (show Summable (fun n : ℕ => ‖x n‖ ^ 2) from hx).const_smul
        ((hbL0 q) ^ 2)
  have hDsum : Summable (fun n : ℕ => ‖D n‖ ^ 2) := by
    apply Summable.of_nonneg_of_le
      (fun n => sq_nonneg (‖D n‖))
    · intro n
      have hpoint :
          ‖D n‖ ≤ hbL0 q * ‖x n‖ := by
        exact hbCenteredNonlinearity_lipschitz_from_zero
          (parameterDomain_q_pos hD) hf (x n)
      have hright : 0 ≤ hbL0 q * ‖x n‖ :=
        mul_nonneg hL (norm_nonneg _)
      exact (sq_le_sq₀ (norm_nonneg _) hright).2 hpoint
    · exact hmajor
  have hpoint :
      ∀ n : ℕ, ‖D n‖ ^ 2 ≤ (hbL0 q) ^ 2 * ‖x n‖ ^ 2 := by
    intro n
    have hbound :
        ‖D n‖ ≤ hbL0 q * ‖x n‖ :=
      hbCenteredNonlinearity_lipschitz_from_zero
        (parameterDomain_q_pos hD) hf (x n)
    have hright : 0 ≤ hbL0 q * ‖x n‖ :=
      mul_nonneg hL (norm_nonneg _)
    calc
      ‖D n‖ ^ 2 ≤ (hbL0 q * ‖x n‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) hright).2 hbound
      _ = (hbL0 q) ^ 2 * ‖x n‖ ^ 2 := by ring
  have hsum_le :
      hbSequenceEnergy D ≤ (hbL0 q) ^ 2 * hbSequenceEnergy x := by
    calc
      hbSequenceEnergy D ≤
          ∑' n : ℕ, (hbL0 q) ^ 2 * ‖x n‖ ^ 2 := by
            exact hDsum.tsum_le_tsum hpoint hmajor'
      _ = (hbL0 q) ^ 2 * hbSequenceEnergy x := by
        unfold hbSequenceEnergy
        rw [tsum_mul_left]
  have hnorm_le :
      hbSequenceL2Norm D ≤
        Real.sqrt ((hbL0 q) ^ 2 * hbSequenceEnergy x) := by
    unfold hbSequenceL2Norm
    exact Real.sqrt_le_sqrt hsum_le
  refine ⟨hDsum, ?_⟩
  calc
    hbSequenceL2Norm D ≤
        Real.sqrt ((hbL0 q) ^ 2 * hbSequenceEnergy x) := hnorm_le
    _ = hbL0 q * hbSequenceL2Norm x := by
      unfold hbSequenceL2Norm
      rw [Real.sqrt_mul (sq_nonneg (hbL0 q)),
        Real.sqrt_sq_eq_abs, abs_of_nonneg hL]

private theorem hbPlantResponse_smul
    {q a b : ℝ} {d : ℕ} (c : ℝ) (u : ℕ → Vec d) :
    ∀ n : ℕ,
      hbPlantResponse q a b (fun t => c • u t) n =
        c • hbPlantResponse q a b u n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simp [hbPlantResponse]
      | succ n =>
          cases n with
          | zero =>
              simp [hbPlantResponse]
              module
          | succ n =>
              have hprev1 := ih (n + 1) (by omega)
              have hprev0 := ih n (by omega)
              simp [hbPlantResponse, hprev1, hprev0, smul_sub, smul_smul]
              module

private theorem hb_d9_one_step_prefix_bound_of_old_tau_loop_gain
    {q a b : ℝ} (hD : ParameterDomain q a b)
    (hplant : hbPlantL2GainBound q a b (hbPlantL2Gain q a b))
    (hmult : hbMultiplierL2GainBound hbMultiplierL2Gain)
    {d : ℕ} (hdim : 1 ≤ d) (hf : AdmissibleObjective q d)
    (τ δ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hδ0 : 0 < δ) (hτδ1 : τ + δ ≤ 1)
    (hstep : hbD9ContinuationStepAdmissible q a b δ)
    (hOld :
      ∀ e y : ℕ → Vec d,
        hbSequenceInL2 e →
          hbHomotopyLoopEquation (parameterDomain_q_pos hD) a b hf τ e y →
            hbSequenceInL2 y ∧
              hbSequenceL2Norm y ≤ hbD9C0 q a b * hbSequenceL2Norm e)
    (e x : ℕ → Vec d) (he : hbSequenceInL2 e)
    (hnew :
      hbHomotopyLoopEquation (parameterDomain_q_pos hD) a b hf (τ + δ) e x) :
    (∀ n : ℕ,
      hbSequenceInL2 (hbFinitePrefix n x) ∧
        hbSequenceL2Norm (hbFinitePrefix n x) ≤
          2 * hbD9C0 q a b * hbSequenceL2Norm e) ∧
      hbSequenceInL2 x := by
  have hC0 : 0 ≤ hbD9C0 q a b := by
    exact le_trans (by norm_num)
      (hbD9C0_ge_one_of_gain_bounds hD hplant hmult)
  have hq := parameterDomain_q_pos hD
  rcases hstep with ⟨hδstep, hcontract⟩
  have hδstep' : 0 < δ := hδstep
  have hprefix_bound : ∀ n : ℕ,
      hbSequenceInL2 (hbFinitePrefix n x) ∧
        hbSequenceL2Norm (hbFinitePrefix n x) ≤
          2 * hbD9C0 q a b * hbSequenceL2Norm e := by
    intro n
    let xp : ℕ → Vec d := hbFinitePrefix n x
    let dx : ℕ → Vec d :=
      fun t => hbCenteredNonlinearity hq hf (x t)
    let dp : ℕ → Vec d :=
      fun t => hbCenteredNonlinearity hq hf (xp t)
    let r : ℕ → Vec d :=
      fun t => e t + δ • hbPlantResponse q a b dp t
    let y : ℕ → Vec d := hbCausalLoopSolution hq a b hf τ r
    have hxp : hbSequenceInL2 xp := by
      simpa [xp] using hbFinitePrefix_in_l2 n x
    have hdp :
        hbSequenceInL2 dp ∧
          hbSequenceL2Norm dp ≤ hbL0 q * hbSequenceL2Norm xp := by
      simpa [dp, xp] using
        hb_centered_nonlinearity_l2_bound hD hf xp hxp
    have hplant_dp :=
      hplant.2 dp hdp.1
    have hδplant : hbSequenceInL2
        (fun t : ℕ => δ • hbPlantResponse q a b dp t) := by
      have hs := hplant_dp.1.const_smul (δ ^ 2)
      unfold hbSequenceInL2 at hs ⊢
      convert hs using 1
      funext t
      simp [norm_smul, Real.norm_eq_abs, abs_of_pos hδstep', mul_pow]
    have hr :
        hbSequenceInL2 r ∧
          hbSequenceL2Norm r ≤ hbSequenceL2Norm e +
            δ * hbPlantL2Gain q a b * hbL0 q *
              hbSequenceL2Norm xp := by
      have hsum :=
        hb_sequence_l2_norm_add_le he hδplant
      have hdp_scaled :
          δ * (hbPlantL2Gain q a b * hbSequenceL2Norm dp) ≤
            δ * (hbPlantL2Gain q a b *
              (hbL0 q * hbSequenceL2Norm xp)) := by
        have h₁ :
            hbPlantL2Gain q a b * hbSequenceL2Norm dp ≤
              hbPlantL2Gain q a b *
                (hbL0 q * hbSequenceL2Norm xp) :=
          mul_le_mul_of_nonneg_left hdp.2 hplant.1
        exact mul_le_mul_of_nonneg_left h₁ hδstep'.le
      refine ⟨?_, ?_⟩
      · simpa [r] using hsum.1
      · calc
          hbSequenceL2Norm r ≤
              hbSequenceL2Norm e +
                hbSequenceL2Norm
                  (fun t : ℕ => δ • hbPlantResponse q a b dp t) := by
                    simpa [r] using hsum.2
          _ = hbSequenceL2Norm e +
                δ * hbSequenceL2Norm (hbPlantResponse q a b dp) := by
                  rw [hb_sequence_l2_norm_smul_of_nonneg
                    (le_of_lt hδstep')]
          _ ≤ hbSequenceL2Norm e +
                δ * (hbPlantL2Gain q a b * hbSequenceL2Norm dp) := by
                  exact add_le_add (le_refl _)
                    (mul_le_mul_of_nonneg_left hplant_dp.2 hδstep'.le)
          _ ≤ hbSequenceL2Norm e +
                δ * (hbPlantL2Gain q a b *
                  (hbL0 q * hbSequenceL2Norm xp)) := by
                  exact add_le_add (le_refl _) hdp_scaled
          _ = hbSequenceL2Norm e +
                δ * hbPlantL2Gain q a b * hbL0 q *
                  hbSequenceL2Norm xp := by ring
    have hy_eq :
        hbHomotopyLoopEquation hq a b hf τ r y := by
      simpa [y] using hbCausalLoopSolution_loop_equation hq hf τ r
    have hy_old := hOld r y hr.1 hy_eq
    have hprefix_eq : ∀ k : ℕ, k ≤ n → y k = x k := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
          intro hk
          have hxk :
              x k = e k +
                hbPlantResponse q a b
                  (fun t => (τ + δ) • dx t) k := by
            have ht := hnew k
            simpa [hbHomotopyLoopEquation, hbHomotopyInput, dx] using ht
          have hyk :
              y k = r k +
                hbPlantResponse q a b
                  (fun t => τ •
                    hbCenteredNonlinearity hq hf (y t)) k := by
            have ht := hy_eq k
            simpa [hbHomotopyLoopEquation, hbHomotopyInput] using ht
          have hdpdx : ∀ j : ℕ, j < k → dp j = dx j := by
            intro j hj
            have hjn : j ≤ n := le_trans (Nat.le_of_lt hj) hk
            simp [dp, dx, xp, hbFinitePrefix, hjn]
          have hdy_dx : ∀ j : ℕ, j < k →
              hbCenteredNonlinearity hq hf (y j) = dx j := by
            intro j hj
            rw [ih j hj (le_trans (Nat.le_of_lt hj) hk)]
          have hplant_prefix :
              hbPlantResponse q a b dp k =
                hbPlantResponse q a b dx k :=
            hbPlantResponse_strictlyCausal q a b dp dx k hdpdx
          have hplant_old :
              hbPlantResponse q a b
                  (fun t => τ •
                    hbCenteredNonlinearity hq hf (y t)) k =
                hbPlantResponse q a b (fun t => τ • dx t) k :=
            hbPlantResponse_strictlyCausal q a b
              (fun t => τ • hbCenteredNonlinearity hq hf (y t))
              (fun t => τ • dx t) k (by
                intro j hj
                simpa using congrArg (fun z : Vec d => τ • z) (hdy_dx j hj))
          calc
            y k = r k +
                hbPlantResponse q a b
                  (fun t => τ •
                    hbCenteredNonlinearity hq hf (y t)) k := hyk
            _ = e k + δ • hbPlantResponse q a b dp k +
                hbPlantResponse q a b
                  (fun t => τ •
                    hbCenteredNonlinearity hq hf (y t)) k := by
                  rfl
            _ = e k + δ • hbPlantResponse q a b dx k +
                hbPlantResponse q a b (fun t => τ • dx t) k := by
                  rw [hplant_prefix, hplant_old]
            _ = e k + (τ + δ) •
                hbPlantResponse q a b dx k := by
                  rw [hbPlantResponse_smul τ dx k]
                  module
            _ = x k := by
              have hxk' :
                  x k = e k + (τ + δ) •
                    hbPlantResponse q a b dx k := by
                calc
                  x k = e k +
                      hbPlantResponse q a b
                        (fun t => (τ + δ) • dx t) k := hxk
                  _ = e k + (τ + δ) •
                      hbPlantResponse q a b dx k := by
                        rw [hbPlantResponse_smul (τ + δ) dx k]
              exact hxk'.symm
    have hxy : hbFinitePrefix n y = hbFinitePrefix n x := by
      funext t
      by_cases htn : t ≤ n
      · simp [hbFinitePrefix, htn, hprefix_eq t htn]
      · simp [hbFinitePrefix, htn]
    have henergy_prefix_le :
        hbSequenceEnergy (hbFinitePrefix n y) ≤
          hbSequenceEnergy y := by
      have hprefixy := hbFinitePrefix_in_l2 n y
      have hpoint : ∀ t : ℕ,
          ‖hbFinitePrefix n y t‖ ^ 2 ≤ ‖y t‖ ^ 2 := by
        intro t
        by_cases htn : t ≤ n
        · simp [hbFinitePrefix, htn]
        · simp [hbFinitePrefix, htn]
      exact (by
        unfold hbSequenceEnergy
        exact hprefixy.tsum_le_tsum hpoint hy_old.1)
    have hnorm_prefix_y :
        hbSequenceL2Norm (hbFinitePrefix n y) ≤
          hbSequenceL2Norm y := by
      unfold hbSequenceL2Norm
      exact Real.sqrt_le_sqrt henergy_prefix_le
    have hnorm_prefix_x :
        hbSequenceL2Norm xp ≤ hbSequenceL2Norm y := by
        simpa [xp] using
        (show hbSequenceL2Norm (hbFinitePrefix n x) ≤
            hbSequenceL2Norm y by
          rw [← hxy]
          exact hnorm_prefix_y)
    have hprefix_old :
        hbSequenceL2Norm xp ≤
          hbD9C0 q a b * hbSequenceL2Norm r :=
      hnorm_prefix_x.trans hy_old.2
    have hprefix_ineq :
        hbSequenceL2Norm xp ≤
          hbD9C0 q a b * hbSequenceL2Norm e +
            (hbD9C0 q a b * δ * hbPlantL2Gain q a b * hbL0 q) *
              hbSequenceL2Norm xp := by
      calc
        hbSequenceL2Norm xp ≤
            hbD9C0 q a b * hbSequenceL2Norm r := hprefix_old
        _ ≤ hbD9C0 q a b *
            (hbSequenceL2Norm e +
              δ * hbPlantL2Gain q a b * hbL0 q *
                hbSequenceL2Norm xp) := by
              exact mul_le_mul_of_nonneg_left hr.2 hC0
        _ = hbD9C0 q a b * hbSequenceL2Norm e +
            (hbD9C0 q a b * δ * hbPlantL2Gain q a b * hbL0 q) *
              hbSequenceL2Norm xp := by ring
    have hcontract_mul :
        (hbD9C0 q a b * δ * hbPlantL2Gain q a b * hbL0 q) *
            hbSequenceL2Norm xp ≤
          (1 / 2 : ℝ) * hbSequenceL2Norm xp :=
      mul_le_mul_of_nonneg_right hcontract (Real.sqrt_nonneg _)
    have hbound :
        hbSequenceL2Norm xp ≤
          2 * hbD9C0 q a b * hbSequenceL2Norm e := by
      nlinarith [hprefix_ineq, hcontract_mul]
    exact ⟨by simpa [xp] using hxp, by simpa [xp] using hbound⟩
  refine ⟨hprefix_bound, ?_⟩
  exact hb_d9_l2_of_uniform_finite_prefix_bound x
    (2 * hbD9C0 q a b * hbSequenceL2Norm e)
    (fun n => (hprefix_bound n).2)

private theorem hbPlantL2Gain_le_reciprocal_on_box
    {q a b : ℝ} (hbox : HB_Box q a b) :
    hbPlantL2Gain q a b ≤ 1 / q := by
  let B : ℝ := 1 / q
  let S : Set ℝ := {C : ℝ | hbPlantL2GainBound q a b C}
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact (one_div_pos.mpr
      (parameterDomain_q_pos (HB_box_subset_domain hbox))).le
  have hB_bound : hbPlantL2GainBound q a b B := by
    refine ⟨hB_nonneg, ?_⟩
    intro d input hinput
    simpa [B] using hbPlant_l2_bound_on_box hbox input hinput
  have hS_bddBelow : BddBelow S := by
    refine ⟨0, ?_⟩
    intro C hC
    have hC' : hbPlantL2GainBound q a b C := by
      simpa [S] using hC
    exact hC'.1
  unfold hbPlantL2Gain
  apply csInf_le hS_bddBelow
  simpa [S, B] using hB_bound

private theorem hbMultiplierL2Gain_lt_three :
    hbMultiplierL2Gain < 3 := by
  let B : ℝ := hbMultiplierEpsilon + 2 + 8 / 25
  let S : Set ℝ := {C : ℝ | hbMultiplierL2GainBound C}
  have hB_nonneg : 0 ≤ B := by
    norm_num [B, hbMultiplierEpsilon]
  have hB_bound : hbMultiplierL2GainBound B := by
    refine ⟨hB_nonneg, ?_⟩
    intro d s hs
    simpa [B] using hb_multiplier_finite_lag_l2_bound hs
  have hS_bddBelow : BddBelow S := by
    refine ⟨0, ?_⟩
    intro C hC
    have hC' : hbMultiplierL2GainBound C := by
      simpa [S] using hC
    exact hC'.1
  have hgain_le_B : sInf S ≤ B := by
    apply csInf_le hS_bddBelow
    simpa [S] using hB_bound
  unfold hbMultiplierL2Gain
  have hB_lt_three : B < 3 := by
    norm_num [B, hbMultiplierEpsilon]
  exact lt_of_le_of_lt hgain_le_B hB_lt_three

theorem HB_CAUSAL_CONTINUATION {q a b : ℝ} (hbox : HB_Box q a b)
    : hbCausalContinuationConclusion q a b (HB_box_subset_domain hbox) := by
  let hD := HB_box_subset_domain hbox
  have hplant :
      hbPlantL2GainBound q a b (hbPlantL2Gain q a b) :=
    hbPlantL2Gain_is_bound_on_box hbox
  have hmult : hbMultiplierL2GainBound hbMultiplierL2Gain :=
    hbMultiplierL2Gain_is_bound
  have hquad :
      hbD9ConditionalQuadraticEstimate q a b hD :=
    hb_d9_conditional_quadratic_estimate_of_l2_loop hbox
  have hgain :
      hbD9ConditionalGainEstimate q a b hD :=
    hbD9ConditionalGainEstimate_of_quadratic hbox hquad
  have hcond : hbD9ConditionalEstimate q a b hD :=
    ⟨hquad, hgain⟩
  refine ⟨hplant, hmult, hcond, ?_⟩
  have hL0_nonneg : 0 ≤ hbL0 q := by
    dsimp [hbL0]
    linarith [parameterDomain_q_lt_one hD]
  have hC0_ge : 1 ≤ hbD9C0 q a b :=
    hbD9C0_ge_one_of_gain_bounds hD hplant hmult
  have hC0_nonneg : 0 ≤ hbD9C0 q a b :=
    le_trans (by norm_num) hC0_ge
  have hg_nonneg : 0 ≤ hbPlantL2Gain q a b := hplant.1
  have hloop_all :
      ∀ {d : ℕ}, 1 ≤ d →
        ∀ (hf : AdmissibleObjective q d) (τ : ℝ),
          0 ≤ τ → τ ≤ 1 →
            ∀ e x : ℕ → Vec d,
              hbSequenceInL2 e →
                hbHomotopyLoopEquation
                    (parameterDomain_q_pos hD) a b hf τ e x →
                  hbSequenceInL2 x ∧
                    hbSequenceL2Norm x ≤
                      hbD9C0 q a b * hbSequenceL2Norm e := by
    intro d hd hf τ hτ0 hτ1 e x he hloop
    by_cases hτzero : τ = 0
    · have hloop0 :
          hbHomotopyLoopEquation
              (parameterDomain_q_pos hD) a b hf 0 e x := by
        simpa [hτzero] using hloop
      exact hb_d9_loop_conclusion_tau_zero hD hplant hmult hf e x he hloop0
    · have hτpos : 0 < τ :=
        lt_of_le_of_ne hτ0 (Ne.symm hτzero)
      let A : ℝ :=
        hbD9C0 q a b * hbPlantL2Gain q a b * hbL0 q
      obtain ⟨J, hJ⟩ := exists_nat_ge (max (1 : ℝ) (2 * A))
      have hJone : (1 : ℝ) ≤ (J : ℝ) :=
        le_trans (le_max_left _ _) hJ
      have hJpos : (0 : ℝ) < (J : ℝ) :=
        lt_of_lt_of_le zero_lt_one hJone
      have hJnat : 1 ≤ J := by
        exact_mod_cast hJone
      let δ : ℝ := τ / (J : ℝ)
      have hJdelta : (J : ℝ) * δ = τ := by
        dsimp [δ]
        field_simp [ne_of_gt hJpos]
      have hmesh_le :
          ∀ {k : ℕ}, k ≤ J → (k : ℝ) * δ ≤ τ := by
        intro k hk
        have hkcast : (k : ℝ) ≤ (J : ℝ) := by
          exact_mod_cast hk
        calc
          (k : ℝ) * δ ≤ (J : ℝ) * δ :=
            mul_le_mul_of_nonneg_right hkcast (le_of_lt (div_pos hτpos hJpos))
          _ = τ := hJdelta
      have hδpos : 0 < δ := by
        dsimp [δ]
        exact div_pos hτpos hJpos
      have hA_nonneg : 0 ≤ A := by
        dsimp [A]
        exact mul_nonneg (mul_nonneg hC0_nonneg hg_nonneg) hL0_nonneg
      have hA_bound : 2 * A ≤ (J : ℝ) :=
        le_trans (le_max_right _ _) hJ
      have hA_div : A / (J : ℝ) ≤ (1 / 2 : ℝ) := by
        apply (div_le_iff₀ hJpos).2
        nlinarith
      have hAδ : A * δ ≤ (1 / 2 : ℝ) := by
        have hAdiv_nonneg : 0 ≤ A / (J : ℝ) :=
          div_nonneg hA_nonneg hJpos.le
        calc
          A * δ = (A / (J : ℝ)) * τ := by
            dsimp [δ]
            field_simp [ne_of_gt hJpos]
          _ ≤ (A / (J : ℝ)) * 1 :=
            mul_le_mul_of_nonneg_left hτ1 hAdiv_nonneg
          _ = A / (J : ℝ) := by ring
          _ ≤ (1 / 2 : ℝ) := hA_div
      have hcontract :
          hbD9C0 q a b * δ * hbPlantL2Gain q a b * hbL0 q ≤
            (1 / 2 : ℝ) := by
        simpa [A, mul_assoc, mul_left_comm, mul_comm] using hAδ
      have hstep : hbD9ContinuationStepAdmissible q a b δ :=
        ⟨hδpos, hcontract⟩
      have hind :
          ∀ k : ℕ, k ≤ J →
            ∀ e x : ℕ → Vec d,
              hbSequenceInL2 e →
                hbHomotopyLoopEquation
                    (parameterDomain_q_pos hD) a b hf
                      ((k : ℝ) * δ) e x →
                  hbSequenceInL2 x ∧
                    hbSequenceL2Norm x ≤
                      hbD9C0 q a b * hbSequenceL2Norm e := by
        intro k
        induction k with
        | zero =>
            intro hk e x he hloop0
            have hloop_zero :
                hbHomotopyLoopEquation
                    (parameterDomain_q_pos hD) a b hf 0 e x := by
              simpa using hloop0
            exact hb_d9_loop_conclusion_tau_zero hD hplant hmult hf
              e x he hloop_zero
        | succ k ih =>
            intro hk e x he hloop_next
            have hk_prev : k ≤ J := by omega
            have hτ_prev0 : 0 ≤ (k : ℝ) * δ := by
              exact mul_nonneg (by positivity) hδpos.le
            have hτ_prev1 : (k : ℝ) * δ ≤ 1 :=
              (hmesh_le hk_prev).trans hτ1
            have hτ_next0 : 0 ≤ ((k + 1 : ℕ) : ℝ) * δ := by
              exact mul_nonneg (by positivity) hδpos.le
            have hτ_next1 : ((k + 1 : ℕ) : ℝ) * δ ≤ 1 :=
              (hmesh_le hk).trans hτ1
            have hloop_old :
                ∀ e y : ℕ → Vec d,
                  hbSequenceInL2 e →
                    hbHomotopyLoopEquation
                        (parameterDomain_q_pos hD) a b hf
                          ((k : ℝ) * δ) e y →
                      hbSequenceInL2 y ∧
                        hbSequenceL2Norm y ≤
                          hbD9C0 q a b * hbSequenceL2Norm e := by
              intro e y he hy
              exact ih hk_prev e y he hy
            have hadd :
                (k : ℝ) * δ + δ =
                  ((k + 1 : ℕ) : ℝ) * δ := by
              push_cast
              ring
            have hloop_new :
                hbHomotopyLoopEquation
                    (parameterDomain_q_pos hD) a b hf
                      ((k : ℝ) * δ + δ) e x := by
              rw [hadd]
              exact hloop_next
            have hprefix :=
              hb_d9_one_step_prefix_bound_of_old_tau_loop_gain
                hD hplant hmult hd hf ((k : ℝ) * δ) δ
                hτ_prev0 hτ_prev1 hδpos
                (by
                  simpa [hadd] using hτ_next1)
                hstep hloop_old e x he hloop_new
            have hsharp :=
              hgain hd hf (((k + 1 : ℕ) : ℝ) * δ)
                hτ_next0 hτ_next1 e x he hprefix.2 hloop_next
            exact ⟨hprefix.2, hsharp.2.2⟩
      have hloop_mesh :
          hbHomotopyLoopEquation
              (parameterDomain_q_pos hD) a b hf ((J : ℝ) * δ) e x := by
        rw [hJdelta]
        exact hloop
      have hfinal := hind J (le_rfl) e x he hloop_mesh
      exact hfinal
  have hprefix : hbD9FinitePrefixContinuation q a b hD := by
    intro d hd hf τ δ hτ0 hτ1 hτδ1 hstep e x he hnew
    have hOld :
        ∀ e y : ℕ → Vec d,
          hbSequenceInL2 e →
            hbHomotopyLoopEquation
                (parameterDomain_q_pos hD) a b hf τ e y →
              hbSequenceInL2 y ∧
                hbSequenceL2Norm y ≤
                  hbD9C0 q a b * hbSequenceL2Norm e :=
      hloop_all hd hf τ hτ0 hτ1
    exact
      hb_d9_one_step_prefix_bound_of_old_tau_loop_gain
        hD hplant hmult hd hf τ δ hτ0 hτ1 hstep.1 hτδ1
        hstep hOld e x he hnew
  have hschedule : hbD9GlobalContinuationSchedule q a b := by
    by_cases hgzero : hbPlantL2Gain q a b = 0
    · exact Or.inl hgzero
    · right
      let A : ℝ :=
        hbD9C0 q a b * hbPlantL2Gain q a b * hbL0 q
      obtain ⟨J, hJ⟩ := exists_nat_ge (max (1 : ℝ) (2 * A))
      have hJone : (1 : ℝ) ≤ (J : ℝ) :=
        le_trans (le_max_left _ _) hJ
      have hJpos : (0 : ℝ) < (J : ℝ) :=
        lt_of_lt_of_le zero_lt_one hJone
      have hJnat : 1 ≤ J := by
        exact_mod_cast hJone
      have hA_nonneg : 0 ≤ A := by
        dsimp [A]
        exact mul_nonneg (mul_nonneg hC0_nonneg hg_nonneg) hL0_nonneg
      have hA_bound : 2 * A ≤ (J : ℝ) :=
        le_trans (le_max_right _ _) hJ
      have hA_div : A / (J : ℝ) ≤ (1 / 2 : ℝ) := by
        apply (div_le_iff₀ hJpos).2
        nlinarith
      have hcontract :
          hbD9C0 q a b * (J : ℝ)⁻¹ * hbPlantL2Gain q a b *
              hbL0 q ≤ (1 / 2 : ℝ) := by
        have hAinv : A * (J : ℝ)⁻¹ ≤ (1 / 2 : ℝ) := by
          simpa [div_eq_mul_inv] using hA_div
        simpa [A, mul_assoc, mul_left_comm, mul_comm] using hAinv
      refine ⟨J, hJnat, ?_⟩
      exact ⟨inv_pos.mpr hJpos, hcontract⟩
  have hg_upper : hbPlantL2Gain q a b ≤ 1 / q :=
    hbPlantL2Gain_le_reciprocal_on_box hbox
  have hg_lt : hbPlantL2Gain q a b < 101 := by
    have hqpos : 0 < q := parameterDomain_q_pos hD
    have hq_lower : (999 / 100000 : ℝ) ≤ q := by
      have hqbox : |q - (1 / 100 : ℝ)| ≤ (1 / 100000 : ℝ) := hbox.1
      have hqabs := abs_le.mp hqbox
      norm_num at hqabs ⊢
      linarith [hqabs.1]
    have hrecip_lt : (1 : ℝ) / q < 101 := by
      apply (div_lt_iff₀ hqpos).2
      nlinarith
    exact lt_of_le_of_lt hg_upper hrecip_lt
  have hm_lt : hbMultiplierL2Gain < 3 :=
    hbMultiplierL2Gain_lt_three
  have hL0_lt : hbL0 q < 1 := by
    dsimp [hbL0]
    linarith [parameterDomain_q_pos hD]
  have hgl_lt :
      hbPlantL2Gain q a b * hbL0 q < 101 := by
    calc
      hbPlantL2Gain q a b * hbL0 q <
          101 * hbL0 q :=
        mul_lt_mul_of_pos_right hg_lt
          (parameterDomain_one_sub_q_pos hD)
      _ < 101 * 1 :=
        mul_lt_mul_of_pos_left hL0_lt (by norm_num)
      _ = 101 := by ring
  have hprod_lt :
      hbPlantL2Gain q a b * hbL0 q * hbMultiplierL2Gain <
        101 * 3 := by
    have hle :
        hbPlantL2Gain q a b * hbL0 q * hbMultiplierL2Gain ≤
          101 * hbMultiplierL2Gain :=
      mul_le_mul_of_nonneg_right hgl_lt.le hmult.1
    exact hle.trans_lt
      (mul_lt_mul_of_pos_left hm_lt (by norm_num))
  have hC0_lt : hbD9C0 q a b < 610000 := by
    have hEta : 0 < hbD9Eta := by
      norm_num [hbD9Eta]
    have hquot :
        hbPlantL2Gain q a b * hbL0 q * hbMultiplierL2Gain /
            hbD9Eta < 606000 := by
      have hdiv :=
        div_lt_div_of_pos_right hprod_lt hEta
      norm_num [hbD9Eta] at hdiv
      exact hdiv
    dsimp [hbD9C0]
    nlinarith
  have hloop : hbD9LoopConclusion q a b hD := by
    exact hloop_all
  have hexplicit : hbD9ExplicitConstantConclusion q a b hD := by
    refine ⟨hg_lt, hm_lt, ?_⟩
    intro d hd hf τ hτ0 hτ1 e x he hnew
    have hresult := hloop_all hd hf τ hτ0 hτ1 e x he hnew
    refine ⟨hresult.1, ?_⟩
    exact hresult.2.trans
      (mul_le_mul_of_nonneg_right hC0_lt.le (Real.sqrt_nonneg _))
  exact ⟨hprefix, hschedule, hloop, hexplicit⟩

/-- D9 square-summability transported to the centered actual trajectory.

The D10 state `Y_t` is centered by the minimizer translation; the uncentered
`hbStateAt` pair is related separately by
`hbCenteredStateAt_eq_centered_hbStateAt`. -/
private theorem hb_free_response_l2_of_box
    {q a b : ℝ} (hbox : HB_Box q a b) {d : ℕ}
    (u v : Vec d) :
    hbSequenceInL2 (hbFreeResponse q a b u v) := by
  obtain ⟨k, hk_zero, hk_one, hk_rec, hk_nonneg, hk_summable, hmass⟩ :=
    hb_box_impulse_kernel_data hbox
  let delay : ℕ → ℝ := fun n => if n = 0 then 0 else k (n - 1)
  have hdelay_shift : Summable (fun n : ℕ => delay (n + 1)) := by
    simpa [delay] using hk_summable
  have hdelay : Summable delay :=
    (summable_nat_add_iff 1).1 hdelay_shift
  have hksq : Summable (fun n : ℕ => k n ^ 2) := by
    let K : ℝ := ∑' n : ℕ, k n
    have hK_nonneg : 0 ≤ K := by
      exact tsum_nonneg hk_nonneg
    have hk_le : ∀ n : ℕ, k n ≤ K := by
      intro n
      simpa [K] using
        hk_summable.sum_le_tsum ({n} : Finset ℕ)
          (fun m _ => hk_nonneg m)
    have hmajor : Summable (fun n : ℕ => K * k n) :=
      Summable.mul_left K hk_summable
    refine Summable.of_nonneg_of_le (fun n => sq_nonneg (k n)) ?_ hmajor
    intro n
    have hmul := mul_le_mul_of_nonneg_right (hk_le n) (hk_nonneg n)
    simpa [pow_two, mul_comm] using hmul
  have hdelay_sq : Summable (fun n : ℕ => delay n ^ 2) := by
    have hshift : Summable (fun n : ℕ => delay (n + 1) ^ 2) := by
      simpa [delay] using hksq
    exact (summable_nat_add_iff 1).1 hshift
  have hkv : hbSequenceInL2 (fun n : ℕ => k n • v) := by
    unfold hbSequenceInL2
    have hscale := Summable.mul_left (‖v‖ ^ 2) hksq
    apply Summable.congr hscale
    intro n
    have hkn : 0 ≤ k n := hk_nonneg n
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hkn]
    ring
  have hdu : hbSequenceInL2 (fun n : ℕ => delay n • u) := by
    unfold hbSequenceInL2
    have hscale := Summable.mul_left (‖u‖ ^ 2) hdelay_sq
    apply Summable.congr hscale
    intro n
    have hdn : 0 ≤ delay n := by
      dsimp [delay]
      split
      · simp
      · exact hk_nonneg _
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hdn]
    ring
  have hbdu : hbSequenceInL2 (fun n : ℕ => b • (delay n • u)) := by
    unfold hbSequenceInL2
    have hscale := Summable.mul_left (b ^ 2)
      (show Summable (fun n : ℕ => ‖delay n • u‖ ^ 2) from hdu)
    apply Summable.congr hscale
    intro n
    have hdn : 0 ≤ delay n := by
      dsimp [delay]
      split
      · simp
      · exact hk_nonneg _
    simp only [norm_smul, Real.norm_eq_abs]
    rw [abs_of_nonneg hdn]
    calc
      b ^ 2 * (delay n * ‖u‖) ^ 2 =
          |b| ^ 2 * (delay n * ‖u‖) ^ 2 := by
            rw [sq_abs b]
      _ = (|b| * (delay n * ‖u‖)) ^ 2 := by ring
  have hneg : hbSequenceInL2 (fun n : ℕ => -(b • (delay n • u))) := by
    simpa [hbSequenceInL2] using hbdu
  have hdelay_rec (n : ℕ) :
      (1 + b - a * q) * delay (n + 1) - b * delay n = k (n + 1) := by
    cases n with
    | zero =>
        simp [delay, hk_zero, hk_one]
    | succ n =>
        simpa [delay] using (hk_rec n).symm
  have hstep (n : ℕ) :
      (1 + b - a * q) •
          (k (n + 1) • v - b • (delay (n + 1) • u)) -
        b • (k n • v - b • (delay n • u)) =
      k (n + 2) • v - b • (delay (n + 2) • u) := by
    have hdelay_next : delay (n + 2) = k (n + 1) := by
      simp [delay]
    rw [hdelay_next]
    let c : ℝ := 1 + b - a * q
    change c •
          (k (n + 1) • v - b • (delay (n + 1) • u)) -
        b • (k n • v - b • (delay n • u)) =
      k (n + 2) • v - b • (k (n + 1) • u)
    calc
      c •
            (k (n + 1) • v - b • (delay (n + 1) • u)) -
          b • (k n • v - b • (delay n • u)) =
        ((c * k (n + 1) - b * k n) • v -
          b • ((c * delay (n + 1) -
            b * delay n) • u)) := by
              simp only [smul_sub, sub_smul, smul_smul]
              module
      _ = k (n + 2) • v - b • (k (n + 1) • u) := by
        dsimp [c]
        rw [hk_rec n, hdelay_rec n]
  have hrep : ∀ n : ℕ,
      hbFreeResponse q a b u v n =
        k n • v - b • (delay n • u) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        cases n with
        | zero =>
            simp [hbFreeResponse, delay, hk_zero]
        | succ n =>
            cases n with
            | zero =>
                simp [hbFreeResponse, delay, hk_zero, hk_one]
            | succ n =>
                change
                  (1 + b - a * q) •
                      hbFreeResponse q a b u v (n + 1) -
                    b • hbFreeResponse q a b u v n =
                    k (n + 2) • v - b • (delay (n + 2) • u)
                rw [ih (n + 1) (by omega), ih n (by omega)]
                exact hstep n
  have heq :
      (fun n : ℕ => hbFreeResponse q a b u v n) =
        (fun n : ℕ => k n • v + -(b • (delay n • u))) := by
    funext n
    rw [hrep n]
    simp [sub_eq_add_neg]
  unfold hbSequenceInL2
  change Summable (fun n : ℕ => ‖(fun m : ℕ =>
    hbFreeResponse q a b u v m) n‖ ^ 2)
  rw [heq]
  exact (hb_sequence_l2_norm_add_le hkv hneg).1

private theorem hb_centered_iterate_homotopy_loop_equation
    {q a b : ℝ} (hbox : HB_Box q a b) {d : ℕ} (hdim : 1 ≤ d)
    (hf : AdmissibleObjective q d) (xMinusOne xZero : Vec d) :
    hbHomotopyLoopEquation
      (parameterDomain_q_pos (HB_box_subset_domain hbox)) a b hf 1
      (hbFreeResponse q a b
        (xMinusOne -
          objectiveMinimizer (parameterDomain_q_pos (HB_box_subset_domain hbox)) hf)
        (xZero -
          objectiveMinimizer (parameterDomain_q_pos (HB_box_subset_domain hbox)) hf))
      (hbCenteredIterate
        (parameterDomain_q_pos (HB_box_subset_domain hbox)) a b hf
        xMinusOne xZero) := by
  have hgen :=
    hbLoopRepresentation_generated
      (parameterDomain_q_pos (HB_box_subset_domain hbox)) a b hf
      xMinusOne xZero
  unfold hbLoopRepresentation at hgen
  change ∀ t : ℕ,
    hbCenteredIterate
        (parameterDomain_q_pos (HB_box_subset_domain hbox)) a b hf
        xMinusOne xZero t =
      hbFreeResponse q a b
          (xMinusOne -
            objectiveMinimizer
              (parameterDomain_q_pos (HB_box_subset_domain hbox)) hf)
          (xZero -
            objectiveMinimizer
              (parameterDomain_q_pos (HB_box_subset_domain hbox)) hf) t +
        hbPlantResponse q a b
          (fun t : ℕ =>
            (1 : ℝ) • hbCenteredNonlinearity
              (parameterDomain_q_pos (HB_box_subset_domain hbox)) hf
              (hbCenteredIterate
                (parameterDomain_q_pos (HB_box_subset_domain hbox)) a b hf
                xMinusOne xZero t)) t
  simpa only [one_smul] using hgen

private theorem hb_centered_state_energy_summable_of_centered_iterate_l2
    {q : ℝ} {d : ℕ} (hq : 0 < q) (a b : ℝ)
    (hf : AdmissibleObjective q d) (xMinusOne xZero : Vec d)
    (hx :
      hbSequenceInL2
        (hbCenteredIterate hq a b hf xMinusOne xZero)) :
    Summable (fun t : ℕ =>
      centeredStateNormSq
        (hbCenteredStateAt hq a b hf xMinusOne xZero t)) := by
  let x : ℕ → Vec d := hbCenteredIterate hq a b hf xMinusOne xZero
  let Y : ℕ → HBState d :=
    hbCenteredStateAt hq a b hf xMinusOne xZero
  have hcurrent_x : Summable (fun t : ℕ => ‖x t‖ ^ 2) := by
    simpa [x] using hx
  have hcurrent :
      Summable (fun t : ℕ => ‖(Y t).2‖ ^ 2) := by
    apply Summable.congr hcurrent_x
    intro t
    have hbridge :=
      hbCenteredStateAt_eq_centered_hbStateAt
        hq a b hf xMinusOne xZero t
    dsimp only at hbridge
    have hsecond := congrArg Prod.snd hbridge
    have hsecond_Y :
        (Y t).2 =
          (hbStateAt a b hf xMinusOne xZero t).2 -
            objectiveMinimizer hq hf := by
      simpa [Y] using hsecond
    have hsecond_x :
        x t =
          (hbStateAt a b hf xMinusOne xZero t).2 -
            objectiveMinimizer hq hf := by
      simpa [x, hbCenteredIterate] using hsecond
    rw [hsecond_Y, hsecond_x]
  have hprevious_succ (n : ℕ) :
      (Y (n + 1)).1 = x n := by
    dsimp [Y, x]
    rw [hbCenteredStateAt_succ]
    simp [hbCenteredMap, hbCenteredIterate]
  have hprevious_shift :
      Summable (fun n : ℕ => ‖(Y (n + 1)).1‖ ^ 2) := by
    apply Summable.congr hcurrent_x
    intro n
    rw [hprevious_succ]
  have hprevious :
      Summable (fun t : ℕ => ‖(Y t).1‖ ^ 2) :=
    (summable_nat_add_iff 1).1 hprevious_shift
  have henergy :
      Summable (fun t : ℕ => ‖(Y t).1‖ ^ 2 + ‖(Y t).2‖ ^ 2) :=
    hprevious.add hcurrent
  simpa [Y, centeredStateNormSq] using henergy

theorem HB_centered_actual_trajectory_summable_of_causal_continuation {q a b : ℝ}
    (hbox : HB_Box q a b) {d : ℕ} (hdim : 1 ≤ d)
    (hf : AdmissibleObjective q d) (xMinusOne xZero : Vec d) :
    let hq := parameterDomain_q_pos (HB_box_subset_domain hbox)
    Summable (fun t : ℕ =>
      centeredStateNormSq
        (hbCenteredStateAt hq a b hf xMinusOne xZero t)) := by
  dsimp
  let hD := HB_box_subset_domain hbox
  let hq := parameterDomain_q_pos hD
  let xStar := objectiveMinimizer hq hf
  let e := hbFreeResponse q a b (xMinusOne - xStar) (xZero - xStar)
  let x := hbCenteredIterate hq a b hf xMinusOne xZero
  have he : hbSequenceInL2 e := by
    simpa [e, xStar, hq, hD] using
      hb_free_response_l2_of_box hbox (xMinusOne - xStar) (xZero - xStar)
  have hloop : hbHomotopyLoopEquation hq a b hf 1 e x := by
    simpa [e, x, xStar, hq, hD] using
      hb_centered_iterate_homotopy_loop_equation
        hbox hdim hf xMinusOne xZero
  have hcausal := HB_CAUSAL_CONTINUATION hbox
  have hx : hbSequenceInL2 x := by
    exact hcausal.2.2.2.2.2.1 hdim hf 1 (by norm_num) (by norm_num)
      e x he hloop |>.1
  simpa [x, hq, hD] using
    hb_centered_state_energy_summable_of_centered_iterate_l2
      hq a b hf xMinusOne xZero hx

set_option maxHeartbeats 4000000 in
private theorem hb_free_response_energy_bound_of_box
    {q a b : ℝ} (hbox : HB_Box q a b) {d : ℕ}
    (u v : Vec d) :
    hbSequenceInL2 (hbFreeResponse q a b u v) ∧
      hbSequenceEnergy (hbFreeResponse q a b u v) ≤
        100 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  obtain ⟨k, hk_zero, hk_one, hk_rec, hk_nonneg, hk_summable, hmass⟩ :=
    hb_box_impulse_kernel_data hbox
  have he : hbSequenceInL2 (hbFreeResponse q a b u v) :=
    hb_free_response_l2_of_box hbox u v
  obtain ⟨r₁, r₂, hr₂_pos, hr₂_lt_r₁, hr₁_lt_one, hrsum, hrprod,
    hr₁_root, hr₂_root⟩ := hb_box_characteristic_roots hbox
  have hr₁_pos : 0 < r₁ := lt_trans hr₂_pos hr₂_lt_r₁
  have hr₂_lt_one : r₂ < 1 := lt_trans hr₂_lt_r₁ hr₁_lt_one
  have hden_pos : 0 < r₁ - r₂ := sub_pos.mpr hr₂_lt_r₁
  have hone₁_pos : 0 < 1 - r₁ := sub_pos.mpr hr₁_lt_one
  have hone₂_pos : 0 < 1 - r₂ := sub_pos.mpr hr₂_lt_one
  have hb_pos : 0 < b := by
    rw [← hrprod]
    exact mul_pos hr₁_pos hr₂_pos
  have hb_lt_one : b < 1 := by
    calc
      b = r₁ * r₂ := hrprod.symm
      _ < r₁ * 1 := mul_lt_mul_of_pos_left hr₂_lt_one hr₁_pos
      _ = r₁ := by ring
      _ < 1 := hr₁_lt_one
  let α : ℝ := 1 + b - a * q
  let K : ℕ → ℝ :=
    fun n => (r₁ ^ (n + 1) - r₂ ^ (n + 1)) / (r₁ - r₂)
  have hK_zero : K 0 = 1 := by
    dsimp [K]
    field_simp [ne_of_gt hden_pos]
  have hK_one : K 1 = α := by
    dsimp [K, α]
    have hden_ne : r₁ - r₂ ≠ 0 := ne_of_gt hden_pos
    apply (div_eq_iff hden_ne).2
    calc
      r₁ ^ 2 - r₂ ^ 2 = (r₁ + r₂) * (r₁ - r₂) := by ring
      _ = (1 + b - a * q) * (r₁ - r₂) := by rw [hrsum]
  have hK_rec : ∀ n : ℕ, K (n + 2) = α * K (n + 1) - b * K n := by
    intro n
    dsimp [K, α]
    have hden_ne : r₁ - r₂ ≠ 0 := ne_of_gt hden_pos
    have hp₁ :
        r₁ ^ (n + 2 + 1) = r₁ ^ (n + 1) * r₁ ^ 2 := by
      rw [show n + 2 + 1 = (n + 1) + 2 by omega, pow_add]
    have hp₂ :
        r₂ ^ (n + 2 + 1) = r₂ ^ (n + 1) * r₂ ^ 2 := by
      rw [show n + 2 + 1 = (n + 1) + 2 by omega, pow_add]
    have hq₁ :
        r₁ ^ (n + 1 + 1) = r₁ ^ (n + 1) * r₁ := by
      rw [pow_succ]
    have hq₂ :
        r₂ ^ (n + 1 + 1) = r₂ ^ (n + 1) * r₂ := by
      rw [pow_succ]
    rw [hp₁, hp₂, hq₁, hq₂]
    field_simp [hden_ne]
    rw [hr₁_root, hr₂_root]
    ring
  have hk_eq_K : ∀ n : ℕ, k n = K n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        cases n with
        | zero =>
            rw [hk_zero, hK_zero]
        | succ n =>
            cases n with
            | zero =>
                rw [hk_one, hK_one]
            | succ n =>
                change k (n + 2) = K (n + 2)
                rw [hk_rec n, hK_rec n]
                rw [ih (n + 1) (by omega), ih n (by omega)]
  have hK_nonneg : ∀ n : ℕ, 0 ≤ K n := by
    intro n
    rw [← hk_eq_K n]
    exact hk_nonneg n
  have hgeo₁sq : Summable (fun n : ℕ => (r₁ ^ 2) ^ n) := by
    apply summable_geometric_of_lt_one
    · positivity
    · nlinarith [mul_pos hr₁_pos (sub_pos.mpr hr₁_lt_one)]
  have hgeo₂sq : Summable (fun n : ℕ => (r₂ ^ 2) ^ n) := by
    apply summable_geometric_of_lt_one
    · positivity
    · nlinarith [mul_pos hr₂_pos (sub_pos.mpr hr₂_lt_one)]
  have hgeo_b : Summable (fun n : ℕ => b ^ n) :=
    summable_geometric_of_lt_one hb_pos.le hb_lt_one
  have hA : Summable (fun n : ℕ => r₁ ^ 2 * (r₁ ^ 2) ^ n) :=
    Summable.mul_left (r₁ ^ 2) hgeo₁sq
  have hB : Summable (fun n : ℕ => r₂ ^ 2 * (r₂ ^ 2) ^ n) :=
    Summable.mul_left (r₂ ^ 2) hgeo₂sq
  have hC : Summable (fun n : ℕ => 2 * (b * b ^ n)) :=
    Summable.mul_left 2 (Summable.mul_left b hgeo_b)
  have hnum : Summable (fun n : ℕ =>
      r₁ ^ 2 * (r₁ ^ 2) ^ n + r₂ ^ 2 * (r₂ ^ 2) ^ n - 2 * (b * b ^ n)) :=
    (hA.add hB).sub hC
  have hKsq_point (n : ℕ) :
      K n ^ 2 = (r₁ - r₂)⁻¹ ^ 2 *
        (r₁ ^ 2 * (r₁ ^ 2) ^ n + r₂ ^ 2 * (r₂ ^ 2) ^ n -
          2 * (b * b ^ n)) := by
    dsimp [K]
    rw [div_pow]
    have hp₁ :
        (r₁ ^ (n + 1)) ^ 2 = r₁ ^ 2 * (r₁ ^ 2) ^ n := by
      calc
        (r₁ ^ (n + 1)) ^ 2 = r₁ ^ ((n + 1) * 2) := by
          rw [← pow_mul]
        _ = r₁ ^ (2 + n * 2) := by congr 1 <;> omega
        _ = r₁ ^ 2 * r₁ ^ (n * 2) := by rw [pow_add]
        _ = r₁ ^ 2 * (r₁ ^ 2) ^ n := by
          have hpow : r₁ ^ (n * 2) = (r₁ ^ 2) ^ n := by
            calc
              r₁ ^ (n * 2) = r₁ ^ (2 * n) := by congr 1 <;> omega
              _ = (r₁ ^ 2) ^ n := by rw [pow_mul]
          rw [hpow]
    have hp₂ :
        (r₂ ^ (n + 1)) ^ 2 = r₂ ^ 2 * (r₂ ^ 2) ^ n := by
      calc
        (r₂ ^ (n + 1)) ^ 2 = r₂ ^ ((n + 1) * 2) := by
          rw [← pow_mul]
        _ = r₂ ^ (2 + n * 2) := by congr 1 <;> omega
        _ = r₂ ^ 2 * r₂ ^ (n * 2) := by rw [pow_add]
        _ = r₂ ^ 2 * (r₂ ^ 2) ^ n := by
          have hpow : r₂ ^ (n * 2) = (r₂ ^ 2) ^ n := by
            calc
              r₂ ^ (n * 2) = r₂ ^ (2 * n) := by congr 1 <;> omega
              _ = (r₂ ^ 2) ^ n := by rw [pow_mul]
          rw [hpow]
    have hcross :
        r₁ ^ (n + 1) * r₂ ^ (n + 1) = b * b ^ n := by
      calc
        r₁ ^ (n + 1) * r₂ ^ (n + 1) =
            (r₁ * r₂) ^ (n + 1) := by rw [mul_pow]
        _ = b ^ (n + 1) := by rw [hrprod]
        _ = b * b ^ n := by rw [pow_succ]; ring
    rw [show (r₁ ^ (n + 1) - r₂ ^ (n + 1)) ^ 2 =
      (r₁ ^ (n + 1)) ^ 2 + (r₂ ^ (n + 1)) ^ 2 -
        2 * (r₁ ^ (n + 1) * r₂ ^ (n + 1)) by ring]
    rw [hp₁, hp₂, hcross]
    field_simp [ne_of_gt hden_pos]
  have hKsq : Summable (fun n : ℕ => K n ^ 2) := by
    have hscaled :
        Summable (fun n : ℕ => (r₁ - r₂)⁻¹ ^ 2 *
          (r₁ ^ 2 * (r₁ ^ 2) ^ n + r₂ ^ 2 * (r₂ ^ 2) ^ n -
            2 * (b * b ^ n))) :=
      Summable.mul_left ((r₁ - r₂)⁻¹ ^ 2) hnum
    apply Summable.congr hscaled
    intro n
    exact (hKsq_point n).symm
  have hsumA :
      (∑' n : ℕ, r₁ ^ 2 * (r₁ ^ 2) ^ n) =
        r₁ ^ 2 * (1 - r₁ ^ 2)⁻¹ := by
    rw [hgeo₁sq.tsum_mul_left,
      tsum_geometric_of_lt_one (by positivity)
        (by nlinarith [mul_pos hr₁_pos (sub_pos.mpr hr₁_lt_one)])]
  have hsumB :
      (∑' n : ℕ, r₂ ^ 2 * (r₂ ^ 2) ^ n) =
        r₂ ^ 2 * (1 - r₂ ^ 2)⁻¹ := by
    rw [hgeo₂sq.tsum_mul_left,
      tsum_geometric_of_lt_one (by positivity)
        (by nlinarith [mul_pos hr₂_pos (sub_pos.mpr hr₂_lt_one)])]
  have hsumC :
      (∑' n : ℕ, 2 * (b * b ^ n)) =
        2 * (b * (1 - b)⁻¹) := by
    have hCb : Summable (fun n : ℕ => b * b ^ n) :=
      Summable.mul_left b hgeo_b
    calc
      (∑' n : ℕ, 2 * (b * b ^ n)) =
          2 * (∑' n : ℕ, b * b ^ n) := hCb.tsum_mul_left 2
      _ = 2 * (b * (∑' n : ℕ, b ^ n)) := by
        rw [hgeo_b.tsum_mul_left]
      _ = 2 * (b * (1 - b)⁻¹) := by
        rw [tsum_geometric_of_lt_one hb_pos.le hb_lt_one]
  have hsumK :
      (∑' n : ℕ, K n ^ 2) =
        (r₁ - r₂)⁻¹ ^ 2 *
          (r₁ ^ 2 * (1 - r₁ ^ 2)⁻¹ +
            r₂ ^ 2 * (1 - r₂ ^ 2)⁻¹ -
              2 * (b * (1 - b)⁻¹)) := by
    calc
      (∑' n : ℕ, K n ^ 2) =
          ∑' n : ℕ, (r₁ - r₂)⁻¹ ^ 2 *
            (r₁ ^ 2 * (r₁ ^ 2) ^ n + r₂ ^ 2 * (r₂ ^ 2) ^ n -
              2 * (b * b ^ n)) := by
                apply tsum_congr
                intro n
                exact hKsq_point n
      _ = (r₁ - r₂)⁻¹ ^ 2 *
          ((∑' n : ℕ, r₁ ^ 2 * (r₁ ^ 2) ^ n +
            ∑' n : ℕ, r₂ ^ 2 * (r₂ ^ 2) ^ n) -
              ∑' n : ℕ, 2 * (b * b ^ n)) := by
                rw [hnum.tsum_mul_left]
                rw [Summable.tsum_sub (hA.add hB) hC,
                  Summable.tsum_add hA hB]
      _ = (r₁ - r₂)⁻¹ ^ 2 *
          (r₁ ^ 2 * (1 - r₁ ^ 2)⁻¹ +
            r₂ ^ 2 * (1 - r₂ ^ 2)⁻¹ -
              2 * (b * (1 - b)⁻¹)) := by rw [hsumA, hsumB, hsumC]
  have hmass_den :
      (1 - r₁ ^ 2) * (1 - r₂ ^ 2) =
        a * q * (2 * (1 + b) - a * q) := by
    have hrootmass : (1 - r₁) * (1 - r₂) = a * q := by
      calc
        (1 - r₁) * (1 - r₂) =
            1 - (r₁ + r₂) + r₁ * r₂ := by ring
        _ = a * q := by rw [hrsum, hrprod]; ring
    have hplus :
        (1 + r₁) * (1 + r₂) = 2 * (1 + b) - a * q := by
      calc
        (1 + r₁) * (1 + r₂) =
            1 + (r₁ + r₂) + r₁ * r₂ := by ring
        _ = 2 * (1 + b) - a * q := by rw [hrsum, hrprod]; ring
    calc
      (1 - r₁ ^ 2) * (1 - r₂ ^ 2) =
          ((1 - r₁) * (1 - r₂)) * ((1 + r₁) * (1 + r₂)) := by ring
      _ = (a * q) * ((1 + r₁) * (1 + r₂)) := by rw [hrootmass]
      _ = a * q * (2 * (1 + b) - a * q) := by rw [hplus]
  have hsumK_formula :
      (∑' n : ℕ, K n ^ 2) =
        (1 + b) / ((1 - b) * a * q * (2 * (1 + b) - a * q)) := by
    rw [hsumK]
    have hden_ne : r₁ - r₂ ≠ 0 := ne_of_gt hden_pos
    have h1_ne : 1 - r₁ ^ 2 ≠ 0 := by
      nlinarith [hone₁_pos, hr₁_pos]
    have h2_ne : 1 - r₂ ^ 2 ≠ 0 := by
      nlinarith [hone₂_pos, hr₂_pos]
    have hb_ne : 1 - b ≠ 0 := ne_of_gt (sub_pos.mpr hb_lt_one)
    have hq : 0 < q := parameterDomain_q_pos (HB_box_subset_domain hbox)
    have ha : 0 < a := (HB_box_subset_domain hbox).2.2.2.2.1
    have hrootmass : (1 - r₁) * (1 - r₂) = a * q := by
      calc
        (1 - r₁) * (1 - r₂) =
            1 - (r₁ + r₂) + r₁ * r₂ := by ring
        _ = a * q := by rw [hrsum, hrprod]; ring
    have hplus :
        (1 + r₁) * (1 + r₂) = 2 * (1 + b) - a * q := by
      calc
        (1 + r₁) * (1 + r₂) =
            1 + (r₁ + r₂) + r₁ * r₂ := by ring
        _ = 2 * (1 + b) - a * q := by rw [hrsum, hrprod]; ring
    have hbracket :
        r₁ ^ 2 * (1 - r₁ ^ 2)⁻¹ +
            r₂ ^ 2 * (1 - r₂ ^ 2)⁻¹ -
              2 * (b * (1 - b)⁻¹) =
          (1 + b) * (r₁ - r₂) ^ 2 /
            ((1 - b) * ((1 - r₁ ^ 2) * (1 - r₂ ^ 2))) := by
      field_simp [h1_ne, h2_ne, hb_ne]
      rw [← hrprod]
      ring
    rw [hbracket]
    have hDpos : 0 < 2 * (1 + b) - a * q := by
      rw [← hplus]
      positivity
    have hDne : 2 * (1 + b) - a * q ≠ 0 := ne_of_gt hDpos
    rw [hmass_den]
    field_simp [hden_ne, hDne, ne_of_gt hq, ne_of_gt ha]
  have hR_nonneg : 0 ≤ ∑' n : ℕ, K n ^ 2 :=
    tsum_nonneg (fun n => sq_nonneg (K n))
  have hR_lt : (∑' n : ℕ, K n ^ 2) < 60 := by
    rcases HB_BOX_ENDPOINT_RANGES hbox with
      ⟨hqlo, hqhi, halo, hahi, hblo, hbhi, hprod, ha2q, ha2q2, hbexpr⟩
    have haq_lower : (11 / 500 : ℝ) < a * q := by
      have hprod' : (9 / 4 : ℝ) * (99 / 10000 : ℝ) < a * q := by
        gcongr
      norm_num at hprod' ⊢
      nlinarith [hprod']
    have haq_upper : a * q < (253 / 10000 : ℝ) := by
      calc
        a * q < a * (11 / 1000 : ℝ) :=
          mul_lt_mul_of_pos_left hqhi
            (HB_box_subset_domain hbox).2.2.2.2.1
        _ < (23 / 10 : ℝ) * (11 / 1000 : ℝ) :=
          mul_lt_mul_of_pos_right hahi (by norm_num)
        _ = (253 / 10000 : ℝ) := by norm_num
    have hlast : (63 / 20 : ℝ) < 2 * (1 + b) - a * q := by
      nlinarith [hblo, haq_upper]
    have hden₁ : (39 / 100 : ℝ) < 1 - b := by linarith
    have hden_pos' :
        0 < (1 - b) * (a * q) * (2 * (1 + b) - a * q) := by
      positivity
    calc
      (∑' n : ℕ, K n ^ 2) =
          (1 + b) / ((1 - b) * a * q * (2 * (1 + b) - a * q)) :=
        hsumK_formula
      _ < (161 / 100 : ℝ) /
          ((39 / 100) * (11 / 500) * (63 / 20)) := by
        have hnum : 1 + b < (161 / 100 : ℝ) := by linarith
        have hden :
            (39 / 100 : ℝ) * (11 / 500) * (63 / 20) <
              (1 - b) * (a * q) * (2 * (1 + b) - a * q) := by
          gcongr
        rw [show (1 - b) * a * q * (2 * (1 + b) - a * q) =
          (1 - b) * (a * q) * (2 * (1 + b) - a * q) by ring]
        gcongr
      _ < 60 := by norm_num
  have hcoef_lt : (∑' n : ℕ, K n ^ 2) * (1 + b ^ 2) < 100 := by
    rcases HB_BOX_ENDPOINT_RANGES hbox with
      ⟨hqlo, hqhi, halo, hahi, hblo, hbhi, hprod, ha2q, ha2q2, hbexpr⟩
    have hb_sq : b ^ 2 < (61 / 100 : ℝ) ^ 2 := by
      nlinarith [hb_pos]
    have hmul :
        (∑' n : ℕ, K n ^ 2) * (1 + b ^ 2) <
          60 * (1 + (61 / 100 : ℝ) ^ 2) := by
      gcongr
    nlinarith
  let delay : ℕ → ℝ := fun n => if n = 0 then 0 else K (n - 1)
  have hdelay_sq : Summable (fun n : ℕ => delay n ^ 2) := by
    have hshift : Summable (fun n : ℕ => delay (n + 1) ^ 2) := by
      simpa [delay] using hKsq
    exact (summable_nat_add_iff 1).1 hshift
  have hdelay_tsum : (∑' n : ℕ, delay n ^ 2) = ∑' n : ℕ, K n ^ 2 := by
    have htail :
        (∑' n : ℕ, delay (n + 1) ^ 2) = ∑' n : ℕ, K n ^ 2 := by
      apply tsum_congr
      intro n
      simp [delay]
    have hsplit := hdelay_sq.sum_add_tsum_nat_add 1
    calc
      (∑' n : ℕ, delay n ^ 2) =
          (∑ n ∈ Finset.range 1, delay n ^ 2) +
            ∑' n : ℕ, delay (n + 1) ^ 2 := hsplit.symm
      _ = 0 + ∑' n : ℕ, K n ^ 2 := by simp [delay, htail]
      _ = ∑' n : ℕ, K n ^ 2 := by ring
  have hdelay_nonneg : ∀ n : ℕ, 0 ≤ delay n := by
    intro n
    dsimp [delay]
    split
    · simp
    · exact hK_nonneg _
  have hrep : ∀ n : ℕ,
      hbFreeResponse q a b u v n =
        K n • v - b • (delay n • u) := by
    have hdelay_rec (n : ℕ) :
        α * delay (n + 1) - b * delay n = K (n + 1) := by
      cases n with
      | zero =>
          simp [delay, α, hK_zero, hK_one]
      | succ n =>
          simpa [delay] using (hK_rec n).symm
    have hstep (n : ℕ) :
        α • (K (n + 1) • v - b • (delay (n + 1) • u)) -
          b • (K n • v - b • (delay n • u)) =
        K (n + 2) • v - b • (delay (n + 2) • u) := by
      have hdelay_next : delay (n + 2) = K (n + 1) := by
        simp [delay]
      rw [hdelay_next]
      calc
        α • (K (n + 1) • v - b • (delay (n + 1) • u)) -
              b • (K n • v - b • (delay n • u)) =
            ((α * K (n + 1) - b * K n) • v -
              b • ((α * delay (n + 1) - b * delay n) • u)) := by
                simp only [smul_sub, sub_smul, smul_smul]
                module
        _ = K (n + 2) • v - b • (K (n + 1) • u) := by
          rw [hK_rec n, hdelay_rec n]
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        cases n with
        | zero =>
            simp [hbFreeResponse, delay, α, hK_zero]
        | succ n =>
            cases n with
            | zero =>
                simp [hbFreeResponse, delay, α, hK_zero, hK_one]
            | succ n =>
                change
                  α • hbFreeResponse q a b u v (n + 1) -
                    b • hbFreeResponse q a b u v n =
                    K (n + 2) • v - b • (delay (n + 2) • u)
                rw [ih (n + 1) (by omega), ih n (by omega)]
                exact hstep n
  have hpoint (n : ℕ) :
      ‖hbFreeResponse q a b u v n‖ ^ 2 ≤
        (K n ^ 2 + b ^ 2 * delay n ^ 2) *
          (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
    rw [hrep n]
    have hnorm :
        ‖K n • v - b • (delay n • u)‖ ≤
          K n * ‖v‖ + b * delay n * ‖u‖ := by
      calc
        ‖K n • v - b • (delay n • u)‖ ≤
            ‖K n • v‖ + ‖b • (delay n • u)‖ := norm_sub_le _ _
        _ = K n * ‖v‖ + b * delay n * ‖u‖ := by
          rw [norm_smul, norm_smul, norm_smul]
          simp [abs_of_nonneg (hK_nonneg n), abs_of_nonneg hb_pos.le,
            abs_of_nonneg (hdelay_nonneg n)]
          ring
    have hright : 0 ≤ K n * ‖v‖ + b * delay n * ‖u‖ :=
      add_nonneg
        (mul_nonneg (hK_nonneg n) (norm_nonneg _))
        (mul_nonneg (mul_nonneg hb_pos.le (hdelay_nonneg n))
          (norm_nonneg _))
    have hnorm_sq :
        ‖K n • v - b • (delay n • u)‖ ^ 2 ≤
          (K n * ‖v‖ + b * delay n * ‖u‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hright).2 hnorm
    have hcs :
        (K n * ‖v‖ + b * delay n * ‖u‖) ^ 2 ≤
          (K n ^ 2 + b ^ 2 * delay n ^ 2) *
            (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
      nlinarith [sq_nonneg (K n * ‖u‖ - b * delay n * ‖v‖)]
    exact hnorm_sq.trans hcs
  have hmajor : Summable (fun n : ℕ =>
      (K n ^ 2 + b ^ 2 * delay n ^ 2) *
        (‖u‖ ^ 2 + ‖v‖ ^ 2)) := by
    have hcoef :
        Summable (fun n : ℕ => K n ^ 2 + b ^ 2 * delay n ^ 2) :=
      hKsq.add (Summable.mul_left (b ^ 2) hdelay_sq)
    exact Summable.mul_right (‖u‖ ^ 2 + ‖v‖ ^ 2) hcoef
  have henergy :
      hbSequenceEnergy (hbFreeResponse q a b u v) ≤
        (∑' n : ℕ, (K n ^ 2 + b ^ 2 * delay n ^ 2) *
          (‖u‖ ^ 2 + ‖v‖ ^ 2)) := by
    unfold hbSequenceEnergy at *
    exact he.tsum_le_tsum hpoint hmajor
  have henergy' :
      hbSequenceEnergy (hbFreeResponse q a b u v) ≤
        ((∑' n : ℕ, K n ^ 2) * (1 + b ^ 2)) *
          (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
    calc
      hbSequenceEnergy (hbFreeResponse q a b u v) ≤
          (∑' n : ℕ, (K n ^ 2 + b ^ 2 * delay n ^ 2) *
            (‖u‖ ^ 2 + ‖v‖ ^ 2)) := henergy
      _ = ((∑' n : ℕ, K n ^ 2) * (1 + b ^ 2)) *
            (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
          have hcoef :
              Summable (fun n : ℕ => K n ^ 2 + b ^ 2 * delay n ^ 2) :=
            hKsq.add (Summable.mul_left (b ^ 2) hdelay_sq)
          rw [hcoef.tsum_mul_right]
          rw [Summable.tsum_add hKsq
            (Summable.mul_left (b ^ 2) hdelay_sq)]
          rw [hdelay_sq.tsum_mul_left, hdelay_tsum]
          ring
  refine ⟨he, ?_⟩
  have hnonneg_init : 0 ≤ ‖u‖ ^ 2 + ‖v‖ ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_right (le_of_lt hcoef_lt) hnonneg_init
  nlinarith [henergy']

private theorem hb_centered_state_energy_eq_initial_add_twice_iterate_energy
    {q : ℝ} {d : ℕ} (hq : 0 < q) (a b : ℝ)
    (hf : AdmissibleObjective q d) (xMinusOne xZero : Vec d)
    (hx : hbSequenceInL2 (hbCenteredIterate hq a b hf xMinusOne xZero)) :
    Summable (fun t : ℕ =>
      centeredStateNormSq
        (hbCenteredStateAt hq a b hf xMinusOne xZero t)) ∧
      (∑' t : ℕ,
        centeredStateNormSq
          (hbCenteredStateAt hq a b hf xMinusOne xZero t)) =
        ‖xMinusOne - objectiveMinimizer hq hf‖ ^ 2 +
          2 * hbSequenceEnergy
            (hbCenteredIterate hq a b hf xMinusOne xZero) := by
  let x : ℕ → Vec d := hbCenteredIterate hq a b hf xMinusOne xZero
  let Y : ℕ → HBState d :=
    hbCenteredStateAt hq a b hf xMinusOne xZero
  have hstate :
      Summable (fun t : ℕ => centeredStateNormSq (Y t)) :=
    hb_centered_state_energy_summable_of_centered_iterate_l2
      hq a b hf xMinusOne xZero hx
  have hcurrent_x : Summable (fun t : ℕ => ‖x t‖ ^ 2) := by
    simpa [x] using hx
  have hcurrent :
      Summable (fun t : ℕ => ‖(Y t).2‖ ^ 2) := by
    apply Summable.congr hcurrent_x
    intro t
    simp [Y, x, hbCenteredIterate]
  have hprevious_succ (n : ℕ) :
      (Y (n + 1)).1 = x n := by
    dsimp [Y, x]
    rw [hbCenteredStateAt_succ]
    simp [hbCenteredMap, hbCenteredIterate]
  have hprevious_shift :
      Summable (fun n : ℕ => ‖(Y (n + 1)).1‖ ^ 2) := by
    apply Summable.congr hcurrent_x
    intro n
    rw [hprevious_succ]
  have hprevious :
      Summable (fun t : ℕ => ‖(Y t).1‖ ^ 2) :=
    (summable_nat_add_iff 1).1 hprevious_shift
  have hprevious_tsum :
      (∑' t : ℕ, ‖(Y t).1‖ ^ 2) =
        ‖xMinusOne - objectiveMinimizer hq hf‖ ^ 2 +
          ∑' n : ℕ, ‖(Y (n + 1)).1‖ ^ 2 := by
    have hsplit := hprevious.sum_add_tsum_nat_add 1
    calc
      (∑' t : ℕ, ‖(Y t).1‖ ^ 2) =
          (∑ t ∈ Finset.range 1, ‖(Y t).1‖ ^ 2) +
            ∑' n : ℕ, ‖(Y (n + 1)).1‖ ^ 2 := hsplit.symm
      _ = ‖xMinusOne - objectiveMinimizer hq hf‖ ^ 2 +
            ∑' n : ℕ, ‖(Y (n + 1)).1‖ ^ 2 := by
        simp [Y, hbCenteredStateAt_zero, hbInitialCenteredState]
  have hprevious_shift_tsum :
      (∑' n : ℕ, ‖(Y (n + 1)).1‖ ^ 2) =
        ∑' n : ℕ, ‖x n‖ ^ 2 := by
    apply tsum_congr
    intro n
    rw [hprevious_succ]
  have hcurrent_tsum :
      (∑' t : ℕ, ‖(Y t).2‖ ^ 2) =
        hbSequenceEnergy x := by
    simp only [hbSequenceEnergy]
    apply tsum_congr
    intro t
    simp [Y, x, hbCenteredIterate]
  have hsum :
      (∑' t : ℕ, centeredStateNormSq (Y t)) =
        ‖xMinusOne - objectiveMinimizer hq hf‖ ^ 2 +
          2 * hbSequenceEnergy x := by
    calc
      (∑' t : ℕ, centeredStateNormSq (Y t)) =
          (∑' t : ℕ, ‖(Y t).1‖ ^ 2) +
            (∑' t : ℕ, ‖(Y t).2‖ ^ 2) := by
              rw [show (fun t : ℕ => centeredStateNormSq (Y t)) =
                (fun t : ℕ => ‖(Y t).1‖ ^ 2 + ‖(Y t).2‖ ^ 2) by
                  funext t
                  rfl]
              exact Summable.tsum_add hprevious hcurrent
      _ = ‖xMinusOne - objectiveMinimizer hq hf‖ ^ 2 +
            2 * hbSequenceEnergy x := by
        rw [hprevious_tsum, hprevious_shift_tsum, hcurrent_tsum]
        unfold hbSequenceEnergy
        ring
  refine ⟨?_, ?_⟩
  · simpa [Y] using hstate
  · simpa [x, Y] using hsum

theorem HB_FREE_RESPONSE_TOTAL_ENERGY {q a b : ℝ} (hbox : HB_Box q a b)
    {d : ℕ} (hdim : 1 ≤ d) (hf : AdmissibleObjective q d)
    (Y : HBState d) :
    let hq := parameterDomain_q_pos (HB_box_subset_domain hbox)
    hbCenteredOrbitSummable hq a b hf Y ∧
      hbCenteredOrbitHasEnergy hq a b hf Y ∧
        hbCenteredEnergyInfinite hq a b hf Y ≤
          HB_D10_free_energy_constant * centeredStateNormSq Y ∧
          HB_D10_free_energy_constant * centeredStateNormSq Y ≤
            HB_C * centeredStateNormSq Y := by
  dsimp
  let hD := HB_box_subset_domain hbox
  let hq := parameterDomain_q_pos hD
  let xStar := objectiveMinimizer hq hf
  let u : Vec d := xStar + Y.1
  let v : Vec d := xStar + Y.2
  let e : ℕ → Vec d := hbFreeResponse q a b Y.1 Y.2
  let x : ℕ → Vec d := hbCenteredIterate hq a b hf u v
  have hinit : hbInitialCenteredState hq hf u v = Y := by
    ext <;>
      simp [hbInitialCenteredState, u, v, xStar, sub_eq_add_neg,
        add_assoc, add_left_comm, add_comm]
  have hfree := hb_free_response_energy_bound_of_box hbox Y.1 Y.2
  have hloop : hbHomotopyLoopEquation hq a b hf 1 e x := by
    simpa [e, x, u, v, xStar, hq, hD, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm] using
      hb_centered_iterate_homotopy_loop_equation hbox hdim hf u v
  have hcausal := HB_CAUSAL_CONTINUATION hbox
  have hexplicit := hcausal.2.2.2.2.2.2
  have hx_and_gain :=
    hexplicit.2.2 hdim hf 1 (by norm_num) (by norm_num)
      e x hfree.1 hloop
  have hx : hbSequenceInL2 x := hx_and_gain.1
  have hgain : hbSequenceL2Norm x ≤
      610000 * hbSequenceL2Norm e := hx_and_gain.2
  have henergy_x :
      hbSequenceEnergy x ≤
        (610000 : ℝ) ^ 2 * hbSequenceEnergy e := by
    have hsq :
        hbSequenceL2Norm x ^ 2 ≤
          (610000 * hbSequenceL2Norm e) ^ 2 := by
      have hright : 0 ≤ (610000 : ℝ) * hbSequenceL2Norm e :=
        mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
      exact
        (sq_le_sq₀ (Real.sqrt_nonneg _) hright).2 hgain
    have hx_sq :
        hbSequenceL2Norm x ^ 2 = hbSequenceEnergy x := by
      unfold hbSequenceL2Norm
      rw [Real.sq_sqrt]
      exact tsum_nonneg (fun n => sq_nonneg (‖x n‖))
    rw [hx_sq] at hsq
    have he_sq :
        hbSequenceL2Norm e ^ 2 = hbSequenceEnergy e := by
      unfold hbSequenceL2Norm
      rw [Real.sq_sqrt]
      exact tsum_nonneg (fun n => sq_nonneg (‖e n‖))
    have hmul_sq :
        (610000 * hbSequenceL2Norm e) ^ 2 =
          (610000 : ℝ) ^ 2 * hbSequenceL2Norm e ^ 2 := by
      ring
    rw [hmul_sq, he_sq] at hsq
    nlinarith
  have henergy_x_bound :
      hbSequenceEnergy x ≤
        (610000 : ℝ) ^ 2 * 100 * centeredStateNormSq Y := by
    calc
      hbSequenceEnergy x ≤
          (610000 : ℝ) ^ 2 * hbSequenceEnergy e := henergy_x
      _ ≤ (610000 : ℝ) ^ 2 * (100 * centeredStateNormSq Y) := by
        gcongr
        simpa [e, centeredStateNormSq] using hfree.2
      _ = (610000 : ℝ) ^ 2 * 100 * centeredStateNormSq Y := by
        ring
  have hstate :=
    hb_centered_state_energy_eq_initial_add_twice_iterate_energy
      hq a b hf u v hx
  have hstate_term (t : ℕ) :
      hbCenteredStateAt hq a b hf u v t =
        (hbCenteredMap hq a b hf)^[t] Y := by
    simp [hbCenteredStateAt, hinit]
  have hfirst_le :
      ‖u - xStar‖ ^ 2 ≤ centeredStateNormSq Y := by
    have htranslate :
        ‖u - xStar‖ ^ 2 + ‖v - xStar‖ ^ 2 =
          centeredStateNormSq Y := by
      simp [u, v, xStar, centeredStateNormSq, sub_eq_add_neg,
        add_assoc, add_left_comm, add_comm]
    nlinarith [sq_nonneg (‖v - xStar‖)]
  have hsum_eq :
      (∑' t : ℕ,
        centeredStateNormSq
          (hbCenteredStateAt hq a b hf u v t)) =
        hbCenteredEnergyInfinite hq a b hf Y := by
    unfold hbCenteredEnergyInfinite
    apply tsum_congr
    intro t
    rw [hstate_term]
  have henergy_upper :
      hbCenteredEnergyInfinite hq a b hf Y ≤
        HB_D10_free_energy_constant * centeredStateNormSq Y := by
    rw [← hsum_eq, hstate.2]
    dsimp [HB_D10_free_energy_constant]
    nlinarith
  have horbit_summable :
      hbCenteredOrbitSummable hq a b hf Y := by
    unfold hbCenteredOrbitSummable hbCenteredOrbitEnergyTerm
    apply Summable.congr hstate.1
    intro t
    rw [hstate_term]
  have horbit_has :
      hbCenteredOrbitHasEnergy hq a b hf Y := by
    have hterm :
        (fun t : ℕ => centeredStateNormSq
          ((hbCenteredMap hq a b hf)^[t] Y)) =
        (fun t : ℕ => centeredStateNormSq
          (hbCenteredStateAt hq a b hf u v t)) := by
      funext t
      rw [hstate_term]
    have hsum_orbit :
        (∑' t : ℕ, centeredStateNormSq
          ((hbCenteredMap hq a b hf)^[t] Y)) =
        ∑' t : ℕ, centeredStateNormSq
          (hbCenteredStateAt hq a b hf u v t) := by
      rw [hterm]
    unfold hbCenteredOrbitHasEnergy hbCenteredEnergyInfinite
      hbCenteredOrbitEnergyTerm
    rw [hsum_orbit, hterm]
    simpa using hstate.1.hasSum
  refine ⟨horbit_summable, horbit_has, henergy_upper, ?_⟩
  have hconst :
      HB_D10_free_energy_constant ≤ HB_C := by
    norm_num [HB_D10_free_energy_constant, HB_C]
  exact mul_le_mul_of_nonneg_right hconst (by
    dsimp [centeredStateNormSq]
    positivity)

private theorem hb_centered_energy_shift_identity {q a b : ℝ} {d : ℕ}
    (hq : 0 < q) (hf : AdmissibleObjective q d) (Y : HBState d)
    (hsum : hbCenteredOrbitSummable hq a b hf Y) :
    hbCenteredEnergyInfinite hq a b hf (hbCenteredMap hq a b hf Y) =
      hbCenteredEnergyInfinite hq a b hf Y - centeredStateNormSq Y := by
  let T := hbCenteredMap hq a b hf
  let term := hbCenteredOrbitEnergyTerm hq a b hf Y
  have hsum_term : Summable term := by
    simpa [hbCenteredOrbitSummable, term] using hsum
  have hshift_terms :
      ∀ j : ℕ,
        hbCenteredOrbitEnergyTerm hq a b hf (T Y) j = term (j + 1) := by
    intro j
    change centeredStateNormSq (T^[j] (T Y)) =
      centeredStateNormSq (T^[j + 1] Y)
    rw [← Function.iterate_succ_apply T j Y]
  have htail :
      (∑' j : ℕ, hbCenteredOrbitEnergyTerm hq a b hf (T Y) j) =
        ∑' j : ℕ, term (j + 1) := by
    exact tsum_congr hshift_terms
  have hfirst :
      (∑ j ∈ Finset.range 1, term j) = centeredStateNormSq Y := by
    simp [term, hbCenteredOrbitEnergyTerm_def, hbCenteredEnergy_iterate_zero]
  have hsplit := hsum_term.sum_add_tsum_nat_add 1
  have henergy :
      hbCenteredEnergyInfinite hq a b hf Y = ∑' j : ℕ, term j := by
    rfl
  have henergy_shift :
      hbCenteredEnergyInfinite hq a b hf (T Y) =
        ∑' j : ℕ, hbCenteredOrbitEnergyTerm hq a b hf (T Y) j := by
    rfl
  rw [henergy_shift, htail, henergy]
  nlinarith

private theorem hb_centered_tail_energy_eq_iterate_energy {q a b : ℝ} {d : ℕ}
    (hq : 0 < q) (hf : AdmissibleObjective q d) (N : ℕ) (Y : HBState d) :
    hbCenteredTailEnergy hq a b hf N Y =
      hbCenteredEnergyInfinite hq a b hf ((hbCenteredMap hq a b hf)^[N] Y) := by
  let T := hbCenteredMap hq a b hf
  unfold hbCenteredTailEnergy hbCenteredEnergyInfinite hbCenteredTailEnergyTerm
    hbCenteredOrbitEnergyTerm
  apply tsum_congr
  intro j
  congr 1
  change T^[j + N] Y = T^[j] (T^[N] Y)
  rw [Function.iterate_add_apply]

private theorem hb_centered_energy_contraction_step {q a b : ℝ} {d : ℕ}
    (hbox : HB_Box q a b) (hdim : 1 ≤ d) (hf : AdmissibleObjective q d)
    (Z : HBState d) :
    let hq := parameterDomain_q_pos (HB_box_subset_domain hbox)
    hbCenteredEnergyInfinite hq a b hf (hbCenteredMap hq a b hf Z) ≤
      HB_contraction * hbCenteredEnergyInfinite hq a b hf Z := by
  dsimp
  let hD := HB_FREE_RESPONSE_TOTAL_ENERGY hbox hdim hf Z
  dsimp at hD
  let hq := parameterDomain_q_pos (HB_box_subset_domain hbox)
  have hshift :=
    hb_centered_energy_shift_identity hq hf Z hD.1
  have hupper :
      hbCenteredEnergyInfinite hq a b hf Z ≤
        HB_C * centeredStateNormSq Z :=
    le_trans hD.2.2.1 hD.2.2.2
  have hCpos : 0 < HB_C := by
    norm_num [HB_C]
  have hCinv_nonneg : 0 ≤ HB_C⁻¹ := le_of_lt (inv_pos.mpr hCpos)
  have hscaled :
      HB_C⁻¹ * hbCenteredEnergyInfinite hq a b hf Z ≤
        centeredStateNormSq Z := by
    calc
      HB_C⁻¹ * hbCenteredEnergyInfinite hq a b hf Z ≤
          HB_C⁻¹ * (HB_C * centeredStateNormSq Z) :=
        mul_le_mul_of_nonneg_left hupper hCinv_nonneg
      _ = centeredStateNormSq Z := by
        field_simp [ne_of_gt hCpos]
  calc
    hbCenteredEnergyInfinite hq a b hf (hbCenteredMap hq a b hf Z) =
        hbCenteredEnergyInfinite hq a b hf Z - centeredStateNormSq Z := hshift
    _ ≤ hbCenteredEnergyInfinite hq a b hf Z -
          HB_C⁻¹ * hbCenteredEnergyInfinite hq a b hf Z := by
      linarith
    _ = HB_contraction * hbCenteredEnergyInfinite hq a b hf Z := by
      unfold HB_contraction
      ring

private theorem hb_centered_tail_geometric_bound {q a b : ℝ} {d : ℕ}
    (hbox : HB_Box q a b) (hdim : 1 ≤ d) (hf : AdmissibleObjective q d)
    (Y : HBState d) :
    let hq := parameterDomain_q_pos (HB_box_subset_domain hbox)
    ∀ N : ℕ,
      hbCenteredTailSummable hq a b hf N Y ∧
        hbCenteredTailHasEnergy hq a b hf N Y ∧
          hbCenteredTailEnergy hq a b hf N Y ≤
            HB_C * HB_contraction ^ N * centeredStateNormSq Y := by
  dsimp
  let hq := parameterDomain_q_pos (HB_box_subset_domain hbox)
  let T := hbCenteredMap hq a b hf
  let E := hbCenteredEnergyInfinite hq a b hf
  let term := hbCenteredOrbitEnergyTerm hq a b hf Y
  let hD0 := HB_FREE_RESPONSE_TOTAL_ENERGY hbox hdim hf Y
  dsimp at hD0
  have hE0 :
      E Y ≤ HB_C * centeredStateNormSq Y :=
    le_trans hD0.2.2.1 hD0.2.2.2
  have hcontract (Z : HBState d) :
      E (T Z) ≤ HB_contraction * E Z := by
    simpa [E, T] using
      (hb_centered_energy_contraction_step hbox hdim hf Z)
  have hcontraction_nonneg : 0 ≤ HB_contraction := by
    norm_num [HB_contraction, HB_C]
  have hpow_nonneg : ∀ N : ℕ, 0 ≤ HB_contraction ^ N := by
    intro N
    exact pow_nonneg hcontraction_nonneg N
  have hiterate_energy (N : ℕ) :
      E (T^[N] Y) ≤ HB_contraction ^ N * E Y := by
    induction N with
    | zero =>
        simp
    | succ N ih =>
        have hstep := hcontract (T^[N] Y)
        have hmul :
            HB_contraction * E (T^[N] Y) ≤
              HB_contraction * (HB_contraction ^ N * E Y) :=
          mul_le_mul_of_nonneg_left ih hcontraction_nonneg
        rw [show T^[N + 1] Y = T (T^[N] Y) by
          simpa [T] using hbCenteredEnergy_iterate_succ hq a b hf N Y]
        calc
          E (T (T^[N] Y)) ≤ HB_contraction * E (T^[N] Y) := hstep
          _ ≤ HB_contraction * (HB_contraction ^ N * E Y) := hmul
          _ = HB_contraction ^ (N + 1) * E Y := by
            rw [pow_succ]
            ring
  intro N
  let Z := T^[N] Y
  let hDN := HB_FREE_RESPONSE_TOTAL_ENERGY hbox hdim hf Z
  dsimp at hDN
  have htail_summable :
      hbCenteredTailSummable hq a b hf N Y := by
    unfold hbCenteredTailSummable hbCenteredTailEnergyTerm
    have hshift_summable :
        Summable (fun j : ℕ =>
          hbCenteredOrbitEnergyTerm hq a b hf Y (j + N)) :=
      (summable_nat_add_iff N).2 hD0.1
    exact hshift_summable
  have htail_has :
      hbCenteredTailHasEnergy hq a b hf N Y := by
    unfold hbCenteredTailHasEnergy
    rw [hb_centered_tail_energy_eq_iterate_energy hq hf N Y]
    unfold hbCenteredOrbitHasEnergy at hDN
    convert hDN.2.1 using 1
    funext j
    unfold hbCenteredTailEnergyTerm hbCenteredOrbitEnergyTerm
    rw [Function.iterate_add_apply]
  have htail_bound :
      hbCenteredTailEnergy hq a b hf N Y ≤
        HB_C * HB_contraction ^ N * centeredStateNormSq Y := by
    rw [hb_centered_tail_energy_eq_iterate_energy hq hf N Y]
    have hmul :
        HB_contraction ^ N * E Y ≤
          HB_contraction ^ N * (HB_C * centeredStateNormSq Y) :=
      mul_le_mul_of_nonneg_left hE0 (hpow_nonneg N)
    calc
      E Z ≤ HB_contraction ^ N * E Y := by
        simpa [Z] using hiterate_energy N
      _ ≤ HB_contraction ^ N * (HB_C * centeredStateNormSq Y) := hmul
      _ = HB_C * HB_contraction ^ N * centeredStateNormSq Y := by ring
  exact ⟨htail_summable, htail_has, htail_bound⟩

private theorem hb_centered_map_continuous {q a b : ℝ} {d : ℕ}
    (hq : 0 < q) (hf : AdmissibleObjective q d) :
    Continuous (hbCenteredMap hq a b hf) := by
  have hgradient :
      Continuous (gradient hf.f) := by
    apply
      (lipschitzWith_of_norm_sub_le_mul (gradient hf.f) 1 ?_).continuous
    intro x y
    simpa [dist_eq_norm] using hf.gradient_lipschitz y x
  have hsuccessor :
      Continuous (fun p : Vec d × Vec d =>
        hbSuccessor a b hf p.1 p.2) := by
    unfold hbSuccessor
    have h1 : Continuous (fun p : Vec d × Vec d => (1 + b) • p.2) :=
      continuous_const.smul continuous_snd
    have h2 : Continuous (fun p : Vec d × Vec d => b • p.1) :=
      continuous_const.smul continuous_fst
    have h3 : Continuous (fun p : Vec d × Vec d =>
        a • gradient hf.f p.2) :=
      continuous_const.smul (hgradient.comp continuous_snd)
    exact (h1.sub h2).sub h3
  let xStar := objectiveMinimizer hq hf
  have hfirst : Continuous (fun Y : HBState d => xStar + Y.1) :=
    continuous_const.add continuous_fst
  have hsecond : Continuous (fun Y : HBState d => xStar + Y.2) :=
    continuous_const.add continuous_snd
  unfold hbCenteredMap
  exact
    continuous_snd.prodMk
      ((hsuccessor.comp (hfirst.prodMk hsecond)).sub continuous_const)

private theorem hb_centered_energy_finite_add_tail {q a b : ℝ} {d : ℕ}
    (hq : 0 < q) (hf : AdmissibleObjective q d) (X : HBState d)
    (hsum : hbCenteredOrbitSummable hq a b hf X) (N : ℕ) :
    hbCenteredEnergyInfinite hq a b hf X =
      hbCenteredEnergyFinite hq a b hf N X +
        hbCenteredTailEnergy hq a b hf N X := by
  have hsplit :=
    hsum.sum_add_tsum_nat_add N
  simpa [hbCenteredOrbitSummable, hbCenteredEnergyInfinite,
    hbCenteredEnergyFinite, hbCenteredTailEnergy, hbCenteredTailEnergyTerm,
    hbCenteredOrbitEnergyTerm] using hsplit.symm

theorem HB_ENERGY_INFINITE_centered_energy {q a b : ℝ}
    (hbox : HB_Box q a b) {d : ℕ} (hdim : 1 ≤ d)
    (hf : AdmissibleObjective q d) (Y : HBState d) :
    let hq := parameterDomain_q_pos (HB_box_subset_domain hbox)
    hbCenteredOrbitSummable hq a b hf Y ∧
      hbCenteredOrbitHasEnergy hq a b hf Y ∧
        centeredStateNormSq Y ≤ hbCenteredEnergyInfinite hq a b hf Y ∧
          hbCenteredEnergyInfinite hq a b hf Y ≤ HB_C * centeredStateNormSq Y ∧
          hbCenteredEnergyInfinite hq a b hf (hbCenteredMap hq a b hf Y) =
            hbCenteredEnergyInfinite hq a b hf Y - centeredStateNormSq Y ∧
          hbCenteredEnergyInfinite hq a b hf (hbCenteredMap hq a b hf Y) ≤
            HB_contraction * hbCenteredEnergyInfinite hq a b hf Y ∧
          (∀ N : ℕ,
            hbCenteredTailSummable hq a b hf N Y ∧
              hbCenteredTailHasEnergy hq a b hf N Y ∧
                hbCenteredTailEnergy hq a b hf N Y ≤
                  HB_C * HB_contraction ^ N * centeredStateNormSq Y) ∧
          hbCenteredEnergyPartialSumsUniformOnBounded hq a b hf ∧
          Continuous (hbCenteredEnergyInfinite hq a b hf) := by
  dsimp
  let hq := parameterDomain_q_pos (HB_box_subset_domain hbox)
  let hD := HB_FREE_RESPONSE_TOTAL_ENERGY hbox hdim hf Y
  dsimp at hD
  have hupper :
      hbCenteredEnergyInfinite hq a b hf Y ≤ HB_C * centeredStateNormSq Y :=
    le_trans hD.2.2.1 hD.2.2.2
  have hlower :
      centeredStateNormSq Y ≤ hbCenteredEnergyInfinite hq a b hf Y := by
    unfold hbCenteredEnergyInfinite
    have hfirst := hD.1.sum_le_tsum (Finset.range 1)
      (fun j _ => by
        simp [hbCenteredOrbitEnergyTerm_def]
        unfold centeredStateNormSq
        positivity)
    simpa [hbCenteredEnergy_iterate_zero, hbCenteredOrbitEnergyTerm_def] using hfirst
  have hshift :=
    hb_centered_energy_shift_identity hq hf Y hD.1
  have hcontract :=
    hb_centered_energy_contraction_step hbox hdim hf Y
  have htail :=
    hb_centered_tail_geometric_bound hbox hdim hf Y
  have hrho_pos : 0 < HB_contraction := by
    norm_num [HB_contraction, HB_C]
  have hrho_lt : HB_contraction < 1 := by
    norm_num [HB_contraction, HB_C]
  have huniform :
      hbCenteredEnergyPartialSumsUniformOnBounded hq a b hf := by
    unfold hbCenteredEnergyPartialSumsUniformOnBounded
    intro R hR
    intro u hu
    rcases Metric.mem_uniformity_dist.mp hu with ⟨ε, hε, hsubset⟩
    have hgeom :
        Tendsto (fun N : ℕ => HB_C * HB_contraction ^ N * R)
          atTop (nhds (0 : ℝ)) := by
      have hp :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hrho_pos) hrho_lt).const_mul
          (HB_C * R)
      simpa [mul_assoc, mul_comm, mul_left_comm] using hp
    have hev :
        ∀ᶠ N : ℕ in atTop,
          HB_C * HB_contraction ^ N * R < ε := by
      have hIio : Set.Iio ε ∈ nhds (0 : ℝ) := Iio_mem_nhds hε
      simpa only [Set.mem_Iio] using hgeom.eventually hIio
    filter_upwards [hev] with N hN
    intro X hX
    apply hsubset
    rw [Real.dist_eq]
    have hDX := HB_FREE_RESPONSE_TOTAL_ENERGY hbox hdim hf X
    dsimp at hDX
    have hsplit :=
      hb_centered_energy_finite_add_tail hq hf X hDX.1 N
    have htailX :=
      (hb_centered_tail_geometric_bound hbox hdim hf X N).2.2
    have htail_nonneg :
        0 ≤ hbCenteredTailEnergy hq a b hf N X := by
      unfold hbCenteredTailEnergy
      apply tsum_nonneg
      intro j
      unfold hbCenteredTailEnergyTerm hbCenteredOrbitEnergyTerm
        centeredStateNormSq
      positivity
    have hdiff :
        hbCenteredEnergyInfinite hq a b hf X -
            hbCenteredEnergyFinite hq a b hf N X =
          hbCenteredTailEnergy hq a b hf N X := by
      linarith [hsplit]
    rw [hdiff, abs_of_nonneg htail_nonneg]
    calc
      hbCenteredTailEnergy hq a b hf N X ≤
          HB_C * HB_contraction ^ N * centeredStateNormSq X := htailX
      _ ≤ HB_C * HB_contraction ^ N * R := by
        have hcoef :
            0 ≤ HB_C * HB_contraction ^ N :=
          mul_nonneg (by norm_num [HB_C])
            (pow_nonneg (le_of_lt hrho_pos) N)
        exact mul_le_mul_of_nonneg_left hX hcoef
      _ < ε := hN
  have hcontinuous :
      Continuous (hbCenteredEnergyInfinite hq a b hf) := by
    let T := hbCenteredMap hq a b hf
    have hmap : Continuous T :=
      hb_centered_map_continuous hq hf
    have hnormsq : Continuous (centeredStateNormSq : HBState d → ℝ) := by
      unfold centeredStateNormSq
      exact (continuous_fst.norm.pow 2).add (continuous_snd.norm.pow 2)
    have hterm (n : ℕ) :
        Continuous (fun Z : HBState d =>
          centeredStateNormSq (T^[n] Z)) :=
      hnormsq.comp (hmap.iterate n)
    apply continuous_iff_continuousAt.mpr
    intro X
    let R : ℝ := centeredStateNormSq X + 1
    let S : Set (HBState d) :=
      {Z | centeredStateNormSq Z < R}
    have hR : 0 ≤ R := by
      dsimp [R]
      have : 0 ≤ centeredStateNormSq X := by
        unfold centeredStateNormSq
        positivity
      linarith
    have hXmem : X ∈ S := by
      dsimp [S, R]
      linarith
    have hcontOn :
        ContinuousOn
          (fun Z : HBState d => ∑' n : ℕ,
            centeredStateNormSq (T^[n] Z)) S := by
      apply continuousOn_tsum
        (u := fun n : ℕ => HB_C * HB_contraction ^ n * R) (s := S)
      · intro n
        exact (hterm n).continuousOn
      · simpa [mul_assoc, mul_comm, mul_left_comm] using
          (summable_geometric_of_lt_one
            (show 0 ≤ HB_contraction from le_of_lt hrho_pos) hrho_lt).mul_left
            (HB_C * R)
      · intro n Z hZ
        have htailZ :=
          hb_centered_tail_geometric_bound hbox hdim hf Z n
        have hterm_nonneg :
            0 ≤ centeredStateNormSq (T^[n] Z) := by
          unfold centeredStateNormSq
          positivity
        have hfirst :=
          htailZ.1.sum_le_tsum (Finset.range 1)
            (fun j _ => by
              unfold hbCenteredTailEnergyTerm hbCenteredOrbitEnergyTerm
                centeredStateNormSq
              positivity)
        have hterm_le_tail :
            centeredStateNormSq (T^[n] Z) ≤
              hbCenteredTailEnergy hq a b hf n Z := by
          simpa [hbCenteredTailEnergy, hbCenteredTailEnergyTerm,
            hbCenteredOrbitEnergyTerm, T] using hfirst
        have htail_bound := htailZ.2.2
        have hnorm :
            ‖centeredStateNormSq (T^[n] Z)‖ =
              centeredStateNormSq (T^[n] Z) := by
          rw [Real.norm_eq_abs, abs_of_nonneg hterm_nonneg]
        calc
          ‖centeredStateNormSq (T^[n] Z)‖ =
              centeredStateNormSq (T^[n] Z) := hnorm
          _ ≤ hbCenteredTailEnergy hq a b hf n Z := hterm_le_tail
          _ ≤ HB_C * HB_contraction ^ n *
                centeredStateNormSq Z := htail_bound
          _ ≤ HB_C * HB_contraction ^ n * R := by
            have hcoef :
                0 ≤ HB_C * HB_contraction ^ n :=
              mul_nonneg (by norm_num [HB_C])
                (pow_nonneg (le_of_lt hrho_pos) n)
            have hZR : centeredStateNormSq Z ≤ R := le_of_lt hZ
            exact mul_le_mul_of_nonneg_left hZR hcoef
    have hopen : IsOpen S := by
      dsimp [S]
      exact isOpen_lt hnormsq continuous_const
    have hlocal := hcontOn.continuousAt (hopen.mem_nhds hXmem)
    simpa [hbCenteredEnergyInfinite, T] using hlocal
  exact ⟨hD.1, hD.2.1, hlower, hupper, hshift, hcontract, htail,
    huniform, hcontinuous⟩

private theorem hb_centered_energy_finite_shift_telescope {q a b : ℝ} {d : ℕ}
    (hq : 0 < q) (hf : AdmissibleObjective q d) (N : ℕ) (Y : HBState d) :
    hbCenteredEnergyFinite hq a b hf N (hbCenteredMap hq a b hf Y) -
        hbCenteredEnergyFinite hq a b hf N Y =
      centeredStateNormSq ((hbCenteredMap hq a b hf)^[N] Y) -
        centeredStateNormSq Y := by
  let T := hbCenteredMap hq a b hf
  let A : ℕ → ℝ := fun k => centeredStateNormSq (T^[k] Y)
  have hsucc (k : ℕ) :
      A (k + 1) = centeredStateNormSq (T (T^[k] Y)) := by
    change centeredStateNormSq (T^[k + 1] Y) =
      centeredStateNormSq (T (T^[k] Y))
    exact congrArg centeredStateNormSq
      (by
        simpa [T, Nat.succ_eq_add_one] using
          hbCenteredEnergy_iterate_succ hq a b hf k Y)
  have hiter (k : ℕ) :
      centeredStateNormSq (T^[k] (T Y)) = A (k + 1) := by
    calc
      centeredStateNormSq (T^[k] (T Y)) =
          centeredStateNormSq (T^[k + 1] Y) := by
            rw [← Function.iterate_succ_apply T k Y]
      _ = centeredStateNormSq (T (T^[k] Y)) := by
        rw [show T^[k + 1] Y = T (T^[k] Y) by
          simpa [T, Nat.succ_eq_add_one] using
            hbCenteredEnergy_iterate_succ hq a b hf k Y]
      _ = A (k + 1) := (hsucc k).symm
  unfold hbCenteredEnergyFinite
  have hsum_shift :
      (∑ k ∈ Finset.range N, centeredStateNormSq (T^[k] (T Y))) =
        ∑ k ∈ Finset.range N, A (k + 1) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hiter k
  have hsum_original :
      (∑ k ∈ Finset.range N, centeredStateNormSq (T^[k] Y)) =
        ∑ k ∈ Finset.range N, A k := by
    rfl
  rw [hsum_shift, hsum_original]
  calc
    (∑ k ∈ Finset.range N, A (k + 1)) -
        ∑ k ∈ Finset.range N, A k =
        ∑ k ∈ Finset.range N, (A (k + 1) - A k) := by
          rw [Finset.sum_sub_distrib]
    _ = -∑ k ∈ Finset.range N, (A k - A (k + 1)) := by
      calc
        ∑ k ∈ Finset.range N, (A (k + 1) - A k) =
            ∑ k ∈ Finset.range N, (-(A k - A (k + 1))) := by
              apply Finset.sum_congr rfl
              intro k hk
              ring
        _ = -∑ k ∈ Finset.range N, (A k - A (k + 1)) := by
          rw [Finset.sum_neg_distrib]
    _ = -(A 0 - A N) := by
      rw [Finset.sum_range_sub' A N]
    _ = A N - A 0 := by ring

private theorem hb_contraction_horizon_half :
    HB_C * HB_contraction ^ HB_N ≤ (1 / 2 : ℝ) := by
  let Cnat : ℕ := 10 ^ 14
  have hCcast : (Cnat : ℝ) = HB_C := by
    change ((10 ^ 14 : ℕ) : ℝ) = (10 : ℝ) ^ 14
    rw [Nat.cast_pow]
    norm_num
  have hN : HB_N = Cnat * 48 := by
    norm_num [HB_N, Cnat]
  have hCpos : 0 < HB_C := by
    rw [← hCcast]
    norm_num
  have hCgt : 1 < HB_C := by
    rw [← hCcast]
    norm_num
  have hspos : 0 < HB_C / (HB_C - 1) := by
    exact div_pos hCpos (sub_pos.mpr hCgt)
  have hrho_pos : 0 < HB_contraction := by
    unfold HB_contraction
    linarith [(inv_lt_one₀ hCpos).2 hCgt]
  have hdenpos : 0 < HB_C - 1 := sub_pos.mpr hCgt
  have hratio_sub :
      HB_C / (HB_C - 1) - 1 = 1 / (HB_C - 1) := by
    field_simp [ne_of_gt hdenpos]
    ring
  have hbern :
      1 + (Cnat : ℝ) * (HB_C / (HB_C - 1) - 1) ≤
        (HB_C / (HB_C - 1)) ^ Cnat := by
    exact one_add_mul_sub_le_pow (a := HB_C / (HB_C - 1))
      (by linarith [hspos.le]) Cnat
  have htwo :
      (2 : ℝ) ≤ (HB_C / (HB_C - 1)) ^ Cnat := by
    have hlinear :
        (2 : ℝ) ≤ 1 + (Cnat : ℝ) * (HB_C / (HB_C - 1) - 1) := by
      rw [hCcast]
      norm_num [HB_C]
    exact hlinear.trans hbern
  have hhalf_base :
      HB_contraction ^ Cnat ≤ (1 / 2 : ℝ) := by
    have hcontract_eq :
        HB_contraction = (HB_C / (HB_C - 1))⁻¹ := by
      unfold HB_contraction
      field_simp [ne_of_gt hCpos, ne_of_gt hdenpos]
    rw [hcontract_eq, inv_pow]
    have hinv :=
      (inv_le_inv₀ (pow_pos hspos Cnat) (by norm_num : (0 : ℝ) < 2)).2 htwo
    simpa [one_div] using hinv
  have hpow :
      HB_contraction ^ HB_N ≤ (1 / 2 : ℝ) ^ 48 := by
    rw [hN, pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg hrho_pos.le Cnat) hhalf_base 48
  have hscaled :
      HB_C * HB_contraction ^ HB_N ≤ HB_C * (1 / 2 : ℝ) ^ 48 :=
    mul_le_mul_of_nonneg_left hpow hCpos.le
  calc
    HB_C * HB_contraction ^ HB_N ≤ HB_C * (1 / 2 : ℝ) ^ 48 := hscaled
    _ ≤ (1 / 2 : ℝ) := by
      norm_num [HB_C]

theorem HB_ENERGY_FINITE_centered_energy {q a b : ℝ}
    (hbox : HB_Box q a b) {d : ℕ} (hdim : 1 ≤ d)
    (hf : AdmissibleObjective q d) (Y : HBState d) :
    let hq := parameterDomain_q_pos (HB_box_subset_domain hbox)
    centeredStateNormSq Y ≤ hbCenteredEnergyFinite hq a b hf HB_N Y ∧
      hbCenteredEnergyFinite hq a b hf HB_N Y ≤ HB_C * centeredStateNormSq Y ∧
      hbCenteredEnergyFinite hq a b hf HB_N (hbCenteredMap hq a b hf Y) -
          hbCenteredEnergyFinite hq a b hf HB_N Y ≤
        -(1 / 2 : ℝ) * centeredStateNormSq Y ∧
      hbCenteredEnergyFinite hq a b hf HB_N (hbCenteredMap hq a b hf Y) ≤
        (1 - (2 * HB_C)⁻¹) * hbCenteredEnergyFinite hq a b hf HB_N Y ∧
      Continuous (hbCenteredEnergyFinite hq a b hf HB_N) := by
  dsimp
  let hq := parameterDomain_q_pos (HB_box_subset_domain hbox)
  let T := hbCenteredMap hq a b hf
  have hD := HB_FREE_RESPONSE_TOTAL_ENERGY hbox hdim hf Y
  dsimp at hD
  have hfinite_lower :
      centeredStateNormSq Y ≤ hbCenteredEnergyFinite hq a b hf HB_N Y := by
    unfold hbCenteredEnergyFinite
    have hNpos : 1 ≤ HB_N := by
      norm_num [HB_N]
    have hsubset : Finset.range 1 ⊆ Finset.range HB_N := by
      intro j hj
      exact Finset.mem_range.mpr
        (Nat.lt_of_lt_of_le (Finset.mem_range.mp hj) hNpos)
    have hnonneg :
        ∀ j ∈ Finset.range HB_N, j ∉ Finset.range 1 →
          0 ≤ centeredStateNormSq ((hbCenteredMap hq a b hf)^[j] Y) := by
      intro j hj hnot
      unfold centeredStateNormSq
      positivity
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
    have hfirst :
        centeredStateNormSq Y ≤
          ∑ j ∈ Finset.range 1,
            centeredStateNormSq ((hbCenteredMap hq a b hf)^[j] Y) := by
      simpa [hbCenteredEnergy_iterate_zero]
    exact hfirst.trans hsum
  have hfinite_upper :
      hbCenteredEnergyFinite hq a b hf HB_N Y ≤
        HB_C * centeredStateNormSq Y := by
    have hpartial :
        hbCenteredEnergyFinite hq a b hf HB_N Y ≤
          hbCenteredEnergyInfinite hq a b hf Y := by
      unfold hbCenteredEnergyFinite hbCenteredEnergyInfinite
      apply hD.1.sum_le_tsum
      intro j hj
      unfold hbCenteredOrbitEnergyTerm centeredStateNormSq
      exact add_nonneg (sq_nonneg _) (sq_nonneg _)
    exact hpartial.trans (le_trans hD.2.2.1 hD.2.2.2)
  have htail := hb_centered_tail_geometric_bound hbox hdim hf Y
  have htail_term :
      centeredStateNormSq (T^[HB_N] Y) ≤
        hbCenteredTailEnergy hq a b hf HB_N Y := by
    have hfirst := (htail HB_N).1.sum_le_tsum (Finset.range 1)
      (fun j _ => by
        unfold hbCenteredTailEnergyTerm hbCenteredOrbitEnergyTerm
          centeredStateNormSq
        exact add_nonneg (sq_nonneg _) (sq_nonneg _))
    simpa [T, hbCenteredTailEnergy, hbCenteredTailEnergyTerm,
      hbCenteredOrbitEnergyTerm] using hfirst
  have hnormY : 0 ≤ centeredStateNormSq Y := by
    unfold centeredStateNormSq
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hterminal :
      centeredStateNormSq (T^[HB_N] Y) ≤
        (1 / 2 : ℝ) * centeredStateNormSq Y := by
    calc
      centeredStateNormSq (T^[HB_N] Y) ≤
          hbCenteredTailEnergy hq a b hf HB_N Y := htail_term
      _ ≤ HB_C * HB_contraction ^ HB_N * centeredStateNormSq Y :=
        (htail HB_N).2.2
      _ ≤ (1 / 2 : ℝ) * centeredStateNormSq Y := by
        exact mul_le_mul_of_nonneg_right
          hb_contraction_horizon_half hnormY
  have htel :=
    hb_centered_energy_finite_shift_telescope (a := a) (b := b) hq hf HB_N Y
  have hdecrease :
      hbCenteredEnergyFinite hq a b hf HB_N (T Y) -
          hbCenteredEnergyFinite hq a b hf HB_N Y ≤
        -(1 / 2 : ℝ) * centeredStateNormSq Y := by
    calc
      hbCenteredEnergyFinite hq a b hf HB_N (T Y) -
          hbCenteredEnergyFinite hq a b hf HB_N Y =
          centeredStateNormSq (T^[HB_N] Y) -
            centeredStateNormSq Y := by
              simpa [T] using htel
      _ ≤ (1 / 2 : ℝ) * centeredStateNormSq Y -
            centeredStateNormSq Y :=
        sub_le_sub_right hterminal _
      _ = -(1 / 2 : ℝ) * centeredStateNormSq Y := by ring
  have hCpos : 0 < HB_C := by
    norm_num [HB_C]
  have h2Cpos : 0 < 2 * HB_C := mul_pos (by norm_num) hCpos
  have hscaled :
      (2 * HB_C)⁻¹ * hbCenteredEnergyFinite hq a b hf HB_N Y ≤
        (1 / 2 : ℝ) * centeredStateNormSq Y := by
    calc
      (2 * HB_C)⁻¹ * hbCenteredEnergyFinite hq a b hf HB_N Y ≤
          (2 * HB_C)⁻¹ * (HB_C * centeredStateNormSq Y) :=
        mul_le_mul_of_nonneg_left hfinite_upper
          (le_of_lt (inv_pos.mpr h2Cpos))
      _ = (1 / 2 : ℝ) * centeredStateNormSq Y := by
        field_simp [ne_of_gt hCpos]
  have hcontract :
      hbCenteredEnergyFinite hq a b hf HB_N (T Y) ≤
        (1 - (2 * HB_C)⁻¹) *
          hbCenteredEnergyFinite hq a b hf HB_N Y := by
    have hdecrease' :
        hbCenteredEnergyFinite hq a b hf HB_N (T Y) ≤
          hbCenteredEnergyFinite hq a b hf HB_N Y -
            (1 / 2 : ℝ) * centeredStateNormSq Y := by
      linarith [hdecrease]
    calc
      hbCenteredEnergyFinite hq a b hf HB_N (T Y) ≤
          hbCenteredEnergyFinite hq a b hf HB_N Y -
            (1 / 2 : ℝ) * centeredStateNormSq Y := hdecrease'
      _ ≤ hbCenteredEnergyFinite hq a b hf HB_N Y -
            (2 * HB_C)⁻¹ *
              hbCenteredEnergyFinite hq a b hf HB_N Y := by
        linarith [hscaled]
      _ = (1 - (2 * HB_C)⁻¹) *
            hbCenteredEnergyFinite hq a b hf HB_N Y := by ring
  have hcontinuous :
      Continuous (hbCenteredEnergyFinite hq a b hf HB_N) := by
    have hmap : Continuous T :=
      hb_centered_map_continuous hq hf
    have hnormsq : Continuous (centeredStateNormSq : HBState d → ℝ) := by
      unfold centeredStateNormSq
      exact (continuous_fst.norm.pow 2).add (continuous_snd.norm.pow 2)
    unfold hbCenteredEnergyFinite
    exact continuous_finset_sum (Finset.range HB_N) (fun k hk =>
      hnormsq.comp (hmap.iterate k))
  exact ⟨hfinite_lower, hfinite_upper, hdecrease, hcontract, hcontinuous⟩

theorem HB_finite_energy_objective_gap_certificate {q a b : ℝ}
    (hbox : HB_Box q a b) {d : ℕ} (hdim : 1 ≤ d)
    (hf : AdmissibleObjective q d) (u v : Vec d) :
    let hq := parameterDomain_q_pos (HB_box_subset_domain hbox)
    let xStar := objectiveMinimizer hq hf
    let Y : HBState d := (u - xStar, v - xStar)
    let w := hbSuccessor a b hf u v
    hf.f w - objectiveMinimum hq hf ≤
        hbCenteredEnergyFinite hq a b hf HB_N (hbCenteredMap hq a b hf Y) ∧
      hbCenteredEnergyFinite hq a b hf HB_N (hbCenteredMap hq a b hf Y) ≤
        hbCenteredEnergyFinite hq a b hf HB_N Y := by
  dsimp
  let hq := parameterDomain_q_pos (HB_box_subset_domain hbox)
  let xStar := objectiveMinimizer hq hf
  let Y : HBState d := (u - xStar, v - xStar)
  let w := hbSuccessor a b hf u v
  have hbridge :
      hbCenteredMap hq a b hf Y = (v - xStar, w - xStar) := by
    simp [Y, w, hbCenteredMap, hbSuccessor, xStar, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm]
  have hsmooth_carrier :=
    Convex.carrier_smooth_quadratic_upper_bound_of_hasGradientWithinAt_lipschitz
      (X := Set.univ)
      (f := fun z : {x : Vec d // x ∈ Set.univ} => hf.f z.1)
      (F := hf.f)
      (grad := fun z : {x : Vec d // x ∈ Set.univ} => gradient hf.f z.1)
      (L := (1 : ℝ))
      (convex_univ)
      (by intro z hz; rfl)
      (by
        intro z
        simpa [hasGradientWithinAt_univ] using
          (HB_admissible_objective_hasGradientAt hf z.1))
      (by
        intro x y
        simpa [one_mul] using hf.gradient_lipschitz x.1 y.1)
      ⟨w, by simp⟩ ⟨xStar, by simp⟩
  have hsmooth_gap :
      hf.f w - hf.f xStar - inner ℝ (gradient hf.f xStar) (w - xStar) ≤
        (1 / 2 : ℝ) * ‖w - xStar‖ ^ 2 := by
    simpa using hsmooth_carrier
  have hzero : gradient hf.f xStar = 0 := by
    simpa [xStar] using (gradient_objectiveMinimizer_eq_zero hq hf)
  have hgap :
      hf.f w - objectiveMinimum hq hf ≤ (1 / 2 : ℝ) * ‖w - xStar‖ ^ 2 := by
    simpa [objectiveMinimum, hzero] using hsmooth_gap
  have hgap_norm :
      hf.f w - objectiveMinimum hq hf ≤
        centeredStateNormSq (hbCenteredMap hq a b hf Y) := by
    rw [hbridge]
    unfold centeredStateNormSq
    calc
      hf.f w - objectiveMinimum hq hf ≤
          (1 / 2 : ℝ) * ‖w - xStar‖ ^ 2 := hgap
      _ ≤ ‖v - xStar‖ ^ 2 + ‖w - xStar‖ ^ 2 := by
        nlinarith [sq_nonneg (‖v - xStar‖)]
  have hfiniteY :=
    HB_ENERGY_FINITE_centered_energy hbox hdim hf Y
  have hfiniteZ :=
    HB_ENERGY_FINITE_centered_energy hbox hdim hf
      (hbCenteredMap hq a b hf Y)
  dsimp at hfiniteY hfiniteZ
  have hstateY : 0 ≤ centeredStateNormSq Y := by
    unfold centeredStateNormSq
    positivity
  have henergyY :
      0 ≤ hbCenteredEnergyFinite hq a b hf HB_N Y :=
    le_trans hstateY hfiniteY.1
  have hCpos : 0 < HB_C := by
    norm_num [HB_C]
  have hinv_nonneg : 0 ≤ (2 * HB_C)⁻¹ := by
    exact le_of_lt (inv_pos.mpr (mul_pos (by norm_num) hCpos))
  have hmonotone :
      hbCenteredEnergyFinite hq a b hf HB_N
          (hbCenteredMap hq a b hf Y) ≤
        hbCenteredEnergyFinite hq a b hf HB_N Y := by
    have hcontract := hfiniteY.2.2.2
    nlinarith
  exact ⟨hgap_norm.trans hfiniteZ.1, hmonotone⟩

theorem HB_B_uniform_linear_convergence {q a b : ℝ}
    (hbox : HB_Box q a b) {d : ℕ} (hdim : 1 ≤ d)
    (hf : AdmissibleObjective q d) (xMinusOne xZero : Vec d) (t : ℕ) :
    let hq := parameterDomain_q_pos (HB_box_subset_domain hbox)
    ‖hbIterate a b hf xMinusOne xZero t - objectiveMinimizer hq hf‖ ≤
      (10 : ℝ) ^ (7 : ℕ) * Real.sqrt (HB_contraction ^ t) *
        Real.sqrt
          (‖xMinusOne - objectiveMinimizer hq hf‖ ^ 2 +
            ‖xZero - objectiveMinimizer hq hf‖ ^ 2) := by
  dsimp
  let hq := parameterDomain_q_pos (HB_box_subset_domain hbox)
  let Y := hbInitialCenteredState hq hf xMinusOne xZero
  let T := hbCenteredMap hq a b hf
  change ‖hbIterate a b hf xMinusOne xZero t - objectiveMinimizer hq hf‖ ≤
    (10 : ℝ) ^ (7 : ℕ) * Real.sqrt (HB_contraction ^ t) *
      Real.sqrt
        (‖xMinusOne - objectiveMinimizer hq hf‖ ^ 2 +
          ‖xZero - objectiveMinimizer hq hf‖ ^ 2)
  have hcontraction_nonneg : 0 ≤ HB_contraction := by
    norm_num [HB_contraction, HB_C]
  have hpow_nonneg : ∀ n : ℕ, 0 ≤ HB_contraction ^ n := by
    intro n
    exact pow_nonneg hcontraction_nonneg n
  have henergyY := HB_ENERGY_INFINITE_centered_energy hbox hdim hf Y
  dsimp at henergyY
  have hinitial_upper :
      hbCenteredEnergyInfinite hq a b hf Y ≤
        HB_C * centeredStateNormSq Y :=
    henergyY.2.2.2.1
  have hiterate_energy (n : ℕ) :
      hbCenteredEnergyInfinite hq a b hf (T^[n] Y) ≤
        HB_contraction ^ n *
          hbCenteredEnergyInfinite hq a b hf Y := by
    induction n with
    | zero =>
        simp
    | succ n ih =>
        have hstep :
            hbCenteredEnergyInfinite hq a b hf (T (T^[n] Y)) ≤
              HB_contraction *
                hbCenteredEnergyInfinite hq a b hf (T^[n] Y) := by
          simpa [T, hq] using
            (hb_centered_energy_contraction_step hbox hdim hf (T^[n] Y))
        have hmul :
            HB_contraction *
                hbCenteredEnergyInfinite hq a b hf (T^[n] Y) ≤
              HB_contraction *
                (HB_contraction ^ n *
                  hbCenteredEnergyInfinite hq a b hf Y) :=
          mul_le_mul_of_nonneg_left ih hcontraction_nonneg
        rw [show T^[n + 1] Y = T (T^[n] Y) by
          simpa [T] using hbCenteredEnergy_iterate_succ hq a b hf n Y]
        calc
          hbCenteredEnergyInfinite hq a b hf (T (T^[n] Y)) ≤
              HB_contraction *
                hbCenteredEnergyInfinite hq a b hf (T^[n] Y) := hstep
          _ ≤ HB_contraction *
                (HB_contraction ^ n *
                  hbCenteredEnergyInfinite hq a b hf Y) := hmul
          _ = HB_contraction ^ (n + 1) *
                hbCenteredEnergyInfinite hq a b hf Y := by
            rw [pow_succ]
            ring
  have henergy_geometric :
      hbCenteredEnergyInfinite hq a b hf (T^[t] Y) ≤
        HB_C * HB_contraction ^ t * centeredStateNormSq Y := by
    calc
      hbCenteredEnergyInfinite hq a b hf (T^[t] Y) ≤
          HB_contraction ^ t *
            hbCenteredEnergyInfinite hq a b hf Y :=
        hiterate_energy t
      _ ≤ HB_contraction ^ t *
            (HB_C * centeredStateNormSq Y) :=
        mul_le_mul_of_nonneg_left hinitial_upper (hpow_nonneg t)
      _ = HB_C * HB_contraction ^ t * centeredStateNormSq Y := by
        ring
  have henergyT :=
    HB_ENERGY_INFINITE_centered_energy hbox hdim hf (T^[t] Y)
  dsimp at henergyT
  have hpair_bound :
      centeredStateNormSq (T^[t] Y) ≤
        HB_C * HB_contraction ^ t * centeredStateNormSq Y :=
    (henergyT.2.2.1).trans henergy_geometric
  have hsecond_bound :
      ‖(T^[t] Y).2‖ ^ 2 ≤
        HB_C * HB_contraction ^ t * centeredStateNormSq Y := by
    have hpair_bound' := hpair_bound
    change ‖(T^[t] Y).1‖ ^ 2 + ‖(T^[t] Y).2‖ ^ 2 ≤
      HB_C * HB_contraction ^ t * centeredStateNormSq Y at hpair_bound'
    nlinarith [sq_nonneg ‖(T^[t] Y).1‖]
  have hstate :
      T^[t] Y =
        ((hbStateAt a b hf xMinusOne xZero t).1 -
            objectiveMinimizer hq hf,
          (hbStateAt a b hf xMinusOne xZero t).2 -
            objectiveMinimizer hq hf) := by
    simpa [T, Y, hbCenteredStateAt] using
      (hbCenteredStateAt_eq_centered_hbStateAt
        hq a b hf xMinusOne xZero t)
  have hsecond :
      (T^[t] Y).2 =
        hbIterate a b hf xMinusOne xZero t -
          objectiveMinimizer hq hf := by
    have h := congrArg (fun Z : HBState d => Z.2) hstate
    simpa [hbIterate] using h
  let S : ℝ :=
    ‖xMinusOne - objectiveMinimizer hq hf‖ ^ 2 +
      ‖xZero - objectiveMinimizer hq hf‖ ^ 2
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    positivity
  have hYnorm : centeredStateNormSq Y = S := by
    dsimp [Y]
    simp [hbInitialCenteredState, S, centeredStateNormSq]
  have hsq :
      ‖hbIterate a b hf xMinusOne xZero t -
          objectiveMinimizer hq hf‖ ^ 2 ≤
        HB_C * HB_contraction ^ t * S := by
    rw [← hsecond]
    simpa [hYnorm] using hsecond_bound
  have hright_nonneg :
      0 ≤ (10 : ℝ) ^ (7 : ℕ) * Real.sqrt (HB_contraction ^ t) *
        Real.sqrt S := by
    positivity
  have hright_sq :
      ((10 : ℝ) ^ (7 : ℕ) * Real.sqrt (HB_contraction ^ t) *
          Real.sqrt S) ^ 2 =
        HB_C * HB_contraction ^ t * S := by
    calc
      ((10 : ℝ) ^ (7 : ℕ) * Real.sqrt (HB_contraction ^ t) *
          Real.sqrt S) ^ 2 =
          ((10 : ℝ) ^ (7 : ℕ)) ^ 2 *
            (Real.sqrt (HB_contraction ^ t)) ^ 2 *
              (Real.sqrt S) ^ 2 := by ring
      _ = HB_C * HB_contraction ^ t * S := by
        rw [Real.sq_sqrt (hpow_nonneg t), Real.sq_sqrt hS_nonneg]
        norm_num [HB_C]
  have hsq' :
      ‖hbIterate a b hf xMinusOne xZero t -
          objectiveMinimizer hq hf‖ ^ 2 ≤
        ((10 : ℝ) ^ (7 : ℕ) * Real.sqrt (HB_contraction ^ t) *
          Real.sqrt S) ^ 2 := by
    rw [hright_sq]
    exact hsq
  have hfinal :=
    (sq_le_sq₀
      (norm_nonneg (hbIterate a b hf xMinusOne xZero t -
        objectiveMinimizer hq hf))
      hright_nonneg).mp hsq'
  simpa [S] using hfinal

theorem HB_A_exact_separation :
    ¬ HB_L qStar aStar bStar ∧ ¬ HB_Cycle qStar aStar bStar := by
  constructor
  · rintro ⟨hD, cert, hworks⟩
    obtain ⟨hR, hRgt, hFpos, hz0, hEta, hxstar, hgstar, hFstar, hres,
      hrealizable, hupdate, hF01, hF12, hF0, hmatrix, hx01, hx12, hg01, hg12⟩ :=
      HB_RATIONAL_WITNESS_exact_data
    obtain ⟨hf, hreal⟩ := hrealizable
    have hfzero : hf.f (0 : Vec 2) = 0 := by
      calc
        hf.f (0 : Vec 2) = hf.f (hbRationalWitnessData.x RecordIndex.star) := by
          rw [hxstar]
        _ = hbRationalWitnessData.F RecordIndex.star := (hreal RecordIndex.star).1
        _ = 0 := hFstar
    have hgzero : gradient hf.f (0 : Vec 2) = 0 := by
      calc
        gradient hf.f (0 : Vec 2) =
            gradient hf.f (hbRationalWitnessData.x RecordIndex.star) := by
          rw [hxstar]
        _ = hbRationalWitnessData.g RecordIndex.star := (hreal RecordIndex.star).2
        _ = 0 := hgstar
    have hglobal : ∀ y : Vec 2, hf.f (0 : Vec 2) ≤ hf.f y := by
      intro y
      have hstrong := hf.strongConvex_lower (0 : Vec 2) y
      rw [hfzero, hgzero] at hstrong
      simp at hstrong
      have hqhalf : 0 ≤ qStar / 2 := by
        norm_num [qStar]
      have hnonneg :
          0 ≤ (qStar / 2 : ℝ) * ‖y - (0 : Vec 2)‖ ^ 2 := by
        exact mul_nonneg hqhalf (sq_nonneg _)
      nlinarith
    have hmin :
        objectiveMinimizer (parameterDomain_q_pos HB_central_parameters_in_domain) hf = 0 := by
      exact
        (objectiveMinimizer_unique
          (parameterDomain_q_pos HB_central_parameters_in_domain) hf hglobal).symm
    have hqeq :
        parameterDomain_q_pos hD =
          parameterDomain_q_pos HB_central_parameters_in_domain :=
      Subsingleton.elim _ _
    have hsuccessor :
        hbSuccessor aStar bStar hf
            (hbRationalWitnessData.x RecordIndex.zero)
            (hbRationalWitnessData.x RecordIndex.one) =
          hbRationalWitnessData.x RecordIndex.two := by
      unfold hbSuccessor
      rw [(hreal RecordIndex.one).2]
      exact hupdate.symm
    have hcert := hworks 2 (by norm_num) hf
      (hbRationalWitnessData.x RecordIndex.zero)
      (hbRationalWitnessData.x RecordIndex.one)
    dsimp at hcert
    rw [hqeq, hsuccessor] at hcert
    have hscale := HB_RATIONAL_WITNESS_certificate_scale hf hreal hmin cert
    have hgap := rational_witness_objective_gap_scale hf hreal hmin
    have hminval :
        objectiveMinimum (parameterDomain_q_pos HB_central_parameters_in_domain) hf = 0 := by
      simp [objectiveMinimum, hmin, hfzero]
    have hbase :
        0 < hf.f (hbRationalWitnessData.x RecordIndex.zero) -
          objectiveMinimum (parameterDomain_q_pos HB_central_parameters_in_domain) hf := by
      rw [(hreal RecordIndex.zero).1, hminval]
      simpa using hF0
    have hRpos : 0 < hbWitnessR := by
      linarith [hRgt]
    have hV1pos :
        0 < hf.f (hbRationalWitnessData.x RecordIndex.one) -
          objectiveMinimum (parameterDomain_q_pos HB_central_parameters_in_domain) hf := by
      rw [hgap.2]
      exact mul_pos hRpos hbase
    have hgap_pos :
        0 < hf.f (hbRationalWitnessData.x RecordIndex.two) -
          objectiveMinimum (parameterDomain_q_pos HB_central_parameters_in_domain) hf := by
      rw [hgap.1]
      exact mul_pos hRpos hV1pos
    let V0 : ℝ :=
      prescribedCertificateValue
        (parameterDomain_q_pos HB_central_parameters_in_domain) hf cert
        (hbRationalWitnessData.x RecordIndex.zero)
        (hbRationalWitnessData.x RecordIndex.one)
    let V1 : ℝ :=
      prescribedCertificateValue
        (parameterDomain_q_pos HB_central_parameters_in_domain) hf cert
        (hbRationalWitnessData.x RecordIndex.one)
        (hbRationalWitnessData.x RecordIndex.two)
    have hmono : V1 ≤ V0 := by
      simpa [V0, V1] using hcert.2
    have hscale' : V1 = hbWitnessR * V0 := by
      simpa [V0, V1] using hscale
    have hV0_nonpos : V0 ≤ 0 := by
      nlinarith [hmono, hscale', hRgt]
    have hV1_nonpos : V1 ≤ 0 := by
      rw [hscale']
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hRpos) hV0_nonpos
    have hgap_cert :
        hf.f (hbRationalWitnessData.x RecordIndex.two) -
            objectiveMinimum (parameterDomain_q_pos HB_central_parameters_in_domain) hf ≤
          V1 := by
      simpa [V1] using hcert.1
    nlinarith
  · exact HB_ALL_FREQUENCY_CYCLE_EXCLUSION

private theorem hb_record_matrix_power_similarity
    {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (R : ℝ)
    (hS : Matrix.transpose S * S = R • (1 : Matrix (Fin d) (Fin d) ℝ)) :
    ∀ n : ℕ,
      Matrix.transpose (S ^ n) * (S ^ n) =
        (R ^ n) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        Matrix.transpose (S ^ (n + 1)) * (S ^ (n + 1)) =
            S.transpose * (Matrix.transpose (S ^ n) * (S ^ n)) * S := by
              rw [pow_succ, Matrix.transpose_mul]
              simp [Matrix.mul_assoc]
        _ = S.transpose * ((R ^ n) • (1 : Matrix (Fin d) (Fin d) ℝ)) * S := by
              rw [ih]
        _ = (R ^ n) • (S.transpose * S) := by
              simp [Matrix.mul_assoc, smul_eq_mul]
        _ = (R ^ n) • (R • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
              rw [hS]
        _ = (R ^ (n + 1)) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
              rw [smul_smul, pow_succ]

private def hb_record_scaled_data
    {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (R : ℝ) (n : ℕ)
    (data : FiniteData d) : FiniteData d where
  x i := matrixVec (S ^ n) (data.x i)
  g i := matrixVec (S ^ n) (data.g i)
  F i := (R ^ n) * data.F i

private theorem hb_record_scaled_residual
    {q : ℝ} {d : ℕ} (data : FiniteData d)
    (S : Matrix (Fin d) (Fin d) ℝ) (R : ℝ)
    (hS : Matrix.transpose S * S = R • (1 : Matrix (Fin d) (Fin d) ℝ))
    (n : ℕ) (i j : RecordIndex) :
    interpolationResidual q (hb_record_scaled_data S R n data) i j =
      (R ^ n) * interpolationResidual q data i j := by
  have hsim :
      Matrix.transpose (S ^ n) * (S ^ n) =
        (R ^ n) • (1 : Matrix (Fin d) (Fin d) ℝ) :=
    hb_record_matrix_power_similarity S R hS n
  have hinner (u v : Vec d) :
      inner ℝ (matrixVec (S ^ n) u) (matrixVec (S ^ n) v) =
        (R ^ n) * inner ℝ u v :=
    matrix_vec_inner_scale_of_similarity (S ^ n) (R ^ n) hsim u v
  have hsub (u v : Vec d) :
      matrixVec (S ^ n) u - matrixVec (S ^ n) v =
        matrixVec (S ^ n) (u - v) := by
    ext k
    simp [matrixVec, Matrix.mulVec, sub_eq_add_neg, Finset.sum_sub_distrib]
  have hnorm (u : Vec d) :
      ‖matrixVec (S ^ n) u‖ ^ 2 = (R ^ n) * ‖u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hinner, real_inner_self_eq_norm_sq]
  have hnorm_sub (u v : Vec d) :
      ‖matrixVec (S ^ n) u - matrixVec (S ^ n) v‖ ^ 2 =
        (R ^ n) * ‖u - v‖ ^ 2 := by
    rw [hsub, hnorm]
  have hinner_sub (u v x y : Vec d) :
      inner ℝ (matrixVec (S ^ n) u - matrixVec (S ^ n) v)
          (matrixVec (S ^ n) x - matrixVec (S ^ n) y) =
        (R ^ n) * inner ℝ (u - v) (x - y) := by
    rw [hsub, hsub, hinner]
  dsimp [interpolationResidual, hb_record_scaled_data]
  simp only [hsub]
  rw [hnorm, hnorm, hinner, hinner]
  ring

private theorem hb_record_scaled_realizable
    {q : ℝ} {d : ℕ} (hD : ParameterDomain q a b)
    (data : FiniteData d) (S : Matrix (Fin d) (Fin d) ℝ) (R : ℝ)
    (hS : Matrix.transpose S * S = R • (1 : Matrix (Fin d) (Fin d) ℝ))
    (hres : ∀ i j : RecordIndex, 0 ≤ interpolationResidual q data i j)
    (hR : 1 < R) :
    ∀ n : ℕ, FiniteDataRealizable q (hb_record_scaled_data S R n data) := by
  have hq0 : 0 < q := parameterDomain_q_pos hD
  have hq1 : q < 1 := parameterDomain_q_lt_one hD
  have hR0 : 0 ≤ R := by linarith
  intro n
  apply (HB_INTERPOLATION hq0 hq1 _).1
  intro i j
  rw [hb_record_scaled_residual data S R hS n i j]
  exact mul_nonneg (pow_nonneg hR0 n) (hres i j)

private theorem hb_record_matrixVec_affine
    {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (c : ℝ)
    (u v w : Vec d) :
    matrixVec M (c • u + v - w) =
      c • matrixVec M u + matrixVec M v - matrixVec M w := by
  ext k
  simp [matrixVec, Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul]

private theorem hb_record_matrixVec_three_smul
    {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (c₁ c₂ c₃ : ℝ) (u v w : Vec d) :
    matrixVec M (c₁ • u + c₂ • v + c₃ • w) =
      c₁ • matrixVec M u + c₂ • matrixVec M v + c₃ • matrixVec M w := by
  ext k
  simp [matrixVec, Matrix.mulVec_add, Matrix.mulVec_smul]

private theorem hb_record_matrixVec_pow_succ
    {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (n : ℕ) (x : Vec d) :
    matrixVec (S ^ (n + 1)) x =
      matrixVec (S ^ n) (matrixVec S x) := by
  unfold matrixVec
  rw [pow_succ, Matrix.mulVec_mulVec]

private theorem hb_record_fullRecord_ext
    {d : ℕ} {r s : FullRecord d}
    (hu : r.uCentered = s.uCentered)
    (gu : r.gradU = s.gradU)
    (hv : r.vCentered = s.vCentered)
    (gv : r.gradV = s.gradV)
    (fu : r.gapU = s.gapU)
    (fv : r.gapV = s.gapV) :
    r = s := by
  cases r
  cases s
  simp_all

theorem HB_RECORD_GENERAL_conditional_obstruction {q a b : ℝ}
    (hD : ParameterDomain q a b) {d : ℕ} (hdim : 1 ≤ d)
    (data : FiniteData d) (S : Matrix (Fin d) (Fin d) ℝ) (R : ℝ)
    (hstar_x : data.x RecordIndex.star = 0)
    (hstar_g : data.g RecordIndex.star = 0)
    (hstar_F : data.F RecordIndex.star = 0)
    (hres : ∀ i j : RecordIndex, 0 ≤ interpolationResidual q data i j)
    (hupdate :
      data.x RecordIndex.two =
        (1 + b) • data.x RecordIndex.one -
          b • data.x RecordIndex.zero - a • data.g RecordIndex.one)
    (hsim_matrix : Matrix.transpose S * S = R • (1 : Matrix (Fin d) (Fin d) ℝ))
    (hR : 1 < R)
    (hx01 : data.x RecordIndex.one = matrixVec S (data.x RecordIndex.zero))
    (hx12 : data.x RecordIndex.two = matrixVec S (data.x RecordIndex.one))
    (hg01 : data.g RecordIndex.one = matrixVec S (data.g RecordIndex.zero))
    (hg12 : data.g RecordIndex.two = matrixVec S (data.g RecordIndex.one))
    (hF01 : data.F RecordIndex.one = R * data.F RecordIndex.zero)
    (hF12 : data.F RecordIndex.two = R * data.F RecordIndex.one)
    (hF0 : 0 < data.F RecordIndex.zero) :
    ¬ ∃ Phi : FullRecord d → ℝ, RecordMapWorks q a b d Phi := by
  rintro ⟨Phi, hPhi⟩
  have hq0 : 0 < q := parameterDomain_q_pos hD
  have hq1 : q < 1 := parameterDomain_q_lt_one hD
  have hR0 : 0 ≤ R := by linarith
  have hscaled_realizable :
      ∀ n : ℕ, FiniteDataRealizable q (hb_record_scaled_data S R n data) :=
    hb_record_scaled_realizable hD data S R hsim_matrix hres hR
  let hf : ℕ → AdmissibleObjective q d :=
    fun n => Classical.choose (hscaled_realizable n)
  have hreal (n : ℕ) (i : RecordIndex) :
      (hf n).f ((hb_record_scaled_data S R n data).x i) =
          (hb_record_scaled_data S R n data).F i ∧
        gradient (hf n).f ((hb_record_scaled_data S R n data).x i) =
          (hb_record_scaled_data S R n data).g i := by
    exact Classical.choose_spec (hscaled_realizable n) i
  have hstar_x_n (n : ℕ) :
      (hb_record_scaled_data S R n data).x RecordIndex.star = 0 := by
    dsimp [hb_record_scaled_data]
    rw [hstar_x]
    simp [matrixVec]
  have hstar_g_n (n : ℕ) :
      (hb_record_scaled_data S R n data).g RecordIndex.star = 0 := by
    dsimp [hb_record_scaled_data]
    rw [hstar_g]
    simp [matrixVec]
  have hstar_F_n (n : ℕ) :
      (hb_record_scaled_data S R n data).F RecordIndex.star = 0 := by
    dsimp [hb_record_scaled_data]
    rw [hstar_F]
    simp
  have hfzero (n : ℕ) : (hf n).f (0 : Vec d) = 0 := by
    calc
      (hf n).f (0 : Vec d) =
          (hf n).f ((hb_record_scaled_data S R n data).x RecordIndex.star) := by
            rw [hstar_x_n]
      _ = (hb_record_scaled_data S R n data).F RecordIndex.star :=
        (hreal n RecordIndex.star).1
      _ = 0 := hstar_F_n n
  have hgzero (n : ℕ) : gradient (hf n).f (0 : Vec d) = 0 := by
    calc
      gradient (hf n).f (0 : Vec d) =
          gradient (hf n).f ((hb_record_scaled_data S R n data).x RecordIndex.star) := by
            rw [hstar_x_n]
      _ = (hb_record_scaled_data S R n data).g RecordIndex.star :=
        (hreal n RecordIndex.star).2
      _ = 0 := hstar_g_n n
  have hglobal (n : ℕ) : ∀ y : Vec d, (hf n).f (0 : Vec d) ≤ (hf n).f y := by
    intro y
    rw [hfzero n]
    have hstrong := (hf n).strongConvex_lower (0 : Vec d) y
    rw [hfzero n, hgzero n] at hstrong
    simp at hstrong
    have hqhalf : 0 ≤ q / 2 := by positivity
    have hnonneg :
        0 ≤ (q / 2 : ℝ) * ‖y - (0 : Vec d)‖ ^ 2 :=
      mul_nonneg hqhalf (sq_nonneg _)
    have hnonneg' : 0 ≤ (q / 2 : ℝ) * ‖y‖ ^ 2 := by
      simpa using hnonneg
    nlinarith
  have hmin (n : ℕ) :
      objectiveMinimizer hq0 (hf n) = 0 := by
    exact (objectiveMinimizer_unique hq0 (hf n) (hglobal n)).symm
  have hminval (n : ℕ) :
      objectiveMinimum hq0 (hf n) = 0 := by
    simp [objectiveMinimum, hmin n, hfzero n]
  let u : ℕ → Vec d :=
    fun n => matrixVec (S ^ n) (data.x RecordIndex.zero)
  let v : ℕ → Vec d :=
    fun n => matrixVec (S ^ n) (data.x RecordIndex.one)
  let w : ℕ → Vec d :=
    fun n => hbSuccessor a b (hf n) (u n) (v n)
  let A : ℕ → FullRecord d :=
    fun n => twoPointRecord hq0 (hf n) (u n) (v n)
  have hval (n : ℕ) (i : RecordIndex) :
      (hf n).f (matrixVec (S ^ n) (data.x i)) =
        (R ^ n) * data.F i := by
    simpa [hb_record_scaled_data] using (hreal n i).1
  have hgrad (n : ℕ) (i : RecordIndex) :
      gradient (hf n).f (matrixVec (S ^ n) (data.x i)) =
        matrixVec (S ^ n) (data.g i) := by
    simpa [hb_record_scaled_data] using (hreal n i).2
  have hsucc (n : ℕ) :
      w n = matrixVec (S ^ n) (data.x RecordIndex.two) := by
    dsimp [w, u, v]
    rw [hbSuccessor_eq_successor_form, hgrad n RecordIndex.one]
    rw [hupdate]
    have hmap :=
      hb_record_matrixVec_three_smul (S ^ n)
        (1 + b) (-b) (-a)
        (data.x RecordIndex.one)
        (data.x RecordIndex.zero)
        (data.g RecordIndex.one)
    simpa [sub_eq_add_neg, smul_neg, add_assoc] using hmap.symm
  have hnext_u (n : ℕ) : u (n + 1) = v n := by
    calc
      u (n + 1) = matrixVec (S ^ (n + 1)) (data.x RecordIndex.zero) := rfl
      _ = matrixVec (S ^ n) (matrixVec S (data.x RecordIndex.zero)) :=
        hb_record_matrixVec_pow_succ S n (data.x RecordIndex.zero)
      _ = matrixVec (S ^ n) (data.x RecordIndex.one) := by rw [hx01]
      _ = v n := rfl
  have hnext_v (n : ℕ) : v (n + 1) = w n := by
    calc
      v (n + 1) = matrixVec (S ^ (n + 1)) (data.x RecordIndex.one) := rfl
      _ = matrixVec (S ^ n) (matrixVec S (data.x RecordIndex.one)) :=
        hb_record_matrixVec_pow_succ S n (data.x RecordIndex.one)
      _ = matrixVec (S ^ n) (data.x RecordIndex.two) := by rw [hx12]
      _ = w n := (hsucc n).symm
  have hnext_grad_u (n : ℕ) :
      gradient (hf (n + 1)).f (u (n + 1)) =
        gradient (hf n).f (v n) := by
    calc
      gradient (hf (n + 1)).f (u (n + 1)) =
          matrixVec (S ^ (n + 1)) (data.g RecordIndex.zero) := by
            simpa [u] using hgrad (n + 1) RecordIndex.zero
      _ = matrixVec (S ^ n) (matrixVec S (data.g RecordIndex.zero)) :=
        hb_record_matrixVec_pow_succ S n (data.g RecordIndex.zero)
      _ = matrixVec (S ^ n) (data.g RecordIndex.one) := by rw [hg01]
      _ = gradient (hf n).f (v n) := by
        simpa [v] using (hgrad n RecordIndex.one).symm
  have hnext_grad_v (n : ℕ) :
      gradient (hf (n + 1)).f (v (n + 1)) =
        gradient (hf n).f (w n) := by
    calc
      gradient (hf (n + 1)).f (v (n + 1)) =
          matrixVec (S ^ (n + 1)) (data.g RecordIndex.one) := by
            simpa [v] using hgrad (n + 1) RecordIndex.one
      _ = matrixVec (S ^ n) (matrixVec S (data.g RecordIndex.one)) :=
        hb_record_matrixVec_pow_succ S n (data.g RecordIndex.one)
      _ = matrixVec (S ^ n) (data.g RecordIndex.two) := by rw [hg12]
      _ = gradient (hf n).f (w n) := by
        rw [hsucc n]
        exact (hgrad n RecordIndex.two).symm
  have hgap_u0 (n : ℕ) :
      (hf n).f (u n) - objectiveMinimum hq0 (hf n) =
        (R ^ n) * data.F RecordIndex.zero := by
    rw [hminval n]
    simpa [u] using hval n RecordIndex.zero
  have hgap_u (n : ℕ) :
      (hf n).f (v n) - objectiveMinimum hq0 (hf n) =
        (R ^ n) * data.F RecordIndex.one := by
    rw [hminval n]
    simpa [v] using hval n RecordIndex.one
  have hgap_v (n : ℕ) :
      (hf n).f (w n) - objectiveMinimum hq0 (hf n) =
        (R ^ n) * data.F RecordIndex.two := by
    rw [hsucc n, hminval n]
    simpa using hval n RecordIndex.two
  have hsucc_record (n : ℕ) :
      twoPointRecord hq0 (hf n) (v n) (w n) = A (n + 1) := by
    apply hb_record_fullRecord_ext
    · dsimp [twoPointRecord, A]
      rw [hmin n, hmin (n + 1)]
      simpa using (hnext_u n).symm
    · dsimp [twoPointRecord, A]
      exact (hnext_grad_u n).symm
    · dsimp [twoPointRecord, A]
      rw [hmin n, hmin (n + 1)]
      simpa using (hnext_v n).symm
    · dsimp [twoPointRecord, A]
      exact (hnext_grad_v n).symm
    · dsimp [twoPointRecord, A]
      rw [hgap_u n, hgap_u0 (n + 1), hF01]
      ring
    · dsimp [twoPointRecord, A]
      rw [hgap_v n, hgap_u (n + 1), hF12]
      ring
  have hqeq : parameterDomain_q_pos hD = hq0 := Subsingleton.elim _ _
  have hstep (n : ℕ) :
      (R ^ n) * data.F RecordIndex.two ≤ Phi (A (n + 1)) ∧
        Phi (A (n + 1)) ≤ Phi (A n) := by
    have hcert := hPhi hD (hf n) (u n) (v n)
    dsimp [w] at hcert
    rw [hqeq] at hcert
    have hsucc' :
        twoPointRecord hq0 (hf n) (v n)
            (hbSuccessor a b (hf n) (u n) (v n)) =
          A (n + 1) := by
      simpa [w] using hsucc_record n
    rw [hsucc'] at hcert
    have hgap_v' :
        (hf n).f (hbSuccessor a b (hf n) (u n) (v n)) -
            objectiveMinimum hq0 (hf n) =
          (R ^ n) * data.F RecordIndex.two := by
      simpa [w] using hgap_v n
    constructor
    · simpa [hgap_v'] using hcert.1
    · simpa [A] using hcert.2
  have hchain : ∀ n : ℕ, Phi (A n) ≤ Phi (A 0) := by
    intro n
    induction n with
    | zero =>
        exact le_rfl
    | succ n ih =>
        have hmono := (hstep n).2
        simpa [Nat.succ_eq_add_one] using hmono.trans ih
  have hbound (n : ℕ) :
      (R ^ n) * data.F RecordIndex.two ≤ Phi (A 0) :=
    (hstep n).1.trans (hchain (n + 1))
  have hF1_pos : 0 < data.F RecordIndex.one := by
    rw [hF01]
    exact mul_pos (by linarith) hF0
  have hFtwo_pos : 0 < data.F RecordIndex.two := by
    rw [hF12]
    exact mul_pos (by linarith) hF1_pos
  have hpow_mul :
      Tendsto (fun n : ℕ => (R ^ n) * data.F RecordIndex.two)
        atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hR).atTop_mul_const hFtwo_pos
  obtain ⟨n, hn⟩ :=
    (hpow_mul.eventually_gt_atTop (Phi (A 0))).exists
  exact (not_lt_of_ge (hbound n)) hn

private def hb_box_parameterized_h (q a b : ℝ) : ℂ :=
  ((1 + (b : ℂ)) - hbWitnessZ - (b : ℂ) * hbWitnessZ⁻¹) / (a : ℂ)

private def hb_box_parameterized_witness_data (q a b : ℝ) : FiniteData 2 where
  x i := complexAsVec2 (hbWitnessComplexX i)
  g i := complexAsVec2 (hb_box_parameterized_h q a b * hbWitnessComplexX i)
  F i := hbWitnessF * Complex.normSq (hbWitnessComplexX i)

private theorem hb_box_parameterized_h_re (q a b : ℝ) :
    (hb_box_parameterized_h q a b).re =
      ((177 / 200 : ℝ) + b * (3553 / 4013)) / a := by
  norm_num [hb_box_parameterized_h, hbWitnessZ, Complex.div_re,
    Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
  by_cases ha : a = 0
  · simp [ha]
  · field_simp [ha]
    ring

private theorem hb_box_parameterized_h_im (q a b : ℝ) :
    (hb_box_parameterized_h q a b).im =
      (-(199 / 200 : ℝ) + b * (3980 / 4013)) / a := by
  norm_num [hb_box_parameterized_h, hbWitnessZ, Complex.div_im,
    Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
  by_cases ha : a = 0
  · simp [ha]
  · field_simp [ha]

set_option maxHeartbeats 1000000 in
private theorem hb_box_parameterized_witness_residuals {q a b : ℝ}
    (hbox : HB_Box q a b) :
    ∀ i j : RecordIndex,
      i ≠ j →
        (1 / 1000 : ℝ) <
          interpolationResidual q (hb_box_parameterized_witness_data q a b) i j := by
  intro i j hij
  rcases hbox with ⟨hqbox, habox, hbbox⟩
  have hq := abs_le.mp hqbox
  have ha := abs_le.mp habox
  have hb := abs_le.mp hbbox
  have hqlo : (999 / 100000 : ℝ) ≤ q := by nlinarith [hq.1]
  have hqhi : q ≤ (1001 / 100000 : ℝ) := by nlinarith [hq.2]
  have halo : (225999 / 100000 : ℝ) ≤ a := by nlinarith [ha.1]
  have hahi : a ≤ (226001 / 100000 : ℝ) := by nlinarith [ha.2]
  have hblo : (59999 / 100000 : ℝ) ≤ b := by nlinarith [hb.1]
  have hbhi : b ≤ (60001 / 100000 : ℝ) := by nlinarith [hb.2]
  have hq1pos : 0 < 1 - q := by linarith
  have ha0 : a ≠ 0 := ne_of_gt (by linarith)
  have hq10 : 1 - q ≠ 0 := ne_of_gt hq1pos
  have hqminus : q - 1 ≠ 0 := by linarith
  have hapos : 0 < a := by linarith
  have hqnonneg : 0 ≤ q := by linarith
  let hr : ℝ := (hb_box_parameterized_h q a b).re
  let hi : ℝ := (hb_box_parameterized_h q a b).im
  have hhrlo : (626640 / 1000000 : ℝ) ≤ hr := by
    rw [show hr = (hb_box_parameterized_h q a b).re by rfl,
      hb_box_parameterized_h_re]
    apply (le_div_iff₀ hapos).2
    nlinarith
  have hhrhi : hr ≤ (626655 / 1000000 : ℝ) := by
    rw [show hr = (hb_box_parameterized_h q a b).re by rfl,
      hb_box_parameterized_h_re]
    apply (div_le_iff₀ hapos).2
    nlinarith
  have hhil : (-176968 / 1000000 : ℝ) ≤ hi := by
    rw [show hi = (hb_box_parameterized_h q a b).im by rfl,
      hb_box_parameterized_h_im]
    apply (le_div_iff₀ hapos).2
    nlinarith
  have hihi : hi ≤ (-176956 / 1000000 : ℝ) := by
    rw [show hi = (hb_box_parameterized_h q a b).im by rfl,
      hb_box_parameterized_h_im]
    apply (div_le_iff₀ hapos).2
    nlinarith
  have hhrqlo :
      (626640 / 1000000 : ℝ) * (999 / 100000 : ℝ) ≤ hr * q := by
    have h₁ := mul_nonneg (sub_nonneg.mpr hhrlo) hqnonneg
    have h₂ := mul_nonneg (sub_nonneg.mpr hqlo) (by norm_num : (0 : ℝ) ≤ 626640 / 1000000)
    nlinarith
  have hhrqhi :
      hr * q ≤ (626655 / 1000000 : ℝ) * (1001 / 100000 : ℝ) := by
    have h₁ := mul_nonneg (sub_nonneg.mpr hhrhi) hqnonneg
    have h₂ := mul_nonneg (sub_nonneg.mpr hqhi)
      (by norm_num : (0 : ℝ) ≤ 626655 / 1000000)
    nlinarith
  have hhiqlo :
      (-176968 / 1000000 : ℝ) * (1001 / 100000 : ℝ) ≤ hi * q := by
    have h₁ := mul_nonneg (sub_nonneg.mpr hhil) hqnonneg
    have h₂ := mul_nonneg (sub_nonneg.mpr hqhi)
      (by norm_num : (0 : ℝ) ≤ 176968 / 1000000)
    nlinarith
  have hhiqhi :
      hi * q ≤ (-176956 / 1000000 : ℝ) * (999 / 100000 : ℝ) := by
    have h₁ := mul_nonneg (sub_nonneg.mpr hihi) hqnonneg
    have h₂ := mul_nonneg (sub_nonneg.mpr hqlo)
      (by norm_num : (0 : ℝ) ≤ 176956 / 1000000)
    nlinarith
  have hhrsq :
      hr ^ 2 ≤ (626655 / 1000000 : ℝ) ^ 2 := by
    have h₁ := mul_nonneg (sub_nonneg.mpr hhrhi)
      (by nlinarith [hhrlo] : (0 : ℝ) ≤ 626655 / 1000000 + hr)
    nlinarith
  have hhisq :
      hi ^ 2 ≤ (-176968 / 1000000 : ℝ) ^ 2 := by
    have h₁ := mul_nonpos_of_nonneg_of_nonpos
      (sub_nonneg.mpr hhil)
      (by nlinarith [hhil] : hi + (-176968 / 1000000 : ℝ) ≤ 0)
    nlinarith
  let residualFormula : RecordIndex → RecordIndex → ℝ :=
    fun r s =>
      match r, s with
      | RecordIndex.star, RecordIndex.star => 0
      | RecordIndex.star, RecordIndex.zero =>
          40 * (50 * hi ^ 2 + 50 * hr ^ 2 - 100 * hr + 9 * q + 41) /
            (4013 * (q - 1))
      | RecordIndex.star, RecordIndex.one =>
          (50 * hi ^ 2 + 50 * hr ^ 2 - 100 * hr + 9 * q + 41) /
            (100 * (q - 1))
      | RecordIndex.star, RecordIndex.two =>
          4013 * (50 * hi ^ 2 + 50 * hr ^ 2 - 100 * hr + 9 * q + 41) /
            (400000 * (q - 1))
      | RecordIndex.zero, RecordIndex.star =>
          40 * (50 * hi ^ 2 + 50 * hr ^ 2 - 100 * hr * q + 91 * q - 41) /
            (4013 * (q - 1))
      | RecordIndex.zero, RecordIndex.zero => 0
      | RecordIndex.zero, RecordIndex.one =>
          (354650 * hi ^ 2 + 398000 * hi * q - 398000 * hi +
            354650 * hr ^ 2 - 354000 * hr * q - 355300 * hr +
            354117 * q + 533) / (401300 * (q - 1))
      | RecordIndex.zero, RecordIndex.two =>
          (3168088450 * hi ^ 2 + 366160000 * hi * q - 366160000 * hi +
            3168088450 * hr ^ 2 - 3162880000 * hr * q -
            3173296900 * hr + 3163817521 * q + 4270929) /
            (1605200000 * (q - 1))
      | RecordIndex.one, RecordIndex.star =>
          (50 * hi ^ 2 + 50 * hr ^ 2 - 100 * hr * q + 91 * q - 41) /
            (100 * (q - 1))
      | RecordIndex.one, RecordIndex.zero =>
          (354650 * hi ^ 2 - 398000 * hi * q + 398000 * hi +
            354650 * hr ^ 2 - 355300 * hr * q - 354000 * hr +
            355183 * q - 533) / (401300 * (q - 1))
      | RecordIndex.one, RecordIndex.one => 0
      | RecordIndex.one, RecordIndex.two =>
          (354650 * hi ^ 2 + 398000 * hi * q - 398000 * hi +
            354650 * hr ^ 2 - 354000 * hr * q - 355300 * hr +
            354117 * q + 533) / (400000 * (q - 1))
      | RecordIndex.two, RecordIndex.star =>
          4013 * (50 * hi ^ 2 + 50 * hr ^ 2 - 100 * hr * q + 91 * q - 41) /
            (400000 * (q - 1))
      | RecordIndex.two, RecordIndex.zero =>
          (3168088450 * hi ^ 2 - 366160000 * hi * q + 366160000 * hi +
            3168088450 * hr ^ 2 - 3173296900 * hr * q -
            3162880000 * hr + 3172359379 * q - 4270929) /
            (1605200000 * (q - 1))
      | RecordIndex.two, RecordIndex.one =>
          (354650 * hi ^ 2 - 398000 * hi * q + 398000 * hi +
            354650 * hr ^ 2 - 355300 * hr * q - 354000 * hr +
            355183 * q - 533) / (400000 * (q - 1))
      | RecordIndex.two, RecordIndex.two => 0
  have hformula :
      ∀ r s : RecordIndex,
        interpolationResidual q (hb_box_parameterized_witness_data q a b) r s =
          residualFormula r s := by
    have hh : hb_box_parameterized_h q a b = ⟨hr, hi⟩ := by
      apply Complex.ext <;> rfl
    intro r s
    cases r <;> cases s
    · simp [residualFormula, interpolationResidual]
    · dsimp [interpolationResidual, hb_box_parameterized_witness_data]
      rw [hh]
      norm_num [residualFormula, interpolationResidual,
        hb_box_parameterized_witness_data, hbWitnessComplexX, hbWitnessZ,
        hbWitnessF, complexAsVec2_sub, complexAsVec2_norm_sq,
        complexAsVec2_inner, Complex.normSq_apply, Complex.div_re,
        Complex.div_im, Complex.inv_re, Complex.inv_im, Complex.mul_re,
        Complex.mul_im]
      field_simp [hq10, hqminus]
      ring
    · dsimp [interpolationResidual, hb_box_parameterized_witness_data]
      rw [hh]
      norm_num [residualFormula, interpolationResidual,
        hb_box_parameterized_witness_data, hbWitnessComplexX, hbWitnessZ,
        hbWitnessF, complexAsVec2_sub, complexAsVec2_norm_sq,
        complexAsVec2_inner, Complex.normSq_apply, Complex.div_re,
        Complex.div_im, Complex.inv_re, Complex.inv_im, Complex.mul_re,
        Complex.mul_im]
      field_simp [hq10, hqminus]
      ring
    · dsimp [interpolationResidual, hb_box_parameterized_witness_data]
      rw [hh]
      norm_num [residualFormula, interpolationResidual,
        hb_box_parameterized_witness_data, hbWitnessComplexX, hbWitnessZ,
        hbWitnessF, complexAsVec2_sub, complexAsVec2_norm_sq,
        complexAsVec2_inner, Complex.normSq_apply, Complex.div_re,
        Complex.div_im, Complex.inv_re, Complex.inv_im, Complex.mul_re,
        Complex.mul_im]
      field_simp [hq10, hqminus]
      ring
    · dsimp [interpolationResidual, hb_box_parameterized_witness_data]
      rw [hh]
      norm_num [residualFormula, interpolationResidual,
        hb_box_parameterized_witness_data, hbWitnessComplexX, hbWitnessZ,
        hbWitnessF, complexAsVec2_sub, complexAsVec2_norm_sq,
        complexAsVec2_inner, Complex.normSq_apply, Complex.div_re,
        Complex.div_im, Complex.inv_re, Complex.inv_im, Complex.mul_re,
        Complex.mul_im]
      field_simp [hq10, hqminus]
      ring
    · simp [residualFormula, interpolationResidual]
    · dsimp [interpolationResidual, hb_box_parameterized_witness_data]
      rw [hh]
      norm_num [residualFormula, interpolationResidual,
        hb_box_parameterized_witness_data, hbWitnessComplexX, hbWitnessZ,
        hbWitnessF, complexAsVec2_sub, complexAsVec2_norm_sq,
        complexAsVec2_inner, Complex.normSq_apply, Complex.div_re,
        Complex.div_im, Complex.inv_re, Complex.inv_im, Complex.mul_re,
        Complex.mul_im]
      field_simp [hq10, hqminus]
      ring
    · dsimp [interpolationResidual, hb_box_parameterized_witness_data]
      rw [hh]
      norm_num [residualFormula, interpolationResidual,
        hb_box_parameterized_witness_data, hbWitnessComplexX, hbWitnessZ,
        hbWitnessF, complexAsVec2_sub, complexAsVec2_norm_sq,
        complexAsVec2_inner, Complex.normSq_apply, Complex.div_re,
        Complex.div_im, Complex.inv_re, Complex.inv_im, Complex.mul_re,
        Complex.mul_im]
      field_simp [hq10, hqminus]
      ring
    · dsimp [interpolationResidual, hb_box_parameterized_witness_data]
      rw [hh]
      norm_num [residualFormula, interpolationResidual,
        hb_box_parameterized_witness_data, hbWitnessComplexX, hbWitnessZ,
        hbWitnessF, complexAsVec2_sub, complexAsVec2_norm_sq,
        complexAsVec2_inner, Complex.normSq_apply, Complex.div_re,
        Complex.div_im, Complex.inv_re, Complex.inv_im, Complex.mul_re,
        Complex.mul_im]
      field_simp [hq10, hqminus]
      ring
    · dsimp [interpolationResidual, hb_box_parameterized_witness_data]
      rw [hh]
      norm_num [residualFormula, interpolationResidual,
        hb_box_parameterized_witness_data, hbWitnessComplexX, hbWitnessZ,
        hbWitnessF, complexAsVec2_sub, complexAsVec2_norm_sq,
        complexAsVec2_inner, Complex.normSq_apply, Complex.div_re,
        Complex.div_im, Complex.inv_re, Complex.inv_im, Complex.mul_re,
        Complex.mul_im]
      field_simp [hq10, hqminus]
      ring
    · simp [residualFormula, interpolationResidual]
    · dsimp [interpolationResidual, hb_box_parameterized_witness_data]
      rw [hh]
      norm_num [residualFormula, interpolationResidual,
        hb_box_parameterized_witness_data, hbWitnessComplexX, hbWitnessZ,
        hbWitnessF, complexAsVec2_sub, complexAsVec2_norm_sq,
        complexAsVec2_inner, Complex.normSq_apply, Complex.div_re,
        Complex.div_im, Complex.inv_re, Complex.inv_im, Complex.mul_re,
        Complex.mul_im]
      field_simp [hq10, hqminus]
      ring
    · dsimp [interpolationResidual, hb_box_parameterized_witness_data]
      rw [hh]
      norm_num [residualFormula, interpolationResidual,
        hb_box_parameterized_witness_data, hbWitnessComplexX, hbWitnessZ,
        hbWitnessF, complexAsVec2_sub, complexAsVec2_norm_sq,
        complexAsVec2_inner, Complex.normSq_apply, Complex.div_re,
        Complex.div_im, Complex.inv_re, Complex.inv_im, Complex.mul_re,
        Complex.mul_im]
      field_simp [hq10, hqminus]
      ring
    · dsimp [interpolationResidual, hb_box_parameterized_witness_data]
      rw [hh]
      norm_num [residualFormula, interpolationResidual,
        hb_box_parameterized_witness_data, hbWitnessComplexX, hbWitnessZ,
        hbWitnessF, complexAsVec2_sub, complexAsVec2_norm_sq,
        complexAsVec2_inner, Complex.normSq_apply, Complex.div_re,
        Complex.div_im, Complex.inv_re, Complex.inv_im, Complex.mul_re,
        Complex.mul_im]
      field_simp [hq10, hqminus]
      ring
    · dsimp [interpolationResidual, hb_box_parameterized_witness_data]
      rw [hh]
      norm_num [residualFormula, interpolationResidual,
        hb_box_parameterized_witness_data, hbWitnessComplexX, hbWitnessZ,
        hbWitnessF, complexAsVec2_sub, complexAsVec2_norm_sq,
        complexAsVec2_inner, Complex.normSq_apply, Complex.div_re,
        Complex.div_im, Complex.inv_re, Complex.inv_im, Complex.mul_re,
        Complex.mul_im]
      field_simp [hq10, hqminus]
      ring
    · simp [residualFormula, interpolationResidual]
  have hA :
      50 * hi ^ 2 + 50 * hr ^ 2 - 100 * hr + 9 * q + 41 ≤
        (-3 / 10 : ℝ) := by
    linarith [hhisq, hhrsq, hhrlo, hqhi]
  have hD :
      50 * hi ^ 2 + 50 * hr ^ 2 - 100 * hr * q + 91 * q - 41 ≤
        (-19 : ℝ) := by
    linarith [hhisq, hhrsq, hhrqlo, hqhi]
  have hP :
      354650 * hi ^ 2 + 398000 * hi * q - 398000 * hi +
          354650 * hr ^ 2 - 354000 * hr * q - 355300 * hr +
          354117 * q + 533 ≤
        (-600 : ℝ) := by
    linarith [hhisq, hhrsq, hhiqhi, hhil, hhrqlo, hhrlo, hqhi]
  have hP2 :
      354650 * hi ^ 2 - 398000 * hi * q + 398000 * hi +
          354650 * hr ^ 2 - 355300 * hr * q - 354000 * hr +
          355183 * q - 533 ≤
        (-100000 : ℝ) := by
    linarith [hhisq, hhrsq, hhiqlo, hihi, hhrqlo, hhrlo, hqhi]
  have hQ :
      3168088450 * hi ^ 2 + 366160000 * hi * q - 366160000 * hi +
          3168088450 * hr ^ 2 - 3162880000 * hr * q -
          3173296900 * hr + 3163817521 * q + 4270929 ≤
        (-500000000 : ℝ) := by
    linarith [hhisq, hhrsq, hhiqhi, hhil, hhrqlo, hhrlo, hqhi]
  have hQ2 :
      3168088450 * hi ^ 2 - 366160000 * hi * q + 366160000 * hi +
          3168088450 * hr ^ 2 - 3173296900 * hr * q -
          3162880000 * hr + 3172359379 * q - 4270929 ≤
        (-600000000 : ℝ) := by
    linarith [hhisq, hhrsq, hhiqlo, hihi, hhrqlo, hhrlo, hqhi]
  have hres := hformula i j
  cases i <;> cases j
  · exact (hij rfl).elim
  · rw [hres]
    simp only [residualFormula]
    rw [lt_div_iff_of_neg (by nlinarith [hq1pos])]
    linarith [hA, hqlo]
  · rw [hres]
    simp only [residualFormula]
    rw [lt_div_iff_of_neg (by nlinarith [hq1pos])]
    linarith [hA, hqlo]
  · rw [hres]
    simp only [residualFormula]
    rw [lt_div_iff_of_neg (by nlinarith [hq1pos])]
    linarith [hA, hqlo]
  · rw [hres]
    simp only [residualFormula]
    rw [lt_div_iff_of_neg (by nlinarith [hq1pos])]
    linarith [hD, hqlo]
  · exact (hij rfl).elim
  · rw [hres]
    simp only [residualFormula]
    rw [lt_div_iff_of_neg (by nlinarith [hq1pos])]
    linarith [hP, hqlo]
  · rw [hres]
    simp only [residualFormula]
    rw [lt_div_iff_of_neg (by nlinarith [hq1pos])]
    linarith [hQ, hqlo]
  · rw [hres]
    simp only [residualFormula]
    rw [lt_div_iff_of_neg (by nlinarith [hq1pos])]
    linarith [hD, hqlo]
  · rw [hres]
    simp only [residualFormula]
    rw [lt_div_iff_of_neg (by nlinarith [hq1pos])]
    linarith [hP2, hqlo]
  · exact (hij rfl).elim
  · rw [hres]
    simp only [residualFormula]
    rw [lt_div_iff_of_neg (by nlinarith [hq1pos])]
    linarith [hP, hqlo]
  · rw [hres]
    simp only [residualFormula]
    rw [lt_div_iff_of_neg (by nlinarith [hq1pos])]
    linarith [hD, hqlo]
  · rw [hres]
    simp only [residualFormula]
    rw [lt_div_iff_of_neg (by nlinarith [hq1pos])]
    linarith [hQ2, hqlo]
  · rw [hres]
    simp only [residualFormula]
    rw [lt_div_iff_of_neg (by nlinarith [hq1pos])]
    linarith [hP2, hqlo]
  · exact (hij rfl).elim

private theorem hb_box_no_common_record_map {q a b : ℝ}
    (hbox : HB_Box q a b) :
    ¬ ∃ Phi : FullRecord 2 → ℝ, RecordMapWorks q a b 2 Phi := by
  obtain ⟨hR, hRgt, hFpos, hz0, hEta, hxstar, hgstar, hFstar, hres0,
      hrealizable, hupdate0, hF01, hF12, hF0, hmatrix, hx01, hx12,
      hg01, hg12⟩ :=
    HB_RATIONAL_WITNESS_exact_data
  let data := hb_box_parameterized_witness_data q a b
  have hstar_x : data.x RecordIndex.star = 0 := by
    ext i
    simp [data, hb_box_parameterized_witness_data, hbWitnessComplexX,
      complexAsVec2]
  have hstar_g : data.g RecordIndex.star = 0 := by
    ext i
    simp [data, hb_box_parameterized_witness_data, hbWitnessComplexX,
      complexAsVec2]
  have hstar_F : data.F RecordIndex.star = 0 := by
    simp [data, hb_box_parameterized_witness_data, hbWitnessComplexX,
      hbWitnessF]
  have hres : ∀ i j : RecordIndex, 0 ≤ interpolationResidual q data i j := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [data, interpolationResidual]
    · have hstrict :=
        hb_box_parameterized_witness_residuals hbox i j hij
      linarith
  have ha0 : a ≠ 0 := by
    rcases hbox with ⟨_, habox, _⟩
    have ha := abs_le.mp habox
    nlinarith [ha.1]
  have hz0' : hbWitnessZ ≠ 0 := hz0
  have hscalar (c : ℝ) (z : ℂ) :
      c • complexAsVec2 z = complexAsVec2 ((c : ℂ) * z) := by
    ext i
    fin_cases i <;> simp [complexAsVec2]
  have hupdate :
      data.x RecordIndex.two =
        (1 + b) • data.x RecordIndex.one -
          b • data.x RecordIndex.zero - a • data.g RecordIndex.one := by
    change complexAsVec2 hbWitnessZ =
      (1 + b) • complexAsVec2 (1 : ℂ) -
        b • complexAsVec2 hbWitnessZ⁻¹ -
          a • complexAsVec2 (hb_box_parameterized_h q a b * (1 : ℂ))
    rw [hscalar (1 + b) 1, hscalar b hbWitnessZ⁻¹,
      hscalar a (hb_box_parameterized_h q a b * (1 : ℂ))]
    rw [complexAsVec2_sub, complexAsVec2_sub]
    apply congrArg complexAsVec2
    dsimp [hb_box_parameterized_h]
    field_simp [ha0]
    push_cast
    ring
  have hF01' : data.F RecordIndex.one = hbWitnessR * data.F RecordIndex.zero := by
    simpa [data, hb_box_parameterized_witness_data, hbRationalWitnessData,
      hbWitnessComplexX] using hF01
  have hF12' : data.F RecordIndex.two = hbWitnessR * data.F RecordIndex.one := by
    simpa [data, hb_box_parameterized_witness_data, hbRationalWitnessData,
      hbWitnessComplexX] using hF12
  have hx01' : data.x RecordIndex.one =
      matrixVec hbWitnessSimilarityMatrix (data.x RecordIndex.zero) := by
    simpa [data, hb_box_parameterized_witness_data, hbRationalWitnessData,
      hbWitnessComplexX] using hx01
  have hx12' : data.x RecordIndex.two =
      matrixVec hbWitnessSimilarityMatrix (data.x RecordIndex.one) := by
    simpa [data, hb_box_parameterized_witness_data, hbRationalWitnessData,
      hbWitnessComplexX] using hx12
  have hg01' :
      data.g RecordIndex.one =
        matrixVec hbWitnessSimilarityMatrix (data.g RecordIndex.zero) := by
    change complexAsVec2 (hb_box_parameterized_h q a b * (1 : ℂ)) =
      matrixVec hbWitnessSimilarityMatrix
        (complexAsVec2 (hb_box_parameterized_h q a b * hbWitnessZ⁻¹))
    rw [← complex_as_vec2_witness_action
      (hb_box_parameterized_h q a b * hbWitnessZ⁻¹)]
    apply congrArg complexAsVec2
    field_simp [hz0']
  have hg12' :
      data.g RecordIndex.two =
        matrixVec hbWitnessSimilarityMatrix (data.g RecordIndex.one) := by
    change complexAsVec2 (hb_box_parameterized_h q a b * hbWitnessZ) =
      matrixVec hbWitnessSimilarityMatrix
        (complexAsVec2 (hb_box_parameterized_h q a b * (1 : ℂ)))
    rw [← complex_as_vec2_witness_action
      (hb_box_parameterized_h q a b * (1 : ℂ))]
    apply congrArg complexAsVec2
    ring
  exact
    HB_RECORD_GENERAL_conditional_obstruction
      (hD := HB_box_subset_domain hbox) (hdim := by norm_num)
      (data := data) (S := hbWitnessSimilarityMatrix) (R := hbWitnessR)
      hstar_x hstar_g hstar_F hres hupdate hmatrix hRgt
      hx01' hx12' hg01' hg12' hF01' hF12' hF0

private theorem hb_box_trajectory_norm_tendsto_zero {q a b : ℝ}
    (hbox : HB_Box q a b) {d : ℕ} (hdim : 1 ≤ d)
    (hf : AdmissibleObjective q d) (xMinusOne xZero : Vec d) :
    Tendsto
      (fun t : ℕ =>
        ‖hbIterate a b hf xMinusOne xZero t -
          objectiveMinimizer
            (parameterDomain_q_pos (HB_box_subset_domain hbox)) hf‖)
      atTop (nhds 0) := by
  let hq := parameterDomain_q_pos (HB_box_subset_domain hbox)
  let S : ℝ :=
    ‖xMinusOne - objectiveMinimizer hq hf‖ ^ 2 +
      ‖xZero - objectiveMinimizer hq hf‖ ^ 2
  have hcontraction_nonneg : 0 ≤ HB_contraction := by
    norm_num [HB_contraction, HB_C]
  have hcontraction_lt_one : HB_contraction < 1 := by
    norm_num [HB_contraction, HB_C]
  have hpow :
      Tendsto (fun t : ℕ => HB_contraction ^ t) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      hcontraction_nonneg hcontraction_lt_one
  have hsqrt :
      Tendsto (fun t : ℕ => Real.sqrt (HB_contraction ^ t))
        atTop (nhds 0) := by
    have hsqrt' :=
      (Real.continuous_sqrt.tendsto 0).comp hpow
    simpa using hsqrt'
  have hupper :
      Tendsto
        (fun t : ℕ =>
          (10 : ℝ) ^ (7 : ℕ) * Real.sqrt (HB_contraction ^ t) *
            Real.sqrt S)
        atTop (nhds 0) := by
    have hconst :
        Tendsto (fun _ : ℕ => (10 : ℝ) ^ (7 : ℕ))
          atTop (nhds ((10 : ℝ) ^ (7 : ℕ))) :=
      tendsto_const_nhds
    have hSconst :
        Tendsto (fun _ : ℕ => Real.sqrt S) atTop (nhds (Real.sqrt S)) :=
      tendsto_const_nhds
    have hmul := (hconst.mul hsqrt).mul hSconst
    simpa using hmul
  have hbound : ∀ t : ℕ,
      ‖hbIterate a b hf xMinusOne xZero t -
          objectiveMinimizer hq hf‖ ≤
        (10 : ℝ) ^ (7 : ℕ) * Real.sqrt (HB_contraction ^ t) *
          Real.sqrt S := by
    intro t
    simpa [hq, S] using
      (HB_B_uniform_linear_convergence hbox hdim hf xMinusOne xZero t)
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
      hupper
      (fun t => norm_nonneg _)
      hbound

theorem HB_BOX_uniform_absence_and_convergence {q a b : ℝ}
    (hbox : HB_Box q a b) :
    ¬ HB_L q a b ∧ ¬ HB_Cycle q a b ∧ HB_G q a b := by
  have hnotL : ¬ HB_L q a b := by
    intro hL
    obtain ⟨Phi, hPhi⟩ := record_map_works_of_HB_L hL
    exact hb_box_no_common_record_map hbox ⟨Phi, hPhi⟩
  have hnotC : ¬ HB_Cycle q a b :=
    HB_BOX_CYCLE_FOURIER_EXCLUSION hbox
  have hG : HB_G q a b := by
    refine ⟨HB_box_subset_domain hbox, ?_⟩
    intro d hdim hf xMinusOne xZero
    exact hb_box_trajectory_norm_tendsto_zero
      hbox hdim hf xMinusOne xZero
  exact ⟨hnotL, hnotC, hG⟩

theorem HB_C_no_common_record_energy :
    ¬ ∃ Phi : FullRecord 2 → ℝ, RecordMapWorks qStar aStar bStar 2 Phi := by
  intro h
  obtain ⟨Phi, hPhi⟩ := h
  obtain ⟨hR, hRgt, hFpos, hz0, hEta, hxstar, hgstar, hFstar, hres,
    hrealizable, hupdate, hF01, hF12, hF0, hmatrix, hx01, hx12, hg01, hg12⟩ :=
    HB_RATIONAL_WITNESS_exact_data
  exact
    (HB_RECORD_GENERAL_conditional_obstruction
      (q := qStar) (a := aStar) (b := bStar)
      (hD := HB_central_parameters_in_domain) (hdim := by norm_num)
      (data := hbRationalWitnessData) (S := hbWitnessSimilarityMatrix)
      (R := hbWitnessR) hxstar hgstar hFstar hres hupdate hmatrix hRgt
      hx01 hx12 hg01 hg12 hF01 hF12 hF0) ⟨Phi, hPhi⟩

end

end HeavyBallSecondRiddle
