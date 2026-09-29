import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Independence.Basic
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
import SOptLib.Glue.Algebra
import SOptLib.Glue.Calculus
import SOptLib.Glue.Probability
import SOptLib.Model.Filtration
import SOptLib.Model.Objective
import SOptLib.Layer1.Proximal
import Algorithms.Unverified.RandomizedAcceleratedProximalPoint.Part002

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

namespace RandomizedAcceleratedProximalPointSetup

open RandomizedAcceleratedProximalPoint

variable (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)

/-! Compatibility shims for the Part004 frontier.

The original split imports these interfaces through `Part003`, but that module
currently fails before producing an environment.  These local declarations keep
the active Lemma 6.14/Theorem 6.16 frontier source-shaped while the upstream
Part003 route is repaired. -/

/-- Aligns with Lan Algorithm 6.8, Eq. (6.6.8).  Considered the compiled
Part001 candidate `outerCenter_eq_xBarIter_pred`; it is the exact interface, but
the current Part004 import path cannot resolve it without rebuilding the broken
Part003 dependency, so this local shim preserves the same statement. -/
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

/-- Aligns with Lan Lemma 6.14, Eqs. (6.6.38)-(6.6.39).  Considered the
compiled Part001 candidate `outer_terminal_params_prevPrefix_const`; it is the
exact prior-prefix parameter constancy helper, but is not resolvable after
dropping the broken Part003 import, so this shim preserves that interface. -/
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

/-- Aligns with Lan Eq. (6.6.16).  Considered the compiled Part001 candidate
`alpha_schedule_bounds_for_theorem_6_16`; it is the exact sign/log package, but
the active import repair needs a local same-interface shim. -/
theorem alpha_schedule_bounds_for_theorem_6_16
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (hα_schedule :
      setup.α =
        1 - 2 / ((Fintype.card ι : ℝ) *
          (Real.sqrt (1 + 16 * (2 + setup.L / setup.μ) / (Fintype.card ι : ℝ)) + 1))) :
    0 < setup.α ∧ setup.α < 1 ∧ Real.log setup.α < 0 := by
  classical
  let m : ℝ := (Fintype.card ι : ℝ)
  let c : ℝ := 2 + setup.L / setup.μ
  let d : ℝ := m * (Real.sqrt (1 + 16 * c / m) + 1)
  have hm_pos : 0 < m := by
    dsimp [m]
    exact_mod_cast Fintype.card_pos
  have hm_ge_one : 1 ≤ m := by
    dsimp [m]
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos : 0 < Fintype.card ι))
  have hratio_ge_one : 1 ≤ setup.L / setup.μ := by
    rw [le_div_iff₀ setup.hμ_pos]
    simpa using setup.hμ_le_L
  have hc_pos : 0 < c := by
    dsimp [c]
    nlinarith
  have harg_gt_one : 1 < 1 + 16 * c / m := by
    have hfrac_pos : 0 < 16 * c / m := by positivity
    linarith
  have hsqrt_gt_one : 1 < Real.sqrt (1 + 16 * c / m) := by
    rw [Real.lt_sqrt (by norm_num)]
    nlinarith
  have hden_gt_two : 2 < d := by
    dsimp [d]
    have hsum_gt_two : 2 < Real.sqrt (1 + 16 * c / m) + 1 := by
      linarith
    nlinarith
  have hden_pos : 0 < d := by linarith
  have htwo_div_pos : 0 < 2 / d := by positivity
  have htwo_div_lt_one : 2 / d < 1 := by
    rw [div_lt_one hden_pos]
    linarith
  have hα_pos : 0 < setup.α := by
    rw [hα_schedule]
    simpa [d, c, m] using (sub_pos.mpr htwo_div_lt_one)
  have hα_lt_one : setup.α < 1 := by
    rw [hα_schedule]
    have hpos :
        0 <
          2 / ((Fintype.card ι : ℝ) *
            (Real.sqrt (1 + 16 * (2 + setup.L / setup.μ) / (Fintype.card ι : ℝ)) + 1)) := by
      simpa [d, c, m] using htwo_div_pos
    linarith
  have hlog_neg : Real.log setup.α < 0 := by
    exact (Real.log_neg_iff hα_pos).mpr hα_lt_one
  exact ⟨hα_pos, hα_lt_one, hlog_neg⟩

/-- Route-local negative-log ceiling bridge for the schedule theorem below.
Considered the later target-file `ceil_log_alpha_schedule_pow_le_inv` and the
compiled Part001 theorem with the same statement; they are exact matches but
occur after `theorem_6_16_schedule_bounds` in this repaired Part004 order, so
this private pre-helper keeps the proof body local without changing theorem
heads. -/
private theorem ceil_log_alpha_schedule_pow_le_inv_pre
    {α B : ℝ} {s : ℕ}
    (hα0 : 0 < α) (hα1 : α < 1) (hB : 0 < B)
    (hs : s = Nat.ceil (-Real.log B / Real.log α)) :
    α ^ s ≤ B⁻¹ := by
  let x : ℝ := -Real.log B / Real.log α
  have hlogα_neg : Real.log α < 0 := (Real.log_neg_iff hα0).mpr hα1
  have hlogα_ne : Real.log α ≠ 0 := ne_of_lt hlogα_neg
  have hx_le_s : x ≤ (s : ℝ) := by
    rw [hs]
    exact Nat.le_ceil x
  have hmul :
      (s : ℝ) * Real.log α ≤ x * Real.log α := by
    simpa [mul_comm] using
      (mul_le_mul_of_nonpos_right hx_le_s (le_of_lt hlogα_neg))
  have hmul' : (s : ℝ) * Real.log α ≤ -Real.log B := by
    calc
      (s : ℝ) * Real.log α ≤ x * Real.log α := hmul
      _ = -Real.log B := by
        simp [x, hlogα_ne]
  have hexp : Real.exp ((s : ℝ) * Real.log α) ≤ Real.exp (-Real.log B) :=
    Real.exp_le_exp.mpr hmul'
  calc
    α ^ s = α ^ ((s : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
    _ = Real.exp (Real.log α * (s : ℝ)) := by
      rw [Real.rpow_def_of_pos hα0]
    _ = Real.exp ((s : ℝ) * Real.log α) := by
      ring_nf
    _ ≤ Real.exp (-Real.log B) := hexp
    _ = B⁻¹ := by
      rw [Real.exp_neg, Real.exp_log hB]

/-- Route-local scalar power bounds for Theorem 6.16's exact `M_F` schedule.
Considered the compiled Part001 `theorem_6_16_power_bounds` and SOptLib
ceiling helpers; Part001 is the matching proof pattern, while SOptLib lacks the
paper-specific `M * max {6/5, (L/μ)^2}` specialization needed here. -/
private theorem theorem_6_16_power_bounds_pre
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
    ceil_log_alpha_schedule_pow_le_inv_pre hα_pos hα_lt_one hMF_pos hs_MF
  have hq_le_Cinv : M * setup.α ^ setup.s ≤ C⁻¹ := by
    calc
      M * setup.α ^ setup.s ≤ M * MF⁻¹ :=
        mul_le_mul_of_nonneg_left hpow (le_of_lt hM_pos)
      _ = C⁻¹ := by
        dsimp [MF]
        field_simp [ne_of_gt hM_pos, ne_of_gt hC_pos]
  have hCinv_le_56 : C⁻¹ ≤ 5 / 6 := by
    have h65_pos : 0 < (6 / 5 : ℝ) := by norm_num
    have hle := one_div_le_one_div_of_le h65_pos hC_ge_65
    simpa [one_div] using hle
  have hCinv_le_muL : C⁻¹ ≤ setup.μ ^ 2 / setup.L ^ 2 := by
    have hRsq_pos : 0 < R ^ 2 := sq_pos_of_pos hR_pos
    have hle := one_div_le_one_div_of_le hRsq_pos hC_ge_Rsq
    have hRsq_inv :
        (R ^ 2)⁻¹ = setup.μ ^ 2 / setup.L ^ 2 := by
      dsimp [R]
      field_simp [hμ_ne, hL_ne]
    simpa [one_div, hRsq_inv] using hle
  exact ⟨le_trans hq_le_Cinv hCinv_le_56, le_trans hq_le_Cinv hCinv_le_muL⟩

/-- Route-local lower bound comparing the `M_F` schedule to Lemma 6.14's
printed `7M/6` ceiling. Considered the compiled Part001
`theorem_6_16_hs_lower`; it is the matching source-derived comparison, copied
locally because this Part004 shim must feed the earlier locked schedule theorem. -/
private theorem theorem_6_16_hs_lower_pre
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
    ⟨_hα_pos, _hα_lt_one, hlogα_neg⟩
  let M : ℝ := 6 * (5 + 2 * setup.L / setup.μ)
  let R : ℝ := setup.L / setup.μ
  let C : ℝ := max (6 / 5 : ℝ) (R ^ 2)
  let A : ℝ := 7 * M / 6
  let MF : ℝ := M * C
  have hL_pos : 0 < setup.L := setup.L_pos
  have hR_ge_one : 1 ≤ R := by
    dsimp [R]
    rw [le_div_iff₀ setup.hμ_pos]
    simpa using setup.hμ_le_L
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
  have hA_pos : 0 < A := by
    dsimp [A]
    positivity
  have hA_le_MF : A ≤ MF := by
    have hmul : M * (7 / 6 : ℝ) ≤ M * C := by
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hM_pos)
      linarith
    dsimp [A, MF]
    linarith
  have hlog_le : Real.log A ≤ Real.log MF := by
    exact Real.log_le_log hA_pos hA_le_MF
  have hreal :
      -Real.log A / Real.log setup.α ≤ -Real.log MF / Real.log setup.α := by
    have hneg : -Real.log MF ≤ -Real.log A := by linarith
    have hinv_nonpos : (Real.log setup.α)⁻¹ ≤ 0 :=
      le_of_lt (inv_lt_zero'.mpr hlogα_neg)
    simpa [div_eq_mul_inv] using
      (mul_le_mul_of_nonpos_right hneg hinv_nonpos)
  have hceil :
      Nat.ceil (-Real.log A / Real.log setup.α) ≤
        Nat.ceil (-Real.log MF / Real.log setup.α) :=
    Nat.ceil_mono hreal
  rw [hs_schedule]
  simpa [A, MF, M, C, R, mul_assoc] using hceil

/-- Aligns with Lan Theorem 6.16's exact inner-loop length.  Considered the
compiled Part001 candidate `theorem_6_16_schedule_bounds`; it bundles the same
source-derived scalar schedule facts, but is not visible on the repaired import
path. -/
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
  have hs_lower := theorem_6_16_hs_lower_pre setup hα_schedule hs_schedule
  have hpow := theorem_6_16_power_bounds_pre setup hα_schedule hs_schedule
  simpa [M] using And.intro hs_lower hpow

/-- Corrected outer boundary supplier for the fixed-run initial gradient memory.

Aligns with Lan Algorithm 6.8 and Theorem 6.17's initial memory boundary.  The
candidate `outerPrefixHatSourceDomain_initialGradientMemory` in Part001 is the
exact match, but it is not directly name-resolvable in this Part004 import cone;
this local copy uses `outerPrefixHatSourceDomain_actualOffsetPrefix`,
`outerProcess_initialGradientMemory_of_sourceDomainPrefix`, and
`outerCenter_eq_xBarIter_pred` to expose the same generated-prefix fact. -/
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

set_option maxHeartbeats 5000000

/-- Route-local assembly of Lan Lemma 6.13 from Eq. (6.6.31) through Eq. (6.6.36).

Aligns with `book/FOML/RandomizedAcceleratedProximalPoint.json`,
`Lemma6_13_WeightedRaGradRecursion`, proof steps for Eq. (6.6.31), residual
bounds (6.6.32)-(6.6.35), Eq. (6.6.36), and the final rearrangement. Considered
Part003 `lemma_6_13_weighted_telescope_eq_6_6_31_to_6_6_36_source_route`, which
is the exact proved source route but outside this Part004 import cone; Part002
`lemma_6_13_eta_weight_telescope`, `lemma_6_13_tau_weight_telescope`,
`lemma_6_13_interior_two_correction_absorption`,
`lemma_6_13_terminal_average_young_absorption`, and
`lemma_6_13_terminal_sample_correction_absorption` are used as internal atoms,
while the SOptLib weighted-residual candidates do not package this paper-specific
source-domain telescope. -/
theorem lemma_6_13_eq631_to_eq636_source_route_local
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (z x0 xStar : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) (hxMem0 : ∀ i, xMem0 i ∈ setup.X)
    (hsource : setup.ambientFixedSourceDomain 0 z x0 xMem0 yMem0 hz hx0)
    (hhat :
      setup.ambientFixedHatSourceDomain 0 z x0 xMem0 yMem0 hz hx0)
    (hgradMem0 :
      setup.ambientFixedInitialGradientMemory z xMem0 yMem0 hxMem0)
    (hxStar : xStar ∈ setup.X)
    (h_opt : ∀ u : {x : E // x ∈ setup.X},
      (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ (fun i => setup.psiAtOn z i ⟨xStar, hxStar⟩) +
        setup.phiAt z xStar ≤
      (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ (fun i => setup.psiAtOn z i u) +
        setup.phiAt z u.1)
    (hs : 1 ≤ setup.s)
    (hparam20 : ∀ t, 1 ≤ t → t + 1 ≤ setup.s →
      setup.αSeq (t + 1) * setup.γSeq (t + 1) = setup.γSeq t)
    (hparam21 : ∀ t, 1 ≤ t → t + 1 ≤ setup.s →
      setup.γSeq (t + 1) *
          ((Fintype.card ι : ℝ) * (1 + setup.τSeq (t + 1)) - 1) ≤
        (Fintype.card ι : ℝ) * setup.γSeq t * (1 + setup.τSeq t))
    (hparam22 : ∀ t, 1 ≤ t → t + 1 ≤ setup.s →
      setup.γSeq (t + 1) * setup.ηSeq (t + 1) ≤
        setup.γSeq t * (1 + setup.ηSeq t))
    (hparam23 :
      setup.ηSeq setup.s * setup.μ / 4 ≥
        ((Fintype.card ι : ℝ) - 1) ^ 2 * setup.Lhat /
          ((Fintype.card ι : ℝ) ^ 2 * setup.τSeq setup.s))
    (hparam24 : ∀ t, 1 ≤ t → t + 1 ≤ setup.s →
      setup.ηSeq t * setup.μ / 2 ≥
        setup.αSeq (t + 1) * setup.Lhat / setup.τSeq (t + 1) +
          ((Fintype.card ι : ℝ) - 1) ^ 2 * setup.Lhat /
            ((Fintype.card ι : ℝ) ^ 2 * setup.τSeq t))
    (hparam25 :
      setup.ηSeq setup.s * setup.μ / 4 ≥
      setup.Lhat /
          ((Fintype.card ι : ℝ) * (1 + setup.τSeq setup.s)))
    (hγSeq_nonneg : ∀ t, 1 ≤ t → t ≤ setup.s → 0 ≤ setup.γSeq t)
    (hτSeq_pos : ∀ t, 1 ≤ t → t ≤ setup.s → 0 < setup.τSeq t)
    (hsource_step :
      ∀ n (hn : n + 1 ≤ setup.s) (ω : Ω),
          setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 (n + 1) ω =
            setup.sourceInnerStepAt 0 z (n + 1) hz (Nat.succ_pos n) hn
              ω (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω)
              (((setup.ambientFixedInnerProcess_mem 0 z x0 xMem0 yMem0 hz hx0 n
                (Nat.le_of_succ_le hn)) ω).1)
              (hsource n hn ω))
    (hsource_yMem :
      ∀ n (hn : n + 1 ≤ setup.s) (ω : Ω) (i : ι),
        (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 (n + 1) ω).yMem i =
          if _ : i = setup.ξ (0 + ((n + 1) - 1)) ω then
            setup.gradPsiOnAt z i
              ⟨setup.xMemAfterSampleAtState (n + 1) (Nat.succ_pos n) hn
                  (setup.ξ (0 + ((n + 1) - 1)) ω) i
                  (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω),
                hsource n hn ω i⟩
          else
            (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω).yMem i)
    (hcurv :
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
            ⟪setup.gradPhiAt z y, x - y⟫_ℝ))
    (hprox45 :
      ∀ n (hn : n + 1 ≤ setup.s),
        ∀ ω : Ω,
          let stPrev :=
            setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω
          let stNext :=
            setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 (n + 1) ω
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
                ((setup.μ / 2) * ‖stNext.x - stPrev.x‖ ^ 2))
    (h630_delta2 :
      ∀ n (hn : n + 1 ≤ setup.s),
        ((∫ ω : Ω,
            ambientFixedDelta2CurrentKernel
              (setup := setup) (offset := 0) (z := z) (x0 := x0)
              (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
              (hz := hz) (hx0 := hx0) (hxStar := hxStar)
              n hn (hhat n hn) ω (setup.ξ n ω) ∂setup.P) =
          ∫ ω : Ω,
            RandomizedAcceleratedProximalPointSetup.currentIndexAverage
              (fun j : ι =>
                ambientFixedDelta2CurrentKernel
                  (setup := setup) (offset := 0) (z := z) (x0 := x0)
                  (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
                  (hz := hz) (hx0 := hx0) (hxStar := hxStar)
                  n hn (hhat n hn) ω j) ∂setup.P) ∧
        (∀ m (hm : m + 1 ≤ setup.s) (ω : Ω) (i : ι),
          (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 (m + 1) ω).yMem i =
            if _ : i = setup.ξ (0 + ((m + 1) - 1)) ω then
              setup.gradPsiOnAt z i
                ⟨setup.xMemAfterSampleAtState (m + 1) (Nat.succ_pos m) hm
                    (setup.ξ (0 + ((m + 1) - 1)) ω) i
                    (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 m ω),
                  hsource m hm ω i⟩
            else
              (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 m ω).yMem i)) :
    lemma_6_13_sourceConclusion setup z x0 xStar xMem0 yMem0 hz hx0 hxMem0 := by
  -- Source formula leaf: instantiate Eq. (6.6.31) with `hprox45` and
  -- `h630_delta2`, use the curvature bounds in `hcurv` for
  -- Eqs. (6.6.35)-(6.6.36), then telescope with the parameter side conditions.
  have hGammaCoeffNonneg :
      ∀ t, 1 ≤ t → t ≤ setup.s → 0 ≤ setup.γSeq t := hγSeq_nonneg
  have hEtaCoeffTelescope :
      ∀ A : ℕ → ℝ, (∀ n, 1 ≤ n → n < setup.s → 0 ≤ A n) →
        Finset.sum (Finset.Icc 1 setup.s)
            (fun t =>
              setup.γSeq t * setup.ηSeq t * A (t - 1) -
                setup.γSeq t * (1 + setup.ηSeq t) * A t) ≤
          setup.γSeq 1 * setup.ηSeq 1 * A 0 -
            setup.γSeq setup.s * (1 + setup.ηSeq setup.s) * A setup.s := by
    intro A hA
    exact lemma_6_13_eta_weight_telescope setup A hs hA hparam22
  have hTauCoeffTelescope :
      ∀ A : ℕ → ℝ, (∀ n, 1 ≤ n → n < setup.s → 0 ≤ A n) →
        Finset.sum (Finset.Icc 1 setup.s)
            (fun t =>
              setup.γSeq t * ((1 + setup.τSeq t) - (Fintype.card ι : ℝ)⁻¹) *
                  A (t - 1) -
                setup.γSeq t * (1 + setup.τSeq t) * A t) ≤
          setup.γSeq 1 * ((1 + setup.τSeq 1) - (Fintype.card ι : ℝ)⁻¹) * A 0 -
            setup.γSeq setup.s * (1 + setup.τSeq setup.s) * A setup.s := by
    intro A hA
    exact lemma_6_13_tau_weight_telescope setup A hs hA hparam21
  have hPsiCurv :
      ∀ i (x y : {x : E // x ∈ setup.X}),
        setup.μ / 2 * ‖x.1 - y.1‖ ^ 2 ≤ setup.psiBregmanAt z i x y ∧
          setup.psiBregmanAt z i x y ≤ setup.Lhat / 2 * ‖x.1 - y.1‖ ^ 2 := by
    intro i x y
    exact setup.psiBregmanAt_curvature_bounds z hcurv.1 i x y
  have hXMem_mem :
      ∀ n, n ≤ setup.s → ∀ ω : Ω, ∀ i : ι,
        (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω).xMem i ∈
          setup.X :=
    setup.ambientFixedInnerProcess_xMem_mem_of_sourceDomain
      0 z x0 xMem0 yMem0 hz hx0 hxMem0 hsource
  have hYMem_grad :
      ∀ n (hn : n ≤ setup.s) (ω : Ω) (i : ι),
        (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω).yMem i =
          setup.gradPsiOnAt z i
            ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω).xMem i,
              hXMem_mem n hn ω i⟩ := by
    intro n hn ω i
    simpa [hXMem_mem] using
      setup.ambientFixedInnerProcess_yMem_gradPsiOnAt_of_initial
        0 z x0 xMem0 yMem0 hz hx0 hxMem0 hsource hgradMem0 n hn ω i
  have hDelta2Weighted :
      Finset.sum Finset.univ
          (fun n : {n : ℕ // n < setup.s} =>
            setup.γSeq (n.1 + 1) *
              ∫ ω : Ω,
                ambientFixedDelta2CurrentKernel
                  (setup := setup) (offset := 0) (z := z) (x0 := x0)
                  (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
                  (hz := hz) (hx0 := hx0) (hxStar := hxStar)
                  n.1 (Nat.succ_le_of_lt n.2) (hhat n.1 (Nat.succ_le_of_lt n.2))
                  ω (setup.ξ n.1 ω) ∂setup.P) =
        Finset.sum Finset.univ
          (fun n : {n : ℕ // n < setup.s} =>
            setup.γSeq (n.1 + 1) *
              ∫ ω : Ω,
                RandomizedAcceleratedProximalPointSetup.currentIndexAverage
                  (fun j : ι =>
                    ambientFixedDelta2CurrentKernel
                      (setup := setup) (offset := 0) (z := z) (x0 := x0)
                      (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
                      (hz := hz) (hx0 := hx0) (hxStar := hxStar)
                      n.1 (Nat.succ_le_of_lt n.2) (hhat n.1 (Nat.succ_le_of_lt n.2))
                      ω j) ∂setup.P) := by
    refine Finset.sum_congr rfl ?_
    intro n _hn
    rw [(h630_delta2 n.1 (Nat.succ_le_of_lt n.2)).1]
  have hProxWeightedPointwise :
      ∀ ω : Ω,
        Finset.sum Finset.univ
            (fun n : {n : ℕ // n < setup.s} =>
              setup.γSeq (n.1 + 1) *
                (let stPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n.1 ω
                  let stNext :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (n.1 + 1) ω
                  let yTilde : ι → E :=
                    fun i =>
                      (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
                        stPrev.yMem i
                  setup.phiAt z stNext.x - setup.phiAt z xStar +
                    ⟪(Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ yTilde,
                      stNext.x - xStar⟫_ℝ)) ≤
          Finset.sum Finset.univ
            (fun n : {n : ℕ // n < setup.s} =>
              setup.γSeq (n.1 + 1) *
                (let stPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n.1 ω
                  let stNext :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (n.1 + 1) ω
                  setup.ηSeq (n.1 + 1) *
                      ((setup.μ / 2) * ‖xStar - stPrev.x‖ ^ 2) -
                    (1 + setup.ηSeq (n.1 + 1)) *
                      ((setup.μ / 2) * ‖xStar - stNext.x‖ ^ 2) -
                    setup.ηSeq (n.1 + 1) *
                      ((setup.μ / 2) * ‖stNext.x - stPrev.x‖ ^ 2))) := by
    intro ω
    refine Finset.sum_le_sum ?_
    intro n _hn
    exact mul_le_mul_of_nonneg_left
      (hprox45 n.1 (Nat.succ_le_of_lt n.2) ω)
      (hGammaCoeffNonneg (n.1 + 1) (Nat.succ_pos n.1) (Nat.succ_le_of_lt n.2))
  have hEtaDistanceTelescopePointwise :
      ∀ ω : Ω,
        Finset.sum (Finset.Icc 1 setup.s)
            (fun t =>
              setup.γSeq t * setup.ηSeq t *
                  ((setup.μ / 2) *
                    ‖xStar -
                      (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        (t - 1) ω).x‖ ^ 2) -
                setup.γSeq t * (1 + setup.ηSeq t) *
                  ((setup.μ / 2) *
                    ‖xStar -
                      (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        t ω).x‖ ^ 2)) ≤
          setup.γSeq 1 * setup.ηSeq 1 *
              ((setup.μ / 2) *
                ‖xStar -
                  (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                    0 ω).x‖ ^ 2) -
            setup.γSeq setup.s * (1 + setup.ηSeq setup.s) *
              ((setup.μ / 2) *
                ‖xStar -
                  (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                    setup.s ω).x‖ ^ 2) := by
    intro ω
    exact hEtaCoeffTelescope
      (fun n =>
        (setup.μ / 2) *
          ‖xStar -
            (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω).x‖ ^ 2)
      (by
        intro n _hn _hnlt
        exact mul_nonneg
          (div_nonneg (le_of_lt setup.hμ_pos) (by norm_num))
          (sq_nonneg _))
  have hTauPsiTelescopePointwise :
      ∀ (ω : Ω) (i : ι),
        let A : ℕ → ℝ := fun n =>
          if hn : n ≤ setup.s then
            setup.psiBregmanAt z i
              ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω).xMem i,
                hXMem_mem n hn ω i⟩
              ⟨xStar, hxStar⟩
          else 0
        Finset.sum (Finset.Icc 1 setup.s)
            (fun t =>
              setup.γSeq t * ((1 + setup.τSeq t) - (Fintype.card ι : ℝ)⁻¹) *
                  A (t - 1) -
                setup.γSeq t * (1 + setup.τSeq t) * A t) ≤
          setup.γSeq 1 * ((1 + setup.τSeq 1) - (Fintype.card ι : ℝ)⁻¹) * A 0 -
            setup.γSeq setup.s * (1 + setup.τSeq setup.s) * A setup.s := by
    intro ω i
    exact hTauCoeffTelescope
      (fun n =>
        if hn : n ≤ setup.s then
          setup.psiBregmanAt z i
            ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω).xMem i,
              hXMem_mem n hn ω i⟩
            ⟨xStar, hxStar⟩
        else 0)
      (by
        intro n _hn hnlt
        change 0 ≤
          (if hn : n ≤ setup.s then
            setup.psiBregmanAt z i
              ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω).xMem i,
                hXMem_mem n hn ω i⟩
              ⟨xStar, hxStar⟩
          else 0)
        rw [dif_pos (Nat.le_of_lt hnlt)]
        have hquad_nonneg :
            0 ≤
              setup.μ / 2 *
                ‖(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω).xMem i -
                    xStar‖ ^ 2 :=
          mul_nonneg
            (div_nonneg (le_of_lt setup.hμ_pos) (by norm_num))
            (sq_nonneg _)
        exact le_trans hquad_nonneg
          (hPsiCurv i
            ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω).xMem i,
              hXMem_mem n (Nat.le_of_lt hnlt) ω i⟩
            ⟨xStar, hxStar⟩).1)
  have hProxWeightedPointwiseIcc :
      ∀ ω : Ω,
        Finset.sum (Finset.Icc 1 setup.s)
            (fun t =>
              setup.γSeq t *
                (let stPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (t - 1) ω
                  let stNext :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω
                  let yTilde : ι → E :=
                    fun i =>
                      (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
                        stPrev.yMem i
                  setup.phiAt z stNext.x - setup.phiAt z xStar +
                    ⟪(Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ yTilde,
                      stNext.x - xStar⟫_ℝ)) ≤
          Finset.sum (Finset.Icc 1 setup.s)
            (fun t =>
              setup.γSeq t *
                (let stPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (t - 1) ω
                  let stNext :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω
                  setup.ηSeq t *
                      ((setup.μ / 2) * ‖xStar - stPrev.x‖ ^ 2) -
                    (1 + setup.ηSeq t) *
                      ((setup.μ / 2) * ‖xStar - stNext.x‖ ^ 2) -
                    setup.ηSeq t *
                      ((setup.μ / 2) * ‖stNext.x - stPrev.x‖ ^ 2))) := by
    intro ω
    have hleft :
        Finset.sum Finset.univ
            (fun n : {n : ℕ // n < setup.s} =>
              setup.γSeq (n.1 + 1) *
                (let stPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n.1 ω
                  let stNext :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (n.1 + 1) ω
                  let yTilde : ι → E :=
                    fun i =>
                      (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
                        stPrev.yMem i
                  setup.phiAt z stNext.x - setup.phiAt z xStar +
                    ⟪(Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ yTilde,
                      stNext.x - xStar⟫_ℝ)) =
          Finset.sum (Finset.Icc 1 setup.s)
            (fun t =>
              setup.γSeq t *
                (let stPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (t - 1) ω
                  let stNext :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω
                  let yTilde : ι → E :=
                    fun i =>
                      (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
                        stPrev.yMem i
                  setup.phiAt z stNext.x - setup.phiAt z xStar +
                    ⟪(Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ yTilde,
                      stNext.x - xStar⟫_ℝ)) := by
      simpa [Nat.succ_sub_one] using
        (sum_univ_subtype_lt_succ_eq_sum_Icc_one
          setup.s
          (fun t =>
            setup.γSeq t *
              (let stPrev :=
                  setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                    (t - 1) ω
                let stNext :=
                  setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω
                let yTilde : ι → E :=
                  fun i =>
                    (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
                      stPrev.yMem i
                setup.phiAt z stNext.x - setup.phiAt z xStar +
                  ⟪(Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ yTilde,
                    stNext.x - xStar⟫_ℝ)))
    have hright :
        Finset.sum Finset.univ
            (fun n : {n : ℕ // n < setup.s} =>
              setup.γSeq (n.1 + 1) *
                (let stPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n.1 ω
                  let stNext :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (n.1 + 1) ω
                  setup.ηSeq (n.1 + 1) *
                      ((setup.μ / 2) * ‖xStar - stPrev.x‖ ^ 2) -
                    (1 + setup.ηSeq (n.1 + 1)) *
                      ((setup.μ / 2) * ‖xStar - stNext.x‖ ^ 2) -
                    setup.ηSeq (n.1 + 1) *
                      ((setup.μ / 2) * ‖stNext.x - stPrev.x‖ ^ 2))) =
          Finset.sum (Finset.Icc 1 setup.s)
            (fun t =>
              setup.γSeq t *
                (let stPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (t - 1) ω
                  let stNext :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω
                  setup.ηSeq t *
                      ((setup.μ / 2) * ‖xStar - stPrev.x‖ ^ 2) -
                    (1 + setup.ηSeq t) *
                      ((setup.μ / 2) * ‖xStar - stNext.x‖ ^ 2) -
                    setup.ηSeq t *
                      ((setup.μ / 2) * ‖stNext.x - stPrev.x‖ ^ 2))) := by
      simpa [Nat.succ_sub_one] using
        (sum_univ_subtype_lt_succ_eq_sum_Icc_one
          setup.s
          (fun t =>
            setup.γSeq t *
              (let stPrev :=
                  setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                    (t - 1) ω
                let stNext :=
                  setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω
                setup.ηSeq t *
                    ((setup.μ / 2) * ‖xStar - stPrev.x‖ ^ 2) -
                  (1 + setup.ηSeq t) *
                    ((setup.μ / 2) * ‖xStar - stNext.x‖ ^ 2) -
                  setup.ηSeq t *
                    ((setup.μ / 2) * ‖stNext.x - stPrev.x‖ ^ 2))))
    have h := hProxWeightedPointwise ω
    rw [hleft, hright] at h
    exact h
  have hDelta2WeightedIcc :
      Finset.sum (Finset.Icc 1 setup.s).attach
          (fun t =>
            setup.γSeq t.1 *
              ∫ ω : Ω,
                ambientFixedDelta2CurrentKernel
                  (setup := setup) (offset := 0) (z := z) (x0 := x0)
                  (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
                  (hz := hz) (hx0 := hx0) (hxStar := hxStar)
                  (t.1 - 1)
                  (by
                    have ht := (Finset.mem_Icc.mp t.2).2
                    simpa [Nat.sub_add_cancel (Finset.mem_Icc.mp t.2).1] using ht)
                  (hhat (t.1 - 1)
                    (by
                      have ht := (Finset.mem_Icc.mp t.2).2
                      simpa [Nat.sub_add_cancel (Finset.mem_Icc.mp t.2).1] using ht))
                  ω (setup.ξ (t.1 - 1) ω) ∂setup.P) =
        Finset.sum (Finset.Icc 1 setup.s).attach
          (fun t =>
            setup.γSeq t.1 *
              ∫ ω : Ω,
                RandomizedAcceleratedProximalPointSetup.currentIndexAverage
                  (fun j : ι =>
                    ambientFixedDelta2CurrentKernel
                      (setup := setup) (offset := 0) (z := z) (x0 := x0)
                      (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
                      (hz := hz) (hx0 := hx0) (hxStar := hxStar)
                      (t.1 - 1)
                      (by
                        have ht := (Finset.mem_Icc.mp t.2).2
                        simpa [Nat.sub_add_cancel (Finset.mem_Icc.mp t.2).1] using ht)
                      (hhat (t.1 - 1)
                        (by
                          have ht := (Finset.mem_Icc.mp t.2).2
                          simpa [Nat.sub_add_cancel (Finset.mem_Icc.mp t.2).1] using ht))
                      ω j) ∂setup.P) := by
    have hleft :
        Finset.sum Finset.univ
            (fun n : {n : ℕ // n < setup.s} =>
              setup.γSeq (n.1 + 1) *
                ∫ ω : Ω,
                  ambientFixedDelta2CurrentKernel
                    (setup := setup) (offset := 0) (z := z) (x0 := x0)
                    (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
                    (hz := hz) (hx0 := hx0) (hxStar := hxStar)
                    n.1 (Nat.succ_le_of_lt n.2) (hhat n.1 (Nat.succ_le_of_lt n.2))
                    ω (setup.ξ n.1 ω) ∂setup.P) =
          Finset.sum (Finset.Icc 1 setup.s).attach
            (fun t =>
              setup.γSeq t.1 *
                ∫ ω : Ω,
                  ambientFixedDelta2CurrentKernel
                    (setup := setup) (offset := 0) (z := z) (x0 := x0)
                    (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
                    (hz := hz) (hx0 := hx0) (hxStar := hxStar)
                    (t.1 - 1)
                    (by
                      have ht := (Finset.mem_Icc.mp t.2).2
                      simpa [Nat.sub_add_cancel (Finset.mem_Icc.mp t.2).1] using ht)
                    (hhat (t.1 - 1)
                      (by
                        have ht := (Finset.mem_Icc.mp t.2).2
                        simpa [Nat.sub_add_cancel (Finset.mem_Icc.mp t.2).1] using ht))
                    ω (setup.ξ (t.1 - 1) ω) ∂setup.P) := by
      simpa [Nat.succ_sub_one] using
        (sum_univ_subtype_lt_succ_eq_sum_Icc_one_attach
          setup.s
          (fun t ht1 hts =>
            setup.γSeq t *
              ∫ ω : Ω,
                ambientFixedDelta2CurrentKernel
                  (setup := setup) (offset := 0) (z := z) (x0 := x0)
                  (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
                  (hz := hz) (hx0 := hx0) (hxStar := hxStar)
                  (t - 1)
                  (by simpa [Nat.sub_add_cancel ht1] using hts)
                  (hhat (t - 1) (by simpa [Nat.sub_add_cancel ht1] using hts))
                  ω (setup.ξ (t - 1) ω) ∂setup.P))
    have hright :
        Finset.sum Finset.univ
            (fun n : {n : ℕ // n < setup.s} =>
              setup.γSeq (n.1 + 1) *
                ∫ ω : Ω,
                  RandomizedAcceleratedProximalPointSetup.currentIndexAverage
                    (fun j : ι =>
                      ambientFixedDelta2CurrentKernel
                        (setup := setup) (offset := 0) (z := z) (x0 := x0)
                        (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
                        (hz := hz) (hx0 := hx0) (hxStar := hxStar)
                        n.1 (Nat.succ_le_of_lt n.2)
                        (hhat n.1 (Nat.succ_le_of_lt n.2))
                        ω j) ∂setup.P) =
          Finset.sum (Finset.Icc 1 setup.s).attach
            (fun t =>
              setup.γSeq t.1 *
                ∫ ω : Ω,
                  RandomizedAcceleratedProximalPointSetup.currentIndexAverage
                    (fun j : ι =>
                      ambientFixedDelta2CurrentKernel
                        (setup := setup) (offset := 0) (z := z) (x0 := x0)
                        (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
                        (hz := hz) (hx0 := hx0) (hxStar := hxStar)
                        (t.1 - 1)
                        (by
                          have ht := (Finset.mem_Icc.mp t.2).2
                          simpa [Nat.sub_add_cancel (Finset.mem_Icc.mp t.2).1] using ht)
                        (hhat (t.1 - 1)
                          (by
                            have ht := (Finset.mem_Icc.mp t.2).2
                            simpa [Nat.sub_add_cancel (Finset.mem_Icc.mp t.2).1] using ht))
                        ω j) ∂setup.P) := by
      simpa [Nat.succ_sub_one] using
        (sum_univ_subtype_lt_succ_eq_sum_Icc_one_attach
          setup.s
          (fun t ht1 hts =>
            setup.γSeq t *
              ∫ ω : Ω,
                RandomizedAcceleratedProximalPointSetup.currentIndexAverage
                  (fun j : ι =>
                    ambientFixedDelta2CurrentKernel
                      (setup := setup) (offset := 0) (z := z) (x0 := x0)
                      (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
                      (hz := hz) (hx0 := hx0) (hxStar := hxStar)
                      (t - 1)
                      (by simpa [Nat.sub_add_cancel ht1] using hts)
                      (hhat (t - 1) (by simpa [Nat.sub_add_cancel ht1] using hts))
                      ω j) ∂setup.P))
    rw [← hleft, ← hright]
    exact hDelta2Weighted
  have hProxEtaTelescopePointwise :
      ∀ ω : Ω,
        Finset.sum (Finset.Icc 1 setup.s)
            (fun t =>
              setup.γSeq t *
                (let stPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (t - 1) ω
                  let stNext :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω
                  let yTilde : ι → E :=
                    fun i =>
                      (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
                        stPrev.yMem i
                  setup.phiAt z stNext.x - setup.phiAt z xStar +
                    ⟪(Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ yTilde,
                      stNext.x - xStar⟫_ℝ)) ≤
          setup.γSeq 1 * setup.ηSeq 1 *
              ((setup.μ / 2) *
                ‖xStar -
                  (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                    0 ω).x‖ ^ 2) -
            setup.γSeq setup.s * (1 + setup.ηSeq setup.s) *
              ((setup.μ / 2) *
                ‖xStar -
                  (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                    setup.s ω).x‖ ^ 2) -
            Finset.sum (Finset.Icc 1 setup.s)
              (fun t =>
                setup.γSeq t * setup.ηSeq t *
                  ((setup.μ / 2) *
                    ‖(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        t ω).x -
                      (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        (t - 1) ω).x‖ ^ 2)) := by
    intro ω
    have hp := hProxWeightedPointwiseIcc ω
    have he := hEtaDistanceTelescopePointwise ω
    have hRhs :
        Finset.sum (Finset.Icc 1 setup.s)
            (fun t =>
              setup.γSeq t *
                (let stPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (t - 1) ω
                  let stNext :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω
                  setup.ηSeq t *
                      ((setup.μ / 2) * ‖xStar - stPrev.x‖ ^ 2) -
                    (1 + setup.ηSeq t) *
                      ((setup.μ / 2) * ‖xStar - stNext.x‖ ^ 2) -
                    setup.ηSeq t *
                      ((setup.μ / 2) * ‖stNext.x - stPrev.x‖ ^ 2))) =
          Finset.sum (Finset.Icc 1 setup.s)
            (fun t =>
              setup.γSeq t * setup.ηSeq t *
                  ((setup.μ / 2) *
                    ‖xStar -
                      (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        (t - 1) ω).x‖ ^ 2) -
                setup.γSeq t * (1 + setup.ηSeq t) *
                  ((setup.μ / 2) *
                    ‖xStar -
                      (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        t ω).x‖ ^ 2)) -
            Finset.sum (Finset.Icc 1 setup.s)
              (fun t =>
                setup.γSeq t * setup.ηSeq t *
                  ((setup.μ / 2) *
                    ‖(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        t ω).x -
                      (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        (t - 1) ω).x‖ ^ 2)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro t _ht
      ring
    calc
      Finset.sum (Finset.Icc 1 setup.s)
          (fun t =>
            setup.γSeq t *
              (let stPrev :=
                  setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                    (t - 1) ω
                let stNext :=
                  setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω
                let yTilde : ι → E :=
                  fun i =>
                    (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
                      stPrev.yMem i
                setup.phiAt z stNext.x - setup.phiAt z xStar +
                  ⟪(Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ yTilde,
                    stNext.x - xStar⟫_ℝ))
          ≤ Finset.sum (Finset.Icc 1 setup.s)
            (fun t =>
              setup.γSeq t *
                (let stPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (t - 1) ω
                  let stNext :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω
                  setup.ηSeq t *
                      ((setup.μ / 2) * ‖xStar - stPrev.x‖ ^ 2) -
                    (1 + setup.ηSeq t) *
                      ((setup.μ / 2) * ‖xStar - stNext.x‖ ^ 2) -
                    setup.ηSeq t *
                      ((setup.μ / 2) * ‖stNext.x - stPrev.x‖ ^ 2))) := hp
      _ =
          Finset.sum (Finset.Icc 1 setup.s)
            (fun t =>
              setup.γSeq t * setup.ηSeq t *
                  ((setup.μ / 2) *
                    ‖xStar -
                      (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        (t - 1) ω).x‖ ^ 2) -
                setup.γSeq t * (1 + setup.ηSeq t) *
                  ((setup.μ / 2) *
                    ‖xStar -
                      (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        t ω).x‖ ^ 2)) -
            Finset.sum (Finset.Icc 1 setup.s)
              (fun t =>
                setup.γSeq t * setup.ηSeq t *
                  ((setup.μ / 2) *
                    ‖(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        t ω).x -
                      (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        (t - 1) ω).x‖ ^ 2)) := hRhs
      _ ≤
          setup.γSeq 1 * setup.ηSeq 1 *
              ((setup.μ / 2) *
                ‖xStar -
                  (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                    0 ω).x‖ ^ 2) -
            setup.γSeq setup.s * (1 + setup.ηSeq setup.s) *
              ((setup.μ / 2) *
                ‖xStar -
                  (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                    setup.s ω).x‖ ^ 2) -
            Finset.sum (Finset.Icc 1 setup.s)
              (fun t =>
                setup.γSeq t * setup.ηSeq t *
                  ((setup.μ / 2) *
                    ‖(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        t ω).x -
                      (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        (t - 1) ω).x‖ ^ 2)) :=
        sub_le_sub_right he _
  have hTauPsiTelescopeSummedPointwise :
      ∀ ω : Ω,
        Finset.sum Finset.univ
            (fun i : ι =>
              let A : ℕ → ℝ := fun n =>
                if hn : n ≤ setup.s then
                  setup.psiBregmanAt z i
                    ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        n ω).xMem i,
                      hXMem_mem n hn ω i⟩
                    ⟨xStar, hxStar⟩
                else 0
              Finset.sum (Finset.Icc 1 setup.s)
                (fun t =>
                  setup.γSeq t *
                      ((1 + setup.τSeq t) - (Fintype.card ι : ℝ)⁻¹) *
                      A (t - 1) -
                    setup.γSeq t * (1 + setup.τSeq t) * A t)) ≤
          Finset.sum Finset.univ
            (fun i : ι =>
              let A : ℕ → ℝ := fun n =>
                if hn : n ≤ setup.s then
                  setup.psiBregmanAt z i
                    ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        n ω).xMem i,
                      hXMem_mem n hn ω i⟩
                    ⟨xStar, hxStar⟩
                else 0
              setup.γSeq 1 *
                  ((1 + setup.τSeq 1) - (Fintype.card ι : ℝ)⁻¹) * A 0 -
                setup.γSeq setup.s * (1 + setup.τSeq setup.s) * A setup.s) := by
    intro ω
    refine Finset.sum_le_sum ?_
    intro i _hi
    exact hTauPsiTelescopePointwise ω i
  have hInitialPsiUpper :
      ∀ i : ι,
        setup.psiBregmanAt z i ⟨xMem0 i, hxMem0 i⟩ ⟨xStar, hxStar⟩ ≤
          setup.Lhat / 2 * ‖xMem0 i - xStar‖ ^ 2 := by
    intro i
    exact (hPsiCurv i ⟨xMem0 i, hxMem0 i⟩ ⟨xStar, hxStar⟩).2
  have hTerminalPsiLower :
      ∀ (ω : Ω) (i : ι),
        setup.μ / 2 *
            ‖(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                setup.s ω).xMem i - xStar‖ ^ 2 ≤
          setup.psiBregmanAt z i
            ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                setup.s ω).xMem i,
              hXMem_mem setup.s le_rfl ω i⟩
            ⟨xStar, hxStar⟩ := by
    intro ω i
    exact
      (hPsiCurv i
        ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
            setup.s ω).xMem i,
          hXMem_mem setup.s le_rfl ω i⟩
        ⟨xStar, hxStar⟩).1
  have hEq631PointwiseTelescope :
      ∀ ω : Ω,
        (Finset.sum (Finset.Icc 1 setup.s)
            (fun t =>
              setup.γSeq t *
                (let stPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (t - 1) ω
                  let stNext :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω
                  let yTilde : ι → E :=
                    fun i =>
                      (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
                        stPrev.yMem i
                  setup.phiAt z stNext.x - setup.phiAt z xStar +
                    ⟪(Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ yTilde,
                      stNext.x - xStar⟫_ℝ)) +
          Finset.sum Finset.univ
            (fun i : ι =>
              let A : ℕ → ℝ := fun n =>
                if hn : n ≤ setup.s then
                  setup.psiBregmanAt z i
                    ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        n ω).xMem i,
                      hXMem_mem n hn ω i⟩
                    ⟨xStar, hxStar⟩
                else 0
              Finset.sum (Finset.Icc 1 setup.s)
                (fun t =>
                  setup.γSeq t *
                      ((1 + setup.τSeq t) - (Fintype.card ι : ℝ)⁻¹) *
                      A (t - 1) -
                    setup.γSeq t * (1 + setup.τSeq t) * A t))) ≤
          (setup.γSeq 1 * setup.ηSeq 1 *
              ((setup.μ / 2) *
                ‖xStar -
                  (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                    0 ω).x‖ ^ 2) -
            setup.γSeq setup.s * (1 + setup.ηSeq setup.s) *
              ((setup.μ / 2) *
                ‖xStar -
                  (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                    setup.s ω).x‖ ^ 2) -
            Finset.sum (Finset.Icc 1 setup.s)
              (fun t =>
                setup.γSeq t * setup.ηSeq t *
                  ((setup.μ / 2) *
                    ‖(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        t ω).x -
                      (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        (t - 1) ω).x‖ ^ 2))) +
          Finset.sum Finset.univ
            (fun i : ι =>
              let A : ℕ → ℝ := fun n =>
                if hn : n ≤ setup.s then
                  setup.psiBregmanAt z i
                    ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        n ω).xMem i,
                      hXMem_mem n hn ω i⟩
                    ⟨xStar, hxStar⟩
                else 0
              setup.γSeq 1 *
                  ((1 + setup.τSeq 1) - (Fintype.card ι : ℝ)⁻¹) * A 0 -
                setup.γSeq setup.s * (1 + setup.τSeq setup.s) * A setup.s) := by
    intro ω
    exact add_le_add
      (hProxEtaTelescopePointwise ω)
      (hTauPsiTelescopeSummedPointwise ω)
  have hEq631EndpointTelescope :
      ∀ ω : Ω,
        (Finset.sum (Finset.Icc 1 setup.s)
            (fun t =>
              setup.γSeq t *
                (let stPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (t - 1) ω
                  let stNext :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω
                  let yTilde : ι → E :=
                    fun i =>
                      (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
                        stPrev.yMem i
                  setup.phiAt z stNext.x - setup.phiAt z xStar +
                    ⟪(Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ yTilde,
                      stNext.x - xStar⟫_ℝ)) +
          Finset.sum Finset.univ
            (fun i : ι =>
              let A : ℕ → ℝ := fun n =>
                if hn : n ≤ setup.s then
                  setup.psiBregmanAt z i
                    ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        n ω).xMem i,
                      hXMem_mem n hn ω i⟩
                    ⟨xStar, hxStar⟩
                else 0
              Finset.sum (Finset.Icc 1 setup.s)
                (fun t =>
                  setup.γSeq t *
                      ((1 + setup.τSeq t) - (Fintype.card ι : ℝ)⁻¹) *
                      A (t - 1) -
                    setup.γSeq t * (1 + setup.τSeq t) * A t))) ≤
          (setup.γSeq 1 * setup.ηSeq 1 *
              ((setup.μ / 2) *
                ‖xStar -
                  (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                    0 ω).x‖ ^ 2) -
            setup.γSeq setup.s * (1 + setup.ηSeq setup.s) *
              ((setup.μ / 2) *
                ‖xStar -
                  (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                    setup.s ω).x‖ ^ 2) -
            Finset.sum (Finset.Icc 1 setup.s)
              (fun t =>
                setup.γSeq t * setup.ηSeq t *
                  ((setup.μ / 2) *
                    ‖(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        t ω).x -
                      (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        (t - 1) ω).x‖ ^ 2))) +
          Finset.sum Finset.univ
            (fun i : ι =>
              setup.γSeq 1 *
                  ((1 + setup.τSeq 1) - (Fintype.card ι : ℝ)⁻¹) *
                  setup.psiBregmanAt z i ⟨xMem0 i, hxMem0 i⟩ ⟨xStar, hxStar⟩ -
                setup.γSeq setup.s * (1 + setup.τSeq setup.s) *
                  setup.psiBregmanAt z i
                    ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        setup.s ω).xMem i,
                      hXMem_mem setup.s le_rfl ω i⟩
                    ⟨xStar, hxStar⟩) := by
    intro ω
    simpa [RandomizedAcceleratedProximalPointSetup.ambientFixedInnerProcess_zero]
      using hEq631PointwiseTelescope ω
  have hInvCard_le_one : (Fintype.card ι : ℝ)⁻¹ ≤ 1 := by
    have hcard_one : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos : 0 < Fintype.card ι))
    exact inv_le_one_of_one_le₀ hcard_one
  have hInitialMemoryCoeff_nonneg :
      0 ≤ setup.γSeq 1 * ((1 + setup.τSeq 1) - (Fintype.card ι : ℝ)⁻¹) := by
    have hγ1 : 0 ≤ setup.γSeq 1 := hγSeq_nonneg 1 le_rfl (by simpa using hs)
    have hτ1 : 0 ≤ setup.τSeq 1 := setup.hτSeq_nonneg 1 le_rfl (by simpa using hs)
    have hbracket : 0 ≤ (1 + setup.τSeq 1) - (Fintype.card ι : ℝ)⁻¹ := by
      nlinarith
    exact mul_nonneg hγ1 hbracket
  have hTerminalMemoryCoeff_nonneg :
      0 ≤ setup.γSeq setup.s * (1 + setup.τSeq setup.s) := by
    have hγs : 0 ≤ setup.γSeq setup.s := hγSeq_nonneg setup.s hs le_rfl
    have hτs : 0 ≤ setup.τSeq setup.s := setup.hτSeq_nonneg setup.s hs le_rfl
    exact mul_nonneg hγs (by nlinarith)
  have hLhat_nonneg : 0 ≤ setup.Lhat := by
    rw [setup.Lhat_def]
    nlinarith [setup.hμ_pos, setup.hμ_le_L]
  have hInitialMemorySqCoeff_nonneg :
      0 ≤ setup.γSeq 1 * ((1 + setup.τSeq 1) - (Fintype.card ι : ℝ)⁻¹) *
        setup.Lhat / 2 := by
    nlinarith [mul_nonneg hInitialMemoryCoeff_nonneg hLhat_nonneg]
  have hMemoryEndpointBound :
      ∀ ω : Ω,
        Finset.sum Finset.univ
            (fun i : ι =>
              setup.γSeq 1 *
                  ((1 + setup.τSeq 1) - (Fintype.card ι : ℝ)⁻¹) *
                  setup.psiBregmanAt z i ⟨xMem0 i, hxMem0 i⟩ ⟨xStar, hxStar⟩ -
                setup.γSeq setup.s * (1 + setup.τSeq setup.s) *
                  setup.psiBregmanAt z i
                    ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        setup.s ω).xMem i,
                      hXMem_mem setup.s le_rfl ω i⟩
                    ⟨xStar, hxStar⟩) ≤
          Finset.sum Finset.univ
            (fun i : ι =>
              setup.γSeq 1 *
                    ((1 + setup.τSeq 1) - (Fintype.card ι : ℝ)⁻¹) *
                    setup.Lhat / 2 * ‖xMem0 i - xStar‖ ^ 2 -
                setup.μ * setup.γSeq setup.s * (1 + setup.τSeq setup.s) / 4 *
                  ‖(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      setup.s ω).xMem i - xStar‖ ^ 2) := by
    intro ω
    refine Finset.sum_le_sum ?_
    intro i _hi
    have hinit :
        setup.γSeq 1 *
            ((1 + setup.τSeq 1) - (Fintype.card ι : ℝ)⁻¹) *
            setup.psiBregmanAt z i ⟨xMem0 i, hxMem0 i⟩ ⟨xStar, hxStar⟩ ≤
          setup.γSeq 1 *
              ((1 + setup.τSeq 1) - (Fintype.card ι : ℝ)⁻¹) *
              setup.Lhat / 2 * ‖xMem0 i - xStar‖ ^ 2 := by
      have h :=
        mul_le_mul_of_nonneg_left (hInitialPsiUpper i) hInitialMemoryCoeff_nonneg
      nlinarith
    have hterm :
        setup.μ * setup.γSeq setup.s * (1 + setup.τSeq setup.s) / 4 *
            ‖(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                setup.s ω).xMem i - xStar‖ ^ 2 ≤
          setup.γSeq setup.s * (1 + setup.τSeq setup.s) *
            setup.psiBregmanAt z i
              ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                  setup.s ω).xMem i,
                hXMem_mem setup.s le_rfl ω i⟩
              ⟨xStar, hxStar⟩ := by
      let C : ℝ := setup.γSeq setup.s * (1 + setup.τSeq setup.s)
      let N : ℝ :=
        ‖(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
            setup.s ω).xMem i - xStar‖ ^ 2
      let B : ℝ :=
        setup.psiBregmanAt z i
          ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
              setup.s ω).xMem i,
            hXMem_mem setup.s le_rfl ω i⟩
          ⟨xStar, hxStar⟩
      have hscaled : C * (setup.μ / 2 * N) ≤ C * B := by
        simpa [C, N, B] using
          mul_le_mul_of_nonneg_left (hTerminalPsiLower ω i)
            hTerminalMemoryCoeff_nonneg
      have hquarter : setup.μ * C / 4 * N ≤ C * (setup.μ / 2 * N) := by
        have hC_nonneg : 0 ≤ C := by
          simpa [C] using hTerminalMemoryCoeff_nonneg
        have hN_nonneg : 0 ≤ N := by
          dsimp [N]
          exact sq_nonneg _
        have hprod_nonneg : 0 ≤ C * setup.μ * N := by
          exact mul_nonneg (mul_nonneg hC_nonneg (le_of_lt setup.hμ_pos)) hN_nonneg
        nlinarith [hprod_nonneg]
      calc
        setup.μ * setup.γSeq setup.s * (1 + setup.τSeq setup.s) / 4 *
              ‖(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                  setup.s ω).xMem i - xStar‖ ^ 2
            = setup.μ * C / 4 * N := by
                dsimp [C, N]
                ring
        _ ≤ C * (setup.μ / 2 * N) := hquarter
        _ ≤ C * B := hscaled
        _ =
            setup.γSeq setup.s * (1 + setup.τSeq setup.s) *
              setup.psiBregmanAt z i
                ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                    setup.s ω).xMem i,
                  hXMem_mem setup.s le_rfl ω i⟩
                ⟨xStar, hxStar⟩ := by
              simpa [C, B]
    nlinarith
  let qLeft : Ω → ℝ := (fun ω =>
    (Finset.sum (Finset.Icc 1 setup.s)
        (fun t =>
          setup.γSeq t *
            (let stPrev :=
                setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                  (t - 1) ω
              let stNext :=
                setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω
              let yTilde : ι → E :=
                fun i =>
                  (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
                    stPrev.yMem i
              setup.phiAt z stNext.x - setup.phiAt z xStar +
                ⟪(Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ yTilde,
                  stNext.x - xStar⟫_ℝ))) +
      (Finset.sum Finset.univ
        (fun i : ι =>
          let A : ℕ → ℝ := (fun n =>
            if hn : n ≤ setup.s then
              setup.psiBregmanAt z i
                ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                    n ω).xMem i,
                  hXMem_mem n hn ω i⟩
                ⟨xStar, hxStar⟩
            else 0)
          Finset.sum (Finset.Icc 1 setup.s)
            (fun t =>
              setup.γSeq t *
                  ((1 + setup.τSeq t) - (Fintype.card ι : ℝ)⁻¹) *
                  A (t - 1) -
                setup.γSeq t * (1 + setup.τSeq t) * A t))))
  let endpointCore : Ω → ℝ := fun ω =>
    setup.γSeq 1 * setup.ηSeq 1 *
        ((setup.μ / 2) *
          ‖xStar -
            (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
              0 ω).x‖ ^ 2) -
      setup.γSeq setup.s * (1 + setup.ηSeq setup.s) *
        ((setup.μ / 2) *
          ‖xStar -
            (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
              setup.s ω).x‖ ^ 2) -
      Finset.sum (Finset.Icc 1 setup.s)
        (fun t =>
          setup.γSeq t * setup.ηSeq t *
            ((setup.μ / 2) *
              ‖(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                  t ω).x -
                (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                  (t - 1) ω).x‖ ^ 2))
  let memoryEndpoint : Ω → ℝ := fun ω =>
    Finset.sum Finset.univ
      (fun i : ι =>
        setup.γSeq 1 *
            ((1 + setup.τSeq 1) - (Fintype.card ι : ℝ)⁻¹) *
            setup.psiBregmanAt z i ⟨xMem0 i, hxMem0 i⟩ ⟨xStar, hxStar⟩ -
          setup.γSeq setup.s * (1 + setup.τSeq setup.s) *
            setup.psiBregmanAt z i
              ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                  setup.s ω).xMem i,
                hXMem_mem setup.s le_rfl ω i⟩
              ⟨xStar, hxStar⟩)
  let memoryNormBound : Ω → ℝ := fun ω =>
    Finset.sum Finset.univ
      (fun i : ι =>
        setup.γSeq 1 *
              ((1 + setup.τSeq 1) - (Fintype.card ι : ℝ)⁻¹) *
              setup.Lhat / 2 * ‖xMem0 i - xStar‖ ^ 2 -
          setup.μ * setup.γSeq setup.s * (1 + setup.τSeq setup.s) / 4 *
            ‖(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                setup.s ω).xMem i - xStar‖ ^ 2)
  let weightedEtaStep : Ω → ℝ := fun ω =>
    Finset.sum (Finset.Icc 1 setup.s)
      (fun t =>
        setup.γSeq t * setup.ηSeq t *
          ((setup.μ / 2) *
            ‖(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                t ω).x -
              (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                (t - 1) ω).x‖ ^ 2))
  have hEq631EndpointTelescope_abbrev :
      ∀ ω : Ω, qLeft ω ≤ endpointCore ω + memoryEndpoint ω := by
    intro ω
    simpa [qLeft, endpointCore, memoryEndpoint] using hEq631EndpointTelescope ω
  have hMemoryEndpointBound_abbrev :
      ∀ ω : Ω, memoryEndpoint ω ≤ memoryNormBound ω := by
    intro ω
    simpa [memoryEndpoint, memoryNormBound] using hMemoryEndpointBound ω
  have hEq631EndpointWithMemoryBound :
      ∀ ω : Ω, qLeft ω ≤ endpointCore ω + memoryNormBound ω := by
    intro ω
    linarith [hEq631EndpointTelescope_abbrev ω, hMemoryEndpointBound_abbrev ω]
  have hEq631WeightedQDeltaResidualBridge :
      ∃ Q delta : ℕ → Ω → ℝ,
        (∀ t, t ∈ Finset.Icc 1 setup.s →
          ∀ ω : Ω, 0 ≤ setup.γSeq t * Q t ω) ∧
        (0 ≤
          ∫ ω : Ω,
            Finset.sum (Finset.Icc 1 setup.s)
              (fun t => setup.γSeq t * Q t ω) ∂setup.P) ∧
        ((∫ ω : Ω,
            Finset.sum (Finset.Icc 1 setup.s)
              (fun t => setup.γSeq t * Q t ω) ∂setup.P) ≤
          ∫ ω : Ω, endpointCore ω + weightedEtaStep ω + memoryEndpoint ω ∂setup.P -
            ∫ ω : Ω,
            Finset.sum (Finset.Icc 1 setup.s)
              (fun t => setup.γSeq t * delta t ω) ∂setup.P) ∧
        ((∫ ω : Ω,
            Finset.sum (Finset.Icc 1 setup.s)
              (fun t => setup.γSeq t * delta t ω) ∂setup.P) ≥
          ∫ ω : Ω, memoryEndpoint ω - memoryNormBound ω ∂setup.P) := by
    -- Source bridge for Lemma 6.13, Eqs. (6.6.26)-(6.6.36).  This replaces the
    -- former endpoint-only `qLeft` nonnegativity leaf with the paper objects:
    -- the weighted nonnegative `Q_t`, the residual `δ_t` kept in Eq. (6.6.31),
      -- and the residual absorption that uses (6.6.20), (6.6.23), (6.6.24), and
      -- (6.6.25).  The bridge deliberately does not return endpoint-only
      -- nonnegativity for `qLeft`; Eq. (6.6.36) is derived downstream from these
      -- source facts.
    let Q : ℕ → Ω → ℝ := fun t ω =>
      if ht1 : 1 ≤ t then
        if hts : t ≤ setup.s then
          let stPrev :=
            setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 (t - 1) ω
          let stNext :=
            setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω
          let xHat : ι → E := fun i =>
            setup.xMemAfterSampleAtState t ht1 hts i i stPrev
          let hxHat : ∀ i : ι, xHat i ∈ setup.X := by
            intro i
            simpa [xHat, stPrev, Nat.sub_add_cancel ht1] using
              hhat (t - 1) (by simpa [Nat.sub_add_cancel ht1] using hts) ω i
          setup.phiAt z stNext.x +
            (Fintype.card ι : ℝ)⁻¹ *
              Finset.sum Finset.univ (fun i => setup.psiAtOn z i ⟨xStar, hxStar⟩) +
            ⟪(Fintype.card ι : ℝ)⁻¹ •
                Finset.sum Finset.univ (fun i => setup.gradPsiOnAt z i ⟨xStar, hxStar⟩),
              stNext.x - xStar⟫_ℝ +
            -(setup.phiAt z xStar +
              (Fintype.card ι : ℝ)⁻¹ *
                Finset.sum Finset.univ
                  (fun i =>
                    setup.psiAtOn z i ⟨xHat i, hxHat i⟩ +
                      ⟪setup.gradPsiOnAt z i ⟨xHat i, hxHat i⟩,
                        xStar - xHat i⟫_ℝ))
        else 0
      else 0
    let delta : ℕ → Ω → ℝ := fun t ω =>
      if ht1 : 1 ≤ t then
        if hts : t ≤ setup.s then
          let stPrev :=
            setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 (t - 1) ω
          let stNext :=
            setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω
          let yTilde : ι → E := fun i =>
            (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) + stPrev.yMem i
          setup.ηSeq t * ((setup.μ / 2) * ‖stNext.x - stPrev.x‖ ^ 2) -
            (Fintype.card ι : ℝ)⁻¹ *
              Finset.sum Finset.univ
                (fun i =>
                  ⟪yTilde i - setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                    setup.xTildeAtState t stPrev - stNext.x⟫_ℝ) +
            setup.τSeq t *
              setup.psiBregmanAt z (setup.ξ (t - 1) ω)
                ⟨stPrev.xMem (setup.ξ (t - 1) ω),
                  hXMem_mem (t - 1) (le_trans (Nat.sub_le t 1) hts) ω
                    (setup.ξ (t - 1) ω)⟩
                ⟨stNext.xMem (setup.ξ (t - 1) ω),
                  hXMem_mem t hts ω (setup.ξ (t - 1) ω)⟩
        else 0
      else 0
    have _hEq630_present := hDelta2WeightedIcc
    have _hProx45_present := hProxEtaTelescopePointwise
    have _hResidualParam20_present := hparam20
    have _hResidualParam23_present := hparam23
    have _hResidualParam24_present := hparam24
    have _hResidualParam25_present := hparam25
    have _hResidualCurvature_present := hPsiCurv
    have hResidualGradPsi_lipschitz :
        ∀ i (x y : {x : E // x ∈ setup.X}),
          ‖setup.gradPsiOnAt z i x - setup.gradPsiOnAt z i y‖ ≤
            setup.Lhat * ‖x.1 - y.1‖ := by
      intro i x y
      exact setup.gradPsiOnAt_lipschitz z i x y
    have hResidualGradPsi_bregman_lower :
      ∀ i (x y : {x : E // x ∈ setup.X}),
          (1 / (2 * setup.Lhat)) *
              ‖setup.gradPsiOnAt z i x - setup.gradPsiOnAt z i y‖ ^ 2 ≤
            setup.psiBregmanAt z i x y := by
      intro i x y
      exact setup.psiBregmanAt_grad_norm_sq_le z hz hcurv.1 i x y
    have hResidualAlphaGammaShift :
        ∀ t, 1 ≤ t → t + 1 ≤ setup.s →
          setup.γSeq t = setup.αSeq (t + 1) * setup.γSeq (t + 1) := by
      intro t ht ht1
      exact (hparam20 t ht ht1).symm
    have hResidualTerminalVarianceCoeff_nonneg :
        0 ≤ setup.ηSeq setup.s * setup.μ / 4 -
          ((Fintype.card ι : ℝ) - 1) ^ 2 * setup.Lhat /
            ((Fintype.card ι : ℝ) ^ 2 * setup.τSeq setup.s) := by
      linarith [hparam23]
    have hResidualInteriorVarianceCoeff_nonneg :
        ∀ t, 1 ≤ t → t + 1 ≤ setup.s →
          0 ≤ setup.γSeq t *
            (setup.ηSeq t * setup.μ / 2 -
              setup.αSeq (t + 1) * setup.Lhat / setup.τSeq (t + 1) -
              ((Fintype.card ι : ℝ) - 1) ^ 2 * setup.Lhat /
                ((Fintype.card ι : ℝ) ^ 2 * setup.τSeq t)) := by
      intro t ht ht1
      have hcoef :
          0 ≤ setup.ηSeq t * setup.μ / 2 -
            setup.αSeq (t + 1) * setup.Lhat / setup.τSeq (t + 1) -
            ((Fintype.card ι : ℝ) - 1) ^ 2 * setup.Lhat /
              ((Fintype.card ι : ℝ) ^ 2 * setup.τSeq t) := by
        linarith [hparam24 t ht ht1]
      exact mul_nonneg
        (hγSeq_nonneg t ht (le_trans (Nat.le_succ t) ht1)) hcoef
    have hResidualTerminalYoung :
        ∀ u v : E,
          0 ≤
            ((setup.ηSeq setup.s * setup.μ / 4) /
                (Fintype.card ι : ℝ)) * ‖v‖ ^ 2 -
              (1 / (Fintype.card ι : ℝ)) * ⟪u, v⟫_ℝ +
              (1 + setup.τSeq setup.s) / (4 * setup.Lhat) * ‖u‖ ^ 2 := by
      intro u v
      have hmpos : 0 < (Fintype.card ι : ℝ) := by
        exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι))
      have hLhat_pos : 0 < setup.Lhat := by
        rw [setup.Lhat_def]
        nlinarith [setup.L_pos, setup.hμ_pos]
      exact
        lemma_6_13_terminal_average_young_absorption
          (m := (Fintype.card ι : ℝ)) (L := setup.Lhat)
          (tau := setup.τSeq setup.s)
          (A := setup.ηSeq setup.s * setup.μ / 4)
          (u := u) (v := v)
          hmpos hLhat_pos (setup.hτSeq_nonneg setup.s hs le_rfl)
          hparam25
      -- Remaining source proof:
      -- 1. prove `Q_t ≥ 0` from (6.6.26)-(6.6.27), `h_opt`, `hcurv`, and
    --    `hγSeq_nonneg`;
    -- 2. combine `hprox45`, `hDelta2WeightedIcc`, and the two telescope helpers
    --    to obtain Eq. (6.6.31) with `- E_s[∑ γ_t δ_t]`;
    -- 3. prove the residual lower bound (6.6.35)-(6.6.36) by Young absorption
    --    using `hparam20`, `hparam23`, `hparam24`, `hparam25`, and `hPsiCurv`;
    have hWeightedQ_pointwise :
        ∀ t, t ∈ Finset.Icc 1 setup.s →
          ∀ ω : Ω, 0 ≤ setup.γSeq t * Q t ω := by
      -- (6.6.26)-(6.6.27): weighted `Q_t` nonnegativity.
      intro t ht ω
      rcases Finset.mem_Icc.mp ht with ⟨ht1, hts⟩
      have hγ_nonneg : 0 ≤ setup.γSeq t := hγSeq_nonneg t ht1 hts
      let stPrev :=
        setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 (t - 1) ω
      let stNext :=
        setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω
      let xHat : ι → E := fun i =>
        setup.xMemAfterSampleAtState t ht1 hts i i stPrev
      have hxHat : ∀ i : ι, xHat i ∈ setup.X := by
        intro i
        simpa [xHat, stPrev, Nat.sub_add_cancel ht1] using
          hhat (t - 1) (by simpa [Nat.sub_add_cancel ht1] using hts) ω i
      have hstNext_mem : stNext.x ∈ setup.X := by
        simpa [stNext] using
          (((setup.ambientFixedInnerProcess_mem 0 z x0 xMem0 yMem0 hz hx0 t hts) ω).1)
      have hFOC :
          0 ≤
            ⟪setup.gradPhiAt z xStar, stNext.x - xStar⟫_ℝ +
              (Fintype.card ι : ℝ)⁻¹ *
                Finset.sum Finset.univ
                  (fun i =>
                    ⟪setup.gradPsiOnAt z i ⟨xStar, hxStar⟩, stNext.x - xStar⟫_ℝ) := by
        exact
          lemma_6_13_subproblem_foc_inner_sum setup z xStar hxStar h_opt
            stNext.x hstNext_mem
      have hphi_support :
          ⟪setup.gradPhiAt z xStar, stNext.x - xStar⟫_ℝ ≤
            setup.phiAt z stNext.x - setup.phiAt z xStar := by
        have hcurv_phi := hcurv.2 stNext.x xStar hstNext_mem hxStar
        have hquad_nonneg :
            0 ≤ setup.μ / 2 * ‖stNext.x - xStar‖ ^ 2 := by
          exact mul_nonneg (by linarith [setup.hμ_pos]) (sq_nonneg _)
        linarith
      have hcore_nonneg :
          0 ≤
            setup.phiAt z stNext.x - setup.phiAt z xStar +
              (Fintype.card ι : ℝ)⁻¹ *
                Finset.sum Finset.univ
                  (fun i =>
                    ⟪setup.gradPsiOnAt z i ⟨xStar, hxStar⟩, stNext.x - xStar⟫_ℝ) := by
        linarith [hFOC, hphi_support]
      have hpsi_support :
          ∀ i : ι,
            setup.psiAtOn z i ⟨xHat i, hxHat i⟩ +
                ⟪setup.gradPsiOnAt z i ⟨xHat i, hxHat i⟩, xStar - xHat i⟫_ℝ ≤
              setup.psiAtOn z i ⟨xStar, hxStar⟩ := by
        intro i
        have hcurv_i := (hcurv.1 i ⟨xStar, hxStar⟩ ⟨xHat i, hxHat i⟩).1
        have hquad_nonneg :
            0 ≤ setup.μ / 2 * ‖xStar - xHat i‖ ^ 2 := by
          exact mul_nonneg (by linarith [setup.hμ_pos]) (sq_nonneg _)
        linarith
      have havg_support_le :
          (Fintype.card ι : ℝ)⁻¹ *
              Finset.sum Finset.univ
                (fun i =>
                  setup.psiAtOn z i ⟨xHat i, hxHat i⟩ +
                    ⟪setup.gradPsiOnAt z i ⟨xHat i, hxHat i⟩,
                      xStar - xHat i⟫_ℝ) ≤
            (Fintype.card ι : ℝ)⁻¹ *
              Finset.sum Finset.univ
                (fun i => setup.psiAtOn z i ⟨xStar, hxStar⟩) := by
        have hcard_nonneg : 0 ≤ (Fintype.card ι : ℝ) := by
          exact_mod_cast Nat.zero_le (Fintype.card ι)
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun i _hi => hpsi_support i))
          (inv_nonneg.mpr hcard_nonneg)
      have hQ_nonneg : 0 ≤ Q t ω := by
        dsimp [Q]
        rw [dif_pos ht1, dif_pos hts]
        have hinner_avg :
            ⟪(Fintype.card ι : ℝ)⁻¹ •
                Finset.sum Finset.univ
                  (fun i => setup.gradPsiOnAt z i ⟨xStar, hxStar⟩),
              stNext.x - xStar⟫_ℝ =
            (Fintype.card ι : ℝ)⁻¹ *
              Finset.sum Finset.univ
                (fun i =>
                  ⟪setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                    stNext.x - xStar⟫_ℝ) := by
          rw [inner_smul_left, sum_inner]
          simp
        rw [hinner_avg]
        linarith [hcore_nonneg, havg_support_le]
      exact mul_nonneg hγ_nonneg hQ_nonneg
    have hWeightedQ_integral_nonneg_local :
        0 ≤
          ∫ ω : Ω,
            Finset.sum (Finset.Icc 1 setup.s)
              (fun t => setup.γSeq t * Q t ω) ∂setup.P := by
      refine integral_nonneg_of_ae ?_
      exact Filter.Eventually.of_forall
        (fun ω =>
          Finset.sum_nonneg
            (fun t ht => hWeightedQ_pointwise t ht ω))
    refine ⟨Q, delta, hWeightedQ_pointwise, hWeightedQ_integral_nonneg_local,
      ?_, ?_⟩
    · -- Eq. (6.6.31) with the residual `δ_t` still present.
      have hEq631_integrated_source_bridge :
          (∫ ω : Ω,
            Finset.sum (Finset.Icc 1 setup.s)
              (fun t => setup.γSeq t * Q t ω) ∂setup.P) +
            (∫ ω : Ω,
              Finset.sum (Finset.Icc 1 setup.s)
                (fun t => setup.γSeq t * delta t ω) ∂setup.P) ≤
            ∫ ω : Ω, endpointCore ω + weightedEtaStep ω + memoryEndpoint ω ∂setup.P := by
        -- Source Eq. (6.6.31), integrated at the granularity used in the book:
        -- expand `Q_t` by (6.6.28)-(6.6.29), replace the displayed `δ₂ᵗ`
        -- summand by the current-index average through Eq. (6.6.30), insert
        -- the prox upper bound (6.6.45), and telescope the eta/tau memory terms.
        -- This is intentionally not the old pointwise `qLeftProxTerm` endpoint
        -- branch; the source-facing bridge keeps the residual `δ_t` on the left.
        have _hEq630_current_index_consumed := hDelta2WeightedIcc
        have _hYMem_gradient_memory_consumed := hYMem_grad
        have _hProx45_shape_available := hProxEtaTelescopePointwise
        have _hTau_memory_shape_available := hTauPsiTelescopeSummedPointwise
        -- Remaining source-shaped Eq. (6.6.31) bridge.  The old proof branch
        -- tried to identify the left side with `qLeft`, but `qLeft` omits the
        -- source residual kept in `delta`.  The next proof step should combine
        -- the current-index replacement, gradient-memory invariant, prox
        -- descent, and tau telescope directly into this inequality.
        have hEq631_integrability_pack :
            Integrable
                (fun ω : Ω =>
                  Finset.sum (Finset.Icc 1 setup.s)
                    (fun t => setup.γSeq t * Q t ω)) setup.P ∧
              Integrable
                (fun ω : Ω =>
                  Finset.sum (Finset.Icc 1 setup.s)
                    (fun t => setup.γSeq t * delta t ω)) setup.P ∧
              Integrable (fun ω : Ω => endpointCore ω + memoryEndpoint ω) setup.P := by
          constructor
          · refine setup.ambientFixed_prefix_integrable_real 0 setup.s ?_
            intro ω ω' hprefix
            have hstate :
                ∀ n (hn : n ≤ setup.s),
                  setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω =
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω' := by
              intro n hn
              have hprefix_n :
                  setup.ambientFixedSamplePrefix 0 n ω =
                    setup.ambientFixedSamplePrefix 0 n ω' := by
                funext r
                exact congrFun hprefix ⟨r.1, lt_of_lt_of_le r.2 hn⟩
              exact
                setup.ambientFixedInnerProcess_prefix_const 0 z x0 xMem0 yMem0
                  hz hx0 n hn hprefix_n
            refine Finset.sum_congr rfl ?_
            intro t ht
            rcases Finset.mem_Icc.mp ht with ⟨ht1, hts⟩
            have hprev :
                setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 (t - 1) ω =
                  setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 (t - 1) ω' :=
              hstate (t - 1) (le_trans (Nat.sub_le t 1) hts)
            have hnext :
                setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω =
                  setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω' :=
              hstate t hts
            change setup.γSeq t * Q t ω = setup.γSeq t * Q t ω'
            congr 1
            dsimp [Q]
            rw [dif_pos ht1, dif_pos hts, dif_pos ht1, dif_pos hts]
            simp only [hprev, hnext]
          constructor
          · refine setup.ambientFixed_prefix_integrable_real 0 setup.s ?_
            intro ω ω' hprefix
            have hstate :
                ∀ n (hn : n ≤ setup.s),
                  setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω =
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω' := by
              intro n hn
              have hprefix_n :
                  setup.ambientFixedSamplePrefix 0 n ω =
                    setup.ambientFixedSamplePrefix 0 n ω' := by
                funext r
                exact congrFun hprefix ⟨r.1, lt_of_lt_of_le r.2 hn⟩
              exact
                setup.ambientFixedInnerProcess_prefix_const 0 z x0 xMem0 yMem0
                  hz hx0 n hn hprefix_n
            refine Finset.sum_congr rfl ?_
            intro t ht
            rcases Finset.mem_Icc.mp ht with ⟨ht1, hts⟩
            have ht_sub_lt_s : t - 1 < setup.s := by
              exact lt_of_lt_of_le
                (Nat.sub_lt (lt_of_lt_of_le Nat.zero_lt_one ht1) Nat.zero_lt_one) hts
            have hsample :
                setup.ξ (t - 1) ω = setup.ξ (t - 1) ω' := by
              simpa [RandomizedAcceleratedProximalPointSetup.ambientFixedSamplePrefix]
                using congrFun hprefix ⟨t - 1, ht_sub_lt_s⟩
            have hprev :
                setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 (t - 1) ω =
                  setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 (t - 1) ω' :=
              hstate (t - 1) (le_trans (Nat.sub_le t 1) hts)
            have hnext :
                setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω =
                  setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω' :=
              hstate t hts
            change setup.γSeq t * delta t ω = setup.γSeq t * delta t ω'
            congr 1
            dsimp [delta]
            simp only [if_pos ht1, if_pos hts, hprev, hnext, hsample]
          · refine setup.ambientFixed_prefix_integrable_real 0 setup.s ?_
            intro ω ω' hprefix
            have hstate :
                ∀ n (hn : n ≤ setup.s),
                  setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω =
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω' := by
              intro n hn
              have hprefix_n :
                  setup.ambientFixedSamplePrefix 0 n ω =
                    setup.ambientFixedSamplePrefix 0 n ω' := by
                funext r
                exact congrFun hprefix ⟨r.1, lt_of_lt_of_le r.2 hn⟩
              exact
                setup.ambientFixedInnerProcess_prefix_const 0 z x0 xMem0 yMem0
                  hz hx0 n hn hprefix_n
            have hEtaStepSum :
                Finset.sum (Finset.Icc 1 setup.s)
                    (fun t =>
                      setup.γSeq t * setup.ηSeq t *
                        ((setup.μ / 2) *
                          ‖(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                              t ω).x -
                            (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                              (t - 1) ω).x‖ ^ 2)) =
                  Finset.sum (Finset.Icc 1 setup.s)
                    (fun t =>
                      setup.γSeq t * setup.ηSeq t *
                        ((setup.μ / 2) *
                          ‖(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                              t ω').x -
                            (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                              (t - 1) ω').x‖ ^ 2)) := by
              refine Finset.sum_congr rfl ?_
              intro t ht
              rcases Finset.mem_Icc.mp ht with ⟨_ht1, hts⟩
              rw [hstate t hts, hstate (t - 1) (le_trans (Nat.sub_le t 1) hts)]
            simp [endpointCore, memoryEndpoint, hstate,
              hEtaStepSum,
              RandomizedAcceleratedProximalPointSetup.ambientFixedInnerProcess_zero]
        rcases hEq631_integrability_pack with
          ⟨hQSum_int, hDeltaSum_int, hEndpointMemory_int⟩
        have hLeft_int :
            Integrable
              (fun ω : Ω =>
                Finset.sum (Finset.Icc 1 setup.s)
                    (fun t => setup.γSeq t * Q t ω) +
                  Finset.sum (Finset.Icc 1 setup.s)
                    (fun t => setup.γSeq t * delta t ω)) setup.P :=
          hQSum_int.add hDeltaSum_int
        have hIntegrated_source_left :
            (∫ ω : Ω,
                (Finset.sum (Finset.Icc 1 setup.s)
                    (fun t => setup.γSeq t * Q t ω) +
                  Finset.sum (Finset.Icc 1 setup.s)
                    (fun t => setup.γSeq t * delta t ω)) ∂setup.P) =
            (∫ ω : Ω,
              Finset.sum (Finset.Icc 1 setup.s)
                (fun t => setup.γSeq t * Q t ω) ∂setup.P) +
              (∫ ω : Ω,
                Finset.sum (Finset.Icc 1 setup.s)
                  (fun t => setup.γSeq t * delta t ω) ∂setup.P) := by
          rw [MeasureTheory.integral_add hQSum_int hDeltaSum_int]
        have hIntegrated_source_bridge_normalized :
            ∫ ω : Ω,
              (Finset.sum (Finset.Icc 1 setup.s)
                  (fun t => setup.γSeq t * Q t ω) +
                Finset.sum (Finset.Icc 1 setup.s)
                  (fun t => setup.γSeq t * delta t ω)) ∂setup.P ≤
              ∫ ω : Ω, endpointCore ω + weightedEtaStep ω + memoryEndpoint ω ∂setup.P := by
          have _hEq630_current_index_consumed := hDelta2WeightedIcc
          have _hYMem_gradient_memory_consumed := hYMem_grad
          have _hProx45_shape_consumed := hProxEtaTelescopePointwise
          have _hTau_memory_shape_consumed := hTauPsiTelescopeSummedPointwise
          have hDelta2WeightedIcc_plain :
              Finset.sum (Finset.Icc 1 setup.s)
                  (fun t =>
                    if ht : t ∈ Finset.Icc 1 setup.s then
                      setup.γSeq t *
                        ∫ ω : Ω,
                          ambientFixedDelta2CurrentKernel
                            (setup := setup) (offset := 0) (z := z) (x0 := x0)
                            (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
                            (hz := hz) (hx0 := hx0) (hxStar := hxStar)
                            (t - 1)
                            (by
                              have hts := (Finset.mem_Icc.mp ht).2
                              have ht1 := (Finset.mem_Icc.mp ht).1
                              simpa [Nat.sub_add_cancel ht1] using hts)
                            (hhat (t - 1)
                              (by
                                have hts := (Finset.mem_Icc.mp ht).2
                                have ht1 := (Finset.mem_Icc.mp ht).1
                                simpa [Nat.sub_add_cancel ht1] using hts))
                            ω (setup.ξ (t - 1) ω) ∂setup.P
                    else 0) =
                Finset.sum (Finset.Icc 1 setup.s)
                  (fun t =>
                    if ht : t ∈ Finset.Icc 1 setup.s then
                      setup.γSeq t *
                        ∫ ω : Ω,
                          RandomizedAcceleratedProximalPointSetup.currentIndexAverage
                            (fun j : ι =>
                              ambientFixedDelta2CurrentKernel
                                (setup := setup) (offset := 0) (z := z) (x0 := x0)
                                (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
                                (hz := hz) (hx0 := hx0) (hxStar := hxStar)
                                (t - 1)
                                (by
                                  have hts := (Finset.mem_Icc.mp ht).2
                                  have ht1 := (Finset.mem_Icc.mp ht).1
                                  simpa [Nat.sub_add_cancel ht1] using hts)
                                (hhat (t - 1)
                                  (by
                                    have hts := (Finset.mem_Icc.mp ht).2
                                    have ht1 := (Finset.mem_Icc.mp ht).1
                                    simpa [Nat.sub_add_cancel ht1] using hts))
                                ω j) ∂setup.P
                    else 0) := by
            rw [← Finset.sum_attach (s := Finset.Icc 1 setup.s)]
            rw [← Finset.sum_attach (s := Finset.Icc 1 setup.s)]
            simpa using hDelta2WeightedIcc
          have _hEq630_plain_consumed := hDelta2WeightedIcc_plain
          -- Integrated source Eq. (6.6.31): unfold `Q` and `delta` under the
          -- finite sums, commute the finite-prefix integrals, replace the
          -- displayed `δ₂ᵗ` current-index summand by `hDelta2WeightedIcc`, rewrite
          -- stored gradients using `hYMem_grad`, and combine the prox and memory
          -- telescopes directly against `endpointCore + memoryEndpoint`.
          -- This is the active source-shaped leaf; it intentionally has no
          -- intermediate comparison with the obsolete endpoint-only `qLeft`.
          -- Remaining source algebra bridge for Eq. (6.6.31): expand `Q`
          -- and `delta`, use `hDelta2WeightedIcc_plain` to cancel the
          -- displayed `δ₂ᵗ` term against the current-index average, rewrite
          -- stored memories through `hYMem_grad`, then combine the prox and
          -- tau telescopes directly into `endpointCore + memoryEndpoint`.
          -- The dependency cone intentionally does not pass through the
          -- obsolete comparison `∫ (ΣγQ + Σγδ) ≤ ∫ qLeft`.
          have _hEq630_plain_used := hDelta2WeightedIcc_plain
          have _hYMem_grad_used := hYMem_grad
          have _hProxEta_telescope_used := hProxEtaTelescopePointwise
          have _hTauPsi_telescope_used := hTauPsiTelescopeSummedPointwise
          let proxTauLeft : Ω → ℝ := fun ω =>
            (Finset.sum (Finset.Icc 1 setup.s)
                (fun t =>
                  setup.γSeq t *
                    (let stPrev :=
                        setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                          (t - 1) ω
                      let stNext :=
                        setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                          t ω
                      let yTilde : ι → E :=
                        fun i =>
                          (Fintype.card ι : ℝ) •
                              (stNext.yMem i - stPrev.yMem i) +
                            stPrev.yMem i
                      setup.phiAt z stNext.x - setup.phiAt z xStar +
                        ⟪(Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ yTilde,
                          stNext.x - xStar⟫_ℝ))) +
              (Finset.sum Finset.univ
                (fun i : ι =>
                  let A : ℕ → ℝ := fun n =>
                    if hn : n ≤ setup.s then
                      setup.psiBregmanAt z i
                        ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                            n ω).xMem i,
                          hXMem_mem n hn ω i⟩
                        ⟨xStar, hxStar⟩
                    else 0
                  Finset.sum (Finset.Icc 1 setup.s)
                    (fun t =>
                        setup.γSeq t *
                          ((1 + setup.τSeq t) - (Fintype.card ι : ℝ)⁻¹) *
                          A (t - 1) -
                        setup.γSeq t * (1 + setup.τSeq t) * A t)))
          have hEq631_source_normalization_integrated :
              (∫ ω : Ω,
                (Finset.sum (Finset.Icc 1 setup.s)
                    (fun t => setup.γSeq t * Q t ω) +
                  Finset.sum (Finset.Icc 1 setup.s)
                    (fun t => setup.γSeq t * delta t ω)) ∂setup.P) ≤
                ∫ ω : Ω, proxTauLeft ω + weightedEtaStep ω ∂setup.P := by
            have _hEq630_plain_source := hDelta2WeightedIcc_plain
            have _hYMem_source := hYMem_grad
            have hRealizedYMem_currentBranch :
                ∀ n (hn : n + 1 ≤ setup.s) (ω : Ω),
                  let stPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω
                  let stNext :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 (n + 1) ω
                  (fun i : ι => stNext.yMem i) =
                    (fun i : ι =>
                      if _ : i = setup.ξ n ω then
                        setup.gradPsiOnAt z i
                          ⟨setup.xMemAfterSampleAtState (n + 1) (Nat.succ_pos n) hn
                              (setup.ξ n ω) i stPrev,
                            by
                              simpa using hsource n hn ω i⟩
                      else stPrev.yMem i) :=
              ambientFixed_realized_yMem_eq_currentSample_branch
                (setup := setup) (z := z) (x0 := x0) (xStar := xStar)
                (xMem0 := xMem0) (yMem0 := yMem0)
                (hz := hz) (hx0 := hx0) hsource hsource_yMem
            have hCurrentBranch_delta2Kernel :
                ∀ n (hn : n + 1 ≤ setup.s) (ω : Ω),
                  let stPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω
                  (fun i : ι =>
                    if _ : i = setup.ξ n ω then
                      setup.gradPsiOnAt z i
                        ⟨setup.xMemAfterSampleAtState (n + 1) (Nat.succ_pos n) hn
                            (setup.ξ n ω) i stPrev,
                          by
                            simpa using hsource n hn ω i⟩
                    else stPrev.yMem i) =
                    (fun i : ι =>
                      if _ : i = setup.ξ n ω then
                        setup.gradPsiOnAt z i
                          ⟨setup.xMemAfterSampleAtState (n + 1) (Nat.succ_pos n) hn
                              i i stPrev,
                            hhat n hn ω i⟩
                      else stPrev.yMem i) :=
              ambientFixed_currentSample_branch_eq_delta2Kernel_branch
                (setup := setup) (z := z) (x0 := x0) (xStar := xStar)
                (xMem0 := xMem0) (yMem0 := yMem0)
                (hz := hz) (hx0 := hx0) hsource hhat
            have hRealizedYMem_delta2KernelBranch :
                ∀ n (hn : n + 1 ≤ setup.s) (ω : Ω),
                  let stPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω
                  let stNext :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 (n + 1) ω
                  (fun i : ι => stNext.yMem i) =
                    (fun i : ι =>
                      if _ : i = setup.ξ n ω then
                        setup.gradPsiOnAt z i
                          ⟨setup.xMemAfterSampleAtState (n + 1) (Nat.succ_pos n) hn
                              i i stPrev,
                            hhat n hn ω i⟩
                      else stPrev.yMem i) := by
              intro n hn ω
              exact (hRealizedYMem_currentBranch n hn ω).trans
                (hCurrentBranch_delta2Kernel n hn ω)
            have hRealizedYMem_delta2KernelBranch_Icc :
                ∀ (t : ℕ) (ht1 : 1 ≤ t) (hts : t ≤ setup.s) (ω : Ω),
                  let stPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (t - 1) ω
                  let stNext :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      t ω
                  (fun i : ι => stNext.yMem i) =
                    (fun i : ι =>
                      if _ : i = setup.ξ (t - 1) ω then
                        setup.gradPsiOnAt z i
                          ⟨setup.xMemAfterSampleAtState t
                              ht1 hts
                              i i stPrev,
                            by
                              simpa [Nat.sub_add_cancel ht1, stPrev] using
                                hhat (t - 1)
                                  (by
                                    simpa [Nat.sub_add_cancel ht1] using hts) ω i⟩
                      else stPrev.yMem i) := by
              intro t ht1 hts ω
              have htn : t - 1 + 1 ≤ setup.s := by
                simpa [Nat.sub_add_cancel ht1] using hts
              simpa [Nat.sub_add_cancel ht1] using
                hRealizedYMem_delta2KernelBranch (t - 1) htn ω
            have hSourceStep_state_eq_Icc :
                ∀ (t : ℕ) (ht1 : 1 ≤ t) (hts : t ≤ setup.s) (ω : Ω),
                  let stPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (t - 1) ω
                  let stNext :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      t ω
                  stNext =
                    setup.sourceInnerStepAt 0 z t hz ht1 hts ω stPrev
                      (by
                        simpa [stPrev] using
                          (((setup.ambientFixedInnerProcess_mem 0 z x0 xMem0 yMem0
                            hz hx0 (t - 1) (le_trans (Nat.sub_le t 1) hts)) ω).1))
                      (by
                        intro i
                        have htn : t - 1 + 1 ≤ setup.s := by
                          simpa [Nat.sub_add_cancel ht1] using hts
                        simpa [stPrev, Nat.sub_add_cancel ht1] using
                          hsource (t - 1) htn ω i) := by
              intro t ht1 hts ω
              have htn : t - 1 + 1 ≤ setup.s := by
                simpa [Nat.sub_add_cancel ht1] using hts
              simpa [Nat.sub_add_cancel ht1] using
                hsource_step (t - 1) htn ω
            have hDelta2WeightedResidual_zero :=
              sub_eq_zero.mpr hDelta2WeightedIcc_plain
            have _hEq630_residual_zero_used := hDelta2WeightedResidual_zero
            have _hSourceStep_state_eq_Icc_used := hSourceStep_state_eq_Icc
            have hDelta2WeightedResidual_zero_noif :
                ((Finset.sum (Finset.Icc 1 setup.s).attach
                    (fun t =>
                      setup.γSeq t.1 *
                        ∫ ω : Ω,
                          ambientFixedDelta2CurrentKernel
                            (setup := setup) (offset := 0) (z := z) (x0 := x0)
                            (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
                            (hz := hz) (hx0 := hx0) (hxStar := hxStar)
                            (t.1 - 1)
                            (by
                              have hts := (Finset.mem_Icc.mp t.2).2
                              have ht1 := (Finset.mem_Icc.mp t.2).1
                              simpa [Nat.sub_add_cancel ht1] using hts)
                            (hhat (t.1 - 1)
                              (by
                                have hts := (Finset.mem_Icc.mp t.2).2
                                have ht1 := (Finset.mem_Icc.mp t.2).1
                                simpa [Nat.sub_add_cancel ht1] using hts))
                            ω (setup.ξ (t.1 - 1) ω) ∂setup.P)) -
                  Finset.sum (Finset.Icc 1 setup.s).attach
                    (fun t =>
                      setup.γSeq t.1 *
                        ∫ ω : Ω,
                          RandomizedAcceleratedProximalPointSetup.currentIndexAverage
                            (fun j : ι =>
                              ambientFixedDelta2CurrentKernel
                                (setup := setup) (offset := 0) (z := z) (x0 := x0)
                                (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
                                (hz := hz) (hx0 := hx0) (hxStar := hxStar)
                                (t.1 - 1)
                                (by
                                  have hts := (Finset.mem_Icc.mp t.2).2
                                  have ht1 := (Finset.mem_Icc.mp t.2).1
                                  simpa [Nat.sub_add_cancel ht1] using hts)
                                (hhat (t.1 - 1)
                                  (by
                                    have hts := (Finset.mem_Icc.mp t.2).2
                                    have ht1 := (Finset.mem_Icc.mp t.2).1
                                    simpa [Nat.sub_add_cancel ht1] using hts))
                                ω j) ∂setup.P)) = 0 := by
              -- Eq. (6.6.30) residual cancellation with the membership guards
              -- erased from the finite `Icc` sum.
              exact sub_eq_zero.mpr hDelta2WeightedIcc
            -- Source-normalization leaf for Eq. (6.6.31): expand `Q` and `delta`,
            -- commute finite sums/integrals, use Eq. (6.6.30) on the displayed
            -- `δ₂ᵗ` summand, rewrite stored memories by the gradient-memory
            -- invariant, and keep the positive `η_t V_φ(x^t,x^{t-1})` summand
            -- from Eq. (6.6.32) on the right.  This is the direct non-`qLeft`
            -- algebraic bridge and intentionally avoids the obsolete target
            -- `∫(ΣγQ + Σγδ) ≤ ∫ proxTauLeft`.
            have _hEq630_residual_noif_used := hDelta2WeightedResidual_zero_noif
            let delta2Residual : ℝ :=
              (Finset.sum (Finset.Icc 1 setup.s).attach
                  (fun t =>
                    setup.γSeq t.1 *
                      ∫ ω : Ω,
                        ambientFixedDelta2CurrentKernel
                          (setup := setup) (offset := 0) (z := z) (x0 := x0)
                          (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
                          (hz := hz) (hx0 := hx0) (hxStar := hxStar)
                          (t.1 - 1)
                          (by
                            have hts := (Finset.mem_Icc.mp t.2).2
                            have ht1 := (Finset.mem_Icc.mp t.2).1
                            simpa [Nat.sub_add_cancel ht1] using hts)
                          (hhat (t.1 - 1)
                            (by
                              have hts := (Finset.mem_Icc.mp t.2).2
                              have ht1 := (Finset.mem_Icc.mp t.2).1
                              simpa [Nat.sub_add_cancel ht1] using hts))
                          ω (setup.ξ (t.1 - 1) ω) ∂setup.P)) -
                Finset.sum (Finset.Icc 1 setup.s).attach
                  (fun t =>
                    setup.γSeq t.1 *
                      ∫ ω : Ω,
                        RandomizedAcceleratedProximalPointSetup.currentIndexAverage
                          (fun j : ι =>
                            ambientFixedDelta2CurrentKernel
                              (setup := setup) (offset := 0) (z := z) (x0 := x0)
                              (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
                              (hz := hz) (hx0 := hx0) (hxStar := hxStar)
                              (t.1 - 1)
                              (by
                                have hts := (Finset.mem_Icc.mp t.2).2
                                have ht1 := (Finset.mem_Icc.mp t.2).1
                                simpa [Nat.sub_add_cancel ht1] using hts)
                              (hhat (t.1 - 1)
                                (by
                                  have hts := (Finset.mem_Icc.mp t.2).2
                                  have ht1 := (Finset.mem_Icc.mp t.2).1
                                  simpa [Nat.sub_add_cancel ht1] using hts))
                              ω j) ∂setup.P)
            have hDelta2Residual_eq_zero : delta2Residual = 0 := by
              dsimp [delta2Residual]
              exact hDelta2WeightedResidual_zero_noif
            have hRealizedYTilideBranch_Icc :
                ∀ (t : ℕ) (ht1 : 1 ≤ t) (hts : t ≤ setup.s) (ω : Ω),
                  let stPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (t - 1) ω
                  let stNext :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      t ω
                  (fun i : ι =>
                    (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
                      stPrev.yMem i) =
                    (fun i : ι =>
                      (Fintype.card ι : ℝ) •
                          ((if _ : i = setup.ξ (t - 1) ω then
                              setup.gradPsiOnAt z i
                                ⟨setup.xMemAfterSampleAtState t ht1 hts i i stPrev,
                                  by
                                    simpa [Nat.sub_add_cancel ht1, stPrev] using
                                      hhat (t - 1)
                                        (by
                                          simpa [Nat.sub_add_cancel ht1] using hts)
                                        ω i⟩
                            else stPrev.yMem i) - stPrev.yMem i) +
                        stPrev.yMem i) := by
              intro t ht1 hts ω
              let stPrev :=
                setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                  (t - 1) ω
              let stNext :=
                setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                  t ω
              have hy := hRealizedYMem_delta2KernelBranch_Icc t ht1 hts ω
              funext i
              dsimp only at hy ⊢
              rw [congrFun hy i]
            have _hRealizedYTilideBranch_Icc_used := hRealizedYTilideBranch_Icc
            have hSourceStep_x_eq_prox_avgY_Icc :
                ∀ (t : ℕ) (ht1 : 1 ≤ t) (hts : t ≤ setup.s) (ω : Ω),
                  let stPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (t - 1) ω
                  let stNext :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      t ω
                  let yTilde : ι → E :=
                    fun i =>
                      (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
                        stPrev.yMem i
                  stNext.x =
                    setup.proxStepAt z t hz ht1 hts stPrev.x
                      (by
                        simpa [stPrev] using
                          (((setup.ambientFixedInnerProcess_mem 0 z x0 xMem0 yMem0
                            hz hx0 (t - 1) (le_trans (Nat.sub_le t 1) hts)) ω).1))
                      ((Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ yTilde) := by
              intro t ht1 hts ω
              let stPrev :=
                setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                  (t - 1) ω
              let stNext :=
                setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                  t ω
              have hxPrev : stPrev.x ∈ setup.X := by
                simpa [stPrev] using
                  (((setup.ambientFixedInnerProcess_mem 0 z x0 xMem0 yMem0
                    hz hx0 (t - 1) (le_trans (Nat.sub_le t 1) hts)) ω).1)
              have hxMemNew :
                  ∀ i : ι,
                    setup.xMemAfterSampleAtState t ht1 hts
                      (setup.ξ (0 + (t - 1)) ω) i stPrev ∈ setup.X := by
                intro i
                have htn : t - 1 + 1 ≤ setup.s := by
                  simpa [Nat.sub_add_cancel ht1] using hts
                simpa [stPrev, Nat.sub_add_cancel ht1] using
                  hsource (t - 1) htn ω i
              have hproj :=
                setup.sourceInnerStepAt_x_eq_proxStepAt_realized_estimator
                  0 z t hz ht1 hts ω stPrev hxPrev hxMemNew
              have hstate := hSourceStep_state_eq_Icc t ht1 hts ω
              dsimp only at hstate ⊢
              simpa [stPrev, stNext, hstate.symm] using hproj
            have _hSourceStep_x_eq_prox_avgY_Icc_used :=
              hSourceStep_x_eq_prox_avgY_Icc
            have hDelta2Current_realized_kernel_Icc :
                ∀ (t : ℕ) (ht1 : 1 ≤ t) (hts : t ≤ setup.s) (ω : Ω),
                  let stPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (t - 1) ω
                  let stNext :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      t ω
                  let xHat : ι → E :=
                    fun i => setup.xMemAfterSampleAtState t ht1 hts i i stPrev
                  let hxHat : ∀ i : ι, xHat i ∈ setup.X := by
                    intro i
                    simpa [xHat, stPrev, Nat.sub_add_cancel ht1] using
                      hhat (t - 1) (by simpa [Nat.sub_add_cancel ht1] using hts) ω i
                  let yTilde : ι → E :=
                    fun i =>
                      (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
                        stPrev.yMem i
                  ambientFixedDelta2CurrentKernel
                      (setup := setup) (offset := 0) (z := z) (x0 := x0)
                      (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
                      (hz := hz) (hx0 := hx0) (hxStar := hxStar)
                      (t - 1)
                      (by simpa [Nat.sub_add_cancel ht1] using hts)
                      (hhat (t - 1)
                        (by simpa [Nat.sub_add_cancel ht1] using hts))
                      ω (setup.ξ (t - 1) ω) =
                    (Fintype.card ι : ℝ)⁻¹ *
                      Finset.sum Finset.univ
                        (fun i : ι =>
                          ⟪setup.gradPsiOnAt z i ⟨xHat i, hxHat i⟩ -
                                setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                              setup.xTildeAtState t stPrev⟫_ℝ -
                            ⟪yTilde i - setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                              stNext.x⟫_ℝ +
                            ⟪yTilde i - setup.gradPsiOnAt z i ⟨xHat i, hxHat i⟩,
                              xStar⟫_ℝ) := by
              exact
                ambientFixedDelta2CurrentKernel_realized_sum_Icc
                  setup z x0 xStar xMem0 yMem0 hz hx0 hxStar hhat
                  hRealizedYTilideBranch_Icc hSourceStep_x_eq_prox_avgY_Icc
            have _hDelta2Current_realized_kernel_Icc_used :=
              hDelta2Current_realized_kernel_Icc
            have hSourceStep_xMem_eq_Icc :
                ∀ (t : ℕ) (ht1 : 1 ≤ t) (hts : t ≤ setup.s) (ω : Ω) (i : ι),
                  let stPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (t - 1) ω
                  let stNext :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      t ω
                  stNext.xMem i =
                    setup.xMemAfterSampleAtState t ht1 hts
                      (setup.ξ (t - 1) ω) i stPrev := by
              intro t ht1 hts ω i
              let stPrev :=
                setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                  (t - 1) ω
              let stNext :=
                setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                  t ω
              have hxPrev : stPrev.x ∈ setup.X := by
                simpa [stPrev] using
                  (((setup.ambientFixedInnerProcess_mem 0 z x0 xMem0 yMem0
                    hz hx0 (t - 1) (le_trans (Nat.sub_le t 1) hts)) ω).1)
              have hxMemNew :
                  ∀ i : ι,
                    setup.xMemAfterSampleAtState t ht1 hts
                      (setup.ξ (0 + (t - 1)) ω) i stPrev ∈ setup.X := by
                intro i
                have htn : t - 1 + 1 ≤ setup.s := by
                  simpa [Nat.sub_add_cancel ht1] using hts
                simpa [stPrev, Nat.sub_add_cancel ht1] using
                  hsource (t - 1) htn ω i
              have hproj :=
                setup.sourceInnerStepAt_xMem_eq_xMemAfterSampleAtState
                  0 z t hz ht1 hts ω stPrev hxPrev hxMemNew i
              have hstate := hSourceStep_state_eq_Icc t ht1 hts ω
              dsimp only at hstate ⊢
              simpa [stPrev, stNext, hstate.symm] using hproj
            have hTauMemoryOneHot_Icc :
                ∀ (t : ℕ) (ht1 : 1 ≤ t) (hts : t ≤ setup.s) (ω : Ω),
                  let stPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (t - 1) ω
                  let sample := setup.ξ (t - 1) ω
                  let Aprev : ι → ℝ := fun i =>
                    setup.psiBregmanAt z i
                      ⟨stPrev.xMem i,
                        hXMem_mem (t - 1) (le_trans (Nat.sub_le t 1) hts) ω i⟩
                      ⟨xStar, hxStar⟩
                  let Ahat : ι → ℝ := fun i =>
                    setup.psiBregmanAt z i
                      ⟨setup.xMemAfterSampleAtState t ht1 hts i i stPrev,
                        by
                          simpa [stPrev, Nat.sub_add_cancel ht1] using
                            hhat (t - 1)
                              (by simpa [Nat.sub_add_cancel ht1] using hts) ω i⟩
                      ⟨xStar, hxStar⟩
                  Finset.sum Finset.univ
                      (fun i : ι =>
                        setup.γSeq t *
                            ((1 + setup.τSeq t) - (Fintype.card ι : ℝ)⁻¹) *
                            Aprev i -
                          setup.γSeq t * (1 + setup.τSeq t) *
                            (if i = sample then Ahat i else Aprev i)) =
                    setup.γSeq t * (1 + setup.τSeq t) * Aprev sample -
                      setup.γSeq t * (1 + setup.τSeq t) * Ahat sample -
                      setup.γSeq t * (Fintype.card ι : ℝ)⁻¹ *
                        Finset.sum Finset.univ Aprev := by
              intro t ht1 hts ω
              let stPrev :=
                setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                  (t - 1) ω
              let sample := setup.ξ (t - 1) ω
              let Aprev : ι → ℝ := fun i =>
                setup.psiBregmanAt z i
                  ⟨stPrev.xMem i,
                    hXMem_mem (t - 1) (le_trans (Nat.sub_le t 1) hts) ω i⟩
                  ⟨xStar, hxStar⟩
              let Ahat : ι → ℝ := fun i =>
                setup.psiBregmanAt z i
                  ⟨setup.xMemAfterSampleAtState t ht1 hts i i stPrev,
                    by
                      simpa [stPrev, Nat.sub_add_cancel ht1] using
                        hhat (t - 1)
                          (by simpa [Nat.sub_add_cancel ht1] using hts) ω i⟩
                  ⟨xStar, hxStar⟩
              simpa [stPrev, sample, Aprev, Ahat] using
                one_hot_tau_memory_sum_eq
                  (γ := setup.γSeq t) (τ := setup.τSeq t)
                  (invCard := (Fintype.card ι : ℝ)⁻¹)
                  (sample := sample) (prev := Aprev) (next := Ahat)
            have _hSourceStep_xMem_eq_Icc_used := hSourceStep_xMem_eq_Icc
            have _hTauMemoryOneHot_Icc_used := hTauMemoryOneHot_Icc
            have hTauMemoryActualOneHot_Icc :
                ∀ (t : ℕ) (ht1 : 1 ≤ t) (hts : t ≤ setup.s) (ω : Ω),
                  let stPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (t - 1) ω
                  let stNext :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      t ω
                  let sample := setup.ξ (t - 1) ω
                  let Aprev : ι → ℝ := fun i =>
                    setup.psiBregmanAt z i
                      ⟨stPrev.xMem i,
                        hXMem_mem (t - 1) (le_trans (Nat.sub_le t 1) hts) ω i⟩
                      ⟨xStar, hxStar⟩
                  let Aactual : ι → ℝ := fun i =>
                    setup.psiBregmanAt z i
                      ⟨stNext.xMem i, hXMem_mem t hts ω i⟩
                      ⟨xStar, hxStar⟩
                  let Ahat : ι → ℝ := fun i =>
                    setup.psiBregmanAt z i
                      ⟨setup.xMemAfterSampleAtState t ht1 hts i i stPrev,
                        by
                          simpa [stPrev, Nat.sub_add_cancel ht1] using
                            hhat (t - 1)
                              (by simpa [Nat.sub_add_cancel ht1] using hts) ω i⟩
                      ⟨xStar, hxStar⟩
                  Finset.sum Finset.univ
                      (fun i : ι =>
                        setup.γSeq t *
                            ((1 + setup.τSeq t) - (Fintype.card ι : ℝ)⁻¹) *
                            Aprev i -
                          setup.γSeq t * (1 + setup.τSeq t) *
                            Aactual i) =
                    setup.γSeq t * (1 + setup.τSeq t) * Aprev sample -
                      setup.γSeq t * (1 + setup.τSeq t) * Ahat sample -
                      setup.γSeq t * (Fintype.card ι : ℝ)⁻¹ *
                        Finset.sum Finset.univ Aprev := by
              intro t ht1 hts ω
              let stPrev :=
                setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                  (t - 1) ω
              let stNext :=
                setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                  t ω
              let sample := setup.ξ (t - 1) ω
              let Aprev : ι → ℝ := fun i =>
                setup.psiBregmanAt z i
                  ⟨stPrev.xMem i,
                    hXMem_mem (t - 1) (le_trans (Nat.sub_le t 1) hts) ω i⟩
                  ⟨xStar, hxStar⟩
              let Aactual : ι → ℝ := fun i =>
                setup.psiBregmanAt z i
                  ⟨stNext.xMem i, hXMem_mem t hts ω i⟩
                  ⟨xStar, hxStar⟩
              let Ahat : ι → ℝ := fun i =>
                setup.psiBregmanAt z i
                  ⟨setup.xMemAfterSampleAtState t ht1 hts i i stPrev,
                    by
                      simpa [stPrev, Nat.sub_add_cancel ht1] using
                        hhat (t - 1)
                          (by simpa [Nat.sub_add_cancel ht1] using hts) ω i⟩
                  ⟨xStar, hxStar⟩
              have hactual_branch : ∀ i : ι, Aactual i = if i = sample then Ahat i else Aprev i := by
                intro i
                have hxmem := hSourceStep_xMem_eq_Icc t ht1 hts ω i
                by_cases hi : i = sample
                · subst i
                  have hxmem_hat :
                      stNext.xMem sample =
                        setup.xMemAfterSampleAtState t ht1 hts sample sample stPrev := by
                    simpa [stPrev, stNext, sample] using hxmem
                  simp [Aactual, Ahat, hxmem_hat]
                · dsimp [Aactual, Aprev] at hxmem ⊢
                  have hxmem_prev :
                      stNext.xMem i = stPrev.xMem i := by
                    simpa [sample, RandomizedAcceleratedProximalPointSetup.xMemAfterSampleAtState, hi]
                      using hxmem
                  simp [Aactual, Aprev, hi, hxmem_prev]
              calc
                Finset.sum Finset.univ
                    (fun i : ι =>
                      setup.γSeq t *
                          ((1 + setup.τSeq t) - (Fintype.card ι : ℝ)⁻¹) *
                          Aprev i -
                        setup.γSeq t * (1 + setup.τSeq t) * Aactual i)
                    =
                  Finset.sum Finset.univ
                    (fun i : ι =>
                      setup.γSeq t *
                          ((1 + setup.τSeq t) - (Fintype.card ι : ℝ)⁻¹) *
                          Aprev i -
                        setup.γSeq t * (1 + setup.τSeq t) *
                          (if i = sample then Ahat i else Aprev i)) := by
                    refine Finset.sum_congr rfl ?_
                    intro i _hi
                    rw [hactual_branch i]
                _ =
                  setup.γSeq t * (1 + setup.τSeq t) * Aprev sample -
                    setup.γSeq t * (1 + setup.τSeq t) * Ahat sample -
                    setup.γSeq t * (Fintype.card ι : ℝ)⁻¹ *
                      Finset.sum Finset.univ Aprev := by
                    simpa [stPrev, sample, Aprev, Ahat] using
                      hTauMemoryOneHot_Icc t ht1 hts ω
            have _hTauMemoryActualOneHot_Icc_used := hTauMemoryActualOneHot_Icc
            have hEq631_expanded_with_delta2_residual :
                (∫ ω : Ω,
                  (Finset.sum (Finset.Icc 1 setup.s)
                      (fun t => setup.γSeq t * Q t ω) +
                    Finset.sum (Finset.Icc 1 setup.s)
                      (fun t => setup.γSeq t * delta t ω)) ∂setup.P) ≤
                  (∫ ω : Ω, proxTauLeft ω + weightedEtaStep ω ∂setup.P) +
                    delta2Residual := by
              -- Source Eq. (6.6.31), before applying the zero-residual
              -- cancellation from Eq. (6.6.30): expand `Q_t + δ_t` into the
              -- prox/tau/eta expression plus the realized-minus-averaged
              -- `δ₂ᵗ` current-index residual.
              let timeSet : Finset ℕ := Finset.Icc 1 setup.s
              let leftStep : ℕ → Ω → ℝ := fun t ω =>
                setup.γSeq t * Q t ω + setup.γSeq t * delta t ω
              let proxStepSummand : ℕ → Ω → ℝ := fun t ω =>
                setup.γSeq t *
                  (let stPrev :=
                      setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        (t - 1) ω
                    let stNext :=
                      setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω
                    let yTilde : ι → E :=
                      fun i =>
                        (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
                          stPrev.yMem i
                    setup.phiAt z stNext.x - setup.phiAt z xStar +
                      ⟪(Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ yTilde,
                        stNext.x - xStar⟫_ℝ)
              let etaStepSummand : ℕ → Ω → ℝ := fun t ω =>
                setup.γSeq t * setup.ηSeq t *
                  ((setup.μ / 2) *
                    ‖(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        t ω).x -
                      (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        (t - 1) ω).x‖ ^ 2)
              let tauMemorySummand : ℕ → Ω → ℝ := fun t ω =>
                Finset.sum Finset.univ
                  (fun i : ι =>
                    let A : ℕ → ℝ := fun n =>
                      if hn : n ≤ setup.s then
                        setup.psiBregmanAt z i
                          ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                              n ω).xMem i,
                            hXMem_mem n hn ω i⟩
                          ⟨xStar, hxStar⟩
                      else 0
                    setup.γSeq t *
                        ((1 + setup.τSeq t) - (Fintype.card ι : ℝ)⁻¹) *
                        A (t - 1) -
                      setup.γSeq t * (1 + setup.τSeq t) * A t)
              let rhsStep : ℕ → Ω → ℝ := fun t ω =>
                proxStepSummand t ω + etaStepSummand t ω + tauMemorySummand t ω
              have hleftStep_def :
                  ∀ t ω, leftStep t ω = setup.γSeq t * Q t ω + setup.γSeq t * delta t ω := by
                intro t ω
                rfl
              have hrhsStep_def :
                  ∀ t ω,
                    rhsStep t ω =
                      proxStepSummand t ω + etaStepSummand t ω + tauMemorySummand t ω := by
                intro t ω
                rfl
              let realizedDelta2Summand : ℕ → Ω → ℝ := fun t ω =>
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
                else 0
              let averagedDelta2Summand : ℕ → Ω → ℝ := fun t ω =>
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
                else 0
              have hleft_int :
                  ∀ t ∈ timeSet, Integrable (leftStep t) setup.P := by
                -- Per-time finite-prefix integrability for the abstract lift.
                -- It follows from the same prefix-constancy argument used for
                -- `hQSum_int` and `hDeltaSum_int`; kept local to avoid exposing
                -- Q/delta kernels in the abstract helper statement.
                intro t ht
                rcases Finset.mem_Icc.mp ht with ⟨ht1, hts⟩
                refine setup.ambientFixed_prefix_integrable_real 0 setup.s ?_
                intro ω ω' hprefix
                have hstate :
                    ∀ n (hn : n ≤ setup.s),
                      setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω =
                        setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω' := by
                  intro n hn
                  have hprefix_n :
                      setup.ambientFixedSamplePrefix 0 n ω =
                        setup.ambientFixedSamplePrefix 0 n ω' := by
                    funext r
                    exact congrFun hprefix ⟨r.1, lt_of_lt_of_le r.2 hn⟩
                  exact
                    setup.ambientFixedInnerProcess_prefix_const 0 z x0 xMem0 yMem0
                      hz hx0 n hn hprefix_n
                have hprev :
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        (t - 1) ω =
                      setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        (t - 1) ω' :=
                  hstate (t - 1) (le_trans (Nat.sub_le t 1) hts)
                have hnext :
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω =
                      setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω' :=
                  hstate t hts
                have ht_sub_lt_s : t - 1 < setup.s := by
                  exact lt_of_lt_of_le
                    (Nat.sub_lt (lt_of_lt_of_le Nat.zero_lt_one ht1) Nat.zero_lt_one) hts
                have hsample : setup.ξ (t - 1) ω = setup.ξ (t - 1) ω' := by
                  simpa [RandomizedAcceleratedProximalPointSetup.ambientFixedSamplePrefix]
                    using congrFun hprefix ⟨t - 1, ht_sub_lt_s⟩
                dsimp [leftStep]
                have hQeq : Q t ω = Q t ω' := by
                  dsimp [Q]
                  rw [dif_pos ht1, dif_pos hts, dif_pos ht1, dif_pos hts]
                  simp only [hprev, hnext]
                have hdeltaeq : delta t ω = delta t ω' := by
                  dsimp [delta]
                  simp [ht1, hts, hprev, hnext, hsample]
                rw [hQeq, hdeltaeq]
              have hrhs_int :
                  ∀ t ∈ timeSet, Integrable (rhsStep t) setup.P := by
                -- Per-time integrability of the prox, eta, and tau summands.
                intro t ht
                rcases Finset.mem_Icc.mp ht with ⟨_ht1, hts⟩
                refine setup.ambientFixed_prefix_integrable_real 0 setup.s ?_
                intro ω ω' hprefix
                have hstate :
                    ∀ n (hn : n ≤ setup.s),
                      setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω =
                        setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω' := by
                  intro n hn
                  have hprefix_n :
                      setup.ambientFixedSamplePrefix 0 n ω =
                        setup.ambientFixedSamplePrefix 0 n ω' := by
                    funext r
                    exact congrFun hprefix ⟨r.1, lt_of_lt_of_le r.2 hn⟩
                  exact
                    setup.ambientFixedInnerProcess_prefix_const 0 z x0 xMem0 yMem0
                      hz hx0 n hn hprefix_n
                have hprev :
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        (t - 1) ω =
                      setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        (t - 1) ω' :=
                  hstate (t - 1) (le_trans (Nat.sub_le t 1) hts)
                have hnext :
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω =
                      setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω' :=
                  hstate t hts
                have htau : tauMemorySummand t ω = tauMemorySummand t ω' := by
                  dsimp [tauMemorySummand]
                  refine Finset.sum_congr rfl ?_
                  intro i _hi
                  let Aω : ℕ → ℝ := fun n =>
                    if hn : n ≤ setup.s then
                      setup.psiBregmanAt z i
                        ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                            n ω).xMem i,
                          hXMem_mem n hn ω i⟩
                        ⟨xStar, hxStar⟩
                    else 0
                  let Aω' : ℕ → ℝ := fun n =>
                    if hn : n ≤ setup.s then
                      setup.psiBregmanAt z i
                        ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                            n ω').xMem i,
                          hXMem_mem n hn ω' i⟩
                        ⟨xStar, hxStar⟩
                    else 0
                  change
                    setup.γSeq t * ((1 + setup.τSeq t) - (Fintype.card ι : ℝ)⁻¹) *
                          Aω (t - 1) -
                        setup.γSeq t * (1 + setup.τSeq t) * Aω t =
                      setup.γSeq t * ((1 + setup.τSeq t) - (Fintype.card ι : ℝ)⁻¹) *
                          Aω' (t - 1) -
                        setup.γSeq t * (1 + setup.τSeq t) * Aω' t
                  have hAprev : Aω (t - 1) = Aω' (t - 1) := by
                    simpa [Aω, Aω', le_trans (Nat.sub_le t 1) hts, hprev]
                  have hAnext : Aω t = Aω' t := by
                    simpa [Aω, Aω', hts, hnext]
                  rw [hAprev, hAnext]
                dsimp [rhsStep, proxStepSummand, etaStepSummand]
                rw [hprev, hnext, htau]
              have hIntegratedBridge :
                  (∫ ω : Ω, Finset.sum timeSet (fun t => leftStep t ω) ∂setup.P) ≤
                    (∫ ω : Ω, Finset.sum timeSet (fun t => rhsStep t ω) ∂setup.P) +
                      (Finset.sum timeSet
                          (fun t => ∫ ω : Ω, realizedDelta2Summand t ω ∂setup.P) -
                        Finset.sum timeSet
                          (fun t => ∫ ω : Ω, averagedDelta2Summand t ω ∂setup.P)) := by
                have hactual_int :
                    ∀ t ∈ timeSet, Integrable (realizedDelta2Summand t) setup.P := by
                  intro t ht
                  have ht' : t ∈ Finset.Icc 1 setup.s := by
                    simpa [timeSet] using ht
                  simpa [realizedDelta2Summand] using
                    ambientFixedDelta2CurrentKernel_realized_guarded_Icc_integrable
                      (setup := setup) (z := z) (x0 := x0)
                      (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
                      (hz := hz) (hx0 := hx0) (hxStar := hxStar)
                      hhat t ht'
                have havg_int :
                    ∀ t ∈ timeSet, Integrable (averagedDelta2Summand t) setup.P := by
                  intro t ht
                  have ht' : t ∈ Finset.Icc 1 setup.s := by
                    simpa [timeSet] using ht
                  simpa [averagedDelta2Summand] using
                    ambientFixedDelta2CurrentKernel_average_guarded_Icc_integrable
                      (setup := setup) (z := z) (x0 := x0)
                      (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
                      (hz := hz) (hx0 := hx0) (hxStar := hxStar)
                      hhat t ht'
                -- Source Eq. (6.6.31) must be lifted at expectation/current-index
                -- granularity.  The previous proof route tried to manufacture a
                -- pointwise equality between the averaged `δ₂ᵗ` correction and the
                -- realized sampled `δ₁ᵗ` raw term; Eq. (6.6.30) only supplies the
                -- integrated current-index replacement.  Keep the source facts in
                -- scope and leave the remaining work as the integrated bridge, not
                -- as a pointwise `hPaperToRaw` obligation.
                have _hEq630_integrated_source := hDelta2WeightedIcc
                have _hEq630_per_time_source := h630_delta2
                have _hDelta2_transport_source := hDelta2Current_realized_kernel_Icc
                have _hTau_memory_source := hTauMemoryActualOneHot_Icc
                have _hYMem_grad_source := hYMem_grad
                have _hYBranch_source := hRealizedYTilideBranch_Icc
                have _hProx_source := hSourceStep_x_eq_prox_avgY_Icc
                have _hProx45_source := hprox45
                let correctionStep : ℕ → Ω → ℝ := fun t ω =>
                  (leftStep t ω - rhsStep t ω) +
                    (averagedDelta2Summand t ω - realizedDelta2Summand t ω)
                have hcorr_int :
                    ∀ t ∈ timeSet, Integrable (correctionStep t) setup.P := by
                  intro t ht
                  exact ((hleft_int t ht).sub (hrhs_int t ht)).add
                    ((havg_int t ht).sub (hactual_int t ht))
                have hcorr_zero :
                    (∫ ω : Ω, Finset.sum timeSet
                      (fun t => correctionStep t ω) ∂setup.P) = 0 := by
                  -- This is now the source-faithful Eq. (6.6.30) obligation:
                  -- instantiate `current_sample_average_sub_sample_integral_zero`
                  -- with the `δ₁` raw kernel determined by the strict prefix, then
                  -- sum over the finite time window.  Unlike the retired route, the
                  -- current-index average is not replaced pointwise.
                  have hper_time_zero :
                      ∀ t ∈ timeSet,
                        (∫ ω : Ω, correctionStep t ω ∂setup.P) = 0 := by
                    classical
                    intro t ht
                    rcases Finset.mem_Icc.mp (by simpa [timeSet] using ht) with
                      ⟨ht1, hts⟩
                    let n : ℕ := t - 1
                    have hn : n + 1 ≤ setup.s := by
                      simpa [n, Nat.sub_add_cancel ht1] using hts
                    let Z : Ω → Fin n → ι := setup.ambientFixedSamplePrefix 0 n
                    let rawDelta1 : Ω → ι → ℝ := fun ω j =>
                      let stPrev :=
                        setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                          n ω
                      let xHat : ι → E :=
                        fun i => setup.xMemAfterSampleAtState t ht1 hts i i stPrev
                      let hxHat : ∀ i : ι, xHat i ∈ setup.X := by
                        intro i
                        simpa [xHat, stPrev, n, Nat.sub_add_cancel ht1] using
                          hhat (t - 1)
                            (by simpa [Nat.sub_add_cancel ht1] using hts) ω i
                      let xTilde := setup.xTildeAtState t stPrev
                      let yHyp : ι → ι → E := fun sample i =>
                        (Fintype.card ι : ℝ) •
                            ((if _ : i = sample then
                                setup.gradPsiOnAt z i ⟨xHat i, hxHat i⟩
                              else
                                stPrev.yMem i) - stPrev.yMem i) +
                          stPrev.yMem i
                      let xNextHyp : ι → E := fun sample =>
                        setup.proxStepAt z t hz ht1 hts stPrev.x
                          (by
                            simpa [stPrev, n] using
                              (((setup.ambientFixedInnerProcess_mem 0 z x0 xMem0
                                yMem0 hz hx0 n (Nat.le_of_succ_le hn)) ω).1))
                          ((Fintype.card ι : ℝ)⁻¹ •
                            Finset.sum Finset.univ (fun i : ι => yHyp sample i))
                      let component : ι → ℝ := fun i =>
                        setup.psiAtOn z i ⟨xStar, hxStar⟩ -
                          ⟪setup.gradPsiOnAt z i ⟨xStar, hxStar⟩, xStar⟫_ℝ -
                          (setup.psiAtOn z i ⟨xHat i, hxHat i⟩ -
                            ⟪setup.gradPsiOnAt z i ⟨xHat i, hxHat i⟩, xHat i⟫_ℝ +
                            ⟪setup.gradPsiOnAt z i ⟨xHat i, hxHat i⟩ -
                                setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                              xTilde⟫_ℝ)
                      let Aprev : ι → ℝ := fun i =>
                        setup.psiBregmanAt z i
                          ⟨stPrev.xMem i,
                            by
                              simpa [stPrev, n] using
                                hXMem_mem n (Nat.le_of_succ_le hn) ω i⟩
                          ⟨xStar, hxStar⟩
                      let B : ι → ι → ℝ := fun sample i =>
                        ⟪yHyp sample i - setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                          xTilde - xNextHyp sample⟫_ℝ
                      component j + Aprev j -
                        (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ Aprev +
                        (Fintype.card ι : ℝ)⁻¹ *
                          Finset.sum Finset.univ (fun i : ι => B j i)
                    let delta1RawKernel : (Fin n → ι) → ι → ℝ := fun q j =>
                      if hq : q ∈ Set.range Z then
                        rawDelta1 (Classical.choose hq) j
                      else 0
                    have hZ :
                        Measurable[(SOptLib.filtration setup.ξ setup.hξ_measurable).seq n]
                          Z := by
                      change
                        Measurable[(SOptLib.filtration setup.ξ setup.hξ_measurable).seq n]
                          (fun ω : Ω => fun r : Fin n => setup.ξ (0 + r.1) ω)
                      exact
                        (@measurable_pi_lambda Ω (Fin n) (fun _ : Fin n => ι)
                          ((SOptLib.filtration setup.ξ setup.hξ_measurable).seq n)
                          (fun _ : Fin n => inferInstance)
                          (fun ω : Ω => fun r : Fin n => setup.ξ (0 + r.1) ω)
                          (by
                            intro r
                            simpa [Nat.zero_add] using
                              (SOptLib.measurable_sample_of_lt_prefixFiltration
                                setup.ξ setup.hξ_measurable
                                (n := n) (i := r.1) r.2)))
                    have hF :
                        Measurable
                          (fun q : (Fin n → ι) × ι =>
                            delta1RawKernel q.1 q.2) := by
                      exact measurable_of_finite _
                    have hF_int :
                        ∀ j : ι,
                          Integrable
                            (fun ω : Ω => delta1RawKernel (Z ω) j) setup.P := by
                      intro j
                      refine setup.ambientFixed_prefix_integrable_real 0 n ?_
                      intro ω ω' hprefix
                      change delta1RawKernel (Z ω) j = delta1RawKernel (Z ω') j
                      exact congrArg (fun q => delta1RawKernel q j) (by simpa [Z] using hprefix)
                    have hsample_int :
                        Integrable
                          (fun ω : Ω =>
                            delta1RawKernel (Z ω) (setup.ξ n ω)) setup.P := by
                      refine setup.ambientFixed_prefix_integrable_real 0 (n + 1) ?_
                      intro ω ω' hprefix
                      have hZeq : Z ω = Z ω' := by
                        funext r
                        exact congrFun hprefix
                          ⟨r.1, Nat.lt_trans r.2 (Nat.lt_succ_self n)⟩
                      have hsample : setup.ξ n ω = setup.ξ n ω' := by
                        simpa [RandomizedAcceleratedProximalPointSetup.ambientFixedSamplePrefix]
                          using congrFun hprefix ⟨n, Nat.lt_succ_self n⟩
                      change
                        delta1RawKernel (Z ω) (setup.ξ n ω) =
                          delta1RawKernel (Z ω') (setup.ξ n ω')
                      rw [hZeq, hsample]
                    have hzero :=
                      setup.current_sample_average_sub_sample_integral_zero
                        n (Z := Z) hZ delta1RawKernel hF hF_int hsample_int
                        (setup.γSeq t)
                    have hrepr_integral :
                        (∫ ω : Ω, correctionStep t ω ∂setup.P) =
                          ∫ ω : Ω,
                            setup.γSeq t *
                              (RandomizedAcceleratedProximalPointSetup.currentIndexAverage
                                  (fun j : ι => delta1RawKernel (Z ω) j) -
                                delta1RawKernel (Z ω) (setup.ξ n ω)) ∂setup.P := by
                      have hrepr_pointwise :
                          ∀ ω : Ω,
                            correctionStep t ω =
                              setup.γSeq t *
                                (RandomizedAcceleratedProximalPointSetup.currentIndexAverage
                                    (fun j : ι => delta1RawKernel (Z ω) j) -
                                  delta1RawKernel (Z ω) (setup.ξ n ω)) := by
                        classical
                        have hraw_prefix_const :
                            ∀ ⦃ωa ωb : Ω⦄, Z ωa = Z ωb →
                              ∀ j : ι, rawDelta1 ωa j = rawDelta1 ωb j := by
                          intro ωa ωb hZeq j
                          have hprev :
                              setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                                  n ωa =
                                setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                                  n ωb := by
                            exact
                              setup.ambientFixedInnerProcess_prefix_const
                                0 z x0 xMem0 yMem0 hz hx0 n
                                (Nat.le_of_succ_le hn)
                                (by simpa [Z] using hZeq)
                          let StateData : Type _ :=
                            { st : RaGradState ι E //
                              (∀ i : ι,
                                setup.xMemAfterSampleAtState t ht1 hts i i st ∈ setup.X) ∧
                              (∀ i : ι, st.xMem i ∈ setup.X) ∧ st.x ∈ setup.X }
                          let rawOf : StateData → ι → ℝ := fun packed j =>
                            let stPrev := packed.1
                            let xHat : ι → E :=
                              fun i => setup.xMemAfterSampleAtState t ht1 hts i i stPrev
                            let hxHat : ∀ i : ι, xHat i ∈ setup.X := packed.2.1
                            let xTilde := setup.xTildeAtState t stPrev
                            let yHyp : ι → ι → E := fun sample i =>
                              (Fintype.card ι : ℝ) •
                                  ((if _ : i = sample then
                                      setup.gradPsiOnAt z i ⟨xHat i, hxHat i⟩
                                    else
                                      stPrev.yMem i) - stPrev.yMem i) +
                                stPrev.yMem i
                            let xNextHyp : ι → E := fun sample =>
                              setup.proxStepAt z t hz ht1 hts stPrev.x packed.2.2.2
                                ((Fintype.card ι : ℝ)⁻¹ •
                                  Finset.sum Finset.univ (fun i : ι => yHyp sample i))
                            let component : ι → ℝ := fun i =>
                              setup.psiAtOn z i ⟨xStar, hxStar⟩ -
                                ⟪setup.gradPsiOnAt z i ⟨xStar, hxStar⟩, xStar⟫_ℝ -
                                (setup.psiAtOn z i ⟨xHat i, hxHat i⟩ -
                                  ⟪setup.gradPsiOnAt z i ⟨xHat i, hxHat i⟩, xHat i⟫_ℝ +
                                  ⟪setup.gradPsiOnAt z i ⟨xHat i, hxHat i⟩ -
                                      setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                                    xTilde⟫_ℝ)
                            let Aprev : ι → ℝ := fun i =>
                              setup.psiBregmanAt z i
                                ⟨stPrev.xMem i, packed.2.2.1 i⟩
                                ⟨xStar, hxStar⟩
                            let B : ι → ι → ℝ := fun sample i =>
                              ⟪yHyp sample i - setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                                xTilde - xNextHyp sample⟫_ℝ
                            component j + Aprev j -
                              (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ Aprev +
                              (Fintype.card ι : ℝ)⁻¹ *
                                Finset.sum Finset.univ (fun i : ι => B j i)
                          let pack : Ω → StateData := fun ω =>
                            ⟨setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                                n ω,
                              by
                                refine ⟨?_, ?_⟩
                                · intro i
                                  simpa [n, Nat.sub_add_cancel ht1] using
                                    hhat (t - 1)
                                      (by simpa [Nat.sub_add_cancel ht1] using hts) ω i
                                · refine ⟨?_, ?_⟩
                                  · intro i
                                    exact hXMem_mem n (Nat.le_of_succ_le hn) ω i
                                  · simpa [n] using
                                      (((setup.ambientFixedInnerProcess_mem
                                        0 z x0 xMem0 yMem0 hz hx0 n
                                        (Nat.le_of_succ_le hn)) ω).1)⟩
                          have hpack : pack ωa = pack ωb := by
                            apply Subtype.ext
                            exact hprev
                          change rawOf (pack ωa) j = rawOf (pack ωb) j
                          rw [hpack]
                        have hkernel_eval :
                            ∀ ω j, delta1RawKernel (Z ω) j = rawDelta1 ω j := by
                          intro ω j
                          dsimp [delta1RawKernel]
                          by_cases hq : Z ω ∈ Set.range Z
                          · rw [dif_pos hq]
                            exact hraw_prefix_const (Classical.choose_spec hq) j
                          · exact False.elim (hq ⟨ω, rfl⟩)
                        intro ω
                        have hkernel_average :
                            RandomizedAcceleratedProximalPointSetup.currentIndexAverage
                                (fun j : ι => delta1RawKernel (Z ω) j) =
                              RandomizedAcceleratedProximalPointSetup.currentIndexAverage
                                (fun j : ι => rawDelta1 ω j) := by
                          unfold RandomizedAcceleratedProximalPointSetup.currentIndexAverage
                          congr 1
                          funext j
                          exact hkernel_eval ω j
                        have hraw_corr :
                            correctionStep t ω =
                              setup.γSeq t *
                                (RandomizedAcceleratedProximalPointSetup.currentIndexAverage
                                    (fun j : ι => rawDelta1 ω j) -
                                  rawDelta1 ω (setup.ξ n ω)) := by
                          let stPrev :=
                            setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                              n ω
                          let stNext :=
                            setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                              t ω
                          let sample := setup.ξ n ω
                          let xHat : ι → E :=
                            fun i => setup.xMemAfterSampleAtState t ht1 hts i i stPrev
                          let hxHat : ∀ i : ι, xHat i ∈ setup.X := by
                            intro i
                            simpa [xHat, stPrev, n, Nat.sub_add_cancel ht1] using
                              hhat (t - 1)
                                (by simpa [Nat.sub_add_cancel ht1] using hts) ω i
                          let xTilde := setup.xTildeAtState t stPrev
                          let yHyp : ι → ι → E := fun sample i =>
                            (Fintype.card ι : ℝ) •
                                ((if _ : i = sample then
                                    setup.gradPsiOnAt z i ⟨xHat i, hxHat i⟩
                                  else
                                    stPrev.yMem i) - stPrev.yMem i) +
                              stPrev.yMem i
                          let xNextHyp : ι → E := fun sample =>
                            setup.proxStepAt z t hz ht1 hts stPrev.x
                              (by
                                simpa [stPrev, n] using
                                  (((setup.ambientFixedInnerProcess_mem 0 z x0 xMem0
                                    yMem0 hz hx0 n (Nat.le_of_succ_le hn)) ω).1))
                              ((Fintype.card ι : ℝ)⁻¹ •
                                Finset.sum Finset.univ (fun i : ι => yHyp sample i))
                          let component : ι → ℝ := fun i =>
                            setup.psiAtOn z i ⟨xStar, hxStar⟩ -
                              ⟪setup.gradPsiOnAt z i ⟨xStar, hxStar⟩, xStar⟫_ℝ -
                              (setup.psiAtOn z i ⟨xHat i, hxHat i⟩ -
                                ⟪setup.gradPsiOnAt z i ⟨xHat i, hxHat i⟩, xHat i⟫_ℝ +
                                ⟪setup.gradPsiOnAt z i ⟨xHat i, hxHat i⟩ -
                                    setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                                  xTilde⟫_ℝ)
                          let Aprev : ι → ℝ := fun i =>
                            setup.psiBregmanAt z i
                              ⟨stPrev.xMem i,
                                by
                                  simpa [stPrev, n] using
                                    hXMem_mem n (Nat.le_of_succ_le hn) ω i⟩
                              ⟨xStar, hxStar⟩
                          let Ahat : ι → ℝ := fun i =>
                            setup.psiBregmanAt z i
                              ⟨xHat i, hxHat i⟩
                              ⟨xStar, hxStar⟩
                          let B : ι → ι → ℝ := fun sample i =>
                            ⟪yHyp sample i - setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                              xTilde - xNextHyp sample⟫_ℝ
                          let inner : ℝ :=
                            Finset.sum Finset.univ (fun i : ι => B sample i)
                          let eta : ℝ :=
                            setup.ηSeq t *
                              ((setup.μ / 2) * ‖stNext.x - stPrev.x‖ ^ 2)
                          let bregPrevHat : ℝ :=
                            setup.psiBregmanAt z sample
                              ⟨stPrev.xMem sample,
                                by
                                  simpa [stPrev, n] using
                                    hXMem_mem n (Nat.le_of_succ_le hn) ω sample⟩
                              ⟨xHat sample, hxHat sample⟩
                          let delta1Paper : ℝ :=
                            (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ component
                          let delta1RawAvg : ℝ :=
                            RandomizedAcceleratedProximalPointSetup.currentIndexAverage
                              (fun j : ι => rawDelta1 ω j)
                          have havg_delta2 :
                              averagedDelta2Summand t ω =
                                setup.γSeq t *
                                  ((Fintype.card ι : ℝ)⁻¹ *
                                    (Fintype.card ι : ℝ)⁻¹ *
                                      Finset.sum Finset.univ
                                        (fun i : ι =>
                                          Finset.sum Finset.univ
                                            (fun j : ι => B j i))) := by
                            dsimp [averagedDelta2Summand]
                            rw [dif_pos ht1, dif_pos hts]
                            have hcorr_avg :=
                              ambientFixedDelta2CurrentKernel_average_expansion
                                (setup := setup) (offset := 0) (z := z) (x0 := x0)
                                (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
                                (hz := hz) (hx0 := hx0) (hxStar := hxStar)
                                (n := n) (hn := hn)
                                (hhat := hhat n hn) (ω := ω)
                            rw [hcorr_avg]
                            simp [n, Nat.sub_add_cancel ht1, stPrev, xHat, hxHat,
                              yHyp, xNextHyp, xTilde, B]
                          have hpaper_to_avg_raw :
                              setup.γSeq t * delta1Paper + averagedDelta2Summand t ω =
                                setup.γSeq t * delta1RawAvg := by
                            rw [havg_delta2]
                            simpa [delta1Paper, delta1RawAvg, rawDelta1, stPrev,
                              xHat, hxHat, xTilde, yHyp, xNextHyp, component, Aprev, B]
                              using
                                (eq631_delta1_current_average_scalar
                                  (setup.γSeq t) component Aprev B)
                          have hdelta1_sample_atom :
                              setup.τSeq t * Aprev sample -
                                  (1 + setup.τSeq t) * Ahat sample -
                                  setup.τSeq t *
                                    setup.psiBregmanAt z sample
                                      ⟨stPrev.xMem sample,
                                        by
                                          simpa [stPrev, n] using
                                            hXMem_mem n (Nat.le_of_succ_le hn) ω sample⟩
                                      ⟨xHat sample, hxHat sample⟩ =
                                component sample := by
                            have haff :
                                setup.τSeq t •
                                    (stPrev.xMem sample - xHat sample) =
                                  xHat sample - xTilde := by
                              simpa [sample, xHat, xTilde] using
                                setup.xMemAfterSampleAtState_self_affine_relation
                                  t ht1 hts sample stPrev
                                  (hτSeq_pos t ht1 hts)
                            simpa [Aprev, Ahat, component, sample, xHat, xTilde]
                              using
                                sampled_delta1_raw_atom_from_affine_bregman
                                  (setup := setup) (z := z) (i := sample)
                                  (τ := setup.τSeq t)
                                  (prev := stPrev.xMem sample)
                                  (hat := xHat sample)
                                  (star := xStar)
                                  (xTilde := xTilde)
                                  (hprev :=
                                    by
                                      simpa [stPrev, n] using
                                        hXMem_mem n (Nat.le_of_succ_le hn) ω sample)
                                  (hprev' :=
                                    by
                                      simpa [stPrev, n] using
                                        hXMem_mem n (Nat.le_of_succ_le hn) ω sample)
                                  (hhat := hxHat sample)
                                  (hhat' := hxHat sample)
                                  (hstar := hxStar)
                                  (hstar' := hxStar)
                                  haff
                          have hraw_sample_expand :
                              rawDelta1 ω sample =
                                component sample + Aprev sample -
                                  (Fintype.card ι : ℝ)⁻¹ *
                                    Finset.sum Finset.univ Aprev +
                                  (Fintype.card ι : ℝ)⁻¹ *
                                    Finset.sum Finset.univ (fun i : ι => B sample i) := by
                            simpa [rawDelta1, stPrev, sample, xHat, hxHat, xTilde,
                              yHyp, xNextHyp, component, Aprev, B]
                          have htau_memory_expand :
                              tauMemorySummand t ω =
                                setup.γSeq t * (1 + setup.τSeq t) * Aprev sample -
                                  setup.γSeq t * (1 + setup.τSeq t) * Ahat sample -
                                  setup.γSeq t * (Fintype.card ι : ℝ)⁻¹ *
                                    Finset.sum Finset.univ Aprev := by
                            have htprev_le_s : t - 1 ≤ setup.s :=
                              le_trans (Nat.sub_le t 1) hts
                            have ht_le_succ : t ≤ setup.s + 1 :=
                              Nat.le_succ_of_le hts
                            simpa [tauMemorySummand, stPrev, stNext, sample, Aprev,
                              Ahat, n, htprev_le_s, hts, ht_le_succ]
                              using hTauMemoryActualOneHot_Icc t ht1 hts ω
                          have hdelta_expand :
                              delta t ω =
                                eta - (Fintype.card ι : ℝ)⁻¹ * inner +
                                  setup.τSeq t * bregPrevHat := by
                            let yReal : ι → E := fun i =>
                              (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
                                stPrev.yMem i
                            have htransport :=
                              realized_y_prox_eq_sample_hyp_Icc
                                (setup := setup) (z := z) (x0 := x0)
                                (xMem0 := xMem0) (yMem0 := yMem0)
                                (hz := hz) (hx0 := hx0)
                                hhat hRealizedYTilideBranch_Icc
                                hSourceStep_x_eq_prox_avgY_Icc
                                t ht1 hts ω
                            have hy_real : yReal = yHyp sample := by
                              simpa [yReal, stPrev, stNext, sample, xHat, hxHat,
                                yHyp, xNextHyp, n, Nat.sub_add_cancel ht1]
                                using htransport.1
                            have hx_real : stNext.x = xNextHyp sample := by
                              simpa [stPrev, stNext, sample, xHat, hxHat,
                                yHyp, xNextHyp, n, Nat.sub_add_cancel ht1]
                                using htransport.2
                            have hinner_real :
                                Finset.sum Finset.univ
                                    (fun i : ι =>
                                      ⟪yReal i -
                                          setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                                        xTilde - stNext.x⟫_ℝ) =
                                  inner := by
                              simpa [inner, B, yReal] using
                                finset_inner_residual_transport
                                  (g := fun i : ι =>
                                    setup.gradPsiOnAt z i ⟨xStar, hxStar⟩)
                                  (y := yReal) (y' := yHyp sample)
                                  (x := stNext.x) (xTilde := xTilde)
                                  (x' := xNextHyp sample)
                                  hy_real hx_real
                            have hxmem_sample : stNext.xMem sample = xHat sample := by
                              simpa [stPrev, stNext, sample, xHat, n] using
                                hSourceStep_xMem_eq_Icc t ht1 hts ω sample
                            have hbreg_actual :
                                setup.psiBregmanAt z sample
                                    ⟨stPrev.xMem sample,
                                      by
                                        simpa [stPrev, n] using
                                          hXMem_mem n (Nat.le_of_succ_le hn) ω sample⟩
                                    ⟨stNext.xMem sample,
                                      hXMem_mem t hts ω sample⟩ =
                                  bregPrevHat := by
                              have hsub :
                                  (⟨stNext.xMem sample,
                                      hXMem_mem t hts ω sample⟩ :
                                    {x : E // x ∈ setup.X}) =
                                    ⟨xHat sample, hxHat sample⟩ := by
                                apply Subtype.ext
                                exact hxmem_sample
                              dsimp [bregPrevHat]
                              rw [hsub]
                            simp [delta, ht1, hts, eta, bregPrevHat, yReal, stPrev,
                              stNext, xTilde, sample, n, hinner_real, hbreg_actual]
                          have hdelta_tau_balance :
                              setup.γSeq t * delta t ω +
                                  setup.γSeq t * rawDelta1 ω sample =
                                etaStepSummand t ω + tauMemorySummand t ω := by
                            have hscalar :=
                              eq631_fixed_time_delta1_tau_memory_scalar
                                (gamma := setup.γSeq t)
                                (tau := setup.τSeq t)
                                (invCard := (Fintype.card ι : ℝ)⁻¹)
                                (delta := delta t ω)
                                (eta := eta)
                                (inner := inner)
                                (bregPrevHat := bregPrevHat)
                                (AprevSample := Aprev sample)
                                (AhatSample := Ahat sample)
                                (sumAprev := Finset.sum Finset.univ Aprev)
                                (delta1Component := component sample)
                                (delta1Raw := rawDelta1 ω sample)
                                (tauMemory := tauMemorySummand t ω)
                                hdelta_expand
                                hdelta1_sample_atom
                                hraw_sample_expand
                                htau_memory_expand
                            calc
                              setup.γSeq t * delta t ω +
                                  setup.γSeq t * rawDelta1 ω sample =
                                setup.γSeq t * eta + tauMemorySummand t ω := hscalar
                              _ = etaStepSummand t ω + tauMemorySummand t ω := by
                                simp [etaStepSummand, eta, stPrev, stNext, n]
                                ring
                          let yReal : ι → E := fun i =>
                            (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
                              stPrev.yMem i
                          have hrealized_delta2 :
                              realizedDelta2Summand t ω =
                                setup.γSeq t *
                                  ((Fintype.card ι : ℝ)⁻¹ *
                                    Finset.sum Finset.univ
                                      (fun i : ι =>
                                        ⟪setup.gradPsiOnAt z i ⟨xHat i, hxHat i⟩ -
                                              setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                                            xTilde⟫_ℝ -
                                          ⟪yReal i -
                                              setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                                            stNext.x⟫_ℝ +
                                          ⟪yReal i -
                                              setup.gradPsiOnAt z i ⟨xHat i, hxHat i⟩,
                                            xStar⟫_ℝ)) := by
                            dsimp [realizedDelta2Summand]
                            rw [dif_pos ht1, dif_pos hts]
                            have hreal :=
                              hDelta2Current_realized_kernel_Icc t ht1 hts ω
                            rw [hreal]
                          have hq_decomp :
                              setup.γSeq t * Q t ω =
                                proxStepSummand t ω +
                                  setup.γSeq t * delta1Paper +
                                  realizedDelta2Summand t ω := by
                            rw [hrealized_delta2]
                            have hscalarQ :=
                              eq631_fixed_time_q_realized_delta2_paper_scalar
                                (gamma := setup.γSeq t)
                                (invCard := (Fintype.card ι : ℝ)⁻¹)
                                (phiNext := setup.phiAt z stNext.x)
                                (phiStar := setup.phiAt z xStar)
                                (xNext := stNext.x)
                                (xStar := xStar)
                                (xTilde := xTilde)
                                (psiStar := fun i : ι =>
                                  setup.psiAtOn z i ⟨xStar, hxStar⟩)
                                (psiHat := fun i : ι =>
                                  setup.psiAtOn z i ⟨xHat i, hxHat i⟩)
                                (gStar := fun i : ι =>
                                  setup.gradPsiOnAt z i ⟨xStar, hxStar⟩)
                                (gHat := fun i : ι =>
                                  setup.gradPsiOnAt z i ⟨xHat i, hxHat i⟩)
                                (yTilde := yReal)
                                (xHat := xHat)
                            simpa [Q, proxStepSummand, delta1Paper, component,
                              Finset.sum_sub_distrib, Finset.sum_add_distrib,
                              yReal, stPrev, stNext, xHat, hxHat, xTilde, n,
                              Nat.sub_add_cancel ht1, ht1, hts]
                              using hscalarQ
                          have hcorr_scalar :
                              correctionStep t ω =
                                setup.γSeq t * (delta1RawAvg - rawDelta1 ω sample) := by
                            dsimp [correctionStep]
                            rw [hleftStep_def t ω, hrhsStep_def t ω]
                            linarith [hq_decomp, hpaper_to_avg_raw, hdelta_tau_balance]
                          simpa [delta1RawAvg, sample] using hcorr_scalar
                        calc
                          correctionStep t ω =
                              setup.γSeq t *
                                (RandomizedAcceleratedProximalPointSetup.currentIndexAverage
                                    (fun j : ι => rawDelta1 ω j) -
                                  rawDelta1 ω (setup.ξ n ω)) := hraw_corr
                          _ =
                              setup.γSeq t *
                                (RandomizedAcceleratedProximalPointSetup.currentIndexAverage
                                    (fun j : ι => delta1RawKernel (Z ω) j) -
                                  delta1RawKernel (Z ω) (setup.ξ n ω)) := by
                            rw [hkernel_average, hkernel_eval ω (setup.ξ n ω)]
                      exact MeasureTheory.integral_congr_ae
                        (Filter.Eventually.of_forall hrepr_pointwise)
                    rw [hrepr_integral]
                    exact hzero
                  rw [MeasureTheory.integral_finset_sum]
                  · exact Finset.sum_eq_zero hper_time_zero
                  · intro t ht
                    exact hcorr_int t ht
                have hpoint :
                    ∀ᵐ ω ∂setup.P,
                      Finset.sum timeSet (fun t => leftStep t ω) ≤
                        Finset.sum timeSet (fun t => rhsStep t ω) +
                          (Finset.sum timeSet
                              (fun t => realizedDelta2Summand t ω) -
                            Finset.sum timeSet
                              (fun t => averagedDelta2Summand t ω)) +
                          Finset.sum timeSet (fun t => correctionStep t ω) := by
                  refine Filter.Eventually.of_forall ?_
                  intro ω
                  have hcorr_expand :
                      Finset.sum timeSet (fun t => correctionStep t ω) =
                        Finset.sum timeSet (fun t => leftStep t ω) -
                          Finset.sum timeSet (fun t => rhsStep t ω) +
                        (Finset.sum timeSet
                            (fun t => averagedDelta2Summand t ω) -
                          Finset.sum timeSet
                            (fun t => realizedDelta2Summand t ω)) := by
                    dsimp [correctionStep]
                    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
                  rw [hcorr_expand]
                  ring_nf
                  exact le_rfl
                exact
                  eq631_abstract_sum_residual_lift_with_zero_correction
                    (s := timeSet) (left := leftStep) (rhs := rhsStep)
                    (actual := realizedDelta2Summand)
                    (avg := averagedDelta2Summand) (corr := correctionStep)
                    hleft_int hrhs_int hactual_int havg_int hcorr_int
                    hcorr_zero hpoint
                -- Retired pointwise proof text removed from the active route.
                -- Reconstruct and FILL should prove the integrated bridge above directly.
              have hNormalizeLift :
                  (∫ ω : Ω, Finset.sum timeSet (fun t => leftStep t ω) ∂setup.P) =
                      ∫ ω : Ω,
                        (Finset.sum (Finset.Icc 1 setup.s)
                            (fun t => setup.γSeq t * Q t ω) +
                          Finset.sum (Finset.Icc 1 setup.s)
                            (fun t => setup.γSeq t * delta t ω)) ∂setup.P ∧
                    (∫ ω : Ω, Finset.sum timeSet (fun t => rhsStep t ω) ∂setup.P) +
                        (Finset.sum timeSet
                            (fun t => ∫ ω : Ω, realizedDelta2Summand t ω ∂setup.P) -
                          Finset.sum timeSet
                            (fun t => ∫ ω : Ω, averagedDelta2Summand t ω ∂setup.P)) =
                      (∫ ω : Ω, proxTauLeft ω + weightedEtaStep ω ∂setup.P) +
                        delta2Residual := by
                -- Pure bookkeeping after the abstract lift: `leftStep` splits by
                -- `Finset.sum_add_distrib`, `rhsStep` commutes the tau double
                -- sum with `Finset.sum_comm`, and the residual finite sums are
                -- the no-if Eq. (6.6.30) residual defining `delta2Residual`.
                constructor
                · dsimp [timeSet, leftStep]
                  congr 1
                  funext ω
                  rw [Finset.sum_add_distrib]
                · have hrhs_integral :
                      (∫ ω : Ω,
                        Finset.sum timeSet (fun t => rhsStep t ω) ∂setup.P) =
                        ∫ ω : Ω, proxTauLeft ω + weightedEtaStep ω ∂setup.P := by
                    dsimp [timeSet, rhsStep, proxStepSummand, etaStepSummand,
                      tauMemorySummand, proxTauLeft, weightedEtaStep]
                    simpa [add_assoc, sub_eq_add_neg] using
                      (integral_finset_sum_three_comm_middle
                        (μ := setup.P)
                        (s := Finset.Icc 1 setup.s)
                        (u := (Finset.univ : Finset ι))
                        (a := fun t ω =>
                          setup.γSeq t *
                            (let stPrev :=
                                setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0
                                  hz hx0 (t - 1) ω
                              let stNext :=
                                setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0
                                  hz hx0 t ω
                              let yTilde : ι → E :=
                                fun i =>
                                  (Fintype.card ι : ℝ) •
                                      (stNext.yMem i - stPrev.yMem i) +
                                    stPrev.yMem i
                              setup.phiAt z stNext.x - setup.phiAt z xStar +
                                ⟪(Fintype.card ι : ℝ)⁻¹ •
                                    Finset.sum Finset.univ yTilde,
                                  stNext.x - xStar⟫_ℝ))
                        (b := fun t ω =>
                          setup.γSeq t * setup.ηSeq t *
                            ((setup.μ / 2) *
                              ‖(setup.ambientFixedInnerProcess 0 z x0 xMem0
                                  yMem0 hz hx0 t ω).x -
                                (setup.ambientFixedInnerProcess 0 z x0 xMem0
                                  yMem0 hz hx0 (t - 1) ω).x‖ ^ 2))
                        (c := fun t i ω =>
                          let A : ℕ → ℝ := fun n =>
                            if hn : n ≤ setup.s then
                              setup.psiBregmanAt z i
                                ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0
                                    yMem0 hz hx0 n ω).xMem i,
                                  hXMem_mem n hn ω i⟩
                                ⟨xStar, hxStar⟩
                            else 0
                          setup.γSeq t *
                              ((1 + setup.τSeq t) -
                                (Fintype.card ι : ℝ)⁻¹) *
                              A (t - 1) -
                            setup.γSeq t * (1 + setup.τSeq t) * A t))
                  have hrealized_sum :
                      Finset.sum timeSet
                          (fun t =>
                            ∫ ω : Ω, realizedDelta2Summand t ω ∂setup.P) =
                        Finset.sum (Finset.Icc 1 setup.s).attach
                          (fun t =>
                            setup.γSeq t.1 *
                              ∫ ω : Ω,
                                ambientFixedDelta2CurrentKernel
                                  (setup := setup) (offset := 0) (z := z) (x0 := x0)
                                  (xStar := xStar) (xMem0 := xMem0)
                                  (yMem0 := yMem0)
                                  (hz := hz) (hx0 := hx0) (hxStar := hxStar)
                                  (t.1 - 1)
                                  (by
                                    have hts := (Finset.mem_Icc.mp t.2).2
                                    have ht1 := (Finset.mem_Icc.mp t.2).1
                                    simpa [Nat.sub_add_cancel ht1] using hts)
                                  (hhat (t.1 - 1)
                                    (by
                                      have hts := (Finset.mem_Icc.mp t.2).2
                                      have ht1 := (Finset.mem_Icc.mp t.2).1
                                      simpa [Nat.sub_add_cancel ht1] using hts))
                                  ω (setup.ξ (t.1 - 1) ω) ∂setup.P) := by
                    simpa [timeSet, realizedDelta2Summand]
                      using
                        (sum_Icc_integral_nested_guarded_const_mul_attach
                          (μ := setup.P) (N := setup.s) (γ := setup.γSeq)
                          (F := fun t ht1 hts ω =>
                            ambientFixedDelta2CurrentKernel
                              (setup := setup) (offset := 0) (z := z) (x0 := x0)
                              (xStar := xStar) (xMem0 := xMem0)
                              (yMem0 := yMem0)
                              (hz := hz) (hx0 := hx0) (hxStar := hxStar)
                              (t - 1)
                              (by
                                simpa [Nat.sub_add_cancel ht1] using hts)
                              (hhat (t - 1)
                                (by
                                  simpa [Nat.sub_add_cancel ht1] using hts))
                              ω (setup.ξ (t - 1) ω)))
                  have havg_sum :
                      Finset.sum timeSet
                          (fun t =>
                            ∫ ω : Ω, averagedDelta2Summand t ω ∂setup.P) =
                        Finset.sum (Finset.Icc 1 setup.s).attach
                          (fun t =>
                            setup.γSeq t.1 *
                              ∫ ω : Ω,
                                RandomizedAcceleratedProximalPointSetup.currentIndexAverage
                                  (fun j : ι =>
                                    ambientFixedDelta2CurrentKernel
                                      (setup := setup) (offset := 0) (z := z)
                                      (x0 := x0) (xStar := xStar)
                                      (xMem0 := xMem0) (yMem0 := yMem0)
                                      (hz := hz) (hx0 := hx0) (hxStar := hxStar)
                                      (t.1 - 1)
                                      (by
                                        have hts := (Finset.mem_Icc.mp t.2).2
                                        have ht1 := (Finset.mem_Icc.mp t.2).1
                                        simpa [Nat.sub_add_cancel ht1] using hts)
                                      (hhat (t.1 - 1)
                                        (by
                                          have hts := (Finset.mem_Icc.mp t.2).2
                                          have ht1 := (Finset.mem_Icc.mp t.2).1
                                          simpa [Nat.sub_add_cancel ht1] using hts))
                                      ω j) ∂setup.P) := by
                    simpa [timeSet, averagedDelta2Summand]
                      using
                        (sum_Icc_integral_nested_guarded_const_mul_attach
                          (μ := setup.P) (N := setup.s) (γ := setup.γSeq)
                          (F := fun t ht1 hts ω =>
                            RandomizedAcceleratedProximalPointSetup.currentIndexAverage
                              (fun j : ι =>
                                ambientFixedDelta2CurrentKernel
                                  (setup := setup) (offset := 0) (z := z) (x0 := x0)
                                  (xStar := xStar) (xMem0 := xMem0)
                                  (yMem0 := yMem0)
                                  (hz := hz) (hx0 := hx0) (hxStar := hxStar)
                                  (t - 1)
                                  (by
                                    simpa [Nat.sub_add_cancel ht1] using hts)
                                  (hhat (t - 1)
                                    (by
                                      simpa [Nat.sub_add_cancel ht1] using hts))
                                  ω j)))
                  rw [hrhs_integral, hrealized_sum, havg_sum]
              rcases hNormalizeLift with ⟨hLeftNorm, hRightNorm⟩
              calc
                (∫ ω : Ω,
                  (Finset.sum (Finset.Icc 1 setup.s)
                      (fun t => setup.γSeq t * Q t ω) +
                    Finset.sum (Finset.Icc 1 setup.s)
                      (fun t => setup.γSeq t * delta t ω)) ∂setup.P)
                    =
                  ∫ ω : Ω, Finset.sum timeSet (fun t => leftStep t ω) ∂setup.P :=
                    hLeftNorm.symm
                _ ≤
                    (∫ ω : Ω, Finset.sum timeSet (fun t => rhsStep t ω) ∂setup.P) +
                      (Finset.sum timeSet
                          (fun t => ∫ ω : Ω, realizedDelta2Summand t ω ∂setup.P) -
                        Finset.sum timeSet
                          (fun t => ∫ ω : Ω, averagedDelta2Summand t ω ∂setup.P)) :=
                    hIntegratedBridge
                _ =
                    (∫ ω : Ω, proxTauLeft ω + weightedEtaStep ω ∂setup.P) +
                      delta2Residual := hRightNorm
            linarith
          have hEq631_prox_tau_telescope_integrated :
              ∫ ω : Ω, proxTauLeft ω + weightedEtaStep ω ∂setup.P ≤
                ∫ ω : Ω, endpointCore ω + weightedEtaStep ω + memoryEndpoint ω ∂setup.P := by
            have _hProxEta_source := hProxEtaTelescopePointwise
            have _hTauPsi_source := hTauPsiTelescopeSummedPointwise
            have hProxTau_int : Integrable proxTauLeft setup.P := by
              refine setup.ambientFixed_prefix_integrable_real 0 setup.s ?_
              intro ω ω' hprefix
              have hstate :
                  ∀ n (hn : n ≤ setup.s),
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω =
                      setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω' := by
                intro n hn
                have hprefix_n :
                    setup.ambientFixedSamplePrefix 0 n ω =
                      setup.ambientFixedSamplePrefix 0 n ω' := by
                  funext r
                  exact congrFun hprefix ⟨r.1, lt_of_lt_of_le r.2 hn⟩
                exact
                  setup.ambientFixedInnerProcess_prefix_const 0 z x0 xMem0 yMem0
                    hz hx0 n hn hprefix_n
              have hProxSum_const :
                  Finset.sum (Finset.Icc 1 setup.s)
                      (fun t =>
                        setup.γSeq t *
                          (let stPrev :=
                              setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                                (t - 1) ω
                            let stNext :=
                              setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                                t ω
                            let yTilde : ι → E :=
                              fun i =>
                                (Fintype.card ι : ℝ) •
                                    (stNext.yMem i - stPrev.yMem i) +
                                  stPrev.yMem i
                            setup.phiAt z stNext.x - setup.phiAt z xStar +
                              ⟪(Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ yTilde,
                                stNext.x - xStar⟫_ℝ)) =
                    Finset.sum (Finset.Icc 1 setup.s)
                      (fun t =>
                        setup.γSeq t *
                          (let stPrev :=
                              setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                                (t - 1) ω'
                            let stNext :=
                              setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                                t ω'
                            let yTilde : ι → E :=
                              fun i =>
                                (Fintype.card ι : ℝ) •
                                    (stNext.yMem i - stPrev.yMem i) +
                                  stPrev.yMem i
                            setup.phiAt z stNext.x - setup.phiAt z xStar +
                              ⟪(Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ yTilde,
                                stNext.x - xStar⟫_ℝ)) := by
                refine Finset.sum_congr rfl ?_
                intro t ht
                rcases Finset.mem_Icc.mp ht with ⟨_ht1, hts⟩
                rw [hstate t hts,
                  hstate (t - 1) (le_trans (Nat.sub_le t 1) hts)]
              have hTauSum_const :
                  Finset.sum Finset.univ
                      (fun i : ι =>
                        let A : ℕ → ℝ := fun n =>
                          if hn : n ≤ setup.s then
                            setup.psiBregmanAt z i
                              ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                                  n ω).xMem i,
                                hXMem_mem n hn ω i⟩
                              ⟨xStar, hxStar⟩
                          else 0
                        Finset.sum (Finset.Icc 1 setup.s)
                          (fun t =>
                            setup.γSeq t *
                                ((1 + setup.τSeq t) - (Fintype.card ι : ℝ)⁻¹) *
                                A (t - 1) -
                              setup.γSeq t * (1 + setup.τSeq t) * A t)) =
                    Finset.sum Finset.univ
                      (fun i : ι =>
                        let A : ℕ → ℝ := fun n =>
                          if hn : n ≤ setup.s then
                            setup.psiBregmanAt z i
                              ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                                  n ω').xMem i,
                                hXMem_mem n hn ω' i⟩
                              ⟨xStar, hxStar⟩
                          else 0
                        Finset.sum (Finset.Icc 1 setup.s)
                          (fun t =>
                            setup.γSeq t *
                                ((1 + setup.τSeq t) - (Fintype.card ι : ℝ)⁻¹) *
                                A (t - 1) -
                              setup.γSeq t * (1 + setup.τSeq t) * A t)) := by
                refine Finset.sum_congr rfl ?_
                intro i _hi
                refine Finset.sum_congr rfl ?_
                intro t ht
                rcases Finset.mem_Icc.mp ht with ⟨_ht1, hts⟩
                let Aω : ℕ → ℝ := fun n =>
                  if hn : n ≤ setup.s then
                    setup.psiBregmanAt z i
                      ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                          n ω).xMem i,
                        hXMem_mem n hn ω i⟩
                      ⟨xStar, hxStar⟩
                  else 0
                let Aω' : ℕ → ℝ := fun n =>
                  if hn : n ≤ setup.s then
                    setup.psiBregmanAt z i
                      ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                          n ω').xMem i,
                        hXMem_mem n hn ω' i⟩
                      ⟨xStar, hxStar⟩
                  else 0
                change
                  setup.γSeq t *
                        ((1 + setup.τSeq t) - (Fintype.card ι : ℝ)⁻¹) *
                        Aω (t - 1) -
                      setup.γSeq t * (1 + setup.τSeq t) * Aω t =
                    setup.γSeq t *
                        ((1 + setup.τSeq t) - (Fintype.card ι : ℝ)⁻¹) *
                        Aω' (t - 1) -
                      setup.γSeq t * (1 + setup.τSeq t) * Aω' t
                have hprev_le : t - 1 ≤ setup.s :=
                  le_trans (Nat.sub_le t 1) hts
                have hA_prev : Aω (t - 1) = Aω' (t - 1) := by
                  have hprev_state := hstate (t - 1) hprev_le
                  simpa [Aω, Aω', hprev_le, hprev_state]
                have hA_next : Aω t = Aω' t := by
                  have hnext_state := hstate t hts
                  simpa [Aω, Aω', hts, hnext_state]
                rw [hA_prev, hA_next]
              dsimp [proxTauLeft]
              rw [hProxSum_const, hTauSum_const]
            have hWeightedEtaStep_int : Integrable weightedEtaStep setup.P := by
              refine setup.ambientFixed_prefix_integrable_real 0 setup.s ?_
              intro ω ω' hprefix
              have hstate :
                  ∀ n (hn : n ≤ setup.s),
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω =
                      setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω' := by
                intro n hn
                have hprefix_n :
                    setup.ambientFixedSamplePrefix 0 n ω =
                      setup.ambientFixedSamplePrefix 0 n ω' := by
                  funext r
                  exact congrFun hprefix ⟨r.1, lt_of_lt_of_le r.2 hn⟩
                exact
                  setup.ambientFixedInnerProcess_prefix_const 0 z x0 xMem0 yMem0
                    hz hx0 n hn hprefix_n
              dsimp [weightedEtaStep]
              refine Finset.sum_congr rfl ?_
              intro t ht
              rcases Finset.mem_Icc.mp ht with ⟨_ht1, hts⟩
              rw [hstate t hts,
                hstate (t - 1) (le_trans (Nat.sub_le t 1) hts)]
            have hLeft_add_int :
                Integrable (fun ω : Ω => proxTauLeft ω + weightedEtaStep ω) setup.P :=
              hProxTau_int.add hWeightedEtaStep_int
            have hRight_add_int :
                Integrable
                  (fun ω : Ω => endpointCore ω + weightedEtaStep ω + memoryEndpoint ω)
                  setup.P := by
              have htmp : Integrable
                  (fun ω : Ω => (endpointCore ω + memoryEndpoint ω) + weightedEtaStep ω)
                  setup.P :=
                hEndpointMemory_int.add hWeightedEtaStep_int
              convert htmp using 1
              funext ω
              ring
            have hpoint :
                ∀ᵐ ω ∂setup.P,
                  proxTauLeft ω + weightedEtaStep ω ≤
                    endpointCore ω + weightedEtaStep ω + memoryEndpoint ω :=
              Filter.Eventually.of_forall (fun ω => by
                have hbase :
                    proxTauLeft ω ≤ endpointCore ω + memoryEndpoint ω := by
                  simpa [proxTauLeft, endpointCore, memoryEndpoint] using
                    hEq631EndpointTelescope ω
                linarith)
            exact MeasureTheory.integral_mono_ae hLeft_add_int hRight_add_int hpoint
          exact
            le_trans hEq631_source_normalization_integrated
              hEq631_prox_tau_telescope_integrated
        calc
          (∫ ω : Ω,
              Finset.sum (Finset.Icc 1 setup.s)
                (fun t => setup.γSeq t * Q t ω) ∂setup.P) +
            (∫ ω : Ω,
              Finset.sum (Finset.Icc 1 setup.s)
                (fun t => setup.γSeq t * delta t ω) ∂setup.P)
              = ∫ ω : Ω,
                  (Finset.sum (Finset.Icc 1 setup.s)
                      (fun t => setup.γSeq t * Q t ω) +
                    Finset.sum (Finset.Icc 1 setup.s)
                      (fun t => setup.γSeq t * delta t ω)) ∂setup.P := by
                exact hIntegrated_source_left.symm
          _ ≤ ∫ ω : Ω, endpointCore ω + weightedEtaStep ω + memoryEndpoint ω ∂setup.P :=
            hIntegrated_source_bridge_normalized
      have hsum_le_endpoint :
          (∫ ω : Ω,
            Finset.sum (Finset.Icc 1 setup.s)
              (fun t => setup.γSeq t * Q t ω) ∂setup.P) +
            (∫ ω : Ω,
              Finset.sum (Finset.Icc 1 setup.s)
                (fun t => setup.γSeq t * delta t ω) ∂setup.P) ≤
            ∫ ω : Ω, endpointCore ω + weightedEtaStep ω + memoryEndpoint ω ∂setup.P :=
        hEq631_integrated_source_bridge
      linarith
    · -- Eqs. (6.6.35)-(6.6.36): residual lower bound by Young absorption.
      have hResidual_pointwise :
          ∀ ω : Ω,
            memoryEndpoint ω - memoryNormBound ω ≤
              Finset.sum (Finset.Icc 1 setup.s)
                (fun t => setup.γSeq t * delta t ω) := by
        intro ω
        have hResidualTerminal_cocoercivity :
            ∀ i : ι,
              (1 / (2 * setup.Lhat)) *
                  ‖setup.gradPsiOnAt z i
                        ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                            setup.s ω).xMem i,
                          hXMem_mem setup.s le_rfl ω i⟩ -
                      setup.gradPsiOnAt z i ⟨xStar, hxStar⟩‖ ^ 2 ≤
                setup.psiBregmanAt z i
                  ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      setup.s ω).xMem i,
                    hXMem_mem setup.s le_rfl ω i⟩
                  ⟨xStar, hxStar⟩ := by
          intro i
          exact hResidualGradPsi_bregman_lower i
            ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                setup.s ω).xMem i,
              hXMem_mem setup.s le_rfl ω i⟩
            ⟨xStar, hxStar⟩
        have hResidualStep_cocoercivity :
            ∀ t (_ht1 : 1 ≤ t) (hts : t ≤ setup.s),
              (1 / (2 * setup.Lhat)) *
                  ‖setup.gradPsiOnAt z (setup.ξ (t - 1) ω)
                        ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                            (t - 1) ω).xMem (setup.ξ (t - 1) ω),
                          hXMem_mem (t - 1)
                            (le_trans (Nat.sub_le t 1) hts)
                            ω (setup.ξ (t - 1) ω)⟩ -
                      setup.gradPsiOnAt z (setup.ξ (t - 1) ω)
                        ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                            t ω).xMem (setup.ξ (t - 1) ω),
                          hXMem_mem t hts
                            ω (setup.ξ (t - 1) ω)⟩‖ ^ 2 ≤
                setup.psiBregmanAt z (setup.ξ (t - 1) ω)
                  ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (t - 1) ω).xMem (setup.ξ (t - 1) ω),
                    hXMem_mem (t - 1)
                      (le_trans (Nat.sub_le t 1) hts)
                      ω (setup.ξ (t - 1) ω)⟩
                  ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      t ω).xMem (setup.ξ (t - 1) ω),
                    hXMem_mem t hts
                      ω (setup.ξ (t - 1) ω)⟩ := by
          intro t _ht1 hts
          exact hResidualGradPsi_bregman_lower (setup.ξ (t - 1) ω)
            ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                (t - 1) ω).xMem (setup.ξ (t - 1) ω),
              hXMem_mem (t - 1) (le_trans (Nat.sub_le t 1) hts)
              ω (setup.ξ (t - 1) ω)⟩
            ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                t ω).xMem (setup.ξ (t - 1) ω),
              hXMem_mem t hts ω (setup.ξ (t - 1) ω)⟩
        have _hResidualCocoercivity_consumed :
            (∀ i : ι,
              (1 / (2 * setup.Lhat)) *
                  ‖setup.gradPsiOnAt z i
                        ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                            setup.s ω).xMem i,
                          hXMem_mem setup.s le_rfl ω i⟩ -
                      setup.gradPsiOnAt z i ⟨xStar, hxStar⟩‖ ^ 2 ≤
                setup.psiBregmanAt z i
                  ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      setup.s ω).xMem i,
                      hXMem_mem setup.s le_rfl ω i⟩
                    ⟨xStar, hxStar⟩) ∧
                (∀ t (_ht1 : 1 ≤ t) (hts : t ≤ setup.s),
                  (1 / (2 * setup.Lhat)) *
                      ‖setup.gradPsiOnAt z (setup.ξ (t - 1) ω)
                            ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                                (t - 1) ω).xMem (setup.ξ (t - 1) ω),
                              hXMem_mem (t - 1)
                                (le_trans (Nat.sub_le t 1) hts)
                                ω (setup.ξ (t - 1) ω)⟩ -
                          setup.gradPsiOnAt z (setup.ξ (t - 1) ω)
                            ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                                t ω).xMem (setup.ξ (t - 1) ω),
                              hXMem_mem t
                                hts
                                ω (setup.ξ (t - 1) ω)⟩‖ ^ 2 ≤
                    setup.psiBregmanAt z (setup.ξ (t - 1) ω)
                      ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                          (t - 1) ω).xMem (setup.ξ (t - 1) ω),
                        hXMem_mem (t - 1)
                          (le_trans (Nat.sub_le t 1) hts)
                          ω (setup.ξ (t - 1) ω)⟩
                      ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                          t ω).xMem (setup.ξ (t - 1) ω),
                        hXMem_mem t hts
                          ω (setup.ξ (t - 1) ω)⟩) :=
            ⟨hResidualTerminal_cocoercivity, hResidualStep_cocoercivity⟩
        let stS :=
          setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 setup.s ω
        let stPrevS :=
          setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
            (setup.s - 1) ω
        let v : E := stPrevS.x - stS.x
        let u : ι → E := fun i =>
          setup.gradPsiOnAt z i ⟨stS.xMem i, hXMem_mem setup.s le_rfl ω i⟩ -
            setup.gradPsiOnAt z i ⟨xStar, hxStar⟩
        let B : ι → ℝ := fun i =>
          setup.psiBregmanAt z i
            ⟨stS.xMem i, hXMem_mem setup.s le_rfl ω i⟩ ⟨xStar, hxStar⟩
        let A : ℝ := setup.ηSeq setup.s * setup.μ / 4
        let m : ℝ := (Fintype.card ι : ℝ)
        let terminalCore : ℝ :=
          A * ‖v‖ ^ 2 -
            (1 / m) * Finset.sum Finset.univ (fun i => ⟪u i, v⟫_ℝ)
        have hTerminalAverage_memory_absorption :
            memoryEndpoint ω - memoryNormBound ω ≤
              setup.γSeq setup.s * terminalCore := by
          have hm_pos : 0 < m := by
            dsimp [m]
            exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι))
          have hm_ne : m ≠ 0 := ne_of_gt hm_pos
          have hLhat_pos : 0 < setup.Lhat := by
            rw [setup.Lhat_def]
            nlinarith [setup.L_pos, setup.hμ_pos]
          have hLhat_ne : setup.Lhat ≠ 0 := ne_of_gt hLhat_pos
          have hγs_nonneg : 0 ≤ setup.γSeq setup.s :=
            hγSeq_nonneg setup.s hs le_rfl
          have hτs_nonneg : 0 ≤ setup.τSeq setup.s :=
            setup.hτSeq_nonneg setup.s hs le_rfl
          have honeτ_nonneg : 0 ≤ 1 + setup.τSeq setup.s := by linarith
          have hterminal_young_sum :
              0 ≤
                Finset.sum Finset.univ
                  (fun i =>
                    A / m * ‖v‖ ^ 2 - (1 / m) * ⟪u i, v⟫_ℝ +
                      (1 + setup.τSeq setup.s) / (4 * setup.Lhat) *
                        ‖u i‖ ^ 2) := by
            refine Finset.sum_nonneg ?_
            intro i _hi
            simpa [A, m, u, v] using hResidualTerminalYoung (u i) v
          have hterminal_young :
              0 ≤
                terminalCore +
                  (1 + setup.τSeq setup.s) / (4 * setup.Lhat) *
                    Finset.sum Finset.univ (fun i => ‖u i‖ ^ 2) := by
            let c : ℝ := (1 + setup.τSeq setup.s) / (4 * setup.Lhat)
            have hconst_sum :
                Finset.sum Finset.univ (fun _i : ι => A / m * ‖v‖ ^ 2) =
                  A * ‖v‖ ^ 2 := by
              have hcard_ne : (Fintype.card ι : ℝ) ≠ 0 := by
                exact_mod_cast
                  (Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι)).ne'
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
              dsimp [m] at hm_ne ⊢
              field_simp [hcard_ne]
            have hinner_sum :
                Finset.sum Finset.univ
                    (fun i : ι => (1 / m) * ⟪u i, v⟫_ℝ) =
                  (1 / m) * Finset.sum Finset.univ
                    (fun i : ι => ⟪u i, v⟫_ℝ) := by
              rw [Finset.mul_sum]
            have hnorm_sum :
                Finset.sum Finset.univ
                    (fun i : ι => c * ‖u i‖ ^ 2) =
                  c * Finset.sum Finset.univ (fun i : ι => ‖u i‖ ^ 2) := by
              rw [Finset.mul_sum]
            have hsum_eq :
                Finset.sum Finset.univ
                    (fun i =>
                      A / m * ‖v‖ ^ 2 - (1 / m) * ⟪u i, v⟫_ℝ +
                        (1 + setup.τSeq setup.s) / (4 * setup.Lhat) *
                          ‖u i‖ ^ 2) =
                  terminalCore +
                    (1 + setup.τSeq setup.s) / (4 * setup.Lhat) *
                      Finset.sum Finset.univ (fun i => ‖u i‖ ^ 2) := by
              calc
                Finset.sum Finset.univ
                    (fun i =>
                      A / m * ‖v‖ ^ 2 - (1 / m) * ⟪u i, v⟫_ℝ +
                        (1 + setup.τSeq setup.s) / (4 * setup.Lhat) *
                          ‖u i‖ ^ 2)
                    =
                  Finset.sum Finset.univ (fun _i : ι => A / m * ‖v‖ ^ 2) -
                    Finset.sum Finset.univ
                      (fun i : ι => (1 / m) * ⟪u i, v⟫_ℝ) +
                    Finset.sum Finset.univ
                      (fun i : ι => c * ‖u i‖ ^ 2) := by
                    simp [c, Finset.sum_add_distrib, Finset.sum_sub_distrib]
                _ =
                  terminalCore +
                    (1 + setup.τSeq setup.s) / (4 * setup.Lhat) *
                      Finset.sum Finset.univ (fun i => ‖u i‖ ^ 2) := by
                    rw [hconst_sum, hinner_sum, hnorm_sum]
            rw [← hsum_eq]
            exact hterminal_young_sum
          have hnorm_to_breg :
              (1 + setup.τSeq setup.s) / (4 * setup.Lhat) *
                  Finset.sum Finset.univ (fun i => ‖u i‖ ^ 2) ≤
                (1 + setup.τSeq setup.s) / 2 *
                  Finset.sum Finset.univ B := by
            calc
              (1 + setup.τSeq setup.s) / (4 * setup.Lhat) *
                  Finset.sum Finset.univ (fun i => ‖u i‖ ^ 2)
                  =
                Finset.sum Finset.univ
                  (fun i =>
                    (1 + setup.τSeq setup.s) / (4 * setup.Lhat) *
                      ‖u i‖ ^ 2) := by
                    rw [Finset.mul_sum]
              _ ≤
                Finset.sum Finset.univ
                  (fun i => (1 + setup.τSeq setup.s) / 2 * B i) := by
                    refine Finset.sum_le_sum ?_
                    intro i _hi
                    have hco := hResidualTerminal_cocoercivity i
                    have hscale :=
                      mul_le_mul_of_nonneg_left hco
                        ((div_nonneg honeτ_nonneg (by norm_num : (0 : ℝ) ≤ 2)))
                    have hleft :
                        (1 + setup.τSeq setup.s) / 2 *
                            (1 / (2 * setup.Lhat) * ‖u i‖ ^ 2) =
                          (1 + setup.τSeq setup.s) / (4 * setup.Lhat) *
                            ‖u i‖ ^ 2 := by
                      field_simp [hLhat_ne]
                      ring
                    have hright :
                        (1 + setup.τSeq setup.s) / 2 *
                            setup.psiBregmanAt z i
                              ⟨(setup.ambientFixedInnerProcess 0 z x0 xMem0
                                  yMem0 hz hx0 setup.s ω).xMem i,
                                hXMem_mem setup.s le_rfl ω i⟩
                              ⟨xStar, hxStar⟩ =
                          (1 + setup.τSeq setup.s) / 2 * B i := by
                      simp [B, stS]
                    calc
                      (1 + setup.τSeq setup.s) / (4 * setup.Lhat) *
                          ‖u i‖ ^ 2 =
                        (1 + setup.τSeq setup.s) / 2 *
                          (1 / (2 * setup.Lhat) * ‖u i‖ ^ 2) := by
                          field_simp [hLhat_ne]
                          ring
                      _ ≤ (1 + setup.τSeq setup.s) / 2 * B i := by
                          simpa [u, B, stS] using hscale
              _ =
                (1 + setup.τSeq setup.s) / 2 *
                  Finset.sum Finset.univ B := by
                    rw [Finset.mul_sum]
          have hterminal_core_lower_unweighted :
              -((1 + setup.τSeq setup.s) / 2 *
                  Finset.sum Finset.univ B) ≤ terminalCore := by
            have hneg :
                -((1 + setup.τSeq setup.s) / 2 *
                    Finset.sum Finset.univ B) ≤
                  -((1 + setup.τSeq setup.s) / (4 * setup.Lhat) *
                    Finset.sum Finset.univ (fun i => ‖u i‖ ^ 2)) := by
              linarith [hnorm_to_breg]
            have hcore :
                -((1 + setup.τSeq setup.s) / (4 * setup.Lhat) *
                    Finset.sum Finset.univ (fun i => ‖u i‖ ^ 2)) ≤
                  terminalCore := by
              linarith [hterminal_young]
            linarith
          have hterminal_core_lower :
              -(setup.γSeq setup.s *
                  ((1 + setup.τSeq setup.s) / 2 *
                    Finset.sum Finset.univ B)) ≤
                setup.γSeq setup.s * terminalCore := by
            have hmul :=
              mul_le_mul_of_nonneg_left hterminal_core_lower_unweighted
                hγs_nonneg
            nlinarith [hmul]
          have hmemory_sharp :
              memoryEndpoint ω - memoryNormBound ω ≤
                -(setup.γSeq setup.s *
                    ((1 + setup.τSeq setup.s) / 2 *
                      Finset.sum Finset.univ B)) := by
            have hpoint :
                ∀ i : ι,
                  (setup.γSeq 1 *
                        ((1 + setup.τSeq 1) - (Fintype.card ι : ℝ)⁻¹) *
                        setup.psiBregmanAt z i ⟨xMem0 i, hxMem0 i⟩
                          ⟨xStar, hxStar⟩ -
                      setup.γSeq setup.s * (1 + setup.τSeq setup.s) *
                        setup.psiBregmanAt z i
                          ⟨stS.xMem i, hXMem_mem setup.s le_rfl ω i⟩
                          ⟨xStar, hxStar⟩) -
                    (setup.γSeq 1 *
                          ((1 + setup.τSeq 1) - (Fintype.card ι : ℝ)⁻¹) *
                          setup.Lhat / 2 * ‖xMem0 i - xStar‖ ^ 2 -
                        setup.μ * setup.γSeq setup.s *
                          (1 + setup.τSeq setup.s) / 4 *
                          ‖stS.xMem i - xStar‖ ^ 2) ≤
                  -(setup.γSeq setup.s *
                      ((1 + setup.τSeq setup.s) / 2 * B i)) := by
              intro i
              let C0 : ℝ :=
                setup.γSeq 1 *
                  ((1 + setup.τSeq 1) - (Fintype.card ι : ℝ)⁻¹)
              let Cs : ℝ := setup.γSeq setup.s * (1 + setup.τSeq setup.s)
              let B0 : ℝ :=
                setup.psiBregmanAt z i ⟨xMem0 i, hxMem0 i⟩
                  ⟨xStar, hxStar⟩
              let N0 : ℝ := ‖xMem0 i - xStar‖ ^ 2
              let Bs : ℝ := B i
              let Ns : ℝ := ‖stS.xMem i - xStar‖ ^ 2
              have hC0_nonneg : 0 ≤ C0 := by
                simpa [C0] using hInitialMemoryCoeff_nonneg
              have hCs_nonneg : 0 ≤ Cs := by
                simpa [Cs] using hTerminalMemoryCoeff_nonneg
              have hinit_scaled : C0 * B0 ≤ C0 * (setup.Lhat / 2 * N0) := by
                exact mul_le_mul_of_nonneg_left
                  (by simpa [B0, N0] using hInitialPsiUpper i) hC0_nonneg
              have hinit_nonpos :
                  C0 * B0 - C0 * setup.Lhat / 2 * N0 ≤ 0 := by
                nlinarith [hinit_scaled]
              have hterm_scaled : setup.μ * Cs / 4 * Ns ≤ Cs / 2 * Bs := by
                have hscaled :=
                  mul_le_mul_of_nonneg_left
                    (by simpa [Bs, Ns, B, stS] using hTerminalPsiLower ω i)
                    (div_nonneg hCs_nonneg (by norm_num : (0 : ℝ) ≤ 2))
                nlinarith [hscaled]
              have hterm_le : -Cs * Bs + setup.μ * Cs / 4 * Ns ≤ -Cs / 2 * Bs := by
                nlinarith [hterm_scaled]
              have hcombine :
                  (C0 * B0 - C0 * setup.Lhat / 2 * N0) +
                      (-Cs * Bs + setup.μ * Cs / 4 * Ns) ≤
                    -Cs / 2 * Bs := by
                linarith [hinit_nonpos, hterm_le]
              dsimp [C0, Cs, B0, N0, Bs, Ns, B]
              nlinarith [hcombine]
            calc
              memoryEndpoint ω - memoryNormBound ω
                  =
                Finset.sum Finset.univ
                  (fun i =>
                    (setup.γSeq 1 *
                          ((1 + setup.τSeq 1) - (Fintype.card ι : ℝ)⁻¹) *
                          setup.psiBregmanAt z i ⟨xMem0 i, hxMem0 i⟩
                            ⟨xStar, hxStar⟩ -
                        setup.γSeq setup.s * (1 + setup.τSeq setup.s) *
                          setup.psiBregmanAt z i
                            ⟨stS.xMem i, hXMem_mem setup.s le_rfl ω i⟩
                            ⟨xStar, hxStar⟩) -
                      (setup.γSeq 1 *
                            ((1 + setup.τSeq 1) - (Fintype.card ι : ℝ)⁻¹) *
                            setup.Lhat / 2 * ‖xMem0 i - xStar‖ ^ 2 -
                          setup.μ * setup.γSeq setup.s *
                            (1 + setup.τSeq setup.s) / 4 *
                            ‖stS.xMem i - xStar‖ ^ 2)) := by
                    simp [memoryEndpoint, memoryNormBound, stS,
                      Finset.sum_sub_distrib]
              _ ≤
                Finset.sum Finset.univ
                  (fun i =>
                    -(setup.γSeq setup.s *
                      ((1 + setup.τSeq setup.s) / 2 * B i))) := by
                    exact Finset.sum_le_sum (fun i _hi => hpoint i)
              _ =
                -(setup.γSeq setup.s *
                    ((1 + setup.τSeq setup.s) / 2 *
                      Finset.sum Finset.univ B)) := by
                    rw [Finset.sum_neg_distrib]
                    congr 1
                    rw [← Finset.mul_sum]
                    congr 1
                    rw [← Finset.mul_sum]
          exact le_trans hmemory_sharp hterminal_core_lower
        have hResidual_regrouping_lower :
            setup.γSeq setup.s * terminalCore ≤
              Finset.sum (Finset.Icc 1 setup.s)
                (fun t => setup.γSeq t * delta t ω) := by
          let deltaExpanded : ℕ → ℝ := fun t =>
            if ht1 : 1 ≤ t then
              if hts : t ≤ setup.s then
                let stPrev :=
                  setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                    (t - 1) ω
                let stNext :=
                  setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω
                let yTilde : ι → E := fun i =>
                  (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
                    stPrev.yMem i
                setup.ηSeq t * ((setup.μ / 2) * ‖stNext.x - stPrev.x‖ ^ 2) -
                  (Fintype.card ι : ℝ)⁻¹ *
                    Finset.sum Finset.univ
                      (fun i =>
                        ⟪yTilde i - setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                          (stPrev.x - stNext.x) -
                            setup.αSeq t • (stPrev.xPrev - stPrev.x)⟫_ℝ) +
                  setup.τSeq t *
                    setup.psiBregmanAt z (setup.ξ (t - 1) ω)
                      ⟨stPrev.xMem (setup.ξ (t - 1) ω),
                        hXMem_mem (t - 1) (le_trans (Nat.sub_le t 1) hts) ω
                          (setup.ξ (t - 1) ω)⟩
                      ⟨stNext.xMem (setup.ξ (t - 1) ω),
                        hXMem_mem t hts ω (setup.ξ (t - 1) ω)⟩
              else 0
            else 0
          have hDelta_xTilde_expanded :
              Finset.sum (Finset.Icc 1 setup.s)
                  (fun t => setup.γSeq t * delta t ω) =
                Finset.sum (Finset.Icc 1 setup.s)
                  (fun t => setup.γSeq t * deltaExpanded t) := by
            refine Finset.sum_congr rfl ?_
            intro t ht
            rcases Finset.mem_Icc.mp ht with ⟨ht1, hts⟩
            let stPrev :=
              setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                (t - 1) ω
            let stNext :=
              setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω
            have hxTilde :
                setup.xTildeAtState t stPrev - stNext.x =
                  (stPrev.x - stNext.x) -
                    setup.αSeq t • (stPrev.xPrev - stPrev.x) := by
              simp [RandomizedAcceleratedProximalPointSetup.xTildeAtState]
              module
            simp [delta, deltaExpanded, ht1, hts, stPrev, stNext, hxTilde]
          have hResidual_expanded_lower :
              setup.γSeq setup.s * terminalCore ≤
                Finset.sum (Finset.Icc 1 setup.s)
                  (fun t => setup.γSeq t * deltaExpanded t) := by
            have _hAlphaGammaShift_consumed := hResidualAlphaGammaShift
            have _hTerminalVarianceCoeff_consumed :=
              hResidualTerminalVarianceCoeff_nonneg
            have _hInteriorVarianceCoeff_consumed :=
              hResidualInteriorVarianceCoeff_nonneg
            have hsuccS : setup.s - 1 + 1 ≤ setup.s := by
              simpa [Nat.sub_add_cancel hs]
            have hTerminal_sample_xMem :
                stS.xMem (setup.ξ (setup.s - 1) ω) =
                  setup.xMemAfterSampleAtState setup.s hs le_rfl
                    (setup.ξ (setup.s - 1) ω) (setup.ξ (setup.s - 1) ω)
                    stPrevS := by
              have hstep := hsource_step (setup.s - 1) hsuccS ω
              have hcomp :=
                congrArg
                  (fun st : RaGradState ι E =>
                    st.xMem (setup.ξ (setup.s - 1) ω)) hstep
              simpa [stS, stPrevS,
                RandomizedAcceleratedProximalPointSetup.sourceInnerStepAt,
                Nat.sub_add_cancel hs] using hcomp
            have hTerminal_sample_yMem :
                stS.yMem (setup.ξ (setup.s - 1) ω) =
                  setup.gradPsiOnAt z (setup.ξ (setup.s - 1) ω)
                    ⟨setup.xMemAfterSampleAtState setup.s hs le_rfl
                        (setup.ξ (setup.s - 1) ω) (setup.ξ (setup.s - 1) ω)
                        stPrevS,
                      by
                        simpa [stPrevS, Nat.sub_add_cancel hs] using
                          hsource (setup.s - 1) hsuccS ω
                            (setup.ξ (setup.s - 1) ω)⟩ := by
              have hy :=
                hsource_yMem (setup.s - 1) hsuccS ω
                  (setup.ξ (setup.s - 1) ω)
              simpa [stS, stPrevS, Nat.sub_add_cancel hs] using hy
            have hTerminal_all_yMem_of_initial :
                ∀ i : ι,
                  stS.yMem i =
                    setup.gradPsiOnAt z i
                      ⟨stS.xMem i, hXMem_mem setup.s le_rfl ω i⟩ := by
              intro i
              simpa [stS] using
                hYMem_grad setup.s le_rfl ω i
            have hTerminal_yTilde_inner_sample :
                let j : ι := setup.ξ (setup.s - 1) ω
                let yTildeS : ι → E := fun i =>
                  (Fintype.card ι : ℝ) • (stS.yMem i - stPrevS.yMem i) +
                    stPrevS.yMem i
                let gPrev : ι → E := fun i =>
                  setup.gradPsiOnAt z i
                    ⟨stPrevS.xMem i,
                      hXMem_mem (setup.s - 1) (Nat.sub_le setup.s 1) ω i⟩
                (Fintype.card ι : ℝ)⁻¹ *
                    Finset.sum Finset.univ
                      (fun i =>
                        ⟪yTildeS i - setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                          v⟫_ℝ) =
                  (1 / m) * Finset.sum Finset.univ (fun i => ⟪u i, v⟫_ℝ) +
                    ((m - 1) / m) *
                      ⟪u j -
                          (gPrev j - setup.gradPsiOnAt z j ⟨xStar, hxStar⟩),
                        v⟫_ℝ := by
              let j : ι := setup.ξ (setup.s - 1) ω
              let yTildeS : ι → E := fun i =>
                (Fintype.card ι : ℝ) • (stS.yMem i - stPrevS.yMem i) +
                  stPrevS.yMem i
              let gPrev : ι → E := fun i =>
                setup.gradPsiOnAt z i
                  ⟨stPrevS.xMem i,
                    hXMem_mem (setup.s - 1) (Nat.sub_le setup.s 1) ω i⟩
              have hPrev_all_yMem_of_initial :
                  ∀ i : ι, stPrevS.yMem i = gPrev i := by
                intro i
                simpa [stPrevS, gPrev] using
                  hYMem_grad (setup.s - 1) (Nat.sub_le setup.s 1) ω i
              have hYtilde_decomp :
                  ∀ i : ι,
                    yTildeS i - setup.gradPsiOnAt z i ⟨xStar, hxStar⟩ =
                      u i + ((Fintype.card ι : ℝ) - 1) •
                        (setup.gradPsiOnAt z i
                            ⟨stS.xMem i, hXMem_mem setup.s le_rfl ω i⟩ -
                          gPrev i) := by
                intro i
                have hys := hTerminal_all_yMem_of_initial i
                have hyp := hPrev_all_yMem_of_initial i
                dsimp [yTildeS, u, gPrev]
                rw [hys, hyp]
                module
              have hGradDiff_nonselected :
                  ∀ i : ι, i ≠ j →
                    setup.gradPsiOnAt z i
                          ⟨stS.xMem i, hXMem_mem setup.s le_rfl ω i⟩ -
                        gPrev i = 0 := by
                intro i hij
                have hys := hTerminal_all_yMem_of_initial i
                have hyp := hPrev_all_yMem_of_initial i
                have hymem_nochange : stS.yMem i = stPrevS.yMem i := by
                  have hy := hsource_yMem (setup.s - 1) hsuccS ω i
                  have hij' :
                      i ≠ setup.ξ (0 + (setup.s - 1 + 1 - 1)) ω := by
                    simpa [j, Nat.sub_add_cancel hs] using hij
                  have hij_simple : i ≠ setup.ξ (setup.s - 1) ω := by
                    simpa [j] using hij
                  simp [stS, stPrevS, Nat.sub_add_cancel hs] at hy
                  simp [hij_simple] at hy
                  exact hy
                have hg_eq :
                    setup.gradPsiOnAt z i
                        ⟨stS.xMem i, hXMem_mem setup.s le_rfl ω i⟩ =
                      gPrev i := by
                  calc
                    setup.gradPsiOnAt z i
                        ⟨stS.xMem i, hXMem_mem setup.s le_rfl ω i⟩ =
                        stS.yMem i := by rw [hys]
                    _ = stPrevS.yMem i := hymem_nochange
                    _ = gPrev i := hyp
                simpa [hg_eq]
              have hGradDiff_sum_eq_sample :
                  Finset.sum Finset.univ
                      (fun i : ι =>
                        ⟪setup.gradPsiOnAt z i
                              ⟨stS.xMem i, hXMem_mem setup.s le_rfl ω i⟩ -
                            gPrev i, v⟫_ℝ) =
                    ⟪setup.gradPsiOnAt z j
                          ⟨stS.xMem j, hXMem_mem setup.s le_rfl ω j⟩ -
                        gPrev j, v⟫_ℝ := by
                refine Finset.sum_eq_single j ?_ ?_
                · intro i _hi hij
                  simp [hGradDiff_nonselected i hij]
                · intro hnot
                  exact False.elim (hnot (Finset.mem_univ j))
              have hinner_decomp :
                  Finset.sum Finset.univ
                      (fun i =>
                        ⟪yTildeS i - setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                          v⟫_ℝ) =
                    Finset.sum Finset.univ (fun i => ⟪u i, v⟫_ℝ) +
                      ((Fintype.card ι : ℝ) - 1) *
                        Finset.sum Finset.univ
                          (fun i =>
                            ⟪setup.gradPsiOnAt z i
                                  ⟨stS.xMem i, hXMem_mem setup.s le_rfl ω i⟩ -
                                gPrev i, v⟫_ℝ) := by
                calc
                  Finset.sum Finset.univ
                      (fun i =>
                        ⟪yTildeS i - setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                          v⟫_ℝ) =
                    Finset.sum Finset.univ
                        (fun i =>
                          ⟪u i + ((Fintype.card ι : ℝ) - 1) •
                            (setup.gradPsiOnAt z i
                                ⟨stS.xMem i, hXMem_mem setup.s le_rfl ω i⟩ -
                              gPrev i), v⟫_ℝ) := by
                      refine Finset.sum_congr rfl ?_
                      intro i _hi
                      rw [hYtilde_decomp i]
                  _ =
                    Finset.sum Finset.univ (fun i => ⟪u i, v⟫_ℝ) +
                      Finset.sum Finset.univ
                        (fun i =>
                          ((Fintype.card ι : ℝ) - 1) *
                            ⟪setup.gradPsiOnAt z i
                                  ⟨stS.xMem i, hXMem_mem setup.s le_rfl ω i⟩ -
                                gPrev i, v⟫_ℝ) := by
                      simp [inner_add_left, inner_smul_left,
                        Finset.sum_add_distrib]
                  _ =
                    Finset.sum Finset.univ (fun i => ⟪u i, v⟫_ℝ) +
                      ((Fintype.card ι : ℝ) - 1) *
                        Finset.sum Finset.univ
                          (fun i =>
                            ⟪setup.gradPsiOnAt z i
                                  ⟨stS.xMem i, hXMem_mem setup.s le_rfl ω i⟩ -
                                gPrev i, v⟫_ℝ) := by
                      rw [Finset.mul_sum]
              have hsample_as_u :
                  setup.gradPsiOnAt z j
                        ⟨stS.xMem j, hXMem_mem setup.s le_rfl ω j⟩ -
                      gPrev j =
                    u j - (gPrev j - setup.gradPsiOnAt z j ⟨xStar, hxStar⟩) := by
                dsimp [u]
                module
              calc
                (Fintype.card ι : ℝ)⁻¹ *
                    Finset.sum Finset.univ
                      (fun i =>
                        ⟪yTildeS i - setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                          v⟫_ℝ) =
                  (1 / m) *
                    (Finset.sum Finset.univ (fun i => ⟪u i, v⟫_ℝ) +
                      ((Fintype.card ι : ℝ) - 1) *
                        Finset.sum Finset.univ
                          (fun i =>
                            ⟪setup.gradPsiOnAt z i
                                  ⟨stS.xMem i, hXMem_mem setup.s le_rfl ω i⟩ -
                                gPrev i, v⟫_ℝ)) := by
                    rw [hinner_decomp]
                    simp [m]
                _ =
                  (1 / m) * Finset.sum Finset.univ (fun i => ⟪u i, v⟫_ℝ) +
                    ((m - 1) / m) *
                      ⟪u j -
                          (gPrev j - setup.gradPsiOnAt z j ⟨xStar, hxStar⟩),
                        v⟫_ℝ := by
                    rw [hGradDiff_sum_eq_sample, hsample_as_u]
                    field_simp [m]
                    ring
            have hAlphaGamma_weighted_inner_telescope :
                ∀ F : ℕ → ℝ, F 0 = 0 →
                  Finset.sum (Finset.Icc 1 setup.s)
                      (fun t =>
                        setup.γSeq t *
                          (F t - setup.αSeq t * F (t - 1))) =
                    setup.γSeq setup.s * F setup.s := by
              intro F hF0
              have hstrong :
                  ∀ m, 1 ≤ m → m ≤ setup.s →
                    Finset.sum (Finset.Icc 1 m)
                        (fun t =>
                          setup.γSeq t *
                            (F t - setup.αSeq t * F (t - 1))) =
                      setup.γSeq m * F m := by
                intro m hm
                induction m, hm using Nat.le_induction with
                | base =>
                    intro _hms
                    simp [hF0]
                | succ n hn ih =>
                    intro hsucc_le
                    have hn_le_s : n ≤ setup.s := Nat.le_of_succ_le hsucc_le
                    have hshift :
                        setup.γSeq n =
                          setup.αSeq (n + 1) * setup.γSeq (n + 1) :=
                      hResidualAlphaGammaShift n hn hsucc_le
                    have hn1 : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
                    rw [Finset.sum_Icc_succ_top hn1]
                    rw [Nat.succ_sub_one]
                    rw [ih hn_le_s]
                    rw [hshift]
                    ring
              exact hstrong setup.s hs le_rfl
            have _hEq634_scalar_telescope_consumed :=
              hAlphaGamma_weighted_inner_telescope
            have hEq634_weighted_core_telescope_terminal :
                let F : ℕ → ℝ := fun t =>
                  let stPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (t - 1) ω
                  let stNext :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      t ω
                  let yTilde : ι → E := fun i =>
                    (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
                      stPrev.yMem i
                  (Fintype.card ι : ℝ)⁻¹ *
                    Finset.sum Finset.univ
                      (fun i =>
                        ⟪yTilde i - setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                          stPrev.x - stNext.x⟫_ℝ)
                Finset.sum (Finset.Icc 1 setup.s)
                    (fun t =>
                      setup.γSeq t *
                        (F t - setup.αSeq t * F (t - 1))) =
                  setup.γSeq setup.s *
                    ((1 / m) *
                        Finset.sum Finset.univ (fun i => ⟪u i, v⟫_ℝ) +
                      ((m - 1) / m) *
                        ⟪u (setup.ξ (setup.s - 1) ω) -
                            ((fun i : ι =>
                              setup.gradPsiOnAt z i
                                ⟨stPrevS.xMem i,
                                  hXMem_mem (setup.s - 1)
                                    (Nat.sub_le setup.s 1) ω i⟩)
                                (setup.ξ (setup.s - 1) ω) -
                              setup.gradPsiOnAt z (setup.ξ (setup.s - 1) ω)
                                ⟨xStar, hxStar⟩),
                          v⟫_ℝ) := by
              let F : ℕ → ℝ := fun t =>
                let stPrev :=
                  setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                    (t - 1) ω
                let stNext :=
                  setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                    t ω
                let yTilde : ι → E := fun i =>
                  (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
                    stPrev.yMem i
                (Fintype.card ι : ℝ)⁻¹ *
                  Finset.sum Finset.univ
                    (fun i =>
                      ⟪yTilde i - setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                        stPrev.x - stNext.x⟫_ℝ)
              have hF0 : F 0 = 0 := by
                simp [F]
              have htel := hAlphaGamma_weighted_inner_telescope F hF0
              have hFs :
                  F setup.s =
                    (1 / m) *
                        Finset.sum Finset.univ (fun i => ⟪u i, v⟫_ℝ) +
                      ((m - 1) / m) *
                        ⟪u (setup.ξ (setup.s - 1) ω) -
                            ((fun i : ι =>
                              setup.gradPsiOnAt z i
                                ⟨stPrevS.xMem i,
                                  hXMem_mem (setup.s - 1)
                                    (Nat.sub_le setup.s 1) ω i⟩)
                                (setup.ξ (setup.s - 1) ω) -
                              setup.gradPsiOnAt z (setup.ξ (setup.s - 1) ω)
                                ⟨xStar, hxStar⟩),
                  v⟫_ℝ := by
                simpa [F, stS, stPrevS, v] using
                  hTerminal_yTilde_inner_sample
              exact htel.trans (by rw [hFs])
            have _hEq634_weighted_core_consumed :=
              hEq634_weighted_core_telescope_terminal
            have hYtilde_increment_correction_identity :
                ∀ t (ht2 : 2 ≤ t) (hts : t ≤ setup.s),
                  let stPrevPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (t - 2) ω
                  let stPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (t - 1) ω
                  let stNext :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      t ω
                  let yTildePrev : ι → E := fun i =>
                    (Fintype.card ι : ℝ) • (stPrev.yMem i - stPrevPrev.yMem i) +
                      stPrevPrev.yMem i
                  let yTildeNext : ι → E := fun i =>
                    (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
                      stPrev.yMem i
                  let dPrev : E := stPrev.xPrev - stPrev.x
                  let jCur : ι := setup.ξ (t - 1) ω
                  let jPrev : ι := setup.ξ (t - 2) ω
                  let gCurNew : E :=
                    setup.gradPsiOnAt z jCur
                      ⟨stNext.xMem jCur, hXMem_mem t hts ω jCur⟩
                  let gCurOld : E :=
                    setup.gradPsiOnAt z jCur
                      ⟨stPrev.xMem jCur,
                        hXMem_mem (t - 1) (by omega) ω jCur⟩
                  let gPrevOld : E :=
                    setup.gradPsiOnAt z jPrev
                      ⟨stPrevPrev.xMem jPrev,
                        hXMem_mem (t - 2) (by omega) ω jPrev⟩
                  let gPrevNew : E :=
                    setup.gradPsiOnAt z jPrev
                      ⟨stPrev.xMem jPrev,
                        hXMem_mem (t - 1) (by omega) ω jPrev⟩
                  (Fintype.card ι : ℝ)⁻¹ *
                      Finset.sum Finset.univ
                        (fun i =>
                          ⟪yTildeNext i - setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                            dPrev⟫_ℝ) =
                    (Fintype.card ι : ℝ)⁻¹ *
                        Finset.sum Finset.univ
                          (fun i =>
                            ⟪yTildePrev i - setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                              dPrev⟫_ℝ) +
                      ⟪gCurNew - gCurOld, dPrev⟫_ℝ +
                      ((m - 1) / m) * ⟪gPrevOld - gPrevNew, dPrev⟫_ℝ := by
              intro t ht2 hts
              let stPrevPrev :=
                setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                  (t - 2) ω
              let stPrev :=
                setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                  (t - 1) ω
              let stNext :=
                setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω
              let yTildePrev : ι → E := fun i =>
                (Fintype.card ι : ℝ) • (stPrev.yMem i - stPrevPrev.yMem i) +
                  stPrevPrev.yMem i
              let yTildeNext : ι → E := fun i =>
                (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
                  stPrev.yMem i
              let dPrev : E := stPrev.xPrev - stPrev.x
              let jCur : ι := setup.ξ (t - 1) ω
              let jPrev : ι := setup.ξ (t - 2) ω
              let gCurNew : E :=
                setup.gradPsiOnAt z jCur
                  ⟨stNext.xMem jCur, hXMem_mem t hts ω jCur⟩
              let gCurOld : E :=
                setup.gradPsiOnAt z jCur
                  ⟨stPrev.xMem jCur,
                    hXMem_mem (t - 1) (by omega) ω jCur⟩
              let gPrevOld : E :=
                setup.gradPsiOnAt z jPrev
                  ⟨stPrevPrev.xMem jPrev,
                    hXMem_mem (t - 2) (by omega) ω jPrev⟩
              let gPrevNew : E :=
                setup.gradPsiOnAt z jPrev
                  ⟨stPrev.xMem jPrev,
                    hXMem_mem (t - 1) (by omega) ω jPrev⟩
              have hm_ne : m ≠ 0 := by
                have hm_pos : 0 < m := by
                  dsimp [m]
                  exact_mod_cast
                    (Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι))
                exact ne_of_gt hm_pos
              have ht1 : 1 ≤ t := by omega
              have hprev_le_s : t - 1 ≤ setup.s := by omega
              have hprevprev_le_s : t - 2 ≤ setup.s := by omega
              have hcur_succ : t - 1 + 1 ≤ setup.s := by omega
              have hprev_succ : t - 2 + 1 ≤ setup.s := by omega
              have hcur_step_nat : t - 1 + 1 = t := by omega
              have hprev_step_nat : t - 2 + 1 = t - 1 := by omega
              have hcur_idx_nat : 0 + (t - 1 + 1 - 1) = t - 1 := by omega
              have hprev_idx_nat : 0 + (t - 2 + 1 - 1) = t - 2 := by omega
              have hprev_idx_nat' : t - 1 - 1 = t - 2 := by omega
              have _hsource_step_cur := hsource_step (t - 1) hcur_succ ω
              have hCur_nonselected :
                  ∀ i : ι, i ≠ jCur → stNext.yMem i - stPrev.yMem i = 0 := by
                intro i hij
                have hy := hsource_yMem (t - 1) hcur_succ ω i
                have hij' :
                    ¬ i = setup.ξ (0 + (t - 1 + 1 - 1)) ω := by
                  simpa [jCur, hcur_idx_nat] using hij
                have hij_simple : i ≠ setup.ξ (t - 1) ω := by
                  simpa [jCur] using hij
                have hy' : stNext.yMem i = stPrev.yMem i := by
                  simpa [stNext, stPrev, hcur_step_nat, hcur_idx_nat,
                    hij', hij_simple] using hy
                rw [hy']
                simp
              have hPrev_nonselected :
                  ∀ i : ι, i ≠ jPrev → stPrevPrev.yMem i - stPrev.yMem i = 0 := by
                intro i hij
                have hy := hsource_yMem (t - 2) hprev_succ ω i
                have hij' :
                    ¬ i = setup.ξ (0 + (t - 2 + 1 - 1)) ω := by
                  simpa [jPrev, hprev_idx_nat] using hij
                have hij_simple : i ≠ setup.ξ (t - 2) ω := by
                  simpa [jPrev] using hij
                have hij_simple' : i ≠ setup.ξ (t - 1 - 1) ω := by
                  simpa [hprev_idx_nat'] using hij_simple
                have hy' : stPrev.yMem i = stPrevPrev.yMem i := by
                  simpa [stPrev, stPrevPrev, hprev_step_nat, hprev_idx_nat,
                    hprev_idx_nat', hij', hij_simple, hij_simple'] using hy
                rw [hy']
                simp
              have hCur_sum :
                  Finset.sum Finset.univ
                      (fun i : ι => ⟪stNext.yMem i - stPrev.yMem i, dPrev⟫_ℝ) =
                    ⟪stNext.yMem jCur - stPrev.yMem jCur, dPrev⟫_ℝ := by
                refine Finset.sum_eq_single jCur ?_ ?_
                · intro i _hi hij
                  simp [hCur_nonselected i hij]
                · intro hnot
                  exact False.elim (hnot (Finset.mem_univ jCur))
              have hPrev_sum :
                  Finset.sum Finset.univ
                      (fun i : ι => ⟪stPrevPrev.yMem i - stPrev.yMem i, dPrev⟫_ℝ) =
                    ⟪stPrevPrev.yMem jPrev - stPrev.yMem jPrev, dPrev⟫_ℝ := by
                refine Finset.sum_eq_single jPrev ?_ ?_
                · intro i _hi hij
                  simp [hPrev_nonselected i hij]
                · intro hnot
                  exact False.elim (hnot (Finset.mem_univ jPrev))
              have hCur_selected_grad :
                  stNext.yMem jCur - stPrev.yMem jCur = gCurNew - gCurOld := by
                dsimp [gCurNew, gCurOld, stNext, stPrev]
                rw [hYMem_grad t hts ω jCur,
                  hYMem_grad (t - 1) hprev_le_s ω jCur]
              have hPrev_selected_grad :
                  stPrevPrev.yMem jPrev - stPrev.yMem jPrev =
                    gPrevOld - gPrevNew := by
                dsimp [gPrevOld, gPrevNew, stPrevPrev, stPrev]
                rw [hYMem_grad (t - 2) hprevprev_le_s ω jPrev,
                  hYMem_grad (t - 1) hprev_le_s ω jPrev]
              have hDiff_point :
                  ∀ i : ι,
                    yTildeNext i - yTildePrev i =
                      (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
                        ((Fintype.card ι : ℝ) - 1) •
                          (stPrevPrev.yMem i - stPrev.yMem i) := by
                intro i
                dsimp [yTildeNext, yTildePrev]
                module
              have hDiff_sum :
                  Finset.sum Finset.univ
                      (fun i : ι => ⟪yTildeNext i - yTildePrev i, dPrev⟫_ℝ) =
                    (Fintype.card ι : ℝ) * ⟪gCurNew - gCurOld, dPrev⟫_ℝ +
                      ((Fintype.card ι : ℝ) - 1) *
                        ⟪gPrevOld - gPrevNew, dPrev⟫_ℝ := by
                calc
                  Finset.sum Finset.univ
                      (fun i : ι => ⟪yTildeNext i - yTildePrev i, dPrev⟫_ℝ) =
                    Finset.sum Finset.univ
                      (fun i : ι =>
                        ⟪(Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
                            ((Fintype.card ι : ℝ) - 1) •
                              (stPrevPrev.yMem i - stPrev.yMem i), dPrev⟫_ℝ) := by
                      refine Finset.sum_congr rfl ?_
                      intro i _hi
                      rw [hDiff_point i]
                  _ =
                    (Fintype.card ι : ℝ) *
                        Finset.sum Finset.univ
                          (fun i : ι => ⟪stNext.yMem i - stPrev.yMem i, dPrev⟫_ℝ) +
                      ((Fintype.card ι : ℝ) - 1) *
                        Finset.sum Finset.univ
                          (fun i : ι =>
                            ⟪stPrevPrev.yMem i - stPrev.yMem i, dPrev⟫_ℝ) := by
                      simp [inner_add_left, inner_smul_left, Finset.sum_add_distrib,
                        Finset.mul_sum]
                  _ =
                    (Fintype.card ι : ℝ) * ⟪gCurNew - gCurOld, dPrev⟫_ℝ +
                      ((Fintype.card ι : ℝ) - 1) *
                        ⟪gPrevOld - gPrevNew, dPrev⟫_ℝ := by
                      rw [hCur_sum, hPrev_sum, hCur_selected_grad,
                        hPrev_selected_grad]
              have hsum_split :
                  Finset.sum Finset.univ
                      (fun i : ι =>
                        ⟪yTildeNext i - setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                          dPrev⟫_ℝ) =
                    Finset.sum Finset.univ
                        (fun i : ι =>
                          ⟪yTildePrev i - setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                            dPrev⟫_ℝ) +
                              Finset.sum Finset.univ
                                (fun i : ι => ⟪yTildeNext i - yTildePrev i, dPrev⟫_ℝ) := by
                have hpoint :
                    ∀ i : ι,
                      yTildeNext i - setup.gradPsiOnAt z i ⟨xStar, hxStar⟩ =
                        (yTildePrev i - setup.gradPsiOnAt z i ⟨xStar, hxStar⟩) +
                          (yTildeNext i - yTildePrev i) := by
                  intro i
                  module
                calc
                  Finset.sum Finset.univ
                      (fun i : ι =>
                        ⟪yTildeNext i - setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                          dPrev⟫_ℝ) =
                    Finset.sum Finset.univ
                      (fun i : ι =>
                        ⟪(yTildePrev i - setup.gradPsiOnAt z i ⟨xStar, hxStar⟩) +
                            (yTildeNext i - yTildePrev i), dPrev⟫_ℝ) := by
                      refine Finset.sum_congr rfl ?_
                      intro i _hi
                      rw [hpoint i]
                  _ =
                    Finset.sum Finset.univ
                        (fun i : ι =>
                          ⟪yTildePrev i - setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                            dPrev⟫_ℝ) +
                      Finset.sum Finset.univ
                        (fun i : ι => ⟪yTildeNext i - yTildePrev i, dPrev⟫_ℝ) := by
                      rw [← Finset.sum_add_distrib]
                      refine Finset.sum_congr rfl ?_
                      intro i _hi
                      rw [inner_add_left]
              calc
                (Fintype.card ι : ℝ)⁻¹ *
                    Finset.sum Finset.univ
                      (fun i : ι =>
                        ⟪yTildeNext i - setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                          dPrev⟫_ℝ) =
                  (Fintype.card ι : ℝ)⁻¹ *
                    (Finset.sum Finset.univ
                        (fun i : ι =>
                          ⟪yTildePrev i - setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                            dPrev⟫_ℝ) +
                      Finset.sum Finset.univ
                        (fun i : ι => ⟪yTildeNext i - yTildePrev i, dPrev⟫_ℝ)) := by
                    rw [hsum_split]
                _ =
                  (Fintype.card ι : ℝ)⁻¹ *
                      Finset.sum Finset.univ
                        (fun i : ι =>
                          ⟪yTildePrev i - setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                            dPrev⟫_ℝ) +
                    (Fintype.card ι : ℝ)⁻¹ *
                      ((Fintype.card ι : ℝ) * ⟪gCurNew - gCurOld, dPrev⟫_ℝ +
                        ((Fintype.card ι : ℝ) - 1) *
                          ⟪gPrevOld - gPrevNew, dPrev⟫_ℝ) := by
                    rw [hDiff_sum]
                    ring
                _ =
                  (Fintype.card ι : ℝ)⁻¹ *
                      Finset.sum Finset.univ
                        (fun i : ι =>
                          ⟪yTildePrev i - setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                            dPrev⟫_ℝ) +
                    ⟪gCurNew - gCurOld, dPrev⟫_ℝ +
                    ((m - 1) / m) *
                      ⟪gPrevOld - gPrevNew, dPrev⟫_ℝ := by
                    dsimp [m] at hm_ne ⊢
                    field_simp [hm_ne]
                    ring
            have _hYtilde_increment_correction_consumed :=
              hYtilde_increment_correction_identity
            let F : ℕ → ℝ := fun t =>
              let stPrev :=
                setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                  (t - 1) ω
              let stNext :=
                setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                  t ω
              let yTilde : ι → E := fun i =>
                (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
                  stPrev.yMem i
              (Fintype.card ι : ℝ)⁻¹ *
                Finset.sum Finset.univ
                  (fun i =>
                    ⟪yTilde i - setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                      stPrev.x - stNext.x⟫_ℝ)
            let G : ℕ → ℝ := fun t =>
              let stPrev :=
                setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                  (t - 1) ω
              let stNext :=
                setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                  t ω
              let yTilde : ι → E := fun i =>
                (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
                  stPrev.yMem i
              (Fintype.card ι : ℝ)⁻¹ *
                Finset.sum Finset.univ
                  (fun i =>
                    ⟪yTilde i - setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                      stPrev.xPrev - stPrev.x⟫_ℝ)
            let residualBase : ℕ → ℝ := fun t =>
              if ht1 : 1 ≤ t then
                if hts : t ≤ setup.s then
                  let stPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (t - 1) ω
                  let stNext :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      t ω
                  setup.ηSeq t * (setup.μ / 2 * ‖stNext.x - stPrev.x‖ ^ 2) +
                    setup.τSeq t *
                      setup.psiBregmanAt z (setup.ξ (t - 1) ω)
                        ⟨stPrev.xMem (setup.ξ (t - 1) ω),
                          hXMem_mem (t - 1) (le_trans (Nat.sub_le t 1) hts)
                            ω (setup.ξ (t - 1) ω)⟩
                        ⟨stNext.xMem (setup.ξ (t - 1) ω),
                          hXMem_mem t hts ω (setup.ξ (t - 1) ω)⟩
                else 0
              else 0
            have hDeltaExpanded_split :
                Finset.sum (Finset.Icc 1 setup.s)
                    (fun t => setup.γSeq t * deltaExpanded t) =
                  Finset.sum (Finset.Icc 1 setup.s)
                    (fun t =>
                      setup.γSeq t *
                        (residualBase t - (F t - setup.αSeq t * G t))) := by
              refine Finset.sum_congr rfl ?_
              intro t ht
              rcases Finset.mem_Icc.mp ht with ⟨ht1, hts⟩
              let stPrev :=
                setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                  (t - 1) ω
              let stNext :=
                setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω
              let yTilde : ι → E := fun i =>
                (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
                  stPrev.yMem i
              let Y : ι → E := fun i =>
                yTilde i - setup.gradPsiOnAt z i ⟨xStar, hxStar⟩
              let a : E := stPrev.x - stNext.x
              let b : E := stPrev.xPrev - stPrev.x
              let baseTerm : ℝ :=
                setup.ηSeq t * (setup.μ / 2 * ‖stNext.x - stPrev.x‖ ^ 2) +
                  setup.τSeq t *
                    setup.psiBregmanAt z (setup.ξ (t - 1) ω)
                      ⟨stPrev.xMem (setup.ξ (t - 1) ω),
                        hXMem_mem (t - 1) (le_trans (Nat.sub_le t 1) hts)
                          ω (setup.ξ (t - 1) ω)⟩
                      ⟨stNext.xMem (setup.ξ (t - 1) ω),
                        hXMem_mem t hts ω (setup.ξ (t - 1) ω)⟩
              have hinner_shift :
                  (Fintype.card ι : ℝ)⁻¹ *
                      Finset.sum Finset.univ
                        (fun i => ⟪Y i, a - setup.αSeq t • b⟫_ℝ) =
                    F t - setup.αSeq t * G t := by
                calc
                  (Fintype.card ι : ℝ)⁻¹ *
                      Finset.sum Finset.univ
                        (fun i => ⟪Y i, a - setup.αSeq t • b⟫_ℝ) =
                    (Fintype.card ι : ℝ)⁻¹ *
                      Finset.sum Finset.univ
                        (fun i => ⟪Y i, a⟫_ℝ -
                          setup.αSeq t * ⟪Y i, b⟫_ℝ) := by
                      congr 1
                      refine Finset.sum_congr rfl ?_
                      intro i _hi
                      simp [inner_sub_right, inner_smul_right]
                  _ =
                    (Fintype.card ι : ℝ)⁻¹ *
                      (Finset.sum Finset.univ (fun i => ⟪Y i, a⟫_ℝ) -
                        setup.αSeq t *
                          Finset.sum Finset.univ (fun i => ⟪Y i, b⟫_ℝ)) := by
                      rw [Finset.sum_sub_distrib]
                      congr 1
                      rw [Finset.mul_sum]
                  _ = F t - setup.αSeq t * G t := by
                      dsimp [F, G, stPrev, stNext, yTilde, Y, a, b]
                      ring
              have hbase :
                  residualBase t = baseTerm := by
                dsimp [residualBase, baseTerm, stPrev, stNext]
                simp [ht1, hts]
              have hdelta :
                  deltaExpanded t = baseTerm - (F t - setup.αSeq t * G t) := by
                dsimp [deltaExpanded, F, G, baseTerm, stPrev, stNext,
                  yTilde, Y, a, b] at hinner_shift ⊢
                simp [ht1, hts]
                rw [hinner_shift]
                ring
              calc
                setup.γSeq t * deltaExpanded t =
                    setup.γSeq t * (baseTerm - (F t - setup.αSeq t * G t)) := by
                  rw [hdelta]
                _ =
                    setup.γSeq t *
                      (residualBase t - (F t - setup.αSeq t * G t)) := by
                  rw [hbase]
            have hEq634F :
                Finset.sum (Finset.Icc 1 setup.s)
                    (fun t =>
                      setup.γSeq t * (F t - setup.αSeq t * F (t - 1))) =
                  setup.γSeq setup.s *
                    ((1 / m) *
                        Finset.sum Finset.univ (fun i => ⟪u i, v⟫_ℝ) +
                      ((m - 1) / m) *
                        ⟪u (setup.ξ (setup.s - 1) ω) -
                            ((fun i : ι =>
                              setup.gradPsiOnAt z i
                                ⟨stPrevS.xMem i,
                                  hXMem_mem (setup.s - 1)
                                    (Nat.sub_le setup.s 1) ω i⟩)
                                (setup.ξ (setup.s - 1) ω) -
                              setup.gradPsiOnAt z (setup.ξ (setup.s - 1) ω)
                                ⟨xStar, hxStar⟩),
                          v⟫_ℝ) := by
              simpa [F] using hEq634_weighted_core_telescope_terminal
            have _hDeltaExpanded_split_consumed := hDeltaExpanded_split
            have _hEq634F_consumed := hEq634F
            have hG_one_zero : G 1 = 0 := by
              dsimp [G]
              rw [setup.ambientFixedInnerProcess_zero 0 z x0 xMem0 yMem0 hz hx0 ω]
              simp
            have hG_succ_corr :
                ∀ t (ht2 : 2 ≤ t) (hts : t ≤ setup.s),
                  let stPrevPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (t - 2) ω
                  let stPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (t - 1) ω
                  let stNext :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      t ω
                  let dPrev : E := stPrev.xPrev - stPrev.x
                  let jCur : ι := setup.ξ (t - 1) ω
                  let jPrev : ι := setup.ξ (t - 2) ω
                  let gCurNew : E :=
                    setup.gradPsiOnAt z jCur
                      ⟨stNext.xMem jCur, hXMem_mem t hts ω jCur⟩
                  let gCurOld : E :=
                    setup.gradPsiOnAt z jCur
                      ⟨stPrev.xMem jCur,
                        hXMem_mem (t - 1) (by omega) ω jCur⟩
                  let gPrevOld : E :=
                    setup.gradPsiOnAt z jPrev
                      ⟨stPrevPrev.xMem jPrev,
                        hXMem_mem (t - 2) (by omega) ω jPrev⟩
                  let gPrevNew : E :=
                    setup.gradPsiOnAt z jPrev
                      ⟨stPrev.xMem jPrev,
                        hXMem_mem (t - 1) (by omega) ω jPrev⟩
                  G t =
                    F (t - 1) +
                      ⟪gCurNew - gCurOld, dPrev⟫_ℝ +
                      ((m - 1) / m) * ⟪gPrevOld - gPrevNew, dPrev⟫_ℝ := by
              intro t ht2 hts
              let stPrevPrev :=
                setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                  (t - 2) ω
              let stPrev :=
                setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                  (t - 1) ω
              let stNext :=
                setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω
              have hprev_succ : t - 2 + 1 ≤ setup.s := by omega
              have hprev_step_nat : t - 2 + 1 = t - 1 := by omega
              have hxPrev_eq : stPrev.xPrev = stPrevPrev.x := by
                have hstep := hsource_step (t - 2) hprev_succ ω
                have hcomp := congrArg (fun st : RaGradState ι E => st.xPrev) hstep
                simpa [stPrev, stPrevPrev, hprev_step_nat,
                  RandomizedAcceleratedProximalPointSetup.sourceInnerStepAt]
                  using hcomp
              have hident := hYtilde_increment_correction_identity t ht2 hts
              dsimp [G, F] at hident ⊢
              simpa [stPrevPrev, stPrev, stNext, hxPrev_eq, hprev_step_nat]
                using hident
            let correction : ℕ → ℝ := fun t =>
              if ht2 : 2 ≤ t then
                if hts : t ≤ setup.s then
                  let stPrevPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (t - 2) ω
                  let stPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (t - 1) ω
                  let stNext :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      t ω
                  let dPrev : E := stPrev.xPrev - stPrev.x
                  let jCur : ι := setup.ξ (t - 1) ω
                  let jPrev : ι := setup.ξ (t - 2) ω
                  let gCurNew : E :=
                    setup.gradPsiOnAt z jCur
                      ⟨stNext.xMem jCur, hXMem_mem t hts ω jCur⟩
                  let gCurOld : E :=
                    setup.gradPsiOnAt z jCur
                      ⟨stPrev.xMem jCur,
                        hXMem_mem (t - 1) (by omega) ω jCur⟩
                  let gPrevOld : E :=
                    setup.gradPsiOnAt z jPrev
                      ⟨stPrevPrev.xMem jPrev,
                        hXMem_mem (t - 2) (by omega) ω jPrev⟩
                  let gPrevNew : E :=
                    setup.gradPsiOnAt z jPrev
                      ⟨stPrev.xMem jPrev,
                        hXMem_mem (t - 1) (by omega) ω jPrev⟩
                  ⟪gCurNew - gCurOld, dPrev⟫_ℝ +
                    ((m - 1) / m) * ⟪gPrevOld - gPrevNew, dPrev⟫_ℝ
                else 0
              else 0
            have hF_zero : F 0 = 0 := by
              simp [F]
            have hG_as_F_plus_correction :
                ∀ t ∈ Finset.Icc 1 setup.s,
                  G t = F (t - 1) + correction t := by
              intro t ht
              rcases Finset.mem_Icc.mp ht with ⟨ht1, hts⟩
              by_cases ht2 : 2 ≤ t
              · have hcorr := hG_succ_corr t ht2 hts
                simpa [correction, ht2, hts, add_assoc] using hcorr
              · have ht_eq : t = 1 := by omega
                subst t
                calc
                  G 1 = 0 := hG_one_zero
                  _ = F (1 - 1) + correction 1 := by
                    simp [hF_zero, correction]
            have hFG_weighted_split :
                Finset.sum (Finset.Icc 1 setup.s)
                    (fun t => setup.γSeq t * (F t - setup.αSeq t * G t)) =
                  Finset.sum (Finset.Icc 1 setup.s)
                      (fun t =>
                        setup.γSeq t * (F t - setup.αSeq t * F (t - 1))) -
                    Finset.sum (Finset.Icc 1 setup.s)
                      (fun t => setup.γSeq t * (setup.αSeq t * correction t)) := by
              calc
                Finset.sum (Finset.Icc 1 setup.s)
                    (fun t => setup.γSeq t * (F t - setup.αSeq t * G t)) =
                  Finset.sum (Finset.Icc 1 setup.s)
                    (fun t =>
                      setup.γSeq t * (F t - setup.αSeq t * F (t - 1)) -
                        setup.γSeq t * (setup.αSeq t * correction t)) := by
                    refine Finset.sum_congr rfl ?_
                    intro t ht
                    rw [hG_as_F_plus_correction t ht]
                    ring
                _ =
                  Finset.sum (Finset.Icc 1 setup.s)
                      (fun t =>
                        setup.γSeq t * (F t - setup.αSeq t * F (t - 1))) -
                    Finset.sum (Finset.Icc 1 setup.s)
                      (fun t => setup.γSeq t * (setup.αSeq t * correction t)) := by
                    rw [Finset.sum_sub_distrib]
            have hDeltaExpanded_regroup :
                Finset.sum (Finset.Icc 1 setup.s)
                    (fun t => setup.γSeq t * deltaExpanded t) =
                  Finset.sum (Finset.Icc 1 setup.s)
                      (fun t => setup.γSeq t * residualBase t) -
                    Finset.sum (Finset.Icc 1 setup.s)
                      (fun t =>
                        setup.γSeq t * (F t - setup.αSeq t * F (t - 1))) +
                    Finset.sum (Finset.Icc 1 setup.s)
                      (fun t => setup.γSeq t * (setup.αSeq t * correction t)) := by
              calc
                Finset.sum (Finset.Icc 1 setup.s)
                    (fun t => setup.γSeq t * deltaExpanded t) =
                  Finset.sum (Finset.Icc 1 setup.s)
                    (fun t =>
                      setup.γSeq t *
                        (residualBase t - (F t - setup.αSeq t * G t))) := by
                    rw [hDeltaExpanded_split]
                _ =
                  Finset.sum (Finset.Icc 1 setup.s)
                    (fun t =>
                      setup.γSeq t * residualBase t -
                        setup.γSeq t * (F t - setup.αSeq t * G t)) := by
                    refine Finset.sum_congr rfl ?_
                    intro t _ht
                    ring
                _ =
                  Finset.sum (Finset.Icc 1 setup.s)
                      (fun t => setup.γSeq t * residualBase t) -
                    Finset.sum (Finset.Icc 1 setup.s)
                      (fun t => setup.γSeq t * (F t - setup.αSeq t * G t)) := by
                    rw [Finset.sum_sub_distrib]
                _ =
                  Finset.sum (Finset.Icc 1 setup.s)
                      (fun t => setup.γSeq t * residualBase t) -
                    (Finset.sum (Finset.Icc 1 setup.s)
                        (fun t =>
                          setup.γSeq t * (F t - setup.αSeq t * F (t - 1))) -
                      Finset.sum (Finset.Icc 1 setup.s)
                        (fun t => setup.γSeq t * (setup.αSeq t * correction t))) := by
                    rw [hFG_weighted_split]
                _ =
                  Finset.sum (Finset.Icc 1 setup.s)
                      (fun t => setup.γSeq t * residualBase t) -
                    Finset.sum (Finset.Icc 1 setup.s)
                      (fun t =>
                        setup.γSeq t * (F t - setup.αSeq t * F (t - 1))) +
                    Finset.sum (Finset.Icc 1 setup.s)
                      (fun t => setup.γSeq t * (setup.αSeq t * correction t)) := by
                    ring
            rw [hDeltaExpanded_regroup, hEq634F]
            have hAbsorbedCorrections :
                setup.γSeq setup.s * (A * ‖v‖ ^ 2) ≤
                  Finset.sum (Finset.Icc 1 setup.s)
                      (fun t => setup.γSeq t * residualBase t) -
                    setup.γSeq setup.s *
                      (((m - 1) / m) *
                        ⟪u (setup.ξ (setup.s - 1) ω) -
                            ((fun i : ι =>
                              setup.gradPsiOnAt z i
                                ⟨stPrevS.xMem i,
                                  hXMem_mem (setup.s - 1)
                                    (Nat.sub_le setup.s 1) ω i⟩)
                                (setup.ξ (setup.s - 1) ω) -
                              setup.gradPsiOnAt z (setup.ξ (setup.s - 1) ω)
                                ⟨xStar, hxStar⟩),
                          v⟫_ℝ) +
                    Finset.sum (Finset.Icc 1 setup.s)
                      (fun t => setup.γSeq t * (setup.αSeq t * correction t)) := by
              let j : ι := setup.ξ (setup.s - 1) ω
              let gTerminal : E :=
                u j -
                  ((fun i : ι =>
                    setup.gradPsiOnAt z i
                      ⟨stPrevS.xMem i,
                        hXMem_mem (setup.s - 1)
                          (Nat.sub_le setup.s 1) ω i⟩) j -
                    setup.gradPsiOnAt z j ⟨xStar, hxStar⟩)
              let BTerminal : ℝ :=
                setup.psiBregmanAt z j
                  ⟨stPrevS.xMem j,
                    hXMem_mem (setup.s - 1)
                      (Nat.sub_le setup.s 1) ω j⟩
                  ⟨stS.xMem j, hXMem_mem setup.s le_rfl ω j⟩
              have hm_pos : 0 < m := by
                dsimp [m]
                exact_mod_cast
                  (Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι))
              have hm_ne : m ≠ 0 := ne_of_gt hm_pos
              have hm_ge_one : (1 : ℝ) ≤ m := by
                dsimp [m]
                exact_mod_cast
                  (Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι))
              have hLhat_pos : 0 < setup.Lhat := by
                rw [setup.Lhat_def]
                nlinarith [setup.L_pos, setup.hμ_pos]
              have hτs_pos : 0 < setup.τSeq setup.s :=
                hτSeq_pos setup.s hs le_rfl
              have hγs_nonneg : 0 ≤ setup.γSeq setup.s :=
                hγSeq_nonneg setup.s hs le_rfl
              have hc_terminal_nonneg : 0 ≤ (m - 1) / m := by
                exact div_nonneg (sub_nonneg.mpr hm_ge_one) (le_of_lt hm_pos)
              have hterminal_coeff :
                  ((m - 1) / m) ^ 2 * setup.Lhat / setup.τSeq setup.s ≤ A := by
                have hcoef := hResidualTerminalVarianceCoeff_nonneg
                have hτs_ne : setup.τSeq setup.s ≠ 0 := ne_of_gt hτs_pos
                dsimp [A, m] at hcoef ⊢
                field_simp [hm_ne, hτs_ne] at hcoef ⊢
                nlinarith [hcoef]
              have hbreg_terminal :
                  (1 / (2 * setup.Lhat)) * ‖gTerminal‖ ^ 2 ≤ BTerminal := by
                have hco := hResidualStep_cocoercivity setup.s hs le_rfl
                have hg :
                    gTerminal =
                      -((setup.gradPsiOnAt z j
                          ⟨stPrevS.xMem j,
                            hXMem_mem (setup.s - 1)
                              (Nat.sub_le setup.s 1) ω j⟩) -
                        setup.gradPsiOnAt z j
                          ⟨stS.xMem j, hXMem_mem setup.s le_rfl ω j⟩) := by
                  dsimp [gTerminal, u, j]
                  module
                calc
                  (1 / (2 * setup.Lhat)) * ‖gTerminal‖ ^ 2 =
                      (1 / (2 * setup.Lhat)) *
                        ‖(setup.gradPsiOnAt z j
                            ⟨stPrevS.xMem j,
                              hXMem_mem (setup.s - 1)
                                (Nat.sub_le setup.s 1) ω j⟩) -
                          setup.gradPsiOnAt z j
                            ⟨stS.xMem j, hXMem_mem setup.s le_rfl ω j⟩‖ ^ 2 := by
                    rw [hg, norm_neg]
                  _ ≤ BTerminal := by
                    simpa [BTerminal, j, stPrevS, stS] using hco
              have hterminal_sample_absorb :
                  0 ≤
                    setup.γSeq setup.s *
                      (A * ‖v‖ ^ 2 + (setup.τSeq setup.s / 2) * BTerminal -
                        ((m - 1) / m) *
                          ⟪u (setup.ξ (setup.s - 1) ω) -
                              ((fun i : ι =>
                                setup.gradPsiOnAt z i
                                  ⟨stPrevS.xMem i,
                                    hXMem_mem (setup.s - 1)
                                      (Nat.sub_le setup.s 1) ω i⟩)
                                  (setup.ξ (setup.s - 1) ω) -
                                setup.gradPsiOnAt z (setup.ξ (setup.s - 1) ω)
                                  ⟨xStar, hxStar⟩),
                            v⟫_ℝ) := by
                have hraw :=
                  lemma_6_13_terminal_sample_correction_absorption
                    (L := setup.Lhat) (tau := setup.τSeq setup.s) (A := A)
                    (gamma := setup.γSeq setup.s) (c := (m - 1) / m)
                    (B := BTerminal) (g := gTerminal) (v := v)
                    hLhat_pos hτs_pos hγs_nonneg hc_terminal_nonneg
                    hterminal_coeff hbreg_terminal
                simpa [gTerminal, j] using hraw
              have hInteriorResidualCorrection_nonneg :
                  0 ≤
                    Finset.sum (Finset.Icc 1 setup.s)
                        (fun t => setup.γSeq t * residualBase t) -
                      setup.γSeq setup.s *
                        ((2 * A) * ‖v‖ ^ 2 +
                          (setup.τSeq setup.s / 2) * BTerminal) +
                      Finset.sum (Finset.Icc 1 setup.s)
                        (fun t => setup.γSeq t * (setup.αSeq t * correction t)) := by
                have hc_nonneg : 0 ≤ (m - 1) / m := by
                  exact div_nonneg (sub_nonneg.mpr hm_ge_one) (le_of_lt hm_pos)
                have hInteriorPointwise :
                    ∀ t (ht2 : 2 ≤ t) (hts : t ≤ setup.s),
                      let stPrevPrev :=
                        setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0
                          hz hx0 (t - 2) ω
                      let stPrev :=
                        setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0
                          hz hx0 (t - 1) ω
                      let stNext :=
                        setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0
                          hz hx0 t ω
                      let dPrev : E := stPrev.xPrev - stPrev.x
                      let jCur : ι := setup.ξ (t - 1) ω
                      let jPrev : ι := setup.ξ (t - 2) ω
                      let gCurNew : E :=
                        setup.gradPsiOnAt z jCur
                          ⟨stNext.xMem jCur, hXMem_mem t hts ω jCur⟩
                      let gCurOld : E :=
                        setup.gradPsiOnAt z jCur
                          ⟨stPrev.xMem jCur,
                            hXMem_mem (t - 1) (by omega) ω jCur⟩
                      let gPrevOld : E :=
                        setup.gradPsiOnAt z jPrev
                          ⟨stPrevPrev.xMem jPrev,
                            hXMem_mem (t - 2) (by omega) ω jPrev⟩
                      let gPrevNew : E :=
                        setup.gradPsiOnAt z jPrev
                          ⟨stPrev.xMem jPrev,
                            hXMem_mem (t - 1) (by omega) ω jPrev⟩
                      let BCur : ℝ :=
                        setup.psiBregmanAt z jCur
                          ⟨stPrev.xMem jCur,
                            hXMem_mem (t - 1) (by omega) ω jCur⟩
                          ⟨stNext.xMem jCur, hXMem_mem t hts ω jCur⟩
                      let BPrev : ℝ :=
                        setup.psiBregmanAt z jPrev
                          ⟨stPrevPrev.xMem jPrev,
                            hXMem_mem (t - 2) (by omega) ω jPrev⟩
                          ⟨stPrev.xMem jPrev,
                            hXMem_mem (t - 1) (by omega) ω jPrev⟩
                      0 ≤
                        setup.γSeq (t - 1) *
                            ((setup.ηSeq (t - 1) * setup.μ / 2) *
                              ‖dPrev‖ ^ 2) +
                          setup.γSeq t * ((setup.τSeq t / 2) * BCur) +
                          setup.γSeq (t - 1) *
                            ((setup.τSeq (t - 1) / 2) * BPrev) +
                          setup.γSeq t * (setup.αSeq t * correction t) := by
                  intro t ht2 hts
                  let stPrevPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0
                      hz hx0 (t - 2) ω
                  let stPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0
                      hz hx0 (t - 1) ω
                  let stNext :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0
                      hz hx0 t ω
                  let dPrev : E := stPrev.xPrev - stPrev.x
                  let jCur : ι := setup.ξ (t - 1) ω
                  let jPrev : ι := setup.ξ (t - 2) ω
                  let gCurNew : E :=
                    setup.gradPsiOnAt z jCur
                      ⟨stNext.xMem jCur, hXMem_mem t hts ω jCur⟩
                  let gCurOld : E :=
                    setup.gradPsiOnAt z jCur
                      ⟨stPrev.xMem jCur,
                        hXMem_mem (t - 1) (by omega) ω jCur⟩
                  let gPrevOld : E :=
                    setup.gradPsiOnAt z jPrev
                      ⟨stPrevPrev.xMem jPrev,
                        hXMem_mem (t - 2) (by omega) ω jPrev⟩
                  let gPrevNew : E :=
                    setup.gradPsiOnAt z jPrev
                      ⟨stPrev.xMem jPrev,
                        hXMem_mem (t - 1) (by omega) ω jPrev⟩
                  let BCur : ℝ :=
                    setup.psiBregmanAt z jCur
                      ⟨stPrev.xMem jCur,
                        hXMem_mem (t - 1) (by omega) ω jCur⟩
                      ⟨stNext.xMem jCur, hXMem_mem t hts ω jCur⟩
                  let BPrev : ℝ :=
                    setup.psiBregmanAt z jPrev
                      ⟨stPrevPrev.xMem jPrev,
                        hXMem_mem (t - 2) (by omega) ω jPrev⟩
                      ⟨stPrev.xMem jPrev,
                        hXMem_mem (t - 1) (by omega) ω jPrev⟩
                  have ht_prev_one : 1 ≤ t - 1 := by omega
                  have ht_prev_succ : t - 1 + 1 ≤ setup.s := by omega
                  have ht_prev_le : t - 1 ≤ setup.s := by omega
                  have ht_prev_succ_eq : t - 1 + 1 = t := by omega
                  have hshift :
                      setup.γSeq (t - 1) = setup.αSeq t * setup.γSeq t := by
                    simpa [ht_prev_succ_eq] using
                      hResidualAlphaGammaShift (t - 1) ht_prev_one ht_prev_succ
                  have hγprev_nonneg :
                      0 ≤ setup.γSeq (t - 1) :=
                    hγSeq_nonneg (t - 1) ht_prev_one ht_prev_le
                  have hγcur_nonneg : 0 ≤ setup.γSeq t :=
                    hγSeq_nonneg t (by omega) hts
                  have hα_nonneg : 0 ≤ setup.αSeq t :=
                    setup.hαSeq_nonneg t (by omega) hts
                  have hτprev_pos : 0 < setup.τSeq (t - 1) :=
                    hτSeq_pos (t - 1) ht_prev_one ht_prev_le
                  have hτcur_pos : 0 < setup.τSeq t :=
                    hτSeq_pos t (by omega) hts
                  have hcoef :
                      0 ≤
                        setup.γSeq (t - 1) *
                          (setup.ηSeq (t - 1) * setup.μ / 2 -
                            setup.αSeq t * setup.Lhat / setup.τSeq t -
                            (m - 1) ^ 2 * setup.Lhat /
                              (m ^ 2 * setup.τSeq (t - 1))) := by
                    have hraw :=
                      hResidualInteriorVarianceCoeff_nonneg (t - 1)
                        ht_prev_one ht_prev_succ
                    dsimp [m] at hraw ⊢
                    simpa [ht_prev_succ_eq] using hraw
                  have hcoef_helper :
                      0 ≤
                        setup.γSeq (t - 1) *
                          (setup.ηSeq (t - 1) * setup.μ / 2 -
                            setup.αSeq t * setup.Lhat / setup.τSeq t -
                            ((m - 1) / m) ^ 2 * setup.Lhat /
                              setup.τSeq (t - 1)) := by
                    have hτprev_ne : setup.τSeq (t - 1) ≠ 0 :=
                      ne_of_gt hτprev_pos
                    convert hcoef using 2
                    field_simp [hm_ne, hτprev_ne]
                  have hbcur :
                      (1 / (2 * setup.Lhat)) *
                          ‖gCurNew - gCurOld‖ ^ 2 ≤ BCur := by
                    calc
                      (1 / (2 * setup.Lhat)) *
                          ‖gCurNew - gCurOld‖ ^ 2 =
                        (1 / (2 * setup.Lhat)) *
                          ‖gCurOld - gCurNew‖ ^ 2 := by
                          rw [norm_sub_rev]
                      _ ≤ BCur := by
                        simpa [gCurNew, gCurOld, BCur, stPrev, stNext, jCur]
                          using hResidualStep_cocoercivity t (by omega) hts
                  have hbprev :
                      (1 / (2 * setup.Lhat)) *
                          ‖gPrevOld - gPrevNew‖ ^ 2 ≤ BPrev := by
                    have hprev :=
                      hResidualStep_cocoercivity (t - 1) ht_prev_one ht_prev_le
                    simpa [gPrevOld, gPrevNew, BPrev, stPrevPrev, stPrev,
                      jPrev] using hprev
                  have hraw :
                      0 ≤
                        setup.γSeq (t - 1) *
                            ((setup.ηSeq (t - 1) * setup.μ / 2) *
                              ‖dPrev‖ ^ 2) +
                          setup.γSeq t * ((setup.τSeq t / 2) * BCur) +
                          setup.γSeq (t - 1) *
                            ((setup.τSeq (t - 1) / 2) * BPrev) +
                          setup.γSeq (t - 1) *
                            (⟪gCurNew - gCurOld, dPrev⟫_ℝ +
                              (m - 1) / m *
                                ⟪gPrevOld - gPrevNew, dPrev⟫_ℝ) := by
                    exact
                      lemma_6_13_interior_two_correction_absorption
                        (L := setup.Lhat) (tauPrev := setup.τSeq (t - 1))
                        (tauCur := setup.τSeq t)
                        (eta := setup.ηSeq (t - 1) * setup.μ / 2)
                        (alpha := setup.αSeq t)
                        (gammaPrev := setup.γSeq (t - 1))
                        (gammaCur := setup.γSeq t) (c := (m - 1) / m)
                        (BPrev := BPrev) (BCur := BCur)
                        (gCur := gCurNew - gCurOld)
                        (gPrev := gPrevOld - gPrevNew) (d := dPrev)
                        hLhat_pos hτprev_pos hτcur_pos hγprev_nonneg
                        hγcur_nonneg hα_nonneg hc_nonneg hshift hcoef_helper
                        hbcur hbprev
                  have hcorr :
                      correction t =
                        ⟪gCurNew - gCurOld, dPrev⟫_ℝ +
                          (m - 1) / m *
                            ⟪gPrevOld - gPrevNew, dPrev⟫_ℝ := by
                    simp [correction, ht2, hts, stPrevPrev, stPrev, stNext,
                      dPrev, jCur, jPrev, gCurNew, gCurOld, gPrevOld,
                      gPrevNew]
                  have hrewrite :
                      setup.γSeq t * (setup.αSeq t * correction t) =
                        setup.γSeq (t - 1) *
                          (⟪gCurNew - gCurOld, dPrev⟫_ℝ +
                            (m - 1) / m *
                              ⟪gPrevOld - gPrevNew, dPrev⟫_ℝ) := by
                    rw [hcorr, hshift]
                    ring
                  rw [← hrewrite] at hraw
                  simpa [stPrevPrev, stPrev, stNext, dPrev, jCur, jPrev,
                    gCurNew, gCurOld, gPrevOld, gPrevNew, BCur, BPrev] using hraw
                have hInteriorSum_nonneg :
                    0 ≤
                      Finset.sum (Finset.Icc 2 setup.s) (fun t =>
                        if ht2 : 2 ≤ t then
                          if hts : t ≤ setup.s then
                            let stPrevPrev :=
                              setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0
                                hz hx0 (t - 2) ω
                            let stPrev :=
                              setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0
                                hz hx0 (t - 1) ω
                            let stNext :=
                              setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0
                                hz hx0 t ω
                            let dPrev : E := stPrev.xPrev - stPrev.x
                            let jCur : ι := setup.ξ (t - 1) ω
                            let jPrev : ι := setup.ξ (t - 2) ω
                            let gCurNew : E :=
                              setup.gradPsiOnAt z jCur
                                ⟨stNext.xMem jCur,
                                  hXMem_mem t hts ω jCur⟩
                            let gCurOld : E :=
                              setup.gradPsiOnAt z jCur
                                ⟨stPrev.xMem jCur,
                                  hXMem_mem (t - 1) (by omega) ω jCur⟩
                            let gPrevOld : E :=
                              setup.gradPsiOnAt z jPrev
                                ⟨stPrevPrev.xMem jPrev,
                                  hXMem_mem (t - 2) (by omega) ω jPrev⟩
                            let gPrevNew : E :=
                              setup.gradPsiOnAt z jPrev
                                ⟨stPrev.xMem jPrev,
                                  hXMem_mem (t - 1) (by omega) ω jPrev⟩
                            let BCur : ℝ :=
                              setup.psiBregmanAt z jCur
                                ⟨stPrev.xMem jCur,
                                  hXMem_mem (t - 1) (by omega) ω jCur⟩
                                ⟨stNext.xMem jCur,
                                  hXMem_mem t hts ω jCur⟩
                            let BPrev : ℝ :=
                              setup.psiBregmanAt z jPrev
                                ⟨stPrevPrev.xMem jPrev,
                                  hXMem_mem (t - 2) (by omega) ω jPrev⟩
                                ⟨stPrev.xMem jPrev,
                                  hXMem_mem (t - 1) (by omega) ω jPrev⟩
                            setup.γSeq (t - 1) *
                                ((setup.ηSeq (t - 1) * setup.μ / 2) *
                                  ‖dPrev‖ ^ 2) +
                              setup.γSeq t * ((setup.τSeq t / 2) * BCur) +
                              setup.γSeq (t - 1) *
                                ((setup.τSeq (t - 1) / 2) * BPrev) +
                              setup.γSeq t * (setup.αSeq t * correction t)
                          else 0
                        else 0) := by
                  refine Finset.sum_nonneg ?_
                  intro t ht
                  rcases Finset.mem_Icc.mp ht with ⟨ht2, hts⟩
                  simp [ht2, hts, hInteriorPointwise t ht2 hts]
                -- Remaining Eq. (6.6.35) interior work: rewrite the selected
                -- residual/correction sum as this nonnegative interior sum plus
                -- the endpoint half-Bregman slack.
                let e : ℕ → ℝ := fun t =>
                  if ht1 : 1 ≤ t then
                    if hts : t ≤ setup.s then
                      let stNext :=
                        setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0
                          hz hx0 t ω
                      setup.ηSeq t * (setup.μ / 2 * ‖stNext.xPrev - stNext.x‖ ^ 2)
                    else 0
                  else 0
                let b : ℕ → ℝ := fun t =>
                  if ht1 : 1 ≤ t then
                    if hts : t ≤ setup.s then
                      let stPrev :=
                        setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0
                          hz hx0 (t - 1) ω
                      let stNext :=
                        setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0
                          hz hx0 t ω
                      setup.τSeq t *
                        setup.psiBregmanAt z (setup.ξ (t - 1) ω)
                          ⟨stPrev.xMem (setup.ξ (t - 1) ω),
                            hXMem_mem (t - 1) (le_trans (Nat.sub_le t 1) hts)
                              ω (setup.ξ (t - 1) ω)⟩
                          ⟨stNext.xMem (setup.ξ (t - 1) ω),
                            hXMem_mem t hts ω (setup.ξ (t - 1) ω)⟩
                    else 0
                  else 0
                have hc1 : correction 1 = 0 := by
                  simp [correction]
                have hresidual_point :
                    ∀ t ∈ Finset.Icc 1 setup.s,
                      residualBase t = e t + b t := by
                  intro t ht
                  rcases Finset.mem_Icc.mp ht with ⟨ht1, hts⟩
                  let stPrev :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0
                      hz hx0 (t - 1) ω
                  let stNext :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0
                      hz hx0 t ω
                  have htstep : t - 1 + 1 ≤ setup.s := by omega
                  have htstep_eq : t - 1 + 1 = t := by omega
                  have hxPrev : stNext.xPrev = stPrev.x := by
                    have hstep := hsource_step (t - 1) htstep ω
                    have hcomp :=
                      congrArg (fun st : RaGradState ι E => st.xPrev) hstep
                    simpa [stPrev, stNext, htstep_eq,
                      RandomizedAcceleratedProximalPointSetup.sourceInnerStepAt]
                      using hcomp
                  have hnorm :
                      ‖stNext.x - stPrev.x‖ =
                        ‖stNext.xPrev - stNext.x‖ := by
                    rw [hxPrev, norm_sub_rev]
                  dsimp [residualBase, e, b, stPrev, stNext]
                  simp [ht1, hts]
                  rw [← hnorm]
                  simp [stPrev, stNext]
                have hresidual_sum :
                    Finset.sum (Finset.Icc 1 setup.s)
                        (fun t => setup.γSeq t * residualBase t) =
                      Finset.sum (Finset.Icc 1 setup.s)
                        (fun t => setup.γSeq t * (e t + b t)) := by
                  refine Finset.sum_congr rfl ?_
                  intro t ht
                  rw [hresidual_point t ht]
                have hsstep_eq : setup.s - 1 + 1 = setup.s :=
                  Nat.sub_add_cancel hs
                have hxPrevS : stS.xPrev = stPrevS.x := by
                  have hstep := hsource_step (setup.s - 1) hsuccS ω
                  have hcomp :=
                    congrArg (fun st : RaGradState ι E => st.xPrev) hstep
                  simpa [stPrevS, stS, hsstep_eq,
                    RandomizedAcceleratedProximalPointSetup.sourceInnerStepAt]
                    using hcomp
                have hterminal_decomp :
                    (2 * A) * ‖v‖ ^ 2 +
                        (setup.τSeq setup.s / 2) * BTerminal =
                      e setup.s + b setup.s / 2 := by
                  have hnormS : ‖stPrevS.x - stS.x‖ = ‖stS.xPrev - stS.x‖ := by
                    rw [hxPrevS]
                  dsimp [A, e, b, v, BTerminal, j, stPrevS, stS]
                  simp [hs]
                  rw [← hnormS]
                  ring
                have hsum_decomp :=
                  sum_Icc_residual_endpoint_half_decomp
                    setup.γSeq setup.αSeq e b correction setup.s hs hc1
                have htarget_decomp :
                    Finset.sum (Finset.Icc 1 setup.s)
                        (fun t => setup.γSeq t * residualBase t) -
                        setup.γSeq setup.s *
                          ((2 * A) * ‖v‖ ^ 2 +
                            (setup.τSeq setup.s / 2) * BTerminal) +
                        Finset.sum (Finset.Icc 1 setup.s)
                          (fun t => setup.γSeq t *
                            (setup.αSeq t * correction t)) =
                      Finset.sum (Finset.Icc 2 setup.s) (fun t =>
                          setup.γSeq (t - 1) * e (t - 1) +
                            setup.γSeq t * (b t / 2) +
                            setup.γSeq (t - 1) * (b (t - 1) / 2) +
                            setup.γSeq t * (setup.αSeq t * correction t)) +
                        setup.γSeq 1 * (b 1 / 2) := by
                  calc
                    Finset.sum (Finset.Icc 1 setup.s)
                        (fun t => setup.γSeq t * residualBase t) -
                        setup.γSeq setup.s *
                          ((2 * A) * ‖v‖ ^ 2 +
                            (setup.τSeq setup.s / 2) * BTerminal) +
                        Finset.sum (Finset.Icc 1 setup.s)
                          (fun t => setup.γSeq t *
                            (setup.αSeq t * correction t)) =
                      Finset.sum (Finset.Icc 1 setup.s)
                          (fun t => setup.γSeq t * (e t + b t)) -
                        setup.γSeq setup.s *
                          (e setup.s + b setup.s / 2) +
                        Finset.sum (Finset.Icc 1 setup.s)
                          (fun t => setup.γSeq t *
                            (setup.αSeq t * correction t)) := by
                        rw [hresidual_sum, hterminal_decomp]
                    _ =
                      Finset.sum (Finset.Icc 2 setup.s) (fun t =>
                          setup.γSeq (t - 1) * e (t - 1) +
                            setup.γSeq t * (b t / 2) +
                            setup.γSeq (t - 1) * (b (t - 1) / 2) +
                            setup.γSeq t * (setup.αSeq t * correction t)) +
                        setup.γSeq 1 * (b 1 / 2) := hsum_decomp
                have hInteriorSum_match :
                    Finset.sum (Finset.Icc 2 setup.s) (fun t =>
                        setup.γSeq (t - 1) * e (t - 1) +
                          setup.γSeq t * (b t / 2) +
                          setup.γSeq (t - 1) * (b (t - 1) / 2) +
                          setup.γSeq t * (setup.αSeq t * correction t)) =
                      Finset.sum (Finset.Icc 2 setup.s) (fun t =>
                        if ht2 : 2 ≤ t then
                          if hts : t ≤ setup.s then
                            let stPrevPrev :=
                              setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0
                                hz hx0 (t - 2) ω
                            let stPrev :=
                              setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0
                                hz hx0 (t - 1) ω
                            let stNext :=
                              setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0
                                hz hx0 t ω
                            let dPrev : E := stPrev.xPrev - stPrev.x
                            let jCur : ι := setup.ξ (t - 1) ω
                            let jPrev : ι := setup.ξ (t - 2) ω
                            let gCurNew : E :=
                              setup.gradPsiOnAt z jCur
                                ⟨stNext.xMem jCur,
                                  hXMem_mem t hts ω jCur⟩
                            let gCurOld : E :=
                              setup.gradPsiOnAt z jCur
                                ⟨stPrev.xMem jCur,
                                  hXMem_mem (t - 1) (by omega) ω jCur⟩
                            let gPrevOld : E :=
                              setup.gradPsiOnAt z jPrev
                                ⟨stPrevPrev.xMem jPrev,
                                  hXMem_mem (t - 2) (by omega) ω jPrev⟩
                            let gPrevNew : E :=
                              setup.gradPsiOnAt z jPrev
                                ⟨stPrev.xMem jPrev,
                                  hXMem_mem (t - 1) (by omega) ω jPrev⟩
                            let BCur : ℝ :=
                              setup.psiBregmanAt z jCur
                                ⟨stPrev.xMem jCur,
                                  hXMem_mem (t - 1) (by omega) ω jCur⟩
                                ⟨stNext.xMem jCur,
                                  hXMem_mem t hts ω jCur⟩
                            let BPrev : ℝ :=
                              setup.psiBregmanAt z jPrev
                                ⟨stPrevPrev.xMem jPrev,
                                  hXMem_mem (t - 2) (by omega) ω jPrev⟩
                                ⟨stPrev.xMem jPrev,
                                  hXMem_mem (t - 1) (by omega) ω jPrev⟩
                            setup.γSeq (t - 1) *
                                ((setup.ηSeq (t - 1) * setup.μ / 2) *
                                  ‖dPrev‖ ^ 2) +
                              setup.γSeq t * ((setup.τSeq t / 2) * BCur) +
                              setup.γSeq (t - 1) *
                                ((setup.τSeq (t - 1) / 2) * BPrev) +
                              setup.γSeq t * (setup.αSeq t * correction t)
                          else 0
                        else 0) := by
                  refine Finset.sum_congr rfl ?_
                  intro t ht
                  rcases Finset.mem_Icc.mp ht with ⟨ht2, hts⟩
                  have htprev1 : 1 ≤ t - 1 := by omega
                  have htprevs : t - 1 ≤ setup.s := by omega
                  have ht1cur : 1 ≤ t := by omega
                  have hsubsub : t - 1 - 1 = t - 2 := by omega
                  dsimp [e, b]
                  simp [ht2, hts, htprev1, htprevs, ht1cur, hsubsub]
                  ring
                have hInteriorHelper_nonneg :
                    0 ≤
                      Finset.sum (Finset.Icc 2 setup.s) (fun t =>
                        setup.γSeq (t - 1) * e (t - 1) +
                          setup.γSeq t * (b t / 2) +
                          setup.γSeq (t - 1) * (b (t - 1) / 2) +
                          setup.γSeq t * (setup.αSeq t * correction t)) := by
                  rw [hInteriorSum_match]
                  exact hInteriorSum_nonneg
                have hb1_nonneg : 0 ≤ b 1 := by
                  let st0 :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0
                      hz hx0 0 ω
                  let st1 :=
                    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0
                      hz hx0 1 ω
                  let j1 : ι := setup.ξ 0 ω
                  have hτ1_nonneg : 0 ≤ setup.τSeq 1 :=
                    le_of_lt (hτSeq_pos 1 le_rfl hs)
                  have hB1_nonneg :
                      0 ≤
                        setup.psiBregmanAt z j1
                          ⟨st0.xMem j1, hXMem_mem 0 (by omega) ω j1⟩
                          ⟨st1.xMem j1, hXMem_mem 1 hs ω j1⟩ := by
                    have hlow :=
                      (hPsiCurv j1
                        ⟨st0.xMem j1, hXMem_mem 0 (by omega) ω j1⟩
                        ⟨st1.xMem j1, hXMem_mem 1 hs ω j1⟩).1
                    have hleft_nonneg :
                        0 ≤
                          setup.μ / 2 *
                            ‖st0.xMem j1 - st1.xMem j1‖ ^ 2 := by
                      have hμ_nonneg : 0 ≤ setup.μ := le_of_lt setup.hμ_pos
                      nlinarith [sq_nonneg ‖st0.xMem j1 - st1.xMem j1‖]
                    exact le_trans hleft_nonneg hlow
                  dsimp [b, st0, st1, j1]
                  simp [hs]
                  exact mul_nonneg hτ1_nonneg hB1_nonneg
                have hfirst_nonneg : 0 ≤ setup.γSeq 1 * (b 1 / 2) := by
                  exact mul_nonneg (hγSeq_nonneg 1 le_rfl hs)
                    (div_nonneg hb1_nonneg (by norm_num))
                rw [htarget_decomp]
                exact add_nonneg hInteriorHelper_nonneg hfirst_nonneg
              linarith [hterminal_sample_absorb,
                hInteriorResidualCorrection_nonneg]
            dsimp [terminalCore]
            nlinarith
          simpa [hDelta_xTilde_expanded] using hResidual_expanded_lower
        -- Source bridge still needed: unfold `delta`, use (6.6.33)-(6.6.35),
        -- then consume the residual coefficient facts above and terminal Young.
        exact le_trans hTerminalAverage_memory_absorption
          hResidual_regrouping_lower
      have hDeltaSum_int :
          Integrable
            (fun ω : Ω =>
              Finset.sum (Finset.Icc 1 setup.s)
                (fun t => setup.γSeq t * delta t ω)) setup.P := by
        refine setup.ambientFixed_prefix_integrable_real 0 setup.s ?_
        intro ω ω' hprefix
        have hstate :
            ∀ n (hn : n ≤ setup.s),
              setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω =
                setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω' := by
          intro n hn
          have hprefix_n :
              setup.ambientFixedSamplePrefix 0 n ω =
                setup.ambientFixedSamplePrefix 0 n ω' := by
            funext r
            exact congrFun hprefix ⟨r.1, lt_of_lt_of_le r.2 hn⟩
          exact
            setup.ambientFixedInnerProcess_prefix_const 0 z x0 xMem0 yMem0
              hz hx0 n hn hprefix_n
        refine Finset.sum_congr rfl ?_
        intro t ht
        rcases Finset.mem_Icc.mp ht with ⟨ht1, hts⟩
        have ht_sub_lt_s : t - 1 < setup.s := by
          exact lt_of_lt_of_le
            (Nat.sub_lt (lt_of_lt_of_le Nat.zero_lt_one ht1) Nat.zero_lt_one) hts
        have hsample :
            setup.ξ (t - 1) ω = setup.ξ (t - 1) ω' := by
          simpa [RandomizedAcceleratedProximalPointSetup.ambientFixedSamplePrefix]
            using congrFun hprefix ⟨t - 1, ht_sub_lt_s⟩
        simp [delta, ht1, hts, hstate t hts,
          hstate (t - 1) (le_trans (Nat.sub_le t 1) hts), hsample]
      have hMemoryDiff_int :
          Integrable (fun ω : Ω => memoryEndpoint ω - memoryNormBound ω) setup.P := by
        refine setup.ambientFixed_prefix_integrable_real 0 setup.s ?_
        intro ω ω' hprefix
        have hstate :
            ∀ n (hn : n ≤ setup.s),
              setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω =
                setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω' := by
          intro n hn
          have hprefix_n :
              setup.ambientFixedSamplePrefix 0 n ω =
                setup.ambientFixedSamplePrefix 0 n ω' := by
            funext r
            exact congrFun hprefix ⟨r.1, lt_of_lt_of_le r.2 hn⟩
          exact
            setup.ambientFixedInnerProcess_prefix_const 0 z x0 xMem0 yMem0
              hz hx0 n hn hprefix_n
        simp [memoryEndpoint, memoryNormBound, hstate]
      exact
        MeasureTheory.integral_mono hMemoryDiff_int hDeltaSum_int
          hResidual_pointwise
  rcases hEq631WeightedQDeltaResidualBridge with
    ⟨Q, delta, hQ_nonneg, hWeightedQ_integral_nonneg, hEq631_with_residual,
      hResidual_absorption⟩
  have hEq636NoStepEndpointNonneg :
      0 ≤ ∫ ω : Ω, endpointCore ω + weightedEtaStep ω + memoryNormBound ω ∂setup.P := by
    -- Eq. (6.6.36) consequence: combine nonnegative weighted `Q_t`,
    -- Eq. (6.6.31), and the residual lower bound.  The remaining work is
    -- integral linearity/order algebra, not the tombstoned `qLeft` shortcut.
    have _hQ := hQ_nonneg
    have _hWeighted := hWeightedQ_integral_nonneg
    have _hEq631 := hEq631_with_residual
    have _hResidual := hResidual_absorption
    let A : ℝ :=
      ∫ ω : Ω,
        Finset.sum (Finset.Icc 1 setup.s)
          (fun t => setup.γSeq t * Q t ω) ∂setup.P
    let B : ℝ :=
      ∫ ω : Ω, endpointCore ω + weightedEtaStep ω + memoryEndpoint ω ∂setup.P
    let C : ℝ :=
      ∫ ω : Ω,
        Finset.sum (Finset.Icc 1 setup.s)
          (fun t => setup.γSeq t * delta t ω) ∂setup.P
    let D : ℝ := ∫ ω : Ω, memoryEndpoint ω - memoryNormBound ω ∂setup.P
    let Eint : ℝ :=
      ∫ ω : Ω, endpointCore ω + weightedEtaStep ω + memoryNormBound ω ∂setup.P
    have hEndpointMemory_int :
        Integrable
          (fun ω : Ω => endpointCore ω + weightedEtaStep ω + memoryEndpoint ω)
          setup.P := by
      refine setup.ambientFixed_prefix_integrable_real 0 setup.s ?_
      intro ω ω' hprefix
      have hstate :
          ∀ n (hn : n ≤ setup.s),
            setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω =
              setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω' := by
        intro n hn
        have hprefix_n :
            setup.ambientFixedSamplePrefix 0 n ω =
              setup.ambientFixedSamplePrefix 0 n ω' := by
          funext r
          exact congrFun hprefix ⟨r.1, lt_of_lt_of_le r.2 hn⟩
        exact
          setup.ambientFixedInnerProcess_prefix_const 0 z x0 xMem0 yMem0
            hz hx0 n hn hprefix_n
      have hEtaStepSum :
          Finset.sum (Finset.Icc 1 setup.s)
              (fun t =>
                setup.γSeq t * setup.ηSeq t *
                  ((setup.μ / 2) *
                    ‖(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        t ω).x -
                      (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        (t - 1) ω).x‖ ^ 2)) =
            Finset.sum (Finset.Icc 1 setup.s)
              (fun t =>
                setup.γSeq t * setup.ηSeq t *
                  ((setup.μ / 2) *
                    ‖(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        t ω').x -
                      (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        (t - 1) ω').x‖ ^ 2)) := by
        refine Finset.sum_congr rfl ?_
        intro t ht
        rcases Finset.mem_Icc.mp ht with ⟨_ht1, hts⟩
        rw [hstate t hts, hstate (t - 1) (le_trans (Nat.sub_le t 1) hts)]
      simp [endpointCore, weightedEtaStep, memoryEndpoint, hstate,
        hEtaStepSum,
        RandomizedAcceleratedProximalPointSetup.ambientFixedInnerProcess_zero]
    have hMemoryDiff_int :
        Integrable (fun ω : Ω => memoryEndpoint ω - memoryNormBound ω) setup.P := by
      refine setup.ambientFixed_prefix_integrable_real 0 setup.s ?_
      intro ω ω' hprefix
      have hstate :
          ∀ n (hn : n ≤ setup.s),
            setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω =
              setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω' := by
        intro n hn
        have hprefix_n :
            setup.ambientFixedSamplePrefix 0 n ω =
              setup.ambientFixedSamplePrefix 0 n ω' := by
          funext r
          exact congrFun hprefix ⟨r.1, lt_of_lt_of_le r.2 hn⟩
        exact
          setup.ambientFixedInnerProcess_prefix_const 0 z x0 xMem0 yMem0
            hz hx0 n hn hprefix_n
      simp [memoryEndpoint, memoryNormBound, hstate]
    have hE_eq : Eint = B - D := by
      dsimp [Eint, B, D]
      rw [← MeasureTheory.integral_sub hEndpointMemory_int hMemoryDiff_int]
      congr 1
      ext ω
      ring
    have hBD_nonneg : 0 ≤ B - D := by
      have hA_nonneg : 0 ≤ A := by
        simpa [A] using hWeightedQ_integral_nonneg
      have hA_le : A ≤ B - C := by
        simpa [A, B, C] using hEq631_with_residual
      have hC_ge : C ≥ D := by
        simpa [C, D] using hResidual_absorption
      linarith
    simpa [Eint, hE_eq] using hBD_nonneg
  have _hEq631_source_line_progress :
      (0 ≤
        ∫ ω : Ω,
          Finset.sum (Finset.Icc 1 setup.s)
            (fun t => setup.γSeq t * Q t ω) ∂setup.P) ∧
        ((∫ ω : Ω,
            Finset.sum (Finset.Icc 1 setup.s)
              (fun t => setup.γSeq t * Q t ω) ∂setup.P) ≤
          ∫ ω : Ω, endpointCore ω + weightedEtaStep ω + memoryEndpoint ω ∂setup.P -
            ∫ ω : Ω,
              Finset.sum (Finset.Icc 1 setup.s)
                (fun t => setup.γSeq t * delta t ω) ∂setup.P) ∧
        ((∫ ω : Ω,
            Finset.sum (Finset.Icc 1 setup.s)
              (fun t => setup.γSeq t * delta t ω) ∂setup.P) ≥
          ∫ ω : Ω, memoryEndpoint ω - memoryNormBound ω ∂setup.P) ∧
        0 ≤ ∫ ω : Ω, endpointCore ω + weightedEtaStep ω + memoryNormBound ω ∂setup.P :=
    ⟨hWeightedQ_integral_nonneg, hEq631_with_residual, hResidual_absorption,
      hEq636NoStepEndpointNonneg⟩
  have hEq636StepIntegral_nonneg :
      0 ≤
        ∫ ω : Ω,
          Finset.sum (Finset.Icc 1 setup.s)
            (fun t =>
              setup.γSeq t * setup.ηSeq t *
                ((setup.μ / 2) *
                  ‖(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      t ω).x -
                    (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (t - 1) ω).x‖ ^ 2)) ∂setup.P := by
    -- Eq. (6.6.36) to the Lemma 6.13 statement drops only this nonnegative
    -- accumulated proximal movement term after rewriting the observables.
    refine integral_nonneg_of_ae ?_
    exact Filter.Eventually.of_forall
      (fun ω =>
        Finset.sum_nonneg
          (fun t ht => by
            rcases Finset.mem_Icc.mp ht with ⟨ht1, hts⟩
            exact
              mul_nonneg
                (mul_nonneg (hγSeq_nonneg t ht1 hts)
                  (setup.hηSeq_nonneg t ht1 hts))
                (mul_nonneg (by linarith [setup.hμ_pos]) (sq_nonneg _))))
  have _hEq636_final_conversion_inputs :
      (0 ≤ ∫ ω : Ω, endpointCore ω + weightedEtaStep ω + memoryNormBound ω ∂setup.P) ∧
        0 ≤
          ∫ ω : Ω,
            Finset.sum (Finset.Icc 1 setup.s)
              (fun t =>
                setup.γSeq t * setup.ηSeq t *
                  ((setup.μ / 2) *
                    ‖(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        t ω).x -
                      (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        (t - 1) ω).x‖ ^ 2)) ∂setup.P :=
    ⟨hEq636NoStepEndpointNonneg, hEq636StepIntegral_nonneg⟩
  let Ds : ℝ :=
    setup.expectation
      (setup.ambientFixedDistanceToOptObservable
        z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s le_rfl xStar)
  let Ms : ι → ℝ := fun i =>
    setup.expectation
      (setup.ambientFixedMemoryDistanceToOptObservable
        z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s le_rfl i xStar)
  let Step : ℝ :=
    ∫ ω : Ω,
      Finset.sum (Finset.Icc 1 setup.s)
        (fun t =>
          setup.γSeq t * setup.ηSeq t *
            ((setup.μ / 2) *
              ‖(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                  t ω).x -
                (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                  (t - 1) ω).x‖ ^ 2)) ∂setup.P
  have hdist_int_s : Integrable
      (fun ω : Ω =>
        setup.γSeq setup.s * (1 + setup.ηSeq setup.s) *
          (setup.μ / 2 *
            ‖setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s ω -
              xStar‖ ^ 2))
      setup.P := by
    simpa [norm_sub_rev, mul_assoc, mul_left_comm, mul_comm] using
      ((setup.ambientFixedDistanceToOpt_integrable
        z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s le_rfl xStar).const_mul
          (setup.γSeq setup.s * (1 + setup.ηSeq setup.s) * (setup.μ / 2)))
  have hmem_int_s : Integrable
      (fun ω : Ω =>
        Finset.sum Finset.univ
          (fun i =>
            setup.μ * setup.γSeq setup.s * (1 + setup.τSeq setup.s) / 4 *
              ‖setup.ambientFixedXMem z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s i ω -
                xStar‖ ^ 2))
      setup.P := by
    refine MeasureTheory.integrable_finset_sum Finset.univ ?_
    intro i _hi
    simpa [norm_sub_rev, mul_assoc, mul_left_comm, mul_comm] using
      ((setup.ambientFixedMemoryDistanceToOpt_integrable
        z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s le_rfl i xStar).const_mul
          (setup.μ * setup.γSeq setup.s * (1 + setup.τSeq setup.s) / 4))
  have hwp_expand :
      setup.expectation
          (setup.ambientFixedWeightedPotentialObservable
            z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s le_rfl xStar) =
        setup.γSeq setup.s * (1 + setup.ηSeq setup.s) * ((setup.μ / 2) * Ds) +
          Finset.sum Finset.univ
            (fun i =>
              setup.μ * setup.γSeq setup.s * (1 + setup.τSeq setup.s) / 4 * Ms i) := by
    dsimp [Ds, Ms]
    rw [RandomizedAcceleratedProximalPointSetup.expectation,
      RandomizedAcceleratedProximalPointSetup.ambientFixedWeightedPotentialObservable]
    dsimp [RandomizedAcceleratedProximalPointSetup.ambientFixedWeightedPotential,
      RandomizedAcceleratedProximalPointSetup.ambientFixedDistanceToOptObservable,
      RandomizedAcceleratedProximalPointSetup.ambientFixedMemoryDistanceToOptObservable]
    rw [MeasureTheory.integral_add hdist_int_s hmem_int_s]
    rw [MeasureTheory.integral_finset_sum]
    · simp [RandomizedAcceleratedProximalPointSetup.expectation, norm_sub_rev,
        MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul,
        mul_assoc, mul_left_comm, mul_comm]
    · intro i _hi
      simpa [norm_sub_rev, mul_assoc, mul_left_comm, mul_comm] using
        ((setup.ambientFixedMemoryDistanceToOpt_integrable
          z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s le_rfl i xStar).const_mul
            (setup.μ * setup.γSeq setup.s * (1 + setup.τSeq setup.s) / 4))
  have hStep_int : Integrable
      (fun ω : Ω =>
        Finset.sum (Finset.Icc 1 setup.s)
          (fun t =>
            setup.γSeq t * setup.ηSeq t *
              ((setup.μ / 2) *
                ‖(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                    t ω).x -
                  (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                    (t - 1) ω).x‖ ^ 2))) setup.P := by
    refine setup.ambientFixed_prefix_integrable_real 0 setup.s ?_
    intro ω ω' hprefix
    have hstate :
        ∀ n (hn : n ≤ setup.s),
          setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω =
            setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω' := by
      intro n hn
      have hprefix_n :
          setup.ambientFixedSamplePrefix 0 n ω =
            setup.ambientFixedSamplePrefix 0 n ω' := by
        funext r
        exact congrFun hprefix ⟨r.1, lt_of_lt_of_le r.2 hn⟩
      exact
        setup.ambientFixedInnerProcess_prefix_const 0 z x0 xMem0 yMem0
          hz hx0 n hn hprefix_n
    refine Finset.sum_congr rfl ?_
    intro t ht
    rcases Finset.mem_Icc.mp ht with ⟨_ht1, hts⟩
    rw [hstate t hts, hstate (t - 1) (le_trans (Nat.sub_le t 1) hts)]
  have hEndpointNorm_int :
      Integrable (fun ω : Ω => endpointCore ω + memoryNormBound ω) setup.P := by
    refine setup.ambientFixed_prefix_integrable_real 0 setup.s ?_
    intro ω ω' hprefix
    have hstate :
        ∀ n (hn : n ≤ setup.s),
          setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω =
            setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω' := by
      intro n hn
      have hprefix_n :
          setup.ambientFixedSamplePrefix 0 n ω =
            setup.ambientFixedSamplePrefix 0 n ω' := by
        funext r
        exact congrFun hprefix ⟨r.1, lt_of_lt_of_le r.2 hn⟩
      exact
        setup.ambientFixedInnerProcess_prefix_const 0 z x0 xMem0 yMem0
          hz hx0 n hn hprefix_n
    have hEtaStepSum :
        Finset.sum (Finset.Icc 1 setup.s)
            (fun t =>
              setup.γSeq t * setup.ηSeq t *
                ((setup.μ / 2) *
                  ‖(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      t ω).x -
                    (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (t - 1) ω).x‖ ^ 2)) =
          Finset.sum (Finset.Icc 1 setup.s)
            (fun t =>
              setup.γSeq t * setup.ηSeq t *
                ((setup.μ / 2) *
                  ‖(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      t ω').x -
                    (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      (t - 1) ω').x‖ ^ 2)) := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      rcases Finset.mem_Icc.mp ht with ⟨_ht1, hts⟩
      rw [hstate t hts, hstate (t - 1) (le_trans (Nat.sub_le t 1) hts)]
    simp [endpointCore, memoryNormBound, hstate, hEtaStepSum,
      RandomizedAcceleratedProximalPointSetup.ambientFixedInnerProcess_zero]
  have hEndpointPlusStep_nonneg :
      0 ≤
        (∫ ω : Ω, endpointCore ω + memoryNormBound ω ∂setup.P) + Step := by
    have hNoStepIntegral_eq :
        (∫ ω : Ω, endpointCore ω + weightedEtaStep ω + memoryNormBound ω ∂setup.P) =
          (∫ ω : Ω, endpointCore ω + memoryNormBound ω ∂setup.P) + Step := by
      dsimp [Step]
      rw [← MeasureTheory.integral_add hEndpointNorm_int hStep_int]
      congr 1
      ext ω
      dsimp [weightedEtaStep]
      ring
    simpa [hNoStepIntegral_eq] using hEq636NoStepEndpointNonneg
  have hFinalScalar :
      lemma_6_13_sourceConclusion setup z x0 xStar xMem0 yMem0 hz hx0 hxMem0 := by
    let D0 : ℝ :=
      setup.expectation
        (setup.ambientFixedDistanceToOptObservable
          z x0 xMem0 yMem0 hz hx0 hxMem0 0 (Nat.zero_le setup.s) xStar)
    let M0 : ι → ℝ := fun i =>
      setup.expectation
        (setup.ambientFixedMemoryDistanceToOptObservable
          z x0 xMem0 yMem0 hz hx0 hxMem0 0 (Nat.zero_le setup.s) i xStar)
    let RHS0 : ℝ :=
      setup.γSeq 1 * setup.ηSeq 1 * ((setup.μ / 2) * D0) +
        Finset.sum Finset.univ
          (fun i =>
            setup.γSeq 1 * ((1 + setup.τSeq 1) - (Fintype.card ι : ℝ)⁻¹) *
              setup.Lhat / 2 * M0 i)
    have hD0_eq : D0 = ‖xStar - x0‖ ^ 2 := by
      letI : IsProbabilityMeasure setup.P := setup.hP
      dsimp [D0, RandomizedAcceleratedProximalPointSetup.expectation,
        RandomizedAcceleratedProximalPointSetup.ambientFixedDistanceToOptObservable,
        RandomizedAcceleratedProximalPointSetup.ambientFixedX]
      simp [setup.ambientFixedInnerProcess_zero 0 z x0 xMem0 yMem0 hz hx0]
    have hM0_eq : ∀ i, M0 i = ‖xMem0 i - xStar‖ ^ 2 := by
      intro i
      letI : IsProbabilityMeasure setup.P := setup.hP
      dsimp [M0, RandomizedAcceleratedProximalPointSetup.expectation,
        RandomizedAcceleratedProximalPointSetup.ambientFixedMemoryDistanceToOptObservable,
        RandomizedAcceleratedProximalPointSetup.ambientFixedXMem]
      simp [setup.ambientFixedInnerProcess_zero 0 z x0 xMem0 yMem0 hz hx0]
    -- Remaining purely algebraic conversion: rewrite
    -- `∫ (endpointCore + memoryNormBound) + Step` by integral linearity and
    -- `hwp_expand`; the pointwise step term in `endpointCore` cancels `Step`.
    have _hwp_expand := hwp_expand
    have _hEndpointNorm_int := hEndpointNorm_int
    have _hStep_int := hStep_int
    have _hEndpointPlusStep_nonneg := hEndpointPlusStep_nonneg
    have _hD0_eq := hD0_eq
    have _hM0_eq := hM0_eq
    have hEndpointPlusStep_gap :
        (∫ ω : Ω, endpointCore ω + memoryNormBound ω ∂setup.P) + Step =
          RHS0 -
            setup.expectation
              (setup.ambientFixedWeightedPotentialObservable
                z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s le_rfl xStar) := by
      -- Eq. (6.6.36)-to-Lemma 6.13 scalar bookkeeping: the step integral
      -- cancels the negative movement term inside `endpointCore`, while
      -- `hwp_expand` identifies the terminal distance and memory terms.
      have hEndpointPlusStep_eval :
          (∫ ω : Ω, endpointCore ω + memoryNormBound ω ∂setup.P) + Step =
            (setup.γSeq 1 * setup.ηSeq 1 *
                (setup.μ / 2 * ‖xStar - x0‖ ^ 2) +
              Finset.sum Finset.univ
                (fun i =>
                  setup.γSeq 1 *
                      ((1 + setup.τSeq 1) - (Fintype.card ι : ℝ)⁻¹) *
                      setup.Lhat / 2 *
                    ‖xMem0 i - xStar‖ ^ 2)) -
              (setup.γSeq setup.s * (1 + setup.ηSeq setup.s) *
                  (setup.μ / 2 * Ds) +
                Finset.sum Finset.univ
                  (fun i =>
                    setup.μ * setup.γSeq setup.s * (1 + setup.τSeq setup.s) / 4 *
                      Ms i)) := by
        have hMemoryNormBound_integral :
            (∫ ω : Ω, memoryNormBound ω ∂setup.P) =
              Finset.sum Finset.univ
                (fun i =>
                  setup.γSeq 1 *
                      ((1 + setup.τSeq 1) - (Fintype.card ι : ℝ)⁻¹) *
                      setup.Lhat / 2 *
                    ‖xMem0 i - xStar‖ ^ 2) -
                Finset.sum Finset.univ
                  (fun i =>
                    setup.μ * setup.γSeq setup.s * (1 + setup.τSeq setup.s) / 4 *
                      Ms i) := by
          letI : IsProbabilityMeasure setup.P := setup.hP
          have hterm_int : ∀ i : ι,
              Integrable
                (fun ω : Ω =>
                  setup.μ * setup.γSeq setup.s * (1 + setup.τSeq setup.s) / 4 *
                    ‖(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 setup.s
                        ω).xMem i - xStar‖ ^ 2)
                setup.P := by
            intro i
            simpa [RandomizedAcceleratedProximalPointSetup.ambientFixedXMem,
              mul_assoc, mul_left_comm, mul_comm] using
              ((setup.ambientFixedMemoryDistanceToOpt_integrable
                z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s le_rfl i xStar).const_mul
                  (setup.μ * setup.γSeq setup.s * (1 + setup.τSeq setup.s) / 4))
          have hterm_integral : ∀ i : ι,
              (∫ ω : Ω,
                setup.μ * setup.γSeq setup.s * (1 + setup.τSeq setup.s) / 4 *
                  ‖(setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 setup.s
                      ω).xMem i - xStar‖ ^ 2 ∂setup.P) =
                setup.μ * setup.γSeq setup.s * (1 + setup.τSeq setup.s) / 4 *
                  Ms i := by
            intro i
            dsimp [Ms, RandomizedAcceleratedProximalPointSetup.expectation,
              RandomizedAcceleratedProximalPointSetup.ambientFixedMemoryDistanceToOptObservable,
              RandomizedAcceleratedProximalPointSetup.ambientFixedXMem]
            rw [MeasureTheory.integral_const_mul]
          dsimp [memoryNormBound]
          rw [MeasureTheory.integral_finset_sum]
          · trans
              Finset.sum Finset.univ
                (fun i =>
                  setup.γSeq 1 *
                      ((1 + setup.τSeq 1) - (Fintype.card ι : ℝ)⁻¹) *
                      setup.Lhat / 2 *
                    ‖xMem0 i - xStar‖ ^ 2 -
                    setup.μ * setup.γSeq setup.s * (1 + setup.τSeq setup.s) / 4 *
                      Ms i)
            · refine Finset.sum_congr rfl ?_
              intro i _hi
              rw [MeasureTheory.integral_sub]
              · rw [hterm_integral i]
                simp [MeasureTheory.integral_const, mul_assoc, mul_left_comm, mul_comm]
              · exact MeasureTheory.integrable_const _
              · exact hterm_int i
            · rw [Finset.sum_sub_distrib]
          · intro i _hi
            exact (MeasureTheory.integrable_const _).sub (hterm_int i)
        have hterminal_dist_int' :
            Integrable
              (fun ω : Ω =>
                setup.γSeq setup.s * (1 + setup.ηSeq setup.s) *
                  (setup.μ / 2 *
                    ‖xStar -
                      (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        setup.s ω).x‖ ^ 2))
              setup.P := by
          simpa [RandomizedAcceleratedProximalPointSetup.ambientFixedX,
            norm_sub_rev, mul_assoc, mul_left_comm, mul_comm] using hdist_int_s
        have hterminal_dist_integral :
            (∫ ω : Ω,
              setup.γSeq setup.s * (1 + setup.ηSeq setup.s) *
                (setup.μ / 2 *
                  ‖xStar -
                    (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                      setup.s ω).x‖ ^ 2) ∂setup.P) =
              setup.γSeq setup.s * (1 + setup.ηSeq setup.s) *
                (setup.μ / 2 * Ds) := by
          dsimp [Ds, RandomizedAcceleratedProximalPointSetup.expectation,
            RandomizedAcceleratedProximalPointSetup.ambientFixedDistanceToOptObservable,
            RandomizedAcceleratedProximalPointSetup.ambientFixedX]
          rw [MeasureTheory.integral_const_mul]
          rw [MeasureTheory.integral_const_mul]
        have hinitial_dist_int :
            Integrable
              (fun ω : Ω =>
                setup.γSeq 1 * setup.ηSeq 1 *
                  (setup.μ / 2 *
                    ‖xStar -
                      (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
                        0 ω).x‖ ^ 2))
              setup.P := by
          refine setup.ambientFixed_prefix_integrable_real 0 0 ?_
          intro ω ω' _hprefix
          simp [setup.ambientFixedInnerProcess_zero 0 z x0 xMem0 yMem0 hz hx0]
        have hEndpointCore_int : Integrable endpointCore setup.P := by
          dsimp [endpointCore]
          exact (hinitial_dist_int.sub hterminal_dist_int').sub hStep_int
        have hEndpointCore_integral :
            (∫ ω : Ω, endpointCore ω ∂setup.P) + Step =
              setup.γSeq 1 * setup.ηSeq 1 *
                  (setup.μ / 2 * ‖xStar - x0‖ ^ 2) -
                setup.γSeq setup.s * (1 + setup.ηSeq setup.s) *
                  (setup.μ / 2 * Ds) := by
          letI : IsProbabilityMeasure setup.P := setup.hP
          dsimp [endpointCore, Step]
          rw [MeasureTheory.integral_sub]
          · rw [MeasureTheory.integral_sub]
            · rw [hterminal_dist_integral]
              simp [setup.ambientFixedInnerProcess_zero 0 z x0 xMem0 yMem0 hz hx0,
                MeasureTheory.integral_const, mul_assoc, mul_left_comm, mul_comm]
            · exact hinitial_dist_int
            · exact hterminal_dist_int'
          · exact hinitial_dist_int.sub hterminal_dist_int'
          · exact hStep_int
        have hMemoryNorm_int : Integrable memoryNormBound setup.P := by
          have h := hEndpointNorm_int.sub hEndpointCore_int
          convert h using 1
          funext ω
          dsimp
          ring
        rw [MeasureTheory.integral_add hEndpointCore_int hMemoryNorm_int]
        rw [hMemoryNormBound_integral]
        linarith [hEndpointCore_integral]
      rw [hEndpointPlusStep_eval, hwp_expand]
      dsimp [RHS0]
      rw [hD0_eq]
      simp [hM0_eq, mul_assoc, mul_left_comm, mul_comm]
    have hnonneg_gap :
        0 ≤
          RHS0 -
            setup.expectation
              (setup.ambientFixedWeightedPotentialObservable
                z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s le_rfl xStar) := by
      simpa [hEndpointPlusStep_gap] using hEndpointPlusStep_nonneg
    unfold lemma_6_13_sourceConclusion
    change
      setup.expectation
          (setup.ambientFixedWeightedPotentialObservable
            z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s le_rfl xStar) ≤ RHS0
    linarith
  exact hFinalScalar

/-- Route-local Lemma 6.13 weighted-potential bridge for Theorem 6.17.

Aligns with Lan Lemma 6.13 and Eq. (6.6.36) rearranged to the stated weighted
potential inequality. Considered the Part003 candidate
`lemma_6_13_hatSourceDomain_corrected`, which is the exact source route but is
not visible in the current Part004 import cone; considered Part002
`lemma_6_13_sourceConclusion`, which is only the conclusion `Prop` alias and not
a proof; considered SOptLib/Part002 telescope and scalar candidates from symbol
search, which provide lower arithmetic pieces but not the full source-domain
Eq. (6.6.31)-to-(6.6.36) bridge. The remaining proof obligation is therefore
strictly the source Lemma 6.13 telescope, not the final Theorem 6.17 contraction. -/
theorem lemma_6_13_hatSourceDomain_corrected_local
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (z x0 xStar : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) (hxMem0 : ∀ i, xMem0 i ∈ setup.X)
    (hsource : setup.ambientFixedSourceDomain 0 z x0 xMem0 yMem0 hz hx0)
    (hhat :
      setup.ambientFixedHatSourceDomain 0 z x0 xMem0 yMem0 hz hx0)
    (hgradMem0 :
      setup.ambientFixedInitialGradientMemory z xMem0 yMem0 hxMem0)
    (hxStar : xStar ∈ setup.X)
    (h_opt : ∀ u : {x : E // x ∈ setup.X},
      (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ (fun i => setup.psiAtOn z i ⟨xStar, hxStar⟩) +
        setup.phiAt z xStar ≤
      (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ (fun i => setup.psiAtOn z i u) +
        setup.phiAt z u.1)
    (hs : 1 ≤ setup.s)
    /- Eq. 6.6.20: αₜ₊₁ γₜ₊₁ = γₜ, for paper indices t = 1, …, s−1. -/
    (hparam20 : ∀ t, 1 ≤ t → t + 1 ≤ setup.s →
      setup.αSeq (t + 1) * setup.γSeq (t + 1) = setup.γSeq t)
    /- Eq. 6.6.21: γₜ₊₁[m(1+τₜ₊₁)−1] ≤ mγₜ(1+τₜ), for t = 1, …, s−1. -/
    (hparam21 : ∀ t, 1 ≤ t → t + 1 ≤ setup.s →
      setup.γSeq (t + 1) *
          ((Fintype.card ι : ℝ) * (1 + setup.τSeq (t + 1)) - 1) ≤
        (Fintype.card ι : ℝ) * setup.γSeq t * (1 + setup.τSeq t))
    /- Eq. 6.6.22: γₜ₊₁ ηₜ₊₁ ≤ γₜ(1 + ηₜ), for t = 1, …, s−1. -/
    (hparam22 : ∀ t, 1 ≤ t → t + 1 ≤ setup.s →
      setup.γSeq (t + 1) * setup.ηSeq (t + 1) ≤
        setup.γSeq t * (1 + setup.ηSeq t))
    /- Eq. 6.6.23: ηₛ μ / 4 ≥ (m−1)² L̂ / (m² τₛ) -/
    (hparam23 :
      setup.ηSeq setup.s * setup.μ / 4 ≥
        ((Fintype.card ι : ℝ) - 1) ^ 2 * setup.Lhat /
          ((Fintype.card ι : ℝ) ^ 2 * setup.τSeq setup.s))
    /- Eq. 6.6.24: ηₜ μ / 2 ≥ αₜ₊₁ L̂ / τₜ₊₁ + (m−1)² L̂ / (m² τₜ), for t = 1, …, s−1. -/
    (hparam24 : ∀ t, 1 ≤ t → t + 1 ≤ setup.s →
      setup.ηSeq t * setup.μ / 2 ≥
        setup.αSeq (t + 1) * setup.Lhat / setup.τSeq (t + 1) +
          ((Fintype.card ι : ℝ) - 1) ^ 2 * setup.Lhat /
            ((Fintype.card ι : ℝ) ^ 2 * setup.τSeq t))
    /- Eq. 6.6.25: ηₛ μ / 4 ≥ L̂ / (m(1 + τₛ)) -/
    (hparam25 :
      setup.ηSeq setup.s * setup.μ / 4 ≥
      setup.Lhat /
          ((Fintype.card ι : ℝ) * (1 + setup.τSeq setup.s)))
    /- Eq. 6.6.31 proof: multiply each Qₜ by nonnegative γₜ on t = 1, …, s. -/
    (hγSeq_nonneg : ∀ t, 1 ≤ t → t ≤ setup.s → 0 ≤ setup.γSeq t)
    /- Eq. 6.6.35 Young absorption uses τₜ as a strict denominator. -/
    (hτSeq_pos : ∀ t, 1 ≤ t → t ≤ setup.s → 0 < setup.τSeq t) :
    setup.expectation
        (setup.ambientFixedWeightedPotentialObservable
          z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s le_rfl xStar) ≤
      setup.γSeq 1 * setup.ηSeq 1 *
          ((setup.μ / 2) *
            setup.expectation
              (setup.ambientFixedDistanceToOptObservable
                z x0 xMem0 yMem0 hz hx0 hxMem0 0 (Nat.zero_le setup.s) xStar)) +
        Finset.sum Finset.univ
          (fun i =>
            setup.γSeq 1 *
                ((1 + setup.τSeq 1) - (Fintype.card ι : ℝ)⁻¹) *
                setup.Lhat / 2 *
              setup.expectation
                (setup.ambientFixedMemoryDistanceToOptObservable
              z x0 xMem0 yMem0 hz hx0 hxMem0 0 (Nat.zero_le setup.s) i xStar)) := by
  classical
  have hsource_step :
      ∀ n (hn : n + 1 ≤ setup.s) (ω : Ω),
          setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 (n + 1) ω =
            setup.sourceInnerStepAt 0 z (n + 1) hz (Nat.succ_pos n) hn
              ω (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω)
              (((setup.ambientFixedInnerProcess_mem 0 z x0 xMem0 yMem0 hz hx0 n
                (Nat.le_of_succ_le hn)) ω).1)
              (hsource n hn ω) := by
    intro n hn ω
    exact setup.ambientFixedInnerProcess_succ_eq_sourceInnerStepAt_of_domain
      0 z x0 xMem0 yMem0 hz hx0 hsource n hn ω
  have hsource_yMem :
      ∀ n (hn : n + 1 ≤ setup.s) (ω : Ω) (i : ι),
        (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 (n + 1) ω).yMem i =
          if _ : i = setup.ξ (0 + ((n + 1) - 1)) ω then
            setup.gradPsiOnAt z i
              ⟨setup.xMemAfterSampleAtState (n + 1) (Nat.succ_pos n) hn
                  (setup.ξ (0 + ((n + 1) - 1)) ω) i
                  (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω),
                hsource n hn ω i⟩
          else
            (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 n ω).yMem i := by
    intro n hn ω i
    exact setup.ambientFixedInnerProcess_yMem_eq_source_of_domain
      0 z x0 xMem0 yMem0 hz hx0 hsource n hn ω i
  have hcurv :=
    RandomizedAcceleratedProximalPointSetup.SubproblemCurvature_6_6_8 setup z hz
  have hprox45 :=
    eq_6_6_45_ambientFixed_sourceDomain
      setup 0 z x0 xStar xMem0 yMem0 hz hx0 hxStar
  have h630_delta2 :
      ∀ n (hn : n + 1 ≤ setup.s),
        ((∫ ω : Ω,
            ambientFixedDelta2CurrentKernel
              (setup := setup) (offset := 0) (z := z) (x0 := x0)
              (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
              (hz := hz) (hx0 := hx0) (hxStar := hxStar)
              n hn (hhat n hn) ω (setup.ξ n ω) ∂setup.P) =
          ∫ ω : Ω,
            RandomizedAcceleratedProximalPointSetup.currentIndexAverage
              (fun j : ι =>
                ambientFixedDelta2CurrentKernel
                  (setup := setup) (offset := 0) (z := z) (x0 := x0)
                  (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
                  (hz := hz) (hx0 := hx0) (hxStar := hxStar)
                  n hn (hhat n hn) ω j) ∂setup.P) ∧
        (∀ m (hm : m + 1 ≤ setup.s) (ω : Ω) (i : ι),
          (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 (m + 1) ω).yMem i =
            if _ : i = setup.ξ (0 + ((m + 1) - 1)) ω then
              setup.gradPsiOnAt z i
                ⟨setup.xMemAfterSampleAtState (m + 1) (Nat.succ_pos m) hm
                    (setup.ξ (0 + ((m + 1) - 1)) ω) i
                    (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 m ω),
                  hsource m hm ω i⟩
            else
              (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 m ω).yMem i) := by
    exact eq_6_6_30_ambientFixed_delta2CurrentKernel_source_boundary_route
      (setup := setup) (z := z) (x0 := x0) (xStar := xStar)
      (xMem0 := xMem0) (yMem0 := yMem0)
      (hz := hz) (hx0 := hx0) hsource hhat hxStar
  change lemma_6_13_sourceConclusion setup z x0 xStar xMem0 yMem0 hz hx0 hxMem0
  exact lemma_6_13_eq631_to_eq636_source_route_local
    setup z x0 xStar xMem0 yMem0 hz hx0 hxMem0 hsource hhat hgradMem0
    hxStar h_opt hs hparam20 hparam21 hparam22 hparam23 hparam24 hparam25
    hγSeq_nonneg hτSeq_pos hsource_step hsource_yMem hcurv hprox45 h630_delta2

theorem theorem_6_17_variance_side_conditions_of_q_local
    {μ m c q : ℝ}
    (hμ_pos : 0 < μ) (hm_pos : 0 < m) (hm_ge_one : 1 ≤ m) (hq_gt_one : 1 < q)
    (hc : 16 * c = m * (q - 1) * (q + 1)) :
    ((m * (q + 1) / 2 - 1) * μ / 4 ≥
        (m - 1) ^ 2 * (μ * c) / (m ^ 2 * ((q - 1) / 2))) ∧
      ((m * (q + 1) / 2 - 1) * μ / 2 ≥
        (1 - 2 / (m * (q + 1))) * (μ * c) / ((q - 1) / 2) +
          (m - 1) ^ 2 * (μ * c) / (m ^ 2 * ((q - 1) / 2))) := by
  have hμ_ne : μ ≠ 0 := ne_of_gt hμ_pos
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  have hqsub_pos : 0 < q - 1 := by linarith
  have hqsub_ne : q - 1 ≠ 0 := ne_of_gt hqsub_pos
  have hqadd_pos : 0 < q + 1 := by linarith
  have hqadd_ne : q + 1 ≠ 0 := ne_of_gt hqadd_pos
  have hm_qadd_ne : m * (q + 1) ≠ 0 := mul_ne_zero hm_ne hqadd_ne
  have hhalf_qsub_ne : (q - 1) / 2 ≠ 0 := by positivity
  have hcore_scalar : 0 ≤ (2 * m - 1) * q - 1 := by
    nlinarith [hm_ge_one, hq_gt_one]
  have hcore : 0 ≤ μ * ((2 * m - 1) * q - 1) := by
    exact mul_nonneg (le_of_lt hμ_pos) hcore_scalar
  have hc_solve : c = m * (q - 1) * (q + 1) / 16 := by
    linarith [hc]
  have hprod_core : 0 ≤ m * (q - 1) * ((2 * m - 1) * q - 1) := by
    exact mul_nonneg (mul_nonneg (le_of_lt hm_pos) (le_of_lt hqsub_pos)) hcore_scalar
  have hprod_core_qadd : 0 ≤ m * (q - 1) * (q + 1) * ((2 * m - 1) * q - 1) := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (le_of_lt hm_pos) (le_of_lt hqsub_pos)) (le_of_lt hqadd_pos))
      hcore_scalar
  have hprod_core_qadd_half :
      0 ≤ m * (q - 1) * (q + 1) * ((2 * m - 1) * q - 1) / 2 := by
    positivity
  have hcleared23 :
      (m - 1) ^ 2 * c * 2 ^ 2 * 4 ≤
        m ^ 2 * (q - 1) * (m * (q + 1) - 2) := by
    rw [hc_solve]
    nlinarith [hprod_core]
  have hcleared24 :
      2 ^ 3 * c * (m * (m * (q + 1) - 2) + (q + 1) * (m - 1) ^ 2) ≤
        m ^ 2 * (q + 1) * (m * (q + 1) - 2) * (q - 1) := by
    rw [hc_solve]
    nlinarith [hprod_core_qadd_half]
  constructor
  · field_simp [hμ_ne, hm_ne, hqsub_ne, hqadd_ne, hhalf_qsub_ne]
    nlinarith [hcleared23]
  · field_simp [hμ_ne, hm_ne, hqsub_ne, hqadd_ne, hm_qadd_ne, hhalf_qsub_ne]
    nlinarith [hcleared24]

/-- Triangle-square estimate used in Lan Theorem 6.17 after Eq. (6.6.37);
it aligns the source's `‖a-b‖² ≤ 2‖a-c‖² + 2‖c-b‖²` step with the imported
SOptLib binary norm-square Young inequality; Part004 uses the SOptLib lemma directly through this source-shaped wrapper. -/
theorem sq_norm_sub_le_two_sq_norm_sub_add_local
    {E : Type*} [SeminormedAddCommGroup E] (a b c : E) :
    ‖a - b‖ ^ 2 ≤ 2 * ‖a - c‖ ^ 2 + 2 * ‖c - b‖ ^ 2 := by
  have hdecomp : a - b = (a - c) + (c - b) := by
    simp only [sub_eq_add_neg]
    rw [add_assoc, neg_add_cancel_left]
  rw [hdecomp]
  exact SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq (a - c) (c - b)

/-! Local Part004 copy: Eq. (6.6.17)'s schedule gives the nonnegative `γ_t` weights used when
passing from the `Q_t` inequalities to the weighted Eq. (6.6.31) sum. -/
omit [SecondCountableTopology E] in
theorem gamma_nonneg_from_eq_6_6_17_schedule_local
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (hα_pos : 0 < setup.α)
    (hγSeq_schedule : ∀ t, 1 ≤ t → t ≤ setup.s →
      setup.γSeq t = setup.α ^ (-(t : ℤ))) :
    ∀ t, 1 ≤ t → t ≤ setup.s → 0 ≤ setup.γSeq t := by
  intro t ht hts
  rw [hγSeq_schedule t ht hts]
  exact zpow_nonneg (le_of_lt hα_pos) (-(t : ℤ))

set_option maxHeartbeats 800000
/-- Fixed-memory Theorem 6.17 contraction once the generated initial-gradient
memory boundary is supplied.

Aligns with Lan Theorem 6.17 and the proof step after Eq. (6.6.37).  Considered
the Part003 candidate `theorem_6_17_hatSourceDomain_initialGradientMemory`, which
is the exact source-shaped theorem, plus the SOptLib/Part002 telescope and
stationarity candidates from the pre-search; none are directly callable in this
Part004 import cone as the full contraction bridge.  The remaining proof is the
Part003 source route through `lemma_6_13_hatSourceDomain_corrected`, with
`hgradMem0` retained explicitly rather than added as a setup assumption. -/
theorem theorem_6_17_hatSourceDomain_initialGradientMemory_local
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (z x0 xStar : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) (hxMem0 : ∀ i, xMem0 i ∈ setup.X)
    (hsource : setup.ambientFixedSourceDomain 0 z x0 xMem0 yMem0 hz hx0)
    (hhat :
      setup.ambientFixedHatSourceDomain 0 z x0 xMem0 yMem0 hz hx0)
    (hgradMem0 :
      setup.ambientFixedInitialGradientMemory z xMem0 yMem0 hxMem0)
    (hxStar : xStar ∈ setup.X)
    (hs : 1 ≤ setup.s)
    (hα_schedule :
      setup.α =
        1 - 2 / ((Fintype.card ι : ℝ) *
          (Real.sqrt (1 + 16 * (2 + setup.L / setup.μ) / (Fintype.card ι : ℝ)) + 1)))
    (hαSeq_schedule : ∀ t, 1 ≤ t → t ≤ setup.s → setup.αSeq t = setup.α)
    (hγSeq_schedule : ∀ t, 1 ≤ t → t ≤ setup.s → setup.γSeq t = setup.α ^ (-(t : ℤ)))
    (hτSeq_schedule : ∀ t, 1 ≤ t → t ≤ setup.s →
      setup.τSeq t = ((Fintype.card ι : ℝ) * (1 - setup.α))⁻¹ - 1)
    (hηSeq_schedule : ∀ t, 1 ≤ t → t ≤ setup.s →
      setup.ηSeq t = setup.α * (1 - setup.α)⁻¹)
    (h_opt : ∀ u : {x : E // x ∈ setup.X},
      (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ (fun i => setup.psiAtOn z i ⟨xStar, hxStar⟩) +
        setup.phiAt z xStar ≤
      (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ (fun i => setup.psiAtOn z i u) +
        setup.phiAt z u.1) :
    (setup.expectation
        (setup.ambientFixedDistanceToOptObservable
          z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s le_rfl xStar) ≤
      setup.α ^ setup.s *
          (1 + 2 * setup.Lhat / setup.μ) *
          setup.expectation
            (setup.ambientFixedInitialContractionObservable
              z x0 xMem0 yMem0 hz hx0 hxMem0 xStar)) ∧
    (setup.expectation
        (setup.ambientFixedMemoryDispersionObservable
          z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s le_rfl) ≤
      6 * setup.α ^ setup.s *
          (1 + 2 * setup.Lhat / setup.μ) *
          setup.expectation
            (setup.ambientFixedInitialContractionObservable
              z x0 xMem0 yMem0 hz hx0 hxMem0 xStar)) := by
  classical
  rcases alpha_schedule_bounds_for_theorem_6_16 setup hα_schedule with
    ⟨hα_pos, hα_lt_one, _hlogα_neg⟩
  let m : ℝ := (Fintype.card ι : ℝ)
  let c : ℝ := 2 + setup.L / setup.μ
  let q : ℝ := Real.sqrt (1 + 16 * c / m)
  have hα_ne : setup.α ≠ 0 := ne_of_gt hα_pos
  have hm_pos : 0 < m := by
    dsimp [m]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hm_ge_one : 1 ≤ m := by
    dsimp [m]
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos : 0 < Fintype.card ι))
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  have hμ_ne : setup.μ ≠ 0 := ne_of_gt setup.hμ_pos
  have hδ_pos : 0 < 1 - setup.α := by linarith
  have hδ_ne : 1 - setup.α ≠ 0 := ne_of_gt hδ_pos
  have hmδ_ne : (Fintype.card ι : ℝ) * (1 - setup.α) ≠ 0 := by
    exact mul_ne_zero (by simpa [m] using hm_ne) hδ_ne
  have hratio_ge_one : 1 ≤ setup.L / setup.μ := by
    rw [le_div_iff₀ setup.hμ_pos]
    simpa using setup.hμ_le_L
  have hc_pos : 0 < c := by
    dsimp [c]
    nlinarith
  have harg_nonneg : 0 ≤ 1 + 16 * c / m := by positivity
  have hq_sq : q ^ 2 = 1 + 16 * c / m := by
    dsimp [q]
    exact Real.sq_sqrt harg_nonneg
  have hq_sq_mul : m * q ^ 2 = m + 16 * c := by
    have h := congrArg (fun x : ℝ => m * x) hq_sq
    field_simp [hm_ne] at h
    linarith
  have hq_gt_one : 1 < q := by
    dsimp [q]
    rw [Real.lt_sqrt (by norm_num)]
    have hfrac_pos : 0 < 16 * c / m := by positivity
    nlinarith
  have hq_ne_one : q - 1 ≠ 0 := by linarith
  have hq1_ne : q + 1 ≠ 0 := by linarith
  have h1q_ne : 1 + q ≠ 0 := by linarith
  have hm_q1_ne : m * (q + 1) ≠ 0 := mul_ne_zero hm_ne hq1_ne
  have hc_inv : c * (1 + q)⁻¹ * 16 = m * (q - 1) := by
    field_simp [h1q_ne]
    nlinarith [hq_sq_mul]
  have hc_inv_mu : setup.μ * c * (1 + q)⁻¹ * 16 = setup.μ * (m * (q - 1)) := by
    calc
      setup.μ * c * (1 + q)⁻¹ * 16 = setup.μ * (c * (1 + q)⁻¹ * 16) := by
        ring
      _ = setup.μ * (m * (q - 1)) := by rw [hc_inv]
  have hα_eq : setup.α = 1 - 2 / (m * (q + 1)) := by
    simpa [m, c, q] using hα_schedule
  have hδ_eq : 1 - setup.α = 2 / (m * (q + 1)) := by
    rw [hα_eq]
    ring
  have hτ_closed : ((Fintype.card ι : ℝ) * (1 - setup.α))⁻¹ - 1 = (q - 1) / 2 := by
    dsimp [m] at hm_ne hm_pos hm_q1_ne hδ_eq
    rw [hδ_eq]
    field_simp [hm_ne, hq1_ne, hm_q1_ne]
    ring
  have hη_closed : setup.α * (1 - setup.α)⁻¹ = m * (q + 1) / 2 - 1 := by
    rw [hα_eq]
    have hsub : 1 - (1 - 2 / (m * (q + 1))) = 2 / (m * (q + 1)) := by ring
    rw [hsub]
    field_simp [hm_ne, hq1_ne, hm_q1_ne]
  have hLhat_eq : setup.Lhat = setup.μ * c := by
    rw [setup.Lhat_def]
    dsimp [c]
    field_simp [hμ_ne]
    ring
  have hparam20 : ∀ t, 1 ≤ t → t + 1 ≤ setup.s →
      setup.αSeq (t + 1) * setup.γSeq (t + 1) = setup.γSeq t := by
    intro t ht hts
    have ht1 : 1 ≤ t + 1 := Nat.succ_le_succ (Nat.zero_le t)
    have hαt := hαSeq_schedule (t + 1) ht1 hts
    have hγt1 := hγSeq_schedule (t + 1) ht1 hts
    have hγt := hγSeq_schedule t ht (Nat.le_trans (Nat.le_succ t) hts)
    rw [hαt, hγt1, hγt]
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
    field_simp [pow_ne_zero _ hα_ne]
    ring
  have hparam21 : ∀ t, 1 ≤ t → t + 1 ≤ setup.s →
      setup.γSeq (t + 1) *
          ((Fintype.card ι : ℝ) * (1 + setup.τSeq (t + 1)) - 1) ≤
        (Fintype.card ι : ℝ) * setup.γSeq t * (1 + setup.τSeq t) := by
    intro t ht hts
    have ht1 : 1 ≤ t + 1 := Nat.succ_le_succ (Nat.zero_le t)
    have hγt1 := hγSeq_schedule (t + 1) ht1 hts
    have hγt := hγSeq_schedule t ht (Nat.le_trans (Nat.le_succ t) hts)
    have hτt1 := hτSeq_schedule (t + 1) ht1 hts
    have hτt := hτSeq_schedule t ht (Nat.le_trans (Nat.le_succ t) hts)
    rw [hγt1, hγt, hτt1, hτt]
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
    field_simp [pow_ne_zero _ hα_ne, (by simpa [m] using hm_ne), hδ_ne, hmδ_ne]
    rw [pow_succ]
    ring_nf
    exact le_rfl
  have hparam22 : ∀ t, 1 ≤ t → t + 1 ≤ setup.s →
      setup.γSeq (t + 1) * setup.ηSeq (t + 1) ≤
        setup.γSeq t * (1 + setup.ηSeq t) := by
    intro t ht hts
    have ht1 : 1 ≤ t + 1 := Nat.succ_le_succ (Nat.zero_le t)
    have hγt1 := hγSeq_schedule (t + 1) ht1 hts
    have hγt := hγSeq_schedule t ht (Nat.le_trans (Nat.le_succ t) hts)
    have hηt1 := hηSeq_schedule (t + 1) ht1 hts
    have hηt := hηSeq_schedule t ht (Nat.le_trans (Nat.le_succ t) hts)
    rw [hγt1, hγt, hηt1, hηt]
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
    field_simp [pow_ne_zero _ hα_ne, hδ_ne]
    rw [pow_succ]
    ring_nf
    exact le_rfl
  have h16c : 16 * c = m * (q - 1) * (q + 1) := by
    nlinarith [hq_sq_mul]
  have hscalar :
      ((m * (q + 1) / 2 - 1) * setup.μ / 4 ≥
          (m - 1) ^ 2 * (setup.μ * c) / (m ^ 2 * ((q - 1) / 2))) ∧
        ((m * (q + 1) / 2 - 1) * setup.μ / 2 ≥
          (1 - 2 / (m * (q + 1))) * (setup.μ * c) / ((q - 1) / 2) +
            (m - 1) ^ 2 * (setup.μ * c) / (m ^ 2 * ((q - 1) / 2))) :=
    theorem_6_17_variance_side_conditions_of_q_local
      (μ := setup.μ) (m := m) (c := c) (q := q)
      setup.hμ_pos hm_pos hm_ge_one hq_gt_one h16c
  have hparam23 :
      setup.ηSeq setup.s * setup.μ / 4 ≥
        ((Fintype.card ι : ℝ) - 1) ^ 2 * setup.Lhat /
          ((Fintype.card ι : ℝ) ^ 2 * setup.τSeq setup.s) := by
    have hηs := hηSeq_schedule setup.s hs le_rfl
    have hτs := hτSeq_schedule setup.s hs le_rfl
    rw [hηs, hτs, hη_closed, hτ_closed, hLhat_eq]
    simpa [m] using hscalar.1
  have hparam24 : ∀ t, 1 ≤ t → t + 1 ≤ setup.s →
      setup.ηSeq t * setup.μ / 2 ≥
        setup.αSeq (t + 1) * setup.Lhat / setup.τSeq (t + 1) +
          ((Fintype.card ι : ℝ) - 1) ^ 2 * setup.Lhat /
            ((Fintype.card ι : ℝ) ^ 2 * setup.τSeq t) := by
    intro t ht hts
    have ht1 : 1 ≤ t + 1 := Nat.succ_le_succ (Nat.zero_le t)
    have hαt1 := hαSeq_schedule (t + 1) ht1 hts
    have hηt := hηSeq_schedule t ht (Nat.le_trans (Nat.le_succ t) hts)
    have hτt1 := hτSeq_schedule (t + 1) ht1 hts
    have hτt := hτSeq_schedule t ht (Nat.le_trans (Nat.le_succ t) hts)
    rw [hαt1, hηt, hτt1, hτt, hη_closed, hτ_closed, hLhat_eq, hα_eq]
    simpa [m] using hscalar.2
  have hparam25 :
      setup.ηSeq setup.s * setup.μ / 4 ≥
        setup.Lhat / ((Fintype.card ι : ℝ) * (1 + setup.τSeq setup.s)) := by
    have hηs := hηSeq_schedule setup.s hs le_rfl
    have hτs := hτSeq_schedule setup.s hs le_rfl
    rw [hηs, hτs, hη_closed, hτ_closed, hLhat_eq]
    dsimp only [m] at *
    field_simp [hμ_ne, (by simpa [m] using hm_ne), hq1_ne, h1q_ne]
    ring_nf
    rw [hc_inv_mu]
    ring_nf
    have hfactor_nonneg : 0 ≤ (m - 1) * (q + 1) := by
      exact mul_nonneg (by linarith) (by linarith)
    have hmain_nonneg : 0 ≤ setup.μ * m * ((m - 1) * (q + 1)) := by
      exact mul_nonneg (mul_nonneg (le_of_lt setup.hμ_pos) (le_of_lt hm_pos)) hfactor_nonneg
    dsimp only [m] at hmain_nonneg
    nlinarith [hmain_nonneg]
  have _hside_conditions_progress :
      (∀ t, 1 ≤ t → t + 1 ≤ setup.s →
        setup.αSeq (t + 1) * setup.γSeq (t + 1) = setup.γSeq t) ∧
      (∀ t, 1 ≤ t → t + 1 ≤ setup.s →
        setup.γSeq (t + 1) *
            ((Fintype.card ι : ℝ) * (1 + setup.τSeq (t + 1)) - 1) ≤
          (Fintype.card ι : ℝ) * setup.γSeq t * (1 + setup.τSeq t)) ∧
      (∀ t, 1 ≤ t → t + 1 ≤ setup.s →
        setup.γSeq (t + 1) * setup.ηSeq (t + 1) ≤
          setup.γSeq t * (1 + setup.ηSeq t)) ∧
      setup.ηSeq setup.s * setup.μ / 4 ≥
        setup.Lhat / ((Fintype.card ι : ℝ) * (1 + setup.τSeq setup.s)) :=
    ⟨hparam20, hparam21, hparam22, hparam25⟩
  have hγSeq_nonneg : ∀ t, 1 ≤ t → t ≤ setup.s → 0 ≤ setup.γSeq t := by
    exact gamma_nonneg_from_eq_6_6_17_schedule_local setup hα_pos hγSeq_schedule
  have hτSeq_pos : ∀ t, 1 ≤ t → t ≤ setup.s → 0 < setup.τSeq t := by
    intro t ht hts
    have hτt := hτSeq_schedule t ht hts
    rw [hτt, hτ_closed]
    nlinarith [hq_gt_one]
  have h613 :
      setup.expectation
          (setup.ambientFixedWeightedPotentialObservable
            z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s le_rfl xStar) ≤
        setup.γSeq 1 * setup.ηSeq 1 *
            ((setup.μ / 2) *
              setup.expectation
                (setup.ambientFixedDistanceToOptObservable
                  z x0 xMem0 yMem0 hz hx0 hxMem0 0 (Nat.zero_le setup.s) xStar)) +
          Finset.sum Finset.univ
            (fun i =>
              setup.γSeq 1 *
                  ((1 + setup.τSeq 1) - (Fintype.card ι : ℝ)⁻¹) *
                  setup.Lhat / 2 *
                setup.expectation
                  (setup.ambientFixedMemoryDistanceToOptObservable
                    z x0 xMem0 yMem0 hz hx0 hxMem0 0 (Nat.zero_le setup.s) i xStar)) := by
    exact lemma_6_13_hatSourceDomain_corrected_local
      setup z x0 xStar xMem0 yMem0 hz hx0 hxMem0 hsource hhat hgradMem0 hxStar h_opt
      hs
      hparam20 hparam21 hparam22 hparam23 hparam24 hparam25 hγSeq_nonneg hτSeq_pos
  let Ds : ℝ :=
    setup.expectation
      (setup.ambientFixedDistanceToOptObservable
        z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s le_rfl xStar)
  let Ms : ι → ℝ := fun i =>
    setup.expectation
      (setup.ambientFixedMemoryDistanceToOptObservable
        z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s le_rfl i xStar)
  let D0 : ℝ :=
    setup.expectation
      (setup.ambientFixedDistanceToOptObservable
        z x0 xMem0 yMem0 hz hx0 hxMem0 0 (Nat.zero_le setup.s) xStar)
  let M0 : ι → ℝ := fun i =>
    setup.expectation
      (setup.ambientFixedMemoryDistanceToOptObservable
        z x0 xMem0 yMem0 hz hx0 hxMem0 0 (Nat.zero_le setup.s) i xStar)
  have hdist_int_s : Integrable
      (fun ω : Ω =>
        setup.γSeq setup.s * (1 + setup.ηSeq setup.s) *
          (setup.μ / 2 *
            ‖setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s ω -
              xStar‖ ^ 2))
      setup.P := by
    simpa [norm_sub_rev, mul_assoc, mul_left_comm, mul_comm] using
      ((setup.ambientFixedDistanceToOpt_integrable
        z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s le_rfl xStar).const_mul
          (setup.γSeq setup.s * (1 + setup.ηSeq setup.s) * (setup.μ / 2)))
  have hmem_int_s : Integrable
      (fun ω : Ω =>
        Finset.sum Finset.univ
          (fun i =>
            setup.μ * setup.γSeq setup.s * (1 + setup.τSeq setup.s) / 4 *
              ‖setup.ambientFixedXMem z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s i ω -
                xStar‖ ^ 2))
      setup.P := by
    refine MeasureTheory.integrable_finset_sum Finset.univ ?_
    intro i _hi
    simpa [norm_sub_rev, mul_assoc, mul_left_comm, mul_comm] using
      ((setup.ambientFixedMemoryDistanceToOpt_integrable
        z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s le_rfl i xStar).const_mul
          (setup.μ * setup.γSeq setup.s * (1 + setup.τSeq setup.s) / 4))
  have hwp_expand :
      setup.expectation
          (setup.ambientFixedWeightedPotentialObservable
            z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s le_rfl xStar) =
        setup.γSeq setup.s * (1 + setup.ηSeq setup.s) * ((setup.μ / 2) * Ds) +
          Finset.sum Finset.univ
            (fun i =>
              setup.μ * setup.γSeq setup.s * (1 + setup.τSeq setup.s) / 4 * Ms i) := by
    dsimp [Ds, Ms]
    rw [RandomizedAcceleratedProximalPointSetup.expectation,
      RandomizedAcceleratedProximalPointSetup.ambientFixedWeightedPotentialObservable]
    dsimp [RandomizedAcceleratedProximalPointSetup.ambientFixedWeightedPotential,
      RandomizedAcceleratedProximalPointSetup.ambientFixedDistanceToOptObservable,
      RandomizedAcceleratedProximalPointSetup.ambientFixedMemoryDistanceToOptObservable]
    rw [MeasureTheory.integral_add hdist_int_s hmem_int_s]
    rw [MeasureTheory.integral_finset_sum]
    · simp [RandomizedAcceleratedProximalPointSetup.expectation, norm_sub_rev,
        MeasureTheory.integral_mul_const, MeasureTheory.integral_const_mul,
        mul_assoc, mul_left_comm, mul_comm]
    · intro i _hi
      simpa [norm_sub_rev, mul_assoc, mul_left_comm, mul_comm] using
        ((setup.ambientFixedMemoryDistanceToOpt_integrable
          z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s le_rfl i xStar).const_mul
            (setup.μ * setup.γSeq setup.s * (1 + setup.τSeq setup.s) / 4))
  have hγs_coeff :
      (1 - setup.α) * setup.α ^ setup.s *
        (setup.γSeq setup.s * (1 + setup.ηSeq setup.s)) = 1 := by
    have hγs := hγSeq_schedule setup.s hs le_rfl
    have hηs := hηSeq_schedule setup.s hs le_rfl
    rw [hγs, hηs]
    rw [zpow_neg, zpow_natCast]
    field_simp [pow_ne_zero setup.s hα_ne, hδ_ne]
    try ring
  have hτs_coeff :
      (1 - setup.α) * setup.α ^ setup.s *
          (setup.μ * setup.γSeq setup.s * (1 + setup.τSeq setup.s) / 4) =
        setup.μ / (4 * m) := by
    have hγs := hγSeq_schedule setup.s hs le_rfl
    have hτs := hτSeq_schedule setup.s hs le_rfl
    rw [hγs, hτs]
    rw [zpow_neg, zpow_natCast]
    field_simp [pow_ne_zero setup.s hα_ne, hδ_ne, hm_ne, (by simpa [m] using hmδ_ne)]
    try ring
  have hγ1η1_coeff :
      (1 - setup.α) *
          (setup.γSeq 1 * setup.ηSeq 1 * (setup.μ / 2)) =
        setup.μ / 2 := by
    have hγ1 := hγSeq_schedule 1 le_rfl (by simpa using hs)
    have hη1 := hηSeq_schedule 1 le_rfl (by simpa using hs)
    rw [hγ1, hη1]
    rw [zpow_neg, zpow_natCast]
    field_simp [hα_ne, hδ_ne]
    try ring
  have hγ1τ1_coeff :
      (1 - setup.α) *
          (setup.γSeq 1 *
            (1 + setup.τSeq 1 - (Fintype.card ι : ℝ)⁻¹) * setup.Lhat / 2) =
        setup.Lhat / (2 * m) := by
    have hγ1 := hγSeq_schedule 1 le_rfl (by simpa using hs)
    have hτ1 := hτSeq_schedule 1 le_rfl (by simpa using hs)
    rw [hγ1, hτ1]
    rw [zpow_neg, zpow_natCast]
    dsimp [m] at hmδ_ne hm_ne
    field_simp [hα_ne, hδ_ne, hm_ne, hmδ_ne]
    try ring
  have hEq37 :
      (setup.μ / 2) * Ds +
          Finset.sum Finset.univ (fun i => setup.μ / (4 * m) * Ms i) ≤
        setup.α ^ setup.s *
          ((setup.μ / 2) * D0 +
            Finset.sum Finset.univ (fun i => setup.Lhat / (2 * m) * M0 i)) := by
    have hscale_nonneg : 0 ≤ (1 - setup.α) * setup.α ^ setup.s :=
      mul_nonneg (le_of_lt hδ_pos) (pow_nonneg (le_of_lt hα_pos) setup.s)
    have hscaled := mul_le_mul_of_nonneg_left h613 hscale_nonneg
    rw [hwp_expand] at hscaled
    have hleft :
        (1 - setup.α) * setup.α ^ setup.s *
          (setup.γSeq setup.s * (1 + setup.ηSeq setup.s) * (setup.μ / 2 * Ds) +
            Finset.sum Finset.univ
              (fun i => setup.μ * setup.γSeq setup.s * (1 + setup.τSeq setup.s) / 4 *
                Ms i)) =
        (setup.μ / 2) * Ds +
          Finset.sum Finset.univ (fun i => setup.μ / (4 * m) * Ms i) := by
      calc
        _ =
            ((1 - setup.α) * setup.α ^ setup.s *
                (setup.γSeq setup.s * (1 + setup.ηSeq setup.s))) *
              (setup.μ / 2 * Ds) +
              Finset.sum Finset.univ
                (fun i =>
                  ((1 - setup.α) * setup.α ^ setup.s *
                    (setup.μ * setup.γSeq setup.s * (1 + setup.τSeq setup.s) / 4)) *
                    Ms i) := by
            rw [mul_add, Finset.mul_sum]
            congr 1
            · ring
            · apply Finset.sum_congr rfl
              intro i _hi
              ring
        _ =
            (setup.μ / 2) * Ds +
              Finset.sum Finset.univ (fun i => setup.μ / (4 * m) * Ms i) := by
            rw [hγs_coeff]
            simp only [one_mul]
            apply congrArg (fun x => (setup.μ / 2) * Ds + x)
            apply Finset.sum_congr rfl
            intro i _hi
            rw [hτs_coeff]
    have hinner_right :
        (1 - setup.α) *
          (setup.γSeq 1 * setup.ηSeq 1 * (setup.μ / 2 * D0) +
            Finset.sum Finset.univ
              (fun i =>
                setup.γSeq 1 * (1 + setup.τSeq 1 - (Fintype.card ι : ℝ)⁻¹) *
                  setup.Lhat / 2 * M0 i)) =
        (setup.μ / 2) * D0 +
          Finset.sum Finset.univ (fun i => setup.Lhat / (2 * m) * M0 i) := by
      calc
        _ =
            ((1 - setup.α) * (setup.γSeq 1 * setup.ηSeq 1 * (setup.μ / 2))) *
              D0 +
              Finset.sum Finset.univ
                (fun i =>
                  ((1 - setup.α) *
                    (setup.γSeq 1 *
                      (1 + setup.τSeq 1 - (Fintype.card ι : ℝ)⁻¹) *
                        setup.Lhat / 2)) * M0 i) := by
            rw [mul_add, Finset.mul_sum]
            congr 1
            · ring
            · apply Finset.sum_congr rfl
              intro i _hi
              ring
        _ =
            (setup.μ / 2) * D0 +
              Finset.sum Finset.univ (fun i => setup.Lhat / (2 * m) * M0 i) := by
            rw [hγ1η1_coeff]
            apply congrArg (fun x => (setup.μ / 2) * D0 + x)
            apply Finset.sum_congr rfl
            intro i _hi
            rw [hγ1τ1_coeff]
    have hright :
        (1 - setup.α) * setup.α ^ setup.s *
          (setup.γSeq 1 * setup.ηSeq 1 * (setup.μ / 2 * D0) +
            Finset.sum Finset.univ
              (fun i =>
                setup.γSeq 1 * (1 + setup.τSeq 1 - (Fintype.card ι : ℝ)⁻¹) *
                  setup.Lhat / 2 * M0 i)) =
        setup.α ^ setup.s *
          ((setup.μ / 2) * D0 +
            Finset.sum Finset.univ (fun i => setup.Lhat / (2 * m) * M0 i)) := by
      calc
        _ =
            setup.α ^ setup.s *
              ((1 - setup.α) *
                (setup.γSeq 1 * setup.ηSeq 1 * (setup.μ / 2 * D0) +
                  Finset.sum Finset.univ
                    (fun i =>
                      setup.γSeq 1 * (1 + setup.τSeq 1 - (Fintype.card ι : ℝ)⁻¹) *
                        setup.Lhat / 2 * M0 i))) := by
            ring
        _ =
            setup.α ^ setup.s *
              ((setup.μ / 2) * D0 +
                Finset.sum Finset.univ (fun i => setup.Lhat / (2 * m) * M0 i)) := by
            rw [hinner_right]
    rwa [hleft, hright] at hscaled
  let I : ℝ :=
    setup.expectation
      (setup.ambientFixedInitialContractionObservable
        z x0 xMem0 yMem0 hz hx0 hxMem0 xStar)
  have hD0_eq : D0 = ‖xStar - x0‖ ^ 2 := by
    letI : IsProbabilityMeasure setup.P := setup.hP
    dsimp [D0, RandomizedAcceleratedProximalPointSetup.expectation,
      RandomizedAcceleratedProximalPointSetup.ambientFixedDistanceToOptObservable,
      RandomizedAcceleratedProximalPointSetup.ambientFixedX]
    simp [setup.ambientFixedInnerProcess_zero 0 z x0 xMem0 yMem0 hz hx0]
  have hM0_eq : ∀ i, M0 i = ‖xMem0 i - xStar‖ ^ 2 := by
    intro i
    letI : IsProbabilityMeasure setup.P := setup.hP
    dsimp [M0, RandomizedAcceleratedProximalPointSetup.expectation,
      RandomizedAcceleratedProximalPointSetup.ambientFixedMemoryDistanceToOptObservable,
      RandomizedAcceleratedProximalPointSetup.ambientFixedXMem]
    simp [setup.ambientFixedInnerProcess_zero 0 z x0 xMem0 yMem0 hz hx0]
  have hM0_triangle :
      ∀ i, M0 i ≤
        2 * ‖xMem0 i - x0‖ ^ 2 + 2 * ‖x0 - xStar‖ ^ 2 := by
    intro i
    rw [hM0_eq i]
    exact sq_norm_sub_le_two_sq_norm_sub_add_local (xMem0 i) xStar x0
  have hLhat_nonneg : 0 ≤ setup.Lhat := by
    rw [setup.Lhat_def]
    nlinarith [setup.hμ_pos, setup.hμ_le_L]
  have hcoef_Lhat_nonneg : 0 ≤ setup.Lhat / (2 * m) := by
    positivity
  let I0 : ℝ :=
    ‖xStar - x0‖ ^ 2 +
      m⁻¹ * Finset.sum Finset.univ (fun i => ‖xMem0 i - x0‖ ^ 2)
  have hS0_nonneg :
      0 ≤ Finset.sum Finset.univ (fun i => ‖xMem0 i - x0‖ ^ 2) := by
    exact Finset.sum_nonneg (fun i _hi => sq_nonneg _)
  have hA0_nonneg : 0 ≤ ‖xStar - x0‖ ^ 2 := sq_nonneg _
  have hinit_memory_weight_le :
      Finset.sum Finset.univ (fun i => setup.Lhat / (2 * m) * M0 i) ≤
        Finset.sum Finset.univ
          (fun i =>
            setup.Lhat / (2 * m) *
              (2 * ‖xMem0 i - x0‖ ^ 2 + 2 * ‖x0 - xStar‖ ^ 2)) := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    exact mul_le_mul_of_nonneg_left (hM0_triangle i) hcoef_Lhat_nonneg
  have hinit_dom_expanded :
      (setup.μ / 2) * D0 +
          Finset.sum Finset.univ (fun i => setup.Lhat / (2 * m) * M0 i) ≤
        (setup.μ / 2) * (1 + 2 * setup.Lhat / setup.μ) * I0 := by
    calc
      (setup.μ / 2) * D0 +
          Finset.sum Finset.univ (fun i => setup.Lhat / (2 * m) * M0 i)
          ≤ (setup.μ / 2) * ‖xStar - x0‖ ^ 2 +
              Finset.sum Finset.univ
                (fun i =>
                  setup.Lhat / (2 * m) *
                    (2 * ‖xMem0 i - x0‖ ^ 2 + 2 * ‖x0 - xStar‖ ^ 2)) := by
            rw [hD0_eq]
            exact add_le_add (le_refl _) hinit_memory_weight_le
      _ ≤ (setup.μ / 2) * (1 + 2 * setup.Lhat / setup.μ) * I0 := by
            dsimp [I0]
            rw [norm_sub_rev x0 xStar]
            have hcard_pos : 0 < (Fintype.card ι : ℝ) := by
              exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
            have hcard_ne : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hcard_pos
            have hsum_rewrite :
                Finset.sum Finset.univ
                    (fun i =>
                      setup.Lhat / (2 * m) *
                        (2 * ‖xMem0 i - x0‖ ^ 2 + 2 * ‖xStar - x0‖ ^ 2)) =
                  setup.Lhat / m *
                      Finset.sum Finset.univ (fun i => ‖xMem0 i - x0‖ ^ 2) +
                    setup.Lhat * ‖xStar - x0‖ ^ 2 := by
              calc
                Finset.sum Finset.univ
                    (fun i =>
                      setup.Lhat / (2 * m) *
                        (2 * ‖xMem0 i - x0‖ ^ 2 + 2 * ‖xStar - x0‖ ^ 2))
                    =
                  Finset.sum Finset.univ
                    (fun i =>
                      setup.Lhat / m * ‖xMem0 i - x0‖ ^ 2 +
                        setup.Lhat / m * ‖xStar - x0‖ ^ 2) := by
                    apply Finset.sum_congr rfl
                    intro i _hi
                    field_simp [hm_ne]
                _ =
                  setup.Lhat / m *
                      Finset.sum Finset.univ (fun i => ‖xMem0 i - x0‖ ^ 2) +
                    (Fintype.card ι : ℝ) * (setup.Lhat / m * ‖xStar - x0‖ ^ 2) := by
                    rw [Finset.sum_add_distrib]
                    simp [Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm]
                _ =
                  setup.Lhat / m *
                      Finset.sum Finset.univ (fun i => ‖xMem0 i - x0‖ ^ 2) +
                    setup.Lhat * ‖xStar - x0‖ ^ 2 := by
                    dsimp [m] at hm_ne
                    field_simp [hcard_ne]
                    ring
            rw [hsum_rewrite]
            field_simp [hμ_ne, hm_ne]
            nlinarith [setup.hμ_pos, hLhat_nonneg, hS0_nonneg, hA0_nonneg]
  have hMs_nonneg : ∀ i, 0 ≤ Ms i := by
    intro i
    dsimp [Ms, RandomizedAcceleratedProximalPointSetup.expectation,
      RandomizedAcceleratedProximalPointSetup.ambientFixedMemoryDistanceToOptObservable]
    exact integral_nonneg (fun ω => sq_nonneg _)
  have hterminal_memory_weight_nonneg :
      0 ≤ Finset.sum Finset.univ (fun i => setup.μ / (4 * m) * Ms i) := by
    have hcoef_mu_mem_nonneg : 0 ≤ setup.μ / (4 * m) := by
      exact div_nonneg (le_of_lt setup.hμ_pos) (mul_nonneg (by norm_num) (le_of_lt hm_pos))
    refine Finset.sum_nonneg ?_
    intro i _hi
    exact mul_nonneg hcoef_mu_mem_nonneg (hMs_nonneg i)
  have hdist_weight_le_left :
      (setup.μ / 2) * Ds ≤
        (setup.μ / 2) * Ds +
          Finset.sum Finset.univ (fun i => setup.μ / (4 * m) * Ms i) := by
    linarith
  have hαpow_nonneg : 0 ≤ setup.α ^ setup.s :=
    pow_nonneg (le_of_lt hα_pos) setup.s
  have hdist_weight_le_B0 :
      (setup.μ / 2) * Ds ≤
        setup.α ^ setup.s *
          ((setup.μ / 2) * (1 + 2 * setup.Lhat / setup.μ) * I0) := by
    exact hdist_weight_le_left.trans
      (hEq37.trans (mul_le_mul_of_nonneg_left hinit_dom_expanded hαpow_nonneg))
  have hDs_le_B0 :
      Ds ≤ setup.α ^ setup.s * (1 + 2 * setup.Lhat / setup.μ) * I0 := by
    have hrewrite :
        setup.α ^ setup.s *
            ((setup.μ / 2) * (1 + 2 * setup.Lhat / setup.μ) * I0) =
          (setup.μ / 2) *
            (setup.α ^ setup.s * (1 + 2 * setup.Lhat / setup.μ) * I0) := by
      ring
    rw [hrewrite] at hdist_weight_le_B0
    have hμhalf_pos : 0 < setup.μ / 2 := half_pos setup.hμ_pos
    exact le_of_mul_le_mul_left hdist_weight_le_B0 hμhalf_pos
  have hI_eq : I = I0 := by
    letI : IsProbabilityMeasure setup.P := setup.hP
    dsimp [I, I0, m, RandomizedAcceleratedProximalPointSetup.expectation,
      RandomizedAcceleratedProximalPointSetup.ambientFixedInitialContractionObservable,
      RandomizedAcceleratedProximalPointSetup.ambientFixedX,
      RandomizedAcceleratedProximalPointSetup.ambientFixedXMem]
    simp [setup.ambientFixedInnerProcess_zero 0 z x0 xMem0 yMem0 hz hx0,
      norm_sub_rev]
  have hfirst_conj :
      setup.expectation
          (setup.ambientFixedDistanceToOptObservable
            z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s le_rfl xStar) ≤
        setup.α ^ setup.s *
            (1 + 2 * setup.Lhat / setup.μ) *
            setup.expectation
              (setup.ambientFixedInitialContractionObservable
                z x0 xMem0 yMem0 hz hx0 hxMem0 xStar) := by
    dsimp [Ds, I] at hDs_le_B0 hI_eq
    rw [hI_eq]
    exact hDs_le_B0
  let B0 : ℝ := setup.α ^ setup.s * (1 + 2 * setup.Lhat / setup.μ) * I0
  have hDs_nonneg : 0 ≤ Ds := by
    dsimp [Ds, RandomizedAcceleratedProximalPointSetup.expectation,
      RandomizedAcceleratedProximalPointSetup.ambientFixedDistanceToOptObservable]
    exact integral_nonneg (fun ω => sq_nonneg _)
  have hdist_weight_nonneg : 0 ≤ (setup.μ / 2) * Ds := by
    exact mul_nonneg (le_of_lt (half_pos setup.hμ_pos)) hDs_nonneg
  have hterminal_memory_weight_le_B0 :
      Finset.sum Finset.univ (fun i => setup.μ / (4 * m) * Ms i) ≤
        setup.α ^ setup.s *
          ((setup.μ / 2) * (1 + 2 * setup.Lhat / setup.μ) * I0) := by
    have hmem_le_left :
        Finset.sum Finset.univ (fun i => setup.μ / (4 * m) * Ms i) ≤
          (setup.μ / 2) * Ds +
            Finset.sum Finset.univ (fun i => setup.μ / (4 * m) * Ms i) := by
      linarith
    exact hmem_le_left.trans
      (hEq37.trans (mul_le_mul_of_nonneg_left hinit_dom_expanded hαpow_nonneg))
  have hterminal_memory_weight_eq :
      Finset.sum Finset.univ (fun i => setup.μ / (4 * m) * Ms i) =
        (setup.μ / 4) * (m⁻¹ * Finset.sum Finset.univ (fun i => Ms i)) := by
    calc
      Finset.sum Finset.univ (fun i => setup.μ / (4 * m) * Ms i)
          = setup.μ / (4 * m) * Finset.sum Finset.univ (fun i => Ms i) := by
            rw [Finset.mul_sum]
      _ = (setup.μ / 4) * (m⁻¹ * Finset.sum Finset.univ (fun i => Ms i)) := by
            field_simp [hm_ne]
  have hMemAvg_le_twoB0 :
      m⁻¹ * Finset.sum Finset.univ (fun i => Ms i) ≤ 2 * B0 := by
    have hscaled :
        (setup.μ / 4) * (m⁻¹ * Finset.sum Finset.univ (fun i => Ms i)) ≤
          (setup.μ / 4) * (2 * B0) := by
      rw [← hterminal_memory_weight_eq]
      dsimp [B0]
      have hrhs :
          setup.α ^ setup.s *
              ((setup.μ / 2) * (1 + 2 * setup.Lhat / setup.μ) * I0) =
            (setup.μ / 4) *
              (2 * (setup.α ^ setup.s * (1 + 2 * setup.Lhat / setup.μ) * I0)) := by
        ring
      rwa [← hrhs]
    have hμquarter_pos : 0 < setup.μ / 4 := div_pos setup.hμ_pos (by norm_num)
    exact le_of_mul_le_mul_left hscaled hμquarter_pos
  have hdisp_le_two :
      setup.expectation
          (setup.ambientFixedMemoryDispersionObservable
            z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s le_rfl) ≤
        2 * (m⁻¹ * Finset.sum Finset.univ (fun i => Ms i)) + 2 * Ds := by
    have hdisp_pointwise :
        ∀ ω : Ω,
          m⁻¹ *
              Finset.sum Finset.univ
                (fun i =>
                  ‖setup.ambientFixedXMem z x0 xMem0 yMem0 hz hx0 hxMem0
                      setup.s i ω -
                    setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0
                      setup.s ω‖ ^ 2) ≤
            2 *
                (m⁻¹ *
                  Finset.sum Finset.univ
                    (fun i =>
                      ‖setup.ambientFixedXMem z x0 xMem0 yMem0 hz hx0 hxMem0
                          setup.s i ω - xStar‖ ^ 2)) +
              2 * ‖xStar -
                    setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0
                      setup.s ω‖ ^ 2 := by
      intro ω
      have hsum_le :
          Finset.sum Finset.univ
              (fun i =>
                ‖setup.ambientFixedXMem z x0 xMem0 yMem0 hz hx0 hxMem0
                    setup.s i ω -
                  setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0
                    setup.s ω‖ ^ 2) ≤
            Finset.sum Finset.univ
              (fun i =>
                2 *
                    ‖setup.ambientFixedXMem z x0 xMem0 yMem0 hz hx0 hxMem0
                        setup.s i ω - xStar‖ ^ 2 +
                  2 * ‖xStar -
                        setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0
                          setup.s ω‖ ^ 2) := by
        refine Finset.sum_le_sum ?_
        intro i _hi
        simpa [norm_sub_rev] using
          sq_norm_sub_le_two_sq_norm_sub_add_local
            (setup.ambientFixedXMem z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s i ω)
            (setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s ω)
            xStar
      have hscaled := mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr (le_of_lt hm_pos))
      calc
        m⁻¹ *
            Finset.sum Finset.univ
              (fun i =>
                ‖setup.ambientFixedXMem z x0 xMem0 yMem0 hz hx0 hxMem0
                    setup.s i ω -
                  setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0
                    setup.s ω‖ ^ 2)
            ≤
          m⁻¹ *
            Finset.sum Finset.univ
              (fun i =>
                2 *
                    ‖setup.ambientFixedXMem z x0 xMem0 yMem0 hz hx0 hxMem0
                        setup.s i ω - xStar‖ ^ 2 +
                  2 * ‖xStar -
                        setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0
                          setup.s ω‖ ^ 2) := hscaled
        _ =
            2 *
                (m⁻¹ *
                  Finset.sum Finset.univ
                    (fun i =>
                      ‖setup.ambientFixedXMem z x0 xMem0 yMem0 hz hx0 hxMem0
                          setup.s i ω - xStar‖ ^ 2)) +
              2 * ‖xStar -
                    setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0
                      setup.s ω‖ ^ 2 := by
          rw [Finset.sum_add_distrib]
          simp only [Finset.sum_const, nsmul_eq_mul]
          dsimp [m]
          dsimp [m] at hm_ne
          field_simp [hm_ne]
          rw [mul_add, Finset.mul_sum]
          ring
    have hlhs_disp_int : Integrable
        (fun ω : Ω =>
          m⁻¹ *
              Finset.sum Finset.univ
                (fun i =>
                  ‖setup.ambientFixedXMem z x0 xMem0 yMem0 hz hx0 hxMem0
                      setup.s i ω -
                    setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0
                      setup.s ω‖ ^ 2))
        setup.P := by
      simpa [m] using
        setup.ambientFixedMemoryDispersion_integrable
          z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s le_rfl
    have hmem_to_star_avg_int : Integrable
        (fun ω : Ω =>
          m⁻¹ *
            Finset.sum Finset.univ
              (fun i =>
                ‖setup.ambientFixedXMem z x0 xMem0 yMem0 hz hx0 hxMem0
                    setup.s i ω - xStar‖ ^ 2))
        setup.P := by
      refine (MeasureTheory.integrable_finset_sum Finset.univ ?_).const_mul m⁻¹
      intro i _hi
      simpa [norm_sub_rev] using
        setup.ambientFixedMemoryDistanceToOpt_integrable
          z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s le_rfl i xStar
    have hdist_to_star_int : Integrable
        (fun ω : Ω =>
          ‖xStar -
            setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s ω‖ ^ 2)
        setup.P := by
      simpa [norm_sub_rev] using
        setup.ambientFixedDistanceToOpt_integrable
          z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s le_rfl xStar
    have hrhs_disp_int : Integrable
        (fun ω : Ω =>
          2 *
              (m⁻¹ *
                Finset.sum Finset.univ
                  (fun i =>
                    ‖setup.ambientFixedXMem z x0 xMem0 yMem0 hz hx0 hxMem0
                        setup.s i ω - xStar‖ ^ 2)) +
            2 * ‖xStar -
                  setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0
                    setup.s ω‖ ^ 2)
        setup.P :=
      (hmem_to_star_avg_int.const_mul 2).add (hdist_to_star_int.const_mul 2)
    have hdisp_integral_le :
        (∫ ω : Ω,
          m⁻¹ *
              Finset.sum Finset.univ
                (fun i =>
                  ‖setup.ambientFixedXMem z x0 xMem0 yMem0 hz hx0 hxMem0
                      setup.s i ω -
                    setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0
                      setup.s ω‖ ^ 2) ∂setup.P) ≤
        ∫ ω : Ω,
          (2 *
              (m⁻¹ *
                Finset.sum Finset.univ
                  (fun i =>
                    ‖setup.ambientFixedXMem z x0 xMem0 yMem0 hz hx0 hxMem0
                        setup.s i ω - xStar‖ ^ 2)) +
            2 * ‖xStar -
                  setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0
                    setup.s ω‖ ^ 2) ∂setup.P := by
      exact MeasureTheory.integral_mono hlhs_disp_int hrhs_disp_int hdisp_pointwise
    have hmem_avg_integral_eq :
        (∫ ω : Ω,
          m⁻¹ *
            Finset.sum Finset.univ
              (fun i =>
                ‖setup.ambientFixedXMem z x0 xMem0 yMem0 hz hx0 hxMem0
                    setup.s i ω - xStar‖ ^ 2) ∂setup.P) =
          m⁻¹ * Finset.sum Finset.univ (fun i => Ms i) := by
      rw [MeasureTheory.integral_const_mul]
      rw [MeasureTheory.integral_finset_sum]
      · dsimp [Ms, RandomizedAcceleratedProximalPointSetup.expectation,
          RandomizedAcceleratedProximalPointSetup.ambientFixedMemoryDistanceToOptObservable]
      · intro i _hi
        simpa [norm_sub_rev] using
          setup.ambientFixedMemoryDistanceToOpt_integrable
            z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s le_rfl i xStar
    have hdist_integral_eq :
        (∫ ω : Ω,
          ‖xStar -
            setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s ω‖ ^ 2
          ∂setup.P) = Ds := by
      dsimp [Ds, RandomizedAcceleratedProximalPointSetup.expectation,
        RandomizedAcceleratedProximalPointSetup.ambientFixedDistanceToOptObservable]
    have hrhs_integral_eq :
        (∫ ω : Ω,
          (2 *
              (m⁻¹ *
                Finset.sum Finset.univ
                  (fun i =>
                    ‖setup.ambientFixedXMem z x0 xMem0 yMem0 hz hx0 hxMem0
                        setup.s i ω - xStar‖ ^ 2)) +
            2 * ‖xStar -
                  setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0
                    setup.s ω‖ ^ 2) ∂setup.P) =
          2 * (m⁻¹ * Finset.sum Finset.univ (fun i => Ms i)) + 2 * Ds := by
      rw [MeasureTheory.integral_add (hmem_to_star_avg_int.const_mul 2)
        (hdist_to_star_int.const_mul 2)]
      rw [show
          (∫ ω : Ω,
            2 *
              (m⁻¹ *
                Finset.sum Finset.univ
                  (fun i =>
                    ‖setup.ambientFixedXMem z x0 xMem0 yMem0 hz hx0 hxMem0
                        setup.s i ω - xStar‖ ^ 2)) ∂setup.P) =
            2 * (∫ ω : Ω,
              m⁻¹ *
                Finset.sum Finset.univ
                  (fun i =>
                    ‖setup.ambientFixedXMem z x0 xMem0 yMem0 hz hx0 hxMem0
                        setup.s i ω - xStar‖ ^ 2) ∂setup.P) by
          rw [MeasureTheory.integral_const_mul]]
      rw [show
          (∫ ω : Ω,
            2 * ‖xStar -
                  setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0
                    setup.s ω‖ ^ 2 ∂setup.P) =
            2 * (∫ ω : Ω,
              ‖xStar -
                setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0
                  setup.s ω‖ ^ 2 ∂setup.P) by
          rw [MeasureTheory.integral_const_mul]]
      rw [hmem_avg_integral_eq, hdist_integral_eq]
    change
      (∫ ω : Ω,
        m⁻¹ *
            Finset.sum Finset.univ
              (fun i =>
                ‖setup.ambientFixedXMem z x0 xMem0 yMem0 hz hx0 hxMem0
                    setup.s i ω -
                  setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0
                    setup.s ω‖ ^ 2) ∂setup.P) ≤
        2 * (m⁻¹ * Finset.sum Finset.univ (fun i => Ms i)) + 2 * Ds
    exact hdisp_integral_le.trans_eq hrhs_integral_eq
  have hB0_eq_I :
      B0 =
        setup.α ^ setup.s * (1 + 2 * setup.Lhat / setup.μ) * I := by
    dsimp [B0]
    rw [hI_eq]
  have hDs_le_B0_alias : Ds ≤ B0 := by
    dsimp [B0]
    exact hDs_le_B0
  have hsecond_conj :
      setup.expectation
          (setup.ambientFixedMemoryDispersionObservable
            z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s le_rfl) ≤
        6 * setup.α ^ setup.s *
            (1 + 2 * setup.Lhat / setup.μ) *
            setup.expectation
              (setup.ambientFixedInitialContractionObservable
                z x0 xMem0 yMem0 hz hx0 hxMem0 xStar) := by
    have hto_six :
        setup.expectation
            (setup.ambientFixedMemoryDispersionObservable
              z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s le_rfl) ≤
          6 * B0 := by
      calc
        setup.expectation
            (setup.ambientFixedMemoryDispersionObservable
              z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s le_rfl)
            ≤ 2 * (m⁻¹ * Finset.sum Finset.univ (fun i => Ms i)) + 2 * Ds :=
              hdisp_le_two
        _ ≤ 2 * (2 * B0) + 2 * B0 := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left hMemAvg_le_twoB0 (by norm_num))
                (mul_le_mul_of_nonneg_left hDs_le_B0_alias (by norm_num))
        _ = 6 * B0 := by ring
    calc
      setup.expectation
          (setup.ambientFixedMemoryDispersionObservable
            z x0 xMem0 yMem0 hz hx0 hxMem0 setup.s le_rfl)
          ≤ 6 * B0 := hto_six
      _ =
          6 * setup.α ^ setup.s *
            (1 + 2 * setup.Lhat / setup.μ) *
            setup.expectation
              (setup.ambientFixedInitialContractionObservable
                z x0 xMem0 yMem0 hz hx0 hxMem0 xStar) := by
            rw [hB0_eq_I]
            ring
  constructor
  · exact hfirst_conj
  · exact hsecond_conj

/-- Generated-run corrected Theorem 6.17 entrypoint.  Considered the Part003
candidate `theorem_6_17_hatSourceDomain_corrected`; it is the exact source-route
interface needed by Part004, but Part003 currently fails to build, so this local
shim keeps Lan Lemma 6.14's Eq. (6.6.38)-(6.6.39) bridge type-correct. -/
theorem theorem_6_17_hatSourceDomain_corrected
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (ℓ : setup.OutputIndex)
    (houter_hat : setup.outerPrefixHatSourceDomain ℓ)
    (ω₀ : Ω)
    (hs : 1 ≤ setup.s)
    (hα_schedule :
      setup.α =
        1 - 2 / ((Fintype.card ι : ℝ) *
          (Real.sqrt (1 + 16 * (2 + setup.L / setup.μ) / (Fintype.card ι : ℝ)) + 1)))
    (hαSeq_schedule : ∀ t, 1 ≤ t → t ≤ setup.s → setup.αSeq t = setup.α)
    (hγSeq_schedule : ∀ t, 1 ≤ t → t ≤ setup.s → setup.γSeq t = setup.α ^ (-(t : ℤ)))
    (hτSeq_schedule : ∀ t, 1 ≤ t → t ≤ setup.s →
      setup.τSeq t = ((Fintype.card ι : ℝ) * (1 - setup.α))⁻¹ - 1)
    (hηSeq_schedule : ∀ t, 1 ≤ t → t ≤ setup.s →
      setup.ηSeq t = setup.α * (1 - setup.α)⁻¹) :
    let z : E := setup.outerCenter ℓ.1 ω₀
    let xStar : E := setup.subproblemOptOutput ℓ ω₀
    let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).xBarMem
    let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).yBarMem
    let hz : z ∈ setup.X := by
      simpa [z] using setup.outerCenter_mem ℓ ω₀
    let hxStar : xStar ∈ setup.X := by
      simpa [xStar] using setup.subproblemOptOutput_mem ℓ ω₀
    (setup.expectation
        (setup.ambientFixedDistanceToOptAnyMemObservable
          z z xMem0 yMem0 hz hz setup.s le_rfl xStar) ≤
      setup.α ^ setup.s *
          (1 + 2 * setup.Lhat / setup.μ) *
          setup.expectation
            (setup.ambientFixedInitialContractionAnyMemObservable
              z z xMem0 yMem0 hz hz xStar)) ∧
    (setup.expectation
        (setup.ambientFixedMemoryDispersionAnyMemObservable
          z z xMem0 yMem0 hz hz setup.s le_rfl) ≤
      6 * setup.α ^ setup.s *
          (1 + 2 * setup.Lhat / setup.μ) *
          setup.expectation
            (setup.ambientFixedInitialContractionAnyMemObservable
              z z xMem0 yMem0 hz hz xStar)) := by
  classical
  let z : E := setup.outerCenter ℓ.1 ω₀
  let xStar : E := setup.subproblemOptOutput ℓ ω₀
  let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).xBarMem
  let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).yBarMem
  have hz : z ∈ setup.X := by
    simpa [z] using setup.outerCenter_mem ℓ ω₀
  have hxStar : xStar ∈ setup.X := by
    simpa [xStar] using setup.subproblemOptOutput_mem ℓ ω₀
  have hIcc : ℓ.1 ∈ Finset.Icc 1 (setup.k : ℕ) := by
    simpa [RandomizedAcceleratedProximalPointSetup.outputWindow] using ℓ.2
  have hsubproblem_min :
      IsMinOn (setup.subproblemObjective ℓ.1 ω₀) setup.X
        (setup.subproblemOptOutput ℓ ω₀) := by
    simpa [RandomizedAcceleratedProximalPointSetup.subproblemOptOutput] using
      setup.subproblemOpt_is_minimizer ℓ.1 hIcc ω₀
  have hopt : ∀ u : {x : E // x ∈ setup.X},
      (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ (fun i => setup.psiAtOn z i ⟨xStar, hxStar⟩) +
        setup.phiAt z xStar ≤
      (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ (fun i => setup.psiAtOn z i u) +
        setup.phiAt z u.1 := by
    intro u
    have hle := hsubproblem_min (a := u.1) u.2
    have hopt_sum :
        Finset.sum Finset.univ
            (fun i => setup.psiAt z i xStar) =
          Finset.sum Finset.univ
            (fun i => setup.psiAtOn z i ⟨xStar, hxStar⟩) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact setup.psiAt_of_mem z i hxStar
    simpa [z, xStar, RandomizedAcceleratedProximalPointSetup.subproblemObjective,
      RandomizedAcceleratedProximalPointSetup.psi,
      RandomizedAcceleratedProximalPointSetup.phi, hopt_sum] using hle
  have hsource_requirements :
      (∀ i : ι, xMem0 i ∈ setup.X) ∧
        setup.ambientFixedSourceDomain 0 z z xMem0 yMem0 hz hz ∧
        setup.ambientFixedHatSourceDomain 0 z z xMem0 yMem0 hz hz := by
    exact setup.outerPrefixHatSourceDomain_base ℓ houter_hat ω₀
  have houter_grad :=
    outerPrefixHatSourceDomain_initialGradientMemory setup ℓ houter_hat ω₀
  have hgradMem0 :
      setup.ambientFixedInitialGradientMemory z xMem0 yMem0 hsource_requirements.1 := by
    exact houter_grad.2 hsource_requirements.1
  have h617 :
      (setup.expectation
          (setup.ambientFixedDistanceToOptObservable
            z z xMem0 yMem0 hz hz hsource_requirements.1 setup.s le_rfl xStar) ≤
        setup.α ^ setup.s *
            (1 + 2 * setup.Lhat / setup.μ) *
            setup.expectation
              (setup.ambientFixedInitialContractionObservable
                z z xMem0 yMem0 hz hz hsource_requirements.1 xStar)) ∧
      (setup.expectation
          (setup.ambientFixedMemoryDispersionObservable
            z z xMem0 yMem0 hz hz hsource_requirements.1 setup.s le_rfl) ≤
        6 * setup.α ^ setup.s *
            (1 + 2 * setup.Lhat / setup.μ) *
            setup.expectation
              (setup.ambientFixedInitialContractionObservable
                z z xMem0 yMem0 hz hz hsource_requirements.1 xStar)) := by
    exact theorem_6_17_hatSourceDomain_initialGradientMemory_local
      setup z z xStar xMem0 yMem0 hz hz hsource_requirements.1
      hsource_requirements.2.1 hsource_requirements.2.2 hgradMem0 hxStar
      hs hα_schedule hαSeq_schedule hγSeq_schedule hτSeq_schedule hηSeq_schedule hopt
  simpa [z, xStar, xMem0, yMem0,
    RandomizedAcceleratedProximalPointSetup.ambientFixedDistanceToOptAnyMemObservable,
    RandomizedAcceleratedProximalPointSetup.ambientFixedInitialContractionAnyMemObservable,
    RandomizedAcceleratedProximalPointSetup.ambientFixedMemoryDispersionAnyMemObservable,
    RandomizedAcceleratedProximalPointSetup.ambientFixedXAnyMem,
    RandomizedAcceleratedProximalPointSetup.ambientFixedXMemAnyMem,
    RandomizedAcceleratedProximalPointSetup.ambientFixedDistanceToOptObservable,
    RandomizedAcceleratedProximalPointSetup.ambientFixedInitialContractionObservable,
    RandomizedAcceleratedProximalPointSetup.ambientFixedMemoryDispersionObservable,
    RandomizedAcceleratedProximalPointSetup.ambientFixedX,
    RandomizedAcceleratedProximalPointSetup.ambientFixedXMem] using h617

/-- Aligns with Lan Lemma 6.14, Eq. (6.6.38) RHS.  Considered the Part003
candidate `outer_theorem617_initial_contraction_transport`; it is the exact
time-zero transport helper, but the repaired header cannot import it. -/
theorem outer_theorem617_initial_contraction_transport
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (ℓ : setup.OutputIndex) :
    (∫ ω₀ : Ω,
        let z : E := setup.outerCenter ℓ.1 ω₀
        let xStar : E := setup.subproblemOptOutput ℓ ω₀
        let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).xBarMem
        let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).yBarMem
        let hz : z ∈ setup.X := by
          simpa [z] using setup.outerCenter_mem ℓ ω₀
        setup.expectation
          (setup.ambientFixedInitialContractionAnyMemObservable
            z z xMem0 yMem0 hz hz xStar) ∂setup.P) =
      ∫ ω : Ω,
        setup.selectedPreviousProxDisplacementIntegrand ℓ ω +
          setup.outerMemoryDispersionIntegrand (ℓ.1 - 1) ω ∂setup.P := by
  classical
  letI : IsProbabilityMeasure setup.P := setup.hP
  apply integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro ω₀
  let z : E := setup.outerCenter ℓ.1 ω₀
  let xStar : E := setup.subproblemOptOutput ℓ ω₀
  let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).xBarMem
  let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).yBarMem
  let hz : z ∈ setup.X := by
    simpa [z] using setup.outerCenter_mem ℓ ω₀
  have hcenter :
      z = setup.xBarIter (ℓ.1 - 1) ω₀ := by
    simpa [z] using outerCenter_eq_xBarIter_pred setup ℓ ω₀
  simp [RandomizedAcceleratedProximalPointSetup.expectation,
    RandomizedAcceleratedProximalPointSetup.ambientFixedInitialContractionAnyMemObservable,
    RandomizedAcceleratedProximalPointSetup.ambientFixedXAnyMem,
    RandomizedAcceleratedProximalPointSetup.ambientFixedXMemAnyMem,
    RandomizedAcceleratedProximalPointSetup.selectedPreviousProxDisplacementIntegrand,
    RandomizedAcceleratedProximalPointSetup.outerMemoryDispersionIntegrand,
    RandomizedAcceleratedProximalPointSetup.xBarIter,
    RandomizedAcceleratedProximalPointSetup.ambientFixedInnerProcess_zero,
    z, xStar, xMem0, yMem0, hcenter]

/-- Aligns with Lan Lemma 6.14, Eq. (6.6.38) RHS.  Considered the Part003
candidate `outer_theorem617_initial_contraction_integrable`; it is the exact
integrability helper, but is unavailable while Part003 is unbuildable. -/
theorem outer_theorem617_initial_contraction_integrable
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (ℓ : setup.OutputIndex) :
    Integrable
      (fun ω₀ : Ω =>
        let z : E := setup.outerCenter ℓ.1 ω₀
        let xStar : E := setup.subproblemOptOutput ℓ ω₀
        let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).xBarMem
        let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).yBarMem
        let hz : z ∈ setup.X := by
          simpa [z] using setup.outerCenter_mem ℓ ω₀
        setup.expectation
          (setup.ambientFixedInitialContractionAnyMemObservable
            z z xMem0 yMem0 hz hz xStar)) setup.P := by
  classical
  letI : IsProbabilityMeasure setup.P := setup.hP
  have hfun :
      (fun ω₀ : Ω =>
        let z : E := setup.outerCenter ℓ.1 ω₀
        let xStar : E := setup.subproblemOptOutput ℓ ω₀
        let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).xBarMem
        let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).yBarMem
        let hz : z ∈ setup.X := by
          simpa [z] using setup.outerCenter_mem ℓ ω₀
        setup.expectation
          (setup.ambientFixedInitialContractionAnyMemObservable
            z z xMem0 yMem0 hz hz xStar)) =
        fun ω : Ω =>
          setup.selectedPreviousProxDisplacementIntegrand ℓ ω +
            setup.outerMemoryDispersionIntegrand (ℓ.1 - 1) ω := by
    funext ω₀
    let z : E := setup.outerCenter ℓ.1 ω₀
    let xStar : E := setup.subproblemOptOutput ℓ ω₀
    let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).xBarMem
    let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).yBarMem
    let hz : z ∈ setup.X := by
      simpa [z] using setup.outerCenter_mem ℓ ω₀
    have hcenter :
        z = setup.xBarIter (ℓ.1 - 1) ω₀ := by
      simpa [z] using outerCenter_eq_xBarIter_pred setup ℓ ω₀
    simp [RandomizedAcceleratedProximalPointSetup.expectation,
      RandomizedAcceleratedProximalPointSetup.ambientFixedInitialContractionAnyMemObservable,
      RandomizedAcceleratedProximalPointSetup.ambientFixedXAnyMem,
      RandomizedAcceleratedProximalPointSetup.ambientFixedXMemAnyMem,
      RandomizedAcceleratedProximalPointSetup.selectedPreviousProxDisplacementIntegrand,
      RandomizedAcceleratedProximalPointSetup.outerMemoryDispersionIntegrand,
      RandomizedAcceleratedProximalPointSetup.xBarIter,
      RandomizedAcceleratedProximalPointSetup.ambientFixedInnerProcess_zero,
      z, xStar, xMem0, yMem0, hcenter]
  rw [hfun]
  exact (setup.selectedPreviousProxDisplacementIntegrand_integrable ℓ).add
    (setup.outerPreviousMemoryDispersionIntegrand_integrable ℓ)

/-- Aligns with Lan Lemma 6.14 after substituting `Lhat = L + 2μ`.  Considered
the Part003 candidate `theorem617_outer_scalar_constants`; it is the exact
scalar normalization used downstream, so this shim preserves its statement. -/
theorem theorem617_outer_scalar_constants
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω) :
    setup.α ^ setup.s * (1 + 2 * setup.Lhat / setup.μ) =
        (6 * (5 + 2 * setup.L / setup.μ)) * setup.α ^ setup.s / 6 ∧
      6 * setup.α ^ setup.s * (1 + 2 * setup.Lhat / setup.μ) =
        (6 * (5 + 2 * setup.L / setup.μ)) * setup.α ^ setup.s := by
  have hμ_ne : setup.μ ≠ 0 := ne_of_gt setup.hμ_pos
  constructor
  · rw [setup.Lhat_def]
    field_simp [hμ_ne]
    ring
  · rw [setup.Lhat_def]
    field_simp [hμ_ne]
    ring

/-- Aligns with Lan Lemma 6.14, Eq. (6.6.38).  Considered the Part003 candidate
`selectedCurrentProxDisplacementIntegrand_eq_offset_terminal`; it is the exact
terminal-field projection, but Part003 cannot currently be imported. -/
theorem selectedCurrentProxDisplacementIntegrand_eq_offset_terminal
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (ℓ : setup.OutputIndex) (ω : Ω) :
    setup.selectedCurrentProxDisplacementIntegrand ℓ ω =
      let z : E := setup.outerCenter ℓ.1 ω
      let xStar : E := setup.subproblemOptOutput ℓ ω
      let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω).xBarMem
      let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω).yBarMem
      let hz : z ∈ setup.X := by
        simpa [z] using setup.outerCenter_mem ℓ ω
      ‖xStar -
        (setup.ambientFixedInnerProcess (setup.outerSampleOffset (ℓ.1 - 1))
          z z xMem0 yMem0 hz hz setup.s ω).x‖ ^ 2 := by
  classical
  have hIcc : ℓ.1 ∈ Finset.Icc 1 (setup.k : ℕ) := by
    simpa [RandomizedAcceleratedProximalPointSetup.outputWindow] using ℓ.2
  have hbounds := Finset.mem_Icc.mp hIcc
  have hidx : ℓ.1 - 1 + 1 = ℓ.1 := Nat.sub_add_cancel hbounds.1
  have hsucc : ℓ.1 - 1 + 1 ≤ (setup.k : ℕ) := by
    simpa [hidx] using hbounds.2
  have hcenter :
      setup.outerCenter ℓ.1 ω = setup.xBarIter (ℓ.1 - 1) ω :=
    outerCenter_eq_xBarIter_pred setup ℓ ω
  have hproc := setup.ambientProcess_succ (ℓ.1 - 1) hsucc ω
  have hprocℓ :
      setup.ambientProcess ℓ.1 ω =
        let prev := setup.ambientProcess (ℓ.1 - 1) ω
        let hprev :=
          setup.eq_6_6_13_ambientProcess_mem (ℓ.1 - 1)
            (Nat.le_of_succ_le hsucc) ω
        let innerRec :=
          setup.ambientFixedInnerProcess (setup.outerSampleOffset (ℓ.1 - 1))
            prev.xBar prev.xBar prev.xBarMem prev.yBarMem hprev hprev
        let final := innerRec setup.s ω
        { inner := fun t => innerRec t ω
          xBar := final.x
          xBarMem := final.xMem
          yBarMem := fun i =>
            final.yMem i + (2 * setup.μ) • (prev.xBar - final.x) } := by
    simpa [hidx] using hproc
  have hxbar :
      setup.xBarIter ℓ.1 ω =
        (setup.ambientFixedInnerProcess (setup.outerSampleOffset (ℓ.1 - 1))
          (setup.outerCenter ℓ.1 ω) (setup.outerCenter ℓ.1 ω)
          (setup.ambientProcess (ℓ.1 - 1) ω).xBarMem
          (setup.ambientProcess (ℓ.1 - 1) ω).yBarMem
          (by simpa using setup.outerCenter_mem ℓ ω)
          (by simpa using setup.outerCenter_mem ℓ ω) setup.s ω).x := by
    simpa [RandomizedAcceleratedProximalPointSetup.xBarIter, hcenter] using
      congrArg RapGradOuterState.xBar hprocℓ
  simp [RandomizedAcceleratedProximalPointSetup.selectedCurrentProxDisplacementIntegrand,
    hxbar]

/-- Aligns with Lan Lemma 6.14, Eq. (6.6.39).  Considered the Part003 candidate
`outerMemoryDispersionIntegrand_eq_offset_terminal`; it is the exact terminal
memory projection, but Part003 cannot currently be imported. -/
theorem outerMemoryDispersionIntegrand_eq_offset_terminal
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (ℓ : setup.OutputIndex) (ω : Ω) :
    setup.outerMemoryDispersionIntegrand ℓ.1 ω =
      let z : E := setup.outerCenter ℓ.1 ω
      let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω).xBarMem
      let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω).yBarMem
      let hz : z ∈ setup.X := by
        simpa [z] using setup.outerCenter_mem ℓ ω
      (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ
          (fun i =>
            ‖(setup.ambientFixedInnerProcess (setup.outerSampleOffset (ℓ.1 - 1))
                z z xMem0 yMem0 hz hz setup.s ω).xMem i -
              (setup.ambientFixedInnerProcess (setup.outerSampleOffset (ℓ.1 - 1))
                z z xMem0 yMem0 hz hz setup.s ω).x‖ ^ 2) := by
  classical
  have hIcc : ℓ.1 ∈ Finset.Icc 1 (setup.k : ℕ) := by
    simpa [RandomizedAcceleratedProximalPointSetup.outputWindow] using ℓ.2
  have hbounds := Finset.mem_Icc.mp hIcc
  have hidx : ℓ.1 - 1 + 1 = ℓ.1 := Nat.sub_add_cancel hbounds.1
  have hsucc : ℓ.1 - 1 + 1 ≤ (setup.k : ℕ) := by
    simpa [hidx] using hbounds.2
  have hcenter :
      setup.outerCenter ℓ.1 ω = setup.xBarIter (ℓ.1 - 1) ω :=
    outerCenter_eq_xBarIter_pred setup ℓ ω
  have hproc := setup.ambientProcess_succ (ℓ.1 - 1) hsucc ω
  have hprocℓ :
      setup.ambientProcess ℓ.1 ω =
        let prev := setup.ambientProcess (ℓ.1 - 1) ω
        let hprev :=
          setup.eq_6_6_13_ambientProcess_mem (ℓ.1 - 1)
            (Nat.le_of_succ_le hsucc) ω
        let innerRec :=
          setup.ambientFixedInnerProcess (setup.outerSampleOffset (ℓ.1 - 1))
            prev.xBar prev.xBar prev.xBarMem prev.yBarMem hprev hprev
        let final := innerRec setup.s ω
        { inner := fun t => innerRec t ω
          xBar := final.x
          xBarMem := final.xMem
          yBarMem := fun i =>
            final.yMem i + (2 * setup.μ) • (prev.xBar - final.x) } := by
    simpa [hidx] using hproc
  have hxmem :
      (setup.ambientProcess ℓ.1 ω).xBarMem =
        (setup.ambientFixedInnerProcess (setup.outerSampleOffset (ℓ.1 - 1))
          (setup.outerCenter ℓ.1 ω) (setup.outerCenter ℓ.1 ω)
          (setup.ambientProcess (ℓ.1 - 1) ω).xBarMem
          (setup.ambientProcess (ℓ.1 - 1) ω).yBarMem
          (by simpa using setup.outerCenter_mem ℓ ω)
          (by simpa using setup.outerCenter_mem ℓ ω) setup.s ω).xMem := by
    simpa [RandomizedAcceleratedProximalPointSetup.xBarIter, hcenter] using
      congrArg RapGradOuterState.xBarMem hprocℓ
  have hxbar :
      setup.xBarIter ℓ.1 ω =
        (setup.ambientFixedInnerProcess (setup.outerSampleOffset (ℓ.1 - 1))
          (setup.outerCenter ℓ.1 ω) (setup.outerCenter ℓ.1 ω)
          (setup.ambientProcess (ℓ.1 - 1) ω).xBarMem
          (setup.ambientProcess (ℓ.1 - 1) ω).yBarMem
          (by simpa using setup.outerCenter_mem ℓ ω)
          (by simpa using setup.outerCenter_mem ℓ ω) setup.s ω).x := by
    simpa [RandomizedAcceleratedProximalPointSetup.xBarIter, hcenter] using
      congrArg RapGradOuterState.xBar hprocℓ
  simp [RandomizedAcceleratedProximalPointSetup.outerMemoryDispersionIntegrand,
    hxmem, hxbar]

/-- Aligns with Lan Theorem 6.16's exact inner-loop length after Eq. (6.6.16).
Considered the compiled Part001 candidate `ceil_log_alpha_schedule_pow_le_inv`;
it is the exact negative-log ceiling bridge, but the repaired Part004 import path
cannot resolve it directly. -/
theorem ceil_log_alpha_schedule_pow_le_inv
    {α B : ℝ} {s : ℕ}
    (hα0 : 0 < α) (hα1 : α < 1) (hB : 0 < B)
    (hs : s = Nat.ceil (-Real.log B / Real.log α)) :
    α ^ s ≤ B⁻¹ := by
  let x : ℝ := -Real.log B / Real.log α
  have hlogα_neg : Real.log α < 0 := (Real.log_neg_iff hα0).mpr hα1
  have hlogα_ne : Real.log α ≠ 0 := ne_of_lt hlogα_neg
  have hx_le_s : x ≤ (s : ℝ) := by
    rw [hs]
    exact Nat.le_ceil x
  have hmul :
      (s : ℝ) * Real.log α ≤ x * Real.log α := by
    simpa [mul_comm] using
      (mul_le_mul_of_nonpos_right hx_le_s (le_of_lt hlogα_neg))
  have hmul' : (s : ℝ) * Real.log α ≤ -Real.log B := by
    calc
      (s : ℝ) * Real.log α ≤ x * Real.log α := hmul
      _ = -Real.log B := by
        simp [x, hlogα_ne]
  have hexp : Real.exp ((s : ℝ) * Real.log α) ≤ Real.exp (-Real.log B) :=
    Real.exp_le_exp.mpr hmul'
  calc
    α ^ s = α ^ ((s : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
    _ = Real.exp (Real.log α * (s : ℝ)) := by
      rw [Real.rpow_def_of_pos hα0]
    _ = Real.exp ((s : ℝ) * Real.log α) := by
      ring_nf
    _ ≤ Real.exp (-Real.log B) := hexp
    _ = B⁻¹ := by
      rw [Real.exp_neg, Real.exp_log hB]

/-- Aligns with Lan Theorem 6.16's stationarity branch.  Considered the compiled
Part001 candidate `selectedStationarity_le_scaled_selectedPreviousProxDisplacement`;
it is the exact selected-output bridge used here under the nested Part001
namespace. -/
theorem selectedStationarity_le_scaled_selectedPreviousProxDisplacement
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω) :
    setup.selectedStationarity ≤
      (3 * setup.μ) ^ 2 * setup.selectedPreviousProxDisplacement := by
  exact
    _root_.RandomizedAcceleratedProximalPointSetup.RandomizedAcceleratedProximalPoint.selectedStationarity_le_scaled_selectedPreviousProxDisplacement
      setup

/-- Aligns with Lan Theorem 6.16's output-proximity branch.  Considered the
compiled Part001 candidate `selectedCurrentProxDisplacement_eq_selectedOutputProximity`;
it is the exact observable identity, but is not visible after dropping the broken
Part003 import. -/
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

/-- Aligns with Lan Theorem 6.16 after Eq. (6.6.45).  Considered the compiled
Part001 candidate `theorem_6_16_stationarity_scalar_absorb`; it is the exact
rational scalar absorption used downstream, but is not visible on the repaired
import path. -/
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

/-- Aligns with Lan Theorem 6.16 after Eq. (6.6.45).  Considered the compiled
Part001 candidate `theorem_6_16_proximity_scalar_absorb`; it is the exact
output-proximity scalar absorption, but is not visible on the repaired import
path. -/
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

/-- Joint law of the strict outer prefix and the generated fresh inner block.

Aligns with Lan Lemma 6.14, Eqs. (6.6.38)-(6.6.39): the first
`(ℓ - 1) * s` generated samples are independent of the terminal inner block
starting at `outerSampleOffset (ℓ - 1)`, and that terminal block has the same
law as the offset-0 fixed inner block. Considered SOptLib
`iIndepFun.indepFun_finset_subtype_blocks`, Mathlib
`indepFun_iff_map_prod_eq_prod_map_map`, and target-file
`ambientFixedSamplePrefix_identDistrib`; together these exactly supply the
subtype-block independence, product-law characterization, and offset law
replacement, so this helper only performs the concrete `Fin`-vector
specialization needed by Lan Eq. (6.6.38). -/
theorem outer_prefix_offset_block_joint_law
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (ℓ : setup.OutputIndex) :
    Measure.map
        (fun ω : Ω =>
          ((fun r : Fin ((ℓ.1 - 1) * setup.s) => setup.ξ r.1 ω),
            setup.ambientFixedSamplePrefix
              (setup.outerSampleOffset (ℓ.1 - 1)) setup.s ω)) setup.P =
      (Measure.map
          (fun ω : Ω => fun r : Fin ((ℓ.1 - 1) * setup.s) =>
            setup.ξ r.1 ω) setup.P).prod
        (Measure.map (setup.ambientFixedSamplePrefix 0 setup.s) setup.P) := by
  classical
  letI : IsProbabilityMeasure setup.P := setup.hP
  exact map_pair_eq_prod_map_of_indepFun_of_map_eq
    (P := setup.P)
    (pref := fun ω : Ω => fun r : Fin ((ℓ.1 - 1) * setup.s) => setup.ξ r.1 ω)
    (blockOff := setup.ambientFixedSamplePrefix
      (setup.outerSampleOffset (ℓ.1 - 1)) setup.s)
    (block0 := setup.ambientFixedSamplePrefix 0 setup.s)
    (by
      refine (measurable_pi_lambda _ ?_).aemeasurable
      intro r
      exact setup.hξ_measurable r.1)
    (by
      refine (measurable_pi_lambda _ ?_).aemeasurable
      intro r
      exact setup.hξ_measurable (setup.outerSampleOffset (ℓ.1 - 1) + r.1))
    (setup.outer_prefix_offset_block_indep ℓ)
    ((setup.ambientFixedSamplePrefix_identDistrib
      (setup.outerSampleOffset (ℓ.1 - 1)) 0 setup.s).map_eq)

/-- A finite-valued random variable with the same law as `X` is a.e. supported
on the actual range of `X`.

This is the support bridge for Lan Lemma 6.14, Eqs. (6.6.38)-(6.6.39), where
the generated fresh block has the same finite-vector law as the offset-0 fixed
block. Considered SOptLib `measure_preimage_singleton_eq_of_map_eq`,
`aestronglyMeasurable_map_of_measurable_on_ae_support`, Mathlib
`Measure.map_apply`, and `MeasureTheory.ae_iff`; the singleton lemma is too
pointwise and the support-measurability lemma assumes the support fact, so this
helper packages the exact finite-range support consequence of map equality. -/
theorem ae_mem_range_of_map_eq_finite
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β]
    {μ : Measure α} [IsProbabilityMeasure μ] {X Y : α → β}
    (hfin : (Set.range X).Finite)
    (hX : Measurable X) (hY : Measurable Y)
    (hmap : Measure.map Y μ = Measure.map X μ) :
    ∀ᵐ a ∂μ, Y a ∈ Set.range X := by
  have _hX := hX
  exact ae_mem_range_of_map_eq_of_finite_range hfin hY.aemeasurable hmap

/-- Scalar finite-prefix/fresh-block integral transport for Lemma 6.14.

Aligns with Lan Lemma 6.14, Eqs. (6.6.38)-(6.6.39): after freezing the strict
outer prefix, integrating an arbitrary real terminal kernel over an offset-0
fresh block is the same as evaluating it on the generated fresh block. Considered
SOptLib `integral_comp_eq_integral_of_map_eq`, Mathlib `MeasureTheory.integral_map`
and `MeasureTheory.integral_prod`, and target-local `outer_prefix_offset_block_joint_law`;
the latter is the exact product-law supplier, while this helper packages the
finite-kernel Fubini/map bookkeeping needed by both terminal observables. -/
theorem outer_prefix_offset_block_integral_transport_real
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (ℓ : setup.OutputIndex)
    (Φ : (Fin ((ℓ.1 - 1) * setup.s) → ι) → (Fin setup.s → ι) → ℝ) :
    (∫ ω₀ : Ω,
        ∫ ω₁ : Ω,
          Φ (fun r : Fin ((ℓ.1 - 1) * setup.s) => setup.ξ r.1 ω₀)
            (setup.ambientFixedSamplePrefix 0 setup.s ω₁) ∂setup.P ∂setup.P) =
      ∫ ω : Ω,
        Φ (fun r : Fin ((ℓ.1 - 1) * setup.s) => setup.ξ r.1 ω)
          (setup.ambientFixedSamplePrefix
            (setup.outerSampleOffset (ℓ.1 - 1)) setup.s ω) ∂setup.P := by
  classical
  letI : IsProbabilityMeasure setup.P := setup.hP
  have hpref_meas :
      Measurable (fun ω : Ω =>
        fun r : Fin ((ℓ.1 - 1) * setup.s) => setup.ξ r.1 ω) := by
    refine measurable_pi_lambda _ ?_
    intro r
    exact setup.hξ_measurable r.1
  have hblock0_meas : Measurable (setup.ambientFixedSamplePrefix 0 setup.s) := by
    refine measurable_pi_lambda _ ?_
    intro r
    simpa [RandomizedAcceleratedProximalPointSetup.ambientFixedSamplePrefix]
      using setup.hξ_measurable r.1
  have hblockOff_meas :
      Measurable
        (setup.ambientFixedSamplePrefix (setup.outerSampleOffset (ℓ.1 - 1)) setup.s) := by
    refine measurable_pi_lambda _ ?_
    intro r
    simpa [RandomizedAcceleratedProximalPointSetup.ambientFixedSamplePrefix]
      using setup.hξ_measurable (setup.outerSampleOffset (ℓ.1 - 1) + r.1)
  refine integral_prefix_fresh_block_eq_generated_of_joint_law
    (P := setup.P)
    (pref := fun ω : Ω => fun r : Fin ((ℓ.1 - 1) * setup.s) => setup.ξ r.1 ω)
    (block0 := setup.ambientFixedSamplePrefix 0 setup.s)
    (blockOff :=
      setup.ambientFixedSamplePrefix (setup.outerSampleOffset (ℓ.1 - 1)) setup.s)
    hpref_meas.aemeasurable hblock0_meas.aemeasurable hblockOff_meas.aemeasurable ?_ Φ ?_
  · simpa using outer_prefix_offset_block_joint_law setup ℓ
  · exact Integrable.of_finite

/-- Pointwise factorization of the terminal distance through strict prefix and
fresh fixed-run block.

Aligns with Lan Lemma 6.14, Eq. (6.6.38): the terminal distance observable is
unchanged when both the previous outer-prefix parameters and the inner sample
block are unchanged. Considered `outer_terminal_params_prevPrefix_const`,
`ambientFixedInnerProcess_prefix_const`, and
`ambientFixedInnerProcess_eq_of_samplePrefix_eq_offsets`; the cross-offset
variant is required because the generated terminal block starts at
`outerSampleOffset (ℓ.1 - 1)` rather than offset `0`. -/
theorem outer_terminal_distance_prefix_block_const
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (ℓ : setup.OutputIndex)
    (offset offset' : ℕ)
    (ωp ωp' ωb ωb' : Ω)
    (hprefix :
      (fun r : Fin ((ℓ.1 - 1) * setup.s) => setup.ξ r.1 ωp) =
        (fun r : Fin ((ℓ.1 - 1) * setup.s) => setup.ξ r.1 ωp'))
    (hblock :
      setup.ambientFixedSamplePrefix offset setup.s ωb =
        setup.ambientFixedSamplePrefix offset' setup.s ωb') :
    (let z : E := setup.outerCenter ℓ.1 ωp
     let xStar : E := setup.subproblemOptOutput ℓ ωp
     let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ωp).xBarMem
     let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ωp).yBarMem
     let hz : z ∈ setup.X := by
       simpa [z] using setup.outerCenter_mem ℓ ωp
     ‖xStar -
       (setup.ambientFixedInnerProcess offset z z xMem0 yMem0 hz hz setup.s ωb).x‖ ^ 2) =
      (let z : E := setup.outerCenter ℓ.1 ωp'
       let xStar : E := setup.subproblemOptOutput ℓ ωp'
       let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ωp').xBarMem
       let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ωp').yBarMem
       let hz : z ∈ setup.X := by
         simpa [z] using setup.outerCenter_mem ℓ ωp'
       ‖xStar -
         (setup.ambientFixedInnerProcess offset' z z xMem0 yMem0 hz hz setup.s ωb').x‖ ^ 2) := by
  classical
  let z : E := setup.outerCenter ℓ.1 ωp
  let z' : E := setup.outerCenter ℓ.1 ωp'
  let xStar : E := setup.subproblemOptOutput ℓ ωp
  let xStar' : E := setup.subproblemOptOutput ℓ ωp'
  let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ωp).xBarMem
  let xMem0' : ι → E := (setup.ambientProcess (ℓ.1 - 1) ωp').xBarMem
  let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ωp).yBarMem
  let yMem0' : ι → E := (setup.ambientProcess (ℓ.1 - 1) ωp').yBarMem
  let hz : z ∈ setup.X := by
    simpa [z] using setup.outerCenter_mem ℓ ωp
  have hparams := outer_terminal_params_prevPrefix_const setup ℓ hprefix
  have hz_eq : z = z' := by
    simpa [z, z'] using hparams.1
  have hxStar_eq : xStar = xStar' := by
    simpa [xStar, xStar'] using hparams.2.1
  have hxMem_eq : xMem0 = xMem0' := by
    simpa [xMem0, xMem0'] using hparams.2.2.1
  have hyMem_eq : yMem0 = yMem0' := by
    simpa [yMem0, yMem0'] using hparams.2.2.2
  have hstate :
      setup.ambientFixedInnerProcess offset z z xMem0 yMem0 hz hz setup.s ωb =
        setup.ambientFixedInnerProcess offset' z z xMem0 yMem0 hz hz setup.s ωb' :=
    setup.ambientFixedInnerProcess_eq_of_samplePrefix_eq_offsets
      offset offset' z z xMem0 yMem0 hz hz setup.s le_rfl hblock
  have hstate_x :
      (setup.ambientFixedInnerProcess offset z' z' xMem0' yMem0'
          (by simpa [z'] using setup.outerCenter_mem ℓ ωp')
          (by simpa [z'] using setup.outerCenter_mem ℓ ωp') setup.s ωb).x =
        (setup.ambientFixedInnerProcess offset' z' z' xMem0' yMem0'
          (by simpa [z'] using setup.outerCenter_mem ℓ ωp')
          (by simpa [z'] using setup.outerCenter_mem ℓ ωp') setup.s ωb').x := by
    simpa [z, z', xMem0, xMem0', yMem0, yMem0',
      hz_eq, hxMem_eq, hyMem_eq] using congrArg RaGradState.x hstate
  simpa [z, z', xStar, xStar', xMem0, xMem0', yMem0, yMem0',
    hz_eq, hxStar_eq, hxMem_eq, hyMem_eq, hstate_x]

/-- Pointwise factorization of the terminal memory dispersion through strict
prefix and fresh fixed-run block.

Aligns with Lan Lemma 6.14, Eq. (6.6.39): the terminal memory-dispersion
observable is unchanged when both the previous outer-prefix parameters and the
inner sample block are unchanged. Considered the distance analogue
`outer_terminal_distance_prefix_block_const`, `outer_terminal_params_prevPrefix_const`,
and `ambientFixedInnerProcess_eq_of_samplePrefix_eq_offsets`; the same
cross-offset state equality transports both the terminal `x` and `xMem` fields. -/
theorem outer_terminal_memory_prefix_block_const
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (ℓ : setup.OutputIndex)
    (offset offset' : ℕ)
    (ωp ωp' ωb ωb' : Ω)
    (hprefix :
      (fun r : Fin ((ℓ.1 - 1) * setup.s) => setup.ξ r.1 ωp) =
        (fun r : Fin ((ℓ.1 - 1) * setup.s) => setup.ξ r.1 ωp'))
    (hblock :
      setup.ambientFixedSamplePrefix offset setup.s ωb =
        setup.ambientFixedSamplePrefix offset' setup.s ωb') :
    (let z : E := setup.outerCenter ℓ.1 ωp
     let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ωp).xBarMem
     let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ωp).yBarMem
     let hz : z ∈ setup.X := by
       simpa [z] using setup.outerCenter_mem ℓ ωp
     (Fintype.card ι : ℝ)⁻¹ *
       Finset.sum Finset.univ
        (fun i =>
          ‖(setup.ambientFixedInnerProcess offset z z xMem0 yMem0 hz hz setup.s ωb).xMem i -
            (setup.ambientFixedInnerProcess offset z z xMem0 yMem0 hz hz setup.s ωb).x‖ ^ 2)) =
      (let z : E := setup.outerCenter ℓ.1 ωp'
       let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ωp').xBarMem
       let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ωp').yBarMem
       let hz : z ∈ setup.X := by
         simpa [z] using setup.outerCenter_mem ℓ ωp'
       (Fintype.card ι : ℝ)⁻¹ *
         Finset.sum Finset.univ
          (fun i =>
            ‖(setup.ambientFixedInnerProcess offset' z z xMem0 yMem0 hz hz setup.s ωb').xMem i -
              (setup.ambientFixedInnerProcess offset' z z xMem0 yMem0 hz hz setup.s ωb').x‖ ^ 2)) := by
  classical
  let z : E := setup.outerCenter ℓ.1 ωp
  let z' : E := setup.outerCenter ℓ.1 ωp'
  let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ωp).xBarMem
  let xMem0' : ι → E := (setup.ambientProcess (ℓ.1 - 1) ωp').xBarMem
  let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ωp).yBarMem
  let yMem0' : ι → E := (setup.ambientProcess (ℓ.1 - 1) ωp').yBarMem
  let hz : z ∈ setup.X := by
    simpa [z] using setup.outerCenter_mem ℓ ωp
  have hparams := outer_terminal_params_prevPrefix_const setup ℓ hprefix
  have hz_eq : z = z' := by
    simpa [z, z'] using hparams.1
  have hxMem_eq : xMem0 = xMem0' := by
    simpa [xMem0, xMem0'] using hparams.2.2.1
  have hyMem_eq : yMem0 = yMem0' := by
    simpa [yMem0, yMem0'] using hparams.2.2.2
  have hstate :
      setup.ambientFixedInnerProcess offset z z xMem0 yMem0 hz hz setup.s ωb =
        setup.ambientFixedInnerProcess offset' z z xMem0 yMem0 hz hz setup.s ωb' :=
    setup.ambientFixedInnerProcess_eq_of_samplePrefix_eq_offsets
      offset offset' z z xMem0 yMem0 hz hz setup.s le_rfl hblock
  have hstate' :
      setup.ambientFixedInnerProcess offset z' z' xMem0' yMem0'
          (by simpa [z'] using setup.outerCenter_mem ℓ ωp')
          (by simpa [z'] using setup.outerCenter_mem ℓ ωp') setup.s ωb =
        setup.ambientFixedInnerProcess offset' z' z' xMem0' yMem0'
          (by simpa [z'] using setup.outerCenter_mem ℓ ωp')
          (by simpa [z'] using setup.outerCenter_mem ℓ ωp') setup.s ωb' := by
    simpa [z, z', xMem0, xMem0', yMem0, yMem0',
      hz_eq, hxMem_eq, hyMem_eq] using hstate
  simpa [z, z', xMem0, xMem0', yMem0, yMem0',
    hz_eq, hxMem_eq, hyMem_eq, hstate']

/-- Terminal-distance transport for Lemma 6.14's Theorem 6.17 application.

This is the product-law bridge behind Lan Lemma 6.14, Eq. (6.6.38): the fixed
Theorem 6.17 terminal expectation over the fresh inner block has the same
integral as the generated current outer displacement at block offset
`outerSampleOffset (ℓ.1 - 1)`. Considered SOptLib candidates
`iIndepFun.indepFun_finset_subtype_blocks`,
`iIndepFun.indep_prefixFiltration_future`, `integral_comp_eq_integral_of_map_eq`,
and `IdentDistrib.integral_comp_eq_of_measurable`; they provide the finite-block
independence and map-integral ingredients, but no existing declaration packages
this paper-specific terminal observable and Algorithm 6.8 successor rewrite. -/
theorem outer_theorem617_terminal_distance_transport
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (ℓ : setup.OutputIndex) :
    (∫ ω₀ : Ω,
        let z : E := setup.outerCenter ℓ.1 ω₀
        let xStar : E := setup.subproblemOptOutput ℓ ω₀
        let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).xBarMem
        let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).yBarMem
        let hz : z ∈ setup.X := by
          simpa [z] using setup.outerCenter_mem ℓ ω₀
        setup.expectation
          (setup.ambientFixedDistanceToOptAnyMemObservable
            z z xMem0 yMem0 hz hz setup.s le_rfl xStar) ∂setup.P) =
      ∫ ω : Ω, setup.selectedCurrentProxDisplacementIntegrand ℓ ω ∂setup.P := by
  classical
  have hgenerated_offset :
      (∫ ω : Ω, setup.selectedCurrentProxDisplacementIntegrand ℓ ω ∂setup.P) =
        ∫ ω : Ω,
          (let z : E := setup.outerCenter ℓ.1 ω
           let xStar : E := setup.subproblemOptOutput ℓ ω
           let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω).xBarMem
           let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω).yBarMem
           let hz : z ∈ setup.X := by
             simpa [z] using setup.outerCenter_mem ℓ ω
           ‖xStar -
             (setup.ambientFixedInnerProcess (setup.outerSampleOffset (ℓ.1 - 1))
               z z xMem0 yMem0 hz hz setup.s ω).x‖ ^ 2) ∂setup.P := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall
      (fun ω => selectedCurrentProxDisplacementIntegrand_eq_offset_terminal setup ℓ ω)
  rw [hgenerated_offset]
  -- Remaining proof obligation: finite-block law transport from the offset-0
  -- fixed inner expectation to the generated block at
  -- `outerSampleOffset (ℓ.1 - 1)`, with the strict outer prefix fixed by the
  -- first `(ℓ.1 - 1) * s` samples and the fresh inner block supplied by
  -- `setup.hξ_iIndep` and `setup.hξ_uniform`.
  letI : IsProbabilityMeasure setup.P := setup.hP
  let N : ℕ := (ℓ.1 - 1) * setup.s
  let prefixVec : Ω → (Fin N → ι) := fun ω r => setup.ξ r.1 ω
  let block0 : Ω → (Fin setup.s → ι) := setup.ambientFixedSamplePrefix 0 setup.s
  let blockOff : Ω → (Fin setup.s → ι) :=
    setup.ambientFixedSamplePrefix (setup.outerSampleOffset (ℓ.1 - 1)) setup.s
  let rawDist : ℕ → Ω → Ω → ℝ := fun offset ωp ωb =>
    let z : E := setup.outerCenter ℓ.1 ωp
    let xStar : E := setup.subproblemOptOutput ℓ ωp
    let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ωp).xBarMem
    let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ωp).yBarMem
    let hz : z ∈ setup.X := by
      simpa [z] using setup.outerCenter_mem ℓ ωp
    ‖xStar -
      (setup.ambientFixedInnerProcess offset z z xMem0 yMem0 hz hz setup.s ωb).x‖ ^ 2
  let Φdist : (Fin N → ι) → (Fin setup.s → ι) → ℝ := fun p b =>
    if hp : p ∈ Set.range prefixVec then
      if hb : b ∈ Set.range block0 then
        rawDist 0 (Classical.choose hp) (Classical.choose hb)
      else 0
    else 0
  have hblock0_meas : Measurable block0 := by
    refine measurable_pi_lambda _ ?_
    intro r
    simpa [block0, RandomizedAcceleratedProximalPointSetup.ambientFixedSamplePrefix]
      using setup.hξ_measurable r.1
  have hblockOff_meas : Measurable blockOff := by
    refine measurable_pi_lambda _ ?_
    intro r
    simpa [blockOff, RandomizedAcceleratedProximalPointSetup.ambientFixedSamplePrefix]
      using setup.hξ_measurable (setup.outerSampleOffset (ℓ.1 - 1) + r.1)
  have hblock_eq : Measure.map blockOff setup.P = Measure.map block0 setup.P := by
    simpa [blockOff, block0] using
      (setup.ambientFixedSamplePrefix_identDistrib
        (setup.outerSampleOffset (ℓ.1 - 1)) 0 setup.s).map_eq
  have hblock_ae : ∀ᵐ ω ∂setup.P, blockOff ω ∈ Set.range block0 := by
    exact ae_mem_range_of_map_eq_finite
      (μ := setup.P) (X := block0) (Y := blockOff)
      (Set.toFinite (Set.range block0)) hblock0_meas hblockOff_meas hblock_eq
  have hleft_eval :
      ∀ ω₀ ω₁ : Ω, Φdist (prefixVec ω₀) (block0 ω₁) = rawDist 0 ω₀ ω₁ := by
    intro ω₀ ω₁
    have hblock : block0 ω₁ ∈ Set.range block0 := ⟨ω₁, rfl⟩
    have hconst :
        ∀ ⦃ωp' ωp : Ω⦄ ⦃ωb' : Ω⦄ ⦃ωb : Ω⦄,
          prefixVec ωp' = prefixVec ωp →
            block0 ωb' = block0 ωb →
              rawDist 0 ωp' ωb' = rawDist 0 ωp ωb := by
      intro ωp' ωp ωb' ωb hp hb
      simpa [rawDist] using
        outer_terminal_distance_prefix_block_const setup ℓ 0 0
          ωp' ωp ωb' ωb hp hb
    simp only [Φdist]
    by_cases hp : prefixVec ω₀ ∈ Set.range prefixVec
    · rw [dif_pos hp]
      by_cases hb : block0 ω₁ ∈ Set.range block0
      · rw [dif_pos hb]
        exact hconst (Classical.choose_spec hp) (Classical.choose_spec hb)
      · exact False.elim (hb hblock)
    · exact False.elim (hp ⟨ω₀, rfl⟩)
  have hright_eval :
      ∀ᵐ ω ∂setup.P,
        Φdist (prefixVec ω) (blockOff ω) =
          rawDist (setup.outerSampleOffset (ℓ.1 - 1)) ω ω := by
    filter_upwards [hblock_ae] with ω hb
    have hconst :
        ∀ ⦃ωp' ωp : Ω⦄ ⦃ωb' : Ω⦄ ⦃ωb : Ω⦄,
          prefixVec ωp' = prefixVec ωp →
            block0 ωb' = blockOff ωb →
              rawDist 0 ωp' ωb' =
                rawDist (setup.outerSampleOffset (ℓ.1 - 1)) ωp ωb := by
      intro ωp' ωp ωb' ωb hp hb
      simpa [rawDist] using
        outer_terminal_distance_prefix_block_const setup ℓ 0
          (setup.outerSampleOffset (ℓ.1 - 1)) ωp' ωp ωb' ωb hp hb
    simp only [Φdist]
    by_cases hp : prefixVec ω ∈ Set.range prefixVec
    · rw [dif_pos hp]
      by_cases hblock : blockOff ω ∈ Set.range block0
      · rw [dif_pos hblock]
        exact hconst (Classical.choose_spec hp) (Classical.choose_spec hblock)
      · exact False.elim (hblock hb)
    · exact False.elim (hp ⟨ω, rfl⟩)
  have htransport := outer_prefix_offset_block_integral_transport_real setup ℓ Φdist
  calc
    (∫ ω₀ : Ω,
        let z : E := setup.outerCenter ℓ.1 ω₀
        let xStar : E := setup.subproblemOptOutput ℓ ω₀
        let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).xBarMem
        let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).yBarMem
        let hz : z ∈ setup.X := by
          simpa [z] using setup.outerCenter_mem ℓ ω₀
        setup.expectation
          (setup.ambientFixedDistanceToOptAnyMemObservable
            z z xMem0 yMem0 hz hz setup.s le_rfl xStar) ∂setup.P)
        = ∫ ω₀ : Ω, ∫ ω₁ : Ω, rawDist 0 ω₀ ω₁ ∂setup.P ∂setup.P := by
            apply integral_congr_ae
            refine Filter.Eventually.of_forall ?_
            intro ω₀
            simp [RandomizedAcceleratedProximalPointSetup.expectation,
              RandomizedAcceleratedProximalPointSetup.ambientFixedDistanceToOptAnyMemObservable,
              RandomizedAcceleratedProximalPointSetup.ambientFixedXAnyMem, rawDist]
    _ = ∫ ω₀ : Ω, ∫ ω₁ : Ω, Φdist (prefixVec ω₀) (block0 ω₁) ∂setup.P ∂setup.P := by
            apply integral_congr_ae
            refine Filter.Eventually.of_forall ?_
            intro ω₀
            apply integral_congr_ae
            exact Filter.Eventually.of_forall (fun ω₁ => (hleft_eval ω₀ ω₁).symm)
    _ = ∫ ω : Ω, Φdist (prefixVec ω) (blockOff ω) ∂setup.P := by
            simpa [prefixVec, block0, blockOff, N] using htransport
    _ = ∫ ω : Ω, rawDist (setup.outerSampleOffset (ℓ.1 - 1)) ω ω ∂setup.P := by
            apply integral_congr_ae
            exact hright_eval
    _ = ∫ ω : Ω,
          (let z : E := setup.outerCenter ℓ.1 ω
           let xStar : E := setup.subproblemOptOutput ℓ ω
           let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω).xBarMem
           let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω).yBarMem
           let hz : z ∈ setup.X := by
             simpa [z] using setup.outerCenter_mem ℓ ω
           ‖xStar -
             (setup.ambientFixedInnerProcess (setup.outerSampleOffset (ℓ.1 - 1))
               z z xMem0 yMem0 hz hz setup.s ω).x‖ ^ 2) ∂setup.P := by
            rfl

/-- Terminal-memory transport for Lemma 6.14's Theorem 6.17 application.

This is the product-law bridge behind Lan Lemma 6.14, Eq. (6.6.39), with the
same finite-block law proof as the distance transport and the terminal observable
changed to component-memory dispersion. Considered SOptLib candidates
`iIndepFun.indepFun_finset_subtype_blocks`,
`iIndepFun.indep_sampleBlock_singleton_of_not_mem`,
`integral_comp_eq_integral_of_map_eq`, and
`IdentDistrib.integral_comp_eq_of_measurable`; none states the paper-specific
Algorithm 6.8 terminal memory observable, so this local bridge isolates that
missing specialization. -/
theorem outer_theorem617_terminal_memory_dispersion_transport
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (ℓ : setup.OutputIndex) :
    (∫ ω₀ : Ω,
        let z : E := setup.outerCenter ℓ.1 ω₀
        let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).xBarMem
        let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).yBarMem
        let hz : z ∈ setup.X := by
          simpa [z] using setup.outerCenter_mem ℓ ω₀
        setup.expectation
          (setup.ambientFixedMemoryDispersionAnyMemObservable
            z z xMem0 yMem0 hz hz setup.s le_rfl) ∂setup.P) =
      ∫ ω : Ω, setup.outerMemoryDispersionIntegrand ℓ.1 ω ∂setup.P := by
  classical
  have hgenerated_offset :
      (∫ ω : Ω, setup.outerMemoryDispersionIntegrand ℓ.1 ω ∂setup.P) =
        ∫ ω : Ω,
          (let z : E := setup.outerCenter ℓ.1 ω
           let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω).xBarMem
           let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω).yBarMem
           let hz : z ∈ setup.X := by
             simpa [z] using setup.outerCenter_mem ℓ ω
           (Fintype.card ι : ℝ)⁻¹ *
             Finset.sum Finset.univ
               (fun i =>
                 ‖(setup.ambientFixedInnerProcess (setup.outerSampleOffset (ℓ.1 - 1))
                     z z xMem0 yMem0 hz hz setup.s ω).xMem i -
                   (setup.ambientFixedInnerProcess (setup.outerSampleOffset (ℓ.1 - 1))
                     z z xMem0 yMem0 hz hz setup.s ω).x‖ ^ 2)) ∂setup.P := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall
      (fun ω => outerMemoryDispersionIntegrand_eq_offset_terminal setup ℓ ω)
  rw [hgenerated_offset]
  -- Remaining proof obligation: the same finite-block law transport as the
  -- distance helper, for the terminal component-memory observable.
  letI : IsProbabilityMeasure setup.P := setup.hP
  let N : ℕ := (ℓ.1 - 1) * setup.s
  let prefixVec : Ω → (Fin N → ι) := fun ω r => setup.ξ r.1 ω
  let block0 : Ω → (Fin setup.s → ι) := setup.ambientFixedSamplePrefix 0 setup.s
  let blockOff : Ω → (Fin setup.s → ι) :=
    setup.ambientFixedSamplePrefix (setup.outerSampleOffset (ℓ.1 - 1)) setup.s
  let rawMem : ℕ → Ω → Ω → ℝ := fun offset ωp ωb =>
    let z : E := setup.outerCenter ℓ.1 ωp
    let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ωp).xBarMem
    let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ωp).yBarMem
    let hz : z ∈ setup.X := by
      simpa [z] using setup.outerCenter_mem ℓ ωp
    (Fintype.card ι : ℝ)⁻¹ *
      Finset.sum Finset.univ
        (fun i =>
          ‖(setup.ambientFixedInnerProcess offset z z xMem0 yMem0 hz hz setup.s ωb).xMem i -
            (setup.ambientFixedInnerProcess offset z z xMem0 yMem0 hz hz setup.s ωb).x‖ ^ 2)
  let Φmem : (Fin N → ι) → (Fin setup.s → ι) → ℝ := fun p b =>
    if hp : p ∈ Set.range prefixVec then
      if hb : b ∈ Set.range block0 then
        rawMem 0 (Classical.choose hp) (Classical.choose hb)
      else 0
    else 0
  have hblock0_meas : Measurable block0 := by
    refine measurable_pi_lambda _ ?_
    intro r
    simpa [block0, RandomizedAcceleratedProximalPointSetup.ambientFixedSamplePrefix]
      using setup.hξ_measurable r.1
  have hblockOff_meas : Measurable blockOff := by
    refine measurable_pi_lambda _ ?_
    intro r
    simpa [blockOff, RandomizedAcceleratedProximalPointSetup.ambientFixedSamplePrefix]
      using setup.hξ_measurable (setup.outerSampleOffset (ℓ.1 - 1) + r.1)
  have hblock_eq : Measure.map blockOff setup.P = Measure.map block0 setup.P := by
    simpa [blockOff, block0] using
      (setup.ambientFixedSamplePrefix_identDistrib
        (setup.outerSampleOffset (ℓ.1 - 1)) 0 setup.s).map_eq
  have hblock_ae : ∀ᵐ ω ∂setup.P, blockOff ω ∈ Set.range block0 := by
    exact ae_mem_range_of_map_eq_finite
      (μ := setup.P) (X := block0) (Y := blockOff)
      (Set.toFinite (Set.range block0)) hblock0_meas hblockOff_meas hblock_eq
  have hleft_eval :
      ∀ ω₀ ω₁ : Ω, Φmem (prefixVec ω₀) (block0 ω₁) = rawMem 0 ω₀ ω₁ := by
    intro ω₀ ω₁
    have hp : prefixVec ω₀ ∈ Set.range prefixVec := ⟨ω₀, rfl⟩
    have hb : block0 ω₁ ∈ Set.range block0 := ⟨ω₁, rfl⟩
    have hconst :=
      outer_terminal_memory_prefix_block_const setup ℓ 0 0
        (Classical.choose hp) ω₀ (Classical.choose hb) ω₁
        (Classical.choose_spec hp) (Classical.choose_spec hb)
    simpa [Φmem, rawMem, hp, hb] using hconst
  have hright_eval :
      ∀ᵐ ω ∂setup.P,
        Φmem (prefixVec ω) (blockOff ω) =
          rawMem (setup.outerSampleOffset (ℓ.1 - 1)) ω ω := by
    filter_upwards [hblock_ae] with ω hb
    have hp : prefixVec ω ∈ Set.range prefixVec := ⟨ω, rfl⟩
    have hconst :=
      outer_terminal_memory_prefix_block_const setup ℓ 0
        (setup.outerSampleOffset (ℓ.1 - 1))
        (Classical.choose hp) ω (Classical.choose hb) ω
        (Classical.choose_spec hp) (Classical.choose_spec hb)
    dsimp [Φmem]
    rw [dif_pos hp, dif_pos hb]
    simpa [rawMem] using hconst
  have htransport := outer_prefix_offset_block_integral_transport_real setup ℓ Φmem
  calc
    (∫ ω₀ : Ω,
        let z : E := setup.outerCenter ℓ.1 ω₀
        let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).xBarMem
        let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).yBarMem
        let hz : z ∈ setup.X := by
          simpa [z] using setup.outerCenter_mem ℓ ω₀
        setup.expectation
          (setup.ambientFixedMemoryDispersionAnyMemObservable
            z z xMem0 yMem0 hz hz setup.s le_rfl) ∂setup.P)
        = ∫ ω₀ : Ω, ∫ ω₁ : Ω, rawMem 0 ω₀ ω₁ ∂setup.P ∂setup.P := by
            apply integral_congr_ae
            refine Filter.Eventually.of_forall ?_
            intro ω₀
            simp [RandomizedAcceleratedProximalPointSetup.expectation,
              RandomizedAcceleratedProximalPointSetup.ambientFixedMemoryDispersionAnyMemObservable,
              RandomizedAcceleratedProximalPointSetup.ambientFixedXAnyMem,
              RandomizedAcceleratedProximalPointSetup.ambientFixedXMemAnyMem, rawMem]
    _ = ∫ ω₀ : Ω, ∫ ω₁ : Ω, Φmem (prefixVec ω₀) (block0 ω₁) ∂setup.P ∂setup.P := by
            apply integral_congr_ae
            refine Filter.Eventually.of_forall ?_
            intro ω₀
            apply integral_congr_ae
            exact Filter.Eventually.of_forall (fun ω₁ => (hleft_eval ω₀ ω₁).symm)
    _ = ∫ ω : Ω, Φmem (prefixVec ω) (blockOff ω) ∂setup.P := by
            simpa [prefixVec, block0, blockOff, N] using htransport
    _ = ∫ ω : Ω, rawMem (setup.outerSampleOffset (ℓ.1 - 1)) ω ω ∂setup.P := by
            apply integral_congr_ae
            exact hright_eval
    _ = ∫ ω : Ω,
          (let z : E := setup.outerCenter ℓ.1 ω
           let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω).xBarMem
           let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω).yBarMem
           let hz : z ∈ setup.X := by
             simpa [z] using setup.outerCenter_mem ℓ ω
           (Fintype.card ι : ℝ)⁻¹ *
             Finset.sum Finset.univ
               (fun i =>
                 ‖(setup.ambientFixedInnerProcess (setup.outerSampleOffset (ℓ.1 - 1))
                     z z xMem0 yMem0 hz hz setup.s ω).xMem i -
                   (setup.ambientFixedInnerProcess (setup.outerSampleOffset (ℓ.1 - 1))
                     z z xMem0 yMem0 hz hz setup.s ω).x‖ ^ 2)) ∂setup.P := by
            rfl

/-- Per-output bridge targeted by Lemma 6.14, Eqs. (6.6.38)-(6.6.39).

The proof starts from the source route: freeze the strict outer prefix, identify
the `ℓ`-th exact proximal minimizer by `subproblemOpt_is_minimizer`, rewrite the
generated center by `outerCenter_eq_xBarIter_pred`, and instantiate
`theorem_6_17_hatSourceDomain_corrected` for that fixed subproblem once the
outer-prefix hsource+hhat invariant is available.  The remaining obligation is the
conditional/offset transport from those frozen-prefix source-domain inequalities
to the unconditional outer expectations below. -/
theorem theorem_6_17_outer_hat_offset_bridge
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (ℓ : setup.OutputIndex)
    (houter_hat : setup.outerPrefixHatSourceDomain ℓ)
    (hs : 1 ≤ setup.s)
    /- Parameter schedule: α as in Eq. 6.6.16. -/
    (hα_schedule :
      setup.α =
        1 - 2 / ((Fintype.card ι : ℝ) *
          (Real.sqrt (1 + 16 * (2 + setup.L / setup.μ) / (Fintype.card ι : ℝ)) + 1)))
    /- Inner parameters as in Eq. 6.6.17, stated only on `t = 1, ..., s`. -/
    (hαSeq_schedule : ∀ t, 1 ≤ t → t ≤ setup.s → setup.αSeq t = setup.α)
    (hγSeq_schedule : ∀ t, 1 ≤ t → t ≤ setup.s → setup.γSeq t = setup.α ^ (-(t : ℤ)))
    (hτSeq_schedule : ∀ t, 1 ≤ t → t ≤ setup.s →
      setup.τSeq t = ((Fintype.card ι : ℝ) * (1 - setup.α))⁻¹ - 1)
    (hηSeq_schedule : ∀ t, 1 ≤ t → t ≤ setup.s →
      setup.ηSeq t = setup.α * (1 - setup.α)⁻¹) :
    let M : ℝ := 6 * (5 + 2 * setup.L / setup.μ)
    (∫ ω : Ω, setup.selectedCurrentProxDisplacementIntegrand ℓ ω ∂setup.P) ≤
        (M * setup.α ^ setup.s / 6) *
          ∫ ω : Ω,
            (setup.selectedPreviousProxDisplacementIntegrand ℓ ω +
              setup.outerMemoryDispersionIntegrand (ℓ.1 - 1) ω) ∂setup.P ∧
      (∫ ω : Ω, setup.outerMemoryDispersionIntegrand ℓ.1 ω ∂setup.P) ≤
        (M * setup.α ^ setup.s) *
          ∫ ω : Ω,
            (setup.selectedPreviousProxDisplacementIntegrand ℓ ω +
              setup.outerMemoryDispersionIntegrand (ℓ.1 - 1) ω) ∂setup.P := by
  classical
  let M : ℝ := 6 * (5 + 2 * setup.L / setup.μ)
  have hIcc : ℓ.1 ∈ Finset.Icc 1 (setup.k : ℕ) := by
    simpa [RandomizedAcceleratedProximalPointSetup.outputWindow] using ℓ.2
  have hbounds := Finset.mem_Icc.mp hIcc
  have hcenter :
      ∀ ω : Ω, setup.outerCenter ℓ.1 ω = setup.xBarIter (ℓ.1 - 1) ω :=
    outerCenter_eq_xBarIter_pred setup ℓ
  have hsubproblem_min :
      ∀ ω : Ω, IsMinOn (setup.subproblemObjective ℓ.1 ω) setup.X
        (setup.subproblemOptOutput ℓ ω) := by
    intro ω
    simpa [RandomizedAcceleratedProximalPointSetup.subproblemOptOutput] using
      setup.subproblemOpt_is_minimizer ℓ.1 hIcc ω
  have hfixed_theorem_6_17_instantiated :
      ∀ ω₀ : Ω,
          let z : E := setup.outerCenter ℓ.1 ω₀
          let xStar : E := setup.subproblemOptOutput ℓ ω₀
          let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).xBarMem
          let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).yBarMem
          let hz : z ∈ setup.X := by
            simpa [z] using setup.outerCenter_mem ℓ ω₀
          let hxStar : xStar ∈ setup.X := by
            simpa [xStar] using setup.subproblemOptOutput_mem ℓ ω₀
          (setup.expectation
              (setup.ambientFixedDistanceToOptAnyMemObservable
                z z xMem0 yMem0 hz hz setup.s le_rfl xStar) ≤
            setup.α ^ setup.s *
                (1 + 2 * setup.Lhat / setup.μ) *
                setup.expectation
                  (setup.ambientFixedInitialContractionAnyMemObservable
                    z z xMem0 yMem0 hz hz xStar)) ∧
          (setup.expectation
              (setup.ambientFixedMemoryDispersionAnyMemObservable
                z z xMem0 yMem0 hz hz setup.s le_rfl) ≤
            6 * setup.α ^ setup.s *
                (1 + 2 * setup.Lhat / setup.μ) *
                setup.expectation
                  (setup.ambientFixedInitialContractionAnyMemObservable
                    z z xMem0 yMem0 hz hz xStar)) := by
    intro ω₀
    exact theorem_6_17_hatSourceDomain_corrected setup ℓ houter_hat ω₀ hs hα_schedule
      hαSeq_schedule hγSeq_schedule hτSeq_schedule hηSeq_schedule
  constructor
  ·
    let fixedDistance : Ω → ℝ := fun ω₀ =>
      let z : E := setup.outerCenter ℓ.1 ω₀
      let xStar : E := setup.subproblemOptOutput ℓ ω₀
      let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).xBarMem
      let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).yBarMem
      let hz : z ∈ setup.X := by
        simpa [z] using setup.outerCenter_mem ℓ ω₀
      setup.expectation
        (setup.ambientFixedDistanceToOptAnyMemObservable
          z z xMem0 yMem0 hz hz setup.s le_rfl xStar)
    let fixedInitial : Ω → ℝ := fun ω₀ =>
      let z : E := setup.outerCenter ℓ.1 ω₀
      let xStar : E := setup.subproblemOptOutput ℓ ω₀
      let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).xBarMem
      let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).yBarMem
      let hz : z ∈ setup.X := by
        simpa [z] using setup.outerCenter_mem ℓ ω₀
      setup.expectation
        (setup.ambientFixedInitialContractionAnyMemObservable
          z z xMem0 yMem0 hz hz xStar)
    have hterminal :
        ∫ ω₀ : Ω, fixedDistance ω₀ ∂setup.P =
          ∫ ω : Ω, setup.selectedCurrentProxDisplacementIntegrand ℓ ω ∂setup.P := by
      simpa [fixedDistance] using outer_theorem617_terminal_distance_transport setup ℓ
    have hinit_int : Integrable fixedInitial setup.P := by
      simpa [fixedInitial] using outer_theorem617_initial_contraction_integrable setup ℓ
    have hinit_transport :
        ∫ ω₀ : Ω, fixedInitial ω₀ ∂setup.P =
          ∫ ω : Ω,
            setup.selectedPreviousProxDisplacementIntegrand ℓ ω +
              setup.outerMemoryDispersionIntegrand (ℓ.1 - 1) ω ∂setup.P := by
      simpa [fixedInitial] using outer_theorem617_initial_contraction_transport setup ℓ
    have hright_int :
        Integrable
          (fun ω₀ : Ω =>
            setup.α ^ setup.s * (1 + 2 * setup.Lhat / setup.μ) * fixedInitial ω₀)
          setup.P := by
      exact hinit_int.const_mul _
    have hnonneg : 0 ≤ᵐ[setup.P] fixedDistance := by
      refine Filter.Eventually.of_forall ?_
      intro ω₀
      dsimp [fixedDistance,
        RandomizedAcceleratedProximalPointSetup.expectation,
        RandomizedAcceleratedProximalPointSetup.ambientFixedDistanceToOptAnyMemObservable]
      exact integral_nonneg (fun _ => sq_nonneg _)
    have hpoint :
        fixedDistance ≤
          fun ω₀ : Ω =>
            setup.α ^ setup.s * (1 + 2 * setup.Lhat / setup.μ) * fixedInitial ω₀ := by
      intro ω₀
      simpa [fixedDistance, fixedInitial] using
        (hfixed_theorem_6_17_instantiated ω₀).1
    have hint :=
      MeasureTheory.integral_mono_of_nonneg hnonneg hright_int
        (Filter.Eventually.of_forall hpoint)
    rw [hterminal, (theorem617_outer_scalar_constants setup).1] at hint
    rw [MeasureTheory.integral_const_mul, hinit_transport] at hint
    simpa [M, mul_assoc, mul_left_comm, mul_comm] using hint
  ·
    let fixedMemory : Ω → ℝ := fun ω₀ =>
      let z : E := setup.outerCenter ℓ.1 ω₀
      let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).xBarMem
      let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).yBarMem
      let hz : z ∈ setup.X := by
        simpa [z] using setup.outerCenter_mem ℓ ω₀
      setup.expectation
        (setup.ambientFixedMemoryDispersionAnyMemObservable
          z z xMem0 yMem0 hz hz setup.s le_rfl)
    let fixedInitial : Ω → ℝ := fun ω₀ =>
      let z : E := setup.outerCenter ℓ.1 ω₀
      let xStar : E := setup.subproblemOptOutput ℓ ω₀
      let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).xBarMem
      let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).yBarMem
      let hz : z ∈ setup.X := by
        simpa [z] using setup.outerCenter_mem ℓ ω₀
      setup.expectation
        (setup.ambientFixedInitialContractionAnyMemObservable
          z z xMem0 yMem0 hz hz xStar)
    have hterminal :
        ∫ ω₀ : Ω, fixedMemory ω₀ ∂setup.P =
          ∫ ω : Ω, setup.outerMemoryDispersionIntegrand ℓ.1 ω ∂setup.P := by
      simpa [fixedMemory] using
        outer_theorem617_terminal_memory_dispersion_transport setup ℓ
    have hinit_int : Integrable fixedInitial setup.P := by
      simpa [fixedInitial] using outer_theorem617_initial_contraction_integrable setup ℓ
    have hinit_transport :
        ∫ ω₀ : Ω, fixedInitial ω₀ ∂setup.P =
          ∫ ω : Ω,
            setup.selectedPreviousProxDisplacementIntegrand ℓ ω +
              setup.outerMemoryDispersionIntegrand (ℓ.1 - 1) ω ∂setup.P := by
      simpa [fixedInitial] using outer_theorem617_initial_contraction_transport setup ℓ
    have hright_int :
        Integrable
          (fun ω₀ : Ω =>
            6 * setup.α ^ setup.s *
              (1 + 2 * setup.Lhat / setup.μ) * fixedInitial ω₀)
          setup.P := by
      exact hinit_int.const_mul _
    have hnonneg : 0 ≤ᵐ[setup.P] fixedMemory := by
      refine Filter.Eventually.of_forall ?_
      intro ω₀
      dsimp [fixedMemory,
        RandomizedAcceleratedProximalPointSetup.expectation,
        RandomizedAcceleratedProximalPointSetup.ambientFixedMemoryDispersionAnyMemObservable]
      exact integral_nonneg (fun _ => by positivity)
    have hpoint :
        fixedMemory ≤
          fun ω₀ : Ω =>
            6 * setup.α ^ setup.s *
              (1 + 2 * setup.Lhat / setup.μ) * fixedInitial ω₀ := by
      intro ω₀
      simpa [fixedMemory, fixedInitial] using
        (hfixed_theorem_6_17_instantiated ω₀).2
    have hint :=
      MeasureTheory.integral_mono_of_nonneg hnonneg hright_int
        (Filter.Eventually.of_forall hpoint)
    rw [hterminal, (theorem617_outer_scalar_constants setup).2] at hint
    rw [MeasureTheory.integral_const_mul, hinit_transport] at hint
    simpa [M, mul_assoc, mul_left_comm, mul_comm] using hint

/-- Lemma 6.14's printed inner-loop lower bound implies the scalar contraction
`M * α^s ≤ 6 / 7`.

Aligns with Lan Lemma 6.14's use of `s ≥ ⌈-log(7M/6)/log α⌉` before
Eq. (6.6.40).  Considered the local `ceil_log_alpha_schedule_pow_le_inv`,
`alpha_schedule_bounds_for_theorem_6_16`, Mathlib `pow_le_pow_of_le_one`, and
SOptLib positive-log ceiling helpers; the local negative-log bridge plus Mathlib
power monotonicity are the matching primitives for the paper's literal schedule. -/
theorem lemma_6_14_q_le_six_sevenths
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (hs_lower :
      setup.s ≥
        Nat.ceil
          (-Real.log (7 * (6 * (5 + 2 * setup.L / setup.μ)) / 6) /
            Real.log setup.α))
    (hα_schedule :
      setup.α =
        1 - 2 / ((Fintype.card ι : ℝ) *
          (Real.sqrt (1 + 16 * (2 + setup.L / setup.μ) / (Fintype.card ι : ℝ)) + 1))) :
    (6 * (5 + 2 * setup.L / setup.μ)) * setup.α ^ setup.s ≤ 6 / 7 := by
  classical
  rcases alpha_schedule_bounds_for_theorem_6_16 setup hα_schedule with
    ⟨hα_pos, hα_lt_one, _hlog_neg⟩
  let M : ℝ := 6 * (5 + 2 * setup.L / setup.μ)
  let B : ℝ := 7 * M / 6
  have hterm_nonneg : 0 ≤ 2 * setup.L / setup.μ := by
    exact div_nonneg (mul_nonneg (by norm_num) (le_of_lt setup.L_pos))
      (le_of_lt setup.hμ_pos)
  have hinside_pos : 0 < 5 + 2 * setup.L / setup.μ := by
    linarith
  have hM_pos : 0 < M := by
    dsimp [M]
    exact mul_pos (by norm_num) hinside_pos
  have hB_pos : 0 < B := by
    dsimp [B]
    exact div_pos (mul_pos (by norm_num) hM_pos) (by norm_num)
  have hs_lower_M :
      Nat.ceil (-Real.log B / Real.log setup.α) ≤ setup.s := by
    simpa [M, B, ge_iff_le] using hs_lower
  have hpow_mono :
      setup.α ^ setup.s ≤ setup.α ^ Nat.ceil (-Real.log B / Real.log setup.α) :=
    pow_le_pow_of_le_one (le_of_lt hα_pos) (le_of_lt hα_lt_one) hs_lower_M
  have hpow_ceil :
      setup.α ^ Nat.ceil (-Real.log B / Real.log setup.α) ≤ B⁻¹ :=
    ceil_log_alpha_schedule_pow_le_inv hα_pos hα_lt_one hB_pos rfl
  have hpow : setup.α ^ setup.s ≤ B⁻¹ := le_trans hpow_mono hpow_ceil
  calc
    (6 * (5 + 2 * setup.L / setup.μ)) * setup.α ^ setup.s = M * setup.α ^ setup.s := by
      rfl
    _ ≤ M * B⁻¹ := mul_le_mul_of_nonneg_left hpow (le_of_lt hM_pos)
    _ = 6 / 7 := by
      dsimp [B]
      field_simp [ne_of_gt hM_pos]

/-- Formal scalar obstruction for the printed Lemma 6.14 boundary.

The non-strict consequence `q ≤ 6 / 7` permits the endpoint `q = 6 / 7`,
where the displayed denominator core `6 - 7q` is zero.  This is the
statement-correction artifact for the guarded Lemma 6.14 boundary below; it
shows that the printed non-strict schedule cannot by itself supply the strict
positivity needed by the displayed divisions. -/
theorem lemma_6_14_printed_q_bound_allows_zero_denominator :
    ((6 / 7 : ℝ) ≤ 6 / 7) ∧
      6 - 7 * (6 / 7 : ℝ) = 0 ∧
      ¬ 0 < 6 - 7 * (6 / 7 : ℝ) := by
  norm_num

/-- The exact scalar correction used by the guarded Lemma 6.14 boundary. -/
theorem lemma_6_14_strict_q_bound_iff_denominator_pos {q : ℝ} :
    q < 6 / 7 ↔ 0 < 6 - 7 * q := by
  constructor <;> intro h <;> nlinarith

/-- The printed non-strict scalar boundary cannot imply the strict denominator
positivity needed by the displayed Lemma 6.14 estimates. -/
theorem lemma_6_14_non_strict_q_bound_not_strict_denominator :
    ¬ (∀ q : ℝ, q ≤ 6 / 7 → 0 < 6 - 7 * q) := by
  intro h
  have hbad : 0 < 6 - 7 * (6 / 7 : ℝ) := h (6 / 7) (by norm_num)
  norm_num at hbad

/-- Algorithm 6.8 initializes the outer component memory with zero dispersion.

Aligns with Lemma 6.14's boundary term before Eq. (6.6.40).  Considered
`ambientProcess_zero`, `outerMemoryDispersionIntegrand`, and existing fixed-run
memory-dispersion transports; the initialization theorem is the matching primitive,
because this helper is only the generated outer-memory base case at time `0`. -/
theorem outer_memory_dispersion_integral_zero
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω) :
    (∫ ω : Ω, setup.outerMemoryDispersionIntegrand 0 ω ∂setup.P) = 0 := by
  have hpoint : setup.outerMemoryDispersionIntegrand 0 = fun _ : Ω => 0 := by
    funext ω
    simp [RandomizedAcceleratedProximalPointSetup.outerMemoryDispersionIntegrand,
      RandomizedAcceleratedProximalPointSetup.xBarIter, setup.ambientProcess_zero ω]
  rw [hpoint]
  simp

/-- Eq. (6.6.40)'s finite-window recurrence absorption.

Aligns with Lan Lemma 6.14, Eq. (6.6.40): summing the per-output current
displacement recurrence and the generated-memory recurrence, using the zero
initial memory boundary, gives the common factor `q / (6 * (1 - q))`.  Considered
SOptLib candidates `finite_window_weighted_recurrence_telescope_with_tail_sums`,
`sum_Icc_sub_succ`, `sum_range_sub_succ_le_first_of_last_nonneg`,
`outputWindow_sum_sub_succ_le_first_of_last_nonneg`, and
`summed_one_step_gap_bound_of_telescope`; the closed-interval telescope
`sum_Icc_sub_succ` matches the boundary comparison, while the other candidates
package weighted descent or selected-output forms rather than this literal
two-recurrence memory absorption. -/
theorem lemma_6_14_eq_6_6_40_sum_current_bound
    (A C B : ℕ → ℝ) (k : ℕ) (q : ℝ)
    (hk : 1 ≤ k)
    (hq_nonneg : 0 ≤ q)
    (hq_lt_one : q < 1)
    (hB0 : B 0 = 0)
    (hB_terminal_nonneg : 0 ≤ B k)
    (hC_step : ∀ n ∈ Finset.Icc 1 k,
      C n ≤ (q / 6) * (A n + B (n - 1)))
    (hB_step : ∀ n ∈ Finset.Icc 1 k,
      B n ≤ q * (A n + B (n - 1))) :
    Finset.sum (Finset.Icc 1 k) C ≤
      q / (6 * (1 - q)) * Finset.sum (Finset.Icc 1 k) A := by
  have hB_boundary : B 0 ≤ B k := by
    simpa [hB0] using hB_terminal_nonneg
  have h :=
    sum_le_div_one_sub_of_lagged_aux_recurrence
      A C B k (q / 6) q hk (by positivity) hq_lt_one
      hB_boundary hC_step hB_step
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

/-- Eq. (6.6.8) expanded in the form used by Lemma 6.14, Eq. (6.6.41).

For a paper output index, the generated proximal subproblem objective is the
finite-sum objective plus the combined quadratic
`(3μ/2)‖x - x̄^{ℓ-1}‖²`.  Considered target-file candidates
`subproblemObjectiveOn_eq_of_outerCenter_eq`, `subproblemObjective_of_mem`, and
the SOptLib telescope/selected-output candidates
`integral_sum_telescope_bound_of_pointwise_lower_bound`,
`finiteWindowSelectedOutputExpectation_eq_weighted_sum`, and
`outputWindow_sum_sub_succ`; those either transport equal centers, aggregate an
already-packaged telescope, or model selected-output expectations, while this
bridge is the literal source-domain Eq. (6.6.8) expansion needed before applying
subproblem optimality in Eq. (6.6.41). -/
theorem lemma_6_14_subproblemObjective_eq_avg_add_three_mu_half_sq
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (ℓ : setup.OutputIndex) (ω : Ω) (x : {x : E // x ∈ setup.X}) :
    setup.subproblemObjectiveOn ℓ.1 ω x =
      (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) x +
        (3 * setup.μ / 2) * ‖x.1 - setup.xBarIter (ℓ.1 - 1) ω‖ ^ 2 := by
  classical
  have hcard_ne : ((Fintype.card ι : ℝ) ≠ 0) := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
  have hcenter :
      setup.outerCenter ℓ.1 ω = setup.xBarIter (ℓ.1 - 1) ω :=
    outerCenter_eq_xBarIter_pred setup ℓ ω
  simp [RandomizedAcceleratedProximalPointSetup.subproblemObjectiveOn,
    RandomizedAcceleratedProximalPointSetup.psiOn,
    RandomizedAcceleratedProximalPointSetup.psiAtOn,
    RandomizedAcceleratedProximalPointSetup.phi,
    RandomizedAcceleratedProximalPointSetup.phiAt,
    hcenter, Finset.sum_add_distrib, Finset.sum_const, hcard_ne]
  field_simp [hcard_ne]
  ring

/-- One-index optimality comparison in the expanded Eq. (6.6.41) form.

This is the direct local consequence of `subproblemOptOn_is_minimizer` after
rewriting the source-domain subproblem objective with
`lemma_6_14_subproblemObjective_eq_avg_add_three_mu_half_sq`.  The reusable
SOptLib telescope lemmas were considered, but they start after these per-index
subproblem-optimality inequalities have already been established. -/
theorem lemma_6_14_subproblem_optimality_expanded
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (ℓ : setup.OutputIndex) (ω : Ω) (y : {x : E // x ∈ setup.X}) :
    (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x))
          ⟨setup.subproblemOptOutput ℓ ω, setup.subproblemOptOutput_mem ℓ ω⟩ +
        (3 * setup.μ / 2) *
          setup.selectedPreviousProxDisplacementIntegrand ℓ ω ≤
      (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) y +
        (3 * setup.μ / 2) *
          ‖y.1 - setup.xBarIter (ℓ.1 - 1) ω‖ ^ 2 := by
  classical
  have hIcc : ℓ.1 ∈ Finset.Icc 1 (setup.k : ℕ) := by
    simpa [RandomizedAcceleratedProximalPointSetup.outputWindow] using ℓ.2
  have hmin := setup.subproblemOptOn_is_minimizer ℓ.1 hIcc ω
  have hle :
      setup.subproblemObjectiveOn ℓ.1 ω (setup.subproblemOptOn ℓ.1 hIcc ω) ≤
        setup.subproblemObjectiveOn ℓ.1 ω y := by
    exact hmin (a := y) (by simp)
  have hleft :
      setup.subproblemObjectiveOn ℓ.1 ω (setup.subproblemOptOn ℓ.1 hIcc ω) =
        (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x))
            ⟨setup.subproblemOptOutput ℓ ω, setup.subproblemOptOutput_mem ℓ ω⟩ +
          (3 * setup.μ / 2) *
            setup.selectedPreviousProxDisplacementIntegrand ℓ ω := by
    simpa [RandomizedAcceleratedProximalPointSetup.subproblemOptOutput,
      RandomizedAcceleratedProximalPointSetup.subproblemOpt,
      RandomizedAcceleratedProximalPointSetup.selectedPreviousProxDisplacementIntegrand]
      using
        lemma_6_14_subproblemObjective_eq_avg_add_three_mu_half_sq setup ℓ ω
          (setup.subproblemOptOn ℓ.1 hIcc ω)
  have hright :
      setup.subproblemObjectiveOn ℓ.1 ω y =
        (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) y +
          (3 * setup.μ / 2) *
            ‖y.1 - setup.xBarIter (ℓ.1 - 1) ω‖ ^ 2 :=
    lemma_6_14_subproblemObjective_eq_avg_add_three_mu_half_sq setup ℓ ω y
  calc
    (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x))
          ⟨setup.subproblemOptOutput ℓ ω, setup.subproblemOptOutput_mem ℓ ω⟩ +
        (3 * setup.μ / 2) *
          setup.selectedPreviousProxDisplacementIntegrand ℓ ω
        = setup.subproblemObjectiveOn ℓ.1 ω
            (setup.subproblemOptOn ℓ.1 hIcc ω) := hleft.symm
    _ ≤ setup.subproblemObjectiveOn ℓ.1 ω y := hle
    _ = (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) y +
        (3 * setup.μ / 2) *
          ‖y.1 - setup.xBarIter (ℓ.1 - 1) ω‖ ^ 2 := hright

/-- Pure finite telescope form of Lemma 6.14, Eq. (6.6.42).

This helper isolates the algebra after the per-index subproblem optimality
comparisons have been rewritten as
`F n + c A n ≤ F (n-1) + c C (n-1)`.  The SOptLib candidate
`integral_sum_telescope_bound_of_pointwise_lower_bound` was considered, but it
integrates an already-packaged objective-drop telescope and does not include the
lagged `C (n-1)` boundary/reindexing needed by Lan Eq. (6.6.42). -/
theorem lemma_6_14_finite_objective_telescope_bound
    (F A C : ℕ → ℝ) (k : ℕ) (c gap : ℝ)
    (hk : 1 ≤ k)
    (hc_nonneg : 0 ≤ c)
    (hstep : ∀ n ∈ Finset.Icc 1 k,
      F n + c * A n ≤ F (n - 1) + c * C (n - 1))
    (hC0 : C 0 = 0)
    (hC_terminal_nonneg : 0 ≤ C k)
    (hend : F 0 - F k ≤ gap) :
    c * Finset.sum (Finset.Icc 1 k) A ≤
      gap + c * Finset.sum (Finset.Icc 1 k) C := by
  exact sum_Icc_le_gap_add_sum_of_lagged_step F A C k c gap
    hk hc_nonneg hstep hC0 hC_terminal_nonneg hend

/-- Lemma 6.14, Eq. (6.6.41), first-index boundary `x₀^* = x̄⁰`.

This is the `n = 1` specialization of the expanded subproblem optimality
comparison.  It consumes the Algorithm 6.8 initialization through
`ambientProcess_zero`, not an additional setup assumption. -/
theorem lemma_6_14_first_objective_step
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (ℓ : setup.OutputIndex) (hℓ_one : ℓ.1 = 1) (ω : Ω) :
    (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x))
          ⟨setup.subproblemOptOutput ℓ ω, setup.subproblemOptOutput_mem ℓ ω⟩ +
        (3 * setup.μ / 2) *
          setup.selectedPreviousProxDisplacementIntegrand ℓ ω ≤
      (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) ⟨setup.x₀, setup.hx₀_mem⟩ := by
  classical
  have hopt :=
    lemma_6_14_subproblem_optimality_expanded setup ℓ ω
      ⟨setup.x₀, setup.hx₀_mem⟩
  have hzero :
      ‖setup.x₀ - setup.xBarIter (ℓ.1 - 1) ω‖ ^ 2 = 0 := by
    have hxbar0 : setup.xBarIter 0 ω = setup.x₀ := by
      simp [RandomizedAcceleratedProximalPointSetup.xBarIter,
        setup.ambientProcess_zero ω]
    simp [hℓ_one, hxbar0]
  have hzero' :
      ‖(⟨setup.x₀, setup.hx₀_mem⟩ : {x : E // x ∈ setup.X}).1 -
          setup.xBarIter (ℓ.1 - 1) ω‖ ^ 2 = 0 := by
    simpa using hzero
  rw [hzero'] at hopt
  simpa using hopt

/-- Lemma 6.14, Eq. (6.6.41), successor-index comparison against the previous
exact proximal optimizer.

This packages the non-boundary step before summing: comparing the `ℓ`-th
subproblem minimizer with the previous exact minimizer produces the previous
objective value plus the current-displacement term at the predecessor index. -/
theorem lemma_6_14_successor_objective_step
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (ℓ prev : setup.OutputIndex) (hpred : ℓ.1 - 1 = prev.1) (ω : Ω) :
    (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x))
          ⟨setup.subproblemOptOutput ℓ ω, setup.subproblemOptOutput_mem ℓ ω⟩ +
        (3 * setup.μ / 2) *
          setup.selectedPreviousProxDisplacementIntegrand ℓ ω ≤
      (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x))
          ⟨setup.subproblemOptOutput prev ω, setup.subproblemOptOutput_mem prev ω⟩ +
        (3 * setup.μ / 2) *
          setup.selectedCurrentProxDisplacementIntegrand prev ω := by
  classical
  have hopt :=
    lemma_6_14_subproblem_optimality_expanded setup ℓ ω
      ⟨setup.subproblemOptOutput prev ω, setup.subproblemOptOutput_mem prev ω⟩
  have hdisp :
      ‖setup.subproblemOptOutput prev ω - setup.xBarIter (ℓ.1 - 1) ω‖ ^ 2 =
        setup.selectedCurrentProxDisplacementIntegrand prev ω := by
    simp [RandomizedAcceleratedProximalPointSetup.selectedCurrentProxDisplacementIntegrand,
      hpred]
  have hdisp' :
      ‖(⟨setup.subproblemOptOutput prev ω, setup.subproblemOptOutput_mem prev ω⟩ :
          {x : E // x ∈ setup.X}).1 - setup.xBarIter (ℓ.1 - 1) ω‖ ^ 2 =
        setup.selectedCurrentProxDisplacementIntegrand prev ω := by
    simpa using hdisp
  rw [hdisp'] at hopt
  simpa using hopt

/-- Pointwise Icc-form objective telescope for Lemma 6.14, Eq. (6.6.42).

This consumes the source-facing ingredients for Eqs. (6.6.41)-(6.6.42):
subproblem optimality through the expanded first/successor step helpers, the
`x₀^* = x̄⁰` convention, finite objective telescoping, lagged-current
reindexing, and global optimality of `xOpt` at the terminal exact minimizer.
The result is pointwise, so no integrability of the terminal finite average is needed. -/
theorem lemma_6_14_objective_telescope_pointwise_Icc
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (xOpt : E) (hxOpt_mem : xOpt ∈ setup.X)
    (h_global_opt :
      ∀ z : {x : E // x ∈ setup.X},
        (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) ⟨xOpt, hxOpt_mem⟩ ≤ (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) z)
    (ω : Ω) :
    let c : ℝ := 3 * setup.μ / 2
    let gap : ℝ :=
      (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) ⟨setup.x₀, setup.hx₀_mem⟩ -
        (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) ⟨xOpt, hxOpt_mem⟩
    c * Finset.sum (Finset.Icc 1 (setup.k : ℕ))
        (fun n =>
          if hn : n ∈ setup.outputWindow then
            setup.selectedPreviousProxDisplacementIntegrand ⟨n, hn⟩ ω
          else 0) ≤
      gap + c * Finset.sum (Finset.Icc 1 (setup.k : ℕ))
        (fun n =>
          if hn : n ∈ setup.outputWindow then
            setup.selectedCurrentProxDisplacementIntegrand ⟨n, hn⟩ ω
          else 0) := by
  classical
  let c : ℝ := 3 * setup.μ / 2
  let gap : ℝ :=
    (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) ⟨setup.x₀, setup.hx₀_mem⟩ -
      (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) ⟨xOpt, hxOpt_mem⟩
  let F : ℕ → ℝ := fun n =>
    if hzero : n = 0 then
      (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) ⟨setup.x₀, setup.hx₀_mem⟩
    else if hn : n ∈ setup.outputWindow then
      (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x))
        ⟨setup.subproblemOptOutput ⟨n, hn⟩ ω,
          setup.subproblemOptOutput_mem ⟨n, hn⟩ ω⟩
    else
      (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) ⟨setup.x₀, setup.hx₀_mem⟩
  let A : ℕ → ℝ := fun n =>
    if hn : n ∈ setup.outputWindow then
      setup.selectedPreviousProxDisplacementIntegrand ⟨n, hn⟩ ω
    else 0
  let C : ℕ → ℝ := fun n =>
    if hn : n ∈ setup.outputWindow then
      setup.selectedCurrentProxDisplacementIntegrand ⟨n, hn⟩ ω
    else 0
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    nlinarith [setup.hμ_pos]
  have hstep : ∀ n ∈ Finset.Icc 1 (setup.k : ℕ),
      F n + c * A n ≤ F (n - 1) + c * C (n - 1) := by
    intro n hn
    have hnOut : n ∈ setup.outputWindow := by
      simpa [RandomizedAcceleratedProximalPointSetup.outputWindow] using hn
    have hn_bounds := Finset.mem_Icc.mp hn
    have hn_ne_zero : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn_bounds.1)
    by_cases hfirst : n = 1
    · let ℓ : setup.OutputIndex := ⟨n, hnOut⟩
      have hfirst_step := lemma_6_14_first_objective_step setup ℓ (by simpa [ℓ] using hfirst) ω
      have hpred_zero : n - 1 = 0 := by omega
      have hzero_not_out : (0 : ℕ) ∉ setup.outputWindow := by
        simp [RandomizedAcceleratedProximalPointSetup.outputWindow]
      have honeOut : (1 : ℕ) ∈ setup.outputWindow := by
        simpa [hfirst] using hnOut
      simpa [F, A, C, c, ℓ, hnOut, honeOut, hn_ne_zero, hpred_zero, hzero_not_out,
        hfirst] using hfirst_step
    · have hpredOut : n - 1 ∈ setup.outputWindow := by
        have hpred_lower : 1 ≤ n - 1 := by omega
        have hpred_upper : n - 1 ≤ (setup.k : ℕ) :=
          le_trans (Nat.sub_le n 1) hn_bounds.2
        rw [RandomizedAcceleratedProximalPointSetup.outputWindow]
        exact Finset.mem_Icc.mpr ⟨hpred_lower, hpred_upper⟩
      let ℓ : setup.OutputIndex := ⟨n, hnOut⟩
      let prev : setup.OutputIndex := ⟨n - 1, hpredOut⟩
      have hsucc_step :=
        lemma_6_14_successor_objective_step setup ℓ prev (by rfl) ω
      have hpred_ne_zero : n - 1 ≠ 0 := by omega
      simpa [F, A, C, c, ℓ, prev, hnOut, hpredOut, hn_ne_zero, hpred_ne_zero]
        using hsucc_step
  have hC0 : C 0 = 0 := by
    simp [C, RandomizedAcceleratedProximalPointSetup.outputWindow]
  have hkOut : ((setup.k : ℕ) : ℕ) ∈ setup.outputWindow := by
    rw [RandomizedAcceleratedProximalPointSetup.outputWindow]
    exact Finset.mem_Icc.mpr ⟨setup.k.pos, le_rfl⟩
  have hC_terminal_nonneg : 0 ≤ C (setup.k : ℕ) := by
    dsimp [C]
    simp [hkOut, RandomizedAcceleratedProximalPointSetup.selectedCurrentProxDisplacementIntegrand]
  have hend : F 0 - F (setup.k : ℕ) ≤ gap := by
    let ℓk : setup.OutputIndex := ⟨(setup.k : ℕ), hkOut⟩
    have hk_ne_zero : ((setup.k : ℕ) : ℕ) ≠ 0 := Nat.ne_of_gt setup.k.pos
    have htail :
        (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) ⟨xOpt, hxOpt_mem⟩ ≤
          (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x))
            ⟨setup.subproblemOptOutput ℓk ω, setup.subproblemOptOutput_mem ℓk ω⟩ :=
      h_global_opt
        ⟨setup.subproblemOptOutput ℓk ω, setup.subproblemOptOutput_mem ℓk ω⟩
    dsimp [F, gap, ℓk]
    simp [hk_ne_zero, hkOut]
    nlinarith
  have hfinite :=
    lemma_6_14_finite_objective_telescope_bound F A C (setup.k : ℕ) c gap
      setup.k.pos hc_nonneg hstep hC0 hC_terminal_nonneg hend
  simpa [A, C, c, gap] using hfinite

/-- Pointwise output-window form of the Lemma 6.14 objective telescope.

This is the attached-window restatement of
`lemma_6_14_objective_telescope_pointwise_Icc`, matching the local `A_sum` and
`C_sum` definitions used in `lemma_6_14_under_outerPrefixHatSourceDomain`. -/
theorem lemma_6_14_objective_telescope_pointwise_attach
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (xOpt : E) (hxOpt_mem : xOpt ∈ setup.X)
    (h_global_opt :
      ∀ z : {x : E // x ∈ setup.X},
        (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) ⟨xOpt, hxOpt_mem⟩ ≤ (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) z)
    (ω : Ω) :
    (3 * setup.μ / 2) *
        Finset.sum setup.outputWindow.attach
          (fun ℓ => setup.selectedPreviousProxDisplacementIntegrand ℓ ω) ≤
      ((fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) ⟨setup.x₀, setup.hx₀_mem⟩ -
          (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) ⟨xOpt, hxOpt_mem⟩) +
        (3 * setup.μ / 2) *
          Finset.sum setup.outputWindow.attach
            (fun ℓ => setup.selectedCurrentProxDisplacementIntegrand ℓ ω) := by
  classical
  have hIcc :=
    lemma_6_14_objective_telescope_pointwise_Icc setup xOpt hxOpt_mem h_global_opt ω
  have hA_attach :
      Finset.sum (Finset.Icc 1 (setup.k : ℕ))
          (fun n =>
            if hn : n ∈ setup.outputWindow then
              setup.selectedPreviousProxDisplacementIntegrand ⟨n, hn⟩ ω
            else 0) =
        Finset.sum setup.outputWindow.attach
          (fun ℓ => setup.selectedPreviousProxDisplacementIntegrand ℓ ω) := by
    have h :
        Finset.sum (Finset.Icc 1 (setup.k : ℕ))
            (fun n =>
              if hn : n ∈ setup.outputWindow then
                setup.selectedPreviousProxDisplacementIntegrand ⟨n, hn⟩ ω
              else 0) =
          Finset.sum (Finset.Icc 1 (setup.k : ℕ)).attach
            (fun ℓ =>
              setup.selectedPreviousProxDisplacementIntegrand
                ⟨ℓ.1, by
                  simpa [RandomizedAcceleratedProximalPointSetup.outputWindow] using ℓ.2⟩
                ω) := by
      rw [← Finset.sum_attach (s := Finset.Icc 1 (setup.k : ℕ))]
      refine Finset.sum_congr rfl ?_
      intro n hn
      simp [RandomizedAcceleratedProximalPointSetup.outputWindow, hn]
    simpa [RandomizedAcceleratedProximalPointSetup.outputWindow] using h
  have hC_attach :
      Finset.sum (Finset.Icc 1 (setup.k : ℕ))
          (fun n =>
            if hn : n ∈ setup.outputWindow then
              setup.selectedCurrentProxDisplacementIntegrand ⟨n, hn⟩ ω
            else 0) =
        Finset.sum setup.outputWindow.attach
          (fun ℓ => setup.selectedCurrentProxDisplacementIntegrand ℓ ω) := by
    have h :
        Finset.sum (Finset.Icc 1 (setup.k : ℕ))
            (fun n =>
              if hn : n ∈ setup.outputWindow then
                setup.selectedCurrentProxDisplacementIntegrand ⟨n, hn⟩ ω
              else 0) =
          Finset.sum (Finset.Icc 1 (setup.k : ℕ)).attach
            (fun ℓ =>
              setup.selectedCurrentProxDisplacementIntegrand
                ⟨ℓ.1, by
                  simpa [RandomizedAcceleratedProximalPointSetup.outputWindow] using ℓ.2⟩
                ω) := by
      rw [← Finset.sum_attach (s := Finset.Icc 1 (setup.k : ℕ))]
      refine Finset.sum_congr rfl ?_
      intro n hn
      simp [RandomizedAcceleratedProximalPointSetup.outputWindow, hn]
    simpa [RandomizedAcceleratedProximalPointSetup.outputWindow] using h
  simpa [hA_attach, hC_attach] using hIcc

/-- Scalar absorption after Lan Lemma 6.14, Eq. (6.6.42).

Given the summed current-displacement estimate (6.6.40) and the objective
telescope inequality (6.6.42), solve the two-real-variable system for the
summed previous and current proximal displacements.  Considered target-file
scalar helpers `theorem_6_16_stationarity_scalar_absorb`,
`theorem_6_16_proximity_scalar_absorb`, and SOptLib completion-square/parameter
normalization lemmas; those handle Theorem 6.16's later coefficient reductions
or unrelated Young absorptions, while this helper is the literal Lemma 6.14
`6 - 7q` summed-bound solve. -/
theorem lemma_6_14_scalar_absorption_summed_bounds
    {μ q gap A_sum C_sum : ℝ}
    (hμ_pos : 0 < μ)
    (hq_nonneg : 0 ≤ q)
    (hq_lt_one : q < 1)
    (hdenom_core_pos : 0 < 6 - 7 * q)
    (hgap_nonneg : 0 ≤ gap)
    (hEq640 : C_sum ≤ q / (6 * (1 - q)) * A_sum)
    (hObj : (3 * μ / 2) * A_sum ≤ gap + (3 * μ / 2) * C_sum) :
    A_sum ≤ 4 * (1 - q) / (μ * (6 - 7 * q)) * gap ∧
      C_sum ≤ 2 * q / (3 * μ * (6 - 7 * q)) * gap := by
  have : 0 ≤ gap := hgap_nonneg
  exact bounds_of_coupled_sum_absorption_q_six hμ_pos hq_nonneg
    hdenom_core_pos hEq640 hObj

/-! `lemma_6_14_under_outerPrefixHatSourceDomain` telescopes the outer RapGrad proximal subproblems using
`theorem_6_17_hatSourceDomain_corrected` to obtain the two subproblem-distance bounds
(Eq. 6.6.38-6.6.42).

`subproblemOptOutput ℓ` is the canonical exact minimiser of the ℓ-th proximal
subproblem for `ℓ ∈ {1, ..., k}`.
The inner-loop length `s`
uses the printed Lemma 6.14 ceiling lower bound with `M = 6(5 + 2L/μ)`;
the corrected Lean boundary also exposes the strict positivity of
`6 - 7Mα^s`, because the printed non-strict ceiling only gives
`Mα^s ≤ 6/7` while the displayed algebra divides by this denominator.
the parameter sequences are fixed by Eqs. (6.6.16)-(6.6.17), because the proof
explicitly invokes Theorem 6.17; the conclusion records the paper average over the
random outer index `l̂`.

This is intentionally not named `lemma_6_14`: it consumes the corrected ambient
Algorithm 6.8/6.9 realization, so it is a source-boundary corrected statement rather
than an unchanged A-level copy of the printed Lemma 6.14. -/
theorem lemma_6_14_under_outerPrefixHatSourceDomain
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (xOpt : E)
    (hxOpt_mem : xOpt ∈ setup.X)
    (h_global_opt : ∀ z : {x : E // x ∈ setup.X},
      (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) ⟨xOpt, hxOpt_mem⟩ ≤ (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) z)
    (houter_hat : ∀ ℓ : setup.OutputIndex, setup.outerPrefixHatSourceDomain ℓ)
    /- s ≥ ⌈-log(7M/6)/log α⌉ with M = 6(5 + 2L/μ), as printed in Lemma 6.14. -/
    (hs_lower :
      setup.s ≥
        Nat.ceil
          (-Real.log (7 * (6 * (5 + 2 * setup.L / setup.μ)) / 6) /
            Real.log setup.α))
    /- Strict denominator boundary required by the displayed Lemma 6.14 bounds.
       The printed non-strict schedule gives only `Mα^s ≤ 6/7`; Theorem 6.16's
       exact schedule later supplies this from the stronger `Mα^s ≤ 5/6`. -/
    (hq_lt_six_sevenths :
      (6 * (5 + 2 * setup.L / setup.μ)) * setup.α ^ setup.s < 6 / 7)
    /- Parameter schedule: α as in Eq. 6.6.16. -/
    (hα_schedule :
      setup.α =
        1 - 2 / ((Fintype.card ι : ℝ) *
          (Real.sqrt (1 + 16 * (2 + setup.L / setup.μ) / (Fintype.card ι : ℝ)) + 1)))
    /- Inner parameters as in Eq. 6.6.17, stated only on `t = 1, ..., s`. -/
    (hαSeq_schedule : ∀ t, 1 ≤ t → t ≤ setup.s → setup.αSeq t = setup.α)
    (hγSeq_schedule : ∀ t, 1 ≤ t → t ≤ setup.s → setup.γSeq t = setup.α ^ (-(t : ℤ)))
    (hτSeq_schedule : ∀ t, 1 ≤ t → t ≤ setup.s →
      setup.τSeq t = ((Fintype.card ι : ℝ) * (1 - setup.α))⁻¹ - 1)
    (hηSeq_schedule : ∀ t, 1 ≤ t → t ≤ setup.s →
      setup.ηSeq t = setup.α * (1 - setup.α)⁻¹) :
    let M : ℝ := 6 * (5 + 2 * setup.L / setup.μ)
    let denom : ℝ := setup.μ * (6 - 7 * M * setup.α ^ setup.s)
    (setup.selectedPreviousProxDisplacement ≤
      4 * (1 - M * setup.α ^ setup.s) / (((setup.k : ℕ) : ℝ) * denom) *
        ((fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) ⟨setup.x₀, setup.hx₀_mem⟩ - (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) ⟨xOpt, hxOpt_mem⟩)) ∧
    (setup.selectedCurrentProxDisplacement ≤
      2 * M * setup.α ^ setup.s / (3 * ((setup.k : ℕ) : ℝ) * denom) *
        ((fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) ⟨setup.x₀, setup.hx₀_mem⟩ - (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) ⟨xOpt, hxOpt_mem⟩)) := by
  classical
  have hs : 1 ≤ setup.s := by
    rcases alpha_schedule_bounds_for_theorem_6_16 setup hα_schedule with
      ⟨_hα_pos, _hα_lt_one, hlog_neg⟩
    let M : ℝ := 6 * (5 + 2 * setup.L / setup.μ)
    have hterm_nonneg : 0 ≤ 2 * setup.L / setup.μ := by
      exact div_nonneg (mul_nonneg (by norm_num) (le_of_lt setup.L_pos))
        (le_of_lt setup.hμ_pos)
    have hinside_ge : (5 : ℝ) ≤ 5 + 2 * setup.L / setup.μ := by
      linarith
    have hM_gt : 1 < 7 * M / 6 := by
      calc
        (1 : ℝ) < 7 * 5 := by norm_num
        _ ≤ 7 * (5 + 2 * setup.L / setup.μ) := by
          exact mul_le_mul_of_nonneg_left hinside_ge (by norm_num)
        _ = 7 * M / 6 := by
          dsimp [M]
          ring
    have hlog_pos : 0 < Real.log (7 * M / 6) := Real.log_pos hM_gt
    have hquot_pos :
        0 < -Real.log (7 * M / 6) / Real.log setup.α := by
      exact div_pos_of_neg_of_neg (by linarith) hlog_neg
    have hceil_pos : 0 < Nat.ceil (-Real.log (7 * M / 6) / Real.log setup.α) :=
      Nat.ceil_pos.mpr hquot_pos
    have hceil_le : 1 ≤ Nat.ceil (-Real.log (7 * M / 6) / Real.log setup.α) := by
      exact hceil_pos
    exact le_trans hceil_le (by simpa [M] using hs_lower)
  have hper_outer :
      ∀ ℓ : setup.OutputIndex,
        let M : ℝ := 6 * (5 + 2 * setup.L / setup.μ)
        (∫ ω : Ω, setup.selectedCurrentProxDisplacementIntegrand ℓ ω ∂setup.P) ≤
            (M * setup.α ^ setup.s / 6) *
              ∫ ω : Ω,
                (setup.selectedPreviousProxDisplacementIntegrand ℓ ω +
                  setup.outerMemoryDispersionIntegrand (ℓ.1 - 1) ω) ∂setup.P ∧
          (∫ ω : Ω, setup.outerMemoryDispersionIntegrand ℓ.1 ω ∂setup.P) ≤
            (M * setup.α ^ setup.s) *
              ∫ ω : Ω,
                (setup.selectedPreviousProxDisplacementIntegrand ℓ ω +
                  setup.outerMemoryDispersionIntegrand (ℓ.1 - 1) ω) ∂setup.P := by
    intro ℓ
    exact theorem_6_17_outer_hat_offset_bridge setup ℓ (houter_hat ℓ) hs hα_schedule
      hαSeq_schedule hγSeq_schedule hτSeq_schedule hηSeq_schedule
  let M : ℝ := 6 * (5 + 2 * setup.L / setup.μ)
  let q : ℝ := M * setup.α ^ setup.s
  have hq67 : q ≤ 6 / 7 := by
    simpa [q, M] using lemma_6_14_q_le_six_sevenths setup hs_lower hα_schedule
  have hq_lt67 : q < 6 / 7 := by
    simpa [q, M] using hq_lt_six_sevenths
  have hq_lt_one : q < 1 := lt_of_le_of_lt hq67 (by norm_num)
  have hdenom_core_nonneg : 0 ≤ 6 - 7 * q := by
    nlinarith
  have hdenom_core_pos : 0 < 6 - 7 * q := by
    exact (lemma_6_14_strict_q_bound_iff_denominator_pos (q := q)).mp hq_lt67
  have hB0 :
      (∫ ω : Ω, setup.outerMemoryDispersionIntegrand 0 ω ∂setup.P) = 0 :=
    outer_memory_dispersion_integral_zero setup
  have hq_nonneg : 0 ≤ q := by
    rcases alpha_schedule_bounds_for_theorem_6_16 setup hα_schedule with
      ⟨hα_pos, _hα_lt_one, _hlog_neg⟩
    have hterm_nonneg : 0 ≤ 2 * setup.L / setup.μ := by
      exact div_nonneg (mul_nonneg (by norm_num) (le_of_lt setup.L_pos))
        (le_of_lt setup.hμ_pos)
    have hinside_pos : 0 < 5 + 2 * setup.L / setup.μ := by
      linarith
    have hM_pos : 0 < M := by
      dsimp [M]
      exact mul_pos (by norm_num) hinside_pos
    exact mul_nonneg (le_of_lt hM_pos) (pow_nonneg (le_of_lt hα_pos) setup.s)
  let A : ℕ → ℝ := fun n =>
    if hn : n ∈ setup.outputWindow then
      ∫ ω : Ω,
        setup.selectedPreviousProxDisplacementIntegrand ⟨n, hn⟩ ω ∂setup.P
    else 0
  let C : ℕ → ℝ := fun n =>
    if hn : n ∈ setup.outputWindow then
      ∫ ω : Ω,
        setup.selectedCurrentProxDisplacementIntegrand ⟨n, hn⟩ ω ∂setup.P
    else 0
  let B : ℕ → ℝ := fun n =>
    ∫ ω : Ω, setup.outerMemoryDispersionIntegrand n ω ∂setup.P
  have hB_terminal_nonneg : 0 ≤ B (setup.k : ℕ) := by
    dsimp [B]
    refine integral_nonneg ?_
    intro ω
    dsimp [RandomizedAcceleratedProximalPointSetup.outerMemoryDispersionIntegrand]
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg (fun i _hi => sq_nonneg _))
  have hC_step : ∀ n ∈ Finset.Icc 1 (setup.k : ℕ),
      C n ≤ (q / 6) * (A n + B (n - 1)) := by
    intro n hn
    have hnOut : n ∈ setup.outputWindow := by
      simpa [RandomizedAcceleratedProximalPointSetup.outputWindow] using hn
    have hper := (hper_outer ⟨n, hnOut⟩).1
    have hadd :
        (∫ ω : Ω,
          (setup.selectedPreviousProxDisplacementIntegrand ⟨n, hnOut⟩ ω +
            setup.outerMemoryDispersionIntegrand (n - 1) ω) ∂setup.P) =
          (∫ ω : Ω,
            setup.selectedPreviousProxDisplacementIntegrand ⟨n, hnOut⟩ ω ∂setup.P) +
          (∫ ω : Ω, setup.outerMemoryDispersionIntegrand (n - 1) ω ∂setup.P) := by
      rw [MeasureTheory.integral_add
        (setup.selectedPreviousProxDisplacementIntegrand_integrable ⟨n, hnOut⟩)
        (setup.outerPreviousMemoryDispersionIntegrand_integrable ⟨n, hnOut⟩)]
    rw [hadd] at hper
    simpa [A, C, B, hnOut, q, M] using hper
  have hB_step : ∀ n ∈ Finset.Icc 1 (setup.k : ℕ),
      B n ≤ q * (A n + B (n - 1)) := by
    intro n hn
    have hnOut : n ∈ setup.outputWindow := by
      simpa [RandomizedAcceleratedProximalPointSetup.outputWindow] using hn
    have hper := (hper_outer ⟨n, hnOut⟩).2
    have hadd :
        (∫ ω : Ω,
          (setup.selectedPreviousProxDisplacementIntegrand ⟨n, hnOut⟩ ω +
            setup.outerMemoryDispersionIntegrand (n - 1) ω) ∂setup.P) =
          (∫ ω : Ω,
            setup.selectedPreviousProxDisplacementIntegrand ⟨n, hnOut⟩ ω ∂setup.P) +
          (∫ ω : Ω, setup.outerMemoryDispersionIntegrand (n - 1) ω ∂setup.P) := by
      rw [MeasureTheory.integral_add
        (setup.selectedPreviousProxDisplacementIntegrand_integrable ⟨n, hnOut⟩)
        (setup.outerPreviousMemoryDispersionIntegrand_integrable ⟨n, hnOut⟩)]
    rw [hadd] at hper
    simpa [A, B, hnOut, q, M] using hper
  have hEq640_Icc :
      Finset.sum (Finset.Icc 1 (setup.k : ℕ)) C ≤
        q / (6 * (1 - q)) *
          Finset.sum (Finset.Icc 1 (setup.k : ℕ)) A := by
    exact lemma_6_14_eq_6_6_40_sum_current_bound A C B (setup.k : ℕ) q
      setup.k.pos hq_nonneg hq_lt_one (by simpa [B] using hB0)
      hB_terminal_nonneg hC_step hB_step
  have hEq640 :
      Finset.sum setup.outputWindow.attach
          (fun ℓ => ∫ ω : Ω,
            setup.selectedCurrentProxDisplacementIntegrand ℓ ω ∂setup.P) ≤
        q / (6 * (1 - q)) *
          Finset.sum setup.outputWindow.attach
            (fun ℓ => ∫ ω : Ω,
              setup.selectedPreviousProxDisplacementIntegrand ℓ ω ∂setup.P) := by
    have hC_attach :
        Finset.sum (Finset.Icc 1 (setup.k : ℕ)) C =
          Finset.sum (Finset.Icc 1 (setup.k : ℕ)).attach
            (fun ℓ => ∫ ω : Ω,
              setup.selectedCurrentProxDisplacementIntegrand
                ⟨ℓ.1, by
                  simpa [RandomizedAcceleratedProximalPointSetup.outputWindow] using ℓ.2⟩
                ω ∂setup.P) := by
      rw [← Finset.sum_attach (s := Finset.Icc 1 (setup.k : ℕ))]
      refine Finset.sum_congr rfl ?_
      intro ℓ _hℓ
      simp [C, RandomizedAcceleratedProximalPointSetup.outputWindow]
    have hA_attach :
        Finset.sum (Finset.Icc 1 (setup.k : ℕ)) A =
          Finset.sum (Finset.Icc 1 (setup.k : ℕ)).attach
            (fun ℓ => ∫ ω : Ω,
              setup.selectedPreviousProxDisplacementIntegrand
                ⟨ℓ.1, by
                  simpa [RandomizedAcceleratedProximalPointSetup.outputWindow] using ℓ.2⟩
                ω ∂setup.P) := by
      rw [← Finset.sum_attach (s := Finset.Icc 1 (setup.k : ℕ))]
      refine Finset.sum_congr rfl ?_
      intro ℓ _hℓ
      simp [A, RandomizedAcceleratedProximalPointSetup.outputWindow]
    rw [hC_attach, hA_attach] at hEq640_Icc
    simpa [RandomizedAcceleratedProximalPointSetup.outputWindow] using hEq640_Icc
  let A_sum : ℝ :=
    Finset.sum setup.outputWindow.attach
      (fun ℓ => ∫ ω : Ω,
        setup.selectedPreviousProxDisplacementIntegrand ℓ ω ∂setup.P)
  let C_sum : ℝ :=
    Finset.sum setup.outputWindow.attach
      (fun ℓ => ∫ ω : Ω,
        setup.selectedCurrentProxDisplacementIntegrand ℓ ω ∂setup.P)
  let gap : ℝ :=
    (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) ⟨setup.x₀, setup.hx₀_mem⟩ -
      (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) ⟨xOpt, hxOpt_mem⟩
  have hgap_nonneg : 0 ≤ gap := by
    dsimp [gap]
    exact sub_nonneg.mpr (h_global_opt ⟨setup.x₀, setup.hx₀_mem⟩)
  have hObj :
      (3 * setup.μ / 2) * A_sum ≤ gap + (3 * setup.μ / 2) * C_sum := by
    letI : IsProbabilityMeasure setup.P := setup.hP
    let c : ℝ := 3 * setup.μ / 2
    have hpoint :
        ∀ᵐ ω ∂setup.P,
          c *
              Finset.sum setup.outputWindow.attach
                (fun ℓ => setup.selectedPreviousProxDisplacementIntegrand ℓ ω) ≤
            gap +
              c *
                Finset.sum setup.outputWindow.attach
                  (fun ℓ => setup.selectedCurrentProxDisplacementIntegrand ℓ ω) := by
      exact Filter.Eventually.of_forall fun ω => by
        simpa [c, gap] using
          lemma_6_14_objective_telescope_pointwise_attach setup xOpt hxOpt_mem
            h_global_opt ω
    simpa [A_sum, C_sum, c] using
      integral_finset_sum_le_of_pointwise_finset_sum_le
        (mu := setup.P) (s := setup.outputWindow.attach)
        (A := fun ℓ ω => setup.selectedPreviousProxDisplacementIntegrand ℓ ω)
        (C := fun ℓ ω => setup.selectedCurrentProxDisplacementIntegrand ℓ ω)
        (c := c) (gap := gap)
        (fun ℓ _hℓ => setup.selectedPreviousProxDisplacementIntegrand_integrable ℓ)
        (fun ℓ _hℓ => setup.selectedCurrentProxDisplacementIntegrand_integrable ℓ)
        hpoint
  have hSummed :
      A_sum ≤ 4 * (1 - q) / (setup.μ * (6 - 7 * q)) * gap ∧
        C_sum ≤ 2 * q / (3 * setup.μ * (6 - 7 * q)) * gap := by
    exact lemma_6_14_scalar_absorption_summed_bounds setup.hμ_pos hq_nonneg
      hq_lt_one hdenom_core_pos hgap_nonneg
      (by simpa [A_sum, C_sum] using hEq640)
      hObj
  have hk_real_pos : 0 < (((setup.k : ℕ) : ℝ)) := by
    exact_mod_cast setup.k.pos
  have hk_inv_nonneg : 0 ≤ (((setup.k : ℕ) : ℝ)⁻¹) :=
    inv_nonneg.mpr (le_of_lt hk_real_pos)
  have hprev_avg :
      setup.selectedPreviousProxDisplacement =
        (((setup.k : ℕ) : ℝ)⁻¹) * A_sum := by
    rfl
  have hcurr_avg :
      setup.selectedCurrentProxDisplacement =
        (((setup.k : ℕ) : ℝ)⁻¹) * C_sum := by
    rfl
  have hprev_bound :
      setup.selectedPreviousProxDisplacement ≤
        4 * (1 - q) /
            (((setup.k : ℕ) : ℝ) * (setup.μ * (6 - 7 * q))) * gap := by
    rw [hprev_avg]
    calc
      (((setup.k : ℕ) : ℝ)⁻¹) * A_sum ≤
          (((setup.k : ℕ) : ℝ)⁻¹) *
            (4 * (1 - q) / (setup.μ * (6 - 7 * q)) * gap) :=
        mul_le_mul_of_nonneg_left hSummed.1 hk_inv_nonneg
      _ = 4 * (1 - q) /
            (((setup.k : ℕ) : ℝ) * (setup.μ * (6 - 7 * q))) * gap := by
        field_simp [ne_of_gt hk_real_pos, ne_of_gt setup.hμ_pos,
          ne_of_gt hdenom_core_pos]
  have hcurr_bound :
      setup.selectedCurrentProxDisplacement ≤
        2 * q / (3 * ((setup.k : ℕ) : ℝ) * (setup.μ * (6 - 7 * q))) * gap := by
    rw [hcurr_avg]
    calc
      (((setup.k : ℕ) : ℝ)⁻¹) * C_sum ≤
          (((setup.k : ℕ) : ℝ)⁻¹) *
            (2 * q / (3 * setup.μ * (6 - 7 * q)) * gap) :=
        mul_le_mul_of_nonneg_left hSummed.2 hk_inv_nonneg
      _ = 2 * q / (3 * ((setup.k : ℕ) : ℝ) * (setup.μ * (6 - 7 * q))) * gap := by
        field_simp [ne_of_gt hk_real_pos, ne_of_gt setup.hμ_pos,
          ne_of_gt hdenom_core_pos]
  constructor
  · simpa [M, q, gap, mul_assoc] using hprev_bound
  · simpa [M, q, gap, mul_assoc] using hcurr_bound

/-! `theorem_6_16_under_outerPrefixHatSourceDomain` is the main convergence theorem for Algorithm 6.8.  With parameters
set as in Eq. 6.6.16-6.6.17, the randomized output `x̄^{l̂}` (a random outer iterate)
satisfies both a stationarity bound and an iterate-to-subproblem-solution proximity
bound at rate O(1/k) (Theorem 6.16).

The two bounds are:
- `E[d(∇f(x*_{l̂}), -N_X(x*_{l̂}))²] ≤ 36μ/k · (f(x̄⁰) − f(x*))` (stationarity of exact subproblem sol.)
- `E‖x̄^{l̂} − x*_{l̂}‖² ≤ 4μ/(k·L²) · (f(x̄⁰) − f(x*))` (closeness of output to exact sol.)

Here `x̄^{l̂}` is the computable RapGrad output (xBarIter at the randomly chosen outer
iterate `l̂`), and `x*_{l̂}` is the exact minimiser of the `l̂`-th proximal subproblem,
with `l̂` ranging over the paper window `[k]`.

This corrected theorem keeps the printed numerical conclusion, but the generated
iterates are supplied by the ambient-corrected process because the source does not
state the component-memory domain invariant needed for the literal source-domain
Algorithm 6.9 gradient line. -/
theorem theorem_6_16_under_outerPrefixHatSourceDomain
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (houter_hat : ∀ ℓ : setup.OutputIndex, setup.outerPrefixHatSourceDomain ℓ)
    /- Parameter schedule: α as in Eq. 6.6.16 -/
    (hα_schedule :
      setup.α =
        1 - 2 / ((Fintype.card ι : ℝ) *
          (Real.sqrt (1 + 16 * (2 + setup.L / setup.μ) / (Fintype.card ι : ℝ)) + 1)))
    /- Inner parameters as in Eq. 6.6.17. -/
    (hαSeq_schedule : ∀ t, 1 ≤ t → t ≤ setup.s → setup.αSeq t = setup.α)
    (hγSeq_schedule : ∀ t, 1 ≤ t → t ≤ setup.s → setup.γSeq t = setup.α ^ (-(t : ℤ)))
    (hτSeq_schedule : ∀ t, 1 ≤ t → t ≤ setup.s →
      setup.τSeq t = ((Fintype.card ι : ℝ) * (1 - setup.α))⁻¹ - 1)
    (hηSeq_schedule : ∀ t, 1 ≤ t → t ≤ setup.s →
      setup.ηSeq t = setup.α * (1 - setup.α)⁻¹)
    /- s as in Eq. 6.6.16: s = ⌈−log(M̃)/log(α)⌉ where M̃ = 6(5+2L/μ)·max{6/5, L²/μ²} -/
    (hs_schedule :
      setup.s =
        Nat.ceil
          (-Real.log
            (6 * (5 + 2 * setup.L / setup.μ) *
              max (6 / 5 : ℝ) ((setup.L / setup.μ) ^ 2)) /
            Real.log setup.α)) :
    /- Stationarity of exact subproblem solution x*_{l̂} -/
    (setup.selectedStationarity ≤
      36 * setup.μ / ((setup.k : ℕ) : ℝ) *
        ((fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) ⟨setup.x₀, setup.hx₀_mem⟩ -
          (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) ⟨setup.globalOpt, setup.globalOpt_mem⟩)) ∧
    /- Closeness of computable output x̄^{l̂} to exact subproblem solution x*_{l̂} -/
    (setup.selectedOutputProximity ≤
      4 * setup.μ / (((setup.k : ℕ) : ℝ) * setup.L ^ 2) *
        ((fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) ⟨setup.x₀, setup.hx₀_mem⟩ -
          (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) ⟨setup.globalOpt, setup.globalOpt_mem⟩)) := by
  classical
  let M : ℝ := 6 * (5 + 2 * setup.L / setup.μ)
  let q : ℝ := M * setup.α ^ setup.s
  let gap : ℝ :=
    (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) ⟨setup.x₀, setup.hx₀_mem⟩ -
      (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) ⟨setup.globalOpt, setup.globalOpt_mem⟩
  have hk_pos : 0 < (((setup.k : ℕ) : ℝ)) := by
    exact_mod_cast setup.k.pos
  have hgap_nonneg : 0 ≤ gap := by
    dsimp [gap]
    exact sub_nonneg.mpr
      (setup.globalOpt_is_minimizer ⟨setup.x₀, setup.hx₀_mem⟩)
  rcases theorem_6_16_schedule_bounds setup hα_schedule hs_schedule with
    ⟨hs_lower, hq56, hqL⟩
  have hq_lt_six_sevenths :
      (6 * (5 + 2 * setup.L / setup.μ)) * setup.α ^ setup.s < 6 / 7 := by
    simpa [q, M] using
      (lt_of_le_of_lt hq56 (by norm_num : (5 / 6 : ℝ) < 6 / 7))
  rcases lemma_6_14_under_outerPrefixHatSourceDomain setup setup.globalOpt setup.globalOpt_mem
      setup.globalOpt_is_minimizer houter_hat hs_lower hq_lt_six_sevenths
      hα_schedule hαSeq_schedule hγSeq_schedule hτSeq_schedule hηSeq_schedule with
    ⟨hprev, hcurr⟩
  have hstat := selectedStationarity_le_scaled_selectedPreviousProxDisplacement setup
  have hout := selectedCurrentProxDisplacement_eq_selectedOutputProximity setup
  constructor
  · calc
      setup.selectedStationarity ≤
          (3 * setup.μ) ^ 2 * setup.selectedPreviousProxDisplacement := hstat
      _ ≤
          (3 * setup.μ) ^ 2 *
            (4 * (1 - q) /
                ((((setup.k : ℕ) : ℝ)) * (setup.μ * (6 - 7 * q))) * gap) := by
          exact mul_le_mul_of_nonneg_left
            (by simpa [q, M, gap, mul_assoc] using hprev)
            (sq_nonneg (3 * setup.μ))
      _ ≤ 36 * setup.μ / (((setup.k : ℕ) : ℝ)) * gap := by
          exact theorem_6_16_stationarity_scalar_absorb setup.hμ_pos hk_pos
            hgap_nonneg (by simpa [q, M] using hq56)
      _ =
          36 * setup.μ / (((setup.k : ℕ) : ℝ)) *
            ((fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) ⟨setup.x₀, setup.hx₀_mem⟩ -
              (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) ⟨setup.globalOpt, setup.globalOpt_mem⟩) := by
          rfl
  · rw [← hout]
    calc
      setup.selectedCurrentProxDisplacement ≤
          2 * q / (3 * (((setup.k : ℕ) : ℝ)) * (setup.μ * (6 - 7 * q))) * gap := by
          simpa [q, M, gap, mul_assoc] using hcurr
      _ ≤ 4 * setup.μ / ((((setup.k : ℕ) : ℝ)) * setup.L ^ 2) * gap := by
          exact theorem_6_16_proximity_scalar_absorb setup.hμ_pos setup.L_pos
            hk_pos hgap_nonneg (by simpa [q, M] using hq56)
            (by simpa [q, M] using hqL)
      _ =
          4 * setup.μ / ((((setup.k : ℕ) : ℝ)) * setup.L ^ 2) *
            ((fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) ⟨setup.x₀, setup.hx₀_mem⟩ -
              (fun x => (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)) ⟨setup.globalOpt, setup.globalOpt_mem⟩) := by
          rfl

end RandomizedAcceleratedProximalPointSetup
