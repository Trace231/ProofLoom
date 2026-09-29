import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
import SOptLib.Layer0.ConvexFOC
import SOptLib.Model.Filtration
import SOptLib.Model.Objective
import SOptLib.Layer1.Proximal
import Algorithms.Unverified.RandomizedAcceleratedProximalPoint.Part001

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

theorem ambientFixedDelta2CurrentKernelRegularity_source_boundary
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (z x0 xStar : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) (hxStar : xStar ∈ setup.X)
    (hhat :
      setup.ambientFixedHatSourceDomain 0 z x0 xMem0 yMem0 hz hx0) :
    ambientFixedDelta2CurrentKernelRegularity
      (setup := setup) (offset := 0) (z := z) (x0 := x0)
      (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
      (hz := hz) (hx0 := hx0) (hxStar := hxStar) hhat := by
  -- Source regularity boundary for Eq. (6.6.29): represent the displayed
  -- `δ₂ᵗ` kernel by the strict finite prefix `(ξ 0, ..., ξ (n-1))`, prove
  -- measurability of that prefix, and discharge the finite-range integrability.
  classical
  intro n hn
  let Z : Ω → Fin n → ι := setup.ambientFixedSamplePrefix 0 n
  let K : Ω → ι → ℝ := fun ω j =>
    ambientFixedDelta2CurrentKernel
      (setup := setup) (offset := 0) (z := z) (x0 := x0)
      (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
      (hz := hz) (hx0 := hx0) (hxStar := hxStar)
      n hn (hhat n hn) ω j
  let delta2Current : (Fin n → ι) → ι → ℝ := fun q j =>
    if hq : q ∈ Set.range Z then K (Classical.choose hq) j else 0
  refine ⟨Z, delta2Current, ?_, ?_, ?_, ?_⟩
  · change
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
              setup.ξ setup.hξ_measurable (n := n) (i := r.1) r.2)))
  · exact measurable_of_finite
      (fun q : (Fin n → ι) × ι => delta2Current q.1 q.2)
  · intro j
    refine setup.ambientFixed_prefix_integrable_real 0 n ?_
    intro ω ω' hprefix
    have hmem : Z ω ∈ Set.range Z := ⟨ω, rfl⟩
    have hmem' : Z ω' ∈ Set.range Z := ⟨ω', rfl⟩
    have hchoose_prefix :
        Z (Classical.choose hmem) =
          Z (Classical.choose hmem') := by
      rw [Classical.choose_spec hmem, Classical.choose_spec hmem']
      simpa [Z] using hprefix
    dsimp [delta2Current]
    rw [dif_pos hmem, dif_pos hmem']
    dsimp [K]
    exact ambientFixedDelta2CurrentKernel_prefix_const
      (setup := setup) (offset := 0) (z := z) (x0 := x0)
      (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
      (hz := hz) (hx0 := hx0) (hxStar := hxStar)
      n hn (hhat n hn) j hchoose_prefix
  · intro ω j
    have hmem : Z ω ∈ Set.range Z := ⟨ω, rfl⟩
    dsimp [delta2Current]
    rw [dif_pos hmem]
    dsimp [K]
    exact ambientFixedDelta2CurrentKernel_prefix_const
      (setup := setup) (offset := 0) (z := z) (x0 := x0)
      (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
      (hz := hz) (hx0 := hx0) (hxStar := hxStar)
      n hn (hhat n hn) j (Classical.choose_spec hmem)

/-! Fixed-subproblem Eq. (6.6.30) interface for the corrected Lemma 6.13 route.

The bounded-output helper `eq_6_6_30_conditional_current_index` above packages the
generated-index Lemma 6.12 API.  Lemma 6.13 is stated for a frozen proximal
subproblem, so this interface records the two source facts available on that
boundary: the current-sample uniform averaging identity and the literal
source-domain gradient-memory update under `ambientFixedSourceDomain`. -/
theorem eq_6_6_30_ambientFixed_current_index
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (offset : ℕ) (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X)
    (hsource : setup.ambientFixedSourceDomain offset z x0 xMem0 yMem0 hz hx0)
    {W : Type*} [MeasurableSpace W]
    (sampleTime : ℕ) {Z : Ω → W}
    (hZ : Measurable[(SOptLib.filtration setup.ξ setup.hξ_measurable).seq sampleTime] Z)
    (delta2Current : W → ι → ℝ)
    (hDelta2_meas : Measurable (fun q : W × ι => delta2Current q.1 q.2))
    (hDelta2_int : ∀ j : ι, Integrable (fun ω : Ω => delta2Current (Z ω) j) setup.P) :
    ((∫ ω : Ω, delta2Current (Z ω) (setup.ξ sampleTime ω) ∂setup.P) =
      ∫ ω : Ω,
        RandomizedAcceleratedProximalPointSetup.currentIndexAverage
          (fun j : ι => delta2Current (Z ω) j) ∂setup.P) ∧
    (∀ n (hn : n + 1 ≤ setup.s) (ω : Ω) (i : ι),
      (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 (n + 1) ω).yMem i =
        if _ : i = setup.ξ (offset + ((n + 1) - 1)) ω then
          setup.gradPsiOnAt z i
            ⟨setup.xMemAfterSampleAtState (n + 1) (Nat.succ_pos n) hn
                (setup.ξ (offset + ((n + 1) - 1)) ω) i
                (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω),
              hsource n hn ω i⟩
        else
          (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω).yMem i) := by
  classical
  have hcurrent :=
    setup.current_sample_conditional_uniform_average
      sampleTime hZ delta2Current hDelta2_meas hDelta2_int
  refine ⟨hcurrent, ?_⟩
  intro n hn ω i
  exact setup.ambientFixedInnerProcess_yMem_eq_source_of_domain
    offset z x0 xMem0 yMem0 hz hx0 hsource n hn ω i

/-- Eq. (6.6.30) instantiated with the displayed fixed-run `δ₂ᵗ` kernel.

This is the source-facing supplier consumed by the corrected Lemma 6.13 route:
the generic current-index averaging API is applied only after the `δ₂ᵗ` kernel
has been represented on the strict sample prefix by
`ambientFixedDelta2CurrentKernelRegularity`. -/
theorem eq_6_6_30_ambientFixed_delta2CurrentKernel_source_route
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (z x0 xStar : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X)
    (hsource : setup.ambientFixedSourceDomain 0 z x0 xMem0 yMem0 hz hx0)
    (hhat :
      setup.ambientFixedHatSourceDomain 0 z x0 xMem0 yMem0 hz hx0)
    (hxStar : xStar ∈ setup.X)
    (hdelta2_regular :
      ambientFixedDelta2CurrentKernelRegularity
        (setup := setup) (offset := 0) (z := z) (x0 := x0)
        (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
        (hz := hz) (hx0 := hx0) (hxStar := hxStar) hhat) :
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
  classical
  intro n hn
  rcases hdelta2_regular n hn with
    ⟨Z, delta2Current, hZ, hDelta2_meas, hDelta2_int, hrepr⟩
  have h630 :=
    eq_6_6_30_ambientFixed_current_index
      (setup := setup) (offset := 0) (z := z) (x0 := x0)
      (xMem0 := xMem0) (yMem0 := yMem0)
      (hz := hz) (hx0 := hx0) hsource
      (sampleTime := n) (Z := Z)
      hZ delta2Current hDelta2_meas hDelta2_int
  refine ⟨?_, h630.2⟩
  have hleft :
      (fun ω : Ω => delta2Current (Z ω) (setup.ξ n ω)) =
        fun ω : Ω =>
          ambientFixedDelta2CurrentKernel
            (setup := setup) (offset := 0) (z := z) (x0 := x0)
            (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
            (hz := hz) (hx0 := hx0) (hxStar := hxStar)
            n hn (hhat n hn) ω (setup.ξ n ω) := by
    funext ω
    exact hrepr ω (setup.ξ n ω)
  have hright :
      (fun ω : Ω =>
          RandomizedAcceleratedProximalPointSetup.currentIndexAverage
            (fun j : ι => delta2Current (Z ω) j)) =
        fun ω : Ω =>
          RandomizedAcceleratedProximalPointSetup.currentIndexAverage
            (fun j : ι =>
              ambientFixedDelta2CurrentKernel
                (setup := setup) (offset := 0) (z := z) (x0 := x0)
                (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
                (hz := hz) (hx0 := hx0) (hxStar := hxStar)
                n hn (hhat n hn) ω j) := by
    funext ω
    unfold RandomizedAcceleratedProximalPointSetup.currentIndexAverage
    congr 1
    funext j
    exact hrepr ω j
  rw [← hleft, ← hright]
  exact h630.1

/-- Eq. (6.6.30) for the displayed fixed-run `δ₂ᵗ` summand, with the
strict-prefix regularity boundary discharged at the source boundary.

This is the coarser actual-kernel entrypoint consumed by Lemma 6.13: it exposes
only the source-domain run facts (`hsource`, `hhat`) and hides the finite-prefix
regularity expansion behind the proved source-boundary supplier above. -/
theorem eq_6_6_30_ambientFixed_delta2CurrentKernel_source_boundary_route
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (z x0 xStar : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X)
    (hsource : setup.ambientFixedSourceDomain 0 z x0 xMem0 yMem0 hz hx0)
    (hhat :
      setup.ambientFixedHatSourceDomain 0 z x0 xMem0 yMem0 hz hx0)
    (hxStar : xStar ∈ setup.X) :
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
  classical
  have hdelta2_regular :
      ambientFixedDelta2CurrentKernelRegularity
        (setup := setup) (offset := 0) (z := z) (x0 := x0)
        (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
        (hz := hz) (hx0 := hx0) (hxStar := hxStar) hhat :=
    ambientFixedDelta2CurrentKernelRegularity_source_boundary
      (setup := setup) (z := z) (x0 := x0) (xStar := xStar)
      (xMem0 := xMem0) (yMem0 := yMem0)
      (hz := hz) (hx0 := hx0) (hxStar := hxStar) hhat
  exact
    eq_6_6_30_ambientFixed_delta2CurrentKernel_source_route
      (setup := setup) (z := z) (x0 := x0) (xStar := xStar)
      (xMem0 := xMem0) (yMem0 := yMem0)
      (hz := hz) (hx0 := hx0) hsource hhat hxStar hdelta2_regular

/-- Reindex a zero-based strict-prefix subtype sum into the paper's one-based
`Icc 1 s` convention.  SOptLib's `SOptLib.sum_positiveTimeOutputWindowTimes_eq_Icc`
was considered but indexes `{t // 1 ≤ t}` without the required `n ↦ n + 1`
strict-prefix shift; the finite residual candidates in `SOptLib.Glue.Algebra`
control weighted centers rather than natural-number reindexing. -/
theorem sum_univ_subtype_lt_succ_eq_sum_Icc_one
    {α : Type*} [AddCommMonoid α] (s : ℕ) (F : ℕ → α) :
    Finset.sum Finset.univ (fun n : {n : ℕ // n < s} => F (n.1 + 1)) =
      Finset.sum (Finset.Icc 1 s) (fun t => F t) := by
  classical
  refine Finset.sum_bij (fun n _hn => n.1 + 1) ?_ ?_ ?_ ?_
  · intro n _hn
    exact Finset.mem_Icc.mpr ⟨Nat.succ_pos n.1, Nat.succ_le_of_lt n.2⟩
  · intro a _ha b _hb h
    exact Subtype.ext (Nat.succ.inj h)
  · intro t ht
    rcases Finset.mem_Icc.mp ht with ⟨ht1, hts⟩
    refine ⟨⟨t - 1, ?_⟩, Finset.mem_univ _, ?_⟩
    · have hsucc_le : (t - 1) + 1 ≤ s := by
        simpa [Nat.sub_add_cancel ht1] using hts
      exact Nat.lt_of_succ_le hsucc_le
    · exact Nat.sub_add_cancel ht1
  · intro n _hn
    rfl

/-- Proof-carrying version of `sum_univ_subtype_lt_succ_eq_sum_Icc_one`.
The same SOptLib candidates were considered as above; none carry both one-based
interval bounds needed by proof-dependent kernels such as Eq. (6.6.30)'s
current-index `δ₂` replacement. -/
theorem sum_univ_subtype_lt_succ_eq_sum_Icc_one_attach
    {α : Type*} [AddCommMonoid α] (s : ℕ)
    (F : (t : ℕ) → 1 ≤ t → t ≤ s → α) :
    Finset.sum Finset.univ
        (fun n : {n : ℕ // n < s} =>
          F (n.1 + 1) (Nat.succ_pos n.1) (Nat.succ_le_of_lt n.2)) =
      Finset.sum (Finset.Icc 1 s).attach
        (fun t =>
          F t.1 (Finset.mem_Icc.mp t.2).1 (Finset.mem_Icc.mp t.2).2) := by
  exact sum_univ_subtype_lt_succ_eq_sum_Icc_attach (s := s) (F := F)

/-- Two-coefficient finite telescope used by Lemma 6.13's Eq. (6.6.31) coefficient
bookkeeping.  SOptLib's `sum_weighted_sub_mul_le_first_sub_tail` was considered;
it packages a quotient-style single-coefficient recurrence, while the printed
Eq. (6.6.31) uses adjacent raw coefficient comparisons from (6.6.21)-(6.6.22). -/
theorem sum_Icc_two_coeff_telescope_le
    (c d V : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hV_nonneg : ∀ n, 1 ≤ n → n < k → 0 ≤ V n)
    (hmono : ∀ n, 1 ≤ n → n < k → c (n + 1) ≤ d n) :
    Finset.sum (Finset.Icc 1 k) (fun t => c t * V (t - 1) - d t * V t) ≤
      c 1 * V 0 - d k * V k := by
  exact SOptLib.sum_Icc_two_coeff_telescope_le c d V k hk hV_nonneg hmono

/-- Endpoint-half decomposition for the residual regrouping after Lan Eq. (6.6.35).
The pre-searched candidates `finset_weighted_residual_sum_eq_zero`,
`finset_weighted_variance_eq_second_moment_sub_norm_mean_sq`,
`Finset.weighted_variance_le_second_moment`, `weighted_sq_norm_sub_center_le`,
`coefficients_for_average_minus_search_eq_alpha_step_minus_center`, and
`average_sub_search_eq_alpha_smul_step_sub_weighted_center` were considered;
none matches this interval split because they control weighted centers or affine
transport, while Eq. (6.6.35) needs a natural-number `Icc 1 s` to `Icc 2 s`
endpoint decomposition with a retained first half-Bregman slack. -/
theorem sum_Icc_residual_endpoint_half_decomp
    (γ α e b c : ℕ → ℝ) (s : ℕ) (hs : 1 ≤ s) (hc1 : c 1 = 0) :
    Finset.sum (Finset.Icc 1 s) (fun t => γ t * (e t + b t)) -
        γ s * (e s + b s / 2) +
        Finset.sum (Finset.Icc 1 s) (fun t => γ t * (α t * c t)) =
      Finset.sum (Finset.Icc 2 s) (fun t =>
          γ (t - 1) * e (t - 1) +
            γ t * (b t / 2) +
            γ (t - 1) * (b (t - 1) / 2) +
            γ t * (α t * c t)) +
        γ 1 * (b 1 / 2) := by
  classical
  let P : ℕ → Prop := fun n =>
    Finset.sum (Finset.Icc 1 n) (fun t => γ t * (e t + b t)) -
        γ n * (e n + b n / 2) +
        Finset.sum (Finset.Icc 1 n) (fun t => γ t * (α t * c t)) =
      Finset.sum (Finset.Icc 2 n) (fun t =>
          γ (t - 1) * e (t - 1) +
            γ t * (b t / 2) +
            γ (t - 1) * (b (t - 1) / 2) +
            γ t * (α t * c t)) +
        γ 1 * (b 1 / 2)
  have hbase : P 1 := by
    dsimp [P]
    simp [hc1]
    ring
  have hstep : ∀ n, 1 ≤ n → P n → P (n + 1) := by
    intro n hn ih
    dsimp [P] at ih ⊢
    have h1top : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    have h2top : 2 ≤ n + 1 := by omega
    rw [Finset.sum_Icc_succ_top h1top]
    rw [Finset.sum_Icc_succ_top h1top]
    rw [Finset.sum_Icc_succ_top h2top]
    have hsucc_sub : n + 1 - 1 = n := by omega
    rw [hsucc_sub]
    nlinarith [ih]
  exact Nat.le_induction hbase hstep s hs

/-- Eta-weight telescope for the Eq. (6.6.31) `V_φ` terms.  This specializes the
two-coefficient telescope above to the source side condition (6.6.22), aligning
with Lan §6.6 Eq. (6.6.31)'s `γ_t η_t` / `γ_t(1+η_t)` cancellation. -/
theorem lemma_6_13_eta_weight_telescope
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (A : ℕ → ℝ) (hs : 1 ≤ setup.s)
    (hA_nonneg : ∀ n, 1 ≤ n → n < setup.s → 0 ≤ A n)
    (hparam22 : ∀ t, 1 ≤ t → t + 1 ≤ setup.s →
      setup.γSeq (t + 1) * setup.ηSeq (t + 1) ≤
        setup.γSeq t * (1 + setup.ηSeq t)) :
    Finset.sum (Finset.Icc 1 setup.s)
        (fun t =>
          setup.γSeq t * setup.ηSeq t * A (t - 1) -
            setup.γSeq t * (1 + setup.ηSeq t) * A t) ≤
      setup.γSeq 1 * setup.ηSeq 1 * A 0 -
        setup.γSeq setup.s * (1 + setup.ηSeq setup.s) * A setup.s := by
  classical
  simpa [mul_assoc] using
    (sum_Icc_two_coeff_telescope_le
      (fun t => setup.γSeq t * setup.ηSeq t)
      (fun t => setup.γSeq t * (1 + setup.ηSeq t))
      A setup.s hs hA_nonneg
      (fun n hn hnlt => hparam22 n hn (Nat.succ_le_of_lt hnlt)))

/-- Tau-weight telescope for the Eq. (6.6.31) component-memory terms.  The
finite residual/variance candidates in `SOptLib.Glue.Algebra` were checked but
do not encode the paper's `(m(1+τ)-1)` to `(1+τ)-1/m` coefficient conversion;
this helper specializes (6.6.21) and then applies the raw two-coefficient
telescope needed by Eq. (6.6.31). -/
theorem lemma_6_13_tau_weight_telescope
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (A : ℕ → ℝ) (hs : 1 ≤ setup.s)
    (hA_nonneg : ∀ n, 1 ≤ n → n < setup.s → 0 ≤ A n)
    (hparam21 : ∀ t, 1 ≤ t → t + 1 ≤ setup.s →
      setup.γSeq (t + 1) *
          ((Fintype.card ι : ℝ) * (1 + setup.τSeq (t + 1)) - 1) ≤
        (Fintype.card ι : ℝ) * setup.γSeq t * (1 + setup.τSeq t)) :
    Finset.sum (Finset.Icc 1 setup.s)
        (fun t =>
          setup.γSeq t * ((1 + setup.τSeq t) - (Fintype.card ι : ℝ)⁻¹) *
              A (t - 1) -
            setup.γSeq t * (1 + setup.τSeq t) * A t) ≤
      setup.γSeq 1 * ((1 + setup.τSeq 1) - (Fintype.card ι : ℝ)⁻¹) * A 0 -
        setup.γSeq setup.s * (1 + setup.τSeq setup.s) * A setup.s := by
  classical
  have hmpos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι))
  refine
    (sum_Icc_two_coeff_telescope_le
      (fun t => setup.γSeq t * ((1 + setup.τSeq t) - (Fintype.card ι : ℝ)⁻¹))
      (fun t => setup.γSeq t * (1 + setup.τSeq t))
      A setup.s hs hA_nonneg ?_)
  intro n hn hnlt
  have hraw := hparam21 n hn (Nat.succ_le_of_lt hnlt)
  have hscale :
      (Fintype.card ι : ℝ)⁻¹ *
          (setup.γSeq (n + 1) *
            ((Fintype.card ι : ℝ) * (1 + setup.τSeq (n + 1)) - 1)) ≤
        (Fintype.card ι : ℝ)⁻¹ *
          ((Fintype.card ι : ℝ) * setup.γSeq n * (1 + setup.τSeq n)) :=
    mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr (le_of_lt hmpos))
  have hleft :
      (Fintype.card ι : ℝ)⁻¹ *
          (setup.γSeq (n + 1) *
            ((Fintype.card ι : ℝ) * (1 + setup.τSeq (n + 1)) - 1)) =
        setup.γSeq (n + 1) *
          ((1 + setup.τSeq (n + 1)) - (Fintype.card ι : ℝ)⁻¹) := by
    field_simp [ne_of_gt hmpos]
  have hright :
      (Fintype.card ι : ℝ)⁻¹ *
          ((Fintype.card ι : ℝ) * setup.γSeq n * (1 + setup.τSeq n)) =
        setup.γSeq n * (1 + setup.τSeq n) := by
    field_simp [ne_of_gt hmpos]
  simpa [hleft, hright] using hscale

/-- Conclusion of the corrected source-domain Lemma 6.13 statement. -/
def lemma_6_13_sourceConclusion
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (z x0 xStar : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) (hxMem0 : ∀ i, xMem0 i ∈ setup.X) :
    Prop :=
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
            z x0 xMem0 yMem0 hz hx0 hxMem0 0 (Nat.zero_le setup.s) i xStar))

/-- First-order condition for the exact Eq. (6.6.8) subproblem objective.

Aligns with Lan Lemma 6.13, Eqs. (6.6.26)-(6.6.27): the listed SOptLib
candidate `Convex.first_order_condition_of_isMinOn_hasFDerivWithinAt` is used
directly after differentiating the literal `phiAt + card⁻¹ * ∑ psiAt`
objective with `phiAt_hasGradientAt` and `gradPsiOnAt_hasGradientWithinAt`. -/
theorem lemma_6_13_subproblem_foc_inner_sum
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (z xStar : E)
    (hxStar : xStar ∈ setup.X)
    (h_opt : ∀ u : {x : E // x ∈ setup.X},
      (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ (fun i => setup.psiAtOn z i ⟨xStar, hxStar⟩) +
        setup.phiAt z xStar ≤
      (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ (fun i => setup.psiAtOn z i u) +
        setup.phiAt z u.1) :
    ∀ y, y ∈ setup.X →
      0 ≤
        ⟪setup.gradPhiAt z xStar, y - xStar⟫_ℝ +
          (Fintype.card ι : ℝ)⁻¹ *
            Finset.sum Finset.univ
              (fun i => ⟪setup.gradPsiOnAt z i ⟨xStar, hxStar⟩, y - xStar⟫_ℝ) := by
  classical
  intro y hy
  exact
    Convex.first_order_condition_sum_add_of_isMinOn
      (X := setup.X) (x := xStar) (y := y) (phi := setup.phiAt z)
      (psi := fun i u => setup.psiAt z i u)
      (gradPhi := setup.gradPhiAt z xStar)
      (gradPsi := fun i => setup.gradPsiOnAt z i ⟨xStar, hxStar⟩)
      setup.hX_convex hxStar hy
      (by
        intro u hu
        have h := h_opt ⟨u, hu⟩
        simpa [RandomizedAcceleratedProximalPointSetup.psiAt_of_mem, hxStar, hu,
          add_comm] using h)
      (by
        exact (phiAt_hasGradientAt setup z xStar).hasFDerivAt.hasFDerivWithinAt)
      (by
        intro i
        exact setup.gradPsiOnAt_hasGradientWithinAt z i ⟨xStar, hxStar⟩)

/-- Terminal averaged Young absorption for the Eq. (6.6.35)-to-(6.6.36)
residual step.

Aligns with Lan Lemma 6.13 after Eq. (6.6.35), using the printed relation
`b⟪u,v⟫ - a‖v‖²/2 ≤ b²‖u‖²/(2a)`.  Considered
`scaled_linear_inner_quadratic_le_square_over_denominator`,
`smooth_quadratic_tail_absorption_of_bregman_and_completion_square`, and
`alpha_scaled_bregman_tail_absorption_of_weighted_bound`; they package nearby
completed-square estimates but do not match this terminal averaged coefficient
`1 / m` with the `(6.6.25)` budget split over the component sum. -/
theorem lemma_6_13_terminal_average_young_absorption
    {m L tau A : ℝ} {u v : E}
    (hm : 0 < m) (hL : 0 < L) (htau : 0 ≤ tau)
    (hA : A ≥ L / (m * (1 + tau))) :
    0 ≤ (A / m) * ‖v‖ ^ 2 - (1 / m) * ⟪u, v⟫_ℝ +
      (1 + tau) / (4 * L) * ‖u‖ ^ 2 := by
  exact young_absorb_average_inner_with_quadratic_budget hm hL htau hA

/-- Terminal sampled correction absorption for the Eq. (6.6.35) residual step.

Aligns with Lan Lemma 6.13, Eq. (6.6.35) transition (a): the terminal
`(1 - 1/m)` sampled gradient correction is absorbed by the terminal step budget
and the co-coercivity lower bound.  Considered
`finset_weighted_residual_sum_eq_zero`, `weighted_sq_norm_sub_center_le`, and
the existing `lemma_6_13_terminal_average_young_absorption`; the first two are
centering/variance facts, and the existing helper controls the averaged
`1 / m` terminal component sum rather than this sampled `(m - 1) / m` term. -/
theorem lemma_6_13_terminal_sample_correction_absorption
    {L tau A gamma c B : ℝ} {g v : E}
    (hL : 0 < L) (htau : 0 < tau) (hgamma : 0 ≤ gamma)
    (hc : 0 ≤ c) (hcoef : c ^ 2 * L / tau ≤ A)
    (hbreg : (1 / (2 * L)) * ‖g‖ ^ 2 ≤ B) :
    0 ≤ gamma * (A * ‖v‖ ^ 2 + (tau / 2) * B - c * ⟪g, v⟫_ℝ) := by
  exact _root_.young_absorb_inner_of_norm_sq_budget
    hL htau hgamma hc hcoef hbreg

/-- Interior two-correction absorption for one Eq. (6.6.35) summand.

Aligns with Lan Lemma 6.13, Eq. (6.6.35) transitions (a)-(b), after rewriting
`γ_{t-1} = α_t γ_t`: the previous step norm plus the half-current and
half-previous co-coercivity budgets absorb the two exposed correction inner
products.  Considered SOptLib's `alpha_scaled_bregman_tail_absorption_of_weighted_bound`
and the finite centering candidates in `SOptLib.Glue.Algebra`; they do not match
this source-local pair of adjacent Bregman budgets and the `(m - 1) / m`
sample-memory coefficient. -/
theorem lemma_6_13_interior_two_correction_absorption
    {L tauPrev tauCur eta alpha gammaPrev gammaCur c BPrev BCur : ℝ}
    {gCur gPrev d : E}
    (hL : 0 < L) (htauPrev : 0 < tauPrev) (htauCur : 0 < tauCur)
    (hgammaPrev : 0 ≤ gammaPrev) (hgammaCur : 0 ≤ gammaCur)
    (halpha : 0 ≤ alpha) (hc : 0 ≤ c)
    (hshift : gammaPrev = alpha * gammaCur)
    (hcoef : 0 ≤ gammaPrev *
      (eta - alpha * L / tauCur - c ^ 2 * L / tauPrev))
    (hbcur : (1 / (2 * L)) * ‖gCur‖ ^ 2 ≤ BCur)
    (hbprev : (1 / (2 * L)) * ‖gPrev‖ ^ 2 ≤ BPrev) :
    0 ≤
      gammaPrev * (eta * ‖d‖ ^ 2) +
        gammaCur * ((tauCur / 2) * BCur) +
        gammaPrev * ((tauPrev / 2) * BPrev) +
        gammaPrev * (⟪gCur, d⟫_ℝ + c * ⟪gPrev, d⟫_ℝ) := by
  exact young_absorb_two_adjacent_corrections hL htauPrev htauCur
    hgammaCur halpha hc hshift hcoef hbcur hbprev

/-! Private formula leaf for Lemma 6.13 after the Eq. (6.6.30) current-index
identity has been instantiated with the displayed `δ₂ᵗ` kernel.

This is intentionally the handoff boundary for the printed telescope:
Eqs. (6.6.31)-(6.6.36) are algebraic/inequality manipulation using exactly the
compiled source dependencies passed below.  The proof prose of Eq. (6.6.31)
uses nonnegative `γₜ`, so this leaf carries that sign as a local proof
obligation rather than promoting it to a paper-facing setup field. -/

/-- Realized-sample `yMem` branch normalization for the Eq. (6.6.31) route.

This is a route-local bridge for Lan Lemma 6.13, Eq. (6.6.29): the realized
next memory is rewritten with the current sample index `ξ n` rather than the
source-step arithmetic form `ξ (0 + ((n + 1) - 1))`.  Considered SOptLib candidates
`finset_weighted_residual_sum_eq_zero`, `finset_weighted_variance_eq_second_moment_sub_norm_mean_sq`,
`weighted_variance_le_second_moment`, `weighted_sq_norm_sub_center_le`,
`coefficients_for_average_minus_search_eq_alpha_step_minus_center`, and
`average_sub_search_eq_alpha_smul_step_sub_weighted_center`; none match because
this is not weighted algebra but the Algorithm 6.9 realized gradient-memory
branch needed before the Eq. (6.6.30) current-index cancellation. -/
theorem ambientFixed_realized_yMem_eq_currentSample_branch
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (z x0 xStar : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X)
    (hsource : setup.ambientFixedSourceDomain 0 z x0 xMem0 yMem0 hz hx0)
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
    (n : ℕ) (hn : n + 1 ≤ setup.s) (ω : Ω) :
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
        else stPrev.yMem i) := by
  classical
  funext i
  dsimp only
  have hsrc := hsource_yMem n hn ω i
  simpa using hsrc

/-- Diagonalizes the realized current-sample branch to the hat-point proof used
by `ambientFixedDelta2CurrentKernel`.

This is a route-local bridge for Lan Lemma 6.13, Eq. (6.6.29).  The same SOptLib
weighted-algebra candidates considered for
`ambientFixed_realized_yMem_eq_currentSample_branch` do not apply: this helper is
only proof-irrelevance plus the equality case `i = ξ n ω` for Algorithm 6.9's
realized refreshed component. -/
theorem ambientFixed_currentSample_branch_eq_delta2Kernel_branch
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (z x0 xStar : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X)
    (hsource : setup.ambientFixedSourceDomain 0 z x0 xMem0 yMem0 hz hx0)
    (hhat :
      setup.ambientFixedHatSourceDomain 0 z x0 xMem0 yMem0 hz hx0)
    (n : ℕ) (hn : n + 1 ≤ setup.s) (ω : Ω) :
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
            ⟨setup.xMemAfterSampleAtState (n + 1) (Nat.succ_pos n) hn i i stPrev,
              hhat n hn ω i⟩
        else stPrev.yMem i) := by
  classical
  funext i
  dsimp only
  by_cases hi : i = setup.ξ n ω
  · subst i
    simp
  · simp [hi]

/-- Rewrites the displayed `δ₂ᵗ` finite sum after separately aligning the
realized estimator vector and the prox point.

This is the route-local algebraic part of Lan Lemma 6.13, Eq. (6.6.29).
The SOptLib weighted-algebra candidates
`finset_weighted_residual_sum_eq_zero`,
`finset_weighted_variance_eq_second_moment_sub_norm_mean_sq`,
`Finset.weighted_variance_le_second_moment`, `weighted_sq_norm_sub_center_le`,
`coefficients_for_average_minus_search_eq_alpha_step_minus_center`, and
`average_sub_search_eq_alpha_smul_step_sub_weighted_center` were considered,
but none match: they control weighted residual/variance identities, while this
helper is only equality transport through the literal δ₂ inner-product
summand. -/
theorem delta2Kernel_sum_rewrite_of_y_prox
    (c : ℝ) (g gStar : ι → E) (xtilde xNext prox xStar : E)
    (y yBranch : ι → E)
    (hy : y = yBranch) (hx : xNext = prox) :
    c *
        Finset.sum Finset.univ
          (fun i : ι =>
            ⟪g i - gStar i, xtilde⟫_ℝ -
              ⟪yBranch i - gStar i, prox⟫_ℝ +
              ⟪yBranch i - g i, xStar⟫_ℝ) =
      c *
        Finset.sum Finset.univ
          (fun i : ι =>
            ⟪g i - gStar i, xtilde⟫_ℝ -
              ⟪y i - gStar i, xNext⟫_ℝ +
              ⟪y i - g i, xStar⟫_ℝ) := by
  subst xNext
  subst y
  rfl

/-- Rewrites the displayed `δ₂ᵗ` finite sum when the prox point is a function
of the realized estimator vector.

This is the equality-transport form needed for Lan Lemma 6.13, Eq. (6.6.29):
the caller may use the available realized prox equality `xNext = proxOf y`
directly, without first deriving a separate branch-prox equality.  Considered
SOptLib candidates `finset_weighted_residual_sum_eq_zero`,
`finset_weighted_variance_eq_second_moment_sub_norm_mean_sq`,
`Finset.weighted_variance_le_second_moment`, `weighted_sq_norm_sub_center_le`,
`coefficients_for_average_minus_search_eq_alpha_step_minus_center`, and the
existing target-file helper `delta2Kernel_sum_rewrite_of_y_prox`; none matched
this exact interface because the blocker is transport through `proxOf` from the
realized estimator, not weighted residual algebra or a precomputed prox point. -/
theorem delta2_kernel_sum_rewrite_of_y_prox_fun
    (c : ℝ) (g gStar : ι → E) (xtilde xNext xStar : E)
    (y yBranch : ι → E) (proxOf : (ι → E) → E)
    (hy : y = yBranch) (hx : xNext = proxOf y) :
    c *
        Finset.sum Finset.univ
          (fun i : ι =>
            ⟪g i - gStar i, xtilde⟫_ℝ -
              ⟪yBranch i - gStar i, proxOf yBranch⟫_ℝ +
              ⟪yBranch i - g i, xStar⟫_ℝ) =
      c *
        Finset.sum Finset.univ
          (fun i : ι =>
            ⟪g i - gStar i, xtilde⟫_ℝ -
              ⟪y i - gStar i, xNext⟫_ℝ +
              ⟪y i - g i, xStar⟫_ℝ) := by
  subst yBranch
  subst xNext
  rfl

/-- Rewrites the fixed-current `δ₂ᵗ` kernel to the realized `ỹᵗ` and prox
iterate form used in Lemma 6.13.

This is the source-local Eq. (6.6.29) transport before applying Eq. (6.6.30).
The SOptLib weighted residual/variance candidates and the earlier target-file
helper `delta2Kernel_sum_rewrite_of_y_prox` were considered; none exposes the
needed `proxOf : (ι → E) → E` interface from the realized estimator equality, so
the proof consumes `delta2_kernel_sum_rewrite_of_y_prox_fun` instead. -/
theorem ambientFixedDelta2CurrentKernel_realized_sum_Icc
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (z x0 xStar : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) (hxStar : xStar ∈ setup.X)
    (hhat :
      setup.ambientFixedHatSourceDomain 0 z x0 xMem0 yMem0 hz hx0)
    (hRealizedYTilideBranch_Icc :
      ∀ (t : ℕ) (ht1 : 1 ≤ t) (hts : t ≤ setup.s) (ω : Ω),
        let stPrev :=
          setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
            (t - 1) ω
        let stNext :=
          setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω
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
                              (by simpa [Nat.sub_add_cancel ht1] using hts) ω i⟩
                  else stPrev.yMem i) - stPrev.yMem i) +
              stPrev.yMem i))
    (hSourceStep_x_eq_prox_avgY_Icc :
      ∀ (t : ℕ) (ht1 : 1 ≤ t) (hts : t ≤ setup.s) (ω : Ω),
        let stPrev :=
          setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
            (t - 1) ω
        let stNext :=
          setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω
        let yTilde : ι → E :=
          fun i =>
            (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
              stPrev.yMem i
        stNext.x =
          setup.proxStepAt z t hz ht1 hts stPrev.x
            (by
              simpa [stPrev] using
                (((setup.ambientFixedInnerProcess_mem 0 z x0 xMem0 yMem0 hz hx0
                  (t - 1) (le_trans (Nat.sub_le t 1) hts)) ω).1))
            ((Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ yTilde)) :
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
          (hhat (t - 1) (by simpa [Nat.sub_add_cancel ht1] using hts))
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
  intro t ht1 hts ω
  let stPrev :=
    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
      (t - 1) ω
  let stNext :=
    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω
  let xHat : ι → E :=
    fun i => setup.xMemAfterSampleAtState t ht1 hts i i stPrev
  let hxHat : ∀ i : ι, xHat i ∈ setup.X := by
    intro i
    simpa [xHat, stPrev, Nat.sub_add_cancel ht1] using
      hhat (t - 1) (by simpa [Nat.sub_add_cancel ht1] using hts) ω i
  let yReal : ι → E :=
    fun i =>
      (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
        stPrev.yMem i
  let yBranch : ι → E :=
    fun i =>
      (Fintype.card ι : ℝ) •
          ((if _ : i = setup.ξ (t - 1) ω then
              setup.gradPsiOnAt z i ⟨xHat i, hxHat i⟩
            else stPrev.yMem i) - stPrev.yMem i) +
        stPrev.yMem i
  let proxOf : (ι → E) → E :=
    fun Y =>
      setup.proxStepAt z t hz ht1 hts stPrev.x
        (by
          simpa [stPrev] using
            (((setup.ambientFixedInnerProcess_mem 0 z x0 xMem0 yMem0 hz hx0
              (t - 1) (le_trans (Nat.sub_le t 1) hts)) ω).1))
        ((Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ Y)
  have hy := hRealizedYTilideBranch_Icc t ht1 hts ω
  have hx := hSourceStep_x_eq_prox_avgY_Icc t ht1 hts ω
  dsimp only at hy hx
  have hy' : yReal = yBranch := by
    simpa [yReal, yBranch, stPrev, stNext, xHat] using hy
  have hx' : stNext.x = proxOf yReal := by
    simpa [proxOf, yReal, stPrev, stNext] using hx
  dsimp [ambientFixedDelta2CurrentKernel]
  simp only [Nat.sub_add_cancel ht1]
  simpa [yReal, yBranch, proxOf, stPrev, stNext, xHat] using
    (delta2_kernel_sum_rewrite_of_y_prox_fun
      (c := (Fintype.card ι : ℝ)⁻¹)
      (g := fun i : ι => setup.gradPsiOnAt z i ⟨xHat i, hxHat i⟩)
      (gStar := fun i : ι => setup.gradPsiOnAt z i ⟨xStar, hxStar⟩)
      (xtilde := setup.xTildeAtState t stPrev)
      (xNext := stNext.x)
      (xStar := xStar)
      (y := yReal)
      (yBranch := yBranch)
      (proxOf := proxOf)
      hy' hx')

/-- Rewrites the realized current-index `δ₂ᵗ` kernel in the same `yHyp` /
`xNextHyp` language used by the averaged Eq. (6.6.30) expansion.

This is a route-local bridge for Lan Lemma 6.13, Eqs. (6.6.29)-(6.6.31):
the existing target-file candidates `ambientFixedDelta2CurrentKernel_realized_sum_Icc`,
`delta2_kernel_sum_rewrite_of_y_prox_fun`, and
`ambientFixedDelta2CurrentKernel_average_expansion` were considered.  The first
two supply the realized estimator/prox transport and are reused here, while the
average helper has the right target language but averages over `j` and therefore
does not specialize to the realized sample by itself; the SOptLib weighted
residual candidates are unrelated finite algebra. -/
theorem ambientFixedDelta2CurrentKernel_realized_sample_hyp_expansion_Icc
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (z x0 xStar : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) (hxStar : xStar ∈ setup.X)
    (hhat :
      setup.ambientFixedHatSourceDomain 0 z x0 xMem0 yMem0 hz hx0)
    (hRealizedYTilideBranch_Icc :
      ∀ (t : ℕ) (ht1 : 1 ≤ t) (hts : t ≤ setup.s) (ω : Ω),
        let stPrev :=
          setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
            (t - 1) ω
        let stNext :=
          setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω
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
                              (by simpa [Nat.sub_add_cancel ht1] using hts) ω i⟩
                  else stPrev.yMem i) - stPrev.yMem i) +
              stPrev.yMem i))
    (hSourceStep_x_eq_prox_avgY_Icc :
      ∀ (t : ℕ) (ht1 : 1 ≤ t) (hts : t ≤ setup.s) (ω : Ω),
        let stPrev :=
          setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
            (t - 1) ω
        let stNext :=
          setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω
        let yTilde : ι → E :=
          fun i =>
            (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
              stPrev.yMem i
        stNext.x =
          setup.proxStepAt z t hz ht1 hts stPrev.x
            (by
              simpa [stPrev] using
                (((setup.ambientFixedInnerProcess_mem 0 z x0 xMem0 yMem0 hz hx0
                  (t - 1) (le_trans (Nat.sub_le t 1) hts)) ω).1))
            ((Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ yTilde)) :
    ∀ (t : ℕ) (ht1 : 1 ≤ t) (hts : t ≤ setup.s) (ω : Ω),
      let stPrev :=
        setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
          (t - 1) ω
      let xHat : ι → E :=
        fun i => setup.xMemAfterSampleAtState t ht1 hts i i stPrev
      let hxHat : ∀ i : ι, xHat i ∈ setup.X := by
        intro i
        simpa [xHat, stPrev, Nat.sub_add_cancel ht1] using
          hhat (t - 1) (by simpa [Nat.sub_add_cancel ht1] using hts) ω i
      let yHyp : ι → ι → E := fun j i =>
        (Fintype.card ι : ℝ) •
            ((if _ : i = j then
                setup.gradPsiOnAt z i ⟨xHat i, hxHat i⟩
              else stPrev.yMem i) - stPrev.yMem i) +
          stPrev.yMem i
      let xNextHyp : ι → E := fun j =>
        setup.proxStepAt z t hz ht1 hts stPrev.x
          (by
            simpa [stPrev] using
              (((setup.ambientFixedInnerProcess_mem 0 z x0 xMem0 yMem0
                hz hx0 (t - 1) (le_trans (Nat.sub_le t 1) hts)) ω).1))
          ((Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ (fun i => yHyp j i))
      ambientFixedDelta2CurrentKernel
          (setup := setup) (offset := 0) (z := z) (x0 := x0)
          (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
          (hz := hz) (hx0 := hx0) (hxStar := hxStar)
          (t - 1)
          (by simpa [Nat.sub_add_cancel ht1] using hts)
          (hhat (t - 1) (by simpa [Nat.sub_add_cancel ht1] using hts))
          ω (setup.ξ (t - 1) ω) =
        (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ
            (fun i : ι =>
              ⟪setup.gradPsiOnAt z i ⟨xHat i, hxHat i⟩ -
                    setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                  setup.xTildeAtState t stPrev⟫_ℝ -
                ⟪yHyp (setup.ξ (t - 1) ω) i -
                    setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                  xNextHyp (setup.ξ (t - 1) ω)⟫_ℝ +
                ⟪yHyp (setup.ξ (t - 1) ω) i -
                    setup.gradPsiOnAt z i ⟨xHat i, hxHat i⟩,
                  xStar⟫_ℝ) := by
  intro t ht1 hts ω
  let stPrev :=
    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
      (t - 1) ω
  let stNext :=
    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω
  let xHat : ι → E :=
    fun i => setup.xMemAfterSampleAtState t ht1 hts i i stPrev
  let hxHat : ∀ i : ι, xHat i ∈ setup.X := by
    intro i
    simpa [xHat, stPrev, Nat.sub_add_cancel ht1] using
      hhat (t - 1) (by simpa [Nat.sub_add_cancel ht1] using hts) ω i
  let yReal : ι → E :=
    fun i =>
      (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
        stPrev.yMem i
  let yBranch : ι → E :=
    fun i =>
      (Fintype.card ι : ℝ) •
          ((if _ : i = setup.ξ (t - 1) ω then
              setup.gradPsiOnAt z i ⟨xHat i, hxHat i⟩
            else stPrev.yMem i) - stPrev.yMem i) +
        stPrev.yMem i
  let proxOf : (ι → E) → E :=
    fun Y =>
      setup.proxStepAt z t hz ht1 hts stPrev.x
        (by
          simpa [stPrev] using
            (((setup.ambientFixedInnerProcess_mem 0 z x0 xMem0 yMem0 hz hx0
              (t - 1) (le_trans (Nat.sub_le t 1) hts)) ω).1))
        ((Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ Y)
  have hbase :=
    ambientFixedDelta2CurrentKernel_realized_sum_Icc
      setup z x0 xStar xMem0 yMem0 hz hx0 hxStar hhat
      hRealizedYTilideBranch_Icc hSourceStep_x_eq_prox_avgY_Icc
      t ht1 hts ω
  have hy := hRealizedYTilideBranch_Icc t ht1 hts ω
  have hx := hSourceStep_x_eq_prox_avgY_Icc t ht1 hts ω
  dsimp only at hy hx hbase
  have hy' : yReal = yBranch := by
    simpa [yReal, yBranch, stPrev, stNext, xHat] using hy
  have hx' : stNext.x = proxOf yReal := by
    simpa [proxOf, yReal, stPrev, stNext] using hx
  have htransport :=
    (delta2_kernel_sum_rewrite_of_y_prox_fun
      (c := (Fintype.card ι : ℝ)⁻¹)
      (g := fun i : ι => setup.gradPsiOnAt z i ⟨xHat i, hxHat i⟩)
      (gStar := fun i : ι => setup.gradPsiOnAt z i ⟨xStar, hxStar⟩)
      (xtilde := setup.xTildeAtState t stPrev)
      (xNext := stNext.x)
      (xStar := xStar)
      (y := yReal)
      (yBranch := yBranch)
      (proxOf := proxOf)
      hy' hx')
  dsimp only
  exact hbase.trans (by
    simpa [yReal, yBranch, proxOf, stPrev, stNext, xHat] using htransport.symm)

/-- Abstract finite-window residual lift for Eq. (6.6.31).

This is the algorithm-free integration layer of Lan §6.6: a pointwise finite-sum
inequality with a realized-minus-averaged residual integrates to the same
residual written as a finite sum of integrals.  The pre-searched candidates
`finset_weighted_residual_sum_eq_zero`,
`finset_weighted_variance_eq_second_moment_sub_norm_mean_sq`,
`Finset.weighted_variance_le_second_moment`, `weighted_sq_norm_sub_center_le`,
`composite_upper_model_at_convex_average`, and
`coefficients_for_average_minus_search_eq_alpha_step_minus_center` were
considered; none matches this measure-theoretic residual lift because they are
finite algebra/model lemmas without an `integral_mono_ae` pointwise-to-integral
step. -/
theorem eq631_abstract_sum_residual_lift
    {Ω I : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset I)
    (left rhs actual avg : I → Ω → ℝ)
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
  exact integral_finset_sum_residual_lift_le
    (s := s) (left := left) (rhs := rhs) (actual := actual) (avg := avg)
    hleft_int hrhs_int hactual_int havg_int hpoint

/-- Abstract finite-window residual lift with an integrated zero correction.

This is the algorithm-free version of the expectation/current-index correction
in Lan Lemma 6.13, Eqs. (6.6.30)-(6.6.31): a pointwise identity may still carry
a current-sample residual, provided the finite-window integral of that residual
is zero.  Considered SOptLib candidates
`integral_finset_sum_const_mul_eq_zero`,
`finset_weighted_residual_sum_eq_zero`, and the already-local
`eq631_abstract_sum_residual_lift`; the first two prove narrower cancellation
or finite centering facts, while the local residual lift supplies the exact
measure-theoretic inequality and only needs this zero-correction extension. -/
theorem eq631_abstract_sum_residual_lift_with_zero_correction
    {Ω I : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset I)
    (left rhs actual avg corr : I → Ω → ℝ)
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
  exact integral_finset_sum_residual_lift_le_of_zero_correction
    (s := s) (left := left) (rhs := rhs) (actual := actual) (avg := avg)
    (corr := corr) hleft_int hrhs_int hactual_int havg_int hcorr_int hcorr_zero
    hpoint

/-- Finite-sum algebra for the pointwise residual premise in Eq. (6.6.31).

Searched target/SOptLib for "finite sum pointwise residual inequality summed
residual" and "Finset sum inequality add sub residual"; the only source-level
hit was the integrated `eq631_abstract_sum_residual_lift`, while SOptLib hits
were weighted residual or variance lemmas.  This helper is the missing pure
finite-sum reassociation between the fixed-time balance and that lift. -/
theorem eq631_sum_residual_pointwise_from_fixed_time
    {Ω I : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset I)
    (left rhs actual avg : I → Ω → ℝ)
    (hper :
      ∀ (ω : Ω) (i : I), i ∈ s →
        left i ω + avg i ω = rhs i ω + actual i ω) :
    ∀ᵐ ω ∂μ,
      Finset.sum s (fun i => left i ω) ≤
        Finset.sum s (fun i => rhs i ω) +
          (Finset.sum s (fun i => actual i ω) -
            Finset.sum s (fun i => avg i ω)) := by
  exact ae_finset_sum_residual_le_of_pointwise_balance
    (s := s) (left := left) (rhs := rhs) (actual := actual) (avg := avg) hper

/-- Proof-irrelevance bridge for component values on the carrier subtype.

This is route-local infrastructure for Lemma 6.13's Eq. (6.6.29)-(6.6.32)
alignment. No SOptLib match: searched proof-irrelevance and Bregman candidates
including `Subsingleton.elim`, `carrierBregmanDivergence_three_point_identity`,
`bregmanDivergence_three_point_identity`, and target-file
`affine_bregman_delta1_identity`; those prove algebraic identities, while this
lemma only normalizes carrier membership witnesses. -/
theorem psiAtOn_proof_irrel
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (z : E) (i : ι) {x : E} (hx hx' : x ∈ setup.X) :
    setup.psiAtOn z i ⟨x, hx⟩ = setup.psiAtOn z i ⟨x, hx'⟩ := by
  rfl

/-- Proof-irrelevance bridge for component gradients on the carrier subtype.

This is route-local infrastructure for Lemma 6.13's sampled fixed-time scalar
alignment. No SOptLib match: searched proof-irrelevance and Bregman candidates
including `Subsingleton.elim`, `carrierBregmanDivergence_three_point_identity`,
`bregmanDivergence_three_point_identity`, and target-file
`affine_bregman_delta1_identity`; those do not state equality under changed
carrier membership witnesses. -/
theorem gradPsiOnAt_proof_irrel
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (z : E) (i : ι) {x : E} (hx hx' : x ∈ setup.X) :
    setup.gradPsiOnAt z i ⟨x, hx⟩ = setup.gradPsiOnAt z i ⟨x, hx'⟩ := by
  rfl

/-- Proof-irrelevance bridge for the concrete component Bregman error.

This supports the Lan Lemma 6.13 Eq. (6.6.29)-(6.6.32) scalar route by separating
carrier proof normalization from the sampled-memory algebra. No SOptLib match:
searched `Bregman`, `Subsingleton.elim`, and the pre-searched weighted residual
candidates; existing Bregman lemmas prove mathematical identities, while this
lemma only changes subtype membership witnesses. -/
theorem psiBregmanAt_proof_irrel
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (z : E) (i : ι) {x y : E}
    (hx hx' : x ∈ setup.X) (hy hy' : y ∈ setup.X) :
    setup.psiBregmanAt z i ⟨x, hx⟩ ⟨y, hy⟩ =
      setup.psiBregmanAt z i ⟨x, hx'⟩ ⟨y, hy'⟩ := by
  rfl

/-- Sampled Eq. (6.6.29) Bregman atom with carrier-witness normalization.

This aligns Lan Lemma 6.13's sampled `δ₁ᵗ` component with the local Bregman
notation before the Eq. (6.6.31) scalar assembly.  Considered candidates
`finset_weighted_residual_sum_eq_zero`, `weighted_variance_le_second_moment`,
target-file `affine_bregman_delta1_identity`, and the proof-irrelevance bridges
`psiAtOn_proof_irrel`, `gradPsiOnAt_proof_irrel`, and
`psiBregmanAt_proof_irrel`; the weighted SOptLib lemmas are unrelated finite-sum
facts, while the affine helper plus the three proof-irrelevance bridges exactly
provide the paper Eq. (6.6.29) sampled atom. -/
theorem sampled_delta1_raw_atom_from_affine_bregman
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (z : E) (i : ι) (τ : ℝ)
    (prev hat star xTilde : E)
    (hprev hprev' : prev ∈ setup.X)
    (hhat hhat' : hat ∈ setup.X)
    (hstar hstar' : star ∈ setup.X)
    (haff : τ • (prev - hat) = hat - xTilde) :
    τ * setup.psiBregmanAt z i ⟨prev, hprev'⟩ ⟨star, hstar'⟩ -
        (1 + τ) * setup.psiBregmanAt z i ⟨hat, hhat'⟩ ⟨star, hstar'⟩ -
        τ * setup.psiBregmanAt z i ⟨prev, hprev'⟩ ⟨hat, hhat'⟩ =
      setup.psiAtOn z i ⟨star, hstar'⟩ -
        ⟪setup.gradPsiOnAt z i ⟨star, hstar'⟩, star⟫_ℝ -
        (setup.psiAtOn z i ⟨hat, hhat'⟩ -
          ⟪setup.gradPsiOnAt z i ⟨hat, hhat'⟩, hat⟫_ℝ +
          ⟪setup.gradPsiOnAt z i ⟨hat, hhat'⟩ -
              setup.gradPsiOnAt z i ⟨star, hstar'⟩,
            xTilde⟫_ℝ) := by
  have hbPrevStar :
      setup.psiBregmanAt z i ⟨prev, hprev⟩ ⟨star, hstar⟩ =
        setup.psiBregmanAt z i ⟨prev, hprev'⟩ ⟨star, hstar'⟩ :=
    psiBregmanAt_proof_irrel setup z i hprev hprev' hstar hstar'
  have hbHatStar :
      setup.psiBregmanAt z i ⟨hat, hhat⟩ ⟨star, hstar⟩ =
        setup.psiBregmanAt z i ⟨hat, hhat'⟩ ⟨star, hstar'⟩ :=
    psiBregmanAt_proof_irrel setup z i hhat hhat' hstar hstar'
  have hbPrevHat :
      setup.psiBregmanAt z i ⟨prev, hprev⟩ ⟨hat, hhat⟩ =
        setup.psiBregmanAt z i ⟨prev, hprev'⟩ ⟨hat, hhat'⟩ :=
    psiBregmanAt_proof_irrel setup z i hprev hprev' hhat hhat'
  have hvStar :
      setup.psiAtOn z i ⟨star, hstar⟩ =
        setup.psiAtOn z i ⟨star, hstar'⟩ :=
    psiAtOn_proof_irrel setup z i hstar hstar'
  have hvHat :
      setup.psiAtOn z i ⟨hat, hhat⟩ =
        setup.psiAtOn z i ⟨hat, hhat'⟩ :=
    psiAtOn_proof_irrel setup z i hhat hhat'
  have hgStar :
      setup.gradPsiOnAt z i ⟨star, hstar⟩ =
        setup.gradPsiOnAt z i ⟨star, hstar'⟩ :=
    gradPsiOnAt_proof_irrel setup z i hstar hstar'
  have hgHat :
      setup.gradPsiOnAt z i ⟨hat, hhat⟩ =
        setup.gradPsiOnAt z i ⟨hat, hhat'⟩ :=
    gradPsiOnAt_proof_irrel setup z i hhat hhat'
  have hcore :=
    affine_bregman_delta1_identity
      (τ := τ)
      (vPrev := setup.psiAtOn z i ⟨prev, hprev⟩)
      (vHat := setup.psiAtOn z i ⟨hat, hhat⟩)
      (vStar := setup.psiAtOn z i ⟨star, hstar⟩)
      (gHat := setup.gradPsiOnAt z i ⟨hat, hhat⟩)
      (gStar := setup.gradPsiOnAt z i ⟨star, hstar⟩)
      (prev := prev) (hat := hat) (star := star) (xTilde := xTilde)
      haff
  rw [← hbPrevStar, ← hbHatStar, ← hbPrevHat, ← hvStar, ← hvHat,
    ← hgStar, ← hgHat]
  simpa [RandomizedAcceleratedProximalPointSetup.psiBregmanAt] using hcore

/-- Scalar assembly for the fixed-time Eq. (6.6.31) balance.

This aligns with Lan Lemma 6.13 after the source-specific Eq. (6.6.28)-(6.6.30)
and sampled-memory Eq. (6.6.29) bridges have already been proved: it only
combines `γQ + avgδ₂ = prox + γδ₁ + realδ₂` with
`γδ + γδ₁ = eta + tauMemory`.  Considered candidates
`finiteWindowSelectedOutputExpectation_eq_weighted_sum`,
`finset_weighted_residual_sum_eq_zero`, `weighted_variance_le_second_moment`,
`composite_upper_model_at_convex_average`, and target-file helpers
`ambientFixedDelta2CurrentKernel_average_expansion`,
`ambientFixedDelta2CurrentKernel_realized_sample_hyp_expansion_Icc`,
`affine_bregman_delta1_identity`, and `one_hot_tau_memory_sum_eq`; none is this
final scalar reassociation step, while the target-file helpers supply its
nontrivial premises. -/
theorem eq631_fixed_time_balance_from_parts
    (left rhs prox eta tau q delta avg actual gamma delta1 : ℝ)
    (hleft : left = gamma * q + gamma * delta)
    (hrhs : rhs = prox + eta + tau)
    (hQ :
      gamma * q + avg = prox + gamma * delta1 + actual)
    (hDelta :
      gamma * delta + gamma * delta1 = eta + tau) :
    left + avg = rhs + actual := by
  linarith

/-- Scalar assembly for the source-faithful fixed-time Eq. (6.6.31) balance.

This is the same final reassociation as `eq631_fixed_time_balance_from_parts`,
but with the two mathematical interfaces separated in the form used by the
paper: first decompose `Q_t` using the averaged paper `δ₁ᵗ`, then use a separate
correction bridge to connect that averaged object and the `δ₂ᵗ` average to the
sampled memory expression consumed by the residual/tau-memory algebra. -/
theorem eq631_fixed_time_balance_from_paper_parts
    (left rhs prox eta tau q delta avg actual gamma delta1Paper delta1Raw : ℝ)
    (hleft : left = gamma * q + gamma * delta)
    (hrhs : rhs = prox + eta + tau)
    (hQ :
      gamma * q = prox + gamma * delta1Paper + actual)
    (hPaperToRaw :
      gamma * delta1Paper + avg = gamma * delta1Raw)
    (hDelta :
      gamma * delta + gamma * delta1Raw = eta + tau) :
    left + avg = rhs + actual := by
  linarith

/-- Scalar sampled-memory balance for the T2 part of Eq. (6.6.31).

This is the arithmetic core behind combining the sampled `δ₁` identity with
the one-hot tau-memory expansion: after `delta` is reduced to
`eta - invCard * inner + τ * bregPrevHat`, and `delta1Raw` is reduced using
`affine_bregman_delta1_identity`, the sampled component plus the uniform
`Aprev` subtraction gives `eta + tauMemory`.  Considered SOptLib candidates
`finset_weighted_residual_sum_eq_zero`, `weighted_variance_le_second_moment`,
`composite_upper_model_at_convex_average`, and target-file helpers
`affine_bregman_delta1_identity` and `one_hot_tau_memory_sum_eq`; those target
helpers supply the two source-specific premises, while this lemma is only the
remaining scalar regrouping. -/
theorem eq631_fixed_time_delta1_tau_memory_scalar
    (gamma tau invCard delta eta inner bregPrevHat
      AprevSample AhatSample sumAprev delta1Component delta1Raw tauMemory : ℝ)
    (hdelta :
      delta = eta - invCard * inner + tau * bregPrevHat)
    (hdelta1 :
      tau * AprevSample - (1 + tau) * AhatSample -
          tau * bregPrevHat =
        delta1Component)
    (hdelta1Raw :
      delta1Raw =
        delta1Component + AprevSample - invCard * sumAprev +
          invCard * inner)
    (htau :
      tauMemory =
        gamma * (1 + tau) * AprevSample -
          gamma * (1 + tau) * AhatSample -
          gamma * invCard * sumAprev) :
    gamma * delta + gamma * delta1Raw = gamma * eta + tauMemory := by
  rw [hdelta, hdelta1Raw, ← hdelta1, htau]
  ring

/-- Current-index averaged scalar form of the `δ₁ᵗ` plus Eq. (6.6.30)
correction.

This is the finite algebra behind Lan Lemma 6.13, Eqs. (6.6.29)-(6.6.31):
after the `δ₂ᵗ` correction is written as the double current-index sum, the
paper `δ₁ᵗ` average equals the current-index average of the sampled raw
`δ₁ᵗ` expression.  SOptLib candidates `finset_weighted_residual_sum_eq_zero`,
`inv_card_smul_sum_sub_const_eq`, and
`average_sub_search_eq_alpha_smul_step_sub_weighted_center` were considered;
they cover centering and weighted-average identities, but not this exact
paper scalar assembly with the component atom, memory-centering term, and
double inner-product correction. -/
theorem eq631_delta1_current_average_scalar
    (gamma : ℝ) (component Aprev : ι → ℝ) (B : ι → ι → ℝ) :
    gamma * ((Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ component) +
        gamma * ((Fintype.card ι : ℝ)⁻¹ * (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ
            (fun i : ι => Finset.sum Finset.univ (fun j : ι => B j i))) =
      gamma *
        RandomizedAcceleratedProximalPointSetup.currentIndexAverage
          (fun j : ι =>
            component j + Aprev j -
                (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ Aprev +
              (Fintype.card ι : ℝ)⁻¹ *
                Finset.sum Finset.univ (fun i : ι => B j i)) := by
  simpa [RandomizedAcceleratedProximalPointSetup.currentIndexAverage] using
    finiteUniformAverage_add_centered_double_sum
      (ι := ι) gamma component Aprev B

/-- Apply the one-hot estimator branch family at the realized sample index.

This is route-local infrastructure for the `ỹᵗ = yHyp i_t` transport in Lan
Lemma 6.13, Eqs. (6.6.29)-(6.6.32).  Considered SOptLib/target candidates
`ambientFixed_realized_yMem_eq_currentSample_branch`,
`ambientFixed_currentSample_branch_eq_delta2Kernel_branch`,
`currentIndexAverage_estimator_update_eq`, and stochastic-oracle estimator
update lemmas; those describe realized memory, averaged estimator algebra, or
process recursions, while this helper is only the literal sample application
of the already-constructed branch family. -/
theorem estimator_sample_branch_apply_eq
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (c : ℝ) (sample : ι) (g prev : ι → V) :
    (fun i : ι => c • ((if _ : i = sample then g i else prev i) - prev i) + prev i) =
      (fun j : ι =>
        fun i : ι => c • ((if _ : i = j then g i else prev i) - prev i) + prev i)
        sample := by
  rfl


/-- Realized estimator/prox branch transport to the sampled hypothetical branch.

This is the T1 bridge for Lan Lemma 6.13, Eqs. (6.6.29)-(6.6.32): it consumes
the source-derived realized `ỹᵗ` branch equality and prox equality, then returns
the two small equalities needed by `finset_inner_residual_transport`.  Considered
target-file candidates `ambientFixedDelta2CurrentKernel_realized_sum_Icc`,
`ambientFixedDelta2CurrentKernel_realized_sample_hyp_expansion_Icc`, and
`delta2_kernel_sum_rewrite_of_y_prox_fun`; those prove δ₂-kernel rewrites, while
this helper exposes only the branch/prox equalities needed for the δ residual. -/
theorem realized_y_prox_eq_sample_hyp_Icc
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X)
    (hhat :
      setup.ambientFixedHatSourceDomain 0 z x0 xMem0 yMem0 hz hx0)
    (hRealizedYTilideBranch_Icc :
      ∀ (t : ℕ) (ht1 : 1 ≤ t) (hts : t ≤ setup.s) (ω : Ω),
        let stPrev :=
          setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
            (t - 1) ω
        let stNext :=
          setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω
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
                              (by simpa [Nat.sub_add_cancel ht1] using hts) ω i⟩
                  else stPrev.yMem i) - stPrev.yMem i) +
              stPrev.yMem i))
    (hSourceStep_x_eq_prox_avgY_Icc :
      ∀ (t : ℕ) (ht1 : 1 ≤ t) (hts : t ≤ setup.s) (ω : Ω),
        let stPrev :=
          setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
            (t - 1) ω
        let stNext :=
          setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω
        let yTilde : ι → E :=
          fun i =>
            (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
              stPrev.yMem i
        stNext.x =
          setup.proxStepAt z t hz ht1 hts stPrev.x
            (by
              simpa [stPrev] using
                (((setup.ambientFixedInnerProcess_mem 0 z x0 xMem0 yMem0 hz hx0
                  (t - 1) (le_trans (Nat.sub_le t 1) hts)) ω).1))
            ((Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ yTilde)) :
    ∀ (t : ℕ) (ht1 : 1 ≤ t) (hts : t ≤ setup.s) (ω : Ω),
      let stPrev :=
        setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
          (t - 1) ω
      let stNext :=
        setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω
      let sample := setup.ξ (t - 1) ω
      let xHat : ι → E :=
        fun i => setup.xMemAfterSampleAtState t ht1 hts i i stPrev
      let hxHat : ∀ i : ι, xHat i ∈ setup.X := by
        intro i
        simpa [xHat, stPrev, Nat.sub_add_cancel ht1] using
          hhat (t - 1) (by simpa [Nat.sub_add_cancel ht1] using hts) ω i
      let yReal : ι → E :=
        fun i =>
          (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
            stPrev.yMem i
      let yHyp : ι → ι → E := fun j i =>
        (Fintype.card ι : ℝ) •
            ((if _ : i = j then
                setup.gradPsiOnAt z i ⟨xHat i, hxHat i⟩
              else stPrev.yMem i) - stPrev.yMem i) +
          stPrev.yMem i
      let xNextHyp : ι → E := fun j =>
        setup.proxStepAt z t hz ht1 hts stPrev.x
          (by
            simpa [stPrev] using
              (((setup.ambientFixedInnerProcess_mem 0 z x0 xMem0 yMem0
                hz hx0 (t - 1) (le_trans (Nat.sub_le t 1) hts)) ω).1))
          ((Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ (fun i => yHyp j i))
      yReal = yHyp sample ∧ stNext.x = xNextHyp sample := by
  intro t ht1 hts ω
  let stPrev :=
    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0
      (t - 1) ω
  let stNext :=
    setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω
  let sample := setup.ξ (t - 1) ω
  let xHat : ι → E :=
    fun i => setup.xMemAfterSampleAtState t ht1 hts i i stPrev
  let hxHat : ∀ i : ι, xHat i ∈ setup.X := by
    intro i
    simpa [xHat, stPrev, Nat.sub_add_cancel ht1] using
      hhat (t - 1) (by simpa [Nat.sub_add_cancel ht1] using hts) ω i
  let gHat : ι → E := fun i => setup.gradPsiOnAt z i ⟨xHat i, hxHat i⟩
  let yReal : ι → E :=
    fun i =>
      (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) +
        stPrev.yMem i
  let yBranchSample : ι → E := fun i =>
    (Fintype.card ι : ℝ) •
        ((if _ : i = sample then gHat i else stPrev.yMem i) - stPrev.yMem i) +
      stPrev.yMem i
  let yHyp : ι → ι → E := fun j i =>
    (Fintype.card ι : ℝ) •
        ((if _ : i = j then gHat i else stPrev.yMem i) - stPrev.yMem i) +
      stPrev.yMem i
  let proxOf : (ι → E) → E := fun Y =>
    setup.proxStepAt z t hz ht1 hts stPrev.x
      (by
        simpa [stPrev] using
          (((setup.ambientFixedInnerProcess_mem 0 z x0 xMem0 yMem0 hz hx0
            (t - 1) (le_trans (Nat.sub_le t 1) hts)) ω).1))
      ((Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ Y)
  let xNextHyp : ι → E := fun j => proxOf (yHyp j)
  have hy_src := hRealizedYTilideBranch_Icc t ht1 hts ω
  have hx_src := hSourceStep_x_eq_prox_avgY_Icc t ht1 hts ω
  dsimp only at hy_src hx_src
  have hy0 : yReal = yBranchSample := by
    simpa [yReal, yBranchSample, gHat, sample, stPrev, stNext, xHat] using hy_src
  have hy_sample : yBranchSample = yHyp sample := by
    simpa [yBranchSample, yHyp, gHat] using
      (estimator_sample_branch_apply_eq
        (ι := ι) (c := (Fintype.card ι : ℝ)) (sample := sample)
        (g := gHat) (prev := fun i : ι => stPrev.yMem i))
  have hy : yReal = yHyp sample := hy0.trans hy_sample
  have hx0 : stNext.x = proxOf yReal := by
    simpa [proxOf, yReal, stPrev, stNext] using hx_src
  have hx : stNext.x = xNextHyp sample := by
    calc
      stNext.x = proxOf yReal := hx0
      _ = proxOf (yHyp sample) := by rw [hy]
      _ = xNextHyp sample := rfl
  exact ⟨hy, hx⟩

/-- Transport a finite inner-residual sum across already-typed equalities.

This is route-local infrastructure for the `δ_t` residual in Lan Eq. (6.6.32),
used before the scalar balance `eq631_fixed_time_delta1_tau_memory_scalar`.
Searched SOptLib/target candidates for "Finset sum inner residual transport
function equality" and "inner sub right Finset sum congr"; the hits were
weighted residual/variance or integrability lemmas, not this pointwise equality
transport. -/
theorem finset_inner_residual_transport
    (g y y' : ι → E) (x xTilde x' : E)
    (hy : y = y') (hx : x = x') :
    Finset.sum Finset.univ
        (fun i : ι => ⟪y i - g i, xTilde - x⟫_ℝ) =
      Finset.sum Finset.univ
        (fun i : ι => ⟪y' i - g i, xTilde - x'⟫_ℝ) := by
  subst y'
  subst x'
  rfl

/-- Transport a fixed-time prox summand through aligned estimator and prox
points.

This is the T1 prox-summand part of Lan Lemma 6.13, Eq. (6.6.31): after
`realized_y_prox_eq_sample_hyp_Icc` supplies `ỹᵗ = yHyp i_t` and
`xᵗ = xNextHyp i_t`, the displayed prox term is definitionally the same.
Considered target-file helpers `finset_inner_residual_transport`,
`delta2_kernel_sum_rewrite_of_y_prox_fun`, and
`ambientFixedDelta2CurrentKernel_realized_sample_hyp_expansion_Icc`; those
transport residual or δ₂ kernels, while this helper isolates only the prox
summand transport. -/
theorem prox_summand_transport
    (γ c : ℝ) (phi : E → ℝ) (xStar x x' : E) (y y' : ι → E)
    (hy : y = y') (hx : x = x') :
    γ * (phi x - phi xStar +
        ⟪c • Finset.sum Finset.univ y, x - xStar⟫_ℝ) =
      γ * (phi x' - phi xStar +
        ⟪c • Finset.sum Finset.univ y', x' - xStar⟫_ℝ) := by
  subst y'
  subst x'
  rfl

/-- Pure scalar expansion of Lan Lemma 6.13's `Q_t` decomposition.

This aligns with Eqs. (6.6.28)-(6.6.29): after `Q_t`, the prox summand,
the paper `δ₁ᵗ`, and the realized `δ₂ᵗ` kernel have been unfolded, the remaining
work is finite-sum inner-product algebra.  Considered SOptLib candidates
`finset_weighted_residual_sum_eq_zero`, `weighted_sq_norm_sub_center_le`, and
target-file helpers `currentIndexAverage_delta2_double_sum_expansion`,
`ambientFixedDelta2CurrentKernel_realized_sample_hyp_expansion_Icc`, and
`eq631_fixed_time_delta1_tau_memory_scalar`; none states this non-averaged
`Q = prox + δ₁ + δ₂` expansion, so this helper isolates that literal paper form. -/
theorem eq631_fixed_time_q_realized_delta2_paper_scalar
    (gamma invCard phiNext phiStar : ℝ)
    (xNext xStar xTilde : E)
    (psiStar psiHat : ι → ℝ)
    (gStar gHat yTilde xHat : ι → E) :
    gamma *
        (phiNext +
          invCard * Finset.sum Finset.univ psiStar +
          ⟪invCard • Finset.sum Finset.univ gStar, xNext - xStar⟫_ℝ +
          -(phiStar +
            invCard * Finset.sum Finset.univ
              (fun i : ι => psiHat i + ⟪gHat i, xStar - xHat i⟫_ℝ))) =
      gamma *
          (phiNext - phiStar +
            ⟪invCard • Finset.sum Finset.univ yTilde, xNext - xStar⟫_ℝ) +
        gamma *
          (invCard *
            Finset.sum Finset.univ
              (fun i : ι =>
                psiStar i - ⟪gStar i, xStar⟫_ℝ -
                  (psiHat i - ⟪gHat i, xHat i⟫_ℝ +
                    ⟪gHat i - gStar i, xTilde⟫_ℝ))) +
        gamma *
          (invCard *
            Finset.sum Finset.univ
              (fun i : ι =>
                ⟪gHat i - gStar i, xTilde⟫_ℝ -
                  ⟪yTilde i - gStar i, xNext⟫_ℝ +
                  ⟪yTilde i - gHat i, xStar⟫_ℝ)) := by
  exact finset_inner_scalar_three_way_expansion
    Finset.univ gamma invCard phiNext phiStar xNext xStar xTilde psiStar psiHat gStar gHat yTilde xHat

/-- Finite-sum reassociation used to align the source Eq. (6.6.31) right side
with the local `proxTauLeft + weightedEtaStep` layout.

SOptLib finite residual and telescope candidates were considered, but this is
only the local `sum_add_distrib`/`sum_comm` bookkeeping shape. -/
theorem finset_sum_three_comm_middle
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    (s : Finset I) (u : Finset J)
    (a b : I → ℝ) (c : I → J → ℝ) :
    Finset.sum s (fun i => a i + b i + Finset.sum u (fun j => c i j)) =
      (Finset.sum s a + Finset.sum u (fun j => Finset.sum s (fun i => c i j))) +
        Finset.sum s b := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_comm]
  ring

/-- Integral version of `finset_sum_three_comm_middle` used for the Eq.
(6.6.31) right-hand normalization.

SOptLib finite-sum and integral finite-sum candidates were considered; the
needed step is only pointwise finite-sum reassociation under the integral. -/
theorem integral_finset_sum_three_comm_middle
    {Ω I J : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [DecidableEq I] [DecidableEq J]
    (s : Finset I) (u : Finset J)
    (a b : I → Ω → ℝ) (c : I → J → Ω → ℝ) :
    (∫ ω, Finset.sum s
        (fun i => a i ω + b i ω + Finset.sum u (fun j => c i j ω)) ∂μ) =
      ∫ ω,
        (Finset.sum s (fun i => a i ω) +
          Finset.sum u (fun j => Finset.sum s (fun i => c i j ω))) +
          Finset.sum s (fun i => b i ω) ∂μ := by
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro ω
  exact finset_sum_three_comm_middle s u
    (fun i => a i ω) (fun i => b i ω) (fun i j => c i j ω)

/-- Guarded `Icc` integral sums normalize to the corresponding attached sum.

SOptLib integral finite-sum candidates were checked, including
`integral_finset_sum_const_mul_eq_zero`; none matches this proof-dependent
guard erasure for the Eq. (6.6.30) residual definition. -/
theorem sum_Icc_integral_guarded_const_mul_attach
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

/-- Nested-bound version of `sum_Icc_integral_guarded_const_mul_attach`.

SOptLib and the target-file attached-sum helper above were considered; this
variant is needed because the local Eq. (6.6.30) residual summands are encoded
with nested `1 ≤ t` and `t ≤ s` guards rather than a single `t ∈ Icc` guard. -/
theorem sum_Icc_integral_nested_guarded_const_mul_attach
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (N : ℕ) (γ : ℕ → ℝ)
    (F : (t : ℕ) → 1 ≤ t → t ≤ N → Ω → ℝ) :
    Finset.sum (Finset.Icc 1 N)
        (fun t =>
          ∫ ω,
            (if ht1 : 1 ≤ t then
              if hts : t ≤ N then γ t * F t ht1 hts ω else 0
            else 0) ∂μ) =
      Finset.sum (Finset.Icc 1 N).attach
        (fun t =>
          γ t.1 *
            ∫ ω,
              F t.1 (Finset.mem_Icc.mp t.2).1 (Finset.mem_Icc.mp t.2).2 ω ∂μ) := by
  exact sum_Icc_integral_nested_guarded_const_mul_eq_sum_attach
    (μ := μ) 1 N γ F

end RandomizedAcceleratedProximalPointSetup
