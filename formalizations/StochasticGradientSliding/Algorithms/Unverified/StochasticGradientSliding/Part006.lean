import Algorithms.Unverified.StochasticGradientSliding.Part005
import SOptLib.Model.Bregman
import SOptLib.Model.Filtration
import SOptLib.Model.Iterates
import SOptLib.Model.Norms
import SOptLib.Model.Objective
import SOptLib.Model.Prox
import SOptLib.Model.Subdifferential
import SOptLib.Glue.Probability
import SOptLib.Glue.Martingale
import SOptLib.Layer0.Oracle
import SOptLib.Layer1.Proximal
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

/-!
Stochastic gradient sliding.

Phase 0 object layer for Lan's stochastic gradient sliding method.  The
declarations below encode the paper-facing mathematical objects as definitions:
the composite objective, Bregman prox geometry, stochastic oracle samples, SPS
inner update, and the outer SGS recursion.
-/

open scoped BigOperators Gradient InnerProductSpace
open MeasureTheory ProbabilityTheory

set_option maxHeartbeats 800000

namespace StochasticGradientSliding


universe u v w z

variable {E : Type u} {Sample : Type v} {Ω : Type w}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Fixed-interval form of a compact ceiling bucket as overrun minus
accumulated endpoint deficits.

Aligns with the bucket-local algebra immediately after Lan Eq. (8.1.79):
once a realized integer-budget fiber has been rewritten as an endpoint interval,
the row sum is a constant integer overrun diminished by signed ceiling deficits.
Candidate audit: considered target helper
`compact_ceiling_grid_bucket_signed_sum_eq_card`, SOptLib
`inv_card_smul_sum_sub_const_eq` and `sum_Icc_sub_succ`, and Mathlib
`Finset.sum_sub_distrib`/`Finset.sum_const`; the target helper still carries a
filtered fiber, while the SOptLib telescope helpers do not state this literal
closed-interval algebraic normal form. -/
theorem compact_ceiling_grid_endpoint_interval_deficit_form
    (a b r : ℕ) (grid R Q : ℕ → ℝ) :
    (Finset.Icc a b).sum (fun k => (grid k - (r : ℝ)) * Q r + R r) =
      ((Finset.Icc a b).card : ℝ) * R r -
        Q r * (Finset.Icc a b).sum (fun k => (r : ℝ) - grid k) := by
  classical
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul]
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  ring

/-- Normal form for the endpoint expression stored after bucket grouping.

Aligns with the same Lan Corollary 8.3 / Eq. (8.1.79) bucket algebra as
`compact_ceiling_grid_endpoint_interval_deficit_form`, but starts from the
already-collected endpoint expression used in the local proof state. Candidate
audit: considered the preceding `compact_ceiling_grid_endpoint_interval_deficit_form`,
target `compact_ceiling_grid_bucket_signed_sum_eq_card`, and SOptLib
`sum_Icc_sub_succ`; none rewrites this collected endpoint expression directly,
so this corollary supplies the exact bridge consumed by `endpointTerm`. -/
theorem compact_ceiling_grid_endpoint_interval_normal_form
    (a b r : ℕ) (grid R Q : ℕ → ℝ) :
    Q r *
        ((Finset.Icc a b).sum grid -
          ((Finset.Icc a b).card : ℝ) * (r : ℝ)) +
      ((Finset.Icc a b).card : ℝ) * R r =
      ((Finset.Icc a b).card : ℝ) * R r -
        Q r * (Finset.Icc a b).sum (fun k => (r : ℝ) - grid k) := by
  classical
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  ring

/-- Scalar cancellation for the retained nonmax edge.

Aligns with Lan Corollary 8.3 / Eq. (8.1.79): this is only the algebra that
cancels the retained residual `-Q * (sum - card * def) + Q * sum` while keeping
the outgoing carry. Candidate audit: searched target/SOptLib for "retained edge
normal form endpoint carry"; existing hits such as
`compact_ceiling_grid_endpoint_interval_normal_form`,
`compact_ceiling_grid_corrected_bucket_residual_normal_form`, and the ordered
telescope helpers are bucket/range normal forms or consumers, not this local
five-term retained-edge cancellation. -/
private theorem compact_ceiling_grid_retained_edge_cancel_normal_form
    (card Hr Qr Qs jump deficit sumDef : ℝ) :
    card * (Hr - Qr * deficit) -
        Qr * (sumDef - card * deficit) +
        Qr * jump + Qr * sumDef - Qs * deficit =
      card * Hr + Qr * jump - Qs * deficit := by
  ring

/-- A nonempty realized monotone compact-ceiling bucket is a contiguous interval.

Aligns with the bucket-interval step in Lan Corollary 8.3 after Eq. (8.1.79):
once two endpoint rows have the same integer budget, monotonicity forces every
intermediate row to stay in that bucket. Candidate audit: considered SOptLib
`finite_image_min_max_attainment_pack`, local
`compact_ceiling_grid_tail_sum_eq_realized_bucket_sum`, and Mathlib
`Finset.min'_mem`/`Finset.max'_mem`; the SOptLib helper packages image extrema
rather than filtered fibers, so this local bridge records the exact fiber-to-Icc
form consumed by the compact-grid scalar proof. -/
theorem compact_ceiling_grid_bucket_interval
    (s : Finset ℕ) (N j r : ℕ) (m : ℕ → ℕ)
    (hs :
      s = (Finset.range N).filter (fun k => j ≤ k ∧ m k = r))
    (hne : s.Nonempty)
    (hsame_bucket_between :
      ∀ a b t, a ≤ t → t ≤ b →
        j ≤ a ∧ m a = r → j ≤ b ∧ m b = r →
          j ≤ t ∧ m t = r) :
    s = Finset.Icc (s.min' hne) (s.max' hne) := by
  classical
  ext t
  constructor
  · intro ht
    have hmin_le : s.min' hne ≤ t := Finset.min'_le s t ht
    have hle_max : t ≤ s.max' hne := Finset.le_max' s t ht
    exact Finset.mem_Icc.mpr ⟨hmin_le, hle_max⟩
  · intro ht
    have hIcc := Finset.mem_Icc.mp ht
    have hmin_mem : s.min' hne ∈ s := Finset.min'_mem s hne
    have hmax_mem : s.max' hne ∈ s := Finset.max'_mem s hne
    have hmin_filter :
        s.min' hne ∈
          (Finset.range N).filter (fun k => j ≤ k ∧ m k = r) := by
      simpa [hs] using hmin_mem
    have hmax_filter :
        s.max' hne ∈
          (Finset.range N).filter (fun k => j ≤ k ∧ m k = r) := by
      simpa [hs] using hmax_mem
    have hmin_bucket : j ≤ s.min' hne ∧ m (s.min' hne) = r :=
      (Finset.mem_filter.mp hmin_filter).2
    have hmax_bucket : j ≤ s.max' hne ∧ m (s.max' hne) = r :=
      (Finset.mem_filter.mp hmax_filter).2
    have ht_bucket : j ≤ t ∧ m t = r :=
      hsame_bucket_between (s.min' hne) (s.max' hne) t
        hIcc.1 hIcc.2 hmin_bucket hmax_bucket
    have hmax_range : s.max' hne ∈ Finset.range N :=
      (Finset.mem_filter.mp hmax_filter).1
    have ht_range : t ∈ Finset.range N := by
      exact Finset.mem_range.mpr
        (lt_of_le_of_lt hIcc.2 (Finset.mem_range.mp hmax_range))
    rw [hs]
    exact Finset.mem_filter.mpr ⟨ht_range, ht_bucket⟩

/-- Group the compact ceiling high tail by realized integer-budget buckets.

Aligns with the bucket decomposition required in Lan Corollary 8.3 after
Eq. (8.1.79): the high-tail signed sum is first partitioned by the monotone
integer budget value before applying any bucket potential. Candidate audit:
checked Mathlib `Finset.sum_fiberwise_of_maps_to`/`Finset.sum_filter`, SOptLib
finite partition/telescope helpers, and target-file compact ceiling helpers;
the generic fiberwise lemma supplies the partition API, but this route-local
statement records the exact `j ≤ k ∧ m k = r` bucket shape consumed below. -/
theorem compact_ceiling_grid_tail_sum_eq_realized_bucket_sum
    (N j : ℕ) (grid R Q : ℕ → ℝ) (m : ℕ → ℕ) :
    (Finset.range N).sum (fun k =>
      if j ≤ k then (grid k - (m k : ℝ)) * Q (m k) + R (m k) else 0) =
      (((Finset.range N).filter (fun k => j ≤ k)).image m).sum (fun r =>
        (Finset.range N).sum (fun k =>
          if j ≤ k ∧ m k = r then (grid k - (r : ℝ)) * Q r + R r else 0)) := by
  classical
  let s : Finset ℕ := (Finset.range N).filter (fun k => j ≤ k)
  let f : ℕ → ℝ := fun k => (grid k - (m k : ℝ)) * Q (m k) + R (m k)
  have htail_filter :
    (Finset.range N).sum (fun k =>
        if j ≤ k then (grid k - (m k : ℝ)) * Q (m k) + R (m k) else 0) =
        s.sum f := by
    rw [← Finset.sum_filter]
  have hmaps : ∀ k ∈ s, m k ∈ s.image m := by
    intro k hk
    exact Finset.mem_image_of_mem m hk
  have hfiber :
      (((Finset.range N).filter (fun k => j ≤ k)).image m).sum (fun r =>
        (s.filter (fun k => m k = r)).sum f) =
        s.sum f := by
    simpa [s] using
      (Finset.sum_fiberwise_of_maps_to (s := s)
        (t := s.image m) (g := m) hmaps f)
  have hinner : ∀ r,
      (s.filter (fun k => m k = r)).sum f =
        (Finset.range N).sum (fun k =>
          if j ≤ k ∧ m k = r then (grid k - (r : ℝ)) * Q r + R r else 0) := by
    intro r
    calc
      (s.filter (fun k => m k = r)).sum f
          = ((Finset.range N).filter (fun k => j ≤ k ∧ m k = r)).sum
              (fun k => (grid k - (r : ℝ)) * Q r + R r) := by
            have hset :
                s.filter (fun k => m k = r) =
                  (Finset.range N).filter (fun k => j ≤ k ∧ m k = r) := by
              ext k
              simp [s, and_left_comm, and_assoc]
            rw [hset]
            refine Finset.sum_congr rfl ?_
            intro k hk
            simp at hk
            simp [f, hk.2]
      _ = (Finset.range N).sum (fun k =>
            if j ≤ k ∧ m k = r then (grid k - (r : ℝ)) * Q r + R r else 0) := by
            rw [← Finset.sum_filter]
  calc
    (Finset.range N).sum (fun k =>
        if j ≤ k then (grid k - (m k : ℝ)) * Q (m k) + R (m k) else 0)
        = s.sum f := htail_filter
    _ = (((Finset.range N).filter (fun k => j ≤ k)).image m).sum (fun r =>
          (s.filter (fun k => m k = r)).sum f) := by
          rw [hfiber]
    _ = (((Finset.range N).filter (fun k => j ≤ k)).image m).sum (fun r =>
          (Finset.range N).sum (fun k =>
            if j ≤ k ∧ m k = r then (grid k - (r : ℝ)) * Q r + R r else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro r _hr
          exact hinner r

/-- Right-endpoint exit for a realized compact ceiling bucket.

Aligns with the endpoint-boundary step in Lan Corollary 8.3 / Eq. (8.1.79):
if the successor of the maximal index in a high realized bucket is still in the
horizon, then the underlying real grid has crossed above that bucket's integer
ceiling value. Candidate audit: considered the pre-searched SOptLib process
and filtration candidates, `finite_image_min_max_attainment_pack`, target
`compact_ceiling_grid_bucket_interval`, and Mathlib `Nat.ceil_le`; the SOptLib
hits do not apply to this scalar filtered-fiber endpoint, while `Nat.ceil_le`
and `Finset.le_max'` supply the exact local proof. -/
theorem compact_ceiling_grid_endpoint_exit_or_terminal
    (N j r : ℕ) (grid : ℕ → ℝ) (m : ℕ → ℕ) (fiber : Finset ℕ)
    (hfiber :
      fiber = (Finset.range N).filter (fun k => j ≤ k ∧ m k = r))
    (hfiber_nonempty : fiber.Nonempty)
    (hm_def : ∀ k, m k = max 1 (Nat.ceil (grid k)))
    (hm_mono : Monotone m)
    (hgrid_strict : StrictMono grid)
    (hr_high : 9 ≤ r)
    (hb_succ_range : fiber.max' hfiber_nonempty + 1 ∈ Finset.range N) :
    (r : ℝ) < grid (fiber.max' hfiber_nonempty + 1) := by
  classical
  let b : ℕ := fiber.max' hfiber_nonempty
  have hb_mem : b ∈ fiber := by
    simpa [b] using Finset.max'_mem fiber hfiber_nonempty
  have hb_filter :
      b ∈ (Finset.range N).filter (fun k => j ≤ k ∧ m k = r) := by
    simpa [hfiber] using hb_mem
  have hb_j : j ≤ b := (Finset.mem_filter.mp hb_filter).2.1
  have hb_m : m b = r := (Finset.mem_filter.mp hb_filter).2.2
  have _hb_grid_strict : grid b < grid (b + 1) :=
    hgrid_strict (Nat.lt_succ_self b)
  by_contra hnot
  have hgrid_succ_le : grid (b + 1) ≤ (r : ℝ) := not_lt.mp hnot
  have hceil_succ_le : Nat.ceil (grid (b + 1)) ≤ r :=
    Nat.ceil_le.mpr hgrid_succ_le
  have hr_one : 1 ≤ r := by omega
  have hm_succ_le : m (b + 1) ≤ r := by
    rw [hm_def (b + 1)]
    exact max_le hr_one hceil_succ_le
  have hr_le_m_succ : r ≤ m (b + 1) := by
    calc
      r = m b := hb_m.symm
      _ ≤ m (b + 1) := hm_mono (Nat.le_succ b)
  have hm_succ : m (b + 1) = r := le_antisymm hm_succ_le hr_le_m_succ
  have hb_succ_fiber : b + 1 ∈ fiber := by
    rw [hfiber]
    exact Finset.mem_filter.mpr
      ⟨hb_succ_range, le_trans hb_j (Nat.le_succ b), hm_succ⟩
  have hb_succ_le_b : b + 1 ≤ b := by
    have hle := Finset.le_max' fiber (b + 1) hb_succ_fiber
    simpa [b] using hle
  omega

/-- Endpoint deficit bound for a nonterminal realized compact-ceiling bucket.

Aligns with the boundary-transport part of Lan Corollary 8.3 / Eq. (8.1.79):
once a bucket exits at `b + 1`, the remaining right-endpoint ceiling deficit is
absorbed by the next grid increment, which is the cubic source increment from
Eq. (8.1.75). Candidate audit: searched target/SOptLib for endpoint-deficit
and successor-increment helpers; existing hits
`compact_ceiling_grid_endpoint_exit_or_terminal`,
`compact_ceiling_grid_cubic_increment_eq`, and
`compact_ceiling_grid_actual_bucket_residual_increment_form` provide crossing,
increment algebra, and bucket normal form separately, but none states this
boundary-charge bridge. -/
theorem compact_ceiling_grid_endpoint_deficit_lt_cubic_increment
    (r b : ℕ) (c : ℝ) (grid : ℕ → ℝ)
    (hgrid_increment : ∀ k,
      grid (k + 1) - grid k =
        c * (((k + 2 : ℕ) : ℝ)) * (3 * (k : ℝ) + 7))
    (hupper : grid b ≤ (r : ℝ))
    (hexit : (r : ℝ) < grid (b + 1)) :
    0 ≤ (r : ℝ) - grid b ∧
      (r : ℝ) - grid b <
        c * (((b + 2 : ℕ) : ℝ)) * (3 * (b : ℝ) + 7) := by
  constructor
  · linarith
  · have hdeficit_lt_increment :
        (r : ℝ) - grid b < grid (b + 1) - grid b := by
      linarith
    simpa [hgrid_increment b] using hdeficit_lt_increment

/-- Bucket-local absorption of the integer harmonic overrun by the final
endpoint deficit.

Aligns with the bucket-potential step in Lan Corollary 8.3 / Eq. (8.1.79):
after grouping rows with the same realized compact ceiling, the sum of endpoint
deficits can absorb the integer overrun down to the right-endpoint deficit.
Candidate audit: checked SOptLib `sum_range_sub_succ_le_first_of_last_nonneg`,
Mathlib `Finset.sum_range_sub'`, target helpers
`compact_ceiling_grid_endpoint_interval_deficit_form` and
`compact_ceiling_grid_integer_overrun_le_harmonic_div`; the telescope helpers
do not state this ordered-field absorption, while the harmonic lemma supplies
`hR_le` at the call site. -/
theorem compact_ceiling_grid_bucket_absorb_harmonic_final
    (r : ℕ) (grid R Q H : ℕ → ℝ) (s : Finset ℕ) (b : ℕ)
    (hR_le : R r ≤ H r / (r : ℝ))
    (hQ_nonneg : 0 ≤ Q r)
    (hdeficit :
      (s.card : ℝ) * ((r : ℝ) - grid b) ≤
        s.sum (fun k => (r : ℝ) - grid k)) :
    (s.card : ℝ) * R r -
        Q r * s.sum (fun k => (r : ℝ) - grid k) ≤
      (s.card : ℝ) *
        (H r / (r : ℝ) - Q r * ((r : ℝ) - grid b)) := by
  have hcard_nonneg : 0 ≤ (s.card : ℝ) := by positivity
  have hRpart : (s.card : ℝ) * R r ≤ (s.card : ℝ) * (H r / (r : ℝ)) := by
    exact mul_le_mul_of_nonneg_left hR_le hcard_nonneg
  have hmulD :
      Q r * ((s.card : ℝ) * ((r : ℝ) - grid b)) ≤
        Q r * s.sum (fun k => (r : ℝ) - grid k) :=
    mul_le_mul_of_nonneg_left hdeficit hQ_nonneg
  calc
    (s.card : ℝ) * R r - Q r * s.sum (fun k => (r : ℝ) - grid k)
        ≤ (s.card : ℝ) * (H r / (r : ℝ)) -
            Q r * s.sum (fun k => (r : ℝ) - grid k) := by
          linarith
    _ ≤ (s.card : ℝ) * (H r / (r : ℝ)) -
            Q r * ((s.card : ℝ) * ((r : ℝ) - grid b)) := by
          linarith
    _ = (s.card : ℝ) *
          (H r / (r : ℝ) - Q r * ((r : ℝ) - grid b)) := by
          ring

/-- Bucket-local harmonic absorption retaining the intra-bucket deficit
residual.

Aligns with the signed scalar simplification in Lan Corollary 8.3 / Eq.
(8.1.79): the harmonic endpoint envelope is valid only after keeping the
nonnegative residual between the full bucket deficit and the terminal endpoint
deficit. Candidate audit: considered the target helper
`compact_ceiling_grid_bucket_absorb_harmonic_final`, target row helper
`compact_ceiling_grid_integer_overrun_le_harmonic_div`, Mathlib
`Finset.sum_sub_distrib`, and SOptLib telescope helpers; the existing bucket
helper drops this residual, while the telescope helpers do not package this
ordered-field comparison. -/
theorem compact_ceiling_grid_bucket_absorb_harmonic_with_residual
    (r : ℕ) (grid R Q H : ℕ → ℝ) (s : Finset ℕ) (b : ℕ)
    (hR_le : R r ≤ H r / (r : ℝ))
    (hQ_nonneg : 0 ≤ Q r)
    (hdeficit :
      (s.card : ℝ) * ((r : ℝ) - grid b) ≤
        s.sum (fun k => (r : ℝ) - grid k)) :
    (s.card : ℝ) * R r -
        Q r * s.sum (fun k => (r : ℝ) - grid k) ≤
      (s.card : ℝ) *
          (H r / (r : ℝ) - Q r * ((r : ℝ) - grid b)) -
        Q r *
          (s.sum (fun k => (r : ℝ) - grid k) -
            (s.card : ℝ) * ((r : ℝ) - grid b)) ∧
      0 ≤ Q r *
          (s.sum (fun k => (r : ℝ) - grid k) -
            (s.card : ℝ) * ((r : ℝ) - grid b)) := by
  constructor
  · have hcard_nonneg : 0 ≤ (s.card : ℝ) := by positivity
    have hRpart :
        (s.card : ℝ) * R r ≤ (s.card : ℝ) * (H r / (r : ℝ)) :=
      mul_le_mul_of_nonneg_left hR_le hcard_nonneg
    calc
      (s.card : ℝ) * R r -
          Q r * s.sum (fun k => (r : ℝ) - grid k)
          ≤ (s.card : ℝ) * (H r / (r : ℝ)) -
              Q r * s.sum (fun k => (r : ℝ) - grid k) := by
            linarith
      _ =
          (s.card : ℝ) *
              (H r / (r : ℝ) - Q r * ((r : ℝ) - grid b)) -
            Q r *
              (s.sum (fun k => (r : ℝ) - grid k) -
                (s.card : ℝ) * ((r : ℝ) - grid b)) := by
            ring
  · have hres :
        0 ≤ s.sum (fun k => (r : ℝ) - grid k) -
          (s.card : ℝ) * ((r : ℝ) - grid b) := by
      linarith
    exact mul_nonneg hQ_nonneg hres

/-- Corrected compact-ceiling bucket normal form retaining weighted residual
drops.

Aligns with Lan Corollary 8.3 / Eq. (8.1.79): after replacing the integer
overrun by the harmonic correction, the actual bucket contribution is the final
endpoint charge minus the triangular weighted intra-bucket grid drops. Candidate
audit: considered local `compact_ceiling_grid_bucket_absorb_harmonic_with_residual`,
target `finset_Icc_residual_eq_weighted_Ico_drops`, and SOptLib
`sum_range_sub_succ_le_first_of_last_nonneg`; the residual identity supplies the
needed finite-sum normal form while the telescope lemma is for the later
range-level cancellation. -/
theorem compact_ceiling_grid_corrected_bucket_residual_normal_form
    (a b r : ℕ) (grid Q H : ℕ → ℝ) (hab : a ≤ b) :
    ((Finset.Icc a b).card : ℝ) * (H r / (r : ℝ)) -
        Q r * (Finset.Icc a b).sum (fun k => (r : ℝ) - grid k) -
      ((Finset.Icc a b).card : ℝ) *
        (Q r * ((r : ℝ) * (3 * (r : ℝ) + 7) /
          (((r : ℝ) + 1) * ((r : ℝ) + 2)))) =
      ((Finset.Icc a b).card : ℝ) *
          (H r / (r : ℝ) -
            Q r * ((r : ℝ) - grid b) -
            Q r * ((r : ℝ) * (3 * (r : ℝ) + 7) /
              (((r : ℝ) + 1) * ((r : ℝ) + 2)))) -
        Q r *
          (Finset.Ico a b).sum (fun k =>
            (((k - a + 1 : ℕ) : ℝ) * (grid (k + 1) - grid k))) := by
  have hresD :=
    finset_Icc_residual_eq_weighted_Ico_drops
      a b (fun k => (r : ℝ) - grid k) hab
  have hres :
      (Finset.Icc a b).sum (fun k => (r : ℝ) - grid k) -
          ((Finset.Icc a b).card : ℝ) * ((r : ℝ) - grid b) =
        (Finset.Ico a b).sum (fun k =>
          (((k - a + 1 : ℕ) : ℝ) * (grid (k + 1) - grid k))) := by
    calc
      (Finset.Icc a b).sum (fun k => (r : ℝ) - grid k) -
          ((Finset.Icc a b).card : ℝ) * ((r : ℝ) - grid b)
          =
        (Finset.Ico a b).sum (fun k =>
          (((k - a + 1 : ℕ) : ℝ) *
            (((r : ℝ) - grid k) - ((r : ℝ) - grid (k + 1))))) := by
          exact hresD
      _ =
        (Finset.Ico a b).sum (fun k =>
          (((k - a + 1 : ℕ) : ℝ) * (grid (k + 1) - grid k))) := by
          refine Finset.sum_congr rfl ?_
          intro k _hk
          ring
  rw [← hres]
  ring

/-- Exact correction left by replacing the compact integer overrun `R r` by
the harmonic endpoint envelope `H r / r`.

Aligns with the retained signed term in Lan Corollary 8.3 / Eq. (8.1.79):
the endpoint-only route is too strong unless this positive `Q`-weighted
correction is carried into the bucket telescope. Candidate audit: considered
pre-searched process/update candidates
`estimatorResidualProcess_succ_eq_of_estimator_update`,
`epochCounter_succ_eq_div_of_divisibility_update`,
`mirrorStep_minimizes_of_update`, `literalMirrorStep_of_update_of_interior`,
`BlockIterateState`, and `iIndepFun.indep_past_iSup_current`, plus target
helpers `compact_ceiling_grid_bucket_absorb_harmonic_with_residual` and
`compact_linear_sps_normalized_q_minus_one_eq`; none states this literal
same-row algebraic correction from the paper's `R` and `Q` definitions. -/
theorem compact_ceiling_grid_H_div_sub_R_eq_Q_correction
    (r : ℕ) (R Q H : ℕ → ℝ)
    (hR_def : ∀ r,
      R r =
        (H r * ((r : ℝ) ^ 2 + 3 * (r : ℝ) + 2) -
          (3 * (r : ℝ) ^ 2 + 7 * (r : ℝ))) /
          ((r : ℝ) * ((r : ℝ) + 3) ^ 2))
    (hQ_def : ∀ r,
      Q r =
        (((((r : ℝ) + 1) * ((r : ℝ) + 2) / ((r : ℝ) + 3) ^ 2) *
          (1 + H r / (r : ℝ))) /
          (r : ℝ)))
    (hr : 9 ≤ r) :
    H r / (r : ℝ) - R r =
      Q r * ((r : ℝ) * (3 * (r : ℝ) + 7) /
        (((r : ℝ) + 1) * ((r : ℝ) + 2))) := by
  have hr_pos_nat : 0 < r := by omega
  have hr_pos : 0 < (r : ℝ) := by exact_mod_cast hr_pos_nat
  have hr_ne : (r : ℝ) ≠ 0 := ne_of_gt hr_pos
  have hr1_ne : (r : ℝ) + 1 ≠ 0 := by positivity
  have hr2_ne : (r : ℝ) + 2 ≠ 0 := by positivity
  have hr3_ne : (r : ℝ) + 3 ≠ 0 := by positivity
  rw [hR_def r, hQ_def r]
  field_simp [hr_ne, hr1_ne, hr2_ne, hr3_ne]
  ring

/-- Actual compact-ceiling bucket contribution in corrected residual-drop form.

Aligns with Lan Corollary 8.3 / Eq. (8.1.79): the intervalized actual bucket is
converted to the endpoint charge minus the retained weighted grid-increment
residual while keeping the exact `H / r - R` correction. Candidate audit:
considered local `compact_ceiling_grid_bucket_absorb_harmonic_with_residual`,
`compact_ceiling_grid_corrected_bucket_residual_normal_form`, and SOptLib
`sum_range_sub_succ_le_first_of_last_nonneg`; the absorb helper only gives an
upper envelope, while the corrected residual normal form plus the exact
correction identity gives the source-faithful signed equality needed before the
global potential telescope. -/
theorem compact_ceiling_grid_actual_bucket_residual_increment_form
    (a b r : ℕ) (grid R Q H : ℕ → ℝ)
    (hR_def : ∀ r,
      R r =
        (H r * ((r : ℝ) ^ 2 + 3 * (r : ℝ) + 2) -
          (3 * (r : ℝ) ^ 2 + 7 * (r : ℝ))) /
          ((r : ℝ) * ((r : ℝ) + 3) ^ 2))
    (hQ_def : ∀ r,
      Q r =
        (((((r : ℝ) + 1) * ((r : ℝ) + 2) / ((r : ℝ) + 3) ^ 2) *
          (1 + H r / (r : ℝ))) /
          (r : ℝ)))
    (hr : 9 ≤ r) (hab : a ≤ b) :
    ((Finset.Icc a b).card : ℝ) * R r -
        Q r * (Finset.Icc a b).sum (fun k => (r : ℝ) - grid k) =
      ((Finset.Icc a b).card : ℝ) *
          (H r / (r : ℝ) -
            Q r * ((r : ℝ) - grid b) -
            Q r * ((r : ℝ) * (3 * (r : ℝ) + 7) /
              (((r : ℝ) + 1) * ((r : ℝ) + 2)))) -
        Q r *
          (Finset.Ico a b).sum (fun k =>
            (((k - a + 1 : ℕ) : ℝ) * (grid (k + 1) - grid k))) := by
  have hcorr :=
    compact_ceiling_grid_H_div_sub_R_eq_Q_correction r R Q H hR_def hQ_def hr
  have hnorm :=
    compact_ceiling_grid_corrected_bucket_residual_normal_form a b r grid Q H hab
  calc
    ((Finset.Icc a b).card : ℝ) * R r -
        Q r * (Finset.Icc a b).sum (fun k => (r : ℝ) - grid k)
        =
      ((Finset.Icc a b).card : ℝ) * (H r / (r : ℝ)) -
          Q r * (Finset.Icc a b).sum (fun k => (r : ℝ) - grid k) -
        ((Finset.Icc a b).card : ℝ) *
          (Q r * ((r : ℝ) * (3 * (r : ℝ) + 7) /
            (((r : ℝ) + 1) * ((r : ℝ) + 2)))) := by
          rw [← hcorr]
          ring
    _ =
      ((Finset.Icc a b).card : ℝ) *
          (H r / (r : ℝ) -
            Q r * ((r : ℝ) - grid b) -
            Q r * ((r : ℝ) * (3 * (r : ℝ) + 7) /
              (((r : ℝ) + 1) * ((r : ℝ) + 2)))) -
        Q r *
          (Finset.Ico a b).sum (fun k =>
            (((k - a + 1 : ℕ) : ℝ) * (grid (k + 1) - grid k))) := hnorm

/-- Corrected residual/drop bucket expression as literal signed interval rows.

Aligns with Lan Corollary 8.3 / Eq. (8.1.79): after the harmonic correction
and weighted-drop residual have been introduced, the bucket term is still
exactly the signed row sum over the closed realized interval. Candidate audit:
considered pre-searched process/update candidates, SOptLib
`sum_range_sub_succ_le_first_of_last_nonneg`, target helpers
`compact_ceiling_grid_actual_bucket_residual_increment_form`,
`compact_ceiling_grid_endpoint_interval_deficit_form`, and Mathlib finite-sum
rewrites; the process candidates are unrelated, the telescope API is only for
the later range-level potential, and these two target helpers compose to this
route-local no-fiber algebraic bridge. -/
theorem compact_ceiling_grid_residual_increment_bucket_eq_signed_interval
    (a b r : ℕ) (grid R Q H : ℕ → ℝ)
    (hR_def : ∀ r,
      R r =
        (H r * ((r : ℝ) ^ 2 + 3 * (r : ℝ) + 2) -
          (3 * (r : ℝ) ^ 2 + 7 * (r : ℝ))) /
          ((r : ℝ) * ((r : ℝ) + 3) ^ 2))
    (hQ_def : ∀ r,
      Q r =
        (((((r : ℝ) + 1) * ((r : ℝ) + 2) / ((r : ℝ) + 3) ^ 2) *
          (1 + H r / (r : ℝ))) /
          (r : ℝ)))
    (hr : 9 ≤ r) (hab : a ≤ b) :
    ((Finset.Icc a b).card : ℝ) *
        (H r / (r : ℝ) -
          Q r * ((r : ℝ) - grid b) -
          Q r * ((r : ℝ) * (3 * (r : ℝ) + 7) /
            (((r : ℝ) + 1) * ((r : ℝ) + 2)))) -
      Q r *
        (Finset.Ico a b).sum (fun k =>
          (((k - a + 1 : ℕ) : ℝ) * (grid (k + 1) - grid k))) =
    (Finset.Icc a b).sum (fun k => grid k * Q r - 1) := by
  classical
  have hactual :=
    compact_ceiling_grid_actual_bucket_residual_increment_form
      a b r grid R Q H hR_def hQ_def hr hab
  have hinterval :=
    compact_ceiling_grid_endpoint_interval_deficit_form a b r grid R Q
  have hrow :
      (Finset.Icc a b).sum (fun k => (grid k - (r : ℝ)) * Q r + R r) =
        (Finset.Icc a b).sum (fun k => grid k * Q r - 1) := by
    refine Finset.sum_congr rfl ?_
    intro k _hk
    have hsplit :
        grid k * Q r - 1 = (grid k - (r : ℝ)) * Q r + R r := by
      have hr_pos_nat : 0 < r := by omega
      have hr_pos : 0 < (r : ℝ) := by exact_mod_cast hr_pos_nat
      have hr_ne : (r : ℝ) ≠ 0 := ne_of_gt hr_pos
      have hr3_ne : (r : ℝ) + 3 ≠ 0 := by positivity
      rw [hR_def r, hQ_def r]
      field_simp [hr_ne, hr3_ne]
      ring
    exact hsplit.symm
  calc
    ((Finset.Icc a b).card : ℝ) *
        (H r / (r : ℝ) -
          Q r * ((r : ℝ) - grid b) -
          Q r * ((r : ℝ) * (3 * (r : ℝ) + 7) /
            (((r : ℝ) + 1) * ((r : ℝ) + 2)))) -
      Q r *
        (Finset.Ico a b).sum (fun k =>
          (((k - a + 1 : ℕ) : ℝ) * (grid (k + 1) - grid k)))
        =
      ((Finset.Icc a b).card : ℝ) * R r -
        Q r * (Finset.Icc a b).sum (fun k => (r : ℝ) - grid k) := hactual.symm
    _ =
      (Finset.Icc a b).sum (fun k => (grid k - (r : ℝ)) * Q r + R r) :=
        hinterval.symm
    _ =
      (Finset.Icc a b).sum (fun k => grid k * Q r - 1) := hrow

/-- Deficit form for a nonempty realized high-tail compact-ceiling bucket.

Aligns with Lan Corollary 8.3 / Eq. (8.1.79): after grouping by the realized
integer budget, monotonicity makes each nonempty fiber a closed interval, so the
actual signed bucket contribution is the interval endpoint-deficit expression.
Candidate audit: considered local `compact_ceiling_grid_bucket_signed_sum_eq_card`,
`compact_ceiling_grid_bucket_interval`,
`compact_ceiling_grid_endpoint_interval_deficit_form`, SOptLib
`sum_Icc_sub_succ`, and Mathlib `Finset.sum_filter`; the three local helpers
compose to this exact filtered-fiber-to-interval bridge, while the SOptLib and
Mathlib APIs only provide lower-level telescope/filter mechanics. -/
theorem compact_ceiling_grid_realized_bucket_deficit_form
    (N j r : ℕ) (grid R Q : ℕ → ℝ) (m : ℕ → ℕ)
    (hm_mono : Monotone m)
    (hfiber_nonempty :
      ((Finset.range N).filter (fun k => j ≤ k ∧ m k = r)).Nonempty) :
    (Finset.range N).sum (fun k =>
      if j ≤ k ∧ m k = r then (grid k - (r : ℝ)) * Q r + R r else 0) =
      let fiber : Finset ℕ :=
        (Finset.range N).filter (fun k => j ≤ k ∧ m k = r)
      ((Finset.Icc (fiber.min' hfiber_nonempty)
          (fiber.max' hfiber_nonempty)).card : ℝ) * R r -
        Q r *
          (Finset.Icc (fiber.min' hfiber_nonempty)
            (fiber.max' hfiber_nonempty)).sum (fun k => (r : ℝ) - grid k) := by
  classical
  let fiber : Finset ℕ :=
    (Finset.range N).filter (fun k => j ≤ k ∧ m k = r)
  have hsame_bucket_between :
      ∀ a b t, a ≤ t → t ≤ b →
        j ≤ a ∧ m a = r → j ≤ b ∧ m b = r →
          j ≤ t ∧ m t = r := by
    intro a b t hat htb ha hb
    have hjt : j ≤ t := le_trans ha.1 hat
    have hle_left : r ≤ m t := by
      calc
        r = m a := ha.2.symm
        _ ≤ m t := hm_mono hat
    have hle_right : m t ≤ r := by
      calc
        m t ≤ m b := hm_mono htb
        _ = r := hb.2
    exact ⟨hjt, le_antisymm hle_right hle_left⟩
  have hinterval :
      fiber = Finset.Icc (fiber.min' hfiber_nonempty)
        (fiber.max' hfiber_nonempty) := by
    exact compact_ceiling_grid_bucket_interval fiber N j r m rfl
      hfiber_nonempty hsame_bucket_between
  calc
    (Finset.range N).sum (fun k =>
        if j ≤ k ∧ m k = r then (grid k - (r : ℝ)) * Q r + R r else 0)
        = fiber.sum (fun k => (grid k - (r : ℝ)) * Q r + R r) := by
          rw [← Finset.sum_filter]
    _ =
      (Finset.Icc (fiber.min' hfiber_nonempty)
          (fiber.max' hfiber_nonempty)).sum
        (fun k => (grid k - (r : ℝ)) * Q r + R r) := by
          conv_lhs => rw [hinterval]
    _ =
      ((Finset.Icc (fiber.min' hfiber_nonempty)
          (fiber.max' hfiber_nonempty)).card : ℝ) * R r -
        Q r *
          (Finset.Icc (fiber.min' hfiber_nonempty)
            (fiber.max' hfiber_nonempty)).sum (fun k => (r : ℝ) - grid k) := by
          exact compact_ceiling_grid_endpoint_interval_deficit_form
            (fiber.min' hfiber_nonempty) (fiber.max' hfiber_nonempty) r grid R Q

/-- High-tail signed rows grouped into intervalized realized buckets.

Aligns with Lan Corollary 8.3 / Eq. (8.1.79): this is the mechanical
transport from the row-wise signed high tail to the closed-interval realized
bucket expression, before any endpoint/drop potential estimate is applied.
Candidate audit: considered target helpers
`compact_ceiling_grid_tail_sum_eq_realized_bucket_sum` and
`compact_ceiling_grid_realized_bucket_deficit_form`, plus SOptLib/Mathlib
finite partition/telescope hits `sum_range_sub_succ_le_first_of_last_nonneg`
and `Finset.sum_filter`; the two target helpers compose to the exact
source-local transport, while the generic APIs do not encode the realized
compact-ceiling bucket interval. -/
theorem compact_ceiling_grid_tail_signed_eq_intervalized_buckets
    (N j : ℕ) (grid R Q : ℕ → ℝ) (m : ℕ → ℕ)
    (hm_mono : Monotone m)
    (hsigned_row : ∀ k,
      grid k * Q (m k) - 1 =
        (grid k - (m k : ℝ)) * Q (m k) + R (m k)) :
    (Finset.range N).sum (fun k =>
      if j ≤ k then grid k * Q (m k) - 1 else 0) =
    (Finset.image m ((Finset.range N).filter (fun k => j ≤ k))).sum (fun r =>
      let fiber : Finset ℕ :=
        (Finset.range N).filter (fun k => j ≤ k ∧ m k = r)
      if hne : fiber.Nonempty then
        ((Finset.Icc (fiber.min' hne) (fiber.max' hne)).card : ℝ) * R r -
          Q r *
            (Finset.Icc (fiber.min' hne) (fiber.max' hne)).sum
              (fun k => (r : ℝ) - grid k)
      else 0) := by
  classical
  let B : Finset ℕ :=
    Finset.image m ((Finset.range N).filter (fun k => j ≤ k))
  have hbucket_nonempty : ∀ r ∈ B,
      ((Finset.range N).filter (fun k => j ≤ k ∧ m k = r)).Nonempty := by
    intro r hr
    rcases (by simpa [B, Finset.mem_filter] using hr :
        ∃ k, (k < N ∧ j ≤ k) ∧ m k = r) with ⟨k, ⟨hkN, hjk⟩, hmk⟩
    exact ⟨k, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hkN, hjk, hmk⟩⟩
  have htail_eq_realized :
      (Finset.range N).sum (fun k =>
        if j ≤ k then grid k * Q (m k) - 1 else 0) =
      B.sum (fun r =>
        (Finset.range N).sum (fun k =>
          if j ≤ k ∧ m k = r then (grid k - (r : ℝ)) * Q r + R r else 0)) := by
    calc
      (Finset.range N).sum (fun k =>
          if j ≤ k then grid k * Q (m k) - 1 else 0)
          =
        (Finset.range N).sum (fun k =>
          if j ≤ k then
            (grid k - (m k : ℝ)) * Q (m k) + R (m k)
          else 0) := by
            refine Finset.sum_congr rfl ?_
            intro k _hk
            by_cases hjk : j ≤ k
            · simp [hjk, hsigned_row k]
            · simp [hjk]
      _ =
        (Finset.image m ((Finset.range N).filter (fun k => j ≤ k))).sum
          (fun r =>
            (Finset.range N).sum (fun k =>
              if j ≤ k ∧ m k = r then (grid k - (r : ℝ)) * Q r + R r else 0)) := by
            exact compact_ceiling_grid_tail_sum_eq_realized_bucket_sum
              N j grid R Q m
      _ =
        B.sum (fun r =>
          (Finset.range N).sum (fun k =>
            if j ≤ k ∧ m k = r then (grid k - (r : ℝ)) * Q r + R r else 0)) := by
            rfl
  have hrealized_eq_interval :
      B.sum (fun r =>
        (Finset.range N).sum (fun k =>
          if j ≤ k ∧ m k = r then (grid k - (r : ℝ)) * Q r + R r else 0)) =
      B.sum (fun r =>
        let fiber : Finset ℕ :=
          (Finset.range N).filter (fun k => j ≤ k ∧ m k = r)
        if hne : fiber.Nonempty then
          ((Finset.Icc (fiber.min' hne) (fiber.max' hne)).card : ℝ) * R r -
            Q r *
              (Finset.Icc (fiber.min' hne) (fiber.max' hne)).sum
                (fun k => (r : ℝ) - grid k)
        else 0) := by
    refine Finset.sum_congr rfl ?_
    intro r hr
    have hfiber_nonempty :
        ((Finset.range N).filter (fun k => j ≤ k ∧ m k = r)).Nonempty :=
      hbucket_nonempty r hr
    have hdeficit :=
      compact_ceiling_grid_realized_bucket_deficit_form
        N j r grid R Q m hm_mono hfiber_nonempty
    simpa [hfiber_nonempty] using hdeficit
  exact htail_eq_realized.trans hrealized_eq_interval

set_option maxHeartbeats 800000

/-- Intervalized actual buckets in residual/increment endpoint form.

Aligns with Lan Corollary 8.3 / Eq. (8.1.79): after high-tail rows are grouped
into realized buckets, each bucket is converted to the corrected endpoint
charge minus the weighted intra-bucket grid-increment residual. Candidate
audit: considered target helpers
`compact_ceiling_grid_actual_bucket_residual_increment_form`,
`compact_ceiling_grid_endpoint_exit_or_terminal`, and SOptLib
`sum_range_sub_succ_le_first_of_last_nonneg`; the residual/increment helper is
the exact bucket-local normal form, while endpoint exit and range telescoping
are later global-potential steps rather than pointwise bucket rewrites. -/
theorem compact_ceiling_grid_intervalized_bucket_sum_eq_residual_increment
    (N j : ℕ) (grid R Q H : ℕ → ℝ) (m : ℕ → ℕ)
    (hR_def : ∀ r,
      R r =
        (H r * ((r : ℝ) ^ 2 + 3 * (r : ℝ) + 2) -
          (3 * (r : ℝ) ^ 2 + 7 * (r : ℝ))) /
          ((r : ℝ) * ((r : ℝ) + 3) ^ 2))
    (hQ_def : ∀ r,
      Q r =
        (((((r : ℝ) + 1) * ((r : ℝ) + 2) / ((r : ℝ) + 3) ^ 2) *
          (1 + H r / (r : ℝ))) /
          (r : ℝ)))
    (hj_tail_high : ∀ k, j ≤ k → 9 ≤ m k) :
    (Finset.image m ((Finset.range N).filter (fun k => j ≤ k))).sum (fun r =>
      let fiber : Finset ℕ :=
        (Finset.range N).filter (fun k => j ≤ k ∧ m k = r)
      if hne : fiber.Nonempty then
        ((Finset.Icc (fiber.min' hne) (fiber.max' hne)).card : ℝ) * R r -
          Q r *
            (Finset.Icc (fiber.min' hne) (fiber.max' hne)).sum
              (fun k => (r : ℝ) - grid k)
      else 0) =
    (Finset.image m ((Finset.range N).filter (fun k => j ≤ k))).sum (fun r =>
      let fiber : Finset ℕ :=
        (Finset.range N).filter (fun k => j ≤ k ∧ m k = r)
      if hne : fiber.Nonempty then
        ((Finset.Icc (fiber.min' hne) (fiber.max' hne)).card : ℝ) *
            (H r / (r : ℝ) -
              Q r * ((r : ℝ) - grid (fiber.max' hne)) -
              Q r * ((r : ℝ) * (3 * (r : ℝ) + 7) /
                (((r : ℝ) + 1) * ((r : ℝ) + 2)))) -
          Q r *
            (Finset.Ico (fiber.min' hne) (fiber.max' hne)).sum (fun k =>
              (((k - fiber.min' hne + 1 : ℕ) : ℝ) *
                (grid (k + 1) - grid k)))
      else 0) := by
  classical
  let B : Finset ℕ :=
    Finset.image m ((Finset.range N).filter (fun k => j ≤ k))
  have hbucket_nonempty : ∀ r ∈ B,
      ((Finset.range N).filter (fun k => j ≤ k ∧ m k = r)).Nonempty := by
    intro r hr
    rcases (by simpa [B, Finset.mem_filter] using hr :
        ∃ k, (k < N ∧ j ≤ k) ∧ m k = r) with ⟨k, ⟨hkN, hjk⟩, hmk⟩
    exact ⟨k, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hkN, hjk, hmk⟩⟩
  have hbucket_high : ∀ r ∈ B, 9 ≤ r := by
    intro r hr
    rcases (by simpa [B, Finset.mem_filter] using hr :
        ∃ k, (k < N ∧ j ≤ k) ∧ m k = r) with ⟨k, ⟨_hkN, hjk⟩, hmk⟩
    simpa [hmk] using hj_tail_high k hjk
  refine Finset.sum_congr rfl ?_
  intro r hr
  let fiber : Finset ℕ :=
    (Finset.range N).filter (fun k => j ≤ k ∧ m k = r)
  have hfiber : fiber.Nonempty := hbucket_nonempty r (by simpa [B] using hr)
  have hab : fiber.min' hfiber ≤ fiber.max' hfiber :=
    Finset.le_max' fiber (fiber.min' hfiber) (Finset.min'_mem fiber hfiber)
  have hform :=
    compact_ceiling_grid_actual_bucket_residual_increment_form
      (fiber.min' hfiber) (fiber.max' hfiber) r grid R Q H
      hR_def hQ_def (hbucket_high r (by simpa [B] using hr)) hab
  simpa [fiber, hfiber] using hform

/-- Generic consumer for the compact-grid charge potential.

Aligns with the final finite-telescope step in Lan Corollary 8.3 / Eq.
(8.1.79): once a non-cumulative potential has `A 0 ≤ 1`, nonnegative terminal
value, and pointwise drops dominating the charge, the normalized charge sum is
bounded by `1`. Candidate audit: SOptLib
`sum_range_sub_succ_le_first_of_last_nonneg` is the exact telescope API, while
the target-file compact bucket helpers supply only the source-specific drop
premises and not this generic summation wrapper. -/
theorem compact_ceiling_grid_charge_sum_le_one_of_drop
    (charge A : ℕ → ℝ) (N : ℕ)
    (hA0 : A 0 ≤ 1) (hAN : 0 ≤ A N)
    (hdrop : ∀ k ∈ Finset.range N, charge k ≤ A k - A (k + 1)) :
    (Finset.range N).sum charge ≤ 1 := by
  calc
    (Finset.range N).sum charge
        ≤ (Finset.range N).sum (fun k => A k - A (k + 1)) := by
          exact Finset.sum_le_sum hdrop
    _ ≤ A 0 := by
          exact sum_range_sub_succ_le_first_of_last_nonneg A N hAN
    _ ≤ 1 := hA0
/-- Assemble a full compact-grid charge potential from a high-tail potential.

Aligns with the finite-telescope assembly in Lan Corollary 8.3 / Eq. (8.1.79):
before the first high row the potential spends the exact accumulated low
credit, and from `j` onward it follows the source-specific tail potential.
Candidate audit: considered SOptLib `sum_range_sub_succ_le_first_of_last_nonneg`,
target `compact_ceiling_grid_charge_sum_le_one_of_drop`, and local low-prefix
helpers `compact_ceiling_grid_prefix_signed_le_neg_low_credit` /
`compact_ceiling_grid_low_prefix_exact_credit`; the telescope consumer is the
matching summation API, while the low-prefix helpers do not assemble the
boundary jump into an arbitrary explicit tail potential. -/
theorem compact_ceiling_grid_charge_potential_of_tail
    (N j : ℕ) (grid Q lowCredit : ℕ → ℝ) (m : ℕ → ℕ)
    (A_tail : ℕ → ℝ)
    (hprefix_credit_nonneg :
      0 ≤ (Finset.range N).sum (fun k =>
        if k < j then lowCredit (m k) else 0))
    (hA_tail_j :
      A_tail j ≤ 1 + (Finset.range N).sum (fun k =>
        if k < j then lowCredit (m k) else 0))
    (hA_tail_N : j ≤ N → 0 ≤ A_tail N)
    (hA_tail_drop : ∀ k ∈ Finset.range N, j ≤ k →
      grid k * Q (m k) - 1 ≤ A_tail k - A_tail (k + 1)) :
    let charge : ℕ → ℝ := fun k =>
      (if j ≤ k then grid k * Q (m k) - 1 else 0) -
        (if k < j then lowCredit (m k) else 0)
    (Finset.range N).sum charge ≤ 1 := by
  classical
  intro charge
  let prefixCredit : ℝ :=
    (Finset.range N).sum (fun k =>
      if k < j then lowCredit (m k) else 0)
  let prefixPartial : ℕ → ℝ := fun n =>
    (Finset.range n).sum (fun k => lowCredit (m k))
  let A : ℕ → ℝ := fun k =>
    if k < j then 1 + prefixPartial k else A_tail k
  have hprefix_eq_range : ∀ {n : ℕ}, n ≤ N →
      (Finset.range N).sum (fun k =>
        if k < n then lowCredit (m k) else 0) =
      prefixPartial n := by
    intro n hnN
    calc
      (Finset.range N).sum (fun k =>
          if k < n then lowCredit (m k) else 0)
          = ((Finset.range N).filter (fun k => k < n)).sum
              (fun k => lowCredit (m k)) := by
            rw [← Finset.sum_filter]
      _ = (Finset.range n).sum (fun k => lowCredit (m k)) := by
            have hfilter :
                (Finset.range N).filter (fun k => k < n) = Finset.range n := by
              ext k
              constructor
              · intro hk
                exact Finset.mem_range.mpr (Finset.mem_filter.mp hk).2
              · intro hk
                have hkn : k < n := Finset.mem_range.mp hk
                exact Finset.mem_filter.mpr
                  ⟨Finset.mem_range.mpr (lt_of_lt_of_le hkn hnN), hkn⟩
            rw [hfilter]
      _ = prefixPartial n := rfl
  have hA0 : A 0 ≤ 1 := by
    by_cases h0j : 0 < j
    · simp [A, prefixPartial, h0j]
    · have hj0 : j = 0 := Nat.eq_zero_of_not_pos h0j
      have htail0 : A_tail 0 ≤ 1 := by
        have h := hA_tail_j
        simpa [prefixCredit, hj0] using h
      simpa [A, h0j] using htail0
  have hAN : 0 ≤ A N := by
    by_cases hNj : N < j
    · have hprefixN :
          prefixCredit = prefixPartial N := by
        calc
          prefixCredit =
              (Finset.range N).sum (fun k =>
                if k < N then lowCredit (m k) else 0) := by
                dsimp [prefixCredit]
                refine Finset.sum_congr rfl ?_
                intro k hk
                have hkN : k < N := Finset.mem_range.mp hk
                have hkj : k < j := lt_trans hkN hNj
                simp [hkN, hkj]
          _ = prefixPartial N := hprefix_eq_range (le_refl N)
      have hpartial_nonneg : 0 ≤ prefixPartial N := by
        simpa [← hprefixN] using hprefix_credit_nonneg
      simp [A, hNj]
      linarith
    · have hjN : j ≤ N := Nat.le_of_not_gt hNj
      simp [A, hNj]
      exact hA_tail_N hjN
  have hdrop : ∀ k ∈ Finset.range N, charge k ≤ A k - A (k + 1) := by
    intro k hk
    by_cases hklt : k < j
    · have hnot_tail : ¬ j ≤ k := by omega
      by_cases hksucc : k + 1 < j
      · have hsum_succ :
            prefixPartial (k + 1) =
              prefixPartial k + lowCredit (m k) := by
          simp [prefixPartial, Finset.sum_range_succ]
        simp [charge, A, hklt, hnot_tail, hksucc, hsum_succ]
      · have hsucc_eq : k + 1 = j := by omega
        have hjN : j ≤ N := by
          have hkN : k < N := Finset.mem_range.mp hk
          omega
        have hprefix_j : prefixCredit = prefixPartial j := by
          simpa [prefixCredit] using hprefix_eq_range (n := j) hjN
        have htail_boundary :
            A_tail j ≤ 1 + prefixPartial (k + 1) := by
          have h : A_tail j ≤ 1 + prefixCredit := by
            simpa [prefixCredit] using hA_tail_j
          rw [hprefix_j] at h
          simpa [hsucc_eq] using h
        have hsum_succ :
            prefixPartial (k + 1) =
              prefixPartial k + lowCredit (m k) := by
          simp [prefixPartial, Finset.sum_range_succ]
        simp [charge, A, hklt, hnot_tail, hksucc, hsucc_eq]
        linarith
    · have hjk : j ≤ k := Nat.le_of_not_gt hklt
      have hnot_succ : ¬ k + 1 < j := by omega
      have htail := hA_tail_drop k hk hjk
      simp [charge, A, hklt, hjk, hnot_succ]
      linarith
  exact compact_ceiling_grid_charge_sum_le_one_of_drop charge A N hA0 hAN hdrop

/-- Single realized compact-ceiling bucket as a finite drop potential.

Aligns with the bucket-local part of Lan Corollary 8.3 / Eq. (8.1.79): the
corrected residual/increment endpoint expression is the initial value of a
local potential whose successive drops pay the literal signed rows in that
bucket. Candidate audit: checked pre-searched process/update candidates,
SOptLib `sum_Icc_sub_succ`, Mathlib `Finset.sum_eq_sum_Ico_succ_bot`, and
target helpers `compact_ceiling_grid_actual_bucket_residual_increment_form`,
`compact_ceiling_grid_residual_increment_bucket_eq_signed_interval`, and
`compact_ceiling_grid_endpoint_deficit_lt_cubic_increment`; the process
candidates are unrelated, the telescope APIs provide only the local summation
mechanics, and the residual/increment helper is the matching source-specific
initial-value bridge. -/
theorem compact_ceiling_grid_single_bucket_tail_drop_potential
    (a b r : ℕ) (grid R Q H : ℕ → ℝ)
    (hR_def : ∀ r,
      R r =
        (H r * ((r : ℝ) ^ 2 + 3 * (r : ℝ) + 2) -
          (3 * (r : ℝ) ^ 2 + 7 * (r : ℝ))) /
          ((r : ℝ) * ((r : ℝ) + 3) ^ 2))
    (hQ_def : ∀ r,
      Q r =
        (((((r : ℝ) + 1) * ((r : ℝ) + 2) / ((r : ℝ) + 3) ^ 2) *
          (1 + H r / (r : ℝ))) /
          (r : ℝ)))
    (hr : 9 ≤ r) (hab : a ≤ b) :
    ∃ A_bucket : ℕ → ℝ,
      A_bucket a =
        ((Finset.Icc a b).card : ℝ) *
            (H r / (r : ℝ) -
              Q r * ((r : ℝ) - grid b) -
              Q r * ((r : ℝ) * (3 * (r : ℝ) + 7) /
                (((r : ℝ) + 1) * ((r : ℝ) + 2)))) -
          Q r *
            (Finset.Ico a b).sum (fun k =>
              (((k - a + 1 : ℕ) : ℝ) * (grid (k + 1) - grid k))) ∧
      A_bucket (b + 1) = 0 ∧
      ∀ k ∈ Finset.Icc a b,
        grid k * Q r - 1 ≤ A_bucket k - A_bucket (k + 1) := by
  classical
  let row : ℕ → ℝ := fun k => grid k * Q r - 1
  let A_bucket : ℕ → ℝ := fun n => (Finset.Ico n (b + 1)).sum row
  refine ⟨A_bucket, ?_, ?_, ?_⟩
  · have hbucket :=
      compact_ceiling_grid_residual_increment_bucket_eq_signed_interval
        a b r grid R Q H hR_def hQ_def hr hab
    calc
      A_bucket a = (Finset.Icc a b).sum row := by
        dsimp [A_bucket, row]
        rw [Finset.Ico_add_one_right_eq_Icc]
      _ =
        ((Finset.Icc a b).card : ℝ) *
            (H r / (r : ℝ) -
              Q r * ((r : ℝ) - grid b) -
              Q r * ((r : ℝ) * (3 * (r : ℝ) + 7) /
                (((r : ℝ) + 1) * ((r : ℝ) + 2)))) -
          Q r *
            (Finset.Ico a b).sum (fun k =>
              (((k - a + 1 : ℕ) : ℝ) * (grid (k + 1) - grid k))) := by
          simpa [row] using hbucket.symm
  · simp [A_bucket]
  · intro k hk
    have hk_le_b : k ≤ b := (Finset.mem_Icc.mp hk).2
    have hk_lt_succ : k < b + 1 := Nat.lt_succ_of_le hk_le_b
    have hsplit :
        A_bucket k = row k + A_bucket (k + 1) := by
      dsimp [A_bucket]
      rw [Finset.sum_eq_sum_Ico_succ_bot hk_lt_succ]
    rw [hsplit]
    linarith

/-- Single realized compact-ceiling bucket as a pure-`R` drop potential.

Aligns with Lan Corollary 8.3 / Eq. (8.1.79): adding the explicit
`Q r * ((r : ℝ) - grid k)` deficit suffix to the signed bucket potential turns
the signed-row drops into literal pure-`R` drops on the same bucket. Candidate
audit: considered `compact_ceiling_grid_single_bucket_tail_drop_potential`,
`finite_ordered_bucket_potentials_stitch_of_carry`, SOptLib
`sum_range_sub_succ_le_first_of_last_nonneg`, and downstream
`compact_ceiling_grid_pure_R_nonmax_bucket_boundary_with_deficit_carry`; the
signed bucket helper is the matching acyclic primitive, the stitch/telescope
helpers are consumers, and the downstream pure-`R` boundary helper occurs after
the active frontier. -/
theorem compact_ceiling_grid_single_bucket_pure_R_drop_potential
    (a b r : ℕ) (grid R Q H : ℕ → ℝ)
    (hH_def : ∀ r, H r = (Finset.range r).sum (fun i => 1 / ((i : ℝ) + 1)))
    (hR_def : ∀ r,
      R r =
        (H r * ((r : ℝ) ^ 2 + 3 * (r : ℝ) + 2) -
          (3 * (r : ℝ) ^ 2 + 7 * (r : ℝ))) /
          ((r : ℝ) * ((r : ℝ) + 3) ^ 2))
    (hQ_def : ∀ r,
      Q r =
        (((((r : ℝ) + 1) * ((r : ℝ) + 2) / ((r : ℝ) + 3) ^ 2) *
          (1 + H r / (r : ℝ))) /
          (r : ℝ)))
    (hr : 9 ≤ r) (hab : a ≤ b) :
    ∃ A_bucket : ℕ → ℝ,
      A_bucket a = ((Finset.Icc a b).card : ℝ) * R r ∧
      A_bucket (b + 1) = 0 ∧
      ∀ k ∈ Finset.Icc a b,
        R r ≤ A_bucket k - A_bucket (k + 1) := by
  classical
  rcases
      compact_ceiling_grid_single_bucket_tail_drop_potential
        a b r grid R Q H hR_def hQ_def hr hab with
    ⟨A_signed, hA_signed_init, hA_signed_terminal, hA_signed_drop⟩
  let deficitSuffix : ℕ → ℝ := fun n =>
    Q r * (Finset.Ico n (b + 1)).sum (fun k => (r : ℝ) - grid k)
  let A_bucket : ℕ → ℝ := fun n => A_signed n + deficitSuffix n
  refine ⟨A_bucket, ?_, ?_, ?_⟩
  · have hactual :=
      compact_ceiling_grid_actual_bucket_residual_increment_form
        a b r grid R Q H hR_def hQ_def hr hab
    have hdeficit_Ico :
        (Finset.Ico a (b + 1)).sum (fun k => (r : ℝ) - grid k) =
          (Finset.Icc a b).sum (fun k => (r : ℝ) - grid k) := by
      rw [Finset.Ico_add_one_right_eq_Icc]
    calc
      A_bucket a =
          A_signed a +
            Q r * (Finset.Ico a (b + 1)).sum
              (fun k => (r : ℝ) - grid k) := rfl
      _ =
          (((Finset.Icc a b).card : ℝ) * R r -
              Q r * (Finset.Icc a b).sum (fun k => (r : ℝ) - grid k)) +
            Q r * (Finset.Icc a b).sum (fun k => (r : ℝ) - grid k) := by
            rw [hA_signed_init, hdeficit_Ico]
            rw [← hactual]
      _ = ((Finset.Icc a b).card : ℝ) * R r := by ring
  · simp [A_bucket, deficitSuffix, hA_signed_terminal]
  · intro k hk
    have hk_le_b : k ≤ b := (Finset.mem_Icc.mp hk).2
    have hk_lt_succ : k < b + 1 := Nat.lt_succ_of_le hk_le_b
    have hdeficit_split :
        deficitSuffix k =
          Q r * ((r : ℝ) - grid k) + deficitSuffix (k + 1) := by
      have hsum_split :
          (Finset.Ico k (b + 1)).sum (fun t => (r : ℝ) - grid t) =
            ((r : ℝ) - grid k) +
              (Finset.Ico (k + 1) (b + 1)).sum
                (fun t => (r : ℝ) - grid t) := by
        rw [Finset.sum_eq_sum_Ico_succ_bot hk_lt_succ]
      dsimp [deficitSuffix]
      rw [hsum_split]
      ring
    have hrow_split :
        grid k * Q r - 1 =
          (grid k - (r : ℝ)) * Q r + R r := by
      have hr_pos : 0 < r := by omega
      simpa [hH_def r, hR_def r, hQ_def r] using
        compact_ceiling_grid_signed_row_eq (grid k) hr_pos
    have hrow :
        R r = (grid k * Q r - 1) + Q r * ((r : ℝ) - grid k) := by
      calc
        R r = (grid k * Q r - 1) - (grid k - (r : ℝ)) * Q r := by
          linarith
        _ = (grid k * Q r - 1) + Q r * ((r : ℝ) - grid k) := by ring
    have hdrop_signed := hA_signed_drop k hk
    calc
      R r =
          (grid k * Q r - 1) + Q r * ((r : ℝ) - grid k) := hrow
      _ ≤ (A_signed k - A_signed (k + 1)) +
            (deficitSuffix k - deficitSuffix (k + 1)) := by
          linarith
      _ = A_bucket k - A_bucket (k + 1) := by
          dsimp [A_bucket]
          rw [hdeficit_split]
          ring

/-- The successor of a nonterminal realized bucket starts the next realized
bucket.

Aligns with the ordered-bucket transport needed in Lan Corollary 8.3 /
Eq. (8.1.79): after a monotone realized fiber ends before the horizon, its
successor index belongs to a strictly larger realized bucket and is the
left endpoint of that bucket. Candidate audit: considered target helpers
`compact_ceiling_grid_bucket_interval`,
`compact_ceiling_grid_endpoint_exit_or_terminal`,
`compact_ceiling_grid_endpoint_deficit_lt_cubic_increment`, SOptLib
`finite_image_min_max_attainment_pack`, and Mathlib `Finset.min'_mem` /
`Finset.le_max'`; the endpoint helpers handle grid crossing rather than the
pure order structure, while the SOptLib image-extrema package is not specialized
to filtered monotone fibers. -/
theorem compact_ceiling_grid_next_realized_bucket_min_eq_succ
    (N j r : ℕ) (m : ℕ → ℕ) (hm_mono : Monotone m)
    (hfiber_nonempty :
      ((Finset.range N).filter (fun k => j ≤ k ∧ m k = r)).Nonempty)
    (hsucc :
      ((Finset.range N).filter (fun k => j ≤ k ∧ m k = r)).max'
          hfiber_nonempty + 1 ∈ Finset.range N) :
    let b : ℕ :=
      ((Finset.range N).filter (fun k => j ≤ k ∧ m k = r)).max'
        hfiber_nonempty
    let s : ℕ := m (b + 1)
    s ∈ Finset.image m ((Finset.range N).filter (fun k => j ≤ k)) ∧
      r < s ∧
      ∃ hs :
        ((Finset.range N).filter (fun k => j ≤ k ∧ m k = s)).Nonempty,
        ((Finset.range N).filter (fun k => j ≤ k ∧ m k = s)).min' hs = b + 1 := by
  classical
  dsimp
  let fiberR : Finset ℕ := (Finset.range N).filter (fun k => j ≤ k ∧ m k = r)
  let b : ℕ := fiberR.max' (by simpa [fiberR] using hfiber_nonempty)
  let s : ℕ := m (b + 1)
  have hb_mem : b ∈ fiberR := Finset.max'_mem fiberR (by simpa [fiberR] using hfiber_nonempty)
  have hb_filter :
      b ∈ (Finset.range N).filter (fun k => j ≤ k ∧ m k = r) := by
    simpa [fiberR] using hb_mem
  have hbj : j ≤ b := (Finset.mem_filter.mp hb_filter).2.1
  have hbr : m b = r := (Finset.mem_filter.mp hb_filter).2.2
  have hsucc_range : b + 1 ∈ Finset.range N := by
    simpa [fiberR, b] using hsucc
  have hsucc_tail : b + 1 ∈ (Finset.range N).filter (fun k => j ≤ k) := by
    exact Finset.mem_filter.mpr ⟨hsucc_range, le_trans hbj (Nat.le_succ b)⟩
  have hs_mem :
      s ∈ Finset.image m ((Finset.range N).filter (fun k => j ≤ k)) := by
    exact Finset.mem_image.mpr ⟨b + 1, hsucc_tail, rfl⟩
  let fiberS : Finset ℕ := (Finset.range N).filter (fun k => j ≤ k ∧ m k = s)
  have hsucc_fiberS : b + 1 ∈ fiberS := by
    exact Finset.mem_filter.mpr
      ⟨hsucc_range, le_trans hbj (Nat.le_succ b), rfl⟩
  have hs_nonempty : fiberS.Nonempty := ⟨b + 1, hsucc_fiberS⟩
  have hr_le_s : r ≤ s := by
    calc
      r = m b := hbr.symm
      _ ≤ m (b + 1) := hm_mono (Nat.le_succ b)
      _ = s := rfl
  have hr_ne_s : r ≠ s := by
    intro hrs
    have hsucc_fiberR : b + 1 ∈ fiberR := by
      exact Finset.mem_filter.mpr
        ⟨hsucc_range, le_trans hbj (Nat.le_succ b), by
          dsimp [s] at hrs
          exact hrs.symm⟩
    have hle := Finset.le_max' fiberR (b + 1) hsucc_fiberR
    have : b + 1 ≤ b := by simpa [b] using hle
    omega
  have hr_lt_s : r < s := lt_of_le_of_ne hr_le_s hr_ne_s
  have hmin_ge : b + 1 ≤ fiberS.min' hs_nonempty := by
    have hmin_mem : fiberS.min' hs_nonempty ∈ fiberS :=
      Finset.min'_mem fiberS hs_nonempty
    have hmin_filter :
        fiberS.min' hs_nonempty ∈
          (Finset.range N).filter (fun k => j ≤ k ∧ m k = s) := by
      simpa [fiberS] using hmin_mem
    by_contra hnot
    have hlt : fiberS.min' hs_nonempty < b + 1 := Nat.lt_of_not_ge hnot
    have hle_b : fiberS.min' hs_nonempty ≤ b := by omega
    have hm_le_r : m (fiberS.min' hs_nonempty) ≤ r := by
      calc
        m (fiberS.min' hs_nonempty) ≤ m b := hm_mono hle_b
        _ = r := hbr
    have hs_le_r : s ≤ r := by
      simpa [(Finset.mem_filter.mp hmin_filter).2.2] using hm_le_r
    omega
  have hmin_le : fiberS.min' hs_nonempty ≤ b + 1 :=
    Finset.min'_le fiberS (b + 1) hsucc_fiberS
  refine ⟨by simpa [s] using hs_mem, by simpa [s] using hr_lt_s, ?_⟩
  refine ⟨by simpa [fiberS, s] using hs_nonempty, ?_⟩
  have hmin_eq : fiberS.min' hs_nonempty = b + 1 := le_antisymm hmin_le hmin_ge
  simpa [fiberS, s, b] using hmin_eq

/-- Adjacent realized-bucket endpoint transport for the compact ceiling grid.

Aligns with Lan Corollary 8.3 / Eq. (8.1.79): for a nonterminal realized
bucket, the endpoint ceiling deficit is paid by the grid jump into the next
realized bucket. Candidate audit: checked pre-searched SOptLib
`finite_image_min_max_attainment_pack` and
`sum_range_sub_succ_le_first_of_last_nonneg`, plus local helpers
`compact_ceiling_grid_next_realized_bucket_min_eq_succ` and
`compact_ceiling_grid_endpoint_deficit_lt_cubic_increment`; the SOptLib lemmas
only package generic extrema/telescopes, while the two local helpers are the
source-specific order and endpoint facts composed here. -/
theorem compact_ceiling_grid_adjacent_bucket_endpoint_transport
    (N j r : ℕ) (c : ℝ) (grid : ℕ → ℝ) (m : ℕ → ℕ)
    (hm_mono : Monotone m)
    (hgrid_increment : ∀ k,
      grid (k + 1) - grid k =
        c * (((k + 2 : ℕ) : ℝ)) * (3 * (k : ℝ) + 7))
    (hfiber_nonempty :
      ((Finset.range N).filter (fun k => j ≤ k ∧ m k = r)).Nonempty)
    (hsucc :
      ((Finset.range N).filter (fun k => j ≤ k ∧ m k = r)).max'
          hfiber_nonempty + 1 ∈ Finset.range N)
    (hendpoint :
      0 ≤ (r : ℝ) -
          grid (((Finset.range N).filter (fun k => j ≤ k ∧ m k = r)).max'
            hfiber_nonempty) ∧
        (r : ℝ) -
            grid (((Finset.range N).filter (fun k => j ≤ k ∧ m k = r)).max'
              hfiber_nonempty) <
          c * (((((Finset.range N).filter (fun k => j ≤ k ∧ m k = r)).max'
              hfiber_nonempty) + 2 : ℕ) : ℝ) *
            (3 * ((((Finset.range N).filter (fun k => j ≤ k ∧ m k = r)).max'
              hfiber_nonempty : ℕ) : ℝ) + 7)) :
    let fiberR : Finset ℕ :=
      (Finset.range N).filter (fun k => j ≤ k ∧ m k = r)
    let b : ℕ := fiberR.max' hfiber_nonempty
    let s : ℕ := m (b + 1)
    s ∈ Finset.image m ((Finset.range N).filter (fun k => j ≤ k)) ∧
      r < s ∧
      ∃ hs : ((Finset.range N).filter (fun k => j ≤ k ∧ m k = s)).Nonempty,
        ((Finset.range N).filter (fun k => j ≤ k ∧ m k = s)).min' hs = b + 1 ∧
          0 ≤ (r : ℝ) - grid b ∧
          (r : ℝ) - grid b <
            grid (((Finset.range N).filter (fun k => j ≤ k ∧ m k = s)).min' hs) -
              grid b := by
  classical
  dsimp
  let fiberR : Finset ℕ :=
    (Finset.range N).filter (fun k => j ≤ k ∧ m k = r)
  let b : ℕ := fiberR.max' hfiber_nonempty
  let s : ℕ := m (b + 1)
  have hnext :=
    compact_ceiling_grid_next_realized_bucket_min_eq_succ
      N j r m hm_mono hfiber_nonempty hsucc
  rcases hnext with ⟨hs_mem, hrs, hs_nonempty, hmin⟩
  refine ⟨by simpa [fiberR, b, s] using hs_mem, by simpa [s] using hrs, ?_⟩
  refine ⟨by simpa [s] using hs_nonempty, ?_⟩
  refine ⟨by simpa [fiberR, b, s] using hmin, ?_, ?_⟩
  · simpa [fiberR, b] using hendpoint.1
  · calc
      (r : ℝ) - grid b
          <
        c * (((b + 2 : ℕ) : ℝ)) * (3 * (b : ℝ) + 7) := by
          simpa [fiberR, b] using hendpoint.2
      _ = grid (b + 1) - grid b := by
          rw [hgrid_increment b]
      _ =
        grid (((Finset.range N).filter (fun k => j ≤ k ∧ m k = s)).min'
            (by simpa [s] using hs_nonempty)) -
          grid b := by
          have hmin_s :
              ((Finset.range N).filter (fun k => j ≤ k ∧ m k = s)).min'
                  (by simpa [s] using hs_nonempty) = b + 1 := by
            simpa [fiberR, b, s] using hmin
          rw [hmin_s]

/-- Telescope a finite ordered successor chain from its first element.

This is pure finite-order infrastructure for the ordered realized-bucket step in
Lan Corollary 8.3 / Eq. (8.1.79): local drops along the immediate successor in a
nonempty finite set sum to the first boundary minus the terminal boundary.
Candidate audit: checked SOptLib `sum_range_sub_succ_le_first_of_last_nonneg`,
`finite_image_min_max_attainment_pack`, and target compact-grid bucket/tail
helpers; the range telescope is indexed by consecutive naturals, the extrema
package only supplies min/max membership, and the compact-grid helpers do not
provide a generic finite-chain successor telescope. -/
theorem finset_sum_le_min_sub_terminal_of_ordered_successor
    (B : Finset ℕ) (init Phi : ℕ → ℝ) (next : ℕ → ℕ) (terminal : ℝ)
    (hB : B.Nonempty)
    (hnext_mem : ∀ r (hr : r ∈ B), r ≠ B.max' hB → next r ∈ B)
    (hnext_gt : ∀ r (hr : r ∈ B), r ≠ B.max' hB → r < next r)
    (hnext_le_of_between :
      ∀ r (hr : r ∈ B), r ≠ B.max' hB →
        ∀ x ∈ B, r < x → next r ≤ x)
    (hdrop : ∀ r (hr : r ∈ B), r ≠ B.max' hB →
      init r ≤ Phi r - Phi (next r))
    (hterminal : init (B.max' hB) ≤ Phi (B.max' hB) - terminal) :
    B.sum init ≤ Phi (B.min' hB) - terminal := by
  classical
  induction hcard : B.card using Nat.strong_induction_on generalizing B with
  | h n ih =>
    by_cases hmin_eq_max : B.min' hB = B.max' hB
    · have hB_single : B = {B.max' hB} := by
        ext x
        constructor
        · intro hx
          have hle_max : x ≤ B.max' hB := Finset.le_max' B x hx
          have hmin_le : B.min' hB ≤ x := Finset.min'_le B x hx
          have hx_eq : x = B.max' hB := by omega
          simpa [hx_eq]
        · intro hx
          rw [Finset.mem_singleton] at hx
          rw [hx]
          exact Finset.max'_mem B hB
      calc
        B.sum init = init (B.max' hB) := by
          calc
            B.sum init = ({B.max' hB} : Finset ℕ).sum init := by
              exact congrArg (fun s : Finset ℕ => s.sum init) hB_single
            _ = init (B.max' hB) := by
              simp only [Finset.sum_singleton]
        _ ≤ Phi (B.max' hB) - terminal := hterminal
        _ = Phi (B.min' hB) - terminal := by rw [hmin_eq_max]
    · let rmin : ℕ := B.min' hB
      have hrmin : rmin ∈ B := Finset.min'_mem B hB
      have hrmin_ne_max : rmin ≠ B.max' hB := by
        intro h
        exact hmin_eq_max h
      let B' : Finset ℕ := B.erase rmin
      have hB'_nonempty : B'.Nonempty := by
        refine ⟨B.max' hB, ?_⟩
        exact Finset.mem_erase.mpr ⟨by
          intro hmax_eq_min
          exact hmin_eq_max hmax_eq_min.symm, Finset.max'_mem B hB⟩
      have hcard_lt : B'.card < B.card := by
        simpa [B', hrmin] using Finset.card_erase_lt_of_mem hrmin
      have hmax_B' : B'.max' hB'_nonempty = B.max' hB := by
        apply le_antisymm
        · exact Finset.le_max' B (B'.max' hB'_nonempty)
            (by
              have hmem := Finset.max'_mem B' hB'_nonempty
              exact (Finset.mem_erase.mp hmem).2)
        · exact Finset.le_max' B' (B.max' hB)
            (by
              exact Finset.mem_erase.mpr ⟨by
                intro hmax_eq_min
                exact hmin_eq_max hmax_eq_min.symm, Finset.max'_mem B hB⟩)
      have hnext_rmin_mem_B' : next rmin ∈ B' := by
        have hmemB := hnext_mem rmin hrmin hrmin_ne_max
        exact Finset.mem_erase.mpr ⟨by
          intro hnext_eq
          have hgt := hnext_gt rmin hrmin hrmin_ne_max
          omega, hmemB⟩
      have hmin_B' : B'.min' hB'_nonempty = next rmin := by
        apply le_antisymm
        · exact Finset.min'_le B' (next rmin) hnext_rmin_mem_B'
        · have hmin_mem := Finset.min'_mem B' hB'_nonempty
          have hmin_mem_B : B'.min' hB'_nonempty ∈ B :=
            (Finset.mem_erase.mp hmin_mem).2
          have hmin_ne_rmin : B'.min' hB'_nonempty ≠ rmin :=
            (Finset.mem_erase.mp hmin_mem).1
          have hrmin_lt_min : rmin < B'.min' hB'_nonempty := by
            have hle := Finset.min'_le B (B'.min' hB'_nonempty) hmin_mem_B
            omega
          exact hnext_le_of_between rmin hrmin hrmin_ne_max
            (B'.min' hB'_nonempty) hmin_mem_B hrmin_lt_min
      have hnext_mem' :
          ∀ r (hr : r ∈ B'), r ≠ B'.max' hB'_nonempty → next r ∈ B' := by
        intro r hr hr_ne
        have hrB : r ∈ B := (Finset.mem_erase.mp hr).2
        have hr_ne_max : r ≠ B.max' hB := by
          simpa [hmax_B'] using hr_ne
        have hnextB := hnext_mem r hrB hr_ne_max
        exact Finset.mem_erase.mpr ⟨by
          intro hnext_eq_min
          have hnext_le_r : next r ≤ r := by
            rw [hnext_eq_min]
            exact Finset.min'_le B r hrB
          have hgt := hnext_gt r hrB hr_ne_max
          omega, hnextB⟩
      have hnext_gt' :
          ∀ r (hr : r ∈ B'), r ≠ B'.max' hB'_nonempty → r < next r := by
        intro r hr hr_ne
        exact hnext_gt r (Finset.mem_erase.mp hr).2 (by simpa [hmax_B'] using hr_ne)
      have hnext_le_between' :
          ∀ r (hr : r ∈ B'), r ≠ B'.max' hB'_nonempty →
            ∀ x ∈ B', r < x → next r ≤ x := by
        intro r hr hr_ne x hx hlt
        exact hnext_le_of_between r (Finset.mem_erase.mp hr).2
          (by simpa [hmax_B'] using hr_ne) x (Finset.mem_erase.mp hx).2 hlt
      have hdrop' :
          ∀ r (hr : r ∈ B'), r ≠ B'.max' hB'_nonempty →
            init r ≤ Phi r - Phi (next r) := by
        intro r hr hr_ne
        exact hdrop r (Finset.mem_erase.mp hr).2 (by simpa [hmax_B'] using hr_ne)
      have hterminal' :
          init (B'.max' hB'_nonempty) ≤
            Phi (B'.max' hB'_nonempty) - terminal := by
        simpa [hmax_B'] using hterminal
      have htail :
          B'.sum init ≤ Phi (B'.min' hB'_nonempty) - terminal :=
        ih B'.card (by omega) B' hB'_nonempty hnext_mem' hnext_gt'
          hnext_le_between' hdrop' hterminal' rfl
      have hsum_erase :
          B.sum init = init rmin + B'.sum init := by
        calc
          B.sum init = B'.sum init + init rmin := by
            simpa [B', rmin] using (Finset.sum_erase_add B init hrmin).symm
          _ = init rmin + B'.sum init := by ring
      calc
        B.sum init = init rmin + B'.sum init := hsum_erase
        _ ≤ (Phi rmin - Phi (next rmin)) +
              (Phi (B'.min' hB'_nonempty) - terminal) := by
            exact add_le_add (hdrop rmin hrmin hrmin_ne_max) htail
        _ = Phi (B.min' hB) - terminal := by
            rw [hmin_B']
            dsimp [rmin]
            ring

/-- Telescope an ordered successor chain with an explicit carried boundary term.

Aligns with Lan Corollary 8.3 / Eq. (8.1.79): this is the carry-aware scalar
form of the ordered realized-bucket telescope, where each local bucket start is
paid by a potential drop plus incoming carry minus outgoing carry. Candidate
audit: considered target helpers `finset_sum_le_min_sub_terminal_of_ordered_successor`,
`finite_ordered_bucket_potentials_stitch_of_carry`, and SOptLib
`sum_range_sub_succ_le_first_of_last_nonneg`; the first is the exact ordered
telescope and is specialized here, while the bucket-potential stitch is
pointwise row infrastructure and the SOptLib range telescope lacks realized
successor/carry indexing. -/
theorem finset_sum_le_min_sub_terminal_with_ordered_carry
    (B : Finset ℕ) (init Phi carry : ℕ → ℝ) (next : ℕ → ℕ) (terminal : ℝ)
    (hB : B.Nonempty)
    (hnext_mem : ∀ r (hr : r ∈ B), r ≠ B.max' hB → next r ∈ B)
    (hnext_gt : ∀ r (hr : r ∈ B), r ≠ B.max' hB → r < next r)
    (hnext_le_of_between :
      ∀ r (hr : r ∈ B), r ≠ B.max' hB →
        ∀ x ∈ B, r < x → next r ≤ x)
    (hdrop : ∀ r (hr : r ∈ B), r ≠ B.max' hB →
      init r + carry (next r) ≤ Phi r - Phi (next r) + carry r)
    (hterminal :
      init (B.max' hB) ≤ Phi (B.max' hB) - terminal + carry (B.max' hB)) :
    B.sum init ≤ Phi (B.min' hB) - terminal + carry (B.min' hB) := by
  classical
  let PhiCarry : ℕ → ℝ := fun r => Phi r + carry r
  have hdrop' : ∀ r (hr : r ∈ B), r ≠ B.max' hB →
      init r ≤ PhiCarry r - PhiCarry (next r) := by
    intro r hr hr_ne
    have h := hdrop r hr hr_ne
    dsimp [PhiCarry]
    linarith
  have hterminal' :
      init (B.max' hB) ≤ PhiCarry (B.max' hB) - terminal := by
    have h := hterminal
    dsimp [PhiCarry]
    linarith
  have htelescope :
      B.sum init ≤ PhiCarry (B.min' hB) - terminal :=
    finset_sum_le_min_sub_terminal_of_ordered_successor
      B init PhiCarry next terminal hB hnext_mem hnext_gt
      hnext_le_of_between hdrop' hterminal'
  dsimp [PhiCarry] at htelescope ⊢
  linarith

/-- Erased-max form of the ordered successor telescope.

Aligns with Lan Corollary 8.3 / Eq. (8.1.79) after the terminal bucket is split
off: nonterminal edge budgets telescope along the realized successor chain and
the maximal bucket contributes the terminal boundary term. Candidate audit:
considered the target helper `finset_sum_le_min_sub_terminal_of_ordered_successor`
and SOptLib `sum_range_sub_succ_le_first_of_last_nonneg`; the target helper is
the exact finite-order telescope, while this lemma is only its erased-max
specialization needed by the current bucket endpoint proof shape. -/
theorem finset_erase_sum_add_terminal_le_min_sub_terminal_of_ordered_successor
    (B : Finset ℕ) (edge Phi : ℕ → ℝ) (next : ℕ → ℕ)
    (terminalBudget terminal : ℝ)
    (hB : B.Nonempty)
    (hnext_mem : ∀ r (hr : r ∈ B), r ≠ B.max' hB → next r ∈ B)
    (hnext_gt : ∀ r (hr : r ∈ B), r ≠ B.max' hB → r < next r)
    (hnext_le_of_between :
      ∀ r (hr : r ∈ B), r ≠ B.max' hB →
        ∀ x ∈ B, r < x → next r ≤ x)
    (hdrop : ∀ r (hr : r ∈ B), r ≠ B.max' hB →
      edge r ≤ Phi r - Phi (next r))
    (hterminal : terminalBudget ≤ Phi (B.max' hB) - terminal) :
    (B.erase (B.max' hB)).sum edge + terminalBudget ≤
      Phi (B.min' hB) - terminal := by
  classical
  let init : ℕ → ℝ := fun r =>
    if r = B.max' hB then terminalBudget else edge r
  have hdrop_init : ∀ r (hr : r ∈ B), r ≠ B.max' hB →
      init r ≤ Phi r - Phi (next r) := by
    intro r hr hr_ne
    dsimp [init]
    rw [if_neg hr_ne]
    exact hdrop r hr hr_ne
  have hterminal_init :
      init (B.max' hB) ≤ Phi (B.max' hB) - terminal := by
    dsimp [init]
    rw [if_pos rfl]
    exact hterminal
  have htelescope :
      B.sum init ≤ Phi (B.min' hB) - terminal :=
    finset_sum_le_min_sub_terminal_of_ordered_successor
      B init Phi next terminal hB hnext_mem hnext_gt hnext_le_of_between
      hdrop_init hterminal_init
  have hsum_erase :
      (B.erase (B.max' hB)).sum init =
        (B.erase (B.max' hB)).sum edge := by
    refine Finset.sum_congr rfl ?_
    intro r hr
    have hr_ne : r ≠ B.max' hB := (Finset.mem_erase.mp hr).1
    dsimp [init]
    rw [if_neg hr_ne]
  have hsum_split :
      B.sum init =
        (B.erase (B.max' hB)).sum edge + terminalBudget := by
    calc
      B.sum init =
          (B.erase (B.max' hB)).sum init + init (B.max' hB) := by
            simpa using
              (Finset.sum_erase_add B init (Finset.max'_mem B hB)).symm
      _ =
          (B.erase (B.max' hB)).sum edge + terminalBudget := by
            rw [hsum_erase]
            dsimp [init]
            rw [if_pos rfl]
  exact le_of_eq_of_le hsum_split.symm htelescope

/-- Stitch realized bucket-local potentials into one high-tail potential.

Aligns with Lan Corollary 8.3 / Eq. (8.1.79): once the source-specific scalar
work supplies a non-cumulative carry certificate between adjacent realized
buckets, this pure finite-indexing lemma turns local bucket drops into the
global pointwise high-tail drop potential. Candidate audit: considered target
helpers `compact_ceiling_grid_charge_potential_of_tail`,
`compact_ceiling_grid_single_bucket_tail_drop_potential`,
`finset_sum_le_min_sub_terminal_of_ordered_successor`,
`finset_erase_sum_add_terminal_le_min_sub_terminal_of_ordered_successor`, and
SOptLib `sum_range_sub_succ_le_first_of_last_nonneg`; they respectively
consume an already-global potential, provide one-bucket drops, or telescope
bucket sums, but none stitches pointwise bucket potentials across realized
successor boundaries. -/
theorem finite_ordered_bucket_potentials_stitch_of_carry
    (N j : ℕ) (grid Q : ℕ → ℝ) (m : ℕ → ℕ)
    (B : Finset ℕ) (fiber : ℕ → Finset ℕ)
    (prefixCredit : ℝ) (bucketPotential : ℕ → ℕ → ℝ)
    (carry : ℕ → ℝ) (next : ℕ → ℕ)
    (hB : B.Nonempty)
    (hmem_tail : ∀ k ∈ Finset.range N, j ≤ k → m k ∈ B)
    (hfiber_nonempty : ∀ r ∈ B, (fiber r).Nonempty)
    (hfiber_mem :
      ∀ r (hr : r ∈ B), ∀ k ∈ fiber r, k ∈ Finset.range N ∧ j ≤ k ∧ m k = r)
    (htail_index_mem_bucket_interval :
      ∀ k ∈ Finset.range N, j ≤ k →
        let r : ℕ := m k
        let fr : Finset ℕ := fiber r
        ∀ hne : fr.Nonempty,
          k ∈ Finset.Icc (fr.min' hne) (fr.max' hne))
    (hsame_bucket_succ :
      ∀ k ∈ Finset.range N, j ≤ k →
        let r : ℕ := m k
        let fr : Finset ℕ := fiber r
        ∀ hne : fr.Nonempty,
          k ∈ Finset.Icc (fr.min' hne) (fr.max' hne) →
            k ≠ fr.max' hne →
              k + 1 ∈ Finset.range N ∧ j ≤ k + 1 ∧ m (k + 1) = r)
    (hmin_bucket_starts_at_j :
      let rmin : ℕ := B.min' hB
      let hrmin : rmin ∈ B := Finset.min'_mem B hB
      let fr : Finset ℕ := fiber rmin
      fr.min' (hfiber_nonempty rmin hrmin) = j)
    (hmin_bucket_value_eq_mj : m j = B.min' hB)
    (hmax_bucket_last_eq_N :
      let rmax : ℕ := B.max' hB
      let hrmax : rmax ∈ B := Finset.max'_mem B hB
      let fr : Finset ℕ := fiber rmax
      fr.max' (hfiber_nonempty rmax hrmax) + 1 = N)
    (hbucketPotential_terminal :
      ∀ r (hr : r ∈ B),
        let fr : Finset ℕ := fiber r
        let hne : fr.Nonempty := hfiber_nonempty r hr
        bucketPotential r (fr.max' hne + 1) = 0)
    (hbucketPotential_drop :
      ∀ r (hr : r ∈ B),
        let fr : Finset ℕ := fiber r
        let hne : fr.Nonempty := hfiber_nonempty r hr
        ∀ k ∈ Finset.Icc (fr.min' hne) (fr.max' hne),
          grid k * Q r - 1 ≤
            bucketPotential r k - bucketPotential r (k + 1))
    (hinitCarry :
      bucketPotential (B.min' hB) j + carry (B.min' hB) ≤ 1 + prefixCredit)
    (hterminalCarry : 0 ≤ carry (B.max' hB))
    (hboundaryCarry :
      ∀ r (hr : r ∈ B), r ≠ B.max' hB →
        let fr : Finset ℕ := fiber r
        let hne : fr.Nonempty := hfiber_nonempty r hr
        let b : ℕ := fr.max' hne
        let s : ℕ := next r
        s ∈ B ∧
          ∃ hs : (fiber s).Nonempty,
            (fiber s).min' hs = b + 1 ∧
              bucketPotential s ((fiber s).min' hs) + carry s ≤ carry r) :
    ∃ A_tail : ℕ → ℝ,
      A_tail j ≤ 1 + prefixCredit ∧
      (j ≤ N → 0 ≤ A_tail N) ∧
      ∀ k ∈ Finset.range N, j ≤ k →
        grid k * Q (m k) - 1 ≤ A_tail k - A_tail (k + 1) := by
  classical
  let rmax : ℕ := B.max' hB
  let A_tail : ℕ → ℝ := fun n =>
    if hn : n < N then
      if hjn : j ≤ n then bucketPotential (m n) n + carry (m n) else 0
    else carry rmax
  refine ⟨A_tail, ?_, ?_, ?_⟩
  · let rmin : ℕ := B.min' hB
    have hrmin : rmin ∈ B := Finset.min'_mem B hB
    let fr : Finset ℕ := fiber rmin
    let hne : fr.Nonempty := hfiber_nonempty rmin hrmin
    have hstart : fr.min' hne = j := by
      simpa [rmin, hrmin, fr, hne] using hmin_bucket_starts_at_j
    have hmin_mem : fr.min' hne ∈ fr := Finset.min'_mem fr hne
    have hj_range : j ∈ Finset.range N := by
      have hinfo := hfiber_mem rmin hrmin (fr.min' hne) hmin_mem
      simpa [hstart] using hinfo.1
    have hjN : j < N := Finset.mem_range.mp hj_range
    have hmj : m j = rmin := by
      simpa [rmin] using hmin_bucket_value_eq_mj
    simpa [A_tail, hjN, hmj, rmin] using hinitCarry
  · intro _hjN
    simp [A_tail, rmax]
    exact hterminalCarry
  · intro k hkN hjk
    let r : ℕ := m k
    have hr : r ∈ B := hmem_tail k hkN hjk
    let fr : Finset ℕ := fiber r
    let hne : fr.Nonempty := hfiber_nonempty r hr
    have hk_interval : k ∈ Finset.Icc (fr.min' hne) (fr.max' hne) := by
      simpa [r, fr, hne] using htail_index_mem_bucket_interval k hkN hjk hne
    have hk_lt_N : k < N := Finset.mem_range.mp hkN
    by_cases hkmax : k = fr.max' hne
    ·
      by_cases hrmax : r = B.max' hB
      · have hsuccN_max : fr.max' hne + 1 = N := by
          simpa [rmax, r, hrmax, fr, hne] using hmax_bucket_last_eq_N
        have hsuccN : k + 1 = N := by
          simpa [hkmax] using hsuccN_max
        have hterm : bucketPotential r (fr.max' hne + 1) = 0 := by
          simpa [fr, hne] using hbucketPotential_terminal r hr
        have hdrop := hbucketPotential_drop r hr k hk_interval
        have hdrop' :
            grid k * Q r - 1 ≤ bucketPotential r k := by
          have hterm' : bucketPotential r (k + 1) = 0 := by
            simpa [hkmax] using hterm
          linarith
        have hgoal :
            grid k * Q r - 1 ≤
              (bucketPotential r k + carry r) - carry rmax := by
          have hrmax' : r = rmax := by simpa [rmax] using hrmax
          have hcarry_eq : carry r = carry rmax := by rw [hrmax']
          linarith
        simpa [A_tail, r, rmax, hsuccN, hrmax, hk_lt_N, hjk] using hgoal
      · rcases hboundaryCarry r hr hrmax with ⟨hs_mem, hs, hmin_next, hcarry⟩
        have hnext_info :=
          hfiber_mem (next r) hs_mem ((fiber (next r)).min' hs)
            (Finset.min'_mem (fiber (next r)) hs)
        have hsucc_range : k + 1 ∈ Finset.range N := by
          simpa [hkmax, hmin_next] using hnext_info.1
        have hsucc_j : j ≤ k + 1 := by
          simpa [hkmax, hmin_next] using hnext_info.2.1
        have hm_succ : m (k + 1) = next r := by
          simpa [hkmax, hmin_next] using hnext_info.2.2
        have hsucc_lt_N : k + 1 < N := Finset.mem_range.mp hsucc_range
        have hterm : bucketPotential r (fr.max' hne + 1) = 0 := by
          simpa [fr, hne] using hbucketPotential_terminal r hr
        have hdrop := hbucketPotential_drop r hr k hk_interval
        have hdrop' :
            grid k * Q r - 1 ≤ bucketPotential r k := by
          have hterm' : bucketPotential r (k + 1) = 0 := by
            simpa [hkmax] using hterm
          linarith
        have hcarry' :
            bucketPotential (next r) (k + 1) + carry (next r) ≤ carry r := by
          simpa [hkmax, hmin_next] using hcarry
        have hgoal :
            grid k * Q r - 1 ≤
              (bucketPotential r k + carry r) -
                (bucketPotential (next r) (k + 1) + carry (next r)) := by
          linarith
        simpa [A_tail, r, hm_succ, hsucc_lt_N, hsucc_j, hk_lt_N, hjk] using hgoal
    · rcases hsame_bucket_succ k hkN hjk hne hk_interval hkmax with
        ⟨hsucc_range, hsucc_j, hm_succ⟩
      have hsucc_lt_N : k + 1 < N := Finset.mem_range.mp hsucc_range
      have hdrop := hbucketPotential_drop r hr k hk_interval
      have hgoal :
          grid k * Q r - 1 ≤
            (bucketPotential r k + carry r) -
              (bucketPotential r (k + 1) + carry r) := by
        linarith
      simpa [A_tail, r, hm_succ, hk_lt_N, hjk, hsucc_lt_N, hsucc_j] using hgoal

/-- Stitch realized bucket-local pure-`R` potentials into one high-tail potential.

Aligns with Lan Corollary 8.3 / Eq. (8.1.79): the source-derived compact-policy
scalar simplification needs the literal pure-`R` row after bucket-local deficit
terms have already been absorbed. Candidate audit: considered the pre-searched
`finite_ordered_bucket_potentials_stitch_of_carry`, `finset_sum_le_min_sub_terminal_with_ordered_carry`,
`finite_ordered_carry_certificate_of_start_sum_bound`, and SOptLib
`sum_range_sub_succ_le_first_of_last_nonneg`; the signed stitch has row
`grid k * Q r - 1`, the carry lemmas only build/telescope bucket-start carries,
and the range telescope lacks the realized bucket successor boundary, so a pure
row variant is needed here. -/
theorem finite_ordered_bucket_pure_R_potentials_stitch_of_carry
    (N j : ℕ) (R : ℕ → ℝ) (m : ℕ → ℕ)
    (B : Finset ℕ) (fiber : ℕ → Finset ℕ)
    (prefixCredit : ℝ) (bucketPotential : ℕ → ℕ → ℝ)
    (carry : ℕ → ℝ) (next : ℕ → ℕ)
    (hB : B.Nonempty)
    (hmem_tail : ∀ k ∈ Finset.range N, j ≤ k → m k ∈ B)
    (hfiber_nonempty : ∀ r ∈ B, (fiber r).Nonempty)
    (hfiber_mem :
      ∀ r (hr : r ∈ B), ∀ k ∈ fiber r, k ∈ Finset.range N ∧ j ≤ k ∧ m k = r)
    (htail_index_mem_bucket_interval :
      ∀ k ∈ Finset.range N, j ≤ k →
        let r : ℕ := m k
        let fr : Finset ℕ := fiber r
        ∀ hne : fr.Nonempty,
          k ∈ Finset.Icc (fr.min' hne) (fr.max' hne))
    (hsame_bucket_succ :
      ∀ k ∈ Finset.range N, j ≤ k →
        let r : ℕ := m k
        let fr : Finset ℕ := fiber r
        ∀ hne : fr.Nonempty,
          k ∈ Finset.Icc (fr.min' hne) (fr.max' hne) →
            k ≠ fr.max' hne →
              k + 1 ∈ Finset.range N ∧ j ≤ k + 1 ∧ m (k + 1) = r)
    (hmin_bucket_starts_at_j :
      let rmin : ℕ := B.min' hB
      let hrmin : rmin ∈ B := Finset.min'_mem B hB
      let fr : Finset ℕ := fiber rmin
      fr.min' (hfiber_nonempty rmin hrmin) = j)
    (hmin_bucket_value_eq_mj : m j = B.min' hB)
    (hmax_bucket_last_eq_N :
      let rmax : ℕ := B.max' hB
      let hrmax : rmax ∈ B := Finset.max'_mem B hB
      let fr : Finset ℕ := fiber rmax
      fr.max' (hfiber_nonempty rmax hrmax) + 1 = N)
    (hbucketPotential_terminal :
      ∀ r (hr : r ∈ B),
        let fr : Finset ℕ := fiber r
        let hne : fr.Nonempty := hfiber_nonempty r hr
        bucketPotential r (fr.max' hne + 1) = 0)
    (hbucketPotential_drop :
      ∀ r (hr : r ∈ B),
        let fr : Finset ℕ := fiber r
        let hne : fr.Nonempty := hfiber_nonempty r hr
        ∀ k ∈ Finset.Icc (fr.min' hne) (fr.max' hne),
          R r ≤ bucketPotential r k - bucketPotential r (k + 1))
    (hinitCarry :
      bucketPotential (B.min' hB) j + carry (B.min' hB) ≤ 1 + prefixCredit)
    (hterminalCarry : 0 ≤ carry (B.max' hB))
    (hboundaryCarry :
      ∀ r (hr : r ∈ B), r ≠ B.max' hB →
        let fr : Finset ℕ := fiber r
        let hne : fr.Nonempty := hfiber_nonempty r hr
        let b : ℕ := fr.max' hne
        let s : ℕ := next r
        s ∈ B ∧
          ∃ hs : (fiber s).Nonempty,
            (fiber s).min' hs = b + 1 ∧
              bucketPotential s ((fiber s).min' hs) + carry s ≤ carry r) :
    ∃ A_tail : ℕ → ℝ,
      A_tail j ≤ 1 + prefixCredit ∧
      (j ≤ N → 0 ≤ A_tail N) ∧
      ∀ k ∈ Finset.range N, j ≤ k →
        R (m k) ≤ A_tail k - A_tail (k + 1) := by
  classical
  let rmax : ℕ := B.max' hB
  let A_tail : ℕ → ℝ := fun n =>
    if hn : n < N then
      if hjn : j ≤ n then bucketPotential (m n) n + carry (m n) else 0
    else carry rmax
  refine ⟨A_tail, ?_, ?_, ?_⟩
  · let rmin : ℕ := B.min' hB
    have hrmin : rmin ∈ B := Finset.min'_mem B hB
    let fr : Finset ℕ := fiber rmin
    let hne : fr.Nonempty := hfiber_nonempty rmin hrmin
    have hstart : fr.min' hne = j := by
      simpa [rmin, hrmin, fr, hne] using hmin_bucket_starts_at_j
    have hmin_mem : fr.min' hne ∈ fr := Finset.min'_mem fr hne
    have hj_range : j ∈ Finset.range N := by
      have hinfo := hfiber_mem rmin hrmin (fr.min' hne) hmin_mem
      simpa [hstart] using hinfo.1
    have hjN : j < N := Finset.mem_range.mp hj_range
    have hmj : m j = rmin := by
      simpa [rmin] using hmin_bucket_value_eq_mj
    simpa [A_tail, hjN, hmj, rmin] using hinitCarry
  · intro _hjN
    simp [A_tail, rmax]
    exact hterminalCarry
  · intro k hkN hjk
    let r : ℕ := m k
    have hr : r ∈ B := hmem_tail k hkN hjk
    let fr : Finset ℕ := fiber r
    let hne : fr.Nonempty := hfiber_nonempty r hr
    have hk_interval : k ∈ Finset.Icc (fr.min' hne) (fr.max' hne) := by
      simpa [r, fr, hne] using htail_index_mem_bucket_interval k hkN hjk hne
    have hk_lt_N : k < N := Finset.mem_range.mp hkN
    by_cases hkmax : k = fr.max' hne
    · by_cases hrmax : r = B.max' hB
      · have hsuccN_max : fr.max' hne + 1 = N := by
          simpa [rmax, r, hrmax, fr, hne] using hmax_bucket_last_eq_N
        have hsuccN : k + 1 = N := by
          simpa [hkmax] using hsuccN_max
        have hterm : bucketPotential r (fr.max' hne + 1) = 0 := by
          simpa [fr, hne] using hbucketPotential_terminal r hr
        have hdrop := hbucketPotential_drop r hr k hk_interval
        have hdrop' : R r ≤ bucketPotential r k := by
          have hterm' : bucketPotential r (k + 1) = 0 := by
            simpa [hkmax] using hterm
          linarith
        have hgoal :
            R r ≤ (bucketPotential r k + carry r) - carry rmax := by
          have hrmax' : r = rmax := by simpa [rmax] using hrmax
          have hcarry_eq : carry r = carry rmax := by rw [hrmax']
          linarith
        simpa [A_tail, r, rmax, hsuccN, hrmax, hk_lt_N, hjk] using hgoal
      · rcases hboundaryCarry r hr hrmax with ⟨hs_mem, hs, hmin_next, hcarry⟩
        have hnext_info :=
          hfiber_mem (next r) hs_mem ((fiber (next r)).min' hs)
            (Finset.min'_mem (fiber (next r)) hs)
        have hsucc_range : k + 1 ∈ Finset.range N := by
          simpa [hkmax, hmin_next] using hnext_info.1
        have hsucc_j : j ≤ k + 1 := by
          simpa [hkmax, hmin_next] using hnext_info.2.1
        have hm_succ : m (k + 1) = next r := by
          simpa [hkmax, hmin_next] using hnext_info.2.2
        have hsucc_lt_N : k + 1 < N := Finset.mem_range.mp hsucc_range
        have hterm : bucketPotential r (fr.max' hne + 1) = 0 := by
          simpa [fr, hne] using hbucketPotential_terminal r hr
        have hdrop := hbucketPotential_drop r hr k hk_interval
        have hdrop' : R r ≤ bucketPotential r k := by
          have hterm' : bucketPotential r (k + 1) = 0 := by
            simpa [hkmax] using hterm
          linarith
        have hcarry' :
            bucketPotential (next r) (k + 1) + carry (next r) ≤ carry r := by
          simpa [hkmax, hmin_next] using hcarry
        have hgoal :
            R r ≤
              (bucketPotential r k + carry r) -
                (bucketPotential (next r) (k + 1) + carry (next r)) := by
          linarith
        simpa [A_tail, r, hm_succ, hsucc_lt_N, hsucc_j, hk_lt_N, hjk] using hgoal
    · rcases hsame_bucket_succ k hkN hjk hne hk_interval hkmax with
        ⟨hsucc_range, hsucc_j, hm_succ⟩
      have hsucc_lt_N : k + 1 < N := Finset.mem_range.mp hsucc_range
      have hdrop := hbucketPotential_drop r hr k hk_interval
      have hgoal :
          R r ≤
            (bucketPotential r k + carry r) -
              (bucketPotential r (k + 1) + carry r) := by
        linarith
      simpa [A_tail, r, hm_succ, hk_lt_N, hjk, hsucc_lt_N, hsucc_j] using hgoal

/-- Build the non-cumulative adjacent-bucket carry from an aggregate start budget.

Aligns with Lan Corollary 8.3 / Eq. (8.1.79) after the scalar start-sum
simplification is available: the remaining carry is pure finite-order
bookkeeping over the realized bucket chain. Candidate audit: considered target
`finite_ordered_bucket_potentials_stitch_of_carry`,
`finset_sum_le_min_sub_terminal_of_ordered_successor`, and SOptLib
`sum_range_sub_succ_le_first_of_last_nonneg`; those either consume an already
available carry or telescope scalar drops, while this helper constructs the
future-start carry needed by the current pointwise stitching interface. -/
theorem finite_ordered_carry_certificate_of_start_sum_bound
    (B : Finset ℕ) (start : ℕ → ℝ) (next : ℕ → ℕ) (C : ℝ)
    (hB : B.Nonempty)
    (hstart_sum : B.sum start ≤ C)
    (hnext_mem : ∀ r (hr : r ∈ B), r ≠ B.max' hB → next r ∈ B)
    (hnext_gt : ∀ r (hr : r ∈ B), r ≠ B.max' hB → r < next r)
    (hnext_le_of_between :
      ∀ r (hr : r ∈ B), r ≠ B.max' hB →
        ∀ x ∈ B, r < x → next r ≤ x) :
    ∃ carry : ℕ → ℝ,
      start (B.min' hB) + carry (B.min' hB) ≤ C ∧
      0 ≤ carry (B.max' hB) ∧
      ∀ r (hr : r ∈ B), r ≠ B.max' hB →
        start (next r) + carry (next r) ≤ carry r := by
  classical
  let carry : ℕ → ℝ := fun r => B.sum (fun x => if r < x then start x else 0)
  refine ⟨carry, ?_, ?_, ?_⟩
  · have hpoint :
        ∀ x ∈ B,
          start x =
            (if B.min' hB < x then start x else 0) +
              (if x = B.min' hB then start x else 0) := by
      intro x hx
      have hmin_le : B.min' hB ≤ x := Finset.min'_le B x hx
      by_cases hlt : B.min' hB < x
      · have hne : x ≠ B.min' hB := by omega
        simp [hlt, hne]
      · have hx_eq : x = B.min' hB := by omega
        simp [hlt, hx_eq]
    have hsum_split :
        B.sum start =
          carry (B.min' hB) +
            B.sum (fun x => if x = B.min' hB then start x else 0) := by
      calc
        B.sum start =
            B.sum (fun x =>
              (if B.min' hB < x then start x else 0) +
                (if x = B.min' hB then start x else 0)) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              exact hpoint x hx
        _ =
            carry (B.min' hB) +
              B.sum (fun x => if x = B.min' hB then start x else 0) := by
              rw [Finset.sum_add_distrib]
    have hsingleton :
        B.sum (fun x => if x = B.min' hB then start x else 0) =
          start (B.min' hB) := by
      rw [← Finset.sum_filter]
      have hfilter :
          B.filter (fun x => x = B.min' hB) = {B.min' hB} := by
        ext x
        constructor
        · intro hx
          have hx_eq : x = B.min' hB := (Finset.mem_filter.mp hx).2
          simpa [hx_eq]
        · intro hx
          have hx_eq : x = B.min' hB := by
            simpa using hx
          exact Finset.mem_filter.mpr ⟨by
            simpa [hx_eq] using Finset.min'_mem B hB, hx_eq⟩
      rw [hfilter]
      simp
    have htotal :
        start (B.min' hB) + carry (B.min' hB) = B.sum start := by
      rw [hsum_split, hsingleton]
      ring
    rw [htotal]
    exact hstart_sum
  · have hzero : carry (B.max' hB) = 0 := by
      dsimp [carry]
      refine Finset.sum_eq_zero ?_
      intro x hx
      have hx_le_max : x ≤ B.max' hB := Finset.le_max' B x hx
      have hnot : ¬ B.max' hB < x := not_lt.mpr hx_le_max
      simp [hnot]
    rw [hzero]
  · intro r hr hr_ne
    have hnextB : next r ∈ B := hnext_mem r hr hr_ne
    have hgt : r < next r := hnext_gt r hr hr_ne
    have hpoint :
        ∀ x ∈ B,
          (if r < x then start x else 0) =
            (if x = next r then start x else 0) +
              (if next r < x then start x else 0) := by
      intro x hx
      by_cases hrx : r < x
      · have hnle : next r ≤ x := hnext_le_of_between r hr hr_ne x hx hrx
        by_cases hxnext : x = next r
        · subst x
          simp [hgt]
        · have hnext_lt_x : next r < x := by omega
          simp [hrx, hxnext, hnext_lt_x]
      · have hnot_next_lt : ¬ next r < x := by
          intro hlt
          exact hrx (lt_trans hgt hlt)
        have hx_ne_next : x ≠ next r := by
          intro hxnext
          exact hrx (by simpa [hxnext] using hgt)
        simp [hrx, hnot_next_lt, hx_ne_next]
    have hsum_split :
        carry r =
          B.sum (fun x => if x = next r then start x else 0) +
            carry (next r) := by
      calc
        carry r =
            B.sum (fun x =>
              (if x = next r then start x else 0) +
                (if next r < x then start x else 0)) := by
              dsimp [carry]
              refine Finset.sum_congr rfl ?_
              intro x hx
              exact hpoint x hx
        _ =
            B.sum (fun x => if x = next r then start x else 0) +
              carry (next r) := by
              rw [Finset.sum_add_distrib]
    have hsingleton :
        B.sum (fun x => if x = next r then start x else 0) =
          start (next r) := by
      rw [← Finset.sum_filter]
      have hfilter : B.filter (fun x => x = next r) = {next r} := by
        ext x
        constructor
        · intro hx
          have hx_eq : x = next r := (Finset.mem_filter.mp hx).2
          simpa [hx_eq]
        · intro hx
          have hx_eq : x = next r := by
            simpa using hx
          exact Finset.mem_filter.mpr ⟨by simpa [hx_eq] using hnextB, hx_eq⟩
      rw [hfilter]
      simp
    rw [hsum_split, hsingleton]

/-- Build the adjacent-bucket carry once the first bucket plus its ordered
future starts have the desired initial budget.

This is pure finite-order infrastructure for the non-cumulative carry consumed
by `finite_ordered_bucket_potentials_stitch_of_carry`.  It avoids taking an
aggregate start-sum premise: the only scalar burden left to the source-specific
proof is the initial first-plus-future carry inequality. -/
theorem finite_ordered_future_carry_certificate_of_initial_bound
    (B : Finset ℕ) (start : ℕ → ℝ) (next : ℕ → ℕ) (C : ℝ)
    (hB : B.Nonempty)
    (hinit :
      start (B.min' hB) +
        B.sum (fun x => if B.min' hB < x then start x else 0) ≤ C)
    (hnext_mem : ∀ r (hr : r ∈ B), r ≠ B.max' hB → next r ∈ B)
    (hnext_gt : ∀ r (hr : r ∈ B), r ≠ B.max' hB → r < next r)
    (hnext_le_of_between :
      ∀ r (hr : r ∈ B), r ≠ B.max' hB →
        ∀ x ∈ B, r < x → next r ≤ x) :
    ∃ carry : ℕ → ℝ,
      start (B.min' hB) + carry (B.min' hB) ≤ C ∧
      0 ≤ carry (B.max' hB) ∧
      ∀ r (hr : r ∈ B), r ≠ B.max' hB →
        start (next r) + carry (next r) ≤ carry r := by
  classical
  let carry : ℕ → ℝ := fun r => B.sum (fun x => if r < x then start x else 0)
  refine ⟨carry, ?_, ?_, ?_⟩
  · simpa [carry] using hinit
  · have hzero : carry (B.max' hB) = 0 := by
      dsimp [carry]
      refine Finset.sum_eq_zero ?_
      intro x hx
      have hx_le_max : x ≤ B.max' hB := Finset.le_max' B x hx
      have hnot : ¬ B.max' hB < x := not_lt.mpr hx_le_max
      simp [hnot]
    rw [hzero]
  · intro r hr hr_ne
    have hnextB : next r ∈ B := hnext_mem r hr hr_ne
    have hgt : r < next r := hnext_gt r hr hr_ne
    have hpoint :
        ∀ x ∈ B,
          (if r < x then start x else 0) =
            (if x = next r then start x else 0) +
              (if next r < x then start x else 0) := by
      intro x hx
      by_cases hrx : r < x
      · have hnle : next r ≤ x := hnext_le_of_between r hr hr_ne x hx hrx
        by_cases hxnext : x = next r
        · subst x
          simp [hgt]
        · have hnext_lt_x : next r < x := by omega
          simp [hrx, hxnext, hnext_lt_x]
      · have hnot_next_lt : ¬ next r < x := by
          intro hlt
          exact hrx (lt_trans hgt hlt)
        have hx_ne_next : x ≠ next r := by
          intro hxnext
          exact hrx (by simpa [hxnext] using hgt)
        simp [hrx, hnot_next_lt, hx_ne_next]
    have hsum_split :
        carry r =
          B.sum (fun x => if x = next r then start x else 0) +
            carry (next r) := by
      calc
        carry r =
            B.sum (fun x =>
              (if x = next r then start x else 0) +
                (if next r < x then start x else 0)) := by
              dsimp [carry]
              refine Finset.sum_congr rfl ?_
              intro x hx
              exact hpoint x hx
        _ =
            B.sum (fun x => if x = next r then start x else 0) +
              carry (next r) := by
              rw [Finset.sum_add_distrib]
    have hsingleton :
        B.sum (fun x => if x = next r then start x else 0) =
          start (next r) := by
      rw [← Finset.sum_filter]
      have hfilter : B.filter (fun x => x = next r) = {next r} := by
        ext x
        constructor
        · intro hx
          have hx_eq : x = next r := (Finset.mem_filter.mp hx).2
          simpa [hx_eq]
        · intro hx
          have hx_eq : x = next r := by
            simpa using hx
          exact Finset.mem_filter.mpr ⟨by simpa [hx_eq] using hnextB, hx_eq⟩
      rw [hfilter]
      simp
    rw [hsum_split, hsingleton]

/-- The first realized bucket plus all strictly future realized buckets is the
whole bucket-start sum.

This is pure finite-order bookkeeping for the high-tail carry constructor: it
separates the carried initial budget from the source-specific signed scalar
budget, without adding an aggregate premise to the carry API. -/
theorem finset_min_add_future_sum_eq_sum
    (B : Finset ℕ) (start : ℕ → ℝ) (hB : B.Nonempty) :
    start (B.min' hB) +
        B.sum (fun x => if B.min' hB < x then start x else 0) =
      B.sum start := by
  classical
  have hpoint :
      ∀ x ∈ B,
        start x =
          (if x = B.min' hB then start x else 0) +
            (if B.min' hB < x then start x else 0) := by
    intro x hx
    have hmin_le : B.min' hB ≤ x := Finset.min'_le B x hx
    by_cases hlt : B.min' hB < x
    · have hne : x ≠ B.min' hB := by omega
      simp [hlt, hne]
    · have hx_eq : x = B.min' hB := by omega
      simp [hlt, hx_eq]
  have hsum_split :
      B.sum start =
        B.sum (fun x => if x = B.min' hB then start x else 0) +
          B.sum (fun x => if B.min' hB < x then start x else 0) := by
    calc
      B.sum start =
          B.sum (fun x =>
            (if x = B.min' hB then start x else 0) +
              (if B.min' hB < x then start x else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            exact hpoint x hx
      _ =
          B.sum (fun x => if x = B.min' hB then start x else 0) +
            B.sum (fun x => if B.min' hB < x then start x else 0) := by
            rw [Finset.sum_add_distrib]
  have hsingleton :
      B.sum (fun x => if x = B.min' hB then start x else 0) =
        start (B.min' hB) := by
    rw [← Finset.sum_filter]
    have hfilter :
        B.filter (fun x => x = B.min' hB) = {B.min' hB} := by
      ext x
      constructor
      · intro hx
        have hx_eq : x = B.min' hB := (Finset.mem_filter.mp hx).2
        simpa [hx_eq]
      · intro hx
        have hx_eq : x = B.min' hB := by
          simpa using hx
        exact Finset.mem_filter.mpr ⟨by
          simpa [hx_eq] using Finset.min'_mem B hB, hx_eq⟩
    rw [hfilter]
    simp
  calc
    start (B.min' hB) +
        B.sum (fun x => if B.min' hB < x then start x else 0)
        =
        B.sum (fun x => if x = B.min' hB then start x else 0) +
          B.sum (fun x => if B.min' hB < x then start x else 0) := by
        rw [hsingleton]
    _ = B.sum start := hsum_split.symm

/-- Any adjacent future-carry certificate already bounds the strict future
bucket-start sum.

This is the converse bookkeeping for
`finite_ordered_future_carry_certificate_of_initial_bound`: the carry API used
by the high-tail stitching lemma cannot be weaker than the first-plus-future
start budget.  It therefore identifies the remaining compact-grid obstruction
as the scalar budget for the starts, rather than missing ordered-Finset carry
machinery. -/
theorem finite_ordered_future_sum_le_carry_of_certificate
    (B : Finset ℕ) (start carry : ℕ → ℝ) (next : ℕ → ℕ)
    (hB : B.Nonempty)
    (hterminal : 0 ≤ carry (B.max' hB))
    (hnext_mem : ∀ r (hr : r ∈ B), r ≠ B.max' hB → next r ∈ B)
    (hnext_gt : ∀ r (hr : r ∈ B), r ≠ B.max' hB → r < next r)
    (hnext_le_of_between :
      ∀ r (hr : r ∈ B), r ≠ B.max' hB →
        ∀ x ∈ B, r < x → next r ≤ x)
    (hrec : ∀ r (hr : r ∈ B), r ≠ B.max' hB →
      start (next r) + carry (next r) ≤ carry r) :
    B.sum (fun x => if B.min' hB < x then start x else 0) ≤
      carry (B.min' hB) := by
  classical
  induction hcard : B.card using Nat.strong_induction_on generalizing B with
  | h n ih =>
    by_cases hmin_eq_max : B.min' hB = B.max' hB
    · have hfuture_zero :
          B.sum (fun x => if B.min' hB < x then start x else 0) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro x hx
        have hx_le_max : x ≤ B.max' hB := Finset.le_max' B x hx
        have hnot : ¬ B.min' hB < x := by
          rw [hmin_eq_max]
          exact not_lt.mpr hx_le_max
        simp [hnot]
      have hterminal_min : 0 ≤ carry (B.min' hB) := by
        simpa [hmin_eq_max] using hterminal
      rw [hfuture_zero]
      exact hterminal_min
    · let rmin : ℕ := B.min' hB
      have hrmin : rmin ∈ B := Finset.min'_mem B hB
      have hrmin_ne_max : rmin ≠ B.max' hB := by
        intro h
        exact hmin_eq_max h
      let B' : Finset ℕ := B.erase rmin
      have hB'_nonempty : B'.Nonempty := by
        refine ⟨B.max' hB, ?_⟩
        exact Finset.mem_erase.mpr ⟨by
          intro hmax_eq_min
          exact hmin_eq_max hmax_eq_min.symm, Finset.max'_mem B hB⟩
      have hcard_lt : B'.card < B.card := by
        simpa [B', hrmin] using Finset.card_erase_lt_of_mem hrmin
      have hmax_B' : B'.max' hB'_nonempty = B.max' hB := by
        apply le_antisymm
        · exact Finset.le_max' B (B'.max' hB'_nonempty)
            (by
              have hmem := Finset.max'_mem B' hB'_nonempty
              exact (Finset.mem_erase.mp hmem).2)
        · exact Finset.le_max' B' (B.max' hB)
            (by
              exact Finset.mem_erase.mpr ⟨by
                intro hmax_eq_min
                exact hmin_eq_max hmax_eq_min.symm, Finset.max'_mem B hB⟩)
      have hnext_rmin_mem_B' : next rmin ∈ B' := by
        have hmemB := hnext_mem rmin hrmin hrmin_ne_max
        exact Finset.mem_erase.mpr ⟨by
          intro hnext_eq
          have hgt := hnext_gt rmin hrmin hrmin_ne_max
          omega, hmemB⟩
      have hmin_B' : B'.min' hB'_nonempty = next rmin := by
        apply le_antisymm
        · exact Finset.min'_le B' (next rmin) hnext_rmin_mem_B'
        · have hmin_mem := Finset.min'_mem B' hB'_nonempty
          have hmin_mem_B : B'.min' hB'_nonempty ∈ B :=
            (Finset.mem_erase.mp hmin_mem).2
          have hmin_ne_rmin : B'.min' hB'_nonempty ≠ rmin :=
            (Finset.mem_erase.mp hmin_mem).1
          have hrmin_lt_min : rmin < B'.min' hB'_nonempty := by
            have hle := Finset.min'_le B (B'.min' hB'_nonempty) hmin_mem_B
            omega
          exact hnext_le_of_between rmin hrmin hrmin_ne_max
            (B'.min' hB'_nonempty) hmin_mem_B hrmin_lt_min
      have hnext_mem' :
          ∀ r (hr : r ∈ B'), r ≠ B'.max' hB'_nonempty → next r ∈ B' := by
        intro r hr hr_ne
        have hrB : r ∈ B := (Finset.mem_erase.mp hr).2
        have hr_ne_max : r ≠ B.max' hB := by
          simpa [hmax_B'] using hr_ne
        have hnextB := hnext_mem r hrB hr_ne_max
        exact Finset.mem_erase.mpr ⟨by
          intro hnext_eq_min
          have hnext_le_r : next r ≤ r := by
            rw [hnext_eq_min]
            exact Finset.min'_le B r hrB
          have hgt := hnext_gt r hrB hr_ne_max
          omega, hnextB⟩
      have hnext_gt' :
          ∀ r (hr : r ∈ B'), r ≠ B'.max' hB'_nonempty → r < next r := by
        intro r hr hr_ne
        exact hnext_gt r (Finset.mem_erase.mp hr).2
          (by simpa [hmax_B'] using hr_ne)
      have hnext_le_between' :
          ∀ r (hr : r ∈ B'), r ≠ B'.max' hB'_nonempty →
            ∀ x ∈ B', r < x → next r ≤ x := by
        intro r hr hr_ne x hx hlt
        exact hnext_le_of_between r (Finset.mem_erase.mp hr).2
          (by simpa [hmax_B'] using hr_ne) x (Finset.mem_erase.mp hx).2 hlt
      have hrec' :
          ∀ r (hr : r ∈ B'), r ≠ B'.max' hB'_nonempty →
            start (next r) + carry (next r) ≤ carry r := by
        intro r hr hr_ne
        exact hrec r (Finset.mem_erase.mp hr).2
          (by simpa [hmax_B'] using hr_ne)
      have hterminal' : 0 ≤ carry (B'.max' hB'_nonempty) := by
        simpa [hmax_B'] using hterminal
      have htail_future :
          B'.sum (fun x =>
              if B'.min' hB'_nonempty < x then start x else 0) ≤
            carry (B'.min' hB'_nonempty) :=
        ih B'.card (by omega) B' hB'_nonempty hterminal'
          hnext_mem' hnext_gt' hnext_le_between' hrec' rfl
      have hfuture_eq_B' :
          B.sum (fun x => if rmin < x then start x else 0) =
            B'.sum start := by
        have hsplit :
            B.sum (fun x => if rmin < x then start x else 0) =
              B'.sum (fun x => if rmin < x then start x else 0) +
                (if rmin < rmin then start rmin else 0) := by
          simpa [B', rmin] using
            (Finset.sum_erase_add B
              (fun x => if rmin < x then start x else 0) hrmin).symm
        have hfuture_on_B' :
            B'.sum (fun x => if rmin < x then start x else 0) =
              B'.sum start := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          have hxB : x ∈ B := (Finset.mem_erase.mp hx).2
          have hx_ne : x ≠ rmin := (Finset.mem_erase.mp hx).1
          have hmin_le_x : rmin ≤ x := Finset.min'_le B x hxB
          have hlt : rmin < x := by omega
          simp [hlt]
        rw [hsplit, hfuture_on_B']
        simp
      have hB'_sum_split :
          B'.sum start =
            start (B'.min' hB'_nonempty) +
              B'.sum (fun x =>
                if B'.min' hB'_nonempty < x then start x else 0) := by
        exact (finset_min_add_future_sum_eq_sum B' start hB'_nonempty).symm
      have htail_future_next :
          B'.sum (fun x => if next rmin < x then start x else 0) ≤
            carry (next rmin) := by
        simpa [hmin_B'] using htail_future
      have hrec_min := hrec rmin hrmin hrmin_ne_max
      calc
        B.sum (fun x => if B.min' hB < x then start x else 0)
            = B.sum (fun x => if rmin < x then start x else 0) := by rfl
        _ = B'.sum start := hfuture_eq_B'
        _ =
            start (B'.min' hB'_nonempty) +
              B'.sum (fun x =>
                if B'.min' hB'_nonempty < x then start x else 0) := hB'_sum_split
        _ ≤ start (next rmin) + carry (next rmin) := by
            rw [hmin_B']
            have h := add_le_add_left htail_future_next (start (next rmin))
            linarith
        _ ≤ carry rmin := hrec_min

/-- A future-carry certificate for the high-tail bucket chain implies the same
initial first-plus-future start budget used by the current scalar frontier.

This private lemma is a diagnostic guardrail for the retained-carry route: a
closed certificate in the current carry API cannot bypass the retained signed
`B.sum start` budget, because the API telescopes back to that budget exactly. -/
theorem finite_ordered_initial_bound_of_future_carry_certificate
    (B : Finset ℕ) (start carry : ℕ → ℝ) (next : ℕ → ℕ) (C : ℝ)
    (hB : B.Nonempty)
    (hinit : start (B.min' hB) + carry (B.min' hB) ≤ C)
    (hterminal : 0 ≤ carry (B.max' hB))
    (hnext_mem : ∀ r (hr : r ∈ B), r ≠ B.max' hB → next r ∈ B)
    (hnext_gt : ∀ r (hr : r ∈ B), r ≠ B.max' hB → r < next r)
    (hnext_le_of_between :
      ∀ r (hr : r ∈ B), r ≠ B.max' hB →
        ∀ x ∈ B, r < x → next r ≤ x)
    (hrec : ∀ r (hr : r ∈ B), r ≠ B.max' hB →
      start (next r) + carry (next r) ≤ carry r) :
    start (B.min' hB) +
        B.sum (fun x => if B.min' hB < x then start x else 0) ≤ C := by
  have hfuture :=
    finite_ordered_future_sum_le_carry_of_certificate
      B start carry next hB hterminal hnext_mem hnext_gt
      hnext_le_of_between hrec
  linarith

/-- Build the future-start carry from an independently proved endpoint telescope.

This is the finite-tail carry bridge used by the compact ceiling-grid high tail:
once source-local endpoint drops, terminal nonnegativity, and the first endpoint
source bound supply `B.sum start ≤ C`, the remaining carry is pure ordered-Finset
bookkeeping. -/
theorem finite_ordered_future_carry_certificate_of_endpoint_budget
    (B : Finset ℕ) (start Phi : ℕ → ℝ) (next : ℕ → ℕ)
    (terminal C : ℝ)
    (hB : B.Nonempty)
    (hnext_mem : ∀ r (hr : r ∈ B), r ≠ B.max' hB → next r ∈ B)
    (hnext_gt : ∀ r (hr : r ∈ B), r ≠ B.max' hB → r < next r)
    (hnext_le_of_between :
      ∀ r (hr : r ∈ B), r ≠ B.max' hB →
        ∀ x ∈ B, r < x → next r ≤ x)
    (hdrop : ∀ r (hr : r ∈ B), r ≠ B.max' hB →
      start r ≤ Phi r - Phi (next r))
    (hterminal : start (B.max' hB) ≤ Phi (B.max' hB) - terminal)
    (hsource : Phi (B.min' hB) - terminal ≤ C) :
    ∃ carry : ℕ → ℝ,
      start (B.min' hB) + carry (B.min' hB) ≤ C ∧
      0 ≤ carry (B.max' hB) ∧
      ∀ r (hr : r ∈ B), r ≠ B.max' hB →
        start (next r) + carry (next r) ≤ carry r := by
  classical
  have hstart_sum : B.sum start ≤ C := by
    have htelescope :
        B.sum start ≤ Phi (B.min' hB) - terminal :=
      finset_sum_le_min_sub_terminal_of_ordered_successor
        B start Phi next terminal hB hnext_mem hnext_gt
        hnext_le_of_between hdrop hterminal
    exact le_trans htelescope hsource
  have hinit :
      start (B.min' hB) +
          B.sum (fun x => if B.min' hB < x then start x else 0) ≤ C := by
    rw [finset_min_add_future_sum_eq_sum B start hB]
    exact hstart_sum
  exact
    finite_ordered_future_carry_certificate_of_initial_bound
      B start next C hB hinit hnext_mem hnext_gt hnext_le_of_between

/-- Endpoint-potential certificate from an independently proved start budget.

This is pure ordered-Finset infrastructure.  It does not prove the compact-grid
scalar budget; it records that, after that budget is proved from the retained
`R/Q` source algebra, the local `Phi`/terminal certificate is just the standard
future-start carry packaged as a potential. -/
theorem finite_ordered_endpoint_phi_certificate_of_start_sum_bound
    (B : Finset ℕ) (start : ℕ → ℝ) (next : ℕ → ℕ) (C : ℝ)
    (hB : B.Nonempty)
    (hstart_sum : B.sum start ≤ C)
    (hnext_mem : ∀ r (hr : r ∈ B), r ≠ B.max' hB → next r ∈ B)
    (hnext_gt : ∀ r (hr : r ∈ B), r ≠ B.max' hB → r < next r)
    (hnext_le_of_between :
      ∀ r (hr : r ∈ B), r ≠ B.max' hB →
        ∀ x ∈ B, r < x → next r ≤ x) :
    ∃ Phi : ℕ → ℝ, ∃ terminal : ℝ,
      (∀ r (hr : r ∈ B), r ≠ B.max' hB →
        start r ≤ Phi r - Phi (next r)) ∧
      start (B.max' hB) ≤ Phi (B.max' hB) - terminal ∧
      Phi (B.min' hB) - terminal ≤ C := by
  classical
  rcases
      finite_ordered_carry_certificate_of_start_sum_bound
        B start next C hB hstart_sum hnext_mem hnext_gt hnext_le_of_between with
    ⟨carry, hinit, hterminal_nonneg, hrec⟩
  refine ⟨fun r => start r + carry r, carry (B.max' hB), ?_, ?_, ?_⟩
  · intro r hr hr_ne
    have h := hrec r hr hr_ne
    linarith
  · linarith
  · linarith [hinit, hterminal_nonneg]

/-- Any endpoint-potential certificate implies the corresponding start budget.

Together with
`finite_ordered_endpoint_phi_certificate_of_start_sum_bound`, this identifies the
remaining compact-grid Phi obstruction as the single retained signed scalar
budget, not additional finite-order carry machinery. -/
theorem finite_ordered_start_sum_bound_of_endpoint_phi_certificate
    (B : Finset ℕ) (start Phi : ℕ → ℝ) (next : ℕ → ℕ)
    (terminal C : ℝ)
    (hB : B.Nonempty)
    (hnext_mem : ∀ r (hr : r ∈ B), r ≠ B.max' hB → next r ∈ B)
    (hnext_gt : ∀ r (hr : r ∈ B), r ≠ B.max' hB → r < next r)
    (hnext_le_of_between :
      ∀ r (hr : r ∈ B), r ≠ B.max' hB →
        ∀ x ∈ B, r < x → next r ≤ x)
    (hdrop : ∀ r (hr : r ∈ B), r ≠ B.max' hB →
      start r ≤ Phi r - Phi (next r))
    (hterminal : start (B.max' hB) ≤ Phi (B.max' hB) - terminal)
    (hsource : Phi (B.min' hB) - terminal ≤ C) :
    B.sum start ≤ C := by
  have htelescope :
      B.sum start ≤ Phi (B.min' hB) - terminal :=
    finset_sum_le_min_sub_terminal_of_ordered_successor
      B start Phi next terminal hB hnext_mem hnext_gt hnext_le_of_between
      hdrop hterminal
  exact le_trans htelescope hsource

/-- Partition the `R`-only high tail by realized compact-ceiling buckets.

Aligns with the first finite-fiber step behind Lan Corollary 8.3 / Eq.
(8.1.79): the high tail is grouped by the realized integer budget before the
ordered bucket cancellation is applied. Candidate audit: considered local
`compact_ceiling_grid_tail_sum_eq_realized_bucket_sum`,
`compact_ceiling_grid_realized_bucket_deficit_form`, and
`finset_sum_le_min_sub_terminal_of_ordered_successor`, plus SOptLib
`sum_range_sub_succ_le_first_of_last_nonneg`; the first two include signed
grid-slack terms, while this step needs the literal `R`-only fiber-card
identity and the telescope helpers are for the later ordered budget. -/
theorem compact_ceiling_grid_tail_R_eq_realized_bucket_card_sum
    (N j : ℕ) (R : ℕ → ℝ) (m : ℕ → ℕ) :
    (Finset.range N).sum (fun k => if j ≤ k then R (m k) else 0) =
      (Finset.image m ((Finset.range N).filter (fun k => j ≤ k))).sum (fun r =>
        (((Finset.range N).filter (fun k => j ≤ k ∧ m k = r)).card : ℝ) *
          R r) := by
  classical
  let s : Finset ℕ := (Finset.range N).filter (fun k => j ≤ k)
  let B : Finset ℕ := s.image m
  let f : ℕ → ℝ := fun k => R (m k)
  have htail_filter :
      (Finset.range N).sum (fun k => if j ≤ k then R (m k) else 0) =
        s.sum f := by
    rw [← Finset.sum_filter]
  have hmaps : ∀ k ∈ s, m k ∈ B := by
    intro k hk
    exact Finset.mem_image_of_mem m hk
  have hfiber :
      B.sum (fun r => (s.filter (fun k => m k = r)).sum f) =
        s.sum f := by
    simpa [B] using
      (Finset.sum_fiberwise_of_maps_to (s := s)
        (t := B) (g := m) hmaps f)
  have hinner : ∀ r,
      (s.filter (fun k => m k = r)).sum f =
        (((Finset.range N).filter (fun k => j ≤ k ∧ m k = r)).card : ℝ) *
          R r := by
    intro r
    have hset :
        s.filter (fun k => m k = r) =
          (Finset.range N).filter (fun k => j ≤ k ∧ m k = r) := by
      ext k
      simp [s, and_left_comm, and_assoc]
    calc
      (s.filter (fun k => m k = r)).sum f
          =
        ((Finset.range N).filter (fun k => j ≤ k ∧ m k = r)).sum
          (fun _ => R r) := by
            rw [hset]
            refine Finset.sum_congr rfl ?_
            intro k hk
            have hmk : m k = r := (Finset.mem_filter.mp hk).2.2
            simp [f, hmk]
      _ =
        (((Finset.range N).filter (fun k => j ≤ k ∧ m k = r)).card : ℝ) *
          R r := by
            rw [Finset.sum_const, nsmul_eq_mul]
  calc
    (Finset.range N).sum (fun k => if j ≤ k then R (m k) else 0)
        = s.sum f := htail_filter
    _ = B.sum (fun r => (s.filter (fun k => m k = r)).sum f) := hfiber.symm
    _ =
      B.sum (fun r =>
        (((Finset.range N).filter (fun k => j ≤ k ∧ m k = r)).card : ℝ) *
          R r) := by
        refine Finset.sum_congr rfl ?_
        intro r _hr
        exact hinner r
    _ =
      (Finset.image m ((Finset.range N).filter (fun k => j ≤ k))).sum (fun r =>
        (((Finset.range N).filter (fun k => j ≤ k ∧ m k = r)).card : ℝ) *
          R r) := by
        rfl

/-- Intervalized form of the `R`-only compact-ceiling high tail.

Aligns with Lan Corollary 8.3 / Eq. (8.1.79): after the high tail is grouped by
realized integer budgets, monotonicity makes every realized fiber a closed
interval, so the remaining scalar budget can be stated over interval
cardinalities. Candidate audit: considered
`compact_ceiling_grid_tail_R_eq_realized_bucket_card_sum`,
`compact_ceiling_grid_bucket_interval`, and target signed-bucket helpers
`compact_ceiling_grid_realized_bucket_deficit_form` /
`compact_ceiling_grid_tail_signed_eq_intervalized_buckets`; the first two are
the exact `R`-only transport pieces, while the signed helpers carry additional
`Q`/grid-deficit terms not present in this pure overrun budget. -/
theorem compact_ceiling_grid_tail_R_eq_intervalized_bucket_card_sum
    (N j : ℕ) (R : ℕ → ℝ) (m : ℕ → ℕ) (hm_mono : Monotone m) :
    (Finset.range N).sum (fun k => if j ≤ k then R (m k) else 0) =
      (Finset.image m ((Finset.range N).filter (fun k => j ≤ k))).sum (fun r =>
        let fiber : Finset ℕ :=
          (Finset.range N).filter (fun k => j ≤ k ∧ m k = r)
        if hne : fiber.Nonempty then
          ((Finset.Icc (fiber.min' hne) (fiber.max' hne)).card : ℝ) * R r
        else 0) := by
  classical
  let B : Finset ℕ := Finset.image m ((Finset.range N).filter (fun k => j ≤ k))
  let fiber : ℕ → Finset ℕ := fun r =>
    (Finset.range N).filter (fun k => j ≤ k ∧ m k = r)
  have hbucket_nonempty : ∀ r ∈ B, (fiber r).Nonempty := by
    intro r hr
    rcases (by simpa [B, Finset.mem_filter] using hr :
        ∃ k, (k < N ∧ j ≤ k) ∧ m k = r) with ⟨k, ⟨hkN, hjk⟩, hmk⟩
    exact ⟨k, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hkN, hjk, hmk⟩⟩
  have hinterval_card :
      ∀ r (hr : r ∈ B),
        ((fiber r).card : ℝ) =
          ((Finset.Icc ((fiber r).min' (hbucket_nonempty r hr))
            ((fiber r).max' (hbucket_nonempty r hr))).card : ℝ) := by
    intro r hr
    let fr : Finset ℕ := fiber r
    have hne : fr.Nonempty := by simpa [fr] using hbucket_nonempty r hr
    have hsame_bucket_between :
        ∀ a b t, a ≤ t → t ≤ b →
          j ≤ a ∧ m a = r → j ≤ b ∧ m b = r →
            j ≤ t ∧ m t = r := by
      intro a b t hat htb ha hb
      constructor
      · exact le_trans ha.1 hat
      · have hleft : m a ≤ m t := hm_mono hat
        have hright : m t ≤ m b := hm_mono htb
        omega
    have hfr_interval :
        fr = Finset.Icc (fr.min' hne) (fr.max' hne) := by
      exact compact_ceiling_grid_bucket_interval
        fr N j r m (by simp [fr, fiber]) hne hsame_bucket_between
    have hcard := congrArg Finset.card hfr_interval
    simpa [fr] using congrArg (fun n : ℕ => (n : ℝ)) hcard
  calc
    (Finset.range N).sum (fun k => if j ≤ k then R (m k) else 0)
        =
      B.sum (fun r => (((fiber r).card : ℝ) * R r)) := by
        simpa [B, fiber] using
          compact_ceiling_grid_tail_R_eq_realized_bucket_card_sum N j R m
    _ =
      B.sum (fun r =>
        let fiber : Finset ℕ :=
          (Finset.range N).filter (fun k => j ≤ k ∧ m k = r)
        if hne : fiber.Nonempty then
          ((Finset.Icc (fiber.min' hne) (fiber.max' hne)).card : ℝ) * R r
        else 0) := by
        refine Finset.sum_congr rfl ?_
        intro r hr
        have hne : (fiber r).Nonempty := hbucket_nonempty r hr
        have hcard := hinterval_card r hr
        simp [fiber, hne, hcard]
    _ =
      (Finset.image m ((Finset.range N).filter (fun k => j ≤ k))).sum (fun r =>
        let fiber : Finset ℕ :=
          (Finset.range N).filter (fun k => j ≤ k ∧ m k = r)
        if hne : fiber.Nonempty then
          ((Finset.Icc (fiber.min' hne) (fiber.max' hne)).card : ℝ) * R r
        else 0) := by
        rfl

/-- Partition the total `R`-only compact-ceiling overrun by realized integer
budgets.

Aligns with the all-range finite-fiber step behind Lan Corollary 8.3 /
Eq. (8.1.79). Candidate audit: considered the pre-searched process/update
candidates, SOptLib finite telescope helpers, and target helpers
`compact_ceiling_grid_tail_R_eq_realized_bucket_card_sum` /
`compact_ceiling_grid_tail_R_eq_intervalized_bucket_card_sum`; the process and
telescope candidates are unrelated, while the tail helper specializes exactly
with `j = 0`, so this bridge records the all-range form needed by the pure
integer-overrun aggregate. -/
theorem compact_ceiling_grid_total_R_eq_realized_bucket_card_sum
    (N : ℕ) (R : ℕ → ℝ) (m : ℕ → ℕ) :
    (Finset.range N).sum (fun k => R (m k)) =
      (Finset.image m (Finset.range N)).sum (fun r =>
        (((Finset.range N).filter (fun k => m k = r)).card : ℝ) * R r) := by
  classical
  have htail :=
    compact_ceiling_grid_tail_R_eq_realized_bucket_card_sum N 0 R m
  simpa using htail

/-- Intervalized all-range form of the `R`-only compact-ceiling overrun.

Aligns with the realized-bucket scalar reduction behind Lan Corollary 8.3 /
Eq. (8.1.79). Candidate audit: considered the pre-searched process/update
candidates, SOptLib ordered/range telescope helpers, and target helper
`compact_ceiling_grid_tail_R_eq_intervalized_bucket_card_sum`; only the target
tail helper supplies the required monotone-fiber intervalization, and this
statement is its non-tail specialization for the total pure overrun aggregate. -/
theorem compact_ceiling_grid_total_R_eq_intervalized_bucket_card_sum
    (N : ℕ) (R : ℕ → ℝ) (m : ℕ → ℕ) (hm_mono : Monotone m) :
    (Finset.range N).sum (fun k => R (m k)) =
      (Finset.image m (Finset.range N)).sum (fun r =>
        let fiber : Finset ℕ :=
          (Finset.range N).filter (fun k => m k = r)
        if hne : fiber.Nonempty then
          ((Finset.Icc (fiber.min' hne) (fiber.max' hne)).card : ℝ) * R r
        else 0) := by
  classical
  have htail :=
    compact_ceiling_grid_tail_R_eq_intervalized_bucket_card_sum N 0 R m hm_mono
  simpa using htail

/-- Replace intervalized high-tail `R` buckets by their harmonic row envelope.

Aligns with Lan Corollary 8.3 / Eq. (8.1.79): every realized high-tail bucket
has a representative `k` with `r = m k`, so the rowwise harmonic envelope can be
transported to the bucket cardinality term. Candidate audit: considered target
helpers `compact_ceiling_grid_tail_R_eq_intervalized_bucket_card_sum`,
`compact_ceiling_grid_bucket_absorb_harmonic_final`, and
`compact_ceiling_grid_integer_overrun_le_harmonic_div`; the bucket absorption
helpers include `Q`-weighted deficit terms not present here, while the row
harmonic hypothesis is exactly enough for this pure `R` comparison. -/
theorem compact_ceiling_grid_tail_R_intervalized_le_harmonic_bucket_sum
    (N j : ℕ) (R H : ℕ → ℝ) (m : ℕ → ℕ)
    (hR_harmonic : ∀ k, R (m k) ≤ H (m k) / (m k : ℝ)) :
    (Finset.image m ((Finset.range N).filter (fun k => j ≤ k))).sum (fun r =>
      let fiber : Finset ℕ :=
        (Finset.range N).filter (fun k => j ≤ k ∧ m k = r)
      if hne : fiber.Nonempty then
        ((Finset.Icc (fiber.min' hne) (fiber.max' hne)).card : ℝ) * R r
      else 0) ≤
    (Finset.image m ((Finset.range N).filter (fun k => j ≤ k))).sum (fun r =>
      let fiber : Finset ℕ :=
        (Finset.range N).filter (fun k => j ≤ k ∧ m k = r)
      if hne : fiber.Nonempty then
        ((Finset.Icc (fiber.min' hne) (fiber.max' hne)).card : ℝ) *
          (H r / (r : ℝ))
      else 0) := by
  classical
  refine Finset.sum_le_sum ?_
  intro r hr
  let fiber : Finset ℕ :=
    (Finset.range N).filter (fun k => j ≤ k ∧ m k = r)
  have hfiber_nonempty : fiber.Nonempty := by
    rcases Finset.mem_image.mp hr with ⟨k, hk, rfl⟩
    have hk_range : k ∈ Finset.range N := (Finset.mem_filter.mp hk).1
    have hjk : j ≤ k := (Finset.mem_filter.mp hk).2
    exact ⟨k, Finset.mem_filter.mpr ⟨hk_range, hjk, rfl⟩⟩
  rcases hfiber_nonempty with ⟨k, hkfiber⟩
  have hne : fiber.Nonempty := ⟨k, hkfiber⟩
  have hmk : m k = r := (Finset.mem_filter.mp hkfiber).2.2
  have hrow : R r ≤ H r / (r : ℝ) := by
    simpa [hmk] using hR_harmonic k
  have hcard_nonneg :
      0 ≤ ((Finset.Icc (fiber.min' hne) (fiber.max' hne)).card : ℝ) := by
    positivity
  rw [dif_pos hne, dif_pos hne]
  exact mul_le_mul_of_nonneg_left hrow hcard_nonneg

/-- Retained-correction normal form for the pure `R` high-tail bucket sum.

This is only an algebraic transport: it rewrites each intervalized `R` bucket as
the source-shaped corrected residual/increment expression plus the retained
`Q`-weighted deficit sum.  The remaining budget must still bound this exact
retained-correction expression against the low-prefix credit. -/
theorem compact_ceiling_grid_tail_R_eq_retained_correction_form
    (N j : ℕ) (grid R Q H : ℕ → ℝ) (m : ℕ → ℕ)
    (hR_def : ∀ r,
      R r =
        (H r * ((r : ℝ) ^ 2 + 3 * (r : ℝ) + 2) -
          (3 * (r : ℝ) ^ 2 + 7 * (r : ℝ))) /
          ((r : ℝ) * ((r : ℝ) + 3) ^ 2))
    (hQ_def : ∀ r,
      Q r =
        (((((r : ℝ) + 1) * ((r : ℝ) + 2) / ((r : ℝ) + 3) ^ 2) *
          (1 + H r / (r : ℝ))) /
          (r : ℝ)))
    (hj_tail_high : ∀ k, j ≤ k → 9 ≤ m k) :
    (Finset.image m ((Finset.range N).filter (fun k => j ≤ k))).sum (fun r =>
      let fiber : Finset ℕ :=
        (Finset.range N).filter (fun k => j ≤ k ∧ m k = r)
      if hne : fiber.Nonempty then
        ((Finset.Icc (fiber.min' hne) (fiber.max' hne)).card : ℝ) * R r
      else 0) =
    (Finset.image m ((Finset.range N).filter (fun k => j ≤ k))).sum (fun r =>
      let fiber : Finset ℕ :=
        (Finset.range N).filter (fun k => j ≤ k ∧ m k = r)
      if hne : fiber.Nonempty then
        (((Finset.Icc (fiber.min' hne) (fiber.max' hne)).card : ℝ) *
            (H r / (r : ℝ) -
              Q r * ((r : ℝ) - grid (fiber.max' hne)) -
              Q r * ((r : ℝ) * (3 * (r : ℝ) + 7) /
                (((r : ℝ) + 1) * ((r : ℝ) + 2)))) -
          Q r *
            (Finset.Ico (fiber.min' hne) (fiber.max' hne)).sum (fun k =>
              (((k - fiber.min' hne + 1 : ℕ) : ℝ) *
                (grid (k + 1) - grid k)))) +
          Q r *
            (Finset.Icc (fiber.min' hne) (fiber.max' hne)).sum
              (fun k => (r : ℝ) - grid k)
      else 0) := by
  classical
  refine Finset.sum_congr rfl ?_
  intro r hr
  let fiber : Finset ℕ :=
    (Finset.range N).filter (fun k => j ≤ k ∧ m k = r)
  by_cases hne : fiber.Nonempty
  · have hr_high : 9 ≤ r := by
      rcases Finset.mem_image.mp hr with ⟨k, hk, rfl⟩
      exact hj_tail_high k (Finset.mem_filter.mp hk).2
    have hab : fiber.min' hne ≤ fiber.max' hne :=
      Finset.le_max' fiber (fiber.min' hne) (Finset.min'_mem fiber hne)
    have hform :=
      compact_ceiling_grid_actual_bucket_residual_increment_form
        (fiber.min' hne) (fiber.max' hne) r grid R Q H
        hR_def hQ_def hr_high hab
    rw [dif_pos hne, dif_pos hne]
    rw [← hform]
    ring
  · simp [fiber, hne]
/-- Convert an all-range `R` overrun budget into the signed high-tail budget.

Aligns with Lan Corollary 8.3 / Eq. (8.1.79): the low rows are removed as the
exact `lowCredit` prefix, and the remaining high tail is bounded by the
all-range integer-overrun cancellation. Candidate audit: considered target
helpers `compact_ceiling_grid_prefix_signed_le_neg_low_credit`,
`compact_ceiling_grid_total_R_eq_intervalized_bucket_card_sum`, and SOptLib
`sum_range_sub_succ_le_first_of_last_nonneg`; the prefix helper supplies the
low-credit comparison, while this bridge only needs finite prefix/tail
bookkeeping once the non-cyclic all-range `R` budget is available. -/
theorem compact_ceiling_grid_tail_signed_le_prefix_credit_of_total_R
    (N j : ℕ) (grid R Q lowCredit : ℕ → ℝ) (m : ℕ → ℕ)
    (hprefix_low : ∀ k ∈ Finset.range N, k < j → m k ≤ 8)
    (hslack_nonpos : ∀ k, (grid k - (m k : ℝ)) * Q (m k) ≤ 0)
    (hsigned_row : ∀ k,
      grid k * Q (m k) - 1 =
        (grid k - (m k : ℝ)) * Q (m k) + R (m k))
    (hlowCredit : ∀ r, lowCredit r = if r ≤ 8 then -R r else 0)
    (htotal_R : (Finset.range N).sum (fun k => R (m k)) ≤ 1) :
    (Finset.range N).sum (fun k =>
      if j ≤ k then grid k * Q (m k) - 1 else 0) ≤
    1 + (Finset.range N).sum (fun k =>
      if k < j then lowCredit (m k) else 0) := by
  classical
  let prefixR : ℝ :=
    (Finset.range N).sum (fun k => if k < j then R (m k) else 0)
  let tailR : ℝ :=
    (Finset.range N).sum (fun k => if j ≤ k then R (m k) else 0)
  have htail_signed_le_R :
      (Finset.range N).sum (fun k =>
        if j ≤ k then grid k * Q (m k) - 1 else 0) ≤ tailR := by
    dsimp [tailR]
    refine Finset.sum_le_sum ?_
    intro k _hk
    by_cases hjk : j ≤ k
    · have hsplit := hsigned_row k
      have hslack := hslack_nonpos k
      simp [hjk]
      linarith
    · simp [hjk]
  have htotal_split :
      (Finset.range N).sum (fun k => R (m k)) = prefixR + tailR := by
    dsimp [prefixR, tailR]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro k _hk
    by_cases hklt : k < j
    · have hnot : ¬ j ≤ k := by omega
      simp [hklt, hnot]
    · have hle : j ≤ k := Nat.le_of_not_gt hklt
      simp [hklt, hle]
  have hprefixR_eq :
      prefixR =
        - (Finset.range N).sum (fun k =>
            if k < j then lowCredit (m k) else 0) := by
    dsimp [prefixR]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro k hk
    by_cases hklt : k < j
    · have hlow : m k ≤ 8 := hprefix_low k hk hklt
      simp [hklt, hlow, hlowCredit (m k)]
    · simp [hklt]
  have htailR_budget :
      tailR ≤
        1 + (Finset.range N).sum (fun k =>
          if k < j then lowCredit (m k) else 0) := by
    linarith [htotal_R, htotal_split, hprefixR_eq]
  exact le_trans htail_signed_le_R htailR_budget

/-- Convert an all-range pure-`R` budget into the exact high-tail prefix-credit
bound.

Aligns with Lan Corollary 8.3 / Eq. (8.1.79): after the source scalar bound
controls all compact-ceiling `R` rows, the low prefix is cancelled by the exact
`lowCredit` terms. Candidate audit: considered
`compact_ceiling_grid_tail_signed_le_prefix_credit_of_total_R`, which has the
right finite split but proves a signed `grid * Q - 1` tail rather than the
literal pure-`R` tail needed at the current start-sum boundary; target helpers
`compact_ceiling_grid_exact_low_prefix_credit_cancellation` and
`compact_ceiling_grid_total_R_eq_intervalized_bucket_card_sum` respectively
supply only the prefix rewrite and bucket transport; SOptLib
`sum_range_sub_succ_le_first_of_last_nonneg` is a telescope consumer and does
not state this prefix/tail algebra. -/
private theorem compact_ceiling_grid_tail_R_le_one_plus_prefix_credit_of_total_R
    (N j : ℕ) (R lowCredit : ℕ → ℝ) (m : ℕ → ℕ)
    (hprefix_low : ∀ k ∈ Finset.range N, k < j → m k ≤ 8)
    (hlowCredit : ∀ r, lowCredit r = if r ≤ 8 then -R r else 0)
    (htotal_R : (Finset.range N).sum (fun k => R (m k)) ≤ 1) :
    (Finset.range N).sum (fun k => if j ≤ k then R (m k) else 0) ≤
      1 + (Finset.range N).sum (fun k =>
        if k < j then lowCredit (m k) else 0) := by
  classical
  let prefixR : ℝ :=
    (Finset.range N).sum (fun k => if k < j then R (m k) else 0)
  let tailR : ℝ :=
    (Finset.range N).sum (fun k => if j ≤ k then R (m k) else 0)
  have htotal_split :
      (Finset.range N).sum (fun k => R (m k)) = prefixR + tailR := by
    dsimp [prefixR, tailR]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro k _hk
    by_cases hklt : k < j
    · have hnot : ¬ j ≤ k := by omega
      simp [hklt, hnot]
    · have hle : j ≤ k := Nat.le_of_not_gt hklt
      simp [hklt, hle]
  have hprefixR_eq :
      prefixR =
        - (Finset.range N).sum (fun k =>
            if k < j then lowCredit (m k) else 0) := by
    dsimp [prefixR]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro k hk
    by_cases hklt : k < j
    · have hlow : m k ≤ 8 := hprefix_low k hk hklt
      simp [hklt, hlow, hlowCredit (m k)]
    · simp [hklt]
  change tailR ≤
    1 + (Finset.range N).sum (fun k =>
      if k < j then lowCredit (m k) else 0)
  linarith [htotal_R, htotal_split, hprefixR_eq]
/-- Pre-frontier realized high-tail bucket successor data.

Aligns with Lan Corollary 8.3 / Eq. (8.1.79): this is the pure finite-order
successor structure for monotone realized buckets, isolated before the
endpoint/carry certificate so that the certificate does not depend on later
budget wrappers. Candidate audit: considered the later same-file
`compact_ceiling_grid_high_tail_realized_bucket_successor_structure`,
earlier pointwise helper `compact_ceiling_grid_next_realized_bucket_min_eq_succ`,
ordered telescope helpers `finset_sum_le_min_sub_terminal_of_ordered_successor`
and `finset_sum_le_min_sub_terminal_with_ordered_carry`, and SOptLib
`sum_range_sub_succ_le_first_of_last_nonneg`; the pointwise helper is the exact
order primitive, while the later same-file theorem is declaration-order unsafe
at this frontier and the telescope helpers consume successor data rather than
constructing it. -/
private theorem compact_ceiling_grid_tail_realized_bucket_successor_structure_pre
    (N j : ℕ) (m : ℕ → ℕ)
    (B : Finset ℕ) (fiber : ℕ → Finset ℕ)
    (hm_mono : Monotone m)
    (hB_def : B = Finset.image m ((Finset.range N).filter (fun k => j ≤ k)))
    (hfiber_def : ∀ r,
      fiber r = (Finset.range N).filter (fun k => j ≤ k ∧ m k = r))
    (hB_nonempty : B.Nonempty)
    (hbucket_nonempty : ∀ r ∈ B, (fiber r).Nonempty) :
    (∀ r (hr : r ∈ B), r ≠ B.max' hB_nonempty →
      (fiber r).max' (hbucket_nonempty r hr) + 1 ∈ Finset.range N) ∧
    (∀ r (hr : r ∈ B), r ≠ B.max' hB_nonempty →
      let fr : Finset ℕ := fiber r
      let b : ℕ := fr.max' (hbucket_nonempty r hr)
      let s : ℕ := m (b + 1)
      s ∈ B ∧ r < s ∧
        ∃ hs : (fiber s).Nonempty,
          (fiber s).min' hs = b + 1 ∧
            ∀ x ∈ B, r < x → s ≤ x) := by
  classical
  have hsucc_range_all :
      ∀ r (hr : r ∈ B), r ≠ B.max' hB_nonempty →
        (fiber r).max' (hbucket_nonempty r hr) + 1 ∈ Finset.range N := by
    intro r hr hr_ne
    let fr : Finset ℕ := fiber r
    let hne : fr.Nonempty := hbucket_nonempty r hr
    by_contra hnot_range
    have hb_mem : fr.max' hne ∈ fr := Finset.max'_mem fr hne
    have hb_filter :
        fr.max' hne ∈
          (Finset.range N).filter (fun k => j ≤ k ∧ m k = r) := by
      simpa [fr, hfiber_def r] using hb_mem
    have hb_lt_N : fr.max' hne < N :=
      Finset.mem_range.mp (Finset.mem_filter.mp hb_filter).1
    have hb_m : m (fr.max' hne) = r :=
      (Finset.mem_filter.mp hb_filter).2.2
    have hb_succ_le_N : fr.max' hne + 1 ≤ N :=
      Nat.succ_le_iff.mpr hb_lt_N
    have hN_le_succ : N ≤ fr.max' hne + 1 := by
      by_contra hnot
      exact hnot_range (Finset.mem_range.mpr (Nat.lt_of_not_ge hnot))
    have hb_succ_eq_N : fr.max' hne + 1 = N :=
      le_antisymm hb_succ_le_N hN_le_succ
    let rmax : ℕ := B.max' hB_nonempty
    have hrmax : rmax ∈ B := Finset.max'_mem B hB_nonempty
    have hr_le_rmax : r ≤ rmax := Finset.le_max' B r hr
    have hr_lt_rmax : r < rmax := lt_of_le_of_ne hr_le_rmax hr_ne
    have hrmax_image :
        rmax ∈ Finset.image m ((Finset.range N).filter (fun k => j ≤ k)) := by
      rw [← hB_def]
      exact hrmax
    rcases Finset.mem_image.mp hrmax_image with
      ⟨k, hk_tail, hmk⟩
    have hkN : k < N := Finset.mem_range.mp (Finset.mem_filter.mp hk_tail).1
    have hk_le_b : k ≤ fr.max' hne := by
      have hk_lt_succ : k < fr.max' hne + 1 := by
        simpa [hb_succ_eq_N] using hkN
      omega
    have hrmax_le_r : rmax ≤ r := by
      calc
        rmax = m k := hmk.symm
        _ ≤ m (fr.max' hne) := hm_mono hk_le_b
        _ = r := hb_m
    omega
  refine ⟨hsucc_range_all, ?_⟩
  intro r hr hr_ne
  dsimp
  let fr : Finset ℕ := fiber r
  let hne : fr.Nonempty := hbucket_nonempty r hr
  let b : ℕ := fr.max' hne
  let s : ℕ := m (b + 1)
  have hsucc_range :
      (fiber r).max' (hbucket_nonempty r hr) + 1 ∈ Finset.range N := by
    exact hsucc_range_all r hr hr_ne
  have hstruct :
      s ∈ B ∧ r < s ∧
        ∃ hs : (fiber s).Nonempty, (fiber s).min' hs = b + 1 := by
    have hnext :=
      compact_ceiling_grid_next_realized_bucket_min_eq_succ
        N j r m hm_mono
        (by simpa [hfiber_def r, fr] using hne)
        (by simpa [hfiber_def r, fr, b] using hsucc_range)
    simpa [hB_def, hfiber_def, fr, b, s] using hnext
  rcases hstruct with ⟨hs_mem, hrs, hs, hmin⟩
  refine ⟨hs_mem, hrs, hs, hmin, ?_⟩
  intro x hx hxgt
  have hb_mem : b ∈ fr := Finset.max'_mem fr hne
  have hb_filter :
      b ∈ (Finset.range N).filter (fun k => j ≤ k ∧ m k = r) := by
    simpa [fr, hfiber_def r, b] using hb_mem
  have hb_m : m b = r := (Finset.mem_filter.mp hb_filter).2.2
  have hx_image :
      x ∈ Finset.image m ((Finset.range N).filter (fun k => j ≤ k)) := by
    rw [← hB_def]
    exact hx
  rcases Finset.mem_image.mp hx_image with ⟨k, _hk_tail, hmk⟩
  have hb_succ_le_k : b + 1 ≤ k := by
    by_contra hnot
    have hk_le_b : k ≤ b := by omega
    have hx_le_r : x ≤ r := by
      calc
        x = m k := hmk.symm
        _ ≤ m b := hm_mono hk_le_b
        _ = r := hb_m
    omega
  calc
    s = m (b + 1) := rfl
    _ ≤ m k := hm_mono hb_succ_le_k
    _ = x := hmk

/-- Pre-frontier endpoint geometry for a nonmax realized high-tail bucket.

Aligns with Lan Corollary 8.3 / Eq. (8.1.79): the endpoint deficit of every
nonterminal compact bucket is carried across the grid jump into the next
realized bucket. Candidate audit: considered target
`compact_ceiling_grid_tail_realized_bucket_successor_structure_pre`,
`compact_ceiling_grid_endpoint_exit_or_terminal`,
`compact_ceiling_grid_endpoint_deficit_lt_cubic_increment`, and
`compact_ceiling_grid_adjacent_bucket_endpoint_transport`, plus SOptLib
`sum_range_sub_succ_le_first_of_last_nonneg`; the target helpers provide the
source-specific successor and endpoint pieces, while the SOptLib telescope is a
later aggregate consumer rather than this pointwise bridge. -/
private theorem compact_ceiling_grid_high_tail_bucket_endpoint_geometry_pre
    (N j : ℕ) (c : ℝ) (grid : ℕ → ℝ) (m : ℕ → ℕ)
    (B : Finset ℕ) (fiber : ℕ → Finset ℕ)
    (hm_def : ∀ k, m k = max 1 (Nat.ceil (grid k)))
    (hm_mono : Monotone m)
    (hgrid_strict : StrictMono grid)
    (htail_bucket_window : ∀ k, j ≤ k →
      (m k : ℝ) - 1 < grid k ∧ grid k ≤ (m k : ℝ))
    (hgrid_increment : ∀ k,
      grid (k + 1) - grid k =
        c * (((k + 2 : ℕ) : ℝ)) * (3 * (k : ℝ) + 7))
    (hB_def : B = Finset.image m ((Finset.range N).filter (fun k => j ≤ k)))
    (hfiber_def : ∀ r,
      fiber r = (Finset.range N).filter (fun k => j ≤ k ∧ m k = r))
    (hB_nonempty : B.Nonempty)
    (hbucket_nonempty : ∀ r ∈ B, (fiber r).Nonempty)
    (hbucket_high : ∀ r ∈ B, 9 ≤ r)
    (hsucc_structure :
      (∀ r (hr : r ∈ B), r ≠ B.max' hB_nonempty →
        (fiber r).max' (hbucket_nonempty r hr) + 1 ∈ Finset.range N) ∧
      (∀ r (hr : r ∈ B), r ≠ B.max' hB_nonempty →
        let fr : Finset ℕ := fiber r
        let b : ℕ := fr.max' (hbucket_nonempty r hr)
        let s : ℕ := m (b + 1)
        s ∈ B ∧ r < s ∧
          ∃ hs : (fiber s).Nonempty,
            (fiber s).min' hs = b + 1 ∧
              ∀ x ∈ B, r < x → s ≤ x)) :
    ∀ r (hr : r ∈ B), r ≠ B.max' hB_nonempty →
      let fr : Finset ℕ := fiber r
      let hne : fr.Nonempty := hbucket_nonempty r hr
      let b : ℕ := fr.max' hne
      let s : ℕ := m (b + 1)
      s ∈ B ∧ r < s ∧
        ∃ hs : (fiber s).Nonempty,
          (fiber s).min' hs = b + 1 ∧
            0 ≤ (r : ℝ) - grid b ∧
            (r : ℝ) - grid b < grid ((fiber s).min' hs) - grid b ∧
            ∀ x ∈ B, r < x → s ≤ x := by
  classical
  intro r hr hr_ne
  dsimp
  let fr : Finset ℕ := fiber r
  let hne : fr.Nonempty := hbucket_nonempty r hr
  let b : ℕ := fr.max' hne
  let s : ℕ := m (b + 1)
  have hsucc_range :
      (fiber r).max' (hbucket_nonempty r hr) + 1 ∈ Finset.range N :=
    hsucc_structure.1 r hr hr_ne
  have hstruct := hsucc_structure.2 r hr hr_ne
  dsimp at hstruct
  rcases hstruct with ⟨hs_mem, hrs, hs, hmin, hleast⟩
  have hb_mem : b ∈ fr := Finset.max'_mem fr hne
  have hb_filter :
      b ∈ (Finset.range N).filter (fun k => j ≤ k ∧ m k = r) := by
    simpa [fr, hfiber_def r, b] using hb_mem
  have hbj : j ≤ b := (Finset.mem_filter.mp hb_filter).2.1
  have hbm : m b = r := (Finset.mem_filter.mp hb_filter).2.2
  have hupper : grid b ≤ (r : ℝ) := by
    have hwin := htail_bucket_window b hbj
    simpa [hbm] using hwin.2
  have hexit : (r : ℝ) < grid (b + 1) := by
    have h :=
      compact_ceiling_grid_endpoint_exit_or_terminal
        N j r grid m fr (by simpa [fr] using hfiber_def r) hne hm_def
        hm_mono hgrid_strict (hbucket_high r hr)
        (by simpa [fr, b] using hsucc_range)
    simpa [b] using h
  have hendpoint :
      0 ≤ (r : ℝ) - grid b ∧
        (r : ℝ) - grid b <
          c * (((b + 2 : ℕ) : ℝ)) * (3 * (b : ℝ) + 7) :=
    compact_ceiling_grid_endpoint_deficit_lt_cubic_increment
      r b c grid hgrid_increment hupper hexit
  refine ⟨by simpa [s] using hs_mem, by simpa [s] using hrs, ?_⟩
  refine ⟨by simpa [s] using hs, ?_⟩
  refine ⟨by simpa [fr, b, s] using hmin, hendpoint.1, ?_, ?_⟩
  · calc
      (r : ℝ) - grid b
          < c * (((b + 2 : ℕ) : ℝ)) * (3 * (b : ℝ) + 7) := hendpoint.2
      _ = grid (b + 1) - grid b := by
          rw [hgrid_increment b]
      _ = grid ((fiber s).min' (by simpa [s] using hs)) - grid b := by
          have hmin' : (fiber s).min' (by simpa [s] using hs) = b + 1 := by
            simpa [fr, b, s] using hmin
          rw [hmin']
  · intro x hx hlt
    simpa [s] using hleast x hx hlt

/-- Pre-frontier nonmax pure-`R` bucket endpoint jump.

Aligns with the bucket endpoint/carry part of Lan Corollary 8.3 / Eq.
(8.1.79): after harmonic absorption, a nonterminal pure-`R` bucket plus its
outgoing endpoint carry is controlled by the harmonic endpoint envelope and the
next-bucket grid jump. Candidate audit: considered target
`compact_ceiling_grid_bucket_absorb_harmonic_with_residual`,
`compact_ceiling_grid_high_tail_bucket_endpoint_geometry_pre`,
`compact_ceiling_grid_integer_overrun_le_harmonic_div`,
`Finset.card_nsmul_le_sum`, and later
`compact_ceiling_grid_pure_R_nonmax_bucket_boundary_with_deficit_carry`; the
later helper is declaration-order unsafe at this frontier, while the listed
pre-frontier pieces prove this exact pointwise bridge without an aggregate
budget premise. -/
private theorem compact_ceiling_grid_high_tail_pure_R_nonmax_endpoint_jump_pre
    (B : Finset ℕ) (fiber : ℕ → Finset ℕ)
    (R H Q grid : ℕ → ℝ) (m : ℕ → ℕ)
    (hH_def : ∀ r, H r = (Finset.range r).sum (fun i => 1 / ((i : ℝ) + 1)))
    (hR_def : ∀ r,
      R r =
        (H r * ((r : ℝ) ^ 2 + 3 * (r : ℝ) + 2) -
          (3 * (r : ℝ) ^ 2 + 7 * (r : ℝ))) /
          ((r : ℝ) * ((r : ℝ) + 3) ^ 2))
    (hB_nonempty : B.Nonempty)
    (hbucket_nonempty : ∀ r ∈ B, (fiber r).Nonempty)
    (hbucket_high : ∀ r ∈ B, 9 ≤ r)
    (hgrid_mono : Monotone grid)
    (hendpoint_geometry :
      ∀ r (hr : r ∈ B), r ≠ B.max' hB_nonempty →
        let fr : Finset ℕ := fiber r
        let hne : fr.Nonempty := hbucket_nonempty r hr
        let b : ℕ := fr.max' hne
        let s : ℕ := m (b + 1)
        s ∈ B ∧ r < s ∧
          ∃ hs : (fiber s).Nonempty,
            (fiber s).min' hs = b + 1 ∧
              0 ≤ (r : ℝ) - grid b ∧
              (r : ℝ) - grid b < grid ((fiber s).min' hs) - grid b ∧
              ∀ x ∈ B, r < x → s ≤ x)
    (hQ_next_le :
      ∀ r (hr : r ∈ B), r ≠ B.max' hB_nonempty →
        let fr : Finset ℕ := fiber r
        let hne : fr.Nonempty := hbucket_nonempty r hr
        let b : ℕ := fr.max' hne
        Q (m (b + 1)) ≤ Q r)
    (hQ_nonneg_on_B : ∀ r (hr : r ∈ B), 0 ≤ Q r) :
    ∀ r (hr : r ∈ B), r ≠ B.max' hB_nonempty →
      let fr : Finset ℕ := fiber r
      let hne : fr.Nonempty := hbucket_nonempty r hr
      let b : ℕ := fr.max' hne
      let s : ℕ := m (b + 1)
      ∃ hs : (fiber s).Nonempty,
        (fiber s).min' hs = b + 1 ∧
          ((Finset.Icc (fr.min' hne) (fr.max' hne)).card : ℝ) * R r +
              Q s * ((r : ℝ) - grid b) ≤
            ((Finset.Icc (fr.min' hne) (fr.max' hne)).card : ℝ) *
                (H r / (r : ℝ)) +
              Q r * (grid ((fiber s).min' hs) - grid b) := by
  classical
  intro r hr hr_ne
  dsimp
  let fr : Finset ℕ := fiber r
  let hne : fr.Nonempty := hbucket_nonempty r hr
  let a : ℕ := fr.min' hne
  let b : ℕ := fr.max' hne
  let sNext : ℕ := m (b + 1)
  rcases hendpoint_geometry r hr hr_ne with
    ⟨hs_mem, _hrs, hs, hmin, hdef_nonneg, hdef_lt, _hleast⟩
  refine ⟨hs, by simpa [fr, b, sNext] using hmin, ?_⟩
  let I : Finset ℕ := Finset.Icc a b
  have hR_le : R r ≤ H r / (r : ℝ) := by
    have hr_pos : 0 < r := by
      have hhigh := hbucket_high r hr
      omega
    simpa [hR_def r, hH_def r] using
      compact_ceiling_grid_integer_overrun_le_harmonic_div (r := r) hr_pos
  have hQr_nonneg : 0 ≤ Q r := hQ_nonneg_on_B r hr
  have hdeficit :
      (I.card : ℝ) * ((r : ℝ) - grid b) ≤
        I.sum (fun k => (r : ℝ) - grid k) := by
    have hpoint :
        ∀ k ∈ I, (r : ℝ) - grid b ≤ (r : ℝ) - grid k := by
      intro k hk
      have hk_le_b : k ≤ b := (Finset.mem_Icc.mp hk).2
      have hgrid_le : grid k ≤ grid b := by
        exact hgrid_mono hk_le_b
      linarith
    have hsum := Finset.card_nsmul_le_sum I
      (fun k => (r : ℝ) - grid k) ((r : ℝ) - grid b) hpoint
    simpa [I, nsmul_eq_mul] using hsum
  have habs :=
    compact_ceiling_grid_bucket_absorb_harmonic_with_residual
      r grid R Q H I b hR_le hQr_nonneg hdeficit
  have hcard_R_le_H :
      (I.card : ℝ) * R r ≤ (I.card : ℝ) * (H r / (r : ℝ)) := by
    have h := habs.1
    linarith
  have hQs_le_Qr_def :
      Q sNext * ((r : ℝ) - grid b) ≤ Q r * ((r : ℝ) - grid b) := by
    exact mul_le_mul_of_nonneg_right
      (by simpa [fr, hne, b, sNext] using hQ_next_le r hr hr_ne)
      hdef_nonneg
  have hQr_def_le_jump :
      Q r * ((r : ℝ) - grid b) ≤
        Q r * (grid ((fiber sNext).min' hs) - grid b) := by
    exact mul_le_mul_of_nonneg_left (le_of_lt hdef_lt) hQr_nonneg
  have hcarry :
      Q sNext * ((r : ℝ) - grid b) ≤
        Q r * (grid ((fiber sNext).min' hs) - grid b) :=
    le_trans hQs_le_Qr_def hQr_def_le_jump
  have hgoal :
      (I.card : ℝ) * R r + Q sNext * ((r : ℝ) - grid b) ≤
        (I.card : ℝ) * (H r / (r : ℝ)) +
          Q r * (grid ((fiber sNext).min' hs) - grid b) := by
    linarith
  simpa [fr, hne, a, b, sNext, I] using hgoal
/-- Convert an aggregate high-tail row budget into a suffix drop potential.

This is the source-neutral finite-sum bridge used by the compact ceiling-grid
row budget. Candidate audit: considered SOptLib
`sum_range_sub_succ_le_first_of_last_nonneg`, target
`compact_ceiling_grid_charge_sum_le_one_of_drop`, and later target helpers
`compact_ceiling_grid_tail_potential_of_retained_charge_budget` /
`compact_ceiling_grid_tail_R_drop_potential_source`; the first two consume an
already-built potential, while the later helpers are declaration-order unsafe
at the current frontier. This helper keeps only the mechanical suffix-sum
construction from an explicit aggregate bound. -/
private theorem tail_suffix_potential_of_tail_budget
    (N j : ℕ) (row : ℕ → ℝ) (C : ℝ)
    (hbudget :
      (Finset.range N).sum (fun k => if j ≤ k then row k else 0) ≤ C) :
    ∃ A_tail : ℕ → ℝ,
      A_tail j ≤ C ∧
      (j ≤ N → 0 ≤ A_tail N) ∧
      ∀ k ∈ Finset.range N, j ≤ k →
        row k ≤ A_tail k - A_tail (k + 1) := by
  classical
  let A_tail : ℕ → ℝ := fun n => (Finset.Ico n N).sum row
  refine ⟨A_tail, ?_, ?_, ?_⟩
  · have htail_Ico_eq :
        A_tail j =
          (Finset.range N).sum (fun k => if j ≤ k then row k else 0) := by
      have hfilter :
          (Finset.range N).filter (fun k => j ≤ k) = Finset.Ico j N := by
        ext k
        constructor
        · intro hk
          exact Finset.mem_Ico.mpr
            ⟨(Finset.mem_filter.mp hk).2,
              Finset.mem_range.mp (Finset.mem_filter.mp hk).1⟩
        · intro hk
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2,
              (Finset.mem_Ico.mp hk).1⟩
      calc
        A_tail j = (Finset.Ico j N).sum row := rfl
        _ = ((Finset.range N).filter (fun k => j ≤ k)).sum row := by
              rw [hfilter]
        _ = (Finset.range N).sum (fun k => if j ≤ k then row k else 0) := by
              rw [Finset.sum_filter]
    exact le_of_eq_of_le htail_Ico_eq hbudget
  · intro _hjN
    simp [A_tail]
  · intro k hk _hjk
    have hkN : k < N := Finset.mem_range.mp hk
    have hsplit : A_tail k = row k + A_tail (k + 1) := by
      dsimp [A_tail]
      rw [Finset.sum_eq_sum_Ico_succ_bot hkN]
    rw [hsplit]
    linarith

/-- Transport a high-tail row-drop potential to the retained bucket Phi certificate.

This is the finite bucket half of Lan Corollary 8.3 / Eq. (8.1.79): once a
source-derived `A_tail` pays each realized high-tail row, the retained
fiber-card expression has the standard ordered endpoint certificate. Candidate
audit: considered `finite_ordered_endpoint_phi_certificate_of_start_sum_bound`
and `tail_suffix_potential_of_tail_budget`; the former is the matching ordered
certificate consumer, while the latter constructs `A_tail` only from an
aggregate tail budget and therefore does not provide the source row-drop input
required here. -/
private theorem bucket_phi_certificate_of_tail_row_potential_pre_frontier
    (N j : ℕ) (B : Finset ℕ) (fiber : ℕ → Finset ℕ)
    (retainedExpr R : ℕ → ℝ) (m next : ℕ → ℕ) (prefixCredit : ℝ)
    (hB_nonempty : B.Nonempty)
    (hbucket_nonempty : ∀ r ∈ B, (fiber r).Nonempty)
    (hnext_mem : ∀ r (hr : r ∈ B), r ≠ B.max' hB_nonempty → next r ∈ B)
    (hnext_gt : ∀ r (hr : r ∈ B), r ≠ B.max' hB_nonempty → r < next r)
    (hnext_le :
      ∀ r (hr : r ∈ B), r ≠ B.max' hB_nonempty →
        ∀ x ∈ B, r < x → next r ≤ x)
    (hj_le_N : j ≤ N)
    (hretained_eq :
      ∀ r (hr : r ∈ B),
        let fr : Finset ℕ := fiber r
        let hne : fr.Nonempty := hbucket_nonempty r hr
        retainedExpr r =
          ((Finset.Icc (fr.min' hne) (fr.max' hne)).card : ℝ) * R r)
    (htail_intervalized :
      (Finset.range N).sum (fun k => if j ≤ k then R (m k) else 0) =
        B.sum (fun r =>
          let fr : Finset ℕ := fiber r
          if hne : fr.Nonempty then
            ((Finset.Icc (fr.min' hne) (fr.max' hne)).card : ℝ) * R r
          else 0))
    (A_tail : ℕ → ℝ)
    (hA_tail_j : A_tail j ≤ 1 + prefixCredit)
    (hA_tail_N : 0 ≤ A_tail N)
    (hA_tail_drop :
      ∀ k ∈ Finset.range N, j ≤ k →
        R (m k) ≤ A_tail k - A_tail (k + 1)) :
    ∃ Phi : ℕ → ℝ, ∃ terminal : ℝ,
      (∀ r (hr : r ∈ B), r ≠ B.max' hB_nonempty →
        retainedExpr r ≤ Phi r - Phi (next r)) ∧
      retainedExpr (B.max' hB_nonempty) ≤
        Phi (B.max' hB_nonempty) - terminal ∧
      Phi (B.min' hB_nonempty) - terminal ≤
        1 + prefixCredit := by
  classical
  have hretained_sum_eq_tail :
      B.sum retainedExpr =
        (Finset.range N).sum (fun k => if j ≤ k then R (m k) else 0) := by
    calc
      B.sum retainedExpr =
          B.sum (fun r =>
            let fr : Finset ℕ := fiber r
            if hne : fr.Nonempty then
              ((Finset.Icc (fr.min' hne) (fr.max' hne)).card : ℝ) * R r
            else 0) := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            have hne : (fiber r).Nonempty := hbucket_nonempty r hr
            rw [hretained_eq r hr]
            simp [hne]
      _ = (Finset.range N).sum (fun k =>
            if j ≤ k then R (m k) else 0) := htail_intervalized.symm
  let A : ℕ → ℝ := fun k => if k < j then A_tail j else A_tail k
  have hA_N_nonneg : 0 ≤ A N := by
    have hNj : ¬ N < j := by omega
    simp [A, hNj, hA_tail_N]
  have hdrop :
      ∀ k ∈ Finset.range N,
        (if j ≤ k then R (m k) else 0) ≤ A k - A (k + 1) := by
    intro k hk
    by_cases hjk : j ≤ k
    · have hk_not_lt : ¬ k < j := by omega
      have hks_not_lt : ¬ k + 1 < j := by omega
      simpa [A, hjk, hk_not_lt, hks_not_lt] using
        hA_tail_drop k hk hjk
    · have hklt : k < j := Nat.lt_of_not_ge hjk
      by_cases hkslt : k + 1 < j
      · simp [A, hjk, hklt, hkslt]
      · have hsucc_eq : k + 1 = j := by omega
        simp [A, hjk, hklt, hkslt, hsucc_eq]
  have htail_sum_le :
      (Finset.range N).sum (fun k => if j ≤ k then R (m k) else 0) ≤
        A 0 := by
    calc
      (Finset.range N).sum (fun k => if j ≤ k then R (m k) else 0)
          ≤ (Finset.range N).sum (fun k => A k - A (k + 1)) := by
            exact Finset.sum_le_sum hdrop
      _ ≤ A 0 := by
            exact sum_range_sub_succ_le_first_of_last_nonneg A N hA_N_nonneg
  have hA0_eq : A 0 = A_tail j := by
    by_cases h0j : 0 < j
    · simp [A, h0j]
    · have hj_zero : j = 0 := Nat.eq_zero_of_not_pos h0j
      simp [A, h0j, hj_zero]
  have hretained_budget : B.sum retainedExpr ≤ 1 + prefixCredit := by
    calc
      B.sum retainedExpr =
          (Finset.range N).sum (fun k => if j ≤ k then R (m k) else 0) :=
            hretained_sum_eq_tail
      _ ≤ A 0 := htail_sum_le
      _ = A_tail j := hA0_eq
      _ ≤ 1 + prefixCredit := hA_tail_j
  exact
    finite_ordered_endpoint_phi_certificate_of_start_sum_bound
      B retainedExpr next (1 + prefixCredit) hB_nonempty hretained_budget
      hnext_mem hnext_gt hnext_le

/-- Pre-frontier retained budget from endpoint/carry scalar data.

Aligns with Lan Corollary 8.3 / Eq. (8.1.79): nonterminal retained bucket
mass is paid by the next endpoint carry, leaving only the explicit endpoint
sum plus the terminal retained bucket as the source scalar leaf. Candidate
audit: considered the later same-file
`compact_ceiling_grid_retained_ordered_carry_budget_pre`, ordered helpers
`finite_ordered_future_carry_certificate_of_initial_bound` and
`finite_ordered_endpoint_phi_certificate_of_start_sum_bound`, and SOptLib
`sum_range_sub_succ_le_first_of_last_nonneg`; the later helper is
declaration-order unsafe here, while the ordered helpers need this retained
endpoint scalar inequality as input. -/
private theorem compact_ceiling_grid_retained_ordered_carry_budget_pre_frontier
    (B : Finset ℕ) (fiber : ℕ → Finset ℕ)
    (retainedExpr H Q grid : ℕ → ℝ) (next : ℕ → ℕ)
    (prefixCredit : ℝ)
    (hB_nonempty : B.Nonempty)
    (hbucket_nonempty : ∀ r ∈ B, (fiber r).Nonempty)
    (hretained_nonmax_next_endpoint :
      ∀ r (hr : r ∈ B), r ≠ B.max' hB_nonempty →
        let fr : Finset ℕ := fiber r
        let hne : fr.Nonempty := hbucket_nonempty r hr
        let b : ℕ := fr.max' hne
        let s : ℕ := next r
        ∃ hs : (fiber s).Nonempty,
          (fiber s).min' hs = b + 1 ∧
            retainedExpr r + Q s * ((r : ℝ) - grid b) ≤
              ((Finset.Icc (fr.min' hne) (fr.max' hne)).card : ℝ) *
                  (H r / (r : ℝ)) +
                Q r * (grid ((fiber s).min' hs) - grid b))
    (hendpoint_budget_sum :
      (B.erase (B.max' hB_nonempty)).sum (fun r =>
        if hr : r ∈ B then
          if hr_ne : r ≠ B.max' hB_nonempty then
            let fr : Finset ℕ := fiber r
            let hne : fr.Nonempty := hbucket_nonempty r hr
            let b : ℕ := fr.max' hne
            let s : ℕ := next r
            let hs : (fiber s).Nonempty :=
              Classical.choose (hretained_nonmax_next_endpoint r hr hr_ne)
            ((Finset.Icc (fr.min' hne) (fr.max' hne)).card : ℝ) *
                (H r / (r : ℝ)) +
              Q r * (grid ((fiber s).min' hs) - grid b) -
              Q s * ((r : ℝ) - grid b)
          else 0
        else 0) +
        retainedExpr (B.max' hB_nonempty) ≤ 1 + prefixCredit) :
    B.sum retainedExpr ≤ 1 + prefixCredit := by
  classical
  let endpointBudget : ℕ → ℝ := fun r =>
    if hr : r ∈ B then
      if hr_ne : r ≠ B.max' hB_nonempty then
        let fr : Finset ℕ := fiber r
        let hne : fr.Nonempty := hbucket_nonempty r hr
        let b : ℕ := fr.max' hne
        let s : ℕ := next r
        let hs : (fiber s).Nonempty :=
          Classical.choose (hretained_nonmax_next_endpoint r hr hr_ne)
        ((Finset.Icc (fr.min' hne) (fr.max' hne)).card : ℝ) *
            (H r / (r : ℝ)) +
          Q r * (grid ((fiber s).min' hs) - grid b) -
          Q s * ((r : ℝ) - grid b)
      else 0
    else 0
  have hnonmax_bound :
      ∀ r (hr : r ∈ B), r ≠ B.max' hB_nonempty →
        retainedExpr r ≤ endpointBudget r := by
    intro r hr hr_ne
    have hspec :=
      Classical.choose_spec (hretained_nonmax_next_endpoint r hr hr_ne)
    dsimp [endpointBudget]
    rw [dif_pos hr, dif_pos hr_ne]
    exact (le_sub_iff_add_le).2 hspec.2
  have hmax_mem : B.max' hB_nonempty ∈ B :=
    Finset.max'_mem B hB_nonempty
  have hsplit :
      B.sum retainedExpr =
        (B.erase (B.max' hB_nonempty)).sum retainedExpr +
          retainedExpr (B.max' hB_nonempty) := by
    simpa using (Finset.sum_erase_add B retainedExpr hmax_mem).symm
  have hnonmax_sum :
      (B.erase (B.max' hB_nonempty)).sum retainedExpr ≤
        (B.erase (B.max' hB_nonempty)).sum endpointBudget := by
    refine Finset.sum_le_sum ?_
    intro r hr
    exact hnonmax_bound r (Finset.mem_erase.mp hr).2 (Finset.mem_erase.mp hr).1
  have hendpoint_sum :
      (B.erase (B.max' hB_nonempty)).sum endpointBudget +
          retainedExpr (B.max' hB_nonempty) ≤
        1 + prefixCredit := by
    simpa [endpointBudget] using hendpoint_budget_sum
  linarith
/-- Pre-active comparison from the source signed ceiling-grid aggregate to the
stronger all-row pure-`R` aggregate.

This is a source-route diagnostic for Lan Corollary 8.3 / Eq. (8.1.79): the
public/coarser finite-grid scalar is the signed overrun
`grid k * Q (m k) - 1`, while the old private frontier asks for the stronger
pure-`R` row sum.  The comparison is one-way because each ceiling slack
`(grid k - m k) * Q (m k)` is nonpositive; therefore proving the pure-`R`
frontier is sufficient for the source scalar but is not the canonical source
object itself. -/
private theorem compact_ceiling_grid_signed_overrun_sum_le_total_R_pre_active
    (N : ℕ) (grid R H Q : ℕ → ℝ) (m : ℕ → ℕ)
    (hH_def : ∀ r, H r = (Finset.range r).sum (fun i => 1 / ((i : ℝ) + 1)))
    (hR_def : ∀ r,
      R r =
        (H r * ((r : ℝ) ^ 2 + 3 * (r : ℝ) + 2) -
          (3 * (r : ℝ) ^ 2 + 7 * (r : ℝ))) /
          ((r : ℝ) * ((r : ℝ) + 3) ^ 2))
    (hQ_def : ∀ r,
      Q r =
        (((((r : ℝ) + 1) * ((r : ℝ) + 2) / ((r : ℝ) + 3) ^ 2) *
          (1 + H r / (r : ℝ))) /
          (r : ℝ)))
    (hm_def : ∀ k, m k = max 1 (Nat.ceil (grid k))) :
    (Finset.range N).sum (fun k => grid k * Q (m k) - 1) ≤
      (Finset.range N).sum (fun k => R (m k)) := by
  classical
  refine Finset.sum_le_sum ?_
  intro k _hk
  have hm_pos : 0 < m k := by
    rw [hm_def k]
    exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
  have hgrid_le_m : grid k ≤ (m k : ℝ) := by
    rw [hm_def k]
    exact le_positive_ceil_max_one (grid k)
  have hH_nonneg : 0 ≤ H (m k) := by
    rw [hH_def (m k)]
    exact Finset.sum_nonneg (by intro i _hi; positivity)
  have hQ_nonneg : 0 ≤ Q (m k) := by
    have hmR : 0 < (m k : ℝ) := by exact_mod_cast hm_pos
    rw [hQ_def (m k)]
    positivity
  have hslack_nonpos : (grid k - (m k : ℝ)) * Q (m k) ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hgrid_le_m) hQ_nonneg
  have hsigned_row :
      grid k * Q (m k) - 1 =
        (grid k - (m k : ℝ)) * Q (m k) + R (m k) := by
    simpa [hH_def (m k), hR_def (m k), hQ_def (m k)] using
      compact_ceiling_grid_signed_row_eq (grid k) hm_pos
  linarith
/-- Pre-active semantic dependency certificate for the compact normalized
source route.

This is the artifact-level route evidence requested by the source-route audit:
a no-premise normalized Corollary 8.3(b) linear supplier for every admissible
compact inner budget immediately specializes to the canonical ceiling-grid
aggregate.  Thus the public normalized transport cannot bypass the
ceiling-grid signed/integer supplier; any axiom-clean no-premise route must
prove that supplier, or an equivalent retained endpoint/carry scalar, rather
than continuing the private all-row pure-`R` leaf as if it were the source
object. -/
theorem compact_normalized_source_supplier_implies_ceiling_grid_pre_active
    (N : PositiveTime) (c : ℝ) (hc : 0 ≤ c)
    (hsource :
      ∀ (T : PositiveTime → ℕ), (∀ κ, 0 < T κ) →
        (∀ κ : PositiveTime,
          c * (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2 ≤ (T κ : ℝ)) →
        (Finset.range N.1).sum (fun k =>
          let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
          (((c * ((((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) / (T κ : ℝ))) *
              (((T κ : ℝ) + 1) * ((T κ : ℝ) + 2) / ((T κ : ℝ) + 3) ^ 2)) *
              (1 + ((Finset.range (T κ)).sum (fun i => 1 / ((i : ℝ) + 1))) /
                (T κ : ℝ))) - 1)) ≤ 1) :
    (Finset.range N.1).sum (fun k =>
      let κ : PositiveTime := ⟨k + 1, Nat.succ_pos k⟩
      let m : ℕ :=
        max 1 (Nat.ceil (c * (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2))
      c * ((κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2) *
          (((((m : ℝ) + 1) * ((m : ℝ) + 2) / ((m : ℝ) + 3) ^ 2) *
            (1 + ((Finset.range m).sum (fun i => 1 / ((i : ℝ) + 1))) /
              (m : ℝ))) /
            (m : ℝ)) -
        1) ≤ 1 := by
  classical
  let T : PositiveTime → ℕ := fun κ =>
    max 1 (Nat.ceil (c * (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2))
  have hTpos : ∀ κ, 0 < T κ := by
    intro κ
    dsimp [T]
    exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
  have hbudget_scale : ∀ κ : PositiveTime,
      c * (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2 ≤ (T κ : ℝ) := by
    intro κ
    dsimp [T]
    exact le_positive_ceil_max_one
      (c * (κ.1 : ℝ) * ((κ.1 : ℝ) + 1) ^ 2)
  have h := hsource T hTpos hbudget_scale
  refine le_of_eq_of_le ?_ h
  refine Finset.sum_congr rfl ?_
  intro k _hk
  simp only
  ring
end StochasticGradientSliding
