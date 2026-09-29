import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.Tactic

open MeasureTheory

-- Generalization plan (G0):
-- concept/name: selected tail measure bound from a three-component real
--   selector decomposition; orig was
--   `theorem62_partA_realized_of_optimization_tail`.
-- generality used: arbitrary measurable sample space, arbitrary measure, four
--   real-valued statistics, two real thresholds, three real component bounds,
--   and one final real bound; no probability, independence, integrability,
--   convexity, oracle, normed-space, or finite-dimensional assumptions are
--   used.
-- portable call pattern: two-phase randomized methods first prove that the
--   selected-output failure statistic is bounded by a weighted sum of three
--   component statistics, then combine separately established component tail
--   bounds; the measure, statistics, thresholds, and numeric bounds change
--   while the tail-composition conclusion stays the same.
-- counterargument checked: Mathlib provides binary `measure_union_le` and
--   finite union bounds, while staged selector decomposition covers only the
--   deterministic pointwise norm split. No existing declaration combines the
--   strict selected-tail threshold complement argument with the three
--   component measure bounds and final real-bound aggregation.
-- coverage search: searched "measure selected tail bound three component tail
--   bounds union subset", "measure union three sets upper bound sum
--   probabilities", and LeanSearch "measure of subset of union of three sets
--   bounded by sum of three measures"; top hits were Mathlib
--   `MeasureTheory.measure_iUnion_fintype_le`,
--   `MeasureTheory.measure_biUnion_finset_le`, `measure_union_le`, and staged
--   finite-supremum union-bound lemmas. These cover union ingredients, not the
--   selector-decomposition strict-tail aggregation with real `ofReal` bounds.
-- minimal hypotheses: all hypotheses are pointwise statistic inequalities or
--   component measure bounds; no measurability or finiteness assumptions are
--   needed beyond `[MeasurableSpace Ω]` for `Measure Ω`.

/-- A selected tail statistic controlled by three component statistics has
measure at most any final real bound dominating the component tail bounds.

If `selected` is pointwise bounded by
`4 * primary + 4 * secondary + 2 * tertiary`, then the strict tail
`selected > 2 * (4 * d + 3 * e)` is contained in the union of the component
tails `primary >= 2 * d`, `secondary > e`, and `tertiary > e`.  Component
`ofReal` tail bounds then sum to any supplied final real bound.

Layer: Glue | Gap: Level 1 (three-component selected-tail union aggregation)
Proof: prove the selected strict tail is contained in the nested union by
  contraposing the three component tail complements, then apply Mathlib's
  binary union subadditivity twice and combine `ENNReal.ofReal` finite sums.
Source: Mathlib outer-measure monotonicity, binary union subadditivity, and
  `ENNReal.ofReal` addition for nonnegative real bounds
Used in: two-phase randomized stochastic-gradient selected-output tail proof,
  after selector decomposition reduces the selected failure event to the
  repeated-run, fixed-validation, and selected-validation failure events
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic gradient descent -/
theorem measure_selected_tail_le_of_three_component_tails
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (selected primary secondary tertiary : Ω -> Real)
    (d e Bprimary Bsecondary Btertiary final : Real)
    (hBprimary_nonneg : 0 ≤ Bprimary)
    (hBsecondary_nonneg : 0 ≤ Bsecondary)
    (hBtertiary_nonneg : 0 ≤ Btertiary)
    (hdecomp : ∀ ω,
      selected ω ≤ 4 * primary ω + 4 * secondary ω + 2 * tertiary ω)
    (hprimary :
      μ {ω | primary ω ≥ 2 * d} ≤ ENNReal.ofReal Bprimary)
    (hsecondary :
      μ {ω | secondary ω > e} ≤ ENNReal.ofReal Bsecondary)
    (htertiary :
      μ {ω | tertiary ω > e} ≤ ENNReal.ofReal Btertiary)
    (hfinal : Bprimary + (Bsecondary + Btertiary) ≤ final) :
    μ {ω | selected ω > 2 * (4 * d + 3 * e)} ≤ ENNReal.ofReal final := by
  let selectedEvent : Set Ω := {ω | selected ω > 2 * (4 * d + 3 * e)}
  let primaryEvent : Set Ω := {ω | primary ω ≥ 2 * d}
  let secondaryEvent : Set Ω := {ω | secondary ω > e}
  let tertiaryEvent : Set Ω := {ω | tertiary ω > e}
  have hsubset :
      selectedEvent ⊆ primaryEvent ∪ (secondaryEvent ∪ tertiaryEvent) := by
    intro ω hω
    by_cases hp : ω ∈ primaryEvent
    · exact Or.inl hp
    by_cases hs : ω ∈ secondaryEvent
    · exact Or.inr (Or.inl hs)
    by_cases ht : ω ∈ tertiaryEvent
    · exact Or.inr (Or.inr ht)
    exfalso
    have hp_lt : primary ω < 2 * d := by
      exact lt_of_not_ge hp
    have hs_le : secondary ω ≤ e := by
      exact le_of_not_gt hs
    have ht_le : tertiary ω ≤ e := by
      exact le_of_not_gt ht
    have hupper :
        4 * primary ω + 4 * secondary ω + 2 * tertiary ω <
          2 * (4 * d + 3 * e) := by
      nlinarith
    have hselected_lt : 2 * (4 * d + 3 * e) < selected ω := by
      simpa [selectedEvent] using hω
    nlinarith [hdecomp ω, hupper, hselected_lt]
  have hsum :
      ENNReal.ofReal Bprimary +
          (ENNReal.ofReal Bsecondary + ENNReal.ofReal Btertiary) =
        ENNReal.ofReal (Bprimary + (Bsecondary + Btertiary)) := by
    rw [← ENNReal.ofReal_add hBsecondary_nonneg hBtertiary_nonneg]
    rw [← ENNReal.ofReal_add hBprimary_nonneg
      (add_nonneg hBsecondary_nonneg hBtertiary_nonneg)]
  calc
    μ {ω | selected ω > 2 * (4 * d + 3 * e)}
        = μ selectedEvent := rfl
    _ ≤ μ (primaryEvent ∪ (secondaryEvent ∪ tertiaryEvent)) :=
      measure_mono hsubset
    _ ≤ μ primaryEvent + μ (secondaryEvent ∪ tertiaryEvent) :=
      measure_union_le primaryEvent (secondaryEvent ∪ tertiaryEvent)
    _ ≤ μ primaryEvent + (μ secondaryEvent + μ tertiaryEvent) := by
      exact add_le_add le_rfl (measure_union_le secondaryEvent tertiaryEvent)
    _ ≤ ENNReal.ofReal Bprimary +
        (ENNReal.ofReal Bsecondary + ENNReal.ofReal Btertiary) :=
      add_le_add hprimary (add_le_add hsecondary htertiary)
    _ = ENNReal.ofReal (Bprimary + (Bsecondary + Btertiary)) := hsum
    _ ≤ ENNReal.ofReal final := ENNReal.ofReal_le_ofReal hfinal
