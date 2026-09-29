import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.Tactic

open MeasureTheory
open scoped BigOperators

namespace SOptLib

theorem measure_finset_sup_gt_le_sum_measure_gt
    {Omega iota : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (I : Finset iota) (hI : I.Nonempty)
    (E : iota -> Omega -> Real) (threshold : Real) :
    mu {omega | I.sup' hI (fun i => E i omega) > threshold} <=
      ∑ i ∈ I, mu {omega | E i omega > threshold} := by
  classical
  have hsubset :
      {omega | I.sup' hI (fun i => E i omega) > threshold} ⊆
        ⋃ i, ⋃ _hi : i ∈ I, {omega | E i omega > threshold} := by
    intro omega homega
    have hlt : threshold < I.sup' hI (fun i => E i omega) := homega
    rcases (Finset.lt_sup'_iff hI).mp hlt with ⟨i, hi, hi_gt⟩
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hi_gt⟩⟩
  calc
    mu {omega | I.sup' hI (fun i => E i omega) > threshold}
        <= mu (⋃ i, ⋃ _hi : i ∈ I, {omega | E i omega > threshold}) :=
          measure_mono hsubset
    _ <= ∑ i ∈ I, mu {omega | E i omega > threshold} :=
          measure_biUnion_finset_le I (fun i => {omega | E i omega > threshold})

-- Generalization plan (G0):
-- concept/name: finite supremum strict-tail union bound from per-index strict
--   tail estimates; orig was `fixed_candidate_sup_tail_union_bound`.
-- generality used: arbitrary measurable sample space, arbitrary measure, any
--   nonempty finite index set, real-valued statistics, and a scalar `lambda`;
--   no probability, independence, integrability, convexity, oracle, normed
--   space, or finite-dimensional assumptions are used.
-- portable call pattern: validation and confidence proofs for stochastic
--   algorithms first prove a strict tail estimate for each candidate or block,
--   then bound the strict tail of the maximum statistic by the number of
--   candidates times the per-index tail; the finite index set, measure,
--   statistic, threshold, and scalar tail parameter change. Positivity of
--   `lambda` belongs to callers that establish the per-index estimate, not to
--   this union-bound wrapper.
-- counterargument checked: Mathlib provides the finite union bound
--   `measure_biUnion_finset_le`, but not the combined strict-tail-of-supremum
--   wrapper with the cardinality-divided real bound needed at stochastic
--   optimization call sites.
-- coverage search: queried "measure of supremum greater than threshold finite
--   union bound forall measure greater le card", "measure_iUnion_fintype_le
--   finite union bound measure", and LeanSearch "measure of finite supremum
--   greater than threshold bounded by sum union bound"; top hits were
--   Mathlib's `MeasureTheory.measure_iUnion_fintype_le` and
--   `MeasureTheory.measure_biUnion_finset_le`, plus unrelated SOptLib Markov
--   and finite-sampling lemmas. These cover the union-bound component only.
-- minimal hypotheses: the source nonempty `Fin S` assumption is narrowed to
--   `I.Nonempty`; the proof only uses the supplied per-index ENNReal bounds
--   and finite-union arithmetic.

/-- A finite supremum strict-tail probability is bounded by the number of
indices times a uniform per-index strict-tail bound.

If every statistic in a nonempty finite family satisfies
`mu {omega | E i omega > threshold} <= ofReal (1 / lambda)`, then the strict
tail of the finite supremum is at most `ofReal (I.card / lambda)`.

Layer: Glue | Gap: Level 1 (finite supremum strict-tail union bound)
Proof: embed the strict tail of the `Finset.sup'` in the finite union of the
  component strict-tail events, apply Mathlib's finite union bound, and rewrite
  the constant finite sum in `ENNReal`.
Source: Mathlib finite-set supremum order API, outer-measure finite union
  bound, and `ENNReal.ofReal` finite-sum arithmetic
Used in: two-phase stochastic-gradient validation, passing from per-candidate
  post-optimization empirical-gradient tail estimates to the candidate-list
  maximum error term in the fixed-candidate union-bound display
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/main_theorem/proof/9
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic gradient descent -/
theorem measure_finset_sup_gt_le_card_div_of_forall_measure_gt_le
    {Omega iota : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (I : Finset iota) (hI : I.Nonempty)
    (E : iota -> Omega -> Real) (threshold lambda : Real)
    (hper : forall i, i ∈ I ->
      mu {omega | E i omega > threshold} <= ENNReal.ofReal (1 / lambda)) :
    mu {omega | I.sup' hI (fun i => E i omega) > threshold} <=
      ENNReal.ofReal ((I.card : Real) / lambda) := by
  classical
  calc
    mu {omega | I.sup' hI (fun i => E i omega) > threshold}
        <= ∑ i ∈ I, mu {omega | E i omega > threshold} :=
          measure_finset_sup_gt_le_sum_measure_gt
            (mu := mu) (I := I) (hI := hI) (E := E) (threshold := threshold)
    _ <= ∑ _i ∈ I, ENNReal.ofReal (1 / lambda) := by
          exact Finset.sum_le_sum (by
            intro i hi
            exact hper i hi)
    _ = ENNReal.ofReal ((I.card : Real) / lambda) := by
          rw [Finset.sum_const]
          simp [nsmul_eq_mul, ENNReal.ofReal_natCast, div_eq_mul_inv,
            ENNReal.ofReal_mul (by positivity : 0 <= (I.card : Real))]

end SOptLib
