import Mathlib.Data.Set.Basic

-- Generalization plan (G0):
-- concept/name: membership of a choice-or-default selector under a nonempty
--   candidate-set assumption; orig was choiceOrDefault_mem_of_nonempty.
-- generality used: an arbitrary type `alpha`, candidate set `S : Set alpha`, and
--   arbitrary fallback value; no measure, topology, optimization, or finiteness
--   assumptions are needed.
-- portable call pattern: algorithm proofs that totalize a relational update by
--   choosing a candidate when one exists and using a fallback otherwise can
--   reuse the membership fact while changing the candidate type, set, and
--   fallback value.
-- counterargument checked: this is not paper-local traceability or a caller-side
-- wrapper; the contract packages the recurring dependent-if/choose proof used by
-- totalized algorithm steps, and no exact Mathlib or SOptLib theorem was found.
-- coverage search: searched `choice default membership nonempty set Classical.choose`,
--   `membership of if a set is nonempty choose an element otherwise use a default`,
--   and local `Classical.choose` patterns; Mathlib exposes `Classical.choose_spec`
--   but no matching totalized-selector membership theorem, so coverage is partial.
-- minimal hypotheses: all hypotheses are pointwise and minimal; `default` is
--   required only to make the selector total on empty sets.

open scoped Classical in
/-- A choice-or-default selector belongs to its candidate set whenever that set is
nonempty.

Layer: Glue | Gap: Level 1 (totalized relational-choice membership)
Proof: unfold the dependent conditional under the nonemptiness hypothesis and
apply `Classical.choose_spec` to the resulting selected witness.
Source: Mathlib set nonemptiness, dependent conditionals, and classical choice
specifications
Used in: proving that a canonically selected stochastic-optimization update
satisfies its candidate-step relation whenever the relation has a solution
Book citation: book/ICLR2018/AMSGrad.json#/algorithm_spec
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad Algorithm 2 -/
theorem choiceOrDefault_mem_of_nonempty
    {alpha : Type*} (S : Set alpha) (default : alpha)
    (h : S.Nonempty) :
    (if h' : S.Nonempty then Classical.choose h' else default) ∈ S := by
  rw [dif_pos h]
  exact Classical.choose_spec h
