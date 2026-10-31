import SOptLib.Model.Objective

open scoped BigOperators

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: finite-horizon regret against the infimum fixed comparator;
--   orig was `generatedRegretAgainstInfimum`, renamed away from AMSGrad-specific
--   generated-run terminology.
-- generality used: arbitrary carrier type, feasible comparator set, real-valued
--   loss family, iterate sequence, and finite horizon; no measure, topology,
--   convexity, smoothness, oracle, Hilbert, or finite-dimensional assumptions
--   are used by the definition.
-- portable call pattern: online convex optimization and adaptive-gradient
--   regret proofs call this when replacing the paper expression "cumulative
--   iterate loss minus best fixed feasible comparator loss" by a named model
--   object; the algorithm, feasible set, loss family, iterates, and horizon vary
--   while the conclusion shape stays unchanged.
-- counterargument checked: not just paper-local traceability because the same
--   infimum comparator regret boundary recurs whenever comparator attainment is
--   not assumed; not a duplicate of `objectiveInfimumValue` because this
--   packages the finite-horizon loss aggregation and iterate-loss subtraction
--   around that objective infimum reference.
-- coverage search: searched `finite horizon regret cumulative loss minus
--   infimum fixed comparator`, `objective infimum value sInf image feasible
--   set`, and catalog tokens `regret infimum fixed comparator`; closest hits
--   were AMSGrad-local `regretAgainstInfimum`/`generatedRegretAgainstInfimum`
--   and SOptLib `objectiveInfimumValue`, which is reused here but does not
--   include the finite-horizon regret construction.
-- minimal hypotheses: all already minimal; the feasible-set infimum is stated
--   directly through the feasible subtype and does not require attainment,
--   nonemptiness, or bounded-below assumptions to name the value.

/-- Finite-horizon regret against the infimum fixed feasible comparator.

This names the online-learning quantity given by cumulative loss along an
iterate sequence minus the infimum, over feasible fixed comparators, of the same
finite-horizon cumulative loss.

Layer: Model | Concept: finite-horizon regret against infimum comparator
Proof: (definitional construction; finite sum of iterate losses minus the
  `objectiveInfimumValue` over feasible fixed-comparator cumulative losses)
Source: Mathlib finite sums over natural-number intervals and SOptLib objective
  infimum values over feasible carriers
Used in: AMSGrad Algorithm 2 finite-horizon regret bound for the generated
  checked iterate sequence when no comparator-attainment assumption is supplied
Book citation: book/ICLR2018/AMSGrad.json#/setup/problem
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond,
  AMSGrad Algorithm 2 -/
noncomputable def finiteHorizonRegretAgainstInfimum {E : Type*}
    (F : Set E) (loss : ℕ → E → ℝ) (x : ℕ → E) (T : ℕ) : ℝ :=
  ((Finset.Icc 1 T).sum fun t => loss t (x t)) -
    objectiveInfimumValue (Set.univ : Set {y : E // y ∈ F})
      (fun y : {y : E // y ∈ F} =>
        (Finset.Icc 1 T).sum fun t => loss t y.1)

/-- The finite-horizon regret against an infimum comparator unfolds to cumulative
iterate loss minus the `sInf` of feasible fixed-comparator cumulative losses.

Layer: Model | Gap: Level 0 (finite-horizon regret formula)
Proof: by rfl after unfolding `finiteHorizonRegretAgainstInfimum` and
  `objectiveInfimumValue`.
Source: Mathlib finite sums over intervals and conditionally complete lattice
  infimum API for real-valued set images
Used in: AMSGrad finite-horizon regret proof when rewriting the generated
  checked process regret back to the source-facing comparator-infimum expression
Book citation: book/ICLR2018/AMSGrad.json#/setup/problem
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond,
  AMSGrad Algorithm 2 -/
@[simp]
theorem finiteHorizonRegretAgainstInfimum_def {E : Type*}
    (F : Set E) (loss : ℕ → E → ℝ) (x : ℕ → E) (T : ℕ) :
    finiteHorizonRegretAgainstInfimum F loss x T =
      ((Finset.Icc 1 T).sum fun t => loss t (x t)) -
        sInf ((fun y : {y : E // y ∈ F} =>
          (Finset.Icc 1 T).sum fun t => loss t y.1) '' Set.univ) := by
  rfl

/-- A uniform fixed-comparator regret bound also bounds regret against the
infimum feasible comparator value.

Layer: Model | Gap: Level 1 (finite-horizon uniform comparator bound to
  infimum-comparator regret bound)
Proof: convert the uniform comparator inequality to a lower bound on every
  feasible fixed-comparator cumulative loss, apply `le_csInf`, then rearrange.
Source: Mathlib finite sums and conditionally complete linear-order infimum API
Used in: adaptive-gradient and online-optimization regret proofs that first
  prove bounds against every fixed feasible comparator and then pass to the
  infimum comparator value -/
theorem finiteHorizonRegretAgainstInfimum_le_of_uniform_comparator_bound
    {E : Type*} {F : Set E} {loss : ℕ → E → ℝ} {x : ℕ → E} {T : ℕ} {B : ℝ}
    (hF : F.Nonempty)
    (hbound :
      ∀ y ∈ F,
        ((Finset.Icc 1 T).sum fun t => loss t (x t)) -
          ((Finset.Icc 1 T).sum fun t => loss t y) ≤ B) :
    finiteHorizonRegretAgainstInfimum F loss x T ≤ B := by
  let A : ℝ := (Finset.Icc 1 T).sum fun t => loss t (x t)
  let S : Set ℝ := (fun y : {y : E // y ∈ F} =>
    (Finset.Icc 1 T).sum fun t => loss t y.1) '' Set.univ
  have hnonempty : S.Nonempty := by
    rcases hF with ⟨y, hy⟩
    refine ⟨(Finset.Icc 1 T).sum fun t => loss t y, ?_⟩
    exact ⟨⟨y, hy⟩, Set.mem_univ _, rfl⟩
  have hlower : ∀ y ∈ S, A - B ≤ y := by
    intro y hy
    rcases hy with ⟨z, _hz, rfl⟩
    have hz_bound := hbound z.1 z.2
    change A - (Finset.Icc 1 T).sum (fun t => loss t z.1) ≤ B at hz_bound
    linarith
  have hle_inf : A - B ≤ sInf S := le_csInf hnonempty hlower
  rw [finiteHorizonRegretAgainstInfimum_def]
  change A - sInf S ≤ B
  linarith

end SOptLib
