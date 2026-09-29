import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Process.Filtration

open MeasureTheory ProbabilityTheory

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: martingale-difference L2 hypotheses; orig was
--   `MartingaleDifferenceHypotheses`, renamed away from the paper-local
--   source lemma boundary while exposing the reusable filtration, conditional
--   centering, and second-moment budget contract.
-- generality used: arbitrary measurable sample space, arbitrary measure,
--   arbitrary complete real normed additive target space with measurable structure,
--   natural-time filtration, increment process, and scalar L2 budget sequence;
--   no objective, gradient, oracle, convexity, smoothness, probability, or
--   finite-dimensional assumption is used by the predicate itself.
-- portable call pattern: martingale second-moment and validation residual
--   proofs call this before applying finite covariance diagonalization or
--   Markov tails; the probability space, filtration, increments, and budget
--   sequence vary while the prerequisite contract stays unchanged.
-- counterargument checked: hypothesis-only structures can be paper-local, but
--   this bundle is the reusable boundary repeatedly opened by martingale
--   second-moment and tail proofs; it is not a pure wrapper over Mathlib
--   because Mathlib has no predicate bundling adaptedness, conditional mean
--   zero, L2 integrability, and per-time budgets over a filtration.
-- coverage search: searched `martingale difference L2 hypotheses filtration
--   conditional mean zero second moment bound`, `filtration monotone adapted
--   conditional expectation zero integrable squared norm`, and catalog entries
--   for centered residual processes; closest hits were
--   `SOptLib.AdaptiveCenteredOracleProcess`, SOptLib martingale cancellation
--   lemmas, and finite second-moment bounds, all partial because none includes
--   the full filtered L2 martingale-difference prerequisite contract.
-- minimal hypotheses: kept only the target measurable-space and normed-space
--   structure needed to state measurability, conditional expectation,
--   integrability, squared norms, and scalar budget inequalities.

/-- Bundled L2 martingale-difference hypotheses for a filtered sequence.

The predicate records adapted increments, conditional mean zero, Bochner
integrability, squared-norm integrability, and per-time second-moment budgets
for indices `i >= 1`.

Layer: Glue | Concept: martingale-difference L2 hypotheses
Proof: (definitional construction; conjunction of adaptedness, conditional centering, integrability, and second-moment budget clauses)
Source: Mathlib filtration-as-sub-sigma-algebra order, conditional expectation, Bochner integrability, and squared-norm moment notation
Used in: martingale second-moment and validation residual tail proofs before diagonalizing covariance sums and applying Markov bounds
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/theorems/0/proof/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, two-phase randomized stochastic gradient descent -/
def MartingaleDifferenceL2Hypotheses
    {Ω E : Type*} [mΩ : MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
    (mu : Measure Ω) (F : Filtration Nat mΩ)
    (zeta : Nat -> Ω -> E) (sigmaSeq : Nat -> ℝ) : Prop :=
  (forall i : Nat, 1 <= i ->
    @Measurable Ω E (F i) _ (zeta i)) /\
    (forall i : Nat, 1 <= i -> Integrable (zeta i) mu) /\
    (forall i : Nat, 1 <= i ->
      mu[zeta i | F (i - 1)] =ᵐ[mu] (fun _ => (0 : E))) /\
    (forall i : Nat, 1 <= i ->
      Integrable (fun ω => ‖zeta i ω‖ ^ 2) mu) /\
    (forall i : Nat, 1 <= i ->
      (∫ ω, ‖zeta i ω‖ ^ 2 ∂mu) <= sigmaSeq i ^ 2)

@[simp]
theorem MartingaleDifferenceL2Hypotheses_def
    {Ω E : Type*} [mΩ : MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
    (mu : Measure Ω) (F : Filtration Nat mΩ)
    (zeta : Nat -> Ω -> E) (sigmaSeq : Nat -> ℝ) :
    MartingaleDifferenceL2Hypotheses mu F zeta sigmaSeq =
      ((forall i : Nat, 1 <= i ->
        @Measurable Ω E (F i) _ (zeta i)) /\
        (forall i : Nat, 1 <= i -> Integrable (zeta i) mu) /\
        (forall i : Nat, 1 <= i ->
          mu[zeta i | F (i - 1)] =ᵐ[mu] (fun _ => (0 : E))) /\
        (forall i : Nat, 1 <= i ->
          Integrable (fun ω => ‖zeta i ω‖ ^ 2) mu) /\
        (forall i : Nat, 1 <= i ->
          (∫ ω, ‖zeta i ω‖ ^ 2 ∂mu) <= sigmaSeq i ^ 2)) := rfl

theorem MartingaleDifferenceL2Hypotheses.measurable
    {Ω E : Type*} [mΩ : MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
    {mu : Measure Ω} {F : Filtration Nat mΩ}
    {zeta : Nat -> Ω -> E} {sigmaSeq : Nat -> ℝ}
    (h : MartingaleDifferenceL2Hypotheses mu F zeta sigmaSeq)
    (i : Nat) (hi : 1 <= i) :
    @Measurable Ω E (F i) _ (zeta i) := by
  exact h.1 i hi

theorem MartingaleDifferenceL2Hypotheses.integrable
    {Ω E : Type*} [mΩ : MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
    {mu : Measure Ω} {F : Filtration Nat mΩ}
    {zeta : Nat -> Ω -> E} {sigmaSeq : Nat -> ℝ}
    (h : MartingaleDifferenceL2Hypotheses mu F zeta sigmaSeq)
    (i : Nat) (hi : 1 <= i) :
    Integrable (zeta i) mu := by
  exact h.2.1 i hi

theorem MartingaleDifferenceL2Hypotheses.condExp_eq_zero
    {Ω E : Type*} [mΩ : MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
    {mu : Measure Ω} {F : Filtration Nat mΩ}
    {zeta : Nat -> Ω -> E} {sigmaSeq : Nat -> ℝ}
    (h : MartingaleDifferenceL2Hypotheses mu F zeta sigmaSeq)
    (i : Nat) (hi : 1 <= i) :
    mu[zeta i | F (i - 1)] =ᵐ[mu] (fun _ => (0 : E)) := by
  exact h.2.2.1 i hi

theorem MartingaleDifferenceL2Hypotheses.integrable_norm_sq
    {Ω E : Type*} [mΩ : MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
    {mu : Measure Ω} {F : Filtration Nat mΩ}
    {zeta : Nat -> Ω -> E} {sigmaSeq : Nat -> ℝ}
    (h : MartingaleDifferenceL2Hypotheses mu F zeta sigmaSeq)
    (i : Nat) (hi : 1 <= i) :
    Integrable (fun ω => ‖zeta i ω‖ ^ 2) mu := by
  exact h.2.2.2.1 i hi

theorem MartingaleDifferenceL2Hypotheses.second_moment_le
    {Ω E : Type*} [mΩ : MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
    {mu : Measure Ω} {F : Filtration Nat mΩ}
    {zeta : Nat -> Ω -> E} {sigmaSeq : Nat -> ℝ}
    (h : MartingaleDifferenceL2Hypotheses mu F zeta sigmaSeq)
    (i : Nat) (hi : 1 <= i) :
    (∫ ω, ‖zeta i ω‖ ^ 2 ∂mu) <= sigmaSeq i ^ 2 := by
  exact h.2.2.2.2 i hi

end SOptLib
