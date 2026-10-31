import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Real.Basic

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: finite-horizon step-size and momentum schedule domain; orig was Theorem4ParameterDomainOnHorizon
-- generality used: zero/preorder-valued step and momentum schedules indexed by natural time, with no measure, norm, convexity, or finite-dimensional assumptions
-- portable call pattern: adaptive and momentum-based stochastic-optimization proofs instantiate their step-size schedule, momentum schedule, and finite horizon before using positivity or nonnegativity in divisions, Young inequalities, or telescopes
-- counterargument checked: not paper-local traceability or a caller-side expression because the predicate packages a recurring two-schedule horizon contract; not a duplicate of the pointwise stepSize_pos API or any existing finite-window schedule declaration
-- coverage search: searched `finite horizon step size positive momentum weight nonnegative on Icc` and `parameter domain horizon positivity nonnegative schedule`; hits were pointwise step-size accessors and unrelated schedule-specific bounds, so coverage is partial rather than full
-- minimal hypotheses: zero and preorder structure on the schedule codomain and a natural horizon are sufficient; all algorithm-specific setup, dimension, and source-schedule fields are removed

/-- A finite-window domain for positive step sizes and nonnegative momentum weights.

Layer: Model | Concept: finite-horizon step-size and momentum schedule domain
Proof: (definitional construction; conjunction of pointwise schedule sign conditions over `Finset.Icc 1 T`)
Source: Mathlib finite intervals and ordered comparisons, as used in stochastic-gradient and momentum-method parameter domains
Used in: adaptive and momentum-based stochastic-optimization convergence proofs that need horizon-local positivity of update scales and nonnegativity of momentum coefficients before divisions, Young inequalities, or finite telescopes
Book citation: book/ICLR2018/AMSGrad.json#/assumptions
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad (Algorithm 2) -/
def finiteHorizonStepMomentumDomain
    {R : Type*} [Zero R] [Preorder R]
    (alpha beta : ℕ → R) (T : ℕ) : Prop :=
  (∀ t ∈ Finset.Icc 1 T, 0 < alpha t) ∧
    (∀ t ∈ Finset.Icc 1 T, 0 ≤ beta t)

@[simp] theorem finiteHorizonStepMomentumDomain_def
    {R : Type*} [Zero R] [Preorder R]
    (alpha beta : ℕ → R) (T : ℕ) :
    finiteHorizonStepMomentumDomain alpha beta T =
      ((∀ t ∈ Finset.Icc 1 T, 0 < alpha t) ∧
        (∀ t ∈ Finset.Icc 1 T, 0 ≤ beta t)) := rfl

theorem finiteHorizonStepMomentumDomain_alpha_pos
    {R : Type*} [Zero R] [Preorder R]
    {alpha beta : ℕ → R} {T t : ℕ}
    (hdom : finiteHorizonStepMomentumDomain alpha beta T)
    (ht : t ∈ Finset.Icc 1 T) :
    0 < alpha t :=
  hdom.1 t ht

theorem finiteHorizonStepMomentumDomain_beta_nonneg
    {R : Type*} [Zero R] [Preorder R]
    {alpha beta : ℕ → R} {T t : ℕ}
    (hdom : finiteHorizonStepMomentumDomain alpha beta T)
    (ht : t ∈ Finset.Icc 1 T) :
    0 ≤ beta t :=
  hdom.2 t ht

theorem finiteHorizonStepMomentumDomain_restrict
    {R : Type*} [Zero R] [Preorder R]
    {alpha beta : ℕ → R} {T U : ℕ}
    (hdom : finiteHorizonStepMomentumDomain alpha beta T)
    (hU : U ≤ T) :
    finiteHorizonStepMomentumDomain alpha beta U := by
  refine ⟨?_, ?_⟩
  · intro t ht
    exact hdom.1 t (Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp ht).1, (Finset.mem_Icc.mp ht).2.trans hU⟩)
  · intro t ht
    exact hdom.2 t (Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp ht).1, (Finset.mem_Icc.mp ht).2.trans hU⟩)

end SOptLib
