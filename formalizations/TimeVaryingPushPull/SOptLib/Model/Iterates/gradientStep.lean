import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: gradient step; orig was the PAGE-local `primalUpdate`
-- generality used: an additive group equipped with a real scalar action,
--   which are exactly the algebraic structures needed for subtraction and
--   scalar multiplication; no commutativity, module laws, objective, measure,
--   probability, or finite-dimensional assumptions are used.
-- portable call pattern: gradient, stochastic-gradient, and variance-reduced
--   algorithms can reuse the same affine step by changing the scalar η,
--   current point x, and direction g while keeping the update conclusion.
-- counterargument checked: the source expression is a caller-side affine
--   update, but naming this recurring algorithmic object gives a shared Model
--   API; searches found no existing SOptLib or Mathlib declaration for this
--   plain gradient-step contract.
-- coverage search: searched "gradient affine update scalar multiple subtraction",
--   "gradient step", and "affine update"; existing hits were conditional-
--   gradient updates or downstream bounds and did not cover this object.
-- minimal hypotheses: reduced the source Hilbert, completeness, and finite-
--   dimensional assumptions to `[AddGroup E] [SMul ℝ E]`.

/-- Apply a scalar gradient step to a point by subtracting the scaled direction.

Layer: Model | Concept: affine gradient step
Proof: (definitional construction; subtraction of a real scalar multiple of the direction)
Source: Mathlib additive-group and module scalar-action APIs for first-order update formulas
Used in: primal updates of PAGE and other gradient, stochastic-gradient, and variance-reduced algorithms
Book citation: book/research/PAGE.json#/algorithm_spec/steps/0
Origin algorithm: Li, Bao, Zhang, and Richtárik, PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization -/
def gradientStep {E : Type*} [AddGroup E] [SMul ℝ E]
    (η : ℝ) (x g : E) : E :=
  x - η • g

/-- The gradient step unfolds to its affine update formula.

Layer: Model | Gap: Level 0 (gradient-step unfolding)
Proof: by rfl after unfolding `gradientStep`.
Source: Mathlib additive-group subtraction and module scalar-action APIs
Used in: exposing the primal affine update when a downstream proof needs pointwise algebra
Book citation: book/research/PAGE.json#/algorithm_spec/steps/0
Origin algorithm: Li, Bao, Zhang, and Richtárik, PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization -/
@[simp] theorem gradientStep_def {E : Type*} [AddGroup E] [SMul ℝ E]
    (η : ℝ) (x g : E) :
    gradientStep η x g = x - η • g := by
  rfl

/-- The displacement produced by a gradient step is the negated scaled direction. -/
theorem gradientStep_displacement {E : Type*} [AddCommGroup E] [SMul ℝ E]
    (η : ℝ) (x g : E) :
    gradientStep η x g - x = -(η • g) := by
  simp [gradientStep, sub_eq_add_neg, add_comm]

end SOptLib

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: inverse-metric preconditioned gradient step; orig was `omdUpdate`
-- generality used: an arbitrary finite decidable coordinate type, a real step size,
--   a real square preconditioner, and real direction and iterate vectors; no positivity,
--   invertibility, convexity, smoothness, probability, or oracle assumptions are used
-- portable call pattern: adaptive-gradient and unconstrained online mirror-descent methods
--   reuse the update while changing the coordinate type, step size, preconditioner,
--   gradient, and current iterate
-- counterargument checked: although the formula composes `gradientStep` with matrix-vector
--   multiplication, the recurring inverse-metric direction is the defining mathematical
--   content of a preconditioned step and merits a stable Model API rather than paper-local
--   notation; the richer two-sided Shampoo transition does not cover this one-sided object
-- coverage search: searches for "preconditioned gradient step inverse matrix", "inverse
--   metric gradient update", and "gradientStep matrix mulVec" found `SOptLib.gradientStep`
--   and `SOptLib.twoSidedMatrixPreconditionedStep` only as partial matches; Mathlib semantic
--   search found gradient calculus and matrix inverse primitives but no matching step object
-- minimal hypotheses: `Fintype` supports `mulVec`'s finite sum and `DecidableEq` supports
--   Mathlib's total square-matrix inverse; all other source assumptions are omitted

/-- Take an unconstrained gradient step in the direction obtained by applying the inverse
of a finite-dimensional matrix preconditioner to the supplied gradient.

The matrix inverse is Mathlib's total inverse, so the construction is defined even when the
preconditioner is singular; applications may separately impose positive definiteness.

Layer: Model | Concept: finite-dimensional inverse-metric preconditioned gradient step
Proof: (definitional construction; apply `gradientStep` to the inverse-matrix product `H⁻¹.mulVec g`)
Source: Mathlib finite matrix multiplication and total nonsingular inverse, together with SOptLib's affine `gradientStep`
Used in: adaptive-gradient and online mirror-descent iterate recurrences whose unconstrained update uses the inverse current metric
Book citation: book/research/Source.json#/main_theorem/proof/1/math
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, adaptive online mirror descent -/
noncomputable def preconditionedGradientStep
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η : ℝ) (H : Matrix ι ι ℝ) (g w : ι → ℝ) : ι → ℝ :=
  gradientStep η w (H⁻¹.mulVec g)

/-- A preconditioned gradient step unfolds to subtraction of the scaled inverse-metric
direction.

Layer: Model | Gap: Level 0 (inverse-metric preconditioned-step unfolding)
Proof: by rfl after unfolding `preconditionedGradientStep` and `gradientStep`.
Source: Mathlib finite matrix-vector multiplication and total matrix inverse, with SOptLib's affine `gradientStep` specification
Used in: adaptive-gradient and online mirror-descent proofs that expose the iterate recurrence for one-step metric algebra
Book citation: book/research/Source.json#/main_theorem/proof/1/math
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, adaptive online mirror descent -/
@[simp] theorem preconditionedGradientStep_def
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η : ℝ) (H : Matrix ι ι ℝ) (g w : ι → ℝ) :
    preconditionedGradientStep η H g w = w - η • H⁻¹.mulVec g := by
  rfl

/-- Applying a nonsingular preconditioner to the displacement of its gradient step
recovers the negated scaled supplied direction.

Layer: Model | Gap: Level 0 (preconditioned-step displacement cancellation)
Proof: expose the affine-step displacement, commute matrix-vector multiplication with
negation and scalar multiplication, and cancel the nonsingular inverse.
Source: Mathlib matrix-vector multiplication and nonsingular-inverse cancellation
Used in: adaptive-gradient and online mirror-descent proofs that convert a preconditioned
iterate recurrence back to its supplied gradient direction
Book citation: book/research/Source.json#/main_theorem/proof/1/math
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, adaptive online mirror descent -/
theorem preconditionedGradientStep_displacement
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η : ℝ) (H : Matrix ι ι ℝ) (g w : ι → ℝ)
    (hH : IsUnit H.det) :
    H.mulVec (preconditionedGradientStep η H g w - w) = -(η • g) := by
  calc
    H.mulVec (preconditionedGradientStep η H g w - w) =
        H.mulVec (-(η • H⁻¹.mulVec g)) := by
      rw [preconditionedGradientStep, gradientStep_displacement]
    _ = -(η • H.mulVec (H⁻¹.mulVec g)) := by
      rw [Matrix.mulVec_neg, Matrix.mulVec_smul]
    _ = -(η • (H * H⁻¹).mulVec g) := by
      rw [Matrix.mulVec_mulVec]
    _ = -(η • g) := by
      rw [H.mul_nonsing_inv hH, Matrix.one_mulVec]

end SOptLib
