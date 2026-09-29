import Mathlib.Data.Real.Basic
import Mathlib.Order.SaddlePoint
import Mathlib.Tactic
import SOptLib.Model.Fenchel

open scoped BigOperators
open scoped InnerProductSpace

namespace SOptLib

/-- The pointwise primal-dual saddle gap associated with a payoff.

For a saddle payoff `L : X → Y → ℝ`, this is the cross evaluation
`L xbar y - L x ybar` at two product points `zbar = (xbar, ybar)` and
`z = (x, y)`.

Layer: Model | Concept: Objective
Proof: (definitional construction; cross difference of a saddle payoff)
Source: convex-analysis saddle-point gaps and Mathlib product projection APIs
Used in: random primal-dual gradient formation of the pointwise saddle gap
  before weighted expectation and saddle-point nonnegativity arguments
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
noncomputable def saddleGap
    {X Y : Type*} (L : X → Y → ℝ) (zbar z : X × Y) : ℝ :=
  L zbar.1 z.2 - L z.1 zbar.2

/-- The pointwise saddle gap unfolds to its cross-evaluation formula.

Layer: Model | Gap: Level 0 (pointwise saddle-gap formula)
Proof: by rfl after unfolding `saddleGap`.
Source: convex-analysis saddle-point gaps and Mathlib product projection APIs
Used in: random primal-dual gradient expansion of the pointwise saddle gap in
  weighted Jensen and one-step recursion algebra
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
@[simp] theorem saddleGap_def
    {X Y : Type*} (L : X → Y → ℝ) (zbar z : X × Y) :
    saddleGap L zbar z = L zbar.1 z.2 - L z.1 zbar.2 := by
  rfl

/-- A saddle point makes every pointwise saddle gap nonnegative.

For a saddle value `L`, Mathlib's `IsSaddlePointOn s t L xstar ystar`
gives the comparison `L xstar y ≤ L x ystar` for `x ∈ s` and `y ∈ t`.
Rewriting this comparison as a nonnegative subtraction gives the usual
primal-dual saddle gap.

Layer: Model | Gap: Level 1 (saddle-point gap nonnegativity)
Proof: apply the defining inequality of `IsSaddlePointOn` at the current
  primal-dual pair, then convert `b ≤ a` into `0 ≤ a - b` with
  `sub_nonneg_of_le`.
Source: Mathlib order-theoretic saddle points and ordered additive group
  subtraction calculus
Used in: random primal-dual gradient dropping pointwise nonnegative saddle
  gaps at an optimal saddle solution before the terminal Bregman bound
Book citation: book/FOML/RandomPrimalDualGradient.json#/main_theorem/proof/7
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem saddleGap_nonneg_of_isSaddlePoint
    {X Y β : Type*} [AddGroup β] [Preorder β] [AddRightMono β]
    {s : Set X} {t : Set Y} (L : X → Y → β) (z zstar : X × Y)
    (hz_left : z.1 ∈ s) (hz_right : z.2 ∈ t)
    (hzstar : IsSaddlePointOn s t L zstar.1 zstar.2) :
    0 ≤ L z.1 zstar.2 - L zstar.1 z.2 := by
  exact sub_nonneg_of_le (hzstar z.1 hz_left z.2 hz_right)

/-- The value of a linearly coupled saddle objective.

This names objectives of the form `r x + <A x, B y> - J y`, where the primal
carrier is evaluated in a Hilbert space and the dual variable contributes a
coupling vector and a penalty.

Layer: Model | Concept: Objective
Proof: (definitional construction; primal regularizer plus inner-product
  coupling minus dual penalty)
Source: convex-analysis saddle reformulations and Mathlib real inner-product
  APIs
Used in: random primal-dual gradient saddle objective before gap formation and
  Fenchel-dual min-max comparisons
Book citation: book/FOML/RandomPrimalDualGradient.json#/setup/saddle_reformulation
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
noncomputable def linearCoupledSaddleValue
    {X Y E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (evalX : X → E) (regularizer : X → ℝ)
    (coupling : Y → E) (dualPenalty : Y → ℝ)
    (x : X) (y : Y) : ℝ :=
  regularizer x + ⟪evalX x, coupling y⟫_ℝ - dualPenalty y

/-- The linearly coupled saddle value unfolds to its defining formula.

Layer: Model | Gap: Level 0 (linearly coupled saddle objective formula)
Proof: by rfl after unfolding `linearCoupledSaddleValue`.
Source: convex-analysis saddle reformulations and Mathlib real inner-product
  APIs
Used in: random primal-dual gradient saddle objective expansion in gap and
  Fenchel-dual algebra
Book citation: book/FOML/RandomPrimalDualGradient.json#/setup/saddle_reformulation
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
@[simp] theorem linearCoupledSaddleValue_def
    {X Y E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (evalX : X → E) (regularizer : X → ℝ)
    (coupling : Y → E) (dualPenalty : Y → ℝ)
    (x : X) (y : Y) :
    linearCoupledSaddleValue evalX regularizer coupling dualPenalty x y =
      regularizer x + ⟪evalX x, coupling y⟫_ℝ - dualPenalty y := by
  rfl

/-- Difference of two linearly coupled saddle values with the primal point fixed.

Layer: Model | Gap: Level 0 (same-primal saddle objective difference)
Proof: unfold the model value, use linearity of the inner product in the dual
  coupling argument, and collect real terms.
Source: convex-analysis saddle gap algebra
Used in: saddle-gap expansion and primal-dual comparison inequalities -/
theorem linearCoupledSaddleValue_sub_same_left
    {X Y E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (evalX : X → E) (regularizer : X → ℝ)
    (coupling : Y → E) (dualPenalty : Y → ℝ)
    (x : X) (y₁ y₂ : Y) :
    linearCoupledSaddleValue evalX regularizer coupling dualPenalty x y₁ -
        linearCoupledSaddleValue evalX regularizer coupling dualPenalty x y₂ =
      ⟪evalX x, coupling y₁ - coupling y₂⟫_ℝ -
        (dualPenalty y₁ - dualPenalty y₂) := by
  simp [linearCoupledSaddleValue, inner_sub_right]
  ring

/-- Difference of two linearly coupled saddle values with the dual point fixed.

Layer: Model | Gap: Level 0 (same-dual saddle objective difference)
Proof: unfold the model value, use linearity of the inner product in the primal
  evaluation argument, and collect real terms.
Source: convex-analysis saddle gap algebra
Used in: saddle-gap expansion and primal-dual comparison inequalities -/
theorem linearCoupledSaddleValue_sub_same_right
    {X Y E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (evalX : X → E) (regularizer : X → ℝ)
    (coupling : Y → E) (dualPenalty : Y → ℝ)
    (x₁ x₂ : X) (y : Y) :
    linearCoupledSaddleValue evalX regularizer coupling dualPenalty x₁ y -
        linearCoupledSaddleValue evalX regularizer coupling dualPenalty x₂ y =
      regularizer x₁ - regularizer x₂ +
        ⟪evalX x₁ - evalX x₂, coupling y⟫_ℝ := by
  simp [linearCoupledSaddleValue, inner_sub_left]
  ring

/-- The linearly coupled Fenchel saddle value touches the weighted objective at
the scaled supporting-gradient dual point.

For each component, a supporting gradient `grad i (evalX x)` at `evalX x`
computes the Fenchel conjugate of `w i • grad i (evalX x)`. Summing those
component equalities cancels the linear coupling in the product saddle value,
leaving the carrier regularizer plus the weighted finite-sum objective.

Layer: Model | Gap: Level 1 (finite-product Fenchel saddle touching equality)
Proof: apply the one-component scaled Fenchel support equality componentwise,
  rewrite the linearly coupled saddle objective by `inner_sum`, and collect the
  finite-sum algebra.
Source: convex analysis Fenchel conjugates and Mathlib finite-sum
  inner-product algebra
Used in: random primal-dual gradient identification of the scaled
  component-gradient dual witness as a saddle value touching the primal
  composite objective
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem linearCoupledSaddleValue_scaledGradientFenchelPoint_eq_objective
    {ι X E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (evalX : X → E) (regularizer : X → ℝ)
    (w : ι → ℝ) (f : ι → E → ℝ) (grad : ι → E → E)
    (x : X) (hw : ∀ i : ι, 0 ≤ w i)
    (hsupport : ∀ i : ι, ∀ z : E,
      f i (evalX x) + ⟪grad i (evalX x), z - evalX x⟫_ℝ ≤ f i z) :
    linearCoupledSaddleValue
        evalX regularizer
        (fun y : (i : ι) → {y : E // y ∈ fenchelConjugateDomain (w i) (f i)} =>
          ∑ i : ι, (y i).1)
        (fun y : (i : ι) → {y : E // y ∈ fenchelConjugateDomain (w i) (f i)} =>
          ∑ i : ι, fenchelConjugateOnCarrier (w i) (f i) (y i))
        x
        (fun i : ι =>
          ⟨w i • grad i (evalX x),
            smul_gradient_mem_fenchelConjugateDomain_of_support
              (f i) (evalX x) (grad i (evalX x)) (hw i) (hsupport i)⟩) =
      regularizer x + ∑ i : ι, w i * f i (evalX x) := by
  classical
  have hFenchel : ∀ i : ι,
      fenchelConjugateOnCarrier (w i) (f i)
          (⟨w i • grad i (evalX x),
            smul_gradient_mem_fenchelConjugateDomain_of_support
              (f i) (evalX x) (grad i (evalX x)) (hw i) (hsupport i)⟩ :
            {y : E // y ∈ fenchelConjugateDomain (w i) (f i)}) =
        ⟪evalX x, w i • grad i (evalX x)⟫_ℝ -
          w i * f i (evalX x) := by
    intro i
    simpa [fenchelConjugateOnCarrier, fenchelConjugateDomain] using
      (fenchel_conjugate_smul_supporting_gradient_eq
        (f := f i) (x := evalX x) (g := grad i (evalX x))
        (c := w i) (hw i) (hsupport i))
  simp only [linearCoupledSaddleValue, hFenchel, inner_sum, Finset.sum_sub_distrib]
  ring

/-- The linearly coupled Fenchel saddle value at a scaled base-gradient dual
point is the weighted first-order model at that base point.

For each component, a supporting gradient at `evalX base` computes the scaled
Fenchel-conjugate value. In the product saddle objective, the component
conjugate terms cancel the base-point linear couplings and leave the
regularizer at `x`, the weighted component values at `base`, and the affine
linearization term from `base` to `x`.

Layer: Model | Gap: Level 1 (finite-product Fenchel saddle linearization)
Proof: apply the componentwise scaled Fenchel support equality, unfold the
  linearly coupled saddle objective, and collect the finite-sum inner-product
  algebra into the weighted first-order model.
Source: convex analysis Fenchel conjugates and Mathlib finite-sum
  inner-product algebra
Used in: random primal-dual gradient conversion of the scaled component-gradient
  saddle value into the first-order model used for the saddle-solution proof
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem linearCoupledSaddleValue_scaledGradientFenchelPoint_eq_firstOrderModel
    {ι X E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (evalX : X → E) (regularizer : X → ℝ)
    (w : ι → ℝ) (f : ι → E → ℝ) (grad : ι → E → E)
    (x base : X) (hw : ∀ i : ι, 0 ≤ w i)
    (hsupport : ∀ i : ι, ∀ z : E,
      f i (evalX base) + ⟪grad i (evalX base), z - evalX base⟫_ℝ ≤ f i z) :
    linearCoupledSaddleValue
        evalX regularizer
        (fun y : (i : ι) → {y : E // y ∈ fenchelConjugateDomain (w i) (f i)} =>
          ∑ i : ι, (y i).1)
        (fun y : (i : ι) → {y : E // y ∈ fenchelConjugateDomain (w i) (f i)} =>
          ∑ i : ι, fenchelConjugateOnCarrier (w i) (f i) (y i))
        x
        (fun i : ι =>
          ⟨w i • grad i (evalX base),
            smul_gradient_mem_fenchelConjugateDomain_of_support
              (f i) (evalX base) (grad i (evalX base)) (hw i) (hsupport i)⟩) =
      regularizer x + ∑ i : ι, w i * f i (evalX base) +
        ⟪evalX x - evalX base, ∑ i : ι, w i • grad i (evalX base)⟫_ℝ := by
  classical
  have hFenchel : ∀ i : ι,
      fenchelConjugateOnCarrier (w i) (f i)
          (⟨w i • grad i (evalX base),
            smul_gradient_mem_fenchelConjugateDomain_of_support
              (f i) (evalX base) (grad i (evalX base)) (hw i) (hsupport i)⟩ :
            {y : E // y ∈ fenchelConjugateDomain (w i) (f i)}) =
        ⟪evalX base, w i • grad i (evalX base)⟫_ℝ -
          w i * f i (evalX base) := by
    intro i
    simpa [fenchelConjugateOnCarrier, fenchelConjugateDomain] using
      (fenchel_conjugate_smul_supporting_gradient_eq
        (f := f i) (x := evalX base) (g := grad i (evalX base))
        (c := w i) (hw i) (hsupport i))
  simp only [linearCoupledSaddleValue, hFenchel, inner_sum, Finset.sum_sub_distrib,
    inner_sub_left]
  ring

/-- A composite minimizer with scaled component-gradient Fenchel coordinates is
a saddle point of the linearly coupled finite-sum saddle objective.

The theorem combines three reusable facts: the scaled-gradient Fenchel point
touches the finite-sum objective, arbitrary Fenchel carrier points give the
dual affine minorant, and the composite minimizer supplies the primal
first-order regularizer bound.

Layer: Model | Gap: Level 1 (scaled-gradient Fenchel saddle witness)
Proof: use the finite-product Fenchel touching equality for the primal
  inequality, the summed Fenchel affine minorant for the dual inequality, and
  chain the two inequalities through the definition of `IsSaddlePointOn`.
Source: convex-analysis Fenchel saddle reformulations and Mathlib saddle-point
  order predicates
Used in: random primal-dual gradient construction of the canonical optimal
  saddle witness from a primal optimizer and scaled component gradients
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem linearCoupledSaddleValue_scaledGradientFenchelPoint_isSaddlePointOn_of_regularizer_firstOrderBound
    {ι X E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (evalX : X → E) (regularizer : X → ℝ)
    (w : ι → ℝ) (f : ι → E → ℝ) (grad : ι → E → E)
    (xStar : X) (hw : ∀ i : ι, 0 ≤ w i)
    (hsupport : ∀ i : ι, ∀ z : E,
      f i (evalX xStar) + ⟪grad i (evalX xStar), z - evalX xStar⟫_ℝ ≤ f i z)
    (hregularizer :
      ∀ x : X,
        regularizer xStar ≤ regularizer x +
          ⟪evalX x - evalX xStar,
            ∑ i : ι, w i • grad i (evalX xStar)⟫_ℝ) :
    IsSaddlePointOn Set.univ Set.univ
      (linearCoupledSaddleValue
        evalX regularizer
        (fun y : (i : ι) → {y : E // y ∈ fenchelConjugateDomain (w i) (f i)} =>
          ∑ i : ι, (y i).1)
        (fun y : (i : ι) → {y : E // y ∈ fenchelConjugateDomain (w i) (f i)} =>
          ∑ i : ι, fenchelConjugateOnCarrier (w i) (f i) (y i)))
      xStar
      (fun i : ι =>
        ⟨w i • grad i (evalX xStar),
          smul_gradient_mem_fenchelConjugateDomain_of_support
            (f i) (evalX xStar) (grad i (evalX xStar)) (hw i) (hsupport i)⟩) := by
  classical
  intro x _hx y _hy
  let yStar : (i : ι) → {y : E // y ∈ fenchelConjugateDomain (w i) (f i)} :=
    fun i : ι =>
      ⟨w i • grad i (evalX xStar),
        smul_gradient_mem_fenchelConjugateDomain_of_support
          (f i) (evalX xStar) (grad i (evalX xStar)) (hw i) (hsupport i)⟩
  have hmin :
      linearCoupledSaddleValue
          evalX regularizer
          (fun y : (i : ι) → {y : E // y ∈ fenchelConjugateDomain (w i) (f i)} =>
            ∑ i : ι, (y i).1)
          (fun y : (i : ι) → {y : E // y ∈ fenchelConjugateDomain (w i) (f i)} =>
            ∑ i : ι, fenchelConjugateOnCarrier (w i) (f i) (y i))
          xStar yStar ≤
        linearCoupledSaddleValue
          evalX regularizer
          (fun y : (i : ι) → {y : E // y ∈ fenchelConjugateDomain (w i) (f i)} =>
            ∑ i : ι, (y i).1)
          (fun y : (i : ι) → {y : E // y ∈ fenchelConjugateDomain (w i) (f i)} =>
            ∑ i : ι, fenchelConjugateOnCarrier (w i) (f i) (y i))
          x yStar := by
    calc
      linearCoupledSaddleValue
          evalX regularizer
          (fun y : (i : ι) → {y : E // y ∈ fenchelConjugateDomain (w i) (f i)} =>
            ∑ i : ι, (y i).1)
          (fun y : (i : ι) → {y : E // y ∈ fenchelConjugateDomain (w i) (f i)} =>
            ∑ i : ι, fenchelConjugateOnCarrier (w i) (f i) (y i))
          xStar yStar =
        regularizer xStar + ∑ i : ι, w i * f i (evalX xStar) := by
          simpa [yStar] using
            (linearCoupledSaddleValue_scaledGradientFenchelPoint_eq_objective
              (evalX := evalX) (regularizer := regularizer)
              (w := w) (f := f) (grad := grad)
              (x := xStar) hw hsupport)
      _ ≤ regularizer x + ∑ i : ι, w i * f i (evalX xStar) +
          ⟪evalX x - evalX xStar,
            ∑ i : ι, w i • grad i (evalX xStar)⟫_ℝ := by
          linarith [hregularizer x]
      _ =
        linearCoupledSaddleValue
          evalX regularizer
          (fun y : (i : ι) → {y : E // y ∈ fenchelConjugateDomain (w i) (f i)} =>
            ∑ i : ι, (y i).1)
          (fun y : (i : ι) → {y : E // y ∈ fenchelConjugateDomain (w i) (f i)} =>
            ∑ i : ι, fenchelConjugateOnCarrier (w i) (f i) (y i))
          x yStar := by
          simpa [yStar] using
            (linearCoupledSaddleValue_scaledGradientFenchelPoint_eq_firstOrderModel
              (evalX := evalX) (regularizer := regularizer)
              (w := w) (f := f) (grad := grad)
              (x := x) (base := xStar) hw hsupport).symm
  have hmax :
      linearCoupledSaddleValue
          evalX regularizer
          (fun y : (i : ι) → {y : E // y ∈ fenchelConjugateDomain (w i) (f i)} =>
            ∑ i : ι, (y i).1)
          (fun y : (i : ι) → {y : E // y ∈ fenchelConjugateDomain (w i) (f i)} =>
            ∑ i : ι, fenchelConjugateOnCarrier (w i) (f i) (y i))
          xStar y ≤
        linearCoupledSaddleValue
          evalX regularizer
          (fun y : (i : ι) → {y : E // y ∈ fenchelConjugateDomain (w i) (f i)} =>
            ∑ i : ι, (y i).1)
          (fun y : (i : ι) → {y : E // y ∈ fenchelConjugateDomain (w i) (f i)} =>
            ∑ i : ι, fenchelConjugateOnCarrier (w i) (f i) (y i))
          xStar yStar := by
    have hFenchel :=
      sum_fenchel_affine_minorant_le_weighted_objective
        (w := w) (f := f) (y := fun i : ι => (y i).1)
        (hy := fun i : ι => (y i).2) (x := evalX xStar)
    have hFenchel' :
        ⟪evalX xStar, ∑ i : ι, (y i).1⟫_ℝ -
            ∑ i : ι, fenchelConjugateOnCarrier (w i) (f i) (y i) ≤
          ∑ i : ι, w i * f i (evalX xStar) := by
      simpa only [Subtype.coe_eta] using hFenchel
    calc
      linearCoupledSaddleValue
          evalX regularizer
          (fun y : (i : ι) → {y : E // y ∈ fenchelConjugateDomain (w i) (f i)} =>
            ∑ i : ι, (y i).1)
          (fun y : (i : ι) → {y : E // y ∈ fenchelConjugateDomain (w i) (f i)} =>
            ∑ i : ι, fenchelConjugateOnCarrier (w i) (f i) (y i))
          xStar y ≤
        regularizer xStar + ∑ i : ι, w i * f i (evalX xStar) := by
          change regularizer xStar + ⟪evalX xStar, ∑ i : ι, (y i).1⟫_ℝ -
              ∑ i : ι, fenchelConjugateOnCarrier (w i) (f i) (y i) ≤
            regularizer xStar + ∑ i : ι, w i * f i (evalX xStar)
          linarith
      _ =
        linearCoupledSaddleValue
          evalX regularizer
          (fun y : (i : ι) → {y : E // y ∈ fenchelConjugateDomain (w i) (f i)} =>
            ∑ i : ι, (y i).1)
          (fun y : (i : ι) → {y : E // y ∈ fenchelConjugateDomain (w i) (f i)} =>
            ∑ i : ι, fenchelConjugateOnCarrier (w i) (f i) (y i))
          xStar yStar := by
          simpa [yStar] using
            (linearCoupledSaddleValue_scaledGradientFenchelPoint_eq_objective
              (evalX := evalX) (regularizer := regularizer)
              (w := w) (f := f) (grad := grad)
              (x := xStar) hw hsupport).symm
  exact le_trans hmax hmin

end SOptLib
