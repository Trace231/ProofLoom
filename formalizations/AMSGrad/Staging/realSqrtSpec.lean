import Mathlib.Data.Real.Sqrt

-- Generalization plan (G0):
-- concept/name: realSqrtSpec and coordinateRealSqrtSpec expose scalar and
--   pointwise real square-root witness relations; orig was IsScalarSqrt and
--   IsCoordSqrt.
-- generality used: real-valued scalar witnesses and arbitrary index types with
--   real-valued coordinate functions; no measure, optimization, or finite-dimensional
--   hypotheses are needed.
-- portable call pattern: adaptive-gradient, normalized-gradient, and projected
--   methods can carry explicit square-root witnesses for scalar schedules or
--   coordinatewise second-moment metrics while varying the value and index type.
-- counterargument checked: not paper-local traceability because the predicates
--   are pure real square-root contracts; not a caller-side wrapper because the
--   scalar and pointwise specifications are reused by quotient, metric, and
--   witness-uniqueness proofs.
-- coverage search: searched `nonnegative real square root square equals value`,
--   `coordinatewise square root witness`, and `real sqrt specification`; Mathlib
--   hits `Real.sqrt_nonneg` and `Real.sq_sqrt` provide the component facts but
--   no named relational scalar/coordinate contract, so coverage is partial.
-- minimal hypotheses: nonnegativity is required only by the constructor theorems;
--   the witness predicates themselves intentionally record the nonnegativity
--   and square equations without adding global assumptions.

/-- A real square-root witness is nonnegative and squares to its value.

Layer: Model | Concept: real square-root witness specification
Proof: (definitional construction; pair the nonnegativity and square equations for a real root)
Source: Mathlib real square-root order and square identities
Used in: scalar parameter schedules and denominator or metric obligations that carry an explicit square-root witness
Book citation: book/ICLR2018/AMSGrad.json#/algorithm_spec/steps/5
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad Algorithm 2 -/
def realSqrtSpec (value root : ℝ) : Prop :=
  0 ≤ root ∧ root ^ 2 = value

@[simp] theorem realSqrtSpec_def (value root : ℝ) :
    realSqrtSpec value root = (0 ≤ root ∧ root ^ 2 = value) := rfl

/-- A coordinatewise real square-root witness satisfies the scalar specification at every index.

Layer: Model | Concept: coordinatewise real square-root witness specification
Proof: (definitional construction; lift the scalar witness relation pointwise over an arbitrary index type)
Source: Mathlib real square-root order and square identities with function extensionality
Used in: adaptive diagonal metrics and coordinatewise second-moment denominators whose roots are supplied as vector witnesses
Book citation: book/ICLR2018/AMSGrad.json#/algorithm_spec/steps/5
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad Algorithm 2 -/
def coordinateRealSqrtSpec {ι : Type*}
    (x sqrtx : ι → ℝ) : Prop :=
  ∀ i, realSqrtSpec (x i) (sqrtx i)

@[simp] theorem coordinateRealSqrtSpec_def {ι : Type*}
    (x sqrtx : ι → ℝ) :
    coordinateRealSqrtSpec x sqrtx =
      (∀ i, realSqrtSpec (x i) (sqrtx i)) := rfl

/-- The canonical real square root satisfies the scalar witness specification
when its value is nonnegative.

Layer: Model | Gap: Level 0 (real square-root witness construction)
Proof: combine `Real.sqrt_nonneg` with `Real.sq_sqrt` under the nonnegative-value hypothesis.
Source: Mathlib real square-root nonnegativity and square identity APIs
Used in: constructing checked scalar square-root witnesses for positive schedules, history norms, and adaptive-moment factors
Book citation: book/ICLR2018/AMSGrad.json#/algorithm_spec/steps/5
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad Algorithm 2 -/
theorem realSqrtSpec_of_nonneg {value : ℝ} (hvalue : 0 ≤ value) :
    realSqrtSpec value (Real.sqrt value) := by
  exact ⟨Real.sqrt_nonneg _, Real.sq_sqrt hvalue⟩

/-- Coordinatewise canonical real square roots satisfy the witness specification
when every coordinate value is nonnegative.

Layer: Model | Gap: Level 0 (coordinatewise real square-root witness construction)
Proof: apply the scalar constructor independently at each coordinate.
Source: Mathlib real square-root nonnegativity and square identity APIs with pointwise function reasoning
Used in: constructing adaptive diagonal square-root vectors from nonnegative second-moment coordinates
Book citation: book/ICLR2018/AMSGrad.json#/algorithm_spec/steps/5
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad Algorithm 2 -/
theorem coordinateRealSqrtSpec_of_nonneg {ι : Type*} {x : ι → ℝ}
    (hx : ∀ i, 0 ≤ x i) :
    coordinateRealSqrtSpec x (fun i => Real.sqrt (x i)) := by
  intro i
  exact realSqrtSpec_of_nonneg (hx i)
