import Staging.finiteMatrixQuadraticForm_segment_expansion
import Mathlib.Tactic

open scoped BigOperators

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: finite symmetric matrix quadratic-form difference expansion;
--   orig was `matrixQuadraticForm_sub_expansion`, renamed away from the AMSGrad
--   paper-local quadratic-form wrapper.
-- generality used: arbitrary finite index type with decidable equality, a real
--   finite matrix, pointwise matrix symmetry, and finite Euclidean coordinate
--   vectors; no measure, convexity, smoothness, oracle, filtration, or
--   positive-definiteness assumptions are used.
-- portable call pattern: projection nonexpansiveness, line-search, and
--   mirror/proximal comparison proofs can expand the metric displacement
--   `Q(q-p,q-p)` into endpoint quadratic terms and the symmetric cross term;
--   the matrix, finite index type, and points vary while the algebraic
--   conclusion stays fixed.
-- counterargument checked: this is not paper-local traceability because it
--   removes AMSGrad coordinate aliases and the positive-definite domain; it is
--   not a pure wrapper over Mathlib because the available matrix API does not
--   expose this subtraction-normalized finite-matrix expansion directly.
-- coverage search: queried `quadratic form subtraction expansion symmetric
--   finite matrix bilinear form` and `Matrix.toBilin quadratic form add smul
--   symmetric expansion`; the relevant public hit is the staged affine-line
--   expansion, while no existing public subtraction expansion covers this
--   statement. Mathlib semantic search timed out.
-- minimal hypotheses: pointwise symmetry is the only matrix hypothesis used;
--   positive definiteness and projection-domain fields from the caller are
--   intentionally dropped.

/-- A symmetric finite real matrix quadratic form expands on a displacement as
the two endpoint quadratic terms minus twice the cross term.

For the Mathlib matrix bilinear form attached to a symmetric real finite
matrix `Q`, evaluating the form at `q - p` gives the endpoint terms and the
symmetric cross term `-2 * Matrix.toBilin' Q q p`.

Layer: Model | Gap: Level 0 (finite symmetric matrix quadratic difference expansion)
Proof: specialize the finite-matrix affine-line expansion at scalar `-1`, then
  simplify `q + (-1) • p` to `q - p` and normalize the real coefficients.
Source: Mathlib matrix bilinear forms over finite real coordinate spaces and elementary quadratic-form algebra
Used in: weighted projection nonexpansiveness rearranges positive-definite metric displacements into endpoint quadratic terms and a mixed product before applying the projection inequalities
Book citation: book/ICLR2018/AMSGrad.json#/key_lemmas/0/proof/1
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad -/
theorem finiteMatrixQuadraticForm_sub_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (hQ : ∀ i j, Q i j = Q j i)
    (p q : EuclideanSpace ℝ ι) :
    Matrix.toBilin' Q (q - p) (q - p) =
      Matrix.toBilin' Q q q - 2 * Matrix.toBilin' Q q p +
        Matrix.toBilin' Q p p := by
  have h := SOptLib.matrix_toBilin_add_smul_self_of_symm Q hQ
    (WithLp.ofLp q) (WithLp.ofLp p) (-1)
  simpa [sub_eq_add_neg, WithLp.ofLp_add, WithLp.ofLp_smul, pow_two] using h

end SOptLib
