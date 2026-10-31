import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import SOptLib.Model.Prox.finiteMatrixWeightedProjectionArgmin
import SOptLib.Model.Norms.FiniteMatrixQuadraticForm
namespace SOptLib

-- Generalization plan (G0):
-- concept/name: finite matrix weighted projection minimizes the associated quadratic form; orig was `weighted_projection_minimizes_quadratic_form`.
-- generality used: finite real Euclidean coordinate space `EuclideanSpace ℝ ι` with `[Fintype ι]`, a real matrix metric with pointwise nonnegative quadratic form, and a parameterized feasible argmin for the named matrix weighted norm; no measure, convexity, smoothness, or oracle assumptions are needed.
-- portable call pattern: adaptive-gradient and projected-gradient proofs can supply a feasible set, a metric with nonnegative quadratic form, a center, and a weighted-norm argmin to obtain quadratic-form minimality; the set, metric, and center vary while the conclusion stays unchanged.
-- counterargument checked: this is not paper-local traceability or a caller-side expression because it is the reusable non-linear bridge from a matrix weighted-norm argmin to its squared quadratic-form comparison; it does not duplicate the argmin or positive-definite metric APIs.
-- coverage search: queried `finite matrix weighted projection minimizes quadratic form argmin positive definite metric` and `parameterized feasible argmin forall objective minimizer`; existing hits were the staged argmin relation and positive-definite square identity, which are inputs rather than this composed minimization theorem.
-- minimal hypotheses: finite coordinates are required by the finite-matrix APIs, while only pointwise nonnegativity is needed for the square-root identity; no convexity or measure assumptions are needed.

/-- A finite-matrix weighted projection with nonnegative quadratic form minimizes the associated
quadratic form over the feasible set.

The theorem squares the nonnegative matrix weighted-norm comparison supplied by
the feasible argmin relation and rewrites each square as the corresponding
finite-matrix quadratic form using pointwise nonnegativity.

Layer: Model | Gap: Level 1 (weighted-norm argmin to quadratic-form minimality)
Proof: use the pointwise form of the parameterized feasible argmin, apply monotonicity of squaring on nonnegative reals, and rewrite with the real square-root identity under pointwise quadratic-form nonnegativity.
Source: finite-dimensional quadratic forms, real square-root arithmetic, and Mathlib feasible-argmin order predicates
Used in: adaptive projected-gradient and matrix-metric projection proofs that need to replace a weighted-norm projection comparison by a quadratic-form inequality before deriving variational inequalities or contraction bounds
Book citation: book/ICLR2018/AMSGrad.json#/key_lemmas/0/proof/0
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad Algorithm 2 -/
theorem finite_matrix_weighted_projection_minimizes_quadratic_form
    {ι : Type*} [Fintype ι]
    (F : Set (EuclideanSpace ℝ ι)) (metric : ι → ι → ℝ)
    (z u : EuclideanSpace ℝ ι)
    (hmetric : ∀ v, 0 ≤ finiteMatrixQuadraticForm metric v)
    (hproj :
      parameterizedFeasibleArgmin
        (fun metric y x =>
          positiveDefiniteFiniteMatrixWeightedNorm metric (x - y))
        F metric z u) :
    u ∈ F ∧
      ∀ x ∈ F,
        finiteMatrixQuadraticForm metric (u - z) ≤
          finiteMatrixQuadraticForm metric (x - z) := by
  have hmin :
      u ∈ F ∧
        ∀ x ∈ F,
          positiveDefiniteFiniteMatrixWeightedNorm metric (u - z) ≤
            positiveDefiniteFiniteMatrixWeightedNorm metric (x - z) :=
    (parameterizedFeasibleArgmin_iff_forall_le
      (fun metric y x =>
        positiveDefiniteFiniteMatrixWeightedNorm metric (x - y))
      F metric z u).1 hproj
  refine ⟨hmin.1, ?_⟩
  intro x hx
  have hleft_nonneg :
      0 ≤ positiveDefiniteFiniteMatrixWeightedNorm metric (u - z) := by
    simp [positiveDefiniteFiniteMatrixWeightedNorm]
  have hright_nonneg :
      0 ≤ positiveDefiniteFiniteMatrixWeightedNorm metric (x - z) := by
    simp [positiveDefiniteFiniteMatrixWeightedNorm]
  have hleft_sq :
      positiveDefiniteFiniteMatrixWeightedNorm metric (u - z) ^ 2 =
        finiteMatrixQuadraticForm metric (u - z) := by
    simpa [positiveDefiniteFiniteMatrixWeightedNorm] using
      Real.sq_sqrt (hmetric (u - z))
  have hright_sq :
      positiveDefiniteFiniteMatrixWeightedNorm metric (x - z) ^ 2 =
        finiteMatrixQuadraticForm metric (x - z) := by
    simpa [positiveDefiniteFiniteMatrixWeightedNorm] using
      Real.sq_sqrt (hmetric (x - z))
  have hsq :
      positiveDefiniteFiniteMatrixWeightedNorm metric (u - z) *
          positiveDefiniteFiniteMatrixWeightedNorm metric (u - z) ≤
        positiveDefiniteFiniteMatrixWeightedNorm metric (x - z) *
          positiveDefiniteFiniteMatrixWeightedNorm metric (x - z) :=
    mul_self_le_mul_self hleft_nonneg (hmin.2 x hx)
  calc
    finiteMatrixQuadraticForm metric (u - z) =
        positiveDefiniteFiniteMatrixWeightedNorm metric (u - z) ^ 2 := by
          exact hleft_sq.symm
    _ ≤ positiveDefiniteFiniteMatrixWeightedNorm metric (x - z) ^ 2 := by
          simpa [pow_two] using hsq
    _ = finiteMatrixQuadraticForm metric (x - z) := by
          exact hright_sq

end SOptLib
