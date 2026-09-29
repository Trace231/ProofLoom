import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import Staging.finiteMatrixWeightedProjectionArgmin
import Staging.isPositiveDefiniteFiniteMatrix

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: finite matrix weighted projection minimizes the associated quadratic form; orig was `weighted_projection_minimizes_quadratic_form`.
-- generality used: finite real Euclidean coordinate space `EuclideanSpace ℝ ι` with `[Fintype ι] [DecidableEq ι]`, a real matrix metric, positive definiteness, and a parameterized feasible argmin for the named matrix weighted norm; no measure, convexity, smoothness, or oracle assumptions are needed.
-- portable call pattern: adaptive-gradient and projected-gradient proofs can supply a feasible set, positive-definite metric, center, and weighted-norm argmin to obtain quadratic-form minimality; the set, metric, and center vary while the conclusion stays unchanged.
-- counterargument checked: this is not paper-local traceability or a caller-side expression because it is the reusable non-linear bridge from a matrix weighted-norm argmin to its squared quadratic-form comparison; it does not duplicate the argmin or positive-definite metric APIs.
-- coverage search: queried `finite matrix weighted projection minimizes quadratic form argmin positive definite metric` and `parameterized feasible argmin forall objective minimizer`; existing hits were the staged argmin relation and positive-definite square identity, which are inputs rather than this composed minimization theorem.
-- minimal hypotheses: finite coordinates and decidable equality are required by the existing finite-matrix APIs; positivity is used only through the named metric-domain square identity, and no convexity or measure assumptions are needed.

/-- A positive-definite finite-matrix weighted projection minimizes the associated
quadratic form over the feasible set.

The theorem squares the nonnegative matrix weighted-norm comparison supplied by
the feasible argmin relation and rewrites each square as the corresponding
finite-matrix quadratic form.

Layer: Model | Gap: Level 1 (weighted-norm argmin to quadratic-form minimality)
Proof: use the pointwise form of the parameterized feasible argmin, apply monotonicity of squaring on nonnegative reals, and rewrite with the positive-definite matrix weighted-norm square identity.
Source: finite-dimensional positive-definite quadratic forms, real square-root arithmetic, and Mathlib feasible-argmin order predicates
Used in: adaptive projected-gradient and matrix-metric projection proofs that need to replace a weighted-norm projection comparison by a quadratic-form inequality before deriving variational inequalities or contraction bounds
Book citation: book/ICLR2018/AMSGrad.json#/key_lemmas/0/proof/0
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad Algorithm 2 -/
theorem finite_matrix_weighted_projection_minimizes_quadratic_form
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Set (EuclideanSpace ℝ ι)) (metric : ι → ι → ℝ)
    (z u : EuclideanSpace ℝ ι)
    (hmetric : IsPositiveDefiniteFiniteMatrix metric)
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
  have hsq :
      positiveDefiniteFiniteMatrixWeightedNorm metric (u - z) *
          positiveDefiniteFiniteMatrixWeightedNorm metric (u - z) ≤
        positiveDefiniteFiniteMatrixWeightedNorm metric (x - z) *
          positiveDefiniteFiniteMatrixWeightedNorm metric (x - z) :=
    mul_self_le_mul_self hleft_nonneg (hmin.2 x hx)
  calc
    finiteMatrixQuadraticForm metric (u - z) =
        positiveDefiniteFiniteMatrixWeightedNorm metric (u - z) ^ 2 := by
          exact (isPositiveDefiniteFiniteMatrix metric hmetric (u - z)).symm
    _ ≤ positiveDefiniteFiniteMatrixWeightedNorm metric (x - z) ^ 2 := by
          simpa [pow_two] using hsq
    _ = finiteMatrixQuadraticForm metric (x - z) := by
          exact isPositiveDefiniteFiniteMatrix metric hmetric (x - z)

end SOptLib
