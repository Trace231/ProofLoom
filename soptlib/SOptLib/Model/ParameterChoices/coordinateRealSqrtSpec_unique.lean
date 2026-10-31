import Mathlib.Tactic

-- Generalization plan (G0):
-- concept/name: coordinateRealSqrtSpec_unique exposes uniqueness of a
--   coordinatewise real square-root specification; orig was coord_sqrt_unique.
-- generality used: arbitrary index type and real-valued coordinate functions;
--   no measure, topology, finite-dimensional, optimization, or Euclidean-space
--   hypotheses are used.
-- portable call pattern: adaptive-coordinate algorithms call this when two
--   independently supplied nonnegative square-root witnesses represent the
--   same second-moment or preconditioner vector.
-- counterargument checked: Mathlib supplies scalar nonnegative-square
--   uniqueness but not this pointwise function-level contract; the result is
--   therefore reusable infrastructure rather than paper-local traceability.
-- coverage search: searched `coordinate square root uniqueness nonnegative
--   square equal`, `function equality pointwise equal squares`, and
--   `real square root specification unique`; Mathlib `sq_eq_sq₀` was the
--   closest partial hit and no SOptLib declaration covered this conclusion.
-- minimal hypotheses: pointwise nonnegativity and equality of the two squares
--   through a common value are exactly the scalar hypotheses used.

/-- Coordinatewise real square-root specifications for the same value vector
are unique.

If two real-valued functions are pointwise nonnegative and each squares to the
same value at every index, then the functions agree at every index.

Layer: Glue | Gap: Level 0 (pointwise nonnegative square-root uniqueness)
Proof: Apply function extensionality and `sq_eq_sq₀` coordinate by coordinate;
the common square-value equations establish equal squares.
Source: Mathlib real ordered-ring square equality and function extensionality APIs
Used in: adaptive-moment methods identifying independently supplied square-root
witnesses for second-moment denominators before quotient and projection reasoning
Book citation: book/ICLR2018/AMSGrad.json#/algorithm_spec/steps/5
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond,
AMSGrad Algorithm 2 -/
theorem coordinateRealSqrtSpec_unique {ι : Type*}
    {v r s : ι → ℝ}
    (hr : ∀ i, 0 ≤ r i ∧ r i ^ 2 = v i)
    (hs : ∀ i, 0 ≤ s i ∧ s i ^ 2 = v i) :
    r = s := by
  funext i
  have hri := hr i
  have hsi := hs i
  have hsq : r i ^ 2 = s i ^ 2 := by
    rw [hri.2, hsi.2]
  exact (sq_eq_sq₀ hri.1 hsi.1).mp hsq
