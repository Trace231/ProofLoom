import Mathlib.Tactic

-- Generalization plan (G0):
-- concept/name: fun_eq_of_forall_nonneg_sq_eq exposes equality of two
--   real-valued functions from pointwise nonnegativity and equal squares.
-- generality used: arbitrary index type and functions into `ℝ`; no topology,
--   measure, optimization, or Euclidean-space structure is involved.
-- portable call pattern: callers with two nonnegative real-valued witnesses for
--   the same squared quantity can identify the witnesses pointwise.
-- counterargument checked: not a pure wrapper because Mathlib provides the
--   scalar nonnegative square criterion, while callers often need the
--   function-extensional conclusion.
-- coverage search: searched `function equality from pointwise nonnegative
--   equal squares` and `nonnegative square equality implies equality real`; top
--   hits were this staging declaration, unrelated moment/norm infrastructure,
--   and Mathlib scalar `sq_eq_sq₀`, all partial rather than this theorem.
-- minimal hypotheses: pointwise nonnegativity and square equality are exactly
--   the scalar data needed at each index.

/-- Nonnegative real-valued functions with the same pointwise square are equal.

If two real-valued functions are pointwise nonnegative and have the same
pointwise square, then they agree at every input.

Layer: Glue | Gap: Level 0 (pointwise nonnegative square equality)
Proof: extensionality reduces the function equality to scalar inputs; `sq_eq_sq₀` identifies nonnegative real numbers with equal squares.
Source: Mathlib real ordered-ring square equality and function extensionality APIs
Used in: adaptive methods identifying independently supplied nonnegative witnesses for long-term second-moment preconditioners before quotient and projection reasoning
Book citation: book/ICLR2018/AMSGrad.json#/algorithm_spec/steps/5
Origin algorithm: Reddi, Kale, and Kumar, On the Convergence of Adam and Beyond, AMSGrad Algorithm 2 -/
theorem fun_eq_of_forall_nonneg_sq_eq {ι : Type*}
    {r s : ι → ℝ}
    (hr : ∀ i, 0 ≤ r i)
    (hs : ∀ i, 0 ≤ s i)
    (hsq : ∀ i, r i ^ 2 = s i ^ 2) :
    r = s := by
  funext i
  exact (sq_eq_sq₀ (hr i) (hs i)).mp (hsq i)
