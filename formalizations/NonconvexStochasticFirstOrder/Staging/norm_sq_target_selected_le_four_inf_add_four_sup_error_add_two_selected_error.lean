import SOptLib.Glue.Algebra

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: finite selector target norm-square decomposition; orig was
--   `Selector_decomposition`, renamed away from the paper's selector label to
--   expose the reusable selected-target/error split.
-- generality used: a nonempty finite index type and a seminormed additive
--   commutative group; no measure, independence, integrability, convexity,
--   oracle, inner-product, completeness, or finite-dimensional assumptions are
--   used.
-- portable call pattern: validation selectors in stochastic first-order,
--   zeroth-order, and mirror-descent proofs choose an index minimizing an
--   empirical vector norm, then need the selected target norm square bounded
--   by the best target norm square, the worst empirical-target error, and the
--   selected error; only the index type and vector families change.
-- counterargument checked: the proof is deterministic finite algebra, but it
--   is not paper-local traceability or a pure wrapper because the same
--   selector decomposition recurs whenever a data-dependent validation
--   selector is analyzed. Existing SOptLib entries cover the two-term
--   norm-square Young inequality and finite error-value sets, not this
--   selector-level decomposition.
-- coverage search: queried "finite selector minimal empirical norm target
--   norm squared bounded by infimum supremum error", "norm squared selected
--   target minimal empirical inf supremum error inequality", and LeanSearch
--   for "finite type selected index minimal norm bound target norm squared by
--   infimum target norms and supremum empirical target errors"; top hits were
--   `SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq`,
--   `SOptLib.finiteRunErrorSqValues`, `SOptLib.mem_finiteRunErrorSqValues`,
--   and unrelated Mathlib product-supremum norm lemmas, all partial rather
--   than duplicates.
-- minimal hypotheses: the source's Hilbert state space and algorithm setup are
--   reduced to `[Fintype ι] [Nonempty ι] [SeminormedAddCommGroup E]` plus the
--   pointwise selected empirical-norm minimality hypothesis.

/-- A finite empirical-norm selector gives a target norm-square decomposition.

If `i` minimizes the empirical norms `‖G j‖` over a nonempty finite family, then
the selected target norm square is controlled by four times the finite infimum
of target norm squares, four times the finite supremum of empirical-target
error squares, and twice the selected error square.

Layer: Glue | Gap: Level 1 (finite selector norm-square decomposition)
Proof: choose an index attaining the finite infimum of target norm squares,
  compare empirical norms by selector minimality, split each vector with the
  two-term norm-square Young inequality, and combine the finite `inf'`/`sup'`
  bounds by real arithmetic.
Source: Mathlib finite extrema over finsets, seminormed additive-group norm
  algebra, and SOptLib's binary norm-square Young inequality
Used in: two-phase validation selection after independent optimization runs,
  separating the selected true-gradient square into optimization, validation
  error, and selected-candidate error terms
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/convergence_results/12
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic gradient descent -/
theorem norm_sq_target_selected_le_four_inf_add_four_sup_error_add_two_selected_error
    {ι E : Type*} [Fintype ι] [Nonempty ι] [SeminormedAddCommGroup E]
    (G target : ι → E) (i : ι)
    (hmin : ∀ j : ι, ‖G i‖ ≤ ‖G j‖) :
    ‖target i‖ ^ 2 ≤
      4 * (Finset.univ.inf' (Finset.univ_nonempty) (fun j : ι => ‖target j‖ ^ 2)) +
        4 * (Finset.univ.sup' (Finset.univ_nonempty)
          (fun j : ι => ‖G j - target j‖ ^ 2)) +
          2 * ‖G i - target i‖ ^ 2 := by
  classical
  let A : ι → ℝ := fun j => ‖target j‖ ^ 2
  let Err : ι → ℝ := fun j => ‖G j - target j‖ ^ 2
  obtain ⟨j0, _hj0mem, hj0_le_inf⟩ :
      ∃ j0 : ι, j0 ∈ Finset.univ ∧
        A j0 ≤ Finset.univ.inf' (Finset.univ_nonempty) A := by
    exact
      (Finset.inf'_le_iff (s := Finset.univ)
        (H := Finset.univ_nonempty) (f := A)
        (a := Finset.univ.inf' (Finset.univ_nonempty) A)).mp le_rfl
  have hErr_le_sup :
      Err j0 ≤ Finset.univ.sup' (Finset.univ_nonempty) Err := by
    simpa [Err] using
      (Finset.le_sup' (s := Finset.univ) (f := Err) (b := j0) (by simp))
  have hmin_sq : ‖G i‖ ^ 2 ≤ ‖G j0‖ ^ 2 := by
    nlinarith [hmin j0, norm_nonneg (G i), norm_nonneg (G j0)]
  have hj0_split : ‖G j0‖ ^ 2 ≤ 2 * A j0 + 2 * Err j0 := by
    have h :=
      SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq
        (target j0) (G j0 - target j0)
    simpa [A, Err, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  have hEmp :
      ‖G i‖ ^ 2 ≤
        2 * (Finset.univ.inf' (Finset.univ_nonempty) A) +
          2 * (Finset.univ.sup' (Finset.univ_nonempty) Err) := by
    calc
      ‖G i‖ ^ 2 ≤ ‖G j0‖ ^ 2 := hmin_sq
      _ ≤ 2 * A j0 + 2 * Err j0 := hj0_split
      _ ≤ 2 * (Finset.univ.inf' (Finset.univ_nonempty) A) +
          2 * (Finset.univ.sup' (Finset.univ_nonempty) Err) := by
        nlinarith [hj0_le_inf, hErr_le_sup]
  have hTarget :
      ‖target i‖ ^ 2 ≤
        2 * ‖G i‖ ^ 2 + 2 * ‖G i - target i‖ ^ 2 := by
    have hbase :
        ‖target i‖ ^ 2 ≤
          2 * ‖G i‖ ^ 2 + 2 * ‖target i - G i‖ ^ 2 := by
      have h :=
        SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq
          (G i) (target i - G i)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
    simpa [norm_sub_rev] using hbase
  change
    ‖target i‖ ^ 2 ≤
      4 * (Finset.univ.inf' (Finset.univ_nonempty) A) +
        4 * (Finset.univ.sup' (Finset.univ_nonempty) Err) +
          2 * ‖G i - target i‖ ^ 2
  nlinarith [hTarget, hEmp]

end SOptLib
