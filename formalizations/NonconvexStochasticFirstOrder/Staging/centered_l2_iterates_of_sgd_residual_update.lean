import SOptLib.Glue.Probability

open MeasureTheory

-- Generalization plan (G0):
-- concept/name: centered_l2_iterates_of_sgd_residual_update exposes finite-horizon
--   centered square-integrability induction for a stochastic-gradient recursion.
-- generality used: arbitrary measure space, a normed additive real vector
--   space, an iterate process, gradient/oracle/residual processes, a fixed base
--   point, and pointwise gradient-L2, residual-L2, oracle-decomposition, and
--   affine-update contracts; no probability, filtration, independence,
--   convexity, inner-product, completeness, or finite-dimensional assumptions.
-- portable call pattern: stochastic-gradient, zeroth-order, and variance-reduced
--   algorithms call this after establishing process measurability; the iterate
--   horizon, stepsizes, gradient map, oracle, residual, measure, and base point
--   vary while the centered-L2 induction conclusion is unchanged.
-- counterargument checked: the theorem is not paper-local traceability or a
--   caller-side expression because it composes gradient/residual L2 transfer
--   with the nontrivial finite-horizon recursion induction; existing SOptLib
--   entries provide only the affine one-step transport and L2 closure pieces.
-- coverage search: queried `centered square integrable iterates affine stochastic
--   gradient residual update`, `affine update centered squared integrability
--   induction finite horizon iterate`, and `integrable squared norm affine update
--   previous L2 subtraction scalar`; closest hits were
--   `integrable_sq_norm_sub_smul_sub_const_of_l2`,
--   `integrable_sq_norm_const_sub_affine_update`, and
--   `integrable_sq_norm_grad_of_lipschitz_grad_centered_l2`, all component
--   declarations rather than this finite-horizon induction.
-- minimal hypotheses: the paper's probability and filtration setup is reduced
--   to an arbitrary measure `μ`, process measurability, and the pointwise
--   contracts directly consumed by the induction.

/-- Every iterate of a finite stochastic-gradient recursion is centered
square-integrable when the gradient and residual processes have the required
L2 closure properties.

The oracle direction is the sum of the gradient at the current iterate and a
square-integrable residual, and each successor iterate is an affine
subtraction of that direction.

Layer: Layer1 | Gap: Level 1 (finite-horizon centered L2 recursion)
Proof: induct on the iterate index, use the supplied gradient-L2 bridge and
residual decomposition to obtain oracle L2, then apply the centered affine
update closure to the successor equation.
Source: Mathlib Bochner integrability and MemLp exponent-two closure, together
with SOptLib centered L2 scalar-subtraction transport
Used in: stochastic-gradient iteration proofs before converting centered iterate
control into gradient, objective-value, and oracle cross-term integrability
Book citation: book/FOML/NonconvexStochasticFirstOrder.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, RSGD method -/
theorem centered_l2_iterates_of_sgd_residual_update
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω}
    (base : E) (x G residual : Nat → Ω → E) (grad : E → E)
    (γ : Nat → ℝ) (N : Nat)
    (hx_aesm :
      ∀ m : Nat, m < N → AEStronglyMeasurable (x m) μ)
    (hgrad_aesm :
      ∀ m : Nat, m < N →
        AEStronglyMeasurable (fun ω => grad (x m ω)) μ)
    (hG_aesm : ∀ m : Nat, m < N → AEStronglyMeasurable (G m) μ)
    (hresidual_aesm :
      ∀ m : Nat, m < N → AEStronglyMeasurable (residual m) μ)
    (hgrad_sq :
      ∀ m : Nat,
        m < N →
        Integrable (fun ω => ‖x m ω - base‖ ^ (2 : Nat)) μ →
          Integrable (fun ω => ‖grad (x m ω)‖ ^ (2 : Nat)) μ)
    (hresidual_sq :
      ∀ m : Nat, m < N →
        Integrable (fun ω => ‖residual m ω‖ ^ (2 : Nat)) μ)
    (hG_eq :
      ∀ m : Nat, m < N → ∀ ω : Ω,
        G m ω = grad (x m ω) + residual m ω)
    (hx_zero : x 0 =ᵐ[μ] fun _ => base)
    (hupdate :
      ∀ m : Nat, m < N → ∀ ω : Ω,
        x (m + 1) ω = x m ω - γ m • G m ω) :
    ∀ m : Nat, m < N →
      Integrable (fun ω => ‖x m ω - base‖ ^ (2 : Nat)) μ := by
  intro m
  induction m with
  | zero =>
      intro _hm
      refine (MeasureTheory.integrable_zero Ω ℝ μ).congr ?_
      filter_upwards [hx_zero] with ω hω
      rw [hω]
      simp
  | succ m ih =>
      intro hm
      have hmN' : m < N := lt_trans (Nat.lt_succ_self m) hm
      have hgrad_sq_m :
          Integrable (fun ω => ‖grad (x m ω)‖ ^ (2 : Nat)) μ :=
        hgrad_sq m hmN' (ih hmN')
      have hG_sq :
          Integrable (fun ω => ‖G m ω‖ ^ (2 : Nat)) μ := by
        have hsum_sq :
            Integrable
              (fun ω => ‖grad (x m ω) - (-residual m ω)‖ ^ (2 : Nat)) μ :=
          integrable_sq_norm_sub
            (u := fun ω => grad (x m ω))
            (v := fun ω => -residual m ω)
            (hgrad_aesm m hmN') (hresidual_aesm m hmN').neg
            hgrad_sq_m
            (by simpa using hresidual_sq m hmN')
        refine hsum_sq.congr ?_
        filter_upwards with ω
        rw [hG_eq m hmN' ω]
        congr 1
        abel
      have hnext :
          Integrable
            (fun ω => ‖(x m ω - γ m • G m ω) - base‖ ^ (2 : Nat)) μ :=
        integrable_sq_norm_sub_smul_sub_const_of_l2
          (ν := μ) (x := x m) (g := G m) (c := base) (γ := γ m)
          (hx_aesm m hmN') (hG_aesm m hmN') (ih hmN') hG_sq
      refine hnext.congr ?_
      filter_upwards with ω
      rw [hupdate m hmN' ω]
