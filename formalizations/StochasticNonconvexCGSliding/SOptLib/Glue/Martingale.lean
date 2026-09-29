-- SOptLib/Glue/Martingale.lean
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.ConditionalExpectation
import SOptLib.Glue.Probability


open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

/-- Conditional expectation cancels an inner product against an adapted translated vector.

If the vector-valued noise `δ` has conditional expectation zero with respect to `m`,
and `x` is `m`-measurable, then the scalar inner product
`ω ↦ ⟪δ ω, x ω - c⟫_ℝ` also has conditional expectation zero.

Layer: Glue | Gap: Level 1 (conditional-expectation pullout for adapted inner products)
Proof: apply Mathlib's bilinear conditional-expectation pullout to `innerSL ℝ`,
  then rewrite the pulled-out conditional expectation using the martingale-difference
  hypothesis.
Source: Mathlib conditional expectation pull-out API
Used in: stochastic mirror descent martingale noise cancellation
Book citation: book/PAPER/ALG.json#/stochastic_mirror_descent
Origin algorithm: Lan stochastic mirror descent martingale cancellation -/
theorem condExp_inner_sub_const_eq_zero_of_condExp_eq_zero
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} {m : MeasurableSpace Ω}
    {δ x : Ω → E} {c : E}
    (hx : @Measurable Ω E m _ x)
    (hδ_ce : P[δ | m] =ᵐ[P] 0)
    (hδ_int : Integrable δ P)
    (hinner_int : Integrable (fun ω => ⟪δ ω, x ω - c⟫_ℝ) P) :
    P[(fun ω => ⟪δ ω, x ω - c⟫_ℝ) | m] =ᵐ[P] 0 := by
  let B : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
  have hx_asm : AEStronglyMeasurable[m] (fun ω => x ω - c) P := by
    exact (hx.sub measurable_const).aestronglyMeasurable
  have hpull := MeasureTheory.condExp_bilin_of_aestronglyMeasurable_right
    (μ := P) (m := m) (B := B) (f := δ) (g := fun ω => x ω - c)
    hx_asm hinner_int hδ_int
  refine hpull.trans ?_
  filter_upwards [hδ_ce] with ω hω
  simp [B, hω]



/-- A scalar random variable has zero integral when its conditional expectation is a.e. zero.

Layer: Glue | Gap: Level 1 (conditional-to-unconditional integral cancellation)
Proof: use `MeasureTheory.integral_condExp` to identify the integral of the conditional
  expectation with the original integral, then rewrite the left-hand side by the a.e.
  zero hypothesis.
Source: Mathlib conditional expectation API
Used in: stochastic mirror descent martingale noise cancellation
Book citation: book/PAPER/ALG.json#/stochastic_mirror_descent
Origin algorithm: Lan stochastic mirror descent martingale cancellation -/
theorem integral_eq_zero_of_condExp_ae_eq_zero
    {Ω : Type*} {m0 : MeasurableSpace Ω}
    {P : @Measure Ω m0} {m : MeasurableSpace Ω}
    {Z : Ω → ℝ}
    (hm : m ≤ m0)
    [SigmaFinite (P.trim hm)]
    (h_cond_zero : P[Z | m] =ᵐ[P] 0) :
    ∫ ω, Z ω ∂P = 0 := by
  have htotal : ∫ ω, (P[Z | m]) ω ∂P = ∫ ω, Z ω ∂P :=
    MeasureTheory.integral_condExp (μ := P) (m := m) (f := Z) hm
  have hleft : ∫ ω, (P[Z | m]) ω ∂P = 0 := by
    simpa using integral_congr_ae h_cond_zero
  exact htotal ▸ hleft


open MeasureTheory
open scoped BigOperators

/-- A finite sum of deterministic scalar multiples has zero integral when each
unscaled summand has zero integral.

Layer: Glue | Gap: Level 1 (finite integral cancellation)
Proof: exchange the finite sum and the integral, then use linearity of the
  Bochner integral over deterministic real constants.
Source: Mathlib Bochner integral finite-sum and scalar-linearity API
Used in: stochastic mirror descent martingale window cancellation
Book citation: book/PAPER/ALG.json#/stochastic_mirror_descent
Origin algorithm: Lan stochastic mirror descent martingale window cancellation -/
theorem integral_finset_sum_const_mul_eq_zero
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset ι) (c : ι → ℝ) (Z : ι → Ω → ℝ)
    (hZ_int : ∀ i ∈ s, Integrable (Z i) μ)
    (hZ_zero : ∀ i ∈ s, ∫ ω, Z i ω ∂μ = 0) :
    ∫ ω, Finset.sum s (fun i => c i * Z i ω) ∂μ = 0 := by
  classical
  have hterms :
      ∀ i ∈ s, Integrable (fun ω => c i * Z i ω) μ := by
    intro i hi
    exact (hZ_int i hi).const_mul (c i)
  rw [integral_finset_sum s hterms]
  refine Finset.sum_eq_zero ?_
  intro i hi
  rw [integral_const_mul, hZ_zero i hi, mul_zero]


open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

/-- Conditional unbiasedness cancels an adapted martingale inner product in integral.

If a vector-valued noise term `δ` has conditional expectation zero with respect to a
sub-sigma-algebra `m`, and the multiplier `x` is `m`-measurable, then the integral of
`ω ↦ ⟪δ ω, x ω - c⟫_ℝ` is zero, assuming the usual integrability side conditions.

Layer: Glue | Gap: Level 1 (adapted inner-product martingale cancellation)
Proof: first pull conditional expectation through the continuous bilinear inner product,
  then use the equality between a scalar random variable and its conditional expectation
  under integration.
Source: Mathlib conditional expectation pull-out and integral APIs
Used in: stochastic mirror descent martingale noise cancellation
Book citation: book/PAPER/ALG.json#/stochastic_mirror_descent
Origin algorithm: Lan stochastic mirror descent martingale cancellation -/
theorem integral_inner_sub_const_eq_zero_of_condExp_eq_zero
    {Ω E : Type*} {m0 : MeasurableSpace Ω}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : @Measure Ω m0} {m : MeasurableSpace Ω}
    (hm : m ≤ m0)
    [SigmaFinite (P.trim hm)]
    {δ x : Ω → E} {c : E}
    (hx : Measurable[m] x)
    (hδ_ce : P[δ | m] =ᵐ[P] 0)
    (hδ_int : Integrable δ P)
    (hinner_int : Integrable (fun ω => ⟪δ ω, x ω - c⟫_ℝ) P) :
    ∫ ω, ⟪δ ω, x ω - c⟫_ℝ ∂P = 0 := by
  have hscalar :
      P[(fun ω => ⟪δ ω, x ω - c⟫_ℝ) | m] =ᵐ[P] 0 :=
    @condExp_inner_sub_const_eq_zero_of_condExp_eq_zero Ω E m0 _ _ _ _ _ _ P m δ x c
      hx hδ_ce hδ_int hinner_int
  exact integral_eq_zero_of_condExp_ae_eq_zero (P := P) (m := m) hm hscalar

/-- A scalar inner-product random variable has zero integral when its conditional
expectation is a.e. zero.

Layer: Glue | Gap: Level 1 (scalar inner-product conditional-expectation cancellation)
Proof: specialize the generic conditional-expectation zero-integral lemma to
  `ω ↦ ⟪δ ω, x ω - c⟫_ℝ`.
Source: Mathlib measure theory conditional expectation and Bochner integral APIs
Used in: stochastic mirror descent martingale noise inner-product cancellation
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem integral_inner_eq_zero_of_scalar_condExp_eq_zero
    {Ω E : Type*} {m0 : MeasurableSpace Ω}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {P : @Measure Ω m0} {m : MeasurableSpace Ω}
    (hm : m ≤ m0)
    [SigmaFinite (P.trim hm)]
    {δ x : Ω → E} {c : E}
    (h_cond_zero :
      P[(fun ω => ⟪δ ω, x ω - c⟫_ℝ) | m] =ᵐ[P] 0) :
    ∫ ω, ⟪δ ω, x ω - c⟫_ℝ ∂P = 0 := by
  exact integral_eq_zero_of_condExp_ae_eq_zero
    (P := P) (m := m) (Z := fun ω => ⟪δ ω, x ω - c⟫_ℝ) hm h_cond_zero

private theorem integrable_inner_of_integrable_sq_norm_aux
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {P : Measure Ω} {u v : Ω → E}
    (hu_meas : AEStronglyMeasurable u P)
    (hv_meas : AEStronglyMeasurable v P)
    (hu_sq : Integrable (fun ω => ‖u ω‖ ^ 2) P)
    (hv_sq : Integrable (fun ω => ‖v ω‖ ^ 2) P) :
    Integrable (fun ω => ⟪u ω, v ω⟫_ℝ) P := by
  have hu_l2 : MemLp u 2 P :=
    (memLp_two_iff_integrable_sq_norm hu_meas).2 hu_sq
  have hv_l2 : MemLp v 2 P :=
    (memLp_two_iff_integrable_sq_norm hv_meas).2 hv_sq
  have hprod : Integrable (fun ω => ‖u ω‖ * ‖v ω‖) P := by
    simpa [Pi.mul_apply] using
      (MemLp.integrable_mul hu_l2.norm hv_l2.norm :
        Integrable ((fun ω => ‖u ω‖) * (fun ω => ‖v ω‖)) P)
  exact hprod.mono'
    (AEStronglyMeasurable.inner hu_meas hv_meas)
    (Filter.Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using abs_real_inner_le_norm (u ω) (v ω))

/-- The squared norm integral of a finite Hilbert sum is the sum of diagonal
second moments when every off-diagonal cross integral vanishes.

This is the finite covariance expansion for Hilbert-valued random variables,
stated for an arbitrary measure and a finite index set.

Layer: Glue | Gap: Level 1 (finite Hilbert covariance diagonalization)
Proof: expand the pointwise squared norm with bilinearity of the inner product,
  commute the Bochner integral through both finite sums, and cancel off-diagonal
  terms using the cross-integral hypothesis.
Source: Mathlib finite sums, Bochner integral linearity, and Hilbert inner-product APIs
Used in: nonconvex stochastic mirror descent mini-batch and validation residual variance reduction
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
    {Ω E ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [DecidableEq ι] (μ : Measure Ω) (I : Finset ι) (δ : ι → Ω → E)
    (hmeas : ∀ i ∈ I, AEStronglyMeasurable (δ i) μ)
    (hL2 : ∀ i ∈ I, Integrable (fun ω => ‖δ i ω‖ ^ 2) μ)
    (hcross :
      ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
        ∫ ω, ⟪δ i ω, δ j ω⟫_ℝ ∂μ = 0) :
    ∫ ω, ‖Finset.sum I (fun i => δ i ω)‖ ^ 2 ∂μ =
      Finset.sum I (fun i => ∫ ω, ‖δ i ω‖ ^ 2 ∂μ) := by
  classical
  have hinner_int :
      ∀ i ∈ I, ∀ j ∈ I,
        Integrable (fun ω => ⟪δ i ω, δ j ω⟫_ℝ) μ := by
    intro i hi j hj
    exact integrable_inner_of_integrable_sq_norm_aux
      (hmeas i hi) (hmeas j hj) (hL2 i hi) (hL2 j hj)
  have hpoint :
      (fun ω => ‖Finset.sum I (fun i => δ i ω)‖ ^ 2) =
        (fun ω =>
          Finset.sum I (fun i =>
            Finset.sum I (fun j => ⟪δ i ω, δ j ω⟫_ℝ))) := by
    funext ω
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [inner_sum]
  have hsum_inner_int :
      ∀ i ∈ I,
        Integrable
          (fun ω => Finset.sum I (fun j => ⟪δ i ω, δ j ω⟫_ℝ)) μ := by
    intro i hi
    exact integrable_finset_sum I (fun j hj => hinner_int i hi j hj)
  have hdouble_diag :
      Finset.sum I
          (fun i => Finset.sum I
            (fun j => ∫ ω, ⟪δ i ω, δ j ω⟫_ℝ ∂μ)) =
        Finset.sum I (fun i => ∫ ω, ‖δ i ω‖ ^ 2 ∂μ) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      exact hcross i hi j hj (Ne.symm hji)
    · intro hnot
      exact False.elim (hnot hi)
  calc
    ∫ ω, ‖Finset.sum I (fun i => δ i ω)‖ ^ 2 ∂μ
        = ∫ ω,
            Finset.sum I (fun i =>
              Finset.sum I (fun j => ⟪δ i ω, δ j ω⟫_ℝ)) ∂μ := by
            rw [hpoint]
    _ = Finset.sum I
          (fun i =>
            ∫ ω, Finset.sum I (fun j => ⟪δ i ω, δ j ω⟫_ℝ) ∂μ) := by
            exact integral_finset_sum I hsum_inner_int
    _ = Finset.sum I
          (fun i => Finset.sum I
            (fun j => ∫ ω, ⟪δ i ω, δ j ω⟫_ℝ ∂μ)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact integral_finset_sum I (fun j hj => hinner_int i hi j hj)
    _ = Finset.sum I (fun i => ∫ ω, ‖δ i ω‖ ^ 2 ∂μ) := hdouble_diag

/-- A zero centered cross integral identifies the cross moment with the
center's second moment.

If `∫ ⟪m, g - m⟫ = 0`, then the cross integral `∫ ⟪g, m⟫` equals
`∫ ‖m‖²`, provided the two scalar inner products needed for subtraction are
integrable.

Layer: Glue | Gap: Level 1 (centered Hilbert cross-moment algebra)
Proof: rewrite the centered inner product as `⟪m, g⟫ - ⟪m, m⟫`, commute
  the integral through subtraction, and use symmetry plus
  `⟪m, m⟫ = ‖m‖²`.
Source: Mathlib Bochner integral linearity and real Hilbert-space inner-product APIs
Used in: stochastic nonconvex conditional gradient residual second-moment expansion
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem integral_inner_eq_integral_norm_sq_of_inner_sub_eq_zero
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure Ω) {g m : Ω → E}
    (h_inner_mg : Integrable (fun ω => ⟪m ω, g ω⟫_ℝ) μ)
    (h_inner_mm : Integrable (fun ω => ⟪m ω, m ω⟫_ℝ) μ)
    (hcentered_zero :
      ∫ ω, ⟪m ω, g ω - m ω⟫_ℝ ∂μ = 0) :
    ∫ ω, ⟪g ω, m ω⟫_ℝ ∂μ = ∫ ω, ‖m ω‖ ^ 2 ∂μ := by
  have hdiff_eq :
      (fun ω => ⟪m ω, g ω⟫_ℝ - ⟪m ω, m ω⟫_ℝ) =
        (fun ω => ⟪m ω, g ω - m ω⟫_ℝ) := by
    funext ω
    simp [inner_sub_right]
  have hsub_eq :
      ∫ ω, ⟪m ω, g ω⟫_ℝ ∂μ -
          ∫ ω, ⟪m ω, m ω⟫_ℝ ∂μ = 0 := by
    rw [← integral_sub h_inner_mg h_inner_mm, hdiff_eq]
    exact hcentered_zero
  have hnorm_eq :
      ∫ ω, ⟪m ω, m ω⟫_ℝ ∂μ = ∫ ω, ‖m ω‖ ^ 2 ∂μ := by
    simp
  calc
    ∫ ω, ⟪g ω, m ω⟫_ℝ ∂μ =
        ∫ ω, ⟪m ω, g ω⟫_ℝ ∂μ := by
          simp [real_inner_comm]
    _ = ∫ ω, ⟪m ω, m ω⟫_ℝ ∂μ := by
          linarith
    _ = ∫ ω, ‖m ω‖ ^ 2 ∂μ := hnorm_eq

/-- A centered Hilbert-valued square moment is bounded by the uncentered square
moment when the cross moment equals the center's square moment.

For square-integrable `g` and `m`, the identity
`∫ ⟪m, g⟫ = ∫ ‖m‖²` makes the polarization expansion of
`∫ ‖g - m‖²` equal to `∫ ‖g‖² - ∫ ‖m‖²`, hence no larger than
`∫ ‖g‖²`.

Layer: Glue | Gap: Level 1 (Hilbert second-moment centering contraction)
Proof: derive inner-product integrability from the two square-integrability
  hypotheses, expand `‖g - m‖²` by the real Hilbert norm-square identity,
  commute integrals through the scalar algebra, and cancel the cross term.
Source: Mathlib Bochner integral linearity and real Hilbert-space polarization APIs
Used in: stochastic nonconvex conditional gradient centered gradient-difference
  variance bound
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem integral_norm_sq_sub_le_integral_norm_sq_of_inner_sub_zero
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure Ω) {g m : Ω → E}
    (hg_meas : AEStronglyMeasurable g μ)
    (hm_meas : AEStronglyMeasurable m μ)
    (hg_sq : Integrable (fun ω => ‖g ω‖ ^ 2) μ)
    (hm_sq : Integrable (fun ω => ‖m ω‖ ^ 2) μ)
    (hcross_eq :
      ∫ ω, ⟪m ω, g ω⟫_ℝ ∂μ = ∫ ω, ‖m ω‖ ^ 2 ∂μ) :
    ∫ ω, ‖g ω - m ω‖ ^ 2 ∂μ ≤ ∫ ω, ‖g ω‖ ^ 2 ∂μ := by
  have h_inner_mg :
      Integrable (fun ω => ⟪m ω, g ω⟫_ℝ) μ :=
    integrable_inner_of_integrable_sq_norm_aux hm_meas hg_meas hm_sq hg_sq
  have h_inner_gm :
      Integrable (fun ω => ⟪g ω, m ω⟫_ℝ) μ := by
    simpa [real_inner_comm] using h_inner_mg
  have hcross_eq' :
      ∫ ω, ⟪g ω, m ω⟫_ℝ ∂μ = ∫ ω, ‖m ω‖ ^ 2 ∂μ := by
    simpa [real_inner_comm] using hcross_eq
  have h_expand :
      ∫ ω, ‖g ω - m ω‖ ^ 2 ∂μ =
        ∫ ω, ‖g ω‖ ^ 2 ∂μ -
          2 * ∫ ω, ⟪g ω, m ω⟫_ℝ ∂μ +
          ∫ ω, ‖m ω‖ ^ 2 ∂μ := by
    calc
      ∫ ω, ‖g ω - m ω‖ ^ 2 ∂μ
          = ∫ ω, (‖g ω‖ ^ 2 - 2 * ⟪g ω, m ω⟫_ℝ + ‖m ω‖ ^ 2) ∂μ := by
              refine integral_congr_ae (Filter.Eventually.of_forall ?_)
              intro ω
              simpa using norm_sub_sq_real (g ω) (m ω)
      _ = ∫ ω, ((‖g ω‖ ^ 2 - 2 * ⟪g ω, m ω⟫_ℝ) + ‖m ω‖ ^ 2) ∂μ := by
              refine integral_congr_ae (Filter.Eventually.of_forall ?_)
              intro ω
              ring
      _ = ∫ ω, ‖g ω‖ ^ 2 ∂μ -
            2 * ∫ ω, ⟪g ω, m ω⟫_ℝ ∂μ +
            ∫ ω, ‖m ω‖ ^ 2 ∂μ := by
              have hadd :
                  ∫ ω, ((‖g ω‖ ^ 2 - 2 * ⟪g ω, m ω⟫_ℝ) + ‖m ω‖ ^ 2) ∂μ =
                    ∫ ω, (‖g ω‖ ^ 2 - 2 * ⟪g ω, m ω⟫_ℝ) ∂μ +
                      ∫ ω, ‖m ω‖ ^ 2 ∂μ :=
                integral_add (hg_sq.sub (h_inner_gm.const_mul 2)) hm_sq
              have hsub :
                  ∫ ω, (‖g ω‖ ^ 2 - 2 * ⟪g ω, m ω⟫_ℝ) ∂μ =
                    ∫ ω, ‖g ω‖ ^ 2 ∂μ -
                      ∫ ω, 2 * ⟪g ω, m ω⟫_ℝ ∂μ :=
                integral_sub hg_sq (h_inner_gm.const_mul 2)
              calc
                ∫ ω, ((‖g ω‖ ^ 2 - 2 * ⟪g ω, m ω⟫_ℝ) + ‖m ω‖ ^ 2) ∂μ
                    = ∫ ω, (‖g ω‖ ^ 2 - 2 * ⟪g ω, m ω⟫_ℝ) ∂μ +
                        ∫ ω, ‖m ω‖ ^ 2 ∂μ := hadd
                _ = (∫ ω, ‖g ω‖ ^ 2 ∂μ -
                        ∫ ω, 2 * ⟪g ω, m ω⟫_ℝ ∂μ) +
                      ∫ ω, ‖m ω‖ ^ 2 ∂μ := by rw [hsub]
                _ = ∫ ω, ‖g ω‖ ^ 2 ∂μ -
                      2 * ∫ ω, ⟪g ω, m ω⟫_ℝ ∂μ +
                      ∫ ω, ‖m ω‖ ^ 2 ∂μ := by
                    rw [integral_const_mul 2]
  calc
    ∫ ω, ‖g ω - m ω‖ ^ 2 ∂μ
        = ∫ ω, ‖g ω‖ ^ 2 ∂μ - ∫ ω, ‖m ω‖ ^ 2 ∂μ := by
            rw [h_expand, hcross_eq']
            ring
    _ ≤ ∫ ω, ‖g ω‖ ^ 2 ∂μ := by
            have h_nonneg : 0 ≤ ∫ ω, ‖m ω‖ ^ 2 ∂μ := by
              refine integral_nonneg ?_
              intro ω
              positivity
            linarith

/-- Conditional unbiasedness cancels a left-translated adapted martingale inner product.

If a vector-valued noise term `δ` has conditional expectation zero with respect to
`m`, and the multiplier `x` is `m`-measurable, then the integral of
`ω ↦ ⟪δ ω, c - x ω⟫_ℝ` is zero. In the nonintegrable scalar branch this uses the
standard totalized value of the Bochner integral.

Layer: Glue | Gap: Level 1 (adapted inner-product martingale cancellation with reversed sign)
Proof: split on scalar integrability. In the integrable branch, rewrite the
  integrand as the negative of the standard `x - c` orientation and apply the
  existing conditional-expectation cancellation lemma; in the other branch use
  Mathlib's `integral_undef`.
Source: Mathlib conditional expectation pull-out and Bochner integral totalization APIs
Used in: stochastic accelerated gradient descent martingale cancellation for the error term at an optimal point
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic accelerated gradient descent -/
theorem integral_inner_const_sub_eq_zero_of_condExp_eq_zero
    {Ω E : Type*} {m0 : MeasurableSpace Ω}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : @Measure Ω m0} {m : MeasurableSpace Ω}
    (hm : m ≤ m0)
    [SigmaFinite (P.trim hm)]
    {δ x : Ω → E} {c : E}
    (hx : Measurable[m] x)
    (hδ_ce : P[δ | m] =ᵐ[P] 0)
    (hδ_int : Integrable δ P) :
    ∫ ω, ⟪δ ω, c - x ω⟫_ℝ ∂P = 0 := by
  let target : Ω → ℝ := fun ω => ⟪δ ω, c - x ω⟫_ℝ
  let flipped : Ω → ℝ := fun ω => ⟪δ ω, x ω - c⟫_ℝ
  by_cases htarget_int : Integrable target P
  · have hflipped_int : Integrable flipped P := by
      have hneg : Integrable (fun ω => -target ω) P := htarget_int.neg
      refine hneg.congr ?_
      filter_upwards with ω
      simp [target, flipped, sub_eq_add_neg, inner_add_right]
    have hflipped_zero : ∫ ω, flipped ω ∂P = 0 := by
      exact integral_inner_sub_const_eq_zero_of_condExp_eq_zero
        (P := P) (m := m) hm hx hδ_ce hδ_int hflipped_int
    have htarget_eq_neg : target = fun ω => -flipped ω := by
      funext ω
      simp [target, flipped, sub_eq_add_neg, inner_add_right]
    calc
      ∫ ω, ⟪δ ω, c - x ω⟫_ℝ ∂P
          = ∫ ω, target ω ∂P := rfl
      _ = ∫ ω, -flipped ω ∂P := by rw [htarget_eq_neg]
      _ = -∫ ω, flipped ω ∂P := by
          exact integral_neg flipped
      _ = 0 := by simp [hflipped_zero]
  · have htarget_zero : ∫ ω, target ω ∂P = 0 := by
      simp [integral_undef, htarget_int]
    simpa [target] using htarget_zero


-- Merged from Staging/expectation_inner_eq_of_condExp_eq_and_aestronglyMeasurable_right.lean
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

-- Generalization plan (G0):
-- concept/name: expectation equality for an adapted inner-product projection of
--   a conditional mean; orig was `lemma59_y_inner_auxiliary_expectation_relation`.
-- generality used: arbitrary measurable source, arbitrary measure and
--   sub-sigma-algebra, and a complete real Hilbert target; no probability,
--   finite-dimensional, filtration, convexity, smoothness, oracle, or iterate
--   assumptions are used.
-- portable call pattern: stochastic approximation, randomized coordinate
--   descent, variance-reduced methods, and martingale projection steps replace
--   a random vector by its conditional mean inside an inner product against an
--   adapted payload; the measure, conditioning sigma-algebra, payload, random
--   vector, and conditional mean change while the expectation equality stays
--   the same.
-- counterargument checked: not paper-local traceability because it is a
--   paper-free conditional-expectation projection lemma; not covered by the
--   existing zero martingale inner-product lemmas, which require zero
--   conditional mean and a translated payload, or by Mathlib's pull-out theorem
--   alone, which stops at conditional expectation rather than unconditional
--   expectation equality.
-- coverage search: searched SOptLib/project for `condExp inner`,
--   `aestronglyMeasurable right`, `integral_condExp`, and `expectation inner`;
--   closest hits were `condExp_inner_sub_const_eq_zero_of_condExp_eq_zero`,
--   `integral_inner_sub_const_eq_zero_of_condExp_eq_zero`,
--   `integral_eq_of_condExp_ae_eq`, and
--   `condExp_bilin_eq_const_bilin_of_condExp_eq_const`, none covering an
--   arbitrary vector conditional mean inside an inner-product expectation.
-- minimal hypotheses: kept only `m ≤ m0` and sigma-finiteness for integrating
--   conditional expectations, a.e. strong measurability of the adapted right
--   factor, integrability of the vector being conditioned, and integrability of
--   the scalar inner product required by Mathlib's bilinear pull-out theorem.

/-- Replace a Hilbert-valued random vector by its conditional mean inside an
inner product against an adapted payload under expectation.

If `U` is `m`-a.e. strongly measurable and `μ[Y | m] = T` a.e., then the
expectation of `⟪U, Y⟫` equals the expectation of `⟪U, T⟫`, assuming the usual
integrability side conditions for conditional expectation and the scalar inner
product.

Layer: Glue | Gap: Level 1 (conditional-mean inner-product projection)
Proof: apply Mathlib's bilinear conditional-expectation pull-out theorem for an
  a.e. strongly measurable right factor, rewrite the pulled conditional
  expectation by `μ[Y | m] = T`, and integrate the resulting scalar
  conditional-expectation identity.
Source: Mathlib conditional expectation pull-out and Bochner integral APIs
Used in: randomized gradient extrapolation projection of a conditional
  component-gradient identity against the strict-past primal displacement
Book citation: book/FOML/RandomGradientExtrapolation.json#/algorithm_spec/steps/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem expectation_inner_eq_of_condExp_eq_and_aestronglyMeasurable_right
    {Ω E : Type*} {m0 : MeasurableSpace Ω}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : @Measure Ω m0} {m : MeasurableSpace Ω}
    (hm : m ≤ m0)
    [SigmaFinite (μ.trim hm)]
    {Y T U : Ω → E}
    (hU_aesm : AEStronglyMeasurable[m] U μ)
    (hinner_int : Integrable (fun ω => ⟪Y ω, U ω⟫_ℝ) μ)
    (hY_int : Integrable Y μ)
    (hY_ce : μ[Y | m] =ᵐ[μ] T) :
    (∫ ω, ⟪U ω, Y ω⟫_ℝ ∂μ) =
      ∫ ω, ⟪U ω, T ω⟫_ℝ ∂μ := by
  let B : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
  have hpull :
      μ[(fun ω => ⟪Y ω, U ω⟫_ℝ) | m] =ᵐ[μ]
        fun ω => ⟪T ω, U ω⟫_ℝ := by
    have hraw :=
      MeasureTheory.condExp_bilin_of_aestronglyMeasurable_right
        (μ := μ) (m := m) (B := B) (f := Y) (g := U)
        hU_aesm hinner_int hY_int
    refine hraw.trans ?_
    filter_upwards [hY_ce] with ω hω
    rw [hω]
    exact innerSL_apply_apply (𝕜 := ℝ) (T ω) (U ω)
  have hintegral :
      (∫ ω, ⟪Y ω, U ω⟫_ℝ ∂μ) =
        ∫ ω, ⟪T ω, U ω⟫_ℝ ∂μ := by
    exact
      integral_eq_of_condExp_ae_eq
        (μ := μ) (m := m)
        (A := fun ω => ⟪Y ω, U ω⟫_ℝ)
        (B := fun ω => ⟪T ω, U ω⟫_ℝ)
        hm hpull
  change
    (∫ ω, ⟪U ω, Y ω⟫_ℝ ∂μ) =
      ∫ ω, ⟪U ω, T ω⟫_ℝ ∂μ
  calc
    (∫ ω, ⟪U ω, Y ω⟫_ℝ ∂μ) =
        ∫ ω, ⟪Y ω, U ω⟫_ℝ ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards with ω
          exact (real_inner_comm (U ω) (Y ω)).symm
    _ = ∫ ω, ⟪T ω, U ω⟫_ℝ ∂μ := hintegral
    _ = ∫ ω, ⟪U ω, T ω⟫_ℝ ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards with ω
          exact (real_inner_comm (T ω) (U ω)).symm
