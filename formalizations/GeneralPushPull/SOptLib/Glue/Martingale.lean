-- SOptLib/Glue/Martingale.lean
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Process.Filtration
import SOptLib.Glue.Probability
import SOptLib.Model.ConditionalExpectation


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

-- Promoted from Staging/integral_weighted_norm_sq_sub_le_of_centered_inner_eq_zero.lean
open MeasureTheory
open scoped InnerProductSpace

-- Generalization plan (G0):
-- concept/name: weighted Hilbert second-moment centering contraction; orig was
--   integral_weighted_norm_sq_sub_le_integral_weighted_norm_sq_of_inner_sub_zero
-- generality used: arbitrary measurable sample space, arbitrary measure, real
--   inner-product space, nonnegative a.e. scalar weight, and only the three
--   weighted scalar integrability hypotheses used by integral linearity
-- portable call pattern: recursive-momentum, martingale, and control-variate
--   analyses replace a weighted centered error square by its uncentered second
--   moment while the random weight and Hilbert-valued processes vary
-- counterargument checked: this is not paper-local traceability or a pure
--   wrapper; the random weight prevents direct use of the existing unweighted
--   centering contraction and introduces a distinct weighted integrability contract
-- coverage search: symbol searches for weighted squared-norm centering and
--   zero centered inner integrals found the partial SOptLib theorem
--   integral_norm_sq_sub_le_integral_norm_sq_of_inner_sub_zero; LeanSearch found
--   integral nonnegativity but no weighted Hilbert centering contraction
-- minimal hypotheses: no probability, finite-measure, measurability, completeness,
--   finite-dimensionality, convexity, smoothness, or oracle hypotheses are used

/-- A nonnegative weighted centered second moment is at most its uncentered second moment.

The vanishing weighted inner product between the center and the centered
residual makes the polarization cross term equal the weighted center square;
nonnegativity of the weight then permits that square to be discarded.

Layer: Glue | Gap: Level 1 (weighted Hilbert second-moment centering contraction)
Proof: expand the weighted squared norm with real Hilbert polarization, use the centered-inner integral to identify the cross moment, and drop the nonnegative weighted center square.
Source: Mathlib Bochner integral linearity, a.e. integral nonnegativity, and real inner-product norm-square identities
Used in: recursive-momentum and martingale error recurrences that replace randomly weighted centered estimator squares by uncentered second moments
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec/steps
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum -/
theorem integral_weighted_norm_sq_sub_le_of_centered_inner_eq_zero
    {Ω E : Type*} [MeasurableSpace Ω]
    [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure Ω) {w : Ω → ℝ} {g m : Ω → E}
    (hw_nonneg : ∀ᵐ ω ∂μ, 0 ≤ w ω)
    (hwg_sq : Integrable (fun ω => w ω * ‖g ω‖ ^ 2) μ)
    (hwm_sq : Integrable (fun ω => w ω * ‖m ω‖ ^ 2) μ)
    (hcenter_int :
      Integrable (fun ω => w ω * inner ℝ (m ω) (g ω - m ω)) μ)
    (hcenter_zero :
      ∫ ω, w ω * inner ℝ (m ω) (g ω - m ω) ∂μ = 0) :
    ∫ ω, w ω * ‖g ω - m ω‖ ^ 2 ∂μ ≤
      ∫ ω, w ω * ‖g ω‖ ^ 2 ∂μ := by
  classical
  have hmg_int : Integrable (fun ω => w ω * inner ℝ (m ω) (g ω)) μ := by
    have hsum :
        Integrable
          (fun ω =>
            w ω * inner ℝ (m ω) (g ω - m ω) + w ω * ‖m ω‖ ^ 2) μ :=
      hcenter_int.add hwm_sq
    refine hsum.congr ?_
    filter_upwards with ω
    rw [inner_sub_right]
    simp [sub_eq_add_neg]
    ring
  have hgm_int : Integrable (fun ω => w ω * inner ℝ (g ω) (m ω)) μ := by
    refine hmg_int.congr ?_
    filter_upwards with ω
    simp [real_inner_comm]
  have hmg_eq :
      ∫ ω, w ω * inner ℝ (m ω) (g ω) ∂μ =
        ∫ ω, w ω * ‖m ω‖ ^ 2 ∂μ := by
    have hcenter_as_sub :
        ∫ ω, w ω * inner ℝ (m ω) (g ω - m ω) ∂μ =
          ∫ ω, (w ω * inner ℝ (m ω) (g ω) - w ω * ‖m ω‖ ^ 2) ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards with ω
      rw [inner_sub_right]
      simp [mul_sub]
    have hsub :
        ∫ ω, (w ω * inner ℝ (m ω) (g ω) - w ω * ‖m ω‖ ^ 2) ∂μ =
          ∫ ω, w ω * inner ℝ (m ω) (g ω) ∂μ -
            ∫ ω, w ω * ‖m ω‖ ^ 2 ∂μ :=
      integral_sub hmg_int hwm_sq
    have hzero :
        ∫ ω, w ω * inner ℝ (m ω) (g ω) ∂μ -
            ∫ ω, w ω * ‖m ω‖ ^ 2 ∂μ = 0 := by
      linarith
    linarith
  have hgm_eq :
      ∫ ω, w ω * inner ℝ (g ω) (m ω) ∂μ =
        ∫ ω, w ω * ‖m ω‖ ^ 2 ∂μ := by
    simpa [real_inner_comm] using hmg_eq
  have h_expand :
      ∫ ω, w ω * ‖g ω - m ω‖ ^ 2 ∂μ =
        ∫ ω, w ω * ‖g ω‖ ^ 2 ∂μ -
          2 * ∫ ω, w ω * inner ℝ (g ω) (m ω) ∂μ +
            ∫ ω, w ω * ‖m ω‖ ^ 2 ∂μ := by
    calc
      ∫ ω, w ω * ‖g ω - m ω‖ ^ 2 ∂μ
          = ∫ ω,
              (w ω * ‖g ω‖ ^ 2 - 2 * (w ω * inner ℝ (g ω) (m ω)) +
                w ω * ‖m ω‖ ^ 2) ∂μ := by
              refine integral_congr_ae ?_
              filter_upwards with ω
              have hsq := norm_sub_sq_real (g ω) (m ω)
              rw [hsq]
              ring
      _ = ∫ ω, ((w ω * ‖g ω‖ ^ 2 - 2 * (w ω * inner ℝ (g ω) (m ω))) +
              w ω * ‖m ω‖ ^ 2) ∂μ := by
              refine integral_congr_ae ?_
              filter_upwards with ω
              ring
      _ = ∫ ω, (w ω * ‖g ω‖ ^ 2 - 2 * (w ω * inner ℝ (g ω) (m ω))) ∂μ +
            ∫ ω, w ω * ‖m ω‖ ^ 2 ∂μ := by
              exact integral_add (hwg_sq.sub (hgm_int.const_mul 2)) hwm_sq
      _ = (∫ ω, w ω * ‖g ω‖ ^ 2 ∂μ -
            ∫ ω, 2 * (w ω * inner ℝ (g ω) (m ω)) ∂μ) +
            ∫ ω, w ω * ‖m ω‖ ^ 2 ∂μ := by
              rw [integral_sub hwg_sq (hgm_int.const_mul 2)]
      _ = ∫ ω, w ω * ‖g ω‖ ^ 2 ∂μ -
            2 * ∫ ω, w ω * inner ℝ (g ω) (m ω) ∂μ +
              ∫ ω, w ω * ‖m ω‖ ^ 2 ∂μ := by
              rw [integral_const_mul]
  calc
    ∫ ω, w ω * ‖g ω - m ω‖ ^ 2 ∂μ
        = ∫ ω, w ω * ‖g ω‖ ^ 2 ∂μ -
            ∫ ω, w ω * ‖m ω‖ ^ 2 ∂μ := by
            rw [h_expand, hgm_eq]
            ring
    _ ≤ ∫ ω, w ω * ‖g ω‖ ^ 2 ∂μ := by
            have hnonneg :
                0 ≤ ∫ ω, w ω * ‖m ω‖ ^ 2 ∂μ := by
              refine integral_nonneg_of_ae ?_
              filter_upwards [hw_nonneg] with ω hwω
              exact mul_nonneg hwω (sq_nonneg _)
            linarith

/-! Promoted from Staging/condExp_finset_sum_eq_zero_of_filtration_mono.lean. -/


open MeasureTheory

-- Generalization plan (G0):
-- concept/name: conditional expectation of a finite sum of later-filtration
--   centered increments; orig was `blockNoise_conditionalExpectationEq_zero`.
-- generality used: arbitrary summand index type and finite index set, arbitrary
--   measure and preordered filtration time, and an arbitrary real Banach target; no
--   probability, Hilbert-space, finite-dimensional, or oracle assumptions.
-- portable call pattern: block, epoch, delayed-update, and mini-batch stochastic
--   algorithms form deterministic weighted sums of integrable martingale
--   differences whose sampling times vary but all lie after the conditioning time.
-- counterargument checked: this is not paper-local traceability or a pure
--   wrapper; it composes finite-sum conditional-expectation linearity with a
--   separate filtration-tower argument for every time-indexed summand.
-- coverage search: `conditional expectation finite sum equals zero filtration
--   monotonicity integrable martingale differences` and `conditional expectation
--   of a finite sum equals sum`; Mathlib provides `condExp_finset_sum` and
--   `Filtration.condExp_condExp` separately, while SOptLib has no theorem
--   combining later-time centering with a base-time finite sum.
-- minimal hypotheses: base trim sigma-finiteness is needed even for an empty
--   sum; each later trim's sigma-finiteness and summand integrability are already
--   supplied by its bundled `conditionalExpectationEq` hypothesis.

/-- A deterministic weighted finite sum of increments centered at later
filtration times is centered at the base filtration time.

Each summand may use its own later time. The result first transports its
conditional centering backward by the filtration tower property, then applies
conditional-expectation linearity and scalar compatibility to the finite sum.

Layer: Glue | Gap: Level 1 (finite martingale-difference aggregation across filtration times)
Proof: use the conditional-expectation tower property to center every summand
  at the base time, then commute conditional expectation through deterministic
  scalar multiplication and the finite sum.
Source: Mathlib `MeasureTheory.Filtration.condExp_condExp` and
  `MeasureTheory.condExp_finset_sum`/`MeasureTheory.condExp_smul`
Used in: periodic stochastic push-pull block-noise centering, and future epoch
  or delayed-update aggregation of time-indexed martingale differences
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/3/proof/3
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed
  Exogenous Periodic Directed Networks, block noise in the lifted-center recursion -/
theorem condExp_finset_sum_eq_zero_of_filtration_mono
    {Ω E ι T : Type*} [MeasurableSpace Ω] [Preorder T]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) (filt : Filtration T ‹MeasurableSpace Ω›)
    (base : T) (I : Finset ι) (time : ι → T)
    (coeff : ι → ℝ) (δ : ι → Ω → E)
    [SigmaFinite (μ.trim (filt.le base))]
    (htime : ∀ i ∈ I, base ≤ time i)
    (hδ_zero : ∀ i ∈ I,
      SOptLib.ConditionalExpectation.conditionalExpectationEq μ
        (filt (time i)) (δ i) (fun _ => (0 : E))) :
    SOptLib.ConditionalExpectation.conditionalExpectationEq μ (filt base)
      (fun ω => ∑ i ∈ I, coeff i • δ i ω) (fun _ => (0 : E)) := by
  classical
  have hδ_int : ∀ i ∈ I, Integrable (δ i) μ := fun i hi =>
    (hδ_zero i hi).wellDefined.integrable
  rw [SOptLib.ConditionalExpectation.conditionalExpectationEq_def]
  refine ⟨⟨filt.le base, inferInstance,
    integrable_finset_sum I (fun i hi => (hδ_int i hi).smul (coeff i))⟩, ?_⟩
  have hterm : ∀ i ∈ I, μ[δ i | filt base] =ᵐ[μ] (0 : Ω → E) := by
    intro i hi
    have hzero := hδ_zero i hi
    rcases hzero.1 with ⟨hm, hsf, _hint⟩
    haveI : SigmaFinite (μ.trim (filt.le (time i))) := by
      simpa only using hsf
    calc
      μ[δ i | filt base] =ᵐ[μ]
          μ[μ[δ i | filt (time i)] | filt base] :=
        (filt.condExp_condExp (δ i) (htime i hi)).symm
      _ =ᵐ[μ] μ[(0 : Ω → E) | filt base] := condExp_congr_ae hzero.2
      _ =ᵐ[μ] 0 := by rw [condExp_zero]
  have hscaled : ∀ i ∈ I,
      μ[fun ω => coeff i • δ i ω | filt base] =ᵐ[μ] (0 : Ω → E) := by
    intro i hi
    calc
      μ[fun ω => coeff i • δ i ω | filt base] =ᵐ[μ]
          coeff i • μ[δ i | filt base] := condExp_smul (coeff i) (δ i) _
      _ =ᵐ[μ] coeff i • (0 : Ω → E) := (hterm i hi).const_smul (coeff i)
      _ =ᵐ[μ] 0 := Filter.Eventually.of_forall (fun _ => smul_zero _)
  rw [show (fun ω => ∑ i ∈ I, coeff i • δ i ω) =
      ∑ i ∈ I, fun ω => coeff i • δ i ω by
    funext ω
    simp]
  refine (condExp_finset_sum
    (fun i hi => (hδ_int i hi).smul (coeff i)) (filt base)).trans ?_
  simpa only [Finset.sum_const_zero] using
    (eventuallyEq_sum fun i hi => hscaled i hi)

/-! Promoted from Staging/integral_inner_eq_zero_of_ne_of_forward_cross_zero.lean. -/


open MeasureTheory
open scoped InnerProductSpace

-- Generalization plan (G0):
-- concept/name: pairwise integral orthogonality from forward cross-integral
--   cancellation; orig was a local `hcross` orientation block.
-- generality used: an arbitrary measurable sample space, real inner-product
--   space, measure, and linearly ordered process; no probability, finiteness,
--   integrability, completeness, measurability-on-the-carrier, or finite-
--   dimensional assumptions are used.
-- portable call pattern: martingale-difference, sequential-noise, and
--   variance-reduced methods can turn a time-ordered cancellation rule into
--   the pairwise cross-zero premise required by finite covariance
--   diagonalization while changing the process and forward rule.
-- counterargument checked: this is not paper-local traceability or a pure
--   rename; it isolates the reusable order-orientation and real-inner symmetry
--   step. The related Layer0 oracle-residual theorem carries a filtration,
--   cutoff, measurability, and diagonal-integrability frame absent here.
-- coverage search: searched "integral inner product equals zero for distinct
--   indices from forward ordered cross cancellation" and "symmetric inner
--   product reverse indices integral zero" with project symbol search, plus
--   the exact implication with Mathlib LeanSearch. Mathlib returned only
--   pointwise orthogonality results; SOptLib's
--   `centeredOracleResidual_inner_integral_eq_zero_of_distinct_fresh` is
--   partial, Layer0-specific coverage rather than this minimal Glue contract.
-- minimal hypotheses: all already minimal; only distinctness and the one-sided
--   cross-integral cancellation rule are consumed.

/-- A forward cross-integral cancellation rule makes every distinct pair
orthogonal in integral.

Layer: Glue | Gap: Level 1 (ordered cross-cancellation orientation)
Proof: orient the two distinct indices; use the supplied forward rule
  directly in one order and real-inner-product symmetry in the reverse order.
Source: Mathlib natural-order trichotomy, real Hilbert-space inner-product
  symmetry, and Bochner integral congruence APIs
Used in: propagated sequential-noise covariance diagonalization, where a
  forward martingale cancellation rule must supply every off-diagonal pair
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/6
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on
  Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem integral_inner_eq_zero_of_ne_of_forward_cross_zero
    {Omega E ι : Type*} [MeasurableSpace Omega]
    [SeminormedAddCommGroup E] [InnerProductSpace Real E] [LinearOrder ι]
    (mu : Measure Omega) (Z : ι -> Omega -> E) (i j : ι)
    (hforward :
      forall {a b : ι}, a < b ->
        (∫ omega, inner Real (Z a omega) (Z b omega) ∂mu) = 0)
    (hij : i ≠ j) :
    (∫ omega, inner Real (Z i omega) (Z j omega) ∂mu) = 0 := by
  rcases lt_or_gt_of_ne hij with hij_lt | hji_lt
  · exact hforward hij_lt
  · have hzero :
        (∫ omega, inner Real (Z j omega) (Z i omega) ∂mu) = 0 :=
      hforward hji_lt
    simpa only [real_inner_comm] using hzero

/-! Promoted from Staging/integral_norm_sq_affine_add_eq_of_cross_zero.lean. -/


open MeasureTheory
open scoped InnerProductSpace

-- Generalization plan (G0):
-- concept/name: `integral_norm_sq_smul_add_smul_eq_of_integral_inner_eq_zero`;
--   orig was `integral_norm_sq_affine_add_eq_of_cross_zero`
-- generality used: arbitrary measure on a measurable sample type, an arbitrary real
--   Hilbert space, two processes, two deterministic real coefficients, integrable
--   diagonal and cross terms, and a zero cross-inner-product integral
-- portable call pattern: martingale recurrences, stochastic linear systems, and
--   variance decompositions can change both L2 processes and both deterministic
--   coefficients while reusing the same exact two-term second-moment expansion
-- counterargument checked: not paper-local traceability or a pure wrapper; the
--   finite-family SOptLib theorem requires component measurability and pairwise
--   bookkeeping, while the related staged scaled-difference theorem proves only a
--   lower bound under stronger `MemLp` hypotheses rather than this exact equality
-- coverage search: queries `integral squared norm linear combination zero cross
--   inner product`, `integral norm squared add orthogonal cross zero`, and `second
--   moment affine combination zero covariance` found the partial SOptLib theorem
--   `integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero`; Mathlib semantic
--   search found the pointwise `norm_add_sq_real`, but no integral-level equality
-- minimal hypotheses: the two diagonal integrability assumptions and cross-term
--   integrability are exactly those used by integral linearity; the measure need not
--   be finite or probabilistic, and no completeness or finite-dimensionality is used

/-- The second moment of a deterministic two-term Hilbert-space combination is
the sum of its scaled diagonal moments when the cross moment vanishes.

Layer: Glue | Gap: Level 1 (two-term Hilbert second-moment diagonalization)
Proof: expand the pointwise squared norm with real Hilbert polarization, commute the integral through the three integrable scalar terms, and cancel the cross integral.
Source: Mathlib `norm_add_sq_real`, real inner-product scalar identities, and Bochner integral linearity
Used in: block-phase and block-boundary second-moment recurrences after predictable states are shown orthogonal to fresh stochastic innovations
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/15/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem integral_norm_sq_smul_add_smul_eq_of_integral_inner_eq_zero
    {Omega E : Type*} [MeasurableSpace Omega]
    [SeminormedAddCommGroup E] [InnerProductSpace Real E]
    (mu : Measure Omega) (u v : Omega -> E) (a b : Real)
    (hu_sq_int : Integrable (fun omega => ‖u omega‖ ^ 2) mu)
    (hv_sq_int : Integrable (fun omega => ‖v omega‖ ^ 2) mu)
    (hcross_int : Integrable (fun omega => ⟪u omega, v omega⟫_Real) mu)
    (hcross_zero : (∫ omega, ⟪u omega, v omega⟫_Real ∂mu) = 0) :
    (∫ omega, ‖a • u omega + b • v omega‖ ^ 2 ∂mu) =
      a ^ 2 * (∫ omega, ‖u omega‖ ^ 2 ∂mu) +
        b ^ 2 * (∫ omega, ‖v omega‖ ^ 2 ∂mu) := by
  have hua_int : Integrable (fun omega => a ^ 2 * ‖u omega‖ ^ 2) mu :=
    hu_sq_int.const_mul (a ^ 2)
  have hvb_int : Integrable (fun omega => b ^ 2 * ‖v omega‖ ^ 2) mu :=
    hv_sq_int.const_mul (b ^ 2)
  have hcross_scaled_int :
      Integrable (fun omega => (2 * a * b) * ⟪u omega, v omega⟫_Real) mu :=
    hcross_int.const_mul (2 * a * b)
  have hpoint :
      (fun omega => ‖a • u omega + b • v omega‖ ^ 2) =
        fun omega =>
          a ^ 2 * ‖u omega‖ ^ 2 + b ^ 2 * ‖v omega‖ ^ 2 +
            (2 * a * b) * ⟪u omega, v omega⟫_Real := by
    funext omega
    rw [norm_add_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, inner_smul_left, inner_smul_right]
    simp [mul_pow, sq_abs]
    ring
  rw [hpoint]
  calc
    (∫ omega,
        (a ^ 2 * ‖u omega‖ ^ 2 + b ^ 2 * ‖v omega‖ ^ 2) +
          (2 * a * b) * ⟪u omega, v omega⟫_Real ∂mu) =
        (∫ omega,
          a ^ 2 * ‖u omega‖ ^ 2 + b ^ 2 * ‖v omega‖ ^ 2 ∂mu) +
          ∫ omega, (2 * a * b) * ⟪u omega, v omega⟫_Real ∂mu :=
      integral_add (hua_int.add hvb_int) hcross_scaled_int
    _ = a ^ 2 * (∫ omega, ‖u omega‖ ^ 2 ∂mu) +
          b ^ 2 * (∫ omega, ‖v omega‖ ^ 2 ∂mu) := by
      rw [integral_add hua_int hvb_int]
      rw [integral_const_mul, integral_const_mul, integral_const_mul,
        hcross_zero]
      ring

/-! Promoted from Staging/integral_dependentProductNormSq_finset_sum_eq_sum_integrals_of_cross_zero.lean. -/


open MeasureTheory
open scoped BigOperators InnerProductSpace

-- Generalization plan (G0):
-- concept/name: integral diagonalization of finite sums for dependent-product squared energy; orig was noiseJointCoordinate_expected_frobenius_eq_sum
-- generality used: arbitrary measure on a measurable sample type, finite dependent coordinate family of real inner-product spaces, and a finite summand set; no probability, completeness, finite-dimensionality, oracle, or algorithm assumptions
-- portable call pattern: distributed and block stochastic algorithms diagonalize the expected coordinate energy of finite martingale-transform, mini-batch, or filtered-noise sums while changing the coordinate spaces, summand set, measure, and cross-orthogonality proof
-- counterargument checked: this is not only a paper wrapper because it tensors a one-fiber covariance identity across a dependent finite product and performs the required integral/sum interchange; the existing Hilbert-valued lemma does not conclude an identity for dependentProductNormSq
-- coverage search: queried `integral dependent product norm squared finite sum equals sum integrals coordinatewise cross zero` and `finite coordinate energy integral sum diagonal cross inner products vanish`; the closest SOptLib hits were `integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero` and `dependentProductNormSq_eq_sum`, while Mathlib semantic search returned only component lemmas such as `inner_sum` and `MeasureTheory.integral_finset_sum`
-- minimal hypotheses: source probability, common coordinate carrier, completeness, and finite-dimensional assumptions were dropped; coordinate a.e. strong measurability, square integrability, and vanishing off-diagonal cross integrals are exactly those consumed by the one-fiber diagonalization and finite integral interchange

/-- The integral of the dependent-product energy of a finite sum is the sum of
the term energies when every coordinatewise off-diagonal cross integral vanishes.

Layer: Glue | Gap: Level 1 (dependent-product finite covariance diagonalization)
Proof: apply the Hilbert-valued finite covariance diagonalization in every coordinate,
  then interchange the two finite sums and the coordinate sum with the integral.
Source: SOptLib finite Hilbert covariance diagonalization, Mathlib Bochner integral
  finite-sum linearity, and finite dependent-product squared energy
Used in: distributed gradient-tracking and block stochastic methods that diagonalize
  the expected coordinate energy of a finite martingale-transform or filtered-noise sum
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/main_theorem/proof/0
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed
  Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem integral_dependentProductNormSq_finset_sum_eq_sum_integrals_of_cross_zero
    {Omega iota kappa : Type*} [MeasurableSpace Omega] [Fintype iota]
    {E : iota -> Type*}
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace Real (E i)]
    [DecidableEq kappa]
    (mu : Measure Omega) (I : Finset kappa)
    (delta : kappa -> Omega -> ∀ i, E i)
    (hmeas : ∀ k ∈ I, ∀ i,
      AEStronglyMeasurable (fun omega => delta k omega i) mu)
    (hL2 : ∀ k ∈ I, ∀ i,
      Integrable (fun omega => ‖delta k omega i‖ ^ 2) mu)
    (hcross : ∀ i, ∀ k ∈ I, ∀ l ∈ I, k ≠ l ->
      ∫ omega, ⟪delta k omega i, delta l omega i⟫_Real ∂mu = 0) :
    (∫ omega, SOptLib.dependentProductNormSq
      (Finset.sum I (fun k => delta k omega)) ∂mu) =
      Finset.sum I (fun k =>
        ∫ omega, SOptLib.dependentProductNormSq (delta k omega) ∂mu) := by
  classical
  have hmem (k : kappa) (hk : k ∈ I) (i : iota) :
      MemLp (fun omega => delta k omega i) 2 mu :=
    (memLp_two_iff_integrable_sq_norm (hmeas k hk i)).2 (hL2 k hk i)
  have hcoordinate (i : iota) :
      (∫ omega, ‖Finset.sum I (fun k => delta k omega i)‖ ^ 2 ∂mu) =
        Finset.sum I (fun k => ∫ omega, ‖delta k omega i‖ ^ 2 ∂mu) := by
    exact integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
      mu I (fun k omega => delta k omega i)
      (fun k hk => hmeas k hk i) (fun k hk => hL2 k hk i) (hcross i)
  simp only [SOptLib.dependentProductNormSq_def]
  rw [MeasureTheory.integral_finset_sum]
  · calc
      (∑ i : iota,
          ∫ omega, ‖(Finset.sum I (fun k => delta k omega)) i‖ ^ 2 ∂mu) =
          ∑ i : iota, Finset.sum I (fun k =>
            ∫ omega, ‖delta k omega i‖ ^ 2 ∂mu) := by
        apply Finset.sum_congr rfl
        intro i _hi
        simpa only [Finset.sum_apply] using hcoordinate i
      _ = Finset.sum I (fun k =>
          ∑ i : iota, ∫ omega, ‖delta k omega i‖ ^ 2 ∂mu) := by
        rw [Finset.sum_comm]
      _ = Finset.sum I (fun k =>
          ∫ omega, ∑ i : iota, ‖delta k omega i‖ ^ 2 ∂mu) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [MeasureTheory.integral_finset_sum]
        exact fun i _hi => hL2 k hk i
  · intro i _hi
    have hsum : MemLp
        (fun omega => Finset.sum I (fun k => delta k omega i)) 2 mu := by
      apply memLp_finset_sum I
      intro k hk
      exact hmem k hk i
    simpa only [Finset.sum_apply] using
      ((memLp_two_iff_integrable_sq_norm hsum.aestronglyMeasurable).1 hsum)

/-! Promoted from Staging/integral_sq_smul_sub_ge_of_cross_integral_eq_zero.lean. -/


open MeasureTheory
open scoped InnerProductSpace

-- Generalization plan (G0):
-- concept/name: lower Pythagorean bound for a scaled difference of orthogonal
--   L2 processes; orig was `real_integral_sq_sub_scaled_lower_of_cross_zero`
-- generality used: arbitrary measure on a measurable sample type, a real
--   inner-product space, two independent real coefficients, and two L2 processes;
--   no probability, finite-measure, completeness, finite-dimensionality,
--   convexity, smoothness, oracle, or algorithm assumptions
-- portable call pattern: martingale-recursion, control-variate, and stochastic
--   comparison proofs change the two L2 random variables and scalar coefficients
--   while retaining the same innovation-energy lower bound after proving their
--   cross inner-product integral is zero
-- counterargument checked: this is not paper-local traceability or a pure rename;
--   it packages coefficient scaling, two-term orthogonality, integral expansion,
--   and diagonal nonnegativity in the direct lower-bound orientation needed by callers
-- coverage search: queries `integral squared scaled subtraction lower bound zero
--   cross integral MemLp` and `integral square difference equality sum squares
--   cross zero` found the partial SOptLib theorem
--   `integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero` and centering
--   contractions in `SOptLib.Glue.Martingale`; Mathlib semantic search found only
--   pointwise Pythagorean and L2-space inner-product components, not this bound
-- minimal hypotheses: both `MemLp` hypotheses provide exactly the square and
--   cross-term integrability used by integral linearity; the cross-integral equality
--   is the sole orthogonality assumption, and all source-specific assumptions are dropped

/-- The squared integral norm of a scaled difference of orthogonal L2 processes
dominates the squared coefficient times the second process's energy.

Layer: Glue | Gap: Level 1 (scaled two-term L2 Pythagorean lower bound)
Proof: expand the squared norm by real Hilbert-space polarization, commute the integral through the integrable scalar terms, cancel the cross integral, and discard the nonnegative first diagonal energy.
Source: Mathlib `MemLp` product integrability, Bochner integral linearity, and real Hilbert-space norm-square polarization; SOptLib finite covariance diagonalization provides related finite-family coverage
Used in: fresh-noise lower bounds for martingale recursions and stochastic comparison processes after the predictable component is shown orthogonal to the current innovation
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/16/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem integral_sq_smul_sub_ge_of_cross_integral_eq_zero
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [InnerProductSpace Real E]
    (mu : Measure Omega) (a b : Real) {P N : Omega -> E}
    (hP : MemLp P 2 mu) (hN : MemLp N 2 mu)
    (hcross : (∫ omega, ⟪P omega, N omega⟫_Real ∂mu) = 0) :
    b ^ 2 * (∫ omega, ‖N omega‖ ^ 2 ∂mu) <=
      ∫ omega, ‖a • P omega - b • N omega‖ ^ 2 ∂mu := by
  have hP2_int : Integrable (fun omega => ‖P omega‖ ^ 2) mu :=
    (memLp_two_iff_integrable_sq_norm hP.aestronglyMeasurable).1 hP
  have hN2_int : Integrable (fun omega => ‖N omega‖ ^ 2) mu :=
    (memLp_two_iff_integrable_sq_norm hN.aestronglyMeasurable).1 hN
  have hPN_int : Integrable (fun omega => ⟪P omega, N omega⟫_Real) mu := by
    have hprod : Integrable (fun omega => ‖P omega‖ * ‖N omega‖) mu := by
      simpa [Pi.mul_apply] using
        (MemLp.integrable_mul hP.norm hN.norm :
          Integrable ((fun omega => ‖P omega‖) * (fun omega => ‖N omega‖)) mu)
    exact hprod.mono'
      (hP.aestronglyMeasurable.inner hN.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun omega => by
        simpa [Real.norm_eq_abs] using abs_real_inner_le_norm (P omega) (N omega))
  have hscaledP_int :
      Integrable (fun omega => a ^ 2 * ‖P omega‖ ^ 2) mu :=
    hP2_int.const_mul (a ^ 2)
  have hcross_scaled_int :
      Integrable (fun omega => 2 * a * b * ⟪P omega, N omega⟫_Real) mu :=
    hPN_int.const_mul (2 * a * b)
  have hscaledN_int :
      Integrable (fun omega => b ^ 2 * ‖N omega‖ ^ 2) mu :=
    hN2_int.const_mul (b ^ 2)
  have hexpand :
      (∫ omega, ‖a • P omega - b • N omega‖ ^ 2 ∂mu) =
        a ^ 2 * (∫ omega, ‖P omega‖ ^ 2 ∂mu) -
          2 * a * b * (∫ omega, ⟪P omega, N omega⟫_Real ∂mu) +
            b ^ 2 * (∫ omega, ‖N omega‖ ^ 2 ∂mu) := by
    have hpoint :
        (fun omega => ‖a • P omega - b • N omega‖ ^ 2) =
          fun omega =>
            a ^ 2 * ‖P omega‖ ^ 2 -
              2 * a * b * ⟪P omega, N omega⟫_Real +
                b ^ 2 * ‖N omega‖ ^ 2 := by
      funext omega
      rw [norm_sub_sq_real]
      simp only [norm_smul, Real.norm_eq_abs, inner_smul_left, inner_smul_right]
      simp [mul_pow, sq_abs]
      ring
    rw [hpoint]
    calc
      (∫ omega,
          (a ^ 2 * ‖P omega‖ ^ 2 -
            2 * a * b * ⟪P omega, N omega⟫_Real) +
              b ^ 2 * ‖N omega‖ ^ 2 ∂mu) =
          (∫ omega,
            a ^ 2 * ‖P omega‖ ^ 2 -
              2 * a * b * ⟪P omega, N omega⟫_Real ∂mu) +
            ∫ omega, b ^ 2 * ‖N omega‖ ^ 2 ∂mu :=
        integral_add (hscaledP_int.sub hcross_scaled_int) hscaledN_int
      _ = a ^ 2 * (∫ omega, ‖P omega‖ ^ 2 ∂mu) -
            2 * a * b * (∫ omega, ⟪P omega, N omega⟫_Real ∂mu) +
              b ^ 2 * (∫ omega, ‖N omega‖ ^ 2 ∂mu) := by
        rw [integral_sub hscaledP_int hcross_scaled_int]
        rw [integral_const_mul, integral_const_mul, integral_const_mul]
  rw [hexpand, hcross]
  have ha_nonneg : 0 <= a ^ 2 := sq_nonneg a
  have hP_nonneg : 0 <= ∫ omega, ‖P omega‖ ^ 2 ∂mu :=
    integral_nonneg (fun omega => sq_nonneg ‖P omega‖)
  nlinarith

/-! Promoted from Staging/integral_norm_sq_finset_weighted_sum_eq_sum_sq_mul_of_cross_zero.lean. -/


open MeasureTheory
open scoped BigOperators InnerProductSpace

-- Generalization plan (G0):
-- concept/name: exact second moment of a deterministically weighted finite orthogonal sum;
--   orig was sameTime_weightedNoise_secondMoment_eq_exact
-- generality used: arbitrary measurable sample type, arbitrary measure, finite index set,
--   real Hilbert-valued coordinates, deterministic real weights, square integrability,
--   pairwise zero cross integrals, and exact coordinate second moments
-- portable call pattern: distributed and mini-batch stochastic algorithms can change the
--   coordinate type, weights, Hilbert-valued noise, and diagonal moment profile while reusing
--   the same covariance-diagonalization conclusion
-- counterargument checked: not paper-local traceability or a pure wrapper; the existing
--   unweighted covariance theorem leaves both deterministic scaling and exact diagonal-moment
--   substitution to every caller, while this theorem packages that recurring mathematical step
-- coverage search: searched `integral squared norm deterministic weighted finite sum equals sum
--   squared weights exact second moments cross inner integral zero` and `weighted finset sum norm
--   square integral cross zero diagonal moments`; SOptLib's
--   `integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero` is a strict unweighted ingredient,
--   and Mathlib's orthogonal-family norm identities are pointwise rather than integral statements
-- minimal hypotheses: arbitrary measure rather than probability measure; a Finset rather than a
--   Fintype; no centering, independence, completeness, or finite-dimensionality assumptions

/-- The second moment of a deterministically weighted finite sum is the weighted
sum of exact coordinate second moments when all cross integrals vanish.

Layer: Glue | Gap: Level 1 (weighted finite Hilbert covariance diagonalization with exact diagonal moments)
Proof: apply the finite Hilbert covariance diagonalization to the scalar-multiplied coordinates, pull deterministic squared weights through each integral, and substitute the exact diagonal moments.
Source: SOptLib finite Hilbert covariance diagonalization and Mathlib Bochner integral scalar-linearity APIs
Used in: distributed stochastic-gradient and mini-batch proofs computing exact variance of weighted coordinate-noise aggregates
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/15/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem integral_norm_sq_finset_weighted_sum_eq_sum_sq_mul_of_cross_zero
    {Omega E I : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [InnerProductSpace Real E]
    [DecidableEq I] (mu : Measure Omega) (s : Finset I)
    (c : I -> Real) (Z : I -> Omega -> E) (v : I -> Real)
    (hmeas : ∀ i ∈ s, AEStronglyMeasurable (Z i) mu)
    (hL2 : ∀ i ∈ s, Integrable (fun omega => ‖Z i omega‖ ^ 2) mu)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j ->
      (∫ omega, ⟪Z i omega, Z j omega⟫_Real ∂mu) = 0)
    (hdiag : ∀ i ∈ s, (∫ omega, ‖Z i omega‖ ^ 2 ∂mu) = v i) :
    (∫ omega, ‖Finset.sum s (fun i => c i • Z i omega)‖ ^ 2 ∂mu) =
      Finset.sum s (fun i => c i ^ 2 * v i) := by
  let delta : I -> Omega -> E := fun i omega => c i • Z i omega
  have hdelta_meas : ∀ i ∈ s, AEStronglyMeasurable (delta i) mu := by
    intro i hi
    exact (hmeas i hi).const_smul (c i)
  have hdelta_L2 : ∀ i ∈ s,
      Integrable (fun omega => ‖delta i omega‖ ^ 2) mu := by
    intro i hi
    simpa [delta, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] using
      (hL2 i hi).const_mul (c i ^ 2)
  have hdelta_cross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j ->
      (∫ omega, ⟪delta i omega, delta j omega⟫_Real ∂mu) = 0 := by
    intro i hi j hj hij
    simp only [delta, real_inner_smul_left, real_inner_smul_right]
    rw [integral_const_mul, integral_const_mul, hcross i hi j hj hij,
      mul_zero, mul_zero]
  have hsum := integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
    mu s delta hdelta_meas hdelta_L2 hdelta_cross
  calc
    (∫ omega, ‖Finset.sum s (fun i => c i • Z i omega)‖ ^ 2 ∂mu) =
        ∫ omega, ‖Finset.sum s (fun i => delta i omega)‖ ^ 2 ∂mu := by
          rfl
    _ = Finset.sum s (fun i => ∫ omega, ‖delta i omega‖ ^ 2 ∂mu) := hsum
    _ = Finset.sum s (fun i => c i ^ 2 * v i) := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        (∫ omega, ‖delta i omega‖ ^ 2 ∂mu) =
            ∫ omega, c i ^ 2 * ‖Z i omega‖ ^ 2 ∂mu := by
              congr 1
              funext omega
              simp [delta, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        _ = c i ^ 2 * (∫ omega, ‖Z i omega‖ ^ 2 ∂mu) := by
              rw [integral_const_mul]
        _ = c i ^ 2 * v i := by rw [hdiag i hi]

/-! Promoted from Staging/integral_pi_norm_sq_matrix_mulVec_eq_sum_row_sq_mul_of_cross_zero.lean. -/


open MeasureTheory
open scoped BigOperators InnerProductSpace

-- Generalization plan (G0):
-- concept/name: exact output energy of a finite matrix transform of orthogonal
--   scalar random coordinates; orig was
--   quadraticRestrictedNoiseInnovationCoord_secondMoment_eq_coeffSum
-- generality used: arbitrary measurable sample type and measure, finite input and
--   output index types, a real coefficient matrix, coordinatewise measurability
--   and square integrability, zero off-diagonal cross integrals, and prescribed
--   coordinate second moments
-- portable call pattern: stochastic linear-system, consensus, and distributed-
--   optimization proofs can change the input/output indices, coefficient matrix,
--   scalar noise family, and diagonal variance profile while reusing the same
--   exact matrix-output second-moment identity
-- counterargument checked: not paper-local traceability or a pure wrapper; the
--   existing weighted-sum covariance theorem treats one output row, whereas this
--   result packages the matrix transform, output-coordinate energy, and required
--   integral/sum interchange used by finite-dimensional stochastic systems
-- coverage search: queried `integral pi norm squared matrix mulVec equals sum row
--   squared coefficients cross integrals zero` and `finite matrix transform
--   centered orthogonal equal variance noise second moment`; the closest SOptLib
--   result was `integral_norm_sq_finset_weighted_sum_eq_sum_sq_mul_of_cross_zero`
--   for one weighted sum, while Mathlib's `covarianceBilin_apply_pi` gives a
--   covariance-form expansion under a finite measure rather than this energy identity
-- minimal hypotheses: arbitrary measure rather than probability measure; no
--   centering, independence, completeness, or finite-dimensionality assumptions;
--   all remaining hypotheses are consumed rowwise by covariance diagonalization

/-- The integrated finite-product energy of a matrix transform is the sum of
the squared matrix coefficients times the input coordinate second moments when
all off-diagonal cross integrals vanish.

Layer: Glue | Gap: Level 1 (finite matrix-transform covariance diagonalization)
Proof: apply the exact weighted-sum second-moment identity to every matrix row, then commute the finite output-coordinate energy sum with the Bochner integral.
Source: SOptLib weighted finite covariance diagonalization, Mathlib `Matrix.mulVec`, finite dependent-product energy, and Bochner integral finite-sum linearity
Used in: stochastic linear-system and distributed consensus proofs computing the exact output energy of a deterministic matrix acting on orthogonal coordinate noise
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/14/proof/0
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem integral_pi_norm_sq_matrix_mulVec_eq_sum_row_sq_mul_of_cross_zero
    {Omega I J : Type*} [MeasurableSpace Omega] [Fintype I] [Fintype J]
    (mu : Measure Omega) (A : Matrix I J Real)
    (Z : J -> Omega -> Real) (v : J -> Real)
    (hmeas : forall j, AEStronglyMeasurable (Z j) mu)
    (hL2 : forall j, Integrable (fun omega => ‖Z j omega‖ ^ 2) mu)
    (hcross : forall j k, j ≠ k ->
      (∫ omega, ⟪Z j omega, Z k omega⟫_Real ∂mu) = 0)
    (hdiag : forall j, (∫ omega, ‖Z j omega‖ ^ 2 ∂mu) = v j) :
    (∫ omega, SOptLib.dependentProductNormSq
      (A.mulVec (fun j => Z j omega)) ∂mu) =
      Finset.sum Finset.univ (fun i =>
        Finset.sum Finset.univ (fun j => A i j ^ 2 * v j)) := by
  classical
  have hrow (i : I) :
      (∫ omega, ‖A.mulVec (fun j => Z j omega) i‖ ^ 2 ∂mu) =
        Finset.sum Finset.univ (fun j => A i j ^ 2 * v j) := by
    simpa only [Matrix.mulVec, Real.norm_eq_abs, sq_abs, smul_eq_mul] using
      (integral_norm_sq_finset_weighted_sum_eq_sum_sq_mul_of_cross_zero
        mu Finset.univ (A i) Z v
        (fun j _ => hmeas j) (fun j _ => hL2 j)
        (fun j _ k _ hjk => by
          simpa only [real_inner_comm] using hcross j k hjk)
        (fun j _ => hdiag j))
  have hrow_integrable (i : I) :
      Integrable (fun omega => ‖A.mulVec (fun j => Z j omega) i‖ ^ 2) mu := by
    have hmem : MemLp (fun omega => A.mulVec (fun j => Z j omega) i) 2 mu := by
      simp only [Matrix.mulVec]
      apply memLp_finset_sum Finset.univ
      intro j _
      exact ((memLp_two_iff_integrable_sq_norm (hmeas j)).2 (hL2 j)).const_smul (A i j)
    exact (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).1 hmem
  simp only [SOptLib.dependentProductNormSq_def]
  rw [integral_finset_sum Finset.univ (fun i _ => hrow_integrable i)]
  exact Finset.sum_congr rfl (fun i _ => hrow i)

/-! Promoted from Staging/integral_norm_sq_finset_sum_smul_le_of_cross_zero.lean. -/


open MeasureTheory
open scoped BigOperators InnerProductSpace

-- Generalization plan (G0):
-- concept/name: second-moment bound for a deterministically weighted finite
--   orthogonal sum; orig was sameTime_weightedNoise_secondMoment_le
-- generality used: arbitrary measurable sample type, arbitrary measure, finite
--   index set, real Hilbert-valued coordinates, deterministic real weights,
--   square integrability, pairwise zero cross integrals, and a common upper
--   bound on coordinate second moments
-- portable call pattern: distributed-noise, mini-batch, and randomized-block
--   proofs can change the finite index set, Hilbert random family, deterministic
--   weights, and common moment budget while reusing the same sharp aggregate bound
-- counterargument checked: not paper-local traceability or a pure wrapper; the
--   exact weighted covariance theorem requires prescribed diagonal moments,
--   whereas this theorem packages the recurring monotone passage from component
--   moment bounds to a coefficient-sum bound
-- coverage search: queried `integral squared norm deterministic weighted finite
--   sum bounded by sum squared weights common second moment cross inner integral
--   zero`, `finite weighted Hilbert random variables pairwise orthogonal second
--   moment upper bound`, and the precise sum-smul shape; SOptLib's
--   `integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero` is unweighted,
--   this round's `integral_norm_sq_finset_weighted_sum_eq_sum_sq_mul_of_cross_zero`
--   assumes exact diagonal moments, and Mathlib's `OrthogonalFamily.norm_sum` is
--   pointwise rather than an integral bound
-- minimal hypotheses: arbitrary measure rather than probability measure; a
--   Finset rather than a Fintype; no centering, independence, completeness,
--   finite-dimensionality, or nonnegativity assumption on the common budget

/-- The second moment of a deterministically weighted finite sum is at most the
sum of squared weights times a common component second-moment bound when all
off-diagonal cross integrals vanish.

Layer: Glue | Gap: Level 1 (weighted finite Hilbert covariance bound from uniform diagonal control)
Proof: use weighted finite covariance diagonalization with the actual component moments, then bound each diagonal term by the common budget using nonnegativity of squared coefficients.
Source: SOptLib weighted finite Hilbert covariance diagonalization and Mathlib finite-sum order APIs
Used in: distributed stochastic-gradient, mini-batch, and randomized-block proofs bounding a deterministic weighted aggregate of pairwise orthogonal noise coordinates
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/6
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem integral_norm_sq_finset_sum_smul_le_of_cross_zero
    {Omega E I : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [InnerProductSpace Real E]
    [DecidableEq I] (mu : Measure Omega) (s : Finset I)
    (w : I -> Real) (xi : I -> Omega -> E) (sigma2 : Real)
    (hmeas : ∀ i ∈ s, AEStronglyMeasurable (xi i) mu)
    (hL2 : ∀ i ∈ s, Integrable (fun omega => ‖xi i omega‖ ^ 2) mu)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j ->
      (∫ omega, ⟪xi i omega, xi j omega⟫_Real ∂mu) = 0)
    (hdiag : ∀ i ∈ s, (∫ omega, ‖xi i omega‖ ^ 2 ∂mu) ≤ sigma2) :
    (∫ omega, ‖Finset.sum s (fun i => w i • xi i omega)‖ ^ 2 ∂mu) ≤
      Finset.sum s (fun i => w i ^ 2) * sigma2 := by
  rw [integral_norm_sq_finset_weighted_sum_eq_sum_sq_mul_of_cross_zero
    mu s w xi (fun i => ∫ omega, ‖xi i omega‖ ^ 2 ∂mu)
    hmeas hL2 hcross (fun _ _ => rfl)]
  calc
    Finset.sum s (fun i => w i ^ 2 * ∫ omega, ‖xi i omega‖ ^ 2 ∂mu) ≤
        Finset.sum s (fun i => w i ^ 2 * sigma2) := by
      exact Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_left (hdiag i hi) (sq_nonneg (w i))
    _ = Finset.sum s (fun i => w i ^ 2) * sigma2 := by
      rw [Finset.sum_mul]

/-! Promoted from Staging/integral_scalar_mul_finset_weighted_sum_eq_zero_of_condExp_eq_zero.lean. -/


open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace

-- Generalization plan (G0):
-- concept/name: integral cancellation for an adapted scalar multiplying a
--   deterministic weighted finite sum of conditionally centered variables;
--   orig was `strictPast_scalar_weightedNoise_integral_eq_zero`.
-- generality used: arbitrary sample and index types, arbitrary measure and
--   sub-sigma-algebra, a finite index set, real weights, and real L2 random
--   variables; no probability, oracle, filtration, or finite-dimensional assumptions.
-- portable call pattern: stochastic-gradient, distributed-consensus, mini-batch,
--   and coordinate algorithms cancel a predictable L2 scalar against a finite
--   deterministic weighting of same-time coordinatewise martingale differences;
--   the index set, weights, filtration, multiplier, and noise family may all vary.
-- counterargument checked: this is not paper-local traceability or a pure rename;
--   it composes coordinate conditional-expectation pullout, L2 product
--   integrability, and finite weighted integral cancellation in one callable step.
-- coverage search: searched `integral scalar times finite weighted sum equals zero
--   from coordinate conditional expectation zero adapted measurable L2` and
--   `integral finite sum deterministic scalar weights zero coordinate integrals`;
--   `integral_inner_sub_const_eq_zero_of_condExp_eq_zero` covers one coordinate,
--   `integral_finset_sum_const_mul_eq_zero` covers aggregation after coordinate
--   integrals are known, and `condExp_finset_sum_eq_zero_of_filtration_mono` covers
--   centering of a sum but not its product with an adapted L2 multiplier.
-- minimal hypotheses: probability normalization and full filtration structure
--   were dropped; coordinate integrability is stated pointwise because L2 does
--   not imply L1 for an arbitrary measure, while trim sigma-finiteness, adapted
--   measurability, and L2 membership drive the remaining steps.

/-- An adapted square-integrable scalar has zero integral against a deterministic
weighted finite sum of coordinatewise conditionally centered L2 variables.

Layer: Glue | Gap: Level 1 (finite weighted martingale-transform cancellation)
Proof: apply conditional-expectation pullout and zero-integral cancellation to
  every coordinate, obtain product integrability from Holder's inequality for L2
  functions, then commute the finite deterministic weighted sum with the integral.
Source: Mathlib conditional-expectation pullout and `MemLp.integrable_mul` APIs;
  SOptLib scalar martingale cancellation and finite integral aggregation lemmas
Used in: fresh-noise orthogonality for a strict-past scalar component of a
  distributed stochastic push-pull iterate, before deriving a variance lower bound
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/16/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed
  Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem integral_scalar_mul_finset_weighted_sum_eq_zero_of_condExp_eq_zero
    {Omega iota : Type*} {m0 : MeasurableSpace Omega}
    {mu : @Measure Omega m0} {m : MeasurableSpace Omega}
    (hm : m <= m0) [SigmaFinite (mu.trim hm)]
    (s : Finset iota) (w : iota -> Real) (A : Omega -> Real)
    (Z : iota -> Omega -> Real)
    (hA_meas : Measurable[m] A)
    (hA_mem : MemLp A 2 mu)
    (hZ_cond : ∀ i ∈ s, mu[Z i | m] =ᵐ[mu] 0)
    (hZ_int : ∀ i ∈ s, Integrable (Z i) mu)
    (hZ_mem : ∀ i ∈ s, MemLp (Z i) 2 mu) :
    (∫ omega, A omega * (∑ i ∈ s, w i * Z i omega) ∂mu) = 0 := by
  classical
  have hprod_int (i : iota) (hi : i ∈ s) :
      Integrable (fun omega => A omega * Z i omega) mu := by
    have hprod : Integrable (fun omega => ‖A omega‖ * ‖Z i omega‖) mu := by
      simpa [Pi.mul_apply] using
        (MemLp.integrable_mul hA_mem.norm (hZ_mem i hi).norm :
          Integrable ((fun omega => ‖A omega‖) * (fun omega => ‖Z i omega‖)) mu)
    exact hprod.mono'
      (hA_mem.aestronglyMeasurable.mul (hZ_mem i hi).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun omega => by simp [norm_mul])
  have hcoord_zero (i : iota) (hi : i ∈ s) :
      (∫ omega, A omega * Z i omega ∂mu) = 0 := by
    have hinner_int :
        Integrable (fun omega => ⟪Z i omega, A omega - (0 : Real)⟫_Real) mu := by
      have hinner_eq :
          (fun omega => ⟪Z i omega, A omega - (0 : Real)⟫_Real) =
            fun omega => A omega * Z i omega := by
        funext omega
        simp only [sub_zero]
        change RCLike.re (A omega * star (Z i omega)) = A omega * Z i omega
        simp
      rw [hinner_eq]
      exact hprod_int i hi
    have hzero := integral_inner_sub_const_eq_zero_of_condExp_eq_zero
      (P := mu) (m := m) hm hA_meas (hZ_cond i hi)
      (hZ_int i hi) hinner_int
    simpa using hzero
  have hfun :
      (fun omega => A omega * (∑ i ∈ s, w i * Z i omega)) =
        fun omega => ∑ i ∈ s, w i * (A omega * Z i omega) := by
    funext omega
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [hfun]
  exact @integral_finset_sum_const_mul_eq_zero Omega iota m0 mu s w
    (fun i omega => A omega * Z i omega) hprod_int hcoord_zero



open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

-- Generalization plan (G0):
-- concept/name: zero cross-inner-product integral from conditional event
--   transfer and centered weights; orig was
--   inner_integral_eq_zero_of_conditional_event_transfer
-- generality used: arbitrary measurable source, real Hilbert target with
--   measurable open sets, arbitrary finite measure, a sub-sigma-algebra,
--   measurable random vectors, local adaptedness of the first factor, and only
--   the stated Bochner integrability and event-transfer/centering hypotheses
-- portable call pattern: martingale and dependent-noise covariance proofs vary
--   the random vectors, conditioning sigma-algebra, finite law, and transferred
--   event weights while concluding that the same cross moment vanishes
-- counterargument checked: this is not paper-local traceability or a one-line
--   wrapper; it composes a scalar conditional-event transfer, a Bochner
--   separation argument, and conditional inner-product cancellation into a
--   reusable monotone-class bridge not already present in Mathlib or SOptLib
-- coverage search: searches for `inner product integral zero conditional event
--   transfer centered measurable preimage` and `set integral preimage equality
--   conditional expectation comap` found the partial components
--   condExp_comap_eq_of_preimage_setIntegral_eq,
--   integral_inner_sub_const_eq_zero_of_condExp_eq_zero, integral_inner, and
--   integral_eq_zero_of_forall_integral_inner_eq_zero, but no declaration with
--   the combined event-transfer and past-centering contract
-- minimal hypotheses: the source probability assumption was weakened to
--   IsFiniteMeasure, which is exactly what bounded event indicators require;
--   all measurability, integrability, adaptedness, event-transfer, and
--   centered-weight hypotheses are used

/-- Conditional event transfer and centered conditional weights force the
cross-inner-product integral of two Hilbert-valued random variables to vanish.

For each event generated by `X`, the transfer hypothesis identifies its scalar
indicator with a `past`-conditional weight on every event generated by `Y`.
If those weights have zero integral against every scalar projection of `Y`,
then `Y` has zero conditional mean given `X`, so its cross moment with `X`
vanishes.

Layer: Glue | Gap: Level 1 (conditional-event transfer to zero cross moment)
Proof: use generated-sigma-algebra conditional-expectation uniqueness to transfer each event indicator, scalarize the resulting Bochner set integrals to prove that the conditional mean of `Y` given `X` is zero, and apply adapted inner-product cancellation.
Source: Mathlib conditional expectation pull-out, Bochner set-integral, continuous linear map, and measurable-space comap APIs
Used in: dependent-noise and cross-node covariance arguments that turn conditional event factorization and past-centered weights into cancellation of an off-diagonal Hilbert cross moment
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/6
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem integral_inner_eq_zero_of_conditional_event_transfer
    {Omega F : Type*} [mOmega : MeasurableSpace Omega]
    [NormedAddCommGroup F] [InnerProductSpace Real F] [CompleteSpace F]
    [MeasurableSpace F] [OpensMeasurableSpace F]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (past : MeasurableSpace Omega) (hm : past ≤ mOmega)
    (X Y : Omega → F) (hX_meas : @Measurable Omega F mOmega _ X)
    (hX_aesm : AEStronglyMeasurable[MeasurableSpace.comap X inferInstance] X mu)
    (hY_meas : @Measurable Omega F mOmega _ Y)
    (hY_int : Integrable Y mu)
    (hinner_int : Integrable (fun omega => ⟪X omega, Y omega⟫_Real) mu)
    (hweightedEvent : ∀ B : Set F, MeasurableSet B →
      ∀ C : Set F, MeasurableSet C →
        (∫ omega in Y ⁻¹' C,
          (X ⁻¹' B).indicator (fun _ => (1 : Real)) omega ∂mu) =
        ∫ omega in Y ⁻¹' C,
          condExp past mu ((X ⁻¹' B).indicator (fun _ => (1 : Real))) omega ∂mu)
    (hpastCentered : ∀ B : Set F, MeasurableSet B → ∀ v : F,
      (∫ omega,
        condExp past mu ((X ⁻¹' B).indicator (fun _ => (1 : Real))) omega *
          ⟪v, Y omega⟫_Real ∂mu) = 0) :
    (∫ omega, ⟪X omega, Y omega⟫_Real ∂mu) = 0 := by
  letI : MeasurableSpace Omega := mOmega
  have hsetIntegral_Y_zero (B : Set F) (hB : MeasurableSet B) :
      (∫ omega in X ⁻¹' B, Y omega ∂mu) = 0 := by
    let I : Omega → Real := (X ⁻¹' B).indicator (fun _ => (1 : Real))
    let p : Omega → Real := condExp past mu I
    have hmY : MeasurableSpace.comap Y inferInstance ≤ mOmega := hY_meas.comap_le
    letI : @SigmaFinite Omega (MeasurableSpace.comap Y inferInstance) (mu.trim hmY) :=
      by infer_instance
    have hI_int : Integrable I mu := by
      refine integrable_of_measurable_bounded_real ?_ (C := 1) ?_
      · exact measurable_const.indicator (hB.preimage hX_meas)
      · intro omega
        by_cases homega : X omega ∈ B <;> simp [I, homega]
    have hp_int : Integrable p mu := MeasureTheory.integrable_condExp
    have hp_nonneg : 0 ≤ᵐ[mu] p := by
      apply MeasureTheory.condExp_nonneg
      filter_upwards with omega
      by_cases homega : X omega ∈ B <;> simp [I, homega]
    have hp_le_one : p ≤ᵐ[mu] fun _ : Omega => (1 : Real) := by
      have hmono := MeasureTheory.condExp_mono
        (m := past) hI_int (integrable_const 1) (by
          filter_upwards with omega
          by_cases homega : X omega ∈ B <;> simp [I, homega])
      simpa [p, MeasureTheory.condExp_const hm] using hmono
    have hp_norm : ∀ᵐ omega ∂mu, ‖p omega‖ ≤ 1 := by
      filter_upwards [hp_nonneg, hp_le_one] with omega hnonneg hle
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
    have hce : condExp (MeasurableSpace.comap Y inferInstance) mu I =ᵐ[mu]
        condExp (MeasurableSpace.comap Y inferInstance) mu p := by
      apply condExp_comap_eq_of_preimage_setIntegral_eq
        mu Y hY_meas I p hI_int hp_int
      intro C hC
      simpa [I, p] using hweightedEvent B hB C hC
    have hscalar_zero (v : F) :
        (∫ omega, I omega * ⟪v, Y omega⟫_Real ∂mu) = 0 := by
      let q : Omega → Real := fun omega => ⟪v, Y omega⟫_Real
      have hq_int : Integrable q mu :=
        ContinuousLinearMap.integrable_comp (L := innerSL Real v) hY_int
      have hq_mY : Measurable[MeasurableSpace.comap Y inferInstance] q :=
        (innerSL Real v).continuous.measurable.comp (comap_measurable Y)
      have hIq_int : Integrable (fun omega => I omega * q omega) mu := by
        apply hq_int.bdd_mul (c := 1) hI_int.aestronglyMeasurable
        filter_upwards with omega
        by_cases homega : X omega ∈ B <;> simp [I, homega]
      have hpq_int : Integrable (fun omega => p omega * q omega) mu :=
        hq_int.bdd_mul (c := 1) hp_int.aestronglyMeasurable hp_norm
      have hIp_ce := MeasureTheory.condExp_mul_of_aestronglyMeasurable_right
        hq_mY.aestronglyMeasurable hIq_int hI_int
      have hpp_ce := MeasureTheory.condExp_mul_of_aestronglyMeasurable_right
        hq_mY.aestronglyMeasurable hpq_int hp_int
      have hproducts :
          condExp (MeasurableSpace.comap Y inferInstance) mu
              (fun omega => I omega * q omega) =ᵐ[mu]
            condExp (MeasurableSpace.comap Y inferInstance) mu
              (fun omega => p omega * q omega) := by
        refine hIp_ce.trans ?_
        refine (hce.mul (Filter.EventuallyEq.rfl)).trans ?_
        exact hpp_ce.symm
      have hintegral :
          (∫ omega, I omega * q omega ∂mu) = ∫ omega, p omega * q omega ∂mu :=
        (MeasureTheory.integral_condExp hmY).symm.trans
          ((integral_congr_ae hproducts).trans (MeasureTheory.integral_condExp hmY))
      calc
        (∫ omega, I omega * ⟪v, Y omega⟫_Real ∂mu) =
            ∫ omega, I omega * q omega ∂mu := by rfl
        _ = ∫ omega, p omega * q omega ∂mu := hintegral
        _ = 0 := by simpa [p, q] using hpastCentered B hB v
    have hpre_meas : MeasurableSet (X ⁻¹' B) := hB.preimage hX_meas
    have hscalar_set_zero (v : F) :
        (∫ omega in X ⁻¹' B, ⟪v, Y omega⟫_Real ∂mu) = 0 := by
      calc
        (∫ omega in X ⁻¹' B, ⟪v, Y omega⟫_Real ∂mu) =
            ∫ omega, I omega * ⟪v, Y omega⟫_Real ∂mu := by
          rw [← MeasureTheory.integral_indicator hpre_meas]
          apply integral_congr_ae
          filter_upwards with omega
          by_cases homega : X omega ∈ B <;>
            simp [I, Set.indicator, homega]
        _ = 0 := hscalar_zero v
    let z : F := ∫ omega in X ⁻¹' B, Y omega ∂mu
    have hz_inner (v : F) : ⟪v, z⟫_Real = 0 := by
      have hY_on : Integrable Y (mu.restrict (X ⁻¹' B)) := hY_int.integrableOn
      have hcomm := (innerSL Real v).integral_comp_comm hY_on
      change ⟪v, ∫ omega in X ⁻¹' B, Y omega ∂mu⟫_Real = 0
      calc
        ⟪v, ∫ omega in X ⁻¹' B, Y omega ∂mu⟫_Real =
            ∫ omega in X ⁻¹' B, ⟪v, Y omega⟫_Real ∂mu := by
          simpa only [innerSL_apply_apply] using hcomm.symm
        _ = 0 := hscalar_set_zero v
    have hz_norm_sq : ‖z‖ ^ 2 = 0 := by
      simpa [real_inner_self_eq_norm_sq] using hz_inner z
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz_norm_sq)
  have hmX : MeasurableSpace.comap X inferInstance ≤ mOmega := hX_meas.comap_le
  letI : @SigmaFinite Omega (MeasurableSpace.comap X inferInstance) (mu.trim hmX) :=
    by infer_instance
  have hY_ce : condExp (MeasurableSpace.comap X inferInstance) mu Y =ᵐ[mu]
      fun _ => (0 : F) := by
    have hraw := condExp_comap_eq_of_preimage_setIntegral_eq
      mu X hX_meas Y (fun _ : Omega => (0 : F)) hY_int
        (integrable_zero Omega F mu) (by
          intro B hB
          simpa using hsetIntegral_Y_zero B hB)
    have hzero_fun : (fun _ : Omega => (0 : F)) = (0 : Omega → F) := rfl
    rw [hzero_fun, MeasureTheory.condExp_zero] at hraw
    exact hraw
  have hYX_int : Integrable (fun omega => ⟪Y omega, X omega⟫_Real) mu := by
    simpa [real_inner_comm] using hinner_int
  have hcancel := expectation_inner_eq_of_condExp_eq_and_aestronglyMeasurable_right
    (μ := mu) (m := MeasurableSpace.comap X inferInstance)
    (Y := Y) (T := fun _ => (0 : F)) (U := X) hmX
    hX_aesm hYX_int hY_int hY_ce
  simpa using hcancel



open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

-- Generalization plan (G0):
-- concept/name: off-diagonal Hilbert orthogonality from conditional
--   factorization of finite measurable cylinders and conditional centering;
--   orig was
--   sameTime_distinctNode_inner_integral_eq_zero
-- generality used: arbitrary finite index type, measurable source, arbitrary
--   finite measure and sub-sigma-algebra, and a complete second-countable real
--   Hilbert target whose open sets are measurable;
--   no probability, finite-dimensional, filtration, oracle, node, or algorithm
--   assumptions
-- portable call pattern: stochastic approximation, distributed optimization,
--   and dependent-noise proofs vary the two Hilbert-valued random variables,
--   their finite law, and conditioning sigma-algebra while retaining rectangle
--   indicator factorization and conditional centering of the second variable
--   to cancel the same off-diagonal cross moment
-- counterargument checked: this is not paper-local traceability or a one-line
--   wrapper; it derives the conditional event-transfer and centered-weight
--   hypotheses needed by the existing monotone-class bridge. Mathlib's
--   CondIndepFun requires a standard Borel source, and its covariance-zero API
--   is scalar and unconditional, so neither covers this contract
-- coverage search: queried `conditional expectation indicator rectangle
--   factorization centered Hilbert inner product integral equals zero`,
--   `condExp product indicators factorization cross covariance zero`, and
--   `conditionally independent centered Hilbert random variables`; closest
--   partial hits were integral_inner_eq_zero_of_conditional_event_transfer,
--   integral_eq_of_condExp_ae_eq, MeasureTheory conditional-expectation
--   pull-out lemmas, ProbabilityTheory.CondIndepFun, and the scalar theorem
--   ProbabilityTheory.IndepFun.covariance_eq_zero
-- minimal hypotheses: probability was weakened to finite measure; full L2 and
--   finite-dimensional hypotheses were replaced by integrability of Y and of
--   the displayed inner product; measurability, rectangle factorization, and
--   conditional centering are exactly the remaining inputs

/-- Conditional factorization of measurable rectangle indicators and
conditional centering force a Hilbert-valued cross-inner-product integral to
vanish.

The factorization hypothesis is an event-level form of conditional
independence. It transfers each event generated by `X` to its conditional
weight against events generated by `Y`; conditional centering of `Y` then
cancels every scalar projection of that weighted variable.

Layer: Glue | Gap: Level 1 (conditional rectangle factorization to zero Hilbert cross moment)
Proof: derive conditional event transfer by integrating the rectangle factorization and derive centered conditional weights by the conditional-expectation scalar pull-out formula, then apply the generated-sigma-algebra monotone-class bridge.
Source: Mathlib conditional-expectation pull-out, indicator integration, Bochner integral, and measurable-space comap APIs
Used in: distributed and mini-batch stochastic methods where distinct same-time noise coordinates factor conditionally on the past and one coordinate is conditionally centered
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/6
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
private theorem integral_inner_eq_zero_of_condExp_pair_indicator_factorization_of_condExp_eq_zero
    {Omega F : Type*} [mOmega : MeasurableSpace Omega]
    [NormedAddCommGroup F] [InnerProductSpace Real F] [CompleteSpace F]
    [MeasurableSpace F] [OpensMeasurableSpace F] [SecondCountableTopology F]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (past : MeasurableSpace Omega) (hm : past ≤ mOmega)
    (X Y : Omega → F)
    (hX_meas : @Measurable Omega F mOmega _ X)
    (hY_meas : @Measurable Omega F mOmega _ Y)
    (hfactor : ∀ B : Set F, MeasurableSet B →
      ∀ C : Set F, MeasurableSet C →
        condExp past mu (fun omega =>
            (X ⁻¹' B).indicator (fun _ => (1 : Real)) omega *
              (Y ⁻¹' C).indicator (fun _ => (1 : Real)) omega) =ᵐ[mu]
          fun omega =>
            condExp past mu
                ((X ⁻¹' B).indicator (fun _ => (1 : Real))) omega *
              condExp past mu
                ((Y ⁻¹' C).indicator (fun _ => (1 : Real))) omega)
    (hY_condExp : condExp past mu Y =ᵐ[mu] fun _ => (0 : F))
    (hY_int : Integrable Y mu)
    (hinner_int : Integrable (fun omega => ⟪X omega, Y omega⟫_Real) mu) :
    (∫ omega, ⟪X omega, Y omega⟫_Real ∂mu) = 0 := by
  letI : MeasurableSpace Omega := mOmega
  have hweightedEvent (B : Set F) (hB : MeasurableSet B) :
      ∀ C : Set F, MeasurableSet C →
        (∫ omega in Y ⁻¹' C,
          (X ⁻¹' B).indicator (fun _ => (1 : Real)) omega ∂mu) =
        ∫ omega in Y ⁻¹' C,
          condExp past mu
            ((X ⁻¹' B).indicator (fun _ => (1 : Real))) omega ∂mu := by
    let I : Omega → Real := (X ⁻¹' B).indicator (fun _ => (1 : Real))
    let p : Omega → Real := condExp past mu I
    have hI_int : Integrable I mu := by
      refine integrable_of_measurable_bounded_real ?_ (C := 1) ?_
      · exact measurable_const.indicator (hB.preimage hX_meas)
      · intro omega
        by_cases homega : X omega ∈ B <;> simp [I, homega]
    have hp_int : Integrable p mu := MeasureTheory.integrable_condExp
    have hp_aesm : AEStronglyMeasurable[past] p mu :=
      MeasureTheory.stronglyMeasurable_condExp.aestronglyMeasurable
    intro C hC
    let J : Omega → Real := (Y ⁻¹' C).indicator (fun _ => (1 : Real))
    have hJ_int : Integrable J mu := by
      refine integrable_of_measurable_bounded_real ?_ (C := 1) ?_
      · exact measurable_const.indicator (hC.preimage hY_meas)
      · intro omega
        by_cases homega : Y omega ∈ C <;> simp [J, homega]
    have hIJ_int : Integrable (fun omega => I omega * J omega) mu := by
      apply hJ_int.bdd_mul (c := 1) hI_int.aestronglyMeasurable
      filter_upwards with omega
      by_cases homega : X omega ∈ B <;> simp [I, homega]
    have hpJ_int : Integrable (fun omega => p omega * J omega) mu := by
      apply hp_int.mul_bdd (c := 1) hJ_int.aestronglyMeasurable
      filter_upwards with omega
      by_cases homega : Y omega ∈ C <;> simp [J, homega]
    have hleft : (∫ omega, I omega * J omega ∂mu) =
        ∫ omega, p omega * condExp past mu J omega ∂mu := by
      exact integral_eq_of_condExp_ae_eq hm (hfactor B hB C hC)
    have hpull := MeasureTheory.condExp_mul_of_aestronglyMeasurable_left
      hp_aesm hpJ_int hJ_int
    have hright : (∫ omega, p omega * J omega ∂mu) =
        ∫ omega, p omega * condExp past mu J omega ∂mu := by
      exact integral_eq_of_condExp_ae_eq hm hpull
    have hprod_eq : (∫ omega, I omega * J omega ∂mu) =
        ∫ omega, p omega * J omega ∂mu := hleft.trans hright.symm
    have hpre : MeasurableSet (Y ⁻¹' C) := hC.preimage hY_meas
    calc
      (∫ omega in Y ⁻¹' C, I omega ∂mu) =
          ∫ omega, I omega * J omega ∂mu := by
        rw [← MeasureTheory.integral_indicator hpre]
        apply integral_congr_ae
        filter_upwards with omega
        by_cases homega : Y omega ∈ C <;>
          simp [J, Set.indicator, homega]
      _ = ∫ omega, p omega * J omega ∂mu := hprod_eq
      _ = ∫ omega in Y ⁻¹' C, p omega ∂mu := by
        rw [← MeasureTheory.integral_indicator hpre]
        apply integral_congr_ae
        filter_upwards with omega
        by_cases homega : Y omega ∈ C <;>
          simp [J, Set.indicator, homega]
  have hpastCentered (B : Set F) (hB : MeasurableSet B) (v : F) :
      (∫ omega,
        condExp past mu
            ((X ⁻¹' B).indicator (fun _ => (1 : Real))) omega *
          ⟪v, Y omega⟫_Real ∂mu) = 0 := by
    let I : Omega → Real := (X ⁻¹' B).indicator (fun _ => (1 : Real))
    let p : Omega → Real := condExp past mu I
    have hI_int : Integrable I mu := by
      refine integrable_of_measurable_bounded_real ?_ (C := 1) ?_
      · exact measurable_const.indicator (hB.preimage hX_meas)
      · intro omega
        by_cases homega : X omega ∈ B <;> simp [I, homega]
    have hp_int : Integrable p mu := MeasureTheory.integrable_condExp
    have hp_past : AEStronglyMeasurable[past] p mu :=
      MeasureTheory.stronglyMeasurable_condExp.aestronglyMeasurable
    have hp_nonneg : 0 ≤ᵐ[mu] p := by
      apply MeasureTheory.condExp_nonneg
      filter_upwards with omega
      by_cases homega : X omega ∈ B <;> simp [I, homega]
    have hp_le_one : p ≤ᵐ[mu] fun _ : Omega => (1 : Real) := by
      have hmono := MeasureTheory.condExp_mono
        (m := past) hI_int (integrable_const 1) (by
          filter_upwards with omega
          by_cases homega : X omega ∈ B <;> simp [I, homega])
      simpa [p, MeasureTheory.condExp_const hm] using hmono
    have hp_norm : ∀ᵐ omega ∂mu, ‖p omega‖ ≤ 1 := by
      filter_upwards [hp_nonneg, hp_le_one] with omega hnonneg hle
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
    have hpY_int : Integrable (fun omega => p omega • Y omega) mu :=
      hY_int.bdd_smul 1 hp_int.aestronglyMeasurable hp_norm
    have hpull := MeasureTheory.condExp_smul_of_aestronglyMeasurable_left
      hp_past hpY_int hY_int
    have hpY_ce : condExp past mu (fun omega => p omega • Y omega) =ᵐ[mu]
        fun _ => (0 : F) := by
      refine hpull.trans ?_
      filter_upwards [hY_condExp] with omega homega
      simp [homega]
    have hpY_zero : (∫ omega, p omega • Y omega ∂mu) = 0 := by
      simpa using integral_eq_of_condExp_ae_eq hm hpY_ce
    calc
      (∫ omega,
        condExp past mu
            ((X ⁻¹' B).indicator (fun _ => (1 : Real))) omega *
          ⟪v, Y omega⟫_Real ∂mu) =
          ∫ omega, ⟪v, p omega • Y omega⟫_Real ∂mu := by
        apply integral_congr_ae
        filter_upwards with omega
        simp [I, p, real_inner_smul_right]
      _ = ⟪v, ∫ omega, p omega • Y omega ∂mu⟫_Real :=
        (innerSL Real v).integral_comp_comm hpY_int
      _ = 0 := by rw [hpY_zero, inner_zero_right]
  have hX_aesm :
      AEStronglyMeasurable[MeasurableSpace.comap X inferInstance] X mu :=
    (comap_measurable X).aestronglyMeasurable
  exact integral_inner_eq_zero_of_conditional_event_transfer
    mu past hm X Y hX_meas hX_aesm hY_meas hY_int hinner_int
      hweightedEvent hpastCentered

/-- Distinct coordinates of a finite conditionally factorized Hilbert-valued
family have zero cross-inner-product integral when the second coordinate is
conditionally centered.

The conditional factorization is stated for every measurable finite cylinder.
Only the two selected coordinates need measurability and `L²` control; the
remaining coordinates disappear after their events are specialized to the
whole space.

Layer: Glue | Gap: Level 1 (finite conditional factorization to off-diagonal Hilbert orthogonality)
Proof: specialize the finite-cylinder factorization to two measurable coordinate events and whole-space events elsewhere, collapse the remaining conditional indicators to one, derive pairwise rectangle factorization, and apply the pairwise conditional-centering bridge.
Source: Mathlib finite-product, conditional-expectation, measurable-indicator, Bochner integral, and Hilbert-space `L²` APIs
Used in: distributed, mini-batch, and multi-sample stochastic methods where a finite same-time noise family factorizes conditionally on the past and each selected noise coordinate is conditionally centered
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/6
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem integral_inner_eq_zero_of_condExp_indicator_factorization_of_condExp_eq_zero
    {Omega F Index : Type*} [mOmega : MeasurableSpace Omega] [Fintype Index]
    [NormedAddCommGroup F] [InnerProductSpace Real F] [CompleteSpace F]
    [MeasurableSpace F] [OpensMeasurableSpace F] [SecondCountableTopology F]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (past : MeasurableSpace Omega) (hm : past ≤ mOmega)
    (Z : Index → Omega → F)
    (hfactor : ∀ events : Index → Set F,
      (∀ k : Index, MeasurableSet (events k)) →
        condExp past mu
            ({omega | ∀ k : Index, Z k omega ∈ events k}.indicator
              (fun _ => (1 : Real))) =ᵐ[mu]
          fun omega => ∏ k : Index,
            condExp past mu
              ((Z k ⁻¹' events k).indicator (fun _ => (1 : Real))) omega)
    (i j : Index) (hij : i ≠ j)
    (hi_meas : @Measurable Omega F mOmega _ (Z i))
    (hj_meas : @Measurable Omega F mOmega _ (Z j))
    (hj_condExp : condExp past mu (Z j) =ᵐ[mu] fun _ => (0 : F))
    (hi_memLp : MemLp (Z i) 2 mu)
    (hj_memLp : MemLp (Z j) 2 mu) :
    (∫ omega, ⟪Z i omega, Z j omega⟫_Real ∂mu) = 0 := by
  classical
  have huniv (k : Index) :
      condExp past mu (fun _ : Omega => (1 : Real)) =
        fun _ : Omega => (1 : Real) :=
    MeasureTheory.condExp_const hm 1
  have hpair (B C : Set F) (hB : MeasurableSet B) (hC : MeasurableSet C) :
      condExp past mu (fun omega =>
          ((Z i) ⁻¹' B).indicator (fun _ => (1 : Real)) omega *
            ((Z j) ⁻¹' C).indicator (fun _ => (1 : Real)) omega) =ᵐ[mu]
        fun omega =>
          condExp past mu
              (((Z i) ⁻¹' B).indicator (fun _ => (1 : Real))) omega *
            condExp past mu
              (((Z j) ⁻¹' C).indicator (fun _ => (1 : Real))) omega := by
    let events : Index → Set F := fun k =>
      if k = i then B else if k = j then C else Set.univ
    have hfamily := hfactor events (by
      intro k
      by_cases hki : k = i
      · simp [events, hki, hB]
      · by_cases hkj : k = j
        · subst k
          simp [events, Ne.symm hij, hC]
        · simp [events, hki, hkj])
    have hji : j ≠ i := Ne.symm hij
    have hleft_fun :
        {omega | ∀ k : Index, Z k omega ∈ events k}.indicator
            (fun _ => (1 : Real)) =
          fun omega =>
            ((Z i) ⁻¹' B).indicator (fun _ => (1 : Real)) omega *
              ((Z j) ⁻¹' C).indicator (fun _ => (1 : Real)) omega := by
      funext omega
      by_cases hiB : Z i omega ∈ B
      · by_cases hjC : Z j omega ∈ C
        · have hall : ∀ k : Index, Z k omega ∈ events k := by
            intro k
            by_cases hki : k = i
            · subst k
              simpa [events] using hiB
            · by_cases hkj : k = j
              · subst k
                simpa [events, hji] using hjC
              · simp [events, hki, hkj]
          simp [hall, hiB, hjC, Set.indicator]
        · have hnot : ¬ ∀ k : Index, Z k omega ∈ events k := by
            intro hall
            have := hall j
            simp [events, hji] at this
            exact hjC this
          simp [hnot, hiB, hjC, Set.indicator]
      · have hnot : ¬ ∀ k : Index, Z k omega ∈ events k := by
          intro hall
          have := hall i
          simp [events] at this
          exact hiB this
        simp [hnot, hiB, Set.indicator]
    rw [hleft_fun] at hfamily
    refine hfamily.trans ?_
    filter_upwards with omega
    let f : Index → Real := fun k =>
      condExp past mu
        ((Z k ⁻¹' events k).indicator (fun _ => (1 : Real))) omega
    have hoff (k : Index) (hk : k ≠ i ∧ k ≠ j) : f k = 1 := by
      dsimp [f]
      rw [show ((Z k ⁻¹' events k).indicator (fun _ => (1 : Real))) =
          fun _ : Omega => (1 : Real) by
        funext omega
        simp [events, hk.1, hk.2, Set.indicator]]
      exact congrFun (huniv k) omega
    have hprod := Finset.prod_eq_mul_of_mem
      (s := (Finset.univ : Finset Index)) (f := f) i j
      (by simp) (by simp) hij (fun k _hk hk => hoff k hk)
    simpa [f, events, hij, hji, Set.indicator] using hprod
  have hinner_int :
      Integrable (fun omega => ⟪Z i omega, Z j omega⟫_Real) mu := by
    have hprod : Integrable (fun omega => ‖Z i omega‖ * ‖Z j omega‖) mu := by
      simpa [Pi.mul_apply] using
        (MeasureTheory.MemLp.integrable_mul hi_memLp.norm hj_memLp.norm :
          Integrable ((fun omega => ‖Z i omega‖) *
            (fun omega => ‖Z j omega‖)) mu)
    exact hprod.mono'
      (AEStronglyMeasurable.inner hi_memLp.aestronglyMeasurable
        hj_memLp.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun omega => by
        simpa [Real.norm_eq_abs] using
          abs_real_inner_le_norm (Z i omega) (Z j omega))
  have hj_int : Integrable (Z j) mu :=
    hj_memLp.integrable (by norm_num)
  exact
    integral_inner_eq_zero_of_condExp_pair_indicator_factorization_of_condExp_eq_zero
      (mOmega := mOmega) mu past hm (Z i) (Z j) hi_meas hj_meas
      (fun B hB C hC => hpair B C hB hC) hj_condExp hj_int hinner_int
