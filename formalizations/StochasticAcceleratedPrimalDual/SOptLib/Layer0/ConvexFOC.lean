import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Seminorm
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic
import SOptLib.Glue.Calculus
import SOptLib.Model.Bregman
import SOptLib.Model.Carrier
import SOptLib.Model.ConditionalGradient
import SOptLib.Model.Prox

open scoped InnerProductSpace

open scoped InnerProductSpace

/-- Derivative of a charted mirror-objective expression from derivatives of the chart
map and charted potential.

Layer: Layer0 | Gap: Level 1 (charted mirror-objective calculus)
Proof: combine the chain rule for the linear inner-product terms with the supplied
  derivative of the charted potential, then collect the resulting continuous linear maps.
Source: Mathlib Frechet derivative and inner-product calculus
Used in: stochastic mirror descent paper mirror objective first-order condition
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan stochastic mirror descent -/
theorem charted_mirrorObjective_hasFDerivWithinAt
    {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : Set H} {u₀ : H}
    (L : H → E) (L' : H →L[ℝ] E) (f : H → ℝ)
    (x g gradz gradx : E) (c γ : ℝ)
    (hLder : HasFDerivWithinAt L L' T u₀)
    (hfder : HasFDerivWithinAt f (((innerSL ℝ) gradz).comp L') T u₀) :
    HasFDerivWithinAt
      (fun u : H => γ * ⟪g, L u⟫_ℝ + (f u - c - ⟪gradx, L u - x⟫_ℝ))
      (((innerSL ℝ) (γ • g + gradz - gradx)).comp L') T u₀ := by
  have hgder :
      HasFDerivWithinAt (fun u : H => γ * ⟪g, L u⟫_ℝ)
        (γ • (((innerSL ℝ) g).comp L')) T u₀ := by
    have hinner :
        HasFDerivWithinAt (fun u : H => ⟪g, L u⟫_ℝ)
          (((innerSL ℝ) g).comp L') T u₀ := by
      simpa using ((innerSL ℝ g).hasFDerivAt.comp_hasFDerivWithinAt u₀ hLder)
    simpa using hinner.const_mul γ
  have hxder :
      HasFDerivWithinAt (fun u : H => ⟪gradx, L u - x⟫_ℝ)
        (((innerSL ℝ) gradx).comp L') T u₀ := by
    simpa using
      ((innerSL ℝ gradx).hasFDerivAt.comp_hasFDerivWithinAt u₀ (hLder.sub_const x))
  have hsum := hgder.add ((hfder.sub_const c).sub hxder)
  have hF :
      (γ • (((innerSL ℝ) g).comp L') +
          ((((innerSL ℝ) gradz).comp L') -
            (((innerSL ℝ) gradx).comp L'))) =
        ((innerSL ℝ) (γ • g + gradz - gradx)).comp L' := by
    ext du
    simp [ContinuousLinearMap.comp_apply]
    ring
  rw [← hF]
  convert hsum using 1

/-- The carrier-form charted mirror objective has the expected within derivative.

For a chart map `L`, a charted potential `f`, carrier evaluations `eval`, values `v`,
and gradients `grad`, the within Frechet derivative of the charted mirror objective
at `chart z` is the inner product with `γ • g + grad z - grad x` composed with `L'`.

Layer: Layer0 | Gap: Level 1 (charted mirror objective carrier derivative)
Proof: Rewrite the carrier data to the ambient charted mirror-objective derivative
  /-- The carrier-form charted mirror objective has the expected within derivative.

  For a chart map `L`, a charted potential `f`, carrier evaluations `eval`, values `v`,
  and gradients `grad`, the within Frechet derivative of the charted mirror objective
  at `chart z` is the inner product with `γ • g + grad z - grad x` composed with `L'`.

  Layer: Layer0 | Gap: Level 1 (charted mirror objective carrier derivative)
  Proof: Rewrite the carrier data to the ambient charted mirror-objective derivative
    /-- The carrier-form charted mirror objective has the expected within derivative.

    For a chart map `L`, a charted potential `f`, carrier evaluations `eval`, values `v`,
    and gradients `grad`, the within Frechet derivative at `chart z` is the inner
    product with `γ • g + grad z - grad x` composed with `L'`.

    Layer: Layer0 | Gap: Level 1 (charted mirror objective carrier derivative)
    Proof: Rewrite the carrier data to the ambient charted mirror-objective derivative
      theorem and close by `simpa`. The supporting calculus is linearity of within
      Frechet derivatives through inner-product and affine objective terms.
    Source: Mathlib Frechet derivative calculus for inner products and continuous linear maps
    Used in: stochastic mirror descent prox-step first-order condition in chart coordinates
    Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
    Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
      Machine Learning, stochastic mirror descent -/
    theorem and close by `simpa`. The supporting calculus is linearity of within
    Frechet derivatives through inner-product and affine objective terms.
  Source: Mathlib Frechet derivative calculus for inner products and continuous linear maps
  Used in: stochastic mirror descent prox-step first-order condition in chart coordinates
  Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
  Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
    Machine Learning, stochastic mirror descent -/
  theorem and close by `simpa`. The supporting calculus is linearity of within
  Frechet derivatives through inner-product and affine objective terms.
Source: Mathlib Frechet derivative calculus for inner products and continuous linear maps
Used in: stochastic mirror descent prox-step first-order condition in chart coordinates
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem carrier_charted_mirrorObjective_hasFDerivWithinAt
    {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {P : Type*} (T : Set H) (chart : P → H)
    (L : H → E) (L' : H →L[ℝ] E) (f : H → ℝ)
    (eval : P → E) (v : P → ℝ) (grad : P → E)
    (x z : P) (g : E) (γ : ℝ)
    (hLder : HasFDerivWithinAt L L' T (chart z))
    (hfder : HasFDerivWithinAt f (((innerSL ℝ) (grad z)).comp L') T (chart z)) :
    HasFDerivWithinAt
      (fun u : H => γ * ⟪g, L u⟫_ℝ + (f u - v x - ⟪grad x, L u - eval x⟫_ℝ))
      (((innerSL ℝ) (γ • g + grad z - grad x)).comp L') T (chart z) := by
  simpa using
    (charted_mirrorObjective_hasFDerivWithinAt
      (L := L) (L' := L') (f := f)
      (x := eval x) (g := g) (gradz := grad z) (gradx := grad x)
      (c := v x) (γ := γ) hLder hfder)

/-- An argmin of a mirror objective satisfies the variational inequality for a feasible
comparison point.

If `z` minimizes the paper objective, the charted objective `Φ` agrees with it on the
convex feasible coordinate set, and the Frechet derivative at `chart z` is represented
by the mirror gradient pairing after the coordinate-to-evaluation bridge, then every
feasible `y` satisfies `0 ≤ ⟪grad, eval y - eval z⟫_ℝ`.

Layer: Model | Gap: Level 1 (mirror-objective argmin variational inequality)
Proof: applies Mathlib's convex first-order necessary condition for a minimizer with
  `HasFDerivWithinAt`, then rewrites the continuous-linear derivative through the
  chart direction map into the stated inner-product form.
Source: Mathlib convex analysis and Frechet derivative APIs
Used in: stochastic mirror descent mirror prox-step optimality as a variational inequality
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem mirrorObjective_argmin_variational
    {H E P : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (objective : P → ℝ) (chart : P → H) (T : Set H)
    (pointOfChart : ∀ u : H, u ∈ T → P)
    (Φ : H → ℝ) (F' : H →L[ℝ] ℝ) (direction : H →L[ℝ] E) (grad : E)
    (eval : P → E) (z y : P)
    (hTconv : Convex ℝ T)
    (hz : chart z ∈ T) (hy : chart y ∈ T)
    (hpointOfChart : ∀ u (hu : u ∈ T), Φ u = objective (pointOfChart u hu))
    (hchart_z : Φ (chart z) = objective z)
    (hmin : ∀ p : P, objective z ≤ objective p)
    (hderiv : HasFDerivWithinAt Φ F' T (chart z))
    (hF' : F' = ((innerSL ℝ) grad).comp direction)
    (hcoord : direction (chart y - chart z) = eval y - eval z) :
    0 ≤ ⟪grad, eval y - eval z⟫_ℝ := by
  have hmin_chart : ∀ u ∈ T, Φ (chart z) ≤ Φ u := by
    intro u hu
    rw [hchart_z, hpointOfChart u hu]
    exact hmin (pointOfChart u hu)
  have hfoc : 0 ≤ F' (chart y - chart z) :=
    Convex.first_order_condition_of_isMinOn_hasFDerivWithinAt
      hTconv hz hy hmin_chart hderiv
  have hF_apply : F' (chart y - chart z) = ⟪grad, eval y - eval z⟫_ℝ := by
    rw [hF']
    simp [ContinuousLinearMap.comp_apply, hcoord]
  simpa [hF_apply] using hfoc

/-- A mirror-step minimizer inherits the paper-facing variational inequality.

An abstract `mirrorStep` whose output minimizes the local mirror objective satisfies
the variational inequality produced by the pointwise minimizer-to-FOC bridge.

Layer: Layer0 | Gap: Level 0 (mirror-step variational bridge)
Proof: apply the supplied pointwise variational bridge to `mirrorStep x g γ`,
  using the abstract minimizer hypothesis as the global minimality witness.
Source: Mathlib inner product space algebra and ordered real inequalities
Used in: stochastic mirror descent mirrorStep variational inequality with gradient extension
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
theorem mirrorStep_variational
    {P E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (mirrorStep : P → E → ℝ → P) (grad eval : P → E)
    (objective : P → E → ℝ → P → ℝ)
    (h_mirrorStep_minimizes :
      ∀ x : P, ∀ g : E, ∀ γ : ℝ, ∀ y : P,
        objective x g γ (mirrorStep x g γ) ≤ objective x g γ y)
    (h_variational :
      ∀ x : P, ∀ g : E, ∀ γ : ℝ, ∀ z y : P,
        (∀ u : P, objective x g γ z ≤ objective x g γ u) →
          0 ≤ ⟪γ • g + grad z - grad x, eval y - eval z⟫_ℝ) :
    ∀ x : P, ∀ g : E, ∀ γ : ℝ, ∀ y : P,
      0 ≤
        ⟪γ • g + grad (mirrorStep x g γ) - grad x,
          eval y - eval (mirrorStep x g γ)⟫_ℝ := by
  intro x g γ y
  exact h_variational x g γ (mirrorStep x g γ) y
    (fun u => h_mirrorStep_minimizes x g γ u)

/-- Convex carrier functions satisfy the usual segment-difference bound.

For a carrier function whose canonical ambient totalization is convex on the
carrier, the value at the segment point from `x` to `u` increases from `x` by
at most `t` times the endpoint difference.

Layer: Layer0 | Gap: Level 0 (carrier convex segment difference bound)
Proof: apply the defining convexity inequality to the weights `1 - t` and `t`,
  identify the affine combination with `AffineMap.lineMap`, and rearrange the
  resulting scalar inequality.
Source: Mathlib convex functions on real normed vector spaces and affine segment APIs
Used in: nonconvex stochastic mirror descent simple convex term bound along the
  projected-gradient segment
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem convexOnCarrier_segment_sub_le_mul_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : Set E} (h : {x : E // x ∈ X} → ℝ)
    (hconv : ConvexOn ℝ X (SOptLib.totalizeOn X h))
    (x u : {x : E // x ∈ X}) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    h
        ⟨AffineMap.lineMap x.1 u.1 t,
          hconv.1.lineMap_mem x.2 u.2 ht⟩ -
        h x ≤
      t * (h u - h x) := by
  classical
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have h1mt : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hsum : (1 - t) + t = 1 := by ring
  have hconv_ineq := hconv.2 x.2 u.2 h1mt ht0 hsum
  have hline :
      (1 - t) • x.1 + t • u.1 = AffineMap.lineMap x.1 u.1 t := by
    rw [AffineMap.lineMap_apply_module]
  let yseg : E := AffineMap.lineMap x.1 u.1 t
  have hyseg : yseg ∈ X := hconv.1.lineMap_mem x.2 u.2 ht
  have hleft :
      SOptLib.totalizeOn X h ((1 - t) • x.1 + t • u.1) =
        h
          ⟨AffineMap.lineMap x.1 u.1 t,
            hconv.1.lineMap_mem x.2 u.2 ht⟩ := by
    rw [hline]
    simpa [yseg] using (SOptLib.totalizeOn_of_mem X h hyseg)
  have hx :
      SOptLib.totalizeOn X h x.1 = h x := by
    simpa using (SOptLib.totalizeOn_of_mem X h x.2)
  have hu :
      SOptLib.totalizeOn X h u.1 = h u := by
    simpa using (SOptLib.totalizeOn_of_mem X h u.2)
  rw [hleft, hx, hu] at hconv_ineq
  simp [smul_eq_mul] at hconv_ineq
  nlinarith

/-- The projected-gradient inner product dominates its squared norm plus the prox objective gap.

For an abstract evaluated prox selector, the standard descent inner bound for
the selected prox point transfers to the inverse-stepsize projected-gradient
mapping by scaling the inequality with `gamma⁻¹` and unfolding the mapping.

Layer: Layer0 | Gap: Level 0 (projected-gradient descent algebra)
Proof: multiply the prox descent inner bound by the nonnegative inverse
  stepsize, unfold the projected-gradient mapping, and simplify the squared
  norm of a nonnegative scalar multiple.
Source: Mathlib real inner-product space algebra and normed vector space scalar norms
Used in: nonconvex stochastic mirror descent prox-step projected-gradient descent estimate
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
theorem projectedGradient_inner_ge_norm_sq_add_hdiff
    {P E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (eval : P → E) (h : P → ℝ) (prox : P → E → ℝ → P)
    (x : P) (g : E) (gamma : ℝ) (hgamma : 0 < gamma)
    (hinner :
      gamma⁻¹ * ‖eval x - eval (prox x g gamma)‖ ^ 2 +
          h (prox x g gamma) - h x ≤
        ⟪g, eval x - eval (prox x g gamma)⟫_ℝ) :
    ⟪g, gamma⁻¹ • (eval x - eval (prox x g gamma))⟫_ℝ ≥
      ‖gamma⁻¹ • (eval x - eval (prox x g gamma))‖ ^ 2 +
        gamma⁻¹ * (h (prox x g gamma) - h x) := by
  let xp := prox x g gamma
  let d : E := eval x - eval xp
  have hgamma_inv_nonneg : 0 ≤ gamma⁻¹ := inv_nonneg.mpr (le_of_lt hgamma)
  have hscale :
      gamma⁻¹ *
          (gamma⁻¹ * ‖eval x - eval xp‖ ^ 2 + h xp - h x) ≤
        gamma⁻¹ * ⟪g, eval x - eval xp⟫_ℝ := by
    exact mul_le_mul_of_nonneg_left hinner hgamma_inv_nonneg
  have hnorm_smul :
      ‖gamma⁻¹ • d‖ ^ 2 = gamma⁻¹ * (gamma⁻¹ * ‖d‖ ^ 2) := by
    have hnorm : ‖gamma⁻¹ • d‖ = gamma⁻¹ * ‖d‖ := by
      rw [norm_smul]
      simp [Real.norm_of_nonneg hgamma_inv_nonneg]
    rw [hnorm]
    ring
  dsimp [xp, d] at hscale hnorm_smul ⊢
  rw [inner_smul_right, hnorm_smul]
  nlinarith

/-- The projected-gradient mapping is Lipschitz in the oracle under a scaled prox-distance bound.

For an abstract evaluated prox selector, if two same-state selected prox points
have inverse-stepsize-scaled ambient distance at most the oracle-vector
distance, then the corresponding projected-gradient mappings satisfy the same
one-Lipschitz estimate in the oracle argument.

Layer: Layer0 | Gap: Level 0 (projected-gradient oracle Lipschitz algebra)
Proof: unfold the projected-gradient mapping, cancel the common base point,
  rewrite the norm of the nonnegative inverse-stepsize scalar multiple, and
  apply the supplied scaled prox-distance bound.
Source: Mathlib normed vector space scalar-norm identities and additive-group algebra
Used in: nonconvex stochastic mirror descent same-state prox-step projected-gradient oracle continuity
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
theorem projectedGradient_lipschitz_oracle_of_prox_scaled_dist
    {P E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (eval : P → E) (prox : P → E → ℝ → P)
    (x : P) (g₁ g₂ : E) (gamma : ℝ) (hgamma : 0 < gamma)
    (hprox :
      gamma⁻¹ * ‖eval (prox x g₁ gamma) - eval (prox x g₂ gamma)‖ ≤
        ‖g₁ - g₂‖) :
    ‖gamma⁻¹ • (eval x - eval (prox x g₁ gamma)) -
        gamma⁻¹ • (eval x - eval (prox x g₂ gamma))‖ ≤ ‖g₁ - g₂‖ := by
  let p₁ := prox x g₁ gamma
  let p₂ := prox x g₂ gamma
  have hgamma_inv_nonneg : 0 ≤ gamma⁻¹ := inv_nonneg.mpr (le_of_lt hgamma)
  have hnorm :
      ‖gamma⁻¹ • (eval p₂ - eval p₁)‖ =
        gamma⁻¹ * ‖eval p₁ - eval p₂‖ := by
    rw [norm_smul, norm_sub_rev]
    simp [Real.norm_of_nonneg hgamma_inv_nonneg]
  dsimp [p₁, p₂] at hprox hnorm ⊢
  have hdiff :
      gamma⁻¹ • (eval x - eval (prox x g₁ gamma)) -
          gamma⁻¹ • (eval x - eval (prox x g₂ gamma)) =
        gamma⁻¹ • (eval (prox x g₂ gamma) - eval (prox x g₁ gamma)) := by
    rw [← smul_sub]
    congr 1
    abel
  rw [hdiff, hnorm]
  exact hprox

/-- A fixed-base prox-point selector is continuous when it is Lipschitz in the oracle.

This is the metric continuity bridge for a prox selector after the base point
and stepsize have been fixed, leaving only the oracle vector as input.

Layer: Layer0 | Gap: Level 0 (prox-point oracle continuity from Lipschitz estimate)
Proof: apply Mathlib's `LipschitzWith.continuous` theorem to the fixed-base
  oracle map.
Source: Mathlib metric-space Lipschitz maps and continuity APIs
Used in: nonconvex stochastic mirror descent fixed-base prox-step oracle continuity
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem proxPoint_continuous_of_lipschitzWith_oracle
    {E P : Type*} [PseudoMetricSpace E] [PseudoMetricSpace P]
    (prox : E → P) {K : NNReal}
    (hprox : LipschitzWith K prox) :
    Continuous prox := by
  exact hprox.continuous

/-- A fixed-stepsize prox-point map is jointly continuous from a state-oracle bound.

If the prox selector is controlled by `gamma` times oracle distance plus the
distance between gradients at the two states, continuity of the gradient map
implies joint continuity of the uncurried state-oracle selector.

Layer: Layer0 | Gap: Level 1 (prox-point state-oracle joint continuity)
Proof: reduce to the staged metric epsilon-delta continuity lemma for prox steps
  controlled by an oracle-distance and base-gradient-distance estimate.
Source: Mathlib metric-space continuity and ordered-field algebra APIs
Used in: stochastic mirror descent fixed-stepsize prox-point continuity for state and oracle inputs
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, randomized stochastic mirror descent -/
theorem proxPoint_continuous_state_oracle_of_bound
    {P E : Type*} [PseudoMetricSpace P] [NormedAddCommGroup E]
    (prox : P → E → P) (grad : P → E) (gamma : ℝ) (hgamma : 0 < gamma)
    (hgrad : Continuous grad)
    (hbound :
      ∀ (x₁ x₂ : P) (g₁ g₂ : E),
        dist (prox x₁ g₁) (prox x₂ g₂) ≤
          gamma * dist g₁ g₂ + dist (grad x₁) (grad x₂)) :
    Continuous (fun p : P × E => prox p.1 p.2) := by
  refine continuous_iff_continuousAt.2 ?_
  intro p₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  rcases Metric.continuousAt_iff.1 (hgrad.continuousAt (x := p₀.1)) (ε / 2) hε2 with
    ⟨δν, hδν_pos, hδν⟩
  let δ : ℝ := min (ε / (2 * max gamma 1)) δν
  have hmax_pos : 0 < max gamma 1 :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right gamma 1)
  have hδ_pos : 0 < δ := by
    exact lt_min (div_pos hε (mul_pos (by norm_num) hmax_pos)) hδν_pos
  refine ⟨δ, hδ_pos, ?_⟩
  intro p hp
  rw [Prod.dist_eq] at hp
  have hp_fst_delta : dist p.1 p₀.1 < δ := (max_lt_iff.mp hp).1
  have hp_snd_delta : dist p.2 p₀.2 < δ := (max_lt_iff.mp hp).2
  have hp_fst : dist p.1 p₀.1 < δν := by
    have hle : δ ≤ δν := min_le_right _ _
    exact lt_of_lt_of_le hp_fst_delta hle
  have hp_snd : dist p.2 p₀.2 < ε / (2 * max gamma 1) := by
    have hle : δ ≤ ε / (2 * max gamma 1) := min_le_left _ _
    exact lt_of_lt_of_le hp_snd_delta hle
  have hνdist :
      dist (grad p.1) (grad p₀.1) < ε / 2 :=
    hδν hp_fst
  have hdist_bound :
      dist (prox p.1 p.2) (prox p₀.1 p₀.2) ≤
        gamma * dist p.2 p₀.2 + dist (grad p.1) (grad p₀.1) :=
    hbound p.1 p₀.1 p.2 p₀.2
  have hgamma_le_max : gamma ≤ max gamma 1 := le_max_left gamma 1
  have hgsmall : gamma * dist p.2 p₀.2 < ε / 2 := by
    calc
      gamma * dist p.2 p₀.2 ≤ max gamma 1 * dist p.2 p₀.2 :=
        mul_le_mul_of_nonneg_right hgamma_le_max dist_nonneg
      _ < max gamma 1 * (ε / (2 * max gamma 1)) :=
        mul_lt_mul_of_pos_left hp_snd hmax_pos
      _ = ε / 2 := by
        field_simp [(ne_of_gt hmax_pos)]
  exact lt_of_le_of_lt hdist_bound (by linarith)

/-- A positive inverse-scaled pointwise distance bound gives a Lipschitz estimate.

If every image distance, scaled by `gamma⁻¹`, is bounded by the source distance
and `gamma` is positive, then the map is `LipschitzWith (Real.toNNReal gamma)`.

Layer: Layer0 | Gap: Level 0 (inverse-scaled Lipschitz packaging)
Proof: multiply the inverse-scaled bound by the positive constant `gamma` and
  discharge the result with Mathlib's metric `LipschitzWith.of_dist_le'` API.
Source: Mathlib metric Lipschitz maps and ordered-field algebra APIs
Used in: nonconvex stochastic mirror descent fixed-base prox-step oracle continuity
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
theorem lipschitzWith_of_inv_mul_dist_le
    {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    (f : α → β) (gamma : ℝ) (hgamma : 0 < gamma)
    (h : ∀ x y : α, gamma⁻¹ * dist (f x) (f y) ≤ dist x y) :
    LipschitzWith (Real.toNNReal gamma) f := by
  refine LipschitzWith.of_dist_le' ?_
  intro x y
  have hgamma_nonneg : 0 ≤ gamma := le_of_lt hgamma
  calc
    dist (f x) (f y) = gamma * (gamma⁻¹ * dist (f x) (f y)) := by
      field_simp [hgamma.ne']
    _ ≤ gamma * dist x y := mul_le_mul_of_nonneg_left (h x y) hgamma_nonneg

/-- A fixed-base prox-point selector is measurable from oracle continuity.

This is the continuity-to-Borel-measurability bridge for a prox selector whose
base point and stepsize have already been fixed, leaving only the oracle vector
as input.

Layer: Layer0 | Gap: Level 0 (prox-point oracle measurability from continuity)
Proof: apply Mathlib's `Continuous.measurable` theorem to the fixed-base
  oracle selector between Borel spaces.
Source: Mathlib topology and Borel measurability APIs for continuous maps
Used in: nonconvex stochastic mirror descent fixed-base prox-step oracle measurability
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem proxPoint_measurable_oracle_of_continuous
    {E P : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
    (prox : E → P) (hprox : Continuous prox) :
    Measurable prox := by
  exact hprox.measurable

/-- A fixed-stepsize prox-point selector is measurable from joint continuity.

This is the continuity-to-Borel-measurability bridge for a prox selector whose
stepsize has already been fixed, leaving only the current state and oracle
vector as inputs.

Layer: Layer0 | Gap: Level 0 (prox-point state-oracle measurability from joint continuity)
Proof: apply Mathlib's `Continuous.measurable` theorem to the jointly continuous
  selector on the product Borel space.
Source: Mathlib topology and Borel measurability APIs for continuous maps on products
Used in: nonconvex stochastic mirror descent fixed-stepsize prox-step measurability
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem proxPoint_measurable_state_oracle_of_continuous
    {P E : Type*} [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopologyEither P E]
    (prox : P × E → P) (hprox : Continuous prox) :
    Measurable prox := by
  exact hprox.measurable

/-- A prox variational inequality and strong monotonicity imply the descent inner bound.

For an abstract carrier mapped into a real Hilbert space, applying the prox
variational inequality at the current point and using one-strong monotonicity
of the mirror gradient controls the squared prox displacement.

Layer: Layer0 | Gap: Level 0 (prox variational inequality to descent bound)
Proof: rewrite the reversed norm and inner product signs, then combine the
  variational inequality with the strong-monotonicity bound by ordered real
  arithmetic.
Source: Mathlib real inner-product space algebra and ordered-field inequalities
Used in: nonconvex stochastic mirror descent prox-step descent estimate
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
theorem prox_descent_inner_bound_of_variational
    {P E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (eval grad : P → E) (h : P → ℝ) (prox x : P) (g : E) (gamma : ℝ)
    (hgamma : 0 < gamma)
    (hvi :
      0 ≤
        ⟪g, eval x - eval prox⟫_ℝ +
          gamma⁻¹ * ⟪grad prox - grad x, eval x - eval prox⟫_ℝ +
          (h x - h prox))
    (hstrong :
      ‖eval prox - eval x‖ ^ 2 ≤
        ⟪eval prox - eval x, grad prox - grad x⟫_ℝ) :
    gamma⁻¹ * ‖eval x - eval prox‖ ^ 2 + h prox - h x ≤
      ⟪g, eval x - eval prox⟫_ℝ := by
  have hnorm : ‖eval x - eval prox‖ ^ 2 = ‖eval prox - eval x‖ ^ 2 := by
    rw [norm_sub_rev]
  have hinner :
      ⟪grad prox - grad x, eval x - eval prox⟫_ℝ =
        -⟪eval prox - eval x, grad prox - grad x⟫_ℝ := by
    rw [real_inner_comm, ← neg_sub (eval prox) (eval x), inner_neg_left]
  have hgamma_inv_nonneg : 0 ≤ gamma⁻¹ := inv_nonneg.mpr (le_of_lt hgamma)
  nlinarith [hvi, hstrong, hnorm, hinner, hgamma_inv_nonneg]

/-- Two same-state prox points have scaled distance bounded by oracle distance.

For an abstract carrier evaluated in a real Hilbert space, two variational
inequalities at the same base point make the nonsmooth terms cancel. Strong
monotonicity of the mirror gradient then controls the selected-point distance.

Layer: Layer0 | Gap: Level 0 (same-state prox-point oracle stability)
Proof: add the two variational inequalities, rewrite the sum into an oracle
  inner product minus the strong-monotonicity pairing, then use Cauchy-Schwarz
  and divide by the positive displacement norm.
Source: Mathlib real inner-product Cauchy-Schwarz and ordered-field algebra APIs
Used in: nonconvex stochastic mirror descent fixed-state prox-step oracle continuity
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
theorem prox_points_scaled_dist_le_oracle_dist_of_variational
    {P E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (eval grad : P → E) (h : P → ℝ)
    (x p₁ p₂ : P) (g₁ g₂ : E) (gamma : ℝ) (hgamma : 0 < gamma)
    (hvi₁ :
      0 ≤
        ⟪g₁, eval p₂ - eval p₁⟫_ℝ +
          gamma⁻¹ * ⟪grad p₁ - grad x, eval p₂ - eval p₁⟫_ℝ +
          (h p₂ - h p₁))
    (hvi₂ :
      0 ≤
        ⟪g₂, eval p₁ - eval p₂⟫_ℝ +
          gamma⁻¹ * ⟪grad p₂ - grad x, eval p₁ - eval p₂⟫_ℝ +
          (h p₁ - h p₂))
    (hstrong :
      ‖eval p₁ - eval p₂‖ ^ 2 ≤
        ⟪eval p₁ - eval p₂, grad p₁ - grad p₂⟫_ℝ) :
    gamma⁻¹ * ‖eval p₁ - eval p₂‖ ≤ ‖g₁ - g₂‖ := by
  let δ : E := eval p₁ - eval p₂
  let C : ℝ := ⟪δ, grad p₁ - grad p₂⟫_ℝ
  have hsum :
      0 ≤
        (⟪g₁, eval p₂ - eval p₁⟫_ℝ +
            gamma⁻¹ * ⟪grad p₁ - grad x, eval p₂ - eval p₁⟫_ℝ +
            (h p₂ - h p₁)) +
          (⟪g₂, eval p₁ - eval p₂⟫_ℝ +
            gamma⁻¹ * ⟪grad p₂ - grad x, eval p₁ - eval p₂⟫_ℝ +
            (h p₁ - h p₂)) := by
    exact add_nonneg hvi₁ hvi₂
  have hcombine :
      (⟪g₁, eval p₂ - eval p₁⟫_ℝ +
            gamma⁻¹ * ⟪grad p₁ - grad x, eval p₂ - eval p₁⟫_ℝ +
            (h p₂ - h p₁)) +
          (⟪g₂, eval p₁ - eval p₂⟫_ℝ +
            gamma⁻¹ * ⟪grad p₂ - grad x, eval p₁ - eval p₂⟫_ℝ +
            (h p₁ - h p₂)) =
        ⟪g₂ - g₁, δ⟫_ℝ - gamma⁻¹ * C := by
    dsimp [δ, C]
    simp only [sub_eq_add_neg, inner_add_left, inner_add_right, inner_neg_left,
      inner_neg_right, real_inner_comm]
    ring
  have hsum' : 0 ≤ ⟪g₂ - g₁, δ⟫_ℝ - gamma⁻¹ * C := by
    rwa [hcombine] at hsum
  have hstrong' : ‖δ‖ ^ 2 ≤ C := by
    dsimp [δ, C]
    exact hstrong
  have hgamma_inv_nonneg : 0 ≤ gamma⁻¹ := inv_nonneg.mpr (le_of_lt hgamma)
  have hquad : gamma⁻¹ * ‖δ‖ ^ 2 ≤ ‖g₁ - g₂‖ * ‖δ‖ := by
    have hmain : gamma⁻¹ * ‖δ‖ ^ 2 ≤ ⟪g₂ - g₁, δ⟫_ℝ := by
      nlinarith
    have hcs :
        ⟪g₂ - g₁, δ⟫_ℝ ≤ ‖g₁ - g₂‖ * ‖δ‖ := by
      calc
        ⟪g₂ - g₁, δ⟫_ℝ ≤ |⟪g₂ - g₁, δ⟫_ℝ| := le_abs_self _
        _ ≤ ‖g₂ - g₁‖ * ‖δ‖ := abs_real_inner_le_norm (g₂ - g₁) δ
        _ = ‖g₁ - g₂‖ * ‖δ‖ := by rw [norm_sub_rev]
    exact le_trans hmain hcs
  by_cases hδ : ‖δ‖ = 0
  · rw [hδ]
    simpa using norm_nonneg (g₁ - g₂)
  · have hδpos : 0 < ‖δ‖ := lt_of_le_of_ne (norm_nonneg δ) (Ne.symm hδ)
    have hquad' : gamma⁻¹ * ‖δ‖ * ‖δ‖ ≤ ‖g₁ - g₂‖ * ‖δ‖ := by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hquad
    exact le_of_mul_le_mul_right hquad' hδpos

/-- Two prox points with different base states are controlled by oracle and base-gradient gaps.

For an abstract carrier evaluated in a real Hilbert space, two prox variational
inequalities make the nonsmooth terms cancel. Strong monotonicity of the mirror
gradient controls the selected-point displacement, while Cauchy-Schwarz bounds
the oracle and base-gradient cross terms.

Layer: Layer0 | Gap: Level 0 (state-oracle prox-point stability)
Proof: add the two variational inequalities, rewrite the sum into oracle,
  strong-monotonicity, and base-gradient pairings, then use Cauchy-Schwarz and
  divide by the positive displacement norm.
Source: Mathlib real inner-product Cauchy-Schwarz and ordered-field algebra APIs
Used in: nonconvex stochastic mirror descent fixed-stepsize prox-step joint continuity
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
theorem prox_points_dist_le_oracle_dist_add_base_grad_dist_of_variational
    {P E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (eval grad : P → E) (h : P → ℝ)
    (x₁ x₂ p₁ p₂ : P) (g₁ g₂ : E) (gamma : ℝ) (hgamma : 0 < gamma)
    (hvi₁ :
      0 ≤
        ⟪g₁, eval p₂ - eval p₁⟫_ℝ +
          gamma⁻¹ * ⟪grad p₁ - grad x₁, eval p₂ - eval p₁⟫_ℝ +
          (h p₂ - h p₁))
    (hvi₂ :
      0 ≤
        ⟪g₂, eval p₁ - eval p₂⟫_ℝ +
          gamma⁻¹ * ⟪grad p₂ - grad x₂, eval p₁ - eval p₂⟫_ℝ +
          (h p₁ - h p₂))
    (hstrong :
      ‖eval p₁ - eval p₂‖ ^ 2 ≤
        ⟪eval p₁ - eval p₂, grad p₁ - grad p₂⟫_ℝ) :
    ‖eval p₁ - eval p₂‖ ≤
      gamma * ‖g₁ - g₂‖ + ‖grad x₁ - grad x₂‖ := by
  let δ : E := eval p₁ - eval p₂
  let C : ℝ := ⟪δ, grad p₁ - grad p₂⟫_ℝ
  let B : ℝ := ⟪grad x₁ - grad x₂, δ⟫_ℝ
  have hsum :
      0 ≤
        (⟪g₁, eval p₂ - eval p₁⟫_ℝ +
            gamma⁻¹ * ⟪grad p₁ - grad x₁, eval p₂ - eval p₁⟫_ℝ +
            (h p₂ - h p₁)) +
          (⟪g₂, eval p₁ - eval p₂⟫_ℝ +
            gamma⁻¹ * ⟪grad p₂ - grad x₂, eval p₁ - eval p₂⟫_ℝ +
            (h p₁ - h p₂)) := by
    exact add_nonneg hvi₁ hvi₂
  have hcombine :
      (⟪g₁, eval p₂ - eval p₁⟫_ℝ +
            gamma⁻¹ * ⟪grad p₁ - grad x₁, eval p₂ - eval p₁⟫_ℝ +
            (h p₂ - h p₁)) +
          (⟪g₂, eval p₁ - eval p₂⟫_ℝ +
            gamma⁻¹ * ⟪grad p₂ - grad x₂, eval p₁ - eval p₂⟫_ℝ +
            (h p₁ - h p₂)) =
        ⟪g₂ - g₁, δ⟫_ℝ - gamma⁻¹ * C + gamma⁻¹ * B := by
    dsimp [δ, C, B]
    simp only [sub_eq_add_neg, inner_add_left, inner_add_right, inner_neg_left,
      inner_neg_right, real_inner_comm]
    ring
  have hsum' : 0 ≤ ⟪g₂ - g₁, δ⟫_ℝ - gamma⁻¹ * C + gamma⁻¹ * B := by
    rwa [hcombine] at hsum
  have hstrong' : ‖δ‖ ^ 2 ≤ C := by
    dsimp [δ, C]
    exact hstrong
  have hgamma_inv_nonneg : 0 ≤ gamma⁻¹ := inv_nonneg.mpr (le_of_lt hgamma)
  have hquad :
      gamma⁻¹ * ‖δ‖ ^ 2 ≤
        ‖g₁ - g₂‖ * ‖δ‖ + gamma⁻¹ * ‖grad x₁ - grad x₂‖ * ‖δ‖ := by
    have hmain :
        gamma⁻¹ * ‖δ‖ ^ 2 ≤
          ⟪g₂ - g₁, δ⟫_ℝ + gamma⁻¹ * B := by
      nlinarith
    have hg :
        ⟪g₂ - g₁, δ⟫_ℝ ≤ ‖g₁ - g₂‖ * ‖δ‖ := by
      calc
        ⟪g₂ - g₁, δ⟫_ℝ ≤ |⟪g₂ - g₁, δ⟫_ℝ| := le_abs_self _
        _ ≤ ‖g₂ - g₁‖ * ‖δ‖ := abs_real_inner_le_norm (g₂ - g₁) δ
        _ = ‖g₁ - g₂‖ * ‖δ‖ := by rw [norm_sub_rev]
    have hB :
        gamma⁻¹ * B ≤ gamma⁻¹ * ‖grad x₁ - grad x₂‖ * ‖δ‖ := by
      have hB_le :
          B ≤ ‖grad x₁ - grad x₂‖ * ‖δ‖ := by
        calc
          B ≤ |B| := le_abs_self _
          _ ≤ ‖grad x₁ - grad x₂‖ * ‖δ‖ := by
            simpa [B] using abs_real_inner_le_norm (grad x₁ - grad x₂) δ
      nlinarith
    nlinarith
  by_cases hδ : ‖δ‖ = 0
  · have hzero : ‖δ‖ ≤ gamma * ‖g₁ - g₂‖ + ‖grad x₁ - grad x₂‖ := by
      rw [hδ]
      positivity
    simpa [δ] using hzero
  · have hδpos : 0 < ‖δ‖ := lt_of_le_of_ne (norm_nonneg δ) (Ne.symm hδ)
    have hquad' :
        gamma⁻¹ * ‖δ‖ * ‖δ‖ ≤
          (‖g₁ - g₂‖ + gamma⁻¹ * ‖grad x₁ - grad x₂‖) * ‖δ‖ := by
      nlinarith [hquad]
    have hdiv :
        gamma⁻¹ * ‖δ‖ ≤
          ‖g₁ - g₂‖ + gamma⁻¹ * ‖grad x₁ - grad x₂‖ :=
      le_of_mul_le_mul_right hquad' hδpos
    have hgamma_nonneg : 0 ≤ gamma := le_of_lt hgamma
    have hscaled :
        gamma * (gamma⁻¹ * ‖δ‖) ≤
          gamma * (‖g₁ - g₂‖ + gamma⁻¹ * ‖grad x₁ - grad x₂‖) :=
      mul_le_mul_of_nonneg_left hdiv hgamma_nonneg
    have hleft : gamma * (gamma⁻¹ * ‖δ‖) = ‖δ‖ := by
      field_simp [hgamma.ne']
    have hright :
        gamma * (‖g₁ - g₂‖ + gamma⁻¹ * ‖grad x₁ - grad x₂‖) =
          gamma * ‖g₁ - g₂‖ + ‖grad x₁ - grad x₂‖ := by
      field_simp [hgamma.ne']
    simpa [δ, hleft, hright] using hscaled

/-- A minimizing prox objective gives a nonnegative scaled component difference.

For an abstract composite prox objective represented as an inner-product oracle
term, inverse-stepsize divergence term, and simple additive term, comparing a
minimizer `xp` with any candidate `y` yields the scaled nonnegative difference
used in prox-step segment estimates.

Layer: Layer0 | Gap: Level 0 (prox minimality scaled objective difference)
Proof: convert the objective comparison to a nonnegative difference, multiply
  by the positive stepsize, unfold the abstract representation, and clear the
  inverse stepsize by ordered-field algebra.
Source: Mathlib real inner-product notation and linear ordered field algebra APIs
Used in: nonconvex stochastic mirror descent prox-step lower bound along a feasible segment
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
theorem prox_minimality_scaled_difference_nonneg
    {P E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (objective : P → E → ℝ → P → ℝ) (V : P → P → ℝ)
    (eval : P → E) (h : P → ℝ)
    (x xp y : P) (g : E) {γ : ℝ} (hγ : 0 < γ)
    (hobjective :
      ∀ u : P, objective x g γ u = ⟪g, eval u⟫_ℝ + γ⁻¹ * V x u + h u)
    (hmin : ∀ u : P, objective x g γ xp ≤ objective x g γ u) :
    0 ≤
      γ * (⟪g, eval y⟫_ℝ - ⟪g, eval xp⟫_ℝ) +
        (V x y - V x xp) +
        γ * (h y - h xp) := by
  have hle : objective x g γ xp ≤ objective x g γ y := hmin y
  have hdiff : 0 ≤ objective x g γ y - objective x g γ xp := sub_nonneg.mpr hle
  have hscaled : 0 ≤ γ * (objective x g γ y - objective x g γ xp) :=
    mul_nonneg hγ.le hdiff
  convert hscaled using 1
  rw [hobjective y, hobjective xp]
  field_simp [hγ.ne']
  ring

/-- A prox segment lower bound survives replacing the segment value of `h` by a convex majorant.

For an abstract point type evaluated in a real Hilbert space, if the scaled prox
minimality inequality holds at a segment point, the inner-product displacement is
identified with `t` times a chosen direction, and the simple term `h` is convexly
majorized along the segment, then the lower bound with endpoint `h` difference follows.

Layer: Layer0 | Gap: Level 0 (prox segment majorization algebra)
Proof: rewrite the scaled prox lower bound by the supplied inner-product segment
  identity, multiply the convex majorization by the nonnegative stepsize, and
  combine the two real inequalities by ordered-ring arithmetic.
Source: Mathlib real inner-product space algebra and ordered-field inequalities
Used in: nonconvex stochastic mirror descent prox-step lower bound along the
  projected-gradient segment
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
theorem prox_segment_majorized_lower_bound
    {P E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (eval : P → E) (V : P → P → ℝ) (h : P → ℝ)
    (x xp u y : P) (g : E) (γ t : ℝ)
    (hγ : 0 ≤ γ)
    (hbase :
      0 ≤
        γ * (⟪g, eval y⟫_ℝ - ⟪g, eval xp⟫_ℝ) +
          (V x y - V x xp) +
          γ * (h y - h xp))
    (hline : eval y = AffineMap.lineMap (eval xp) (eval u) t)
    (hh : h y - h xp ≤ t * (h u - h xp)) :
    0 ≤
      γ * t * ⟪g, eval u - eval xp⟫_ℝ +
        (V x y - V x xp) +
        γ * t * (h u - h xp) := by
  have hinner :
      ⟪g, eval y⟫_ℝ - ⟪g, eval xp⟫_ℝ =
        t * ⟪g, eval u - eval xp⟫_ℝ := by
    have hy : eval y = eval xp + t • (eval u - eval xp) := by
      rw [hline]
      simp [AffineMap.lineMap_apply_module']
      abel
    rw [hy]
    simp [inner_add_right, inner_smul_right]
  have hh_scaled : γ * (h y - h xp) ≤ γ * (t * (h u - h xp)) := by
    exact mul_le_mul_of_nonneg_left hh hγ
  have hbase' :
      0 ≤
        γ * (t * ⟪g, eval u - eval xp⟫_ℝ) +
          (V x y - V x xp) +
          γ * (h y - h xp) := by
    simpa [hinner] using hbase
  have hmajor :
      γ * (t * ⟪g, eval u - eval xp⟫_ℝ) +
          (V x y - V x xp) +
          γ * (h y - h xp) ≤
        γ * (t * ⟪g, eval u - eval xp⟫_ℝ) +
          (V x y - V x xp) +
          γ * (t * (h u - h xp)) := by
    nlinarith
  have hnonneg :
      0 ≤
        γ * (t * ⟪g, eval u - eval xp⟫_ℝ) +
          (V x y - V x xp) +
          γ * (t * (h u - h xp)) :=
    le_trans hbase' hmajor
  simpa [mul_assoc] using hnonneg

/-- A prox segment majorant built from two linear terms and a segment value is zero
at the left endpoint.

The segment point is kept abstract: it only has to return the prox point at
`t = 0`. This covers the common subtype-valued segment construction used in
prox-step arguments without exposing the algorithm-specific carrier setup.

Layer: Layer0 | Gap: Level 0 (prox segment endpoint algebra)
Proof: reduce the conditional segment term with `0 ∈ Icc 0 1`, rewrite the
  segment endpoint to the prox point, and simplify the two zero-scaled linear terms.
Source: Mathlib real inner-product space algebra and interval membership APIs
Used in: nonconvex stochastic mirror descent prox-step majorized segment endpoint
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
theorem prox_segment_majorized_value_zero
    {P E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (V : P → P → ℝ) (h : P → ℝ)
    (x xp u : P) (g d : E) (γ : ℝ)
    (segment : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → P)
    (hsegment_zero :
      ∀ h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1, segment 0 h0 = xp) :
    (fun t : ℝ =>
      γ * t * ⟪g, d⟫_ℝ +
        (if ht : t ∈ Set.Icc (0 : ℝ) 1 then
          V x (segment t ht) - V x xp
        else 0) +
        γ * t * (h u - h xp)) 0 = 0 := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  simp [h0, hsegment_zero h0]

/-- A prox majorant assembled from two linear terms and a segment term has the
sum of the corresponding right derivatives at zero.

This is the scalar calculus step in the prox variational inequality: once the
Bregman segment contribution has derivative `⟪gradDiff, d⟫`, adding the two
linear majorant terms contributes `γ * ⟪g, d⟫` and `γ * C`.

Layer: Layer0 | Gap: Level 0 (prox majorant derivative assembly)
Proof: differentiate the two linear scalar terms with `hasDerivAt_id`, add the
  supplied derivative of the segment term, and normalize multiplication order.
Source: Mathlib one-dimensional derivative calculus for products and sums
Used in: stochastic mirror descent prox-step variational inequality
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
theorem prox_majorant_hasDerivWithinAt_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (β : ℝ → ℝ) (g d gradDiff : E) (γ C : ℝ)
    (hβ : HasDerivWithinAt β ⟪gradDiff, d⟫_ℝ (Set.Icc (0 : ℝ) 1) 0) :
    HasDerivWithinAt
      (fun t : ℝ => γ * t * ⟪g, d⟫_ℝ + β t + γ * t * C)
      (γ * ⟪g, d⟫_ℝ + ⟪gradDiff, d⟫_ℝ + γ * C)
      (Set.Icc (0 : ℝ) 1) 0 := by
  let A : ℝ := ⟪g, d⟫_ℝ
  let B : ℝ := ⟪gradDiff, d⟫_ℝ
  have hlin₁ : HasDerivWithinAt (fun t : ℝ => γ * t * A) (γ * A)
      (Set.Icc (0 : ℝ) 1) 0 := by
    simpa [A, mul_assoc, mul_comm, mul_left_comm] using
      (((hasDerivAt_id (0 : ℝ)).const_mul (γ * A)).hasDerivWithinAt
        (s := Set.Icc (0 : ℝ) 1))
  have hlin₂ : HasDerivWithinAt (fun t : ℝ => γ * t * C) (γ * C)
      (Set.Icc (0 : ℝ) 1) 0 := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (((hasDerivAt_id (0 : ℝ)).const_mul (γ * C)).hasDerivWithinAt
        (s := Set.Icc (0 : ℝ) 1))
  have hβ' : HasDerivWithinAt β B (Set.Icc (0 : ℝ) 1) 0 := by
    simpa [B] using hβ
  have hsum := (hlin₁.add hβ').add hlin₂
  simpa [A, B, add_assoc, mul_assoc] using hsum

/-- A one-dimensional prox majorant minimum gives the scaled prox variational inequality.

For an abstract candidate type with an evaluation map into a real Hilbert space,
if the scalar segment majorant `φ` is nonnegative on `[0,1]`, vanishes at the
left endpoint, and has right derivative equal to the scaled prox expression,
then that scaled variational expression is nonnegative.

Layer: Layer0 | Gap: Level 0 (prox argmin segment first-order condition)
Proof: convert nonnegativity of the segment majorant into a local minimum at
  the left endpoint, then apply the one-sided derivative sign lemma on `[0,1]`.
Source: Mathlib one-dimensional within-derivative calculus and real inner-product algebra
Used in: nonconvex stochastic mirror descent prox-step variational inequality
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
theorem prox_scaled_variational_inequality_of_argmin
    {P E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (eval grad : P → E) (h : P → ℝ)
    (x xp u : P) (g : E) (γ : ℝ) (φ : ℝ → ℝ)
    (hφ0 : φ 0 = 0)
    (hφ_nonneg : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ φ t)
    (hderφ :
      HasDerivWithinAt φ
        (γ * ⟪g, eval u - eval xp⟫_ℝ +
          ⟪grad xp - grad x, eval u - eval xp⟫_ℝ +
          γ * (h u - h xp))
        (Set.Icc (0 : ℝ) 1) 0) :
    0 ≤
      γ * ⟪g, eval u - eval xp⟫_ℝ +
        ⟪grad xp - grad x, eval u - eval xp⟫_ℝ +
        γ * (h u - h xp) := by
  refine right_derivative_nonneg_of_min_on_Icc hderφ ?_
  intro t ht
  simpa [hφ0] using hφ_nonneg t ht

/-- A positive stepsize converts the scaled prox variational inequality to the
unscaled paper form.

For an abstract carrier mapped into a real Hilbert space, the argmin-derived
scaled inequality `γ * ⟪g,d⟫ + ⟪grad xp - grad x,d⟫ + γ * (h u - h xp) ≥ 0`
is equivalent, when `γ > 0`, to the variational inequality with `γ⁻¹` on the
Bregman-gradient pairing.

Layer: Layer0 | Gap: Level 0 (scaled-to-unscaled prox variational inequality)
Proof: multiply the target inequality by the positive stepsize and simplify
  `γ * γ⁻¹`; positivity transfers nonnegativity across the multiplication.
Source: Mathlib real inner-product space algebra and ordered-field inequalities
Used in: nonconvex stochastic mirror descent prox-step variational inequality
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
theorem prox_variational_inequality_of_argmin
    {P E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (eval grad : P → E) (h : P → ℝ)
    (x xp u : P) (g : E) (γ : ℝ) (hγ : 0 < γ)
    (hscaled :
      0 ≤
        γ * ⟪g, eval u - eval xp⟫_ℝ +
          ⟪grad xp - grad x, eval u - eval xp⟫_ℝ +
          γ * (h u - h xp)) :
    0 ≤
      ⟪g, eval u - eval xp⟫_ℝ +
        γ⁻¹ * ⟪grad xp - grad x, eval u - eval xp⟫_ℝ +
        (h u - h xp) := by
  have hmul :
      0 ≤ γ *
        (⟪g, eval u - eval xp⟫_ℝ +
          γ⁻¹ * ⟪grad xp - grad x, eval u - eval xp⟫_ℝ +
          (h u - h xp)) := by
    convert hscaled using 1
    field_simp [hγ.ne']
  exact (mul_nonneg_iff_of_pos_left hγ).mp hmul

/-- A mirror objective has a unique minimizer under a seminorm Bregman lower bound.

If two candidates minimize the same paper mirror objective, a variational bridge
turns those minimizer facts into paired first-order inequalities.  The symmetric
Bregman identity makes their sum nonpositive, while the two directed lower
bounds force the seminorm distance to vanish; injectivity of `eval` then
identifies the minimizers.

Layer: Layer0 | Gap: Level 1 (seminorm-coercive mirror-objective argmin uniqueness)
Proof: add the paired variational inequalities, rewrite the sum using the
  symmetric Bregman identity, combine both directed seminorm lower bounds, and
  use the seminorm zero-kernel implication followed by injectivity of `eval`.
Source: Mathlib real inner-product algebra, seminorm negation, and ordered-field arithmetic
Used in: stochastic block mirror descent block prox-subproblem uniqueness with the paper block norm
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic block mirror descent -/
theorem mirrorObjective_argmin_unique_of_bregman_seminorm_lower_bound
    {P E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (V : P → P → ℝ) (eval grad : P → E) (p : Seminorm ℝ E)
    (heval_inj : Function.Injective eval)
    (x : P) (g : E) (γ : ℝ) (z z' : P)
    (hvariational :
      ∀ {a b : P},
        (∀ y : P,
          SOptLib.paperMirrorObjective V eval x g γ a ≤
            SOptLib.paperMirrorObjective V eval x g γ y) →
          0 ≤ ⟪γ • g + grad a - grad x, eval b - eval a⟫_ℝ)
    (hsymm : ∀ a b : P,
      V a b + V b a = ⟪grad b - grad a, eval b - eval a⟫_ℝ)
    (hlower : ∀ a b : P, (1 / 2 : ℝ) * p (eval b - eval a) ^ 2 ≤ V a b)
    (hp_zero : ∀ {u : E}, p u = 0 → u = 0)
    (hzmin :
      ∀ y : P,
        SOptLib.paperMirrorObjective V eval x g γ z ≤
          SOptLib.paperMirrorObjective V eval x g γ y)
    (hz'min :
      ∀ y : P,
        SOptLib.paperMirrorObjective V eval x g γ z' ≤
          SOptLib.paperMirrorObjective V eval x g γ y) :
    z = z' := by
  have hzvar : 0 ≤ ⟪γ • g + grad z - grad x, eval z' - eval z⟫_ℝ :=
    hvariational hzmin
  have hz'var : 0 ≤ ⟪γ • g + grad z' - grad x, eval z - eval z'⟫_ℝ :=
    hvariational hz'min
  have hsum_nonneg := add_nonneg hzvar hz'var
  have hsum_eq :
      ⟪γ • g + grad z - grad x, eval z' - eval z⟫_ℝ +
        ⟪γ • g + grad z' - grad x, eval z - eval z'⟫_ℝ =
          -(V z z' + V z' z) := by
    rw [hsymm z z']
    have hrev : eval z - eval z' = -(eval z' - eval z) := by
      abel
    rw [hrev, inner_neg_right]
    simp [inner_add_left, inner_sub_left, inner_smul_left]
  have hsym_nonpos : V z z' + V z' z ≤ 0 := by
    linarith
  have hp_rev : p (eval z - eval z') = p (eval z' - eval z) := by
    have hneg : eval z - eval z' = -(eval z' - eval z) := by
      abel
    rw [hneg]
    exact map_neg_eq_map p (eval z' - eval z)
  have hp_sq_nonpos : p (eval z' - eval z) ^ 2 ≤ 0 := by
    have hlower1 : (1 / 2 : ℝ) * p (eval z' - eval z) ^ 2 ≤ V z z' :=
      hlower z z'
    have hlower2 : (1 / 2 : ℝ) * p (eval z' - eval z) ^ 2 ≤ V z' z := by
      simpa [hp_rev] using hlower z' z
    nlinarith
  have hp_eq_zero : p (eval z' - eval z) = 0 := by
    have hsquare : p (eval z' - eval z) ^ 2 = 0 :=
      le_antisymm hp_sq_nonpos (sq_nonneg _)
    exact sq_eq_zero_iff.mp hsquare
  apply heval_inj
  have hdiff : eval z' - eval z = 0 :=
    hp_zero hp_eq_zero
  exact (sub_eq_zero.mp hdiff).symm

/-- A minimizer of a linear plus carrier-Bregman objective satisfies the prox variational
inequality.

For a convex feasible carrier, if `y` minimizes the objective
`u ↦ ⟪ζ, u⟫ + D_ν(z,u)` over the carrier, then every feasible comparison point `x`
satisfies the first-order variational inequality with gradient difference
`grad y - grad z`.

Layer: Layer0 | Gap: Level 1 (linear Bregman prox variational inequality)
Proof: restrict the minimizer inequality to the feasible segment from `y` to `x`,
  use the carrier Bregman segment derivative at zero, assemble the scalar prox
  derivative, and apply the one-sided derivative sign condition.
Source: Mathlib convex segment calculus and SOptLib carrier Bregman derivative APIs
Used in: stochastic block mirror descent block prox-step optimality and mirror
  descent prox-step first-order conditions
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem prox_variational_inequality_of_isMinOn_linear_bregman
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (hX_convex : Convex ℝ X)
    (nu : {x : E // x ∈ X} → ℝ) (nuAmbient : E → ℝ)
    (grad : {x : E // x ∈ X} → E)
    (z y x : {x : E // x ∈ X}) (ζ : E)
    (hnu_eq_segment :
      ∀ t (ht : t ∈ Set.Icc (0 : ℝ) 1),
        nu ⟨AffineMap.lineMap y.1 x.1 t, hX_convex.lineMap_mem y.2 x.2 ht⟩ =
          nuAmbient (AffineMap.lineMap y.1 x.1 t))
    (hnu_diff : DifferentiableWithinAt ℝ nuAmbient X y.1)
    (hgrad_apply :
      (fderivWithin ℝ nuAmbient X y.1) (x.1 - y.1) =
        ⟪grad y, x.1 - y.1⟫_ℝ)
    (hmin :
      IsMinOn
        (fun u : {x : E // x ∈ X} =>
          ⟪ζ, u.1⟫_ℝ + carrierBregmanDivergence nu grad z u)
        Set.univ y) :
    0 ≤ ⟪ζ + grad y - grad z, x.1 - y.1⟫_ℝ := by
  classical
  let objective : {x : E // x ∈ X} → ℝ := fun u =>
    ⟪ζ, u.1⟫_ℝ + carrierBregmanDivergence nu grad z u
  have hmin_all : ∀ u : {x : E // x ∈ X}, objective y ≤ objective u := by
    simpa [objective, isMinOn_univ_iff] using hmin
  let segment : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → {x : E // x ∈ X} :=
    fun t ht =>
      ⟨AffineMap.lineMap y.1 x.1 t,
        hX_convex.lineMap_mem y.2 x.2 ht⟩
  have hsegment_min :
      ∀ t (ht : t ∈ Set.Icc (0 : ℝ) 1), objective y ≤ objective (segment t ht) := by
    intro t ht
    exact hmin_all (segment t ht)
  let d : E := x.1 - y.1
  let β : ℝ → ℝ := fun t =>
    if ht : t ∈ Set.Icc (0 : ℝ) 1 then
      carrierBregmanDivergence nu grad z (segment t ht) -
        carrierBregmanDivergence nu grad z y
    else 0
  have hβderiv :
      HasDerivWithinAt β ⟪grad y - grad z, d⟫_ℝ (Set.Icc (0 : ℝ) 1) 0 := by
    let s : Set ℝ := Set.Icc (0 : ℝ) 1
    let line : ℝ → E := fun t => AffineMap.lineMap y.1 x.1 t
    have hmaps : Set.MapsTo line s X := by
      intro t ht
      exact hX_convex.lineMap_mem y.2 x.2 ht
    have hline_deriv : HasDerivWithinAt line d s 0 := by
      simpa [line, d] using
        (AffineMap.hasDerivWithinAt_lineMap (a := y.1) (b := x.1)
          (s := s) (x := (0 : ℝ)))
    have hνseg : HasDerivWithinAt (fun t => nuAmbient (line t))
        ((fderivWithin ℝ nuAmbient X y.1) d) s 0 := by
      simpa [Function.comp_def] using
        hnu_diff.hasFDerivWithinAt.comp_hasDerivWithinAt_of_eq 0 hline_deriv hmaps
          (by simp [line])
    have hνseg' : HasDerivWithinAt (fun t => nuAmbient (line t))
        ⟪grad y, d⟫_ℝ s 0 := by
      simpa [d, hgrad_apply] using hνseg
    have hlin : HasDerivWithinAt (fun t : ℝ => t * ⟪grad z, d⟫_ℝ)
        ⟪grad z, d⟫_ℝ s 0 := by
      simpa using (hasDerivWithinAt_id (x := (0 : ℝ)) (s := s)).mul_const
        ⟪grad z, d⟫_ℝ
    have hderiv_expr : HasDerivWithinAt
        (fun t : ℝ => (nuAmbient (line t) - nuAmbient y.1) -
          t * ⟪grad z, d⟫_ℝ)
        (⟪grad y, d⟫_ℝ - ⟪grad z, d⟫_ℝ) s 0 := by
      exact (hνseg'.sub_const (nuAmbient y.1)).sub hlin
    have heq : ∀ t ∈ s, β t =
        (fun t : ℝ => (nuAmbient (line t) - nuAmbient y.1) -
          t * ⟪grad z, d⟫_ℝ) t := by
      intro t ht
      have htI : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [s] using ht
      have hseg_sub : (AffineMap.lineMap y.1 x.1 t) - y.1 = t • d := by
        simp [d, AffineMap.lineMap_apply_module']
      have hnu_line : nu ⟨AffineMap.lineMap y.1 x.1 t,
          hX_convex.lineMap_mem y.2 x.2 htI⟩ = nuAmbient (line t) := by
        simpa [line] using hnu_eq_segment t htI
      have hnu_y : nu y = nuAmbient y.1 := by
        have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
        have hbase := hnu_eq_segment 0 h0
        simpa [AffineMap.lineMap_apply_module'] using hbase
      have hinner_diff :
          ⟪grad z, (AffineMap.lineMap y.1 x.1 t) - z.1⟫_ℝ -
              ⟪grad z, y.1 - z.1⟫_ℝ =
            t * ⟪grad z, d⟫_ℝ := by
        calc
          ⟪grad z, (AffineMap.lineMap y.1 x.1 t) - z.1⟫_ℝ -
              ⟪grad z, y.1 - z.1⟫_ℝ =
              ⟪grad z,
                ((AffineMap.lineMap y.1 x.1 t) - z.1) - (y.1 - z.1)⟫_ℝ := by
            rw [← inner_sub_right]
          _ = ⟪grad z, (AffineMap.lineMap y.1 x.1 t) - y.1⟫_ℝ := by
            congr 1
            abel
          _ = ⟪grad z, t • d⟫_ℝ := by
            rw [hseg_sub]
          _ = t * ⟪grad z, d⟫_ℝ := by
            simp [inner_smul_right]
      calc
        β t = carrierBregmanDivergence nu grad z (segment t htI) -
            carrierBregmanDivergence nu grad z y := by
          dsimp [β]
          rw [dif_pos htI]
        _ = (nuAmbient (line t) - nuAmbient y.1) - t * ⟪grad z, d⟫_ℝ := by
          rw [carrierBregmanDivergence_def, carrierBregmanDivergence_def,
            hnu_line, hnu_y]
          rw [← hinner_diff]
          ring
    have hβ : HasDerivWithinAt β
        (⟪grad y, d⟫_ℝ - ⟪grad z, d⟫_ℝ) s 0 := by
      exact hderiv_expr.congr heq (heq 0 (by norm_num [s]))
    have hval : ⟪grad y, d⟫_ℝ - ⟪grad z, d⟫_ℝ =
        ⟪grad y - grad z, d⟫_ℝ := by
      rw [inner_sub_left]
    simpa [s, hval] using hβ
  let φ : ℝ → ℝ := fun t => (1 : ℝ) * t * ⟪ζ, d⟫_ℝ + β t + (1 : ℝ) * t * 0
  have hφmin : ∀ t ∈ Set.Icc (0 : ℝ) 1, φ 0 ≤ φ t := by
    intro t ht
    have hseg := hsegment_min t ht
    have hline_sub : (segment t ht).1 - y.1 = t • d := by
      simp [segment, d, AffineMap.lineMap_apply_module']
    have hinner :
        ⟪ζ, (segment t ht).1⟫_ℝ - ⟪ζ, y.1⟫_ℝ =
          t * ⟪ζ, d⟫_ℝ := by
      calc
        ⟪ζ, (segment t ht).1⟫_ℝ - ⟪ζ, y.1⟫_ℝ =
            ⟪ζ, (segment t ht).1 - y.1⟫_ℝ := by
              rw [inner_sub_right]
        _ = t * ⟪ζ, d⟫_ℝ := by
              rw [hline_sub, inner_smul_right]
    have hβ_eval :
        β t = carrierBregmanDivergence nu grad z (segment t ht) -
          carrierBregmanDivergence nu grad z y := by
      dsimp [β]
      rw [dif_pos ht]
    have hφ0 : φ 0 = 0 := by
      have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
      have hseg0 : segment 0 h0 = y := by
        apply Subtype.ext
        simp [segment, AffineMap.lineMap_apply_module']
      have hβ0 : β 0 = 0 := by
        dsimp [β]
        rw [dif_pos h0, hseg0]
        ring
      simp [φ, hβ0]
    rw [hφ0]
    dsimp [objective] at hseg
    dsimp [φ]
    rw [hβ_eval]
    nlinarith
  have hφderiv :
      HasDerivWithinAt φ
        ((1 : ℝ) * ⟪ζ, d⟫_ℝ + ⟪grad y - grad z, d⟫_ℝ + (1 : ℝ) * 0)
        (Set.Icc (0 : ℝ) 1) 0 := by
    simpa [φ] using
      prox_majorant_hasDerivWithinAt_zero β ζ d (grad y - grad z) (1 : ℝ) 0 hβderiv
  have hnonneg :
      0 ≤ (1 : ℝ) * ⟪ζ, d⟫_ℝ + ⟪grad y - grad z, d⟫_ℝ + (1 : ℝ) * 0 :=
    right_derivative_nonneg_of_min_on_Icc hφderiv hφmin
  simpa [d, inner_add_left, inner_sub_left, add_assoc, sub_eq_add_neg] using hnonneg

/-- The endpoint rule gives a measurable linear-minimization oracle on a real
closed interval.

For a linear coefficient `g`, the selector chooses the left endpoint when
`0 ≤ g` and the right endpoint when `g < 0`. This realizes the minimum of the
one-dimensional linear model over `[a,b]` and is measurable as an `ite` of
constant functions over a measurable half-line.

Layer: Model | Concept: Oracle
Proof: construct the selector by a sign split on the coefficient. Endpoint
  feasibility follows from `a ≤ b`; minimality follows by multiplying interval
  inequalities by nonnegative or nonpositive scalars; measurability is an
  `ite` over the closed half-line `{g | 0 ≤ g}`.
Source: Mathlib ordered real algebra, closed interval membership, and
  measurable half-line APIs
Used in: stochastic conditional-gradient concrete interval LMO construction
  for one-dimensional examples and counterexamples
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
noncomputable def linearMinimizationOracle_Icc_real (a b : ℝ) (hab : a ≤ b) :
    SOptLib.LinearMinimizationOracle ℝ (Set.Icc a b) where
  toFun := fun g => if 0 ≤ g then a else b
  mem := by
    intro g
    by_cases hg : 0 ≤ g
    · simp [hg, hab]
    · simp [hg, hab]
  is_argmin := by
    intro g x hx
    by_cases hg : 0 ≤ g
    · simp [hg, real_inner_eq_re_inner, RCLike.inner_apply, mul_comm]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hx.1 hg
    · have hglt : g < 0 := lt_of_not_ge hg
      have hgle : g ≤ 0 := le_of_lt hglt
      simp [hg, real_inner_eq_re_inner, RCLike.inner_apply, mul_comm]
      simpa [mul_comm] using mul_le_mul_of_nonpos_left hx.2 hgle
  measurable := by
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_Ici

@[simp] theorem linearMinimizationOracle_Icc_real_def
    (a b : ℝ) (hab : a ≤ b) (g : ℝ) :
    (linearMinimizationOracle_Icc_real a b hab).toFun g =
      if 0 ≤ g then a else b := rfl

@[simp] theorem linearMinimizationOracle_Icc_real_apply
    (a b : ℝ) (hab : a ≤ b) (g : ℝ) :
    linearMinimizationOracle_Icc_real a b hab g =
      if 0 ≤ g then a else b := rfl

@[simp] theorem linearMinimizationOracle_Icc_real_apply_of_nonneg
    (a b : ℝ) (hab : a ≤ b) {g : ℝ} (hg : 0 ≤ g) :
    linearMinimizationOracle_Icc_real a b hab g = a := by
  simp [hg]

@[simp] theorem linearMinimizationOracle_Icc_real_apply_of_neg
    (a b : ℝ) (hab : a ≤ b) {g : ℝ} (hg : g < 0) :
    linearMinimizationOracle_Icc_real a b hab g = b := by
  simp [not_le_of_gt hg]

theorem linearMinimizationOracle_Icc_real_mem
    (a b : ℝ) (hab : a ≤ b) (g : ℝ) :
    linearMinimizationOracle_Icc_real a b hab g ∈ Set.Icc a b :=
  (linearMinimizationOracle_Icc_real a b hab).mem g

theorem linearMinimizationOracle_Icc_real_is_argmin
    (a b : ℝ) (hab : a ≤ b) (g x : ℝ) (hx : x ∈ Set.Icc a b) :
    ⟪g, linearMinimizationOracle_Icc_real a b hab g⟫_ℝ ≤ ⟪g, x⟫_ℝ :=
  (linearMinimizationOracle_Icc_real a b hab).is_argmin g x hx

theorem linearMinimizationOracle_Icc_real_mul_le
    (a b : ℝ) (hab : a ≤ b) (g x : ℝ) (hx : x ∈ Set.Icc a b) :
    g * linearMinimizationOracle_Icc_real a b hab g ≤ g * x := by
  simpa [real_inner_eq_re_inner, RCLike.inner_apply, mul_comm]
    using linearMinimizationOracle_Icc_real_is_argmin a b hab g x hx

theorem linearMinimizationOracle_Icc_real_measurable
    (a b : ℝ) (hab : a ≤ b) :
    Measurable (linearMinimizationOracle_Icc_real a b hab).toFun :=
  (linearMinimizationOracle_Icc_real a b hab).measurable

-- Batch 5 promoted staging declarations

-- From Staging/wolfeGap_eq_zero_of_diameter_eq_zero.lean
open scoped InnerProductSpace

namespace SOptLib.ConditionalGradient

-- Generalization plan (G0):
-- G0.1 naming: wolfeGap_eq_zero_of_diameter_eq_zero
-- G0.2 typeclass level used:
--   E: [NormedAddCommGroup E] [InnerProductSpace ℝ E]; the proof uses
--      subtraction, norms, and the real inner product in the Wolfe-gap value,
--      with no finite-dimensionality, completeness, compactness, or topology.
--   measure: none; this is the deterministic zero-diameter stationarity fact,
--      leaving any Dirac or expectation convention to the algorithm file.
--   convexity: none; once a feasible-pair diameter bound is supplied, convexity
--      and compactness play no role in the proof.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient, proving the degenerate
--      zero-diameter branch has zero selected Wolfe gap before simplifying the
--      Dirac expected-gap convention.
--   2. finite-sum nonconvex conditional gradient, discharging any compact
--      singleton-feasible-set Wolfe-gap term before weighted-sum bounds.
-- G0.4 search trace:
--   queries: ["Wolfe gap diameter",
--     "inner product distance zero set diameter"]
--   top hits: ["degenerateExpectedWolfeGap_eq_zero_of_diameter_eq_zero",
--     "SOptLib.ConditionalGradient.wolfeGap_le_linearMinimizer_model_plus_gradient_error_mul_diameter",
--     "SOptLib.ConditionalGradient.wolfeGap_le_maxLinearModel_add_estimatorError_mul_diameter",
--     "expectedWolfeGapExtension_eq_zero_of_diameter_eq_zero",
--     "Metric.diam_eq_zero_iff"]
--   coverage: partial — existing project hits are paper-local expectation
--      theorems or upper bounds, while Mathlib diameter-zero facts do not
--      mention selected conditional-gradient Wolfe gaps.
-- G0.4 not-a-thin-wrapper rationale: the theorem packages the reusable
--   zero-diameter-to-zero-displacement argument and folds the resulting
--   vanishing displacement into the concrete selected Wolfe-gap value.
-- G0.5 structural-content rationale: the statement talks about the concrete
--   `wolfeGap` def and a mathematical diameter bound, not an abstract gap
--   function with a formula-equality hypothesis.
-- G0.5c thin-wrapper self-detect: clean — body uses the diameter bound,
--   norm-zero equivalence, and Wolfe-gap expansion; it is not a direct
--   single-Mathlib or SOptLib alias.
-- G0.5d minimal-hypothesis check: all already minimal; the proof needs only
--   the feasible membership of the current point, the selected maximizer's
--   subtype membership, and the supplied feasible-pair diameter bound.

/-- A selected Wolfe gap is zero on a feasible set with zero diameter.

If every feasible pair has distance bounded by a diameter parameter and that
diameter is zero, then the selected feasible maximizer in the Wolfe-gap value
coincides with the current feasible point, so the gap vanishes.

Layer: Layer0 | Gap: Level 0 (zero-diameter Wolfe-gap cancellation)
Proof: apply the feasible-pair diameter bound to the current point and the
  selected Wolfe maximizer, turn zero norm into equality of the displacement,
  and unfold the selected Wolfe-gap value.
Source: Frank-Wolfe conditional-gradient Wolfe-gap stationarity certificates
  and Mathlib norm-zero algebra in real Hilbert spaces
Used in: stochastic and finite-sum conditional-gradient degenerate feasible-set
  branches before simplifying expected Wolfe-gap displays
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem wolfeGap_eq_zero_of_diameter_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (grad : E → E)
    (maximizer : E → {y : E // y ∈ X}) (x : E) (diam : ℝ)
    (diameter_bound :
      ∀ u v : E, u ∈ X → v ∈ X → ‖u - v‖ ≤ diam)
    (hdiam : diam = 0) (hx : x ∈ X) :
    wolfeGap grad maximizer x = 0 := by
  let y : {y : E // y ∈ X} := maximizer x
  have hdist_le : ‖x - (y : E)‖ ≤ 0 := by
    simpa [hdiam, y] using diameter_bound x (y : E) hx y.property
  have hdist : ‖x - (y : E)‖ = 0 :=
    le_antisymm hdist_le (norm_nonneg _)
  have hsub : x - (y : E) = 0 := norm_eq_zero.mp hdist
  simp [wolfeGap, y, hsub]

end SOptLib.ConditionalGradient

-- From Staging/max_linear_model_le_inner_sub_linearMinimizer.lean
open scoped InnerProductSpace

-- Generalization plan (G0):
-- G0.1 naming: max_linear_model_le_inner_sub_linearMinimizer (orig was:
--   maxLinModel_le_inner_sub_lmo); the name describes the conditional-gradient
--   max-linear model comparison against a linear minimizer, with no paper-local
--   section, theorem, or algorithm markers.
-- G0.2 typeclass level used:
--   E: [NormedAddCommGroup E] [InnerProductSpace ℝ E]; the proof uses only
--      subtraction, real inner products, and ordered real algebra, with no
--      finite-dimensional, completeness, compactness, or topology assumptions.
--   measure: none; this is a deterministic conditional-gradient oracle
--      comparison.
--   convexity: none; once the selected model maximizer and linear minimizer
--      certificate are supplied, convexity is not used.
-- G0.3 reusability — could instantiate:
--   1. stochastic nonconvex conditional gradient, when replacing the selected
--      estimator max-linear model by the realized LMO direction in descent.
--   2. finite-sum conditional-gradient sliding, when comparing a selected
--      linearized gap model against an independently measurable LMO selector.
-- G0.4 search trace:
--   queries: ["linear minimizer model gap", "inner product argmin set bound"]
--   top hits: ["wolfeGap_le_linearMinimizer_model_plus_gradient_error_mul_diameter",
--     "wolfeGap_le_maxLinearModel_add_estimatorError_mul_diameter",
--     "linearMinimizer_exists_of_isCompact",
--     "exists_linearModelMaximizer_on_compact",
--     "prox_variational_inequality_of_isMinOn_linear_bregman"]
--   coverage: partial — existing Wolfe-gap bounds use an LMO term downstream,
--     and compact-existence lemmas provide selectors; none state the direct
--     max-linear-model-to-linear-minimizer comparison for an arbitrary selected
--     model maximizer and pointwise LMO argmin certificate.
-- G0.4 not-a-thin-wrapper rationale: the theorem adds the reusable invariant
--   linking the named `maxLinearModel` value to a separate linear minimizer
--   certificate, rather than re-exporting an existing compactness or Wolfe-gap
--   theorem.
-- G0.5 structural-content rationale: the statement uses the concrete
--   `maxLinearModel` object and the exact pointwise LMO optimality property
--   consumed by conditional-gradient descent proofs.
-- G0.5c thin-wrapper self-detect: clean — body has model unfolding, LMO
--   specialization at the selected maximizer, and inner-product algebra, not a
--   direct single Mathlib or SOptLib alias.
-- G0.5d minimal-hypothesis check: all already minimal; the only hypothesis is
--   the pointwise linear-minimizer comparison used at the selected maximizer.

/-- A selected max-linear model is bounded by the gap at a linear minimizer.

For a conditional-gradient max-linear model realized by a feasible maximizer
selector, any pointwise linear minimizer for the same model vector gives an
upper bound on the selected model value.

Layer: Layer0 | Gap: Level 0 (linear-minimizer comparison for max-linear models)
Proof: specialize the linear-minimizer argmin certificate to the selected model
  maximizer, unfold the named `maxLinearModel`, and rearrange the two
  inner-product subtraction formulas by ordered real algebra.
Source: Frank-Wolfe conditional-gradient linear-oracle calculus in real Hilbert
  spaces
Used in: stochastic and finite-sum conditional-gradient descent proofs replacing
  a selected stochastic max-linear model by the realized LMO direction
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem max_linear_model_le_inner_sub_linearMinimizer
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (maximizer : E → E → {y : E // y ∈ X})
    (linearMinimizer : E → E)
    (linearMinimizer_is_argmin :
      ∀ g z : E, z ∈ X → ⟪g, linearMinimizer g⟫_ℝ ≤ ⟪g, z⟫_ℝ)
    (x G : E) :
    SOptLib.ConditionalGradient.maxLinearModel maximizer x G ≤
      ⟪G, x - linearMinimizer G⟫_ℝ := by
  classical
  let y : {y : E // y ∈ X} := maximizer x G
  have hlmo : ⟪G, linearMinimizer G⟫_ℝ ≤ ⟪G, (y : E)⟫_ℝ :=
    linearMinimizer_is_argmin G (y : E) y.property
  simp [SOptLib.ConditionalGradient.maxLinearModel, inner_sub_right]
  linarith

namespace SOptLib

/-- A minimizer of a convex term plus two weighted Bregman divergences satisfies
the corresponding two-anchor variational inequality.

For an abstract Bregman-like kernel `V`, the proof only needs its directional
derivative along feasible segments from the minimizer. The two anchor centers do
not need to be feasible when the segment derivative law is available.

Layer: Layer0 | Gap: Level 1 (two-anchor Bregman argmin variational inequality)
Proof: restrict the global argmin inequality to the feasible segment from the
  minimizer to a comparison point, bound the convex term on that segment, assemble
  the right derivative at zero, and apply the one-sided derivative sign condition.
Source: Mathlib convex segment calculus and one-dimensional within-derivative APIs
Used in: stochastic accelerated gradient descent two-anchor prox first-order condition
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem two_bregman_argmin_variational_inequality_no_center_mem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (p : E → ℝ) (V : E → E → ℝ) (grad : E → E)
    (hp_convex : ConvexOn ℝ X p)
    {xTilde yTilde uHat : E} {mu1 mu2 : ℝ}
    (huHat : uHat ∈ X)
    (hV_segment_deriv :
      ∀ (a z u : E), z ∈ X →
        let d : E := u - z
        let β : ℝ → ℝ := fun t =>
          if _ht : t ∈ Set.Icc (0 : ℝ) 1 then
            V a (AffineMap.lineMap z u t) - V a z
          else 0
        HasDerivWithinAt β
          ⟪grad z - grad a, d⟫_ℝ
          (Set.Icc (0 : ℝ) 1) 0)
    (h_opt :
      ∀ u, u ∈ X →
        p uHat + mu1 * V xTilde uHat + mu2 * V yTilde uHat ≤
          p u + mu1 * V xTilde u + mu2 * V yTilde u) :
    ∀ u, u ∈ X →
      0 ≤ p u - p uHat +
        mu1 * ⟪grad uHat - grad xTilde, u - uHat⟫_ℝ +
        mu2 * ⟪grad uHat - grad yTilde, u - uHat⟫_ℝ := by
  intro u hu
  classical
  let d : E := u - uHat
  let s : Set ℝ := Set.Icc (0 : ℝ) 1
  let βx : ℝ → ℝ := fun t =>
    if ht : t ∈ Set.Icc (0 : ℝ) 1 then
      V xTilde (AffineMap.lineMap uHat u t) - V xTilde uHat
    else 0
  let βy : ℝ → ℝ := fun t =>
    if ht : t ∈ Set.Icc (0 : ℝ) 1 then
      V yTilde (AffineMap.lineMap uHat u t) - V yTilde uHat
    else 0
  let φ : ℝ → ℝ := fun t =>
    t * (p u - p uHat) + mu1 * βx t + mu2 * βy t
  have hβxderiv : HasDerivWithinAt βx
      ⟪grad uHat - grad xTilde, d⟫_ℝ s 0 := by
    simpa [βx, d, s] using
      hV_segment_deriv xTilde uHat u huHat
  have hβyderiv : HasDerivWithinAt βy
      ⟪grad uHat - grad yTilde, d⟫_ℝ s 0 := by
    simpa [βy, d, s] using
      hV_segment_deriv yTilde uHat u huHat
  have hpderiv : HasDerivWithinAt (fun t : ℝ => t * (p u - p uHat))
      (p u - p uHat) s 0 := by
    simpa using (hasDerivWithinAt_id (x := (0 : ℝ)) (s := s)).mul_const
      (p u - p uHat)
  have hφderiv : HasDerivWithinAt φ
      (p u - p uHat +
        mu1 * ⟪grad uHat - grad xTilde, d⟫_ℝ +
        mu2 * ⟪grad uHat - grad yTilde, d⟫_ℝ) s 0 := by
    have hxmul : HasDerivWithinAt (fun t : ℝ => mu1 * βx t)
        (mu1 * ⟪grad uHat - grad xTilde, d⟫_ℝ) s 0 := by
      simpa using hβxderiv.const_mul mu1
    have hymul : HasDerivWithinAt (fun t : ℝ => mu2 * βy t)
        (mu2 * ⟪grad uHat - grad yTilde, d⟫_ℝ) s 0 := by
      simpa using hβyderiv.const_mul mu2
    simpa [φ, add_assoc] using (hpderiv.add hxmul).add hymul
  have hφmin : ∀ t ∈ s, φ 0 ≤ φ t := by
    intro t ht
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [s] using ht
    rcases Set.mem_Icc.mp htI with ⟨ht0, ht1⟩
    let w : E := AffineMap.lineMap uHat u t
    have hw : w ∈ X := by
      simpa [w] using hp_convex.1.lineMap_mem huHat hu htI
    have hline_conv :
        w = (1 - t) • uHat + t • u := by
      simp [w, AffineMap.lineMap_apply_module']
      module
    have hpseg : p w - p uHat ≤ t * (p u - p uHat) := by
      have hconv :=
        hp_convex.2 huHat hu (sub_nonneg.mpr ht1) ht0 (by ring)
      rw [← hline_conv] at hconv
      have hconv' : p w ≤ (1 - t) * p uHat + t * p u := by
        simpa [smul_eq_mul] using hconv
      nlinarith
    have hmin := h_opt w hw
    have hFdiff :
        0 ≤ (p w - p uHat) +
          mu1 * (V xTilde w - V xTilde uHat) +
          mu2 * (V yTilde w - V yTilde uHat) := by
      nlinarith
    have hβx_eval : βx t = V xTilde w - V xTilde uHat := by
      dsimp [βx, w]
      rw [if_pos htI]
    have hβy_eval : βy t = V yTilde w - V yTilde uHat := by
      dsimp [βy, w]
      rw [if_pos htI]
    have hφ0 : φ 0 = 0 := by
      simp [φ, βx, βy, AffineMap.lineMap_apply_module']
    have hupper :
        (p w - p uHat) +
          mu1 * (V xTilde w - V xTilde uHat) +
          mu2 * (V yTilde w - V yTilde uHat) ≤ φ t := by
      dsimp [φ]
      rw [hβx_eval, hβy_eval]
      nlinarith
    rw [hφ0]
    exact le_trans hFdiff hupper
  have hnonneg := right_derivative_nonneg_of_min_on_Icc hφderiv hφmin
  simpa [d] using hnonneg

/-- A minimizer of a convex term plus two weighted Bregman divergences satisfies
the corresponding two-anchor descent inequality.

For an abstract Bregman-like kernel `V`, the proof only needs its directional
derivative along feasible segments and its three-point identity. This lets the
same theorem apply to carrier Bregman divergences, mirror-descent prox kernels,
and accelerated two-anchor prox subproblems.

Layer: Layer0 | Gap: Level 1 (two-anchor Bregman argmin descent)
Proof: restrict the global argmin inequality to the feasible segment from the
  minimizer to the comparison point, take the right derivative at zero, then
  rewrite the two gradient pairings with the supplied Bregman three-point laws.
Source: Mathlib convex segment calculus, one-sided derivative first-order
  conditions, and Bregman three-point algebra
Used in: stochastic accelerated gradient descent two-anchor prox inequality
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem two_bregman_argmin_descent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (p : E → ℝ) (V : E → E → ℝ) (grad : E → E)
    (hp_convex : ConvexOn ℝ X p)
    {xTilde yTilde uHat : E} {mu1 mu2 : ℝ}
    (huHat : uHat ∈ X)
    (hmu1 : 0 ≤ mu1)
    (hmu2 : 0 ≤ mu2)
    (hV_segment_deriv :
      ∀ (a z u : E), z ∈ X →
        let d : E := u - z
        let β : ℝ → ℝ := fun t =>
          if _ht : t ∈ Set.Icc (0 : ℝ) 1 then
            V a (AffineMap.lineMap z u t) - V a z
          else 0
        HasDerivWithinAt β
          ⟪grad z - grad a, d⟫_ℝ
          (Set.Icc (0 : ℝ) 1) 0)
    (hV_three :
      ∀ a b c : E,
        V a c = V a b + ⟪grad b - grad a, c - b⟫_ℝ + V b c)
    (h_opt :
      ∀ u, u ∈ X →
        p uHat + mu1 * V xTilde uHat + mu2 * V yTilde uHat ≤
          p u + mu1 * V xTilde u + mu2 * V yTilde u) :
    ∀ u, u ∈ X →
      p uHat + mu1 * V xTilde uHat + mu2 * V yTilde uHat ≤
        p u + mu1 * V xTilde u + mu2 * V yTilde u -
          (mu1 + mu2) * V uHat u := by
  intro u hu
  have hvar :=
    two_bregman_argmin_variational_inequality_no_center_mem
      X p V grad hp_convex huHat hV_segment_deriv h_opt u hu
  have h3x := hV_three xTilde uHat u
  have h3y := hV_three yTilde uHat u
  nlinarith


-- Promoted from Staging/seminorm_displacement_le_dual_gap_of_paired_variational.lean
open scoped InnerProductSpace

-- Generalization plan (G0):
-- concept/name: seminorm displacement controlled by paired variational
--   inequalities; orig was prox_variational_pairing_to_primal_dual_bound.
-- generality used: deterministic real Hilbert-space evaluation geometry with
--   an abstract carrier type, gradient map, primal seminorm, dual gauge,
--   positive real stepsize, two pointwise variational inequalities, pointwise
--   strong monotonicity, dual-gauge nonnegativity, and support bound; no
--   measure, convexity, smoothness, or algorithm update hypotheses.
-- portable call pattern: mirror descent, block mirror descent, mirror-prox,
--   and proximal-gradient stability proofs after deriving variational
--   inequalities at two selected prox points; the carrier, gradients, oracle
--   vectors, seminorm, and dual gauge vary while the seminorm displacement
--   bound has the same shape.
-- counterargument checked: this is not paper-local traceability or a
--   caller-side expression; it is the reusable cancellation-and-absorption
--   algebra before any paper-specific metric conversion. Existing prox
--   stability lemmas are close but either use ambient norms or already include
--   a metric-control wrapper, not this portable seminorm core.
-- coverage search: rg/lean_search queries "seminorm displacement dual gap
--   variational strong monotonicity", "prox variational distance dual
--   gradient", and catalog entries around prox stability found
--   SOptLib.proxStep_state_oracle_distance_bound and the staged
--   prox_distance_le_dual_oracle_gap_add_grad_gap_of_variational; coverage is
--   partial, and this differentiates by extracting the pre-metric seminorm
--   displacement theorem. LeanSearch for the same concept timed out.
-- minimal hypotheses: global setup fields were reduced to pointwise
--   variational, strong-monotonicity, dual nonnegativity, and support
--   assumptions; finite-dimensionality and metric control are caller-side
--   producers, not hypotheses of this theorem.

/-- Paired variational inequalities control the selected-point seminorm displacement.

For two candidate points evaluated in a real Hilbert space, the two variational
inequalities cancel the prox-gradient terms up to a strong-monotonicity
residual. A support-dual estimate then bounds the oracle and base-gradient
pairings, and division by the nonzero seminorm displacement gives the stated
dual-gap bound.

Layer: Layer0 | Gap: Level 1 (paired variational seminorm displacement)
Proof: add the paired variational inequalities, rewrite them as oracle,
  strong-monotonicity, and base-gradient terms, bound the two pairings by the
  supplied support dual gauge, then split on zero seminorm displacement.
Source: Mathlib real inner-product algebra, seminorm support-dual estimates,
  and monotone-operator prox stability arguments
Used in: stochastic block mirror descent selected-block prox stability before
  metric conversion and continuity
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem seminorm_displacement_le_dual_gap_of_paired_variational
    {P E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (eval grad : P → E) (primalNorm : Seminorm ℝ E) (dualGauge : E → ℝ)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (z₁ z₂ y₁ y₂ : P) (g₁ g₂ : E)
    (hdual_nonneg : ∀ ζ : E, 0 ≤ dualGauge ζ)
    (hsupport : ∀ ζ d : E, |⟪ζ, d⟫_ℝ| ≤ dualGauge ζ * primalNorm d)
    (hvi₁ :
      0 ≤ ⟪g₁, eval y₂ - eval y₁⟫_ℝ +
        gamma⁻¹ * ⟪grad y₁ - grad z₁, eval y₂ - eval y₁⟫_ℝ)
    (hvi₂ :
      0 ≤ ⟪g₂, eval y₁ - eval y₂⟫_ℝ +
        gamma⁻¹ * ⟪grad y₂ - grad z₂, eval y₁ - eval y₂⟫_ℝ)
    (hstrong :
      primalNorm (eval y₁ - eval y₂) ^ 2 ≤
        ⟪grad y₁ - grad y₂, eval y₁ - eval y₂⟫_ℝ) :
    primalNorm (eval y₁ - eval y₂) ≤
      gamma * dualGauge (g₁ - g₂) + dualGauge (grad z₁ - grad z₂) := by
  let d : E := eval y₁ - eval y₂
  let pnorm : ℝ := primalNorm d
  let gradGap : E := grad z₁ - grad z₂
  have hp_nonneg : 0 ≤ pnorm := by
    exact apply_nonneg primalNorm d
  have hstrong' :
      pnorm ^ 2 ≤ ⟪grad y₁ - grad y₂, d⟫_ℝ := by
    simpa [pnorm, d] using hstrong
  have hsum :
      0 ≤
        (⟪g₁, eval y₂ - eval y₁⟫_ℝ +
          gamma⁻¹ * ⟪grad y₁ - grad z₁, eval y₂ - eval y₁⟫_ℝ) +
        (⟪g₂, eval y₁ - eval y₂⟫_ℝ +
          gamma⁻¹ * ⟪grad y₂ - grad z₂, eval y₁ - eval y₂⟫_ℝ) :=
    add_nonneg hvi₁ hvi₂
  have hsum_rewrite :
      (⟪g₁, eval y₂ - eval y₁⟫_ℝ +
          gamma⁻¹ * ⟪grad y₁ - grad z₁, eval y₂ - eval y₁⟫_ℝ) +
        (⟪g₂, eval y₁ - eval y₂⟫_ℝ +
          gamma⁻¹ * ⟪grad y₂ - grad z₂, eval y₁ - eval y₂⟫_ℝ)
        =
        ⟪g₂ - g₁, d⟫_ℝ -
          gamma⁻¹ * ⟪grad y₁ - grad y₂, d⟫_ℝ +
          gamma⁻¹ * ⟪gradGap, d⟫_ℝ := by
    dsimp [d, gradGap]
    simp [inner_sub_left, inner_sub_right]
    ring
  have hsum' :
      0 ≤
        ⟪g₂ - g₁, d⟫_ℝ -
          gamma⁻¹ * ⟪grad y₁ - grad y₂, d⟫_ℝ +
          gamma⁻¹ * ⟪gradGap, d⟫_ℝ := by
    simpa [hsum_rewrite] using hsum
  have hquad :
      pnorm ^ 2 ≤ gamma * ⟪g₂ - g₁, d⟫_ℝ + ⟪gradGap, d⟫_ℝ := by
    have htmp :
        gamma⁻¹ * pnorm ^ 2 ≤
          ⟪g₂ - g₁, d⟫_ℝ + gamma⁻¹ * ⟪gradGap, d⟫_ℝ := by
      have hinv_nonneg : 0 ≤ gamma⁻¹ := inv_nonneg.mpr (le_of_lt hgamma)
      have hstrong_scaled :
          gamma⁻¹ * pnorm ^ 2 ≤
            gamma⁻¹ * ⟪grad y₁ - grad y₂, d⟫_ℝ :=
        mul_le_mul_of_nonneg_left hstrong' hinv_nonneg
      nlinarith [hstrong_scaled, hsum']
    have hscaled := mul_le_mul_of_nonneg_left htmp (le_of_lt hgamma)
    convert hscaled using 1 <;> field_simp [hgamma.ne']
  have hg_inner :
      ⟪g₂ - g₁, d⟫_ℝ ≤ dualGauge (g₁ - g₂) * pnorm := by
    calc
      ⟪g₂ - g₁, d⟫_ℝ ≤ |⟪g₁ - g₂, d⟫_ℝ| := by
        have hneg : ⟪g₂ - g₁, d⟫_ℝ = -⟪g₁ - g₂, d⟫_ℝ := by
          have hsub : g₂ - g₁ = -(g₁ - g₂) := by abel
          rw [hsub, inner_neg_left]
        rw [hneg]
        exact neg_le_abs _
      _ ≤ dualGauge (g₁ - g₂) * pnorm := by
        simpa [pnorm] using hsupport (g₁ - g₂) d
  have hgrad_inner :
      ⟪gradGap, d⟫_ℝ ≤ dualGauge gradGap * pnorm := by
    calc
      ⟪gradGap, d⟫_ℝ ≤ |⟪gradGap, d⟫_ℝ| := le_abs_self _
      _ ≤ dualGauge gradGap * pnorm := by
        simpa [pnorm] using hsupport gradGap d
  let rhs : ℝ := gamma * dualGauge (g₁ - g₂) + dualGauge gradGap
  have hrhs_nonneg : 0 ≤ rhs := by
    dsimp [rhs]
    exact add_nonneg
      (mul_nonneg (le_of_lt hgamma) (hdual_nonneg (g₁ - g₂)))
      (hdual_nonneg gradGap)
  have hp_le : pnorm ≤ rhs := by
    by_cases hpzero : pnorm = 0
    · simpa [hpzero] using hrhs_nonneg
    · have hppos : 0 < pnorm := lt_of_le_of_ne hp_nonneg (Ne.symm hpzero)
      have hquad_rhs : pnorm ^ 2 ≤ rhs * pnorm := by
        dsimp [rhs]
        nlinarith [hquad, hg_inner, hgrad_inner, hgamma]
      have hmul : pnorm * pnorm ≤ rhs * pnorm := by
        simpa [pow_two] using hquad_rhs
      exact le_of_mul_le_mul_right hmul hppos
  simpa [pnorm, d, gradGap, rhs] using hp_le


-- Promoted from Staging/prox_distance_le_dual_oracle_gap_add_grad_gap_of_variational.lean
open scoped InnerProductSpace

-- Generalization plan (G0):
-- concept/name: prox-distance stability from variational inequalities; orig was
--   blockProx_state_oracle_gradient_bound.
-- generality used: deterministic real Hilbert-space carrier geometry with an
--   abstract prox selector, evaluation map, gradient map, primal seminorm, dual
--   gauge, pointwise variational inequalities, strong monotonicity, support
--   bound, and metric-control constant; no measure or convexity hypotheses.
-- portable call pattern: mirror descent, block mirror descent, and mirror-prox
--   proofs after obtaining two same-stepsize prox variational inequalities;
--   prox, eval, gradient, seminorm, dual gauge, and metric-control hypotheses
--   change, while the distance bound conclusion stays the same.
-- counterargument checked: not paper-local traceability or a one-line wrapper;
--   the proof composes variational cancellation, strong monotonicity, dual
--   support estimates, and seminorm-to-metric control. Existing ambient-norm
--   prox stability is close but does not cover seminorm/dual-gauge geometry.
-- coverage search: rg queries "prox state oracle gradient bound",
--   "prox variational distance dual gradient", and LeanSearch query
--   "proximal variational inequalities strong monotonicity dual norm distance
--   bound"; top hits were SOptLib.proxStep_state_oracle_distance_bound,
--   prox_points_dist_le_oracle_dist_add_base_grad_dist_of_variational, and
--   Mathlib Cauchy-Schwarz/dual-bound facts; coverage partial, this strengthens
--   from ambient norm to pointwise seminorm plus abstract support dual gauge.
-- minimal hypotheses: global setup fields were reduced to pointwise
--   variational, strong-monotonicity, dual nonnegativity, support, and metric
--   control assumptions; finite-dimensionality is not in the lemma and is only
--   one possible caller-side way to produce metric control.

/-- Two same-stepsize prox points are controlled by dual oracle and base-gradient gaps.

For an abstract carrier evaluated in a real Hilbert space, two variational
inequalities cancel the prox nonsmooth terms. Strong monotonicity controls the
selected-point seminorm displacement, a support-dual estimate bounds the oracle
and base-gradient pairings, and metric control converts the seminorm estimate to
the carrier distance.

Layer: Layer0 | Gap: Level 1 (seminorm-dual prox-point state-oracle stability)
Proof: add the two variational inequalities, rewrite the result into oracle,
  strong-monotonicity, and base-gradient terms, absorb a positive displacement
  seminorm, and apply the supplied metric-control constant.
Source: Mathlib real inner-product algebra, seminorm support-dual estimates,
  and variational prox stability from mirror-descent analysis
Used in: stochastic block mirror descent selected-block prox stability before
  continuity and finite-time displacement bounds
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem prox_distance_le_dual_oracle_gap_add_grad_gap_of_variational
    {P E : Type*} [PseudoMetricSpace P] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (prox : P → E → P) (eval grad : P → E)
    (primalNorm : Seminorm ℝ E) (dualGauge : E → ℝ)
    (γ : {γ : ℝ // 0 < γ})
    (hmetric :
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ x y : P, dist x y ≤ C * primalNorm (eval x - eval y))
    (hdual_nonneg : ∀ ζ : E, 0 ≤ dualGauge ζ)
    (hsupport : ∀ ζ d : E, |⟪ζ, d⟫_ℝ| ≤ dualGauge ζ * primalNorm d)
    (hvariational :
      ∀ (z : P) (g : E) (u : P),
        0 ≤ ⟪g, eval u - eval (prox z g)⟫_ℝ +
          (γ.1)⁻¹ * ⟪grad (prox z g) - grad z, eval u - eval (prox z g)⟫_ℝ)
    (hstrong :
      ∀ y₁ y₂ : P,
        primalNorm (eval y₁ - eval y₂) ^ 2 ≤
          ⟪grad y₁ - grad y₂, eval y₁ - eval y₂⟫_ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (z₁ z₂ : P) (g₁ g₂ : E),
        dist (prox z₁ g₁) (prox z₂ g₂) ≤
          C * (γ.1 * dualGauge (g₁ - g₂) + dualGauge (grad z₁ - grad z₂)) := by
  rcases hmetric with ⟨C, hCnonneg, hC⟩
  refine ⟨C, hCnonneg, ?_⟩
  intro z₁ z₂ g₁ g₂
  let y₁ : P := prox z₁ g₁
  let y₂ : P := prox z₂ g₂
  let d : E := eval y₁ - eval y₂
  let pnorm : ℝ := primalNorm d
  let gradGap : E := grad z₁ - grad z₂
  have hp_nonneg : 0 ≤ pnorm := by
    exact apply_nonneg primalNorm d
  have hvi₁ := hvariational z₁ g₁ y₂
  have hvi₂ := hvariational z₂ g₂ y₁
  have hstrong' :
      pnorm ^ 2 ≤ ⟪grad y₁ - grad y₂, d⟫_ℝ := by
    simpa [pnorm, d, y₁, y₂] using hstrong y₁ y₂
  have hsum :
      0 ≤
        (⟪g₁, eval y₂ - eval y₁⟫_ℝ +
          (γ.1)⁻¹ * ⟪grad y₁ - grad z₁, eval y₂ - eval y₁⟫_ℝ) +
        (⟪g₂, eval y₁ - eval y₂⟫_ℝ +
          (γ.1)⁻¹ * ⟪grad y₂ - grad z₂, eval y₁ - eval y₂⟫_ℝ) :=
    add_nonneg hvi₁ hvi₂
  have hsum_rewrite :
      (⟪g₁, eval y₂ - eval y₁⟫_ℝ +
          (γ.1)⁻¹ * ⟪grad y₁ - grad z₁, eval y₂ - eval y₁⟫_ℝ) +
        (⟪g₂, eval y₁ - eval y₂⟫_ℝ +
          (γ.1)⁻¹ * ⟪grad y₂ - grad z₂, eval y₁ - eval y₂⟫_ℝ)
        =
        ⟪g₂ - g₁, d⟫_ℝ -
          (γ.1)⁻¹ * ⟪grad y₁ - grad y₂, d⟫_ℝ +
          (γ.1)⁻¹ * ⟪gradGap, d⟫_ℝ := by
    dsimp [d, gradGap]
    simp [inner_sub_left, inner_sub_right]
    ring
  have hsum' :
      0 ≤
        ⟪g₂ - g₁, d⟫_ℝ -
          (γ.1)⁻¹ * ⟪grad y₁ - grad y₂, d⟫_ℝ +
          (γ.1)⁻¹ * ⟪gradGap, d⟫_ℝ := by
    simpa [hsum_rewrite] using hsum
  have hquad :
      pnorm ^ 2 ≤ γ.1 * ⟪g₂ - g₁, d⟫_ℝ + ⟪gradGap, d⟫_ℝ := by
    have hγpos : 0 < γ.1 := γ.2
    have htmp :
        (γ.1)⁻¹ * pnorm ^ 2 ≤
          ⟪g₂ - g₁, d⟫_ℝ + (γ.1)⁻¹ * ⟪gradGap, d⟫_ℝ := by
      have hinv_nonneg : 0 ≤ (γ.1)⁻¹ := inv_nonneg.mpr (le_of_lt hγpos)
      have hstrong_scaled :
          (γ.1)⁻¹ * pnorm ^ 2 ≤
            (γ.1)⁻¹ * ⟪grad y₁ - grad y₂, d⟫_ℝ :=
        mul_le_mul_of_nonneg_left hstrong' hinv_nonneg
      nlinarith [hstrong_scaled, hsum']
    have hscaled := mul_le_mul_of_nonneg_left htmp (le_of_lt hγpos)
    convert hscaled using 1 <;> field_simp [hγpos.ne']
  have hg_inner :
      ⟪g₂ - g₁, d⟫_ℝ ≤ dualGauge (g₁ - g₂) * pnorm := by
    calc
      ⟪g₂ - g₁, d⟫_ℝ ≤ |⟪g₁ - g₂, d⟫_ℝ| := by
        have hneg : ⟪g₂ - g₁, d⟫_ℝ = -⟪g₁ - g₂, d⟫_ℝ := by
          have hsub : g₂ - g₁ = -(g₁ - g₂) := by abel
          rw [hsub, inner_neg_left]
        rw [hneg]
        exact neg_le_abs _
      _ ≤ dualGauge (g₁ - g₂) * pnorm := by
        simpa [pnorm] using hsupport (g₁ - g₂) d
  have hgrad_inner :
      ⟪gradGap, d⟫_ℝ ≤ dualGauge gradGap * pnorm := by
    calc
      ⟪gradGap, d⟫_ℝ ≤ |⟪gradGap, d⟫_ℝ| := le_abs_self _
      _ ≤ dualGauge gradGap * pnorm := by
        simpa [pnorm] using hsupport gradGap d
  let rhs : ℝ := γ.1 * dualGauge (g₁ - g₂) + dualGauge gradGap
  have hrhs_nonneg : 0 ≤ rhs := by
    dsimp [rhs]
    exact add_nonneg
      (mul_nonneg (le_of_lt γ.2) (hdual_nonneg (g₁ - g₂)))
      (hdual_nonneg gradGap)
  have hp_le : pnorm ≤ rhs := by
    by_cases hpzero : pnorm = 0
    · simpa [hpzero] using hrhs_nonneg
    · have hppos : 0 < pnorm := lt_of_le_of_ne hp_nonneg (Ne.symm hpzero)
      have hquad_rhs : pnorm ^ 2 ≤ rhs * pnorm := by
        dsimp [rhs]
        nlinarith [hquad, hg_inner, hgrad_inner, γ.2]
      have hmul : pnorm * pnorm ≤ rhs * pnorm := by
        simpa [pow_two] using hquad_rhs
      exact le_of_mul_le_mul_right hmul hppos
  have hdist_le : dist y₁ y₂ ≤ C * rhs := by
    calc
      dist y₁ y₂ ≤ C * pnorm := by
        simpa [pnorm, d] using hC y₁ y₂
      _ ≤ C * rhs := mul_le_mul_of_nonneg_left hp_le hCnonneg
  simpa [y₁, y₂, gradGap, rhs, mul_add, mul_assoc] using hdist_le


-- Promoted from Staging/inverseStepsizeMirrorProx_variational_inequality_of_isMinOn.lean
-- Generalization plan (G0):
-- concept/name: inverse-stepsize mirror-prox variational inequality; orig was
--   blockProx_variational_inequality, renamed to expose the prox optimality concept.
-- generality used: abstract Hilbert evaluation space `E`, convex carrier `X`,
--   carrier potential `nu`, ambient potential `nuAmbient`, carrier gradient `grad`,
--   base point, prox minimizer, comparison point, oracle vector, and positive
--   stepsize; no measure, filtration, stochastic oracle, finite-dimensionality,
--   compactness, or smoothness beyond the pointwise differentiability used by FOC.
-- portable call pattern: stochastic mirror descent, block mirror descent,
--   nonconvex mirror descent, and accelerated prox recursions call this after
--   proving an inverse-stepsize Bregman subproblem minimizer; the carrier,
--   potential, gradient realization, and oracle vector vary while the inequality
--   has the same form.
-- counterargument checked: not paper-local traceability and not a caller-side
--   expression; it packages a recurring inverse-objective argmin to scaled FOC
--   to inverse-stepsize normalization that otherwise duplicates rescaling and
--   inner-product algebra.
-- coverage search: queries "prox variational inequality argmin inverse stepsize
--   Bregman", "prox_variational_inequality_of_argmin",
--   "prox_variational_inequality_of_isMinOn_linear_bregman", and LeanSearch
--   "convex first order condition minimizer differentiable on set variational
--   inequality"; hits were `prox_variational_inequality_of_argmin` and
--   `prox_variational_inequality_of_isMinOn_linear_bregman`, which cover the
--   scaled-to-unscaled and argmin-to-scaled halves separately but not the
--   combined inverse-stepsize Bregman prox statement.
-- minimal hypotheses: global setup fields are replaced by the pointwise convex
--   carrier, segment potential equality, differentiability at the minimizer,
--   gradient-pairing realization, positive stepsize, and inverse-stepsize
--   `IsMinOn` certificate.

open scoped InnerProductSpace

/-- A minimizer of an inverse-stepsize linear plus Bregman objective satisfies the
inverse-stepsize mirror-prox variational inequality.

For a convex carrier, if `y` minimizes
`u ↦ ⟪g, eval u⟫ + γ⁻¹ * D_ν(z,u)` and the carrier-gradient pairing realizes
the within derivative of the ambient potential at `y`, then every comparison
point `x` satisfies the usual inverse-stepsize prox optimality inequality.

Layer: Layer0 | Gap: Level 1 (inverse-stepsize Bregman prox variational inequality)
Proof: multiply the inverse-stepsize objective comparison by the positive
  stepsize, apply the carrier Bregman minimizer first-order condition, normalize
  the scaled oracle term, and divide back by the stepsize using the existing
  prox variational algebra lemma.
Source: Mathlib convex first-order conditions and SOptLib carrier Bregman FOC APIs
Used in: stochastic mirror descent and block mirror descent prox-step optimality
  before stability and descent estimates
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem inverseStepsizeMirrorProx_variational_inequality_of_isMinOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (hX_convex : Convex ℝ X)
    (nu : {x : E // x ∈ X} → ℝ) (nuAmbient : E → ℝ)
    (grad : {x : E // x ∈ X} → E)
    (z y x : {x : E // x ∈ X}) (g : E) (γ : ℝ) (hγ : 0 < γ)
    (hnu_eq_segment :
      ∀ t (ht : t ∈ Set.Icc (0 : ℝ) 1),
        nu ⟨AffineMap.lineMap y.1 x.1 t, hX_convex.lineMap_mem y.2 x.2 ht⟩ =
          nuAmbient (AffineMap.lineMap y.1 x.1 t))
    (hnu_diff : DifferentiableWithinAt ℝ nuAmbient X y.1)
    (hgrad_apply :
      (fderivWithin ℝ nuAmbient X y.1) (x.1 - y.1) =
        ⟪grad y, x.1 - y.1⟫_ℝ)
    (hmin :
      IsMinOn
        (fun u : {x : E // x ∈ X} =>
          ⟪g, u.1⟫_ℝ + γ⁻¹ * carrierBregmanDivergence nu grad z u)
        Set.univ y) :
    0 ≤
      ⟪g, x.1 - y.1⟫_ℝ +
        γ⁻¹ * ⟪grad y - grad z, x.1 - y.1⟫_ℝ := by
  have hscaled :
      0 ≤ ⟪(γ • g : E) + grad y - grad z, x.1 - y.1⟫_ℝ := by
    have hmin_scaled :
        IsMinOn
          (fun u : {x : E // x ∈ X} =>
            ⟪(γ • g : E), u.1⟫_ℝ + carrierBregmanDivergence nu grad z u)
          Set.univ y := by
      intro u hu
      have hraw := hmin hu
      have hmul :
          γ * (⟪g, y.1⟫_ℝ + γ⁻¹ * carrierBregmanDivergence nu grad z y) ≤
            γ * (⟪g, u.1⟫_ℝ + γ⁻¹ * carrierBregmanDivergence nu grad z u) :=
        mul_le_mul_of_nonneg_left hraw (le_of_lt hγ)
      simpa [inner_smul_left, mul_add, mul_assoc, hγ.ne'] using hmul
    exact
      prox_variational_inequality_of_isMinOn_linear_bregman
        (hX_convex := hX_convex)
        (nu := nu) (nuAmbient := nuAmbient) (grad := grad)
        (z := z) (y := y) (x := x) (ζ := γ • g)
        hnu_eq_segment hnu_diff hgrad_apply hmin_scaled
  have hscaled_arg :
      0 ≤
        γ * ⟪g, x.1 - y.1⟫_ℝ +
          ⟪grad y - grad z, x.1 - y.1⟫_ℝ := by
    convert hscaled using 1
    simp [inner_add_left, inner_sub_left, inner_smul_left]
    ring
  simpa using
    prox_variational_inequality_of_argmin
      (eval := fun u : {x : E // x ∈ X} => u.1)
      (grad := grad) (h := fun _ => (0 : ℝ))
      (x := z) (xp := y) (u := x) (g := g) (γ := γ) hγ
      (by simpa using hscaled_arg)


-- Generalization plan (G0):
-- concept/name: two-center Bregman residual variational inequality from an
--   `IsMinOn` certificate; orig was `convex_bregman_two_center_residual_variational`.
-- generality used: complete real Hilbert space, carrier set `X`, concrete
--   `SOptLib.DistanceGeneratingFunctionOn E X`, convex term `ConvexOn ℝ X p`,
--   pointwise minimizer membership plus `IsMinOn`; no measure/oracle assumptions.
-- portable call pattern: accelerated gradient, accelerated primal-dual, and
--   mirror/prox proofs with convex composite term plus two Bregman anchors;
--   centers, weights, and comparison point vary while the residual conclusion stays.
-- counterargument checked: close to existing abstract
--   `SOptLib.two_bregman_argmin_variational_inequality_no_center_mem`, but this
--   adapter exposes the concrete named DGF Bregman object and discharges the
--   segment-derivative hypothesis from DGF gradient semantics.
-- coverage search: searched "two bregman argmin descent residual variational
--   IsMinOn", "two center bregman segment derivative", and LeanSearch
--   "convex function minimizer Bregman divergence two centers variational
--   inequality"; Mathlib has only generic convex extrema, SOptLib has the
--   abstract kernel variational theorem but no concrete DGF adapter.
-- minimal hypotheses: minimizer membership is separated from `IsMinOn`; no
--   nonnegativity of weights, center membership, finite dimensionality, or
--   probability assumptions are used.

/-- A two-center Bregman minimizer satisfies the residual variational inequality.

For a distance-generating function on a carrier, a minimizer of a convex term
plus two weighted Bregman divergences has nonnegative first-order residual in
the direction of every feasible comparison point.

Layer: Layer0 | Gap: Level 1 (two-center Bregman residual variational inequality)
Proof: instantiate the abstract two-Bregman argmin variational theorem with the
  DGF Bregman kernel, discharging its segment derivative hypothesis by the
  canonical DGF gradient-at-base theorem and the Bregman segment derivative API.
Source: Mathlib convex segment calculus and SOptLib Bregman derivative /
  first-order condition APIs
Used in: accelerated primal-dual and accelerated mirror-descent two-anchor prox
  residual derivations before three-point Bregman rewriting
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/key_lemmas
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem two_center_bregman_residual_variational_of_isMinOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {X : Set E} (ν : SOptLib.DistanceGeneratingFunctionOn E X)
    {p : E → ℝ} {xHat xTilde yTilde u : E} {mu1 mu2 : ℝ}
    (hp_convex : ConvexOn ℝ X p)
    (hxHat : xHat ∈ X)
    (hmin :
      IsMinOn
        (fun z => p z + mu1 * ν.bregman z xTilde + mu2 * ν.bregman z yTilde)
        X xHat)
    (hu : u ∈ X) :
    0 ≤ p u - p xHat +
      mu1 * ⟪gradient ν.potential xHat - gradient ν.potential xTilde, u - xHat⟫_ℝ +
      mu2 * ⟪gradient ν.potential xHat - gradient ν.potential yTilde, u - xHat⟫_ℝ := by
  classical
  let V : E → E → ℝ := fun a z => ν.bregman z a
  let grad : E → E := fun z => gradient ν.potential z
  have hV_segment_deriv :
      ∀ (a z w : E), z ∈ X →
        let d : E := w - z
        let β : ℝ → ℝ := fun t =>
          if _ht : t ∈ Set.Icc (0 : ℝ) 1 then
            V a (AffineMap.lineMap z w t) - V a z
          else 0
        HasDerivWithinAt β
          ⟪grad z - grad a, d⟫_ℝ
          (Set.Icc (0 : ℝ) 1) 0 := by
    intro a z w hz
    have h :=
      bregman_segment_difference_hasDerivWithinAt_zero
        (v := ν.potential) (grad := grad) (x := a) (xp := z) (u := w)
        (ν.gradient_at z hz)
    simpa [V, grad, SOptLib.DistanceGeneratingFunctionOn.bregman,
      carrierBregmanFormula] using h
  have hopt :
      ∀ z, z ∈ X →
        p xHat + mu1 * V xTilde xHat + mu2 * V yTilde xHat ≤
          p z + mu1 * V xTilde z + mu2 * V yTilde z := by
    intro z hz
    simpa [V] using hmin hz
  have hvar :=
    SOptLib.two_bregman_argmin_variational_inequality_no_center_mem
      X p V grad hp_convex (xTilde := xTilde) (yTilde := yTilde)
      (uHat := xHat) (mu1 := mu1) (mu2 := mu2)
      hxHat hV_segment_deriv hopt u hu
  simpa [V, grad] using hvar

-- Generalization plan (G0):
-- concept/name: fixed-stepsize composite prox selector state-oracle stability;
--   orig was `dualProxSelector_state_oracle_distance_bound`, renamed to expose
--   the reusable selected composite-prox stability step.
-- generality used: arbitrary state carrier `P` evaluated in a real Hilbert
--   space `E`, a fixed positive stepsize, a selected prox map, a simple term,
--   pointwise variational inequalities, and pointwise strong monotonicity. No
--   measure, filtration, compactness, convexity, smoothness, or finite
--   dimensionality is used.
-- portable call pattern: accelerated primal-dual, stochastic mirror descent,
--   and proximal-gradient continuity proofs call this after deriving the
--   selected composite-prox variational inequality; the carrier, prox selector,
--   oracle vector, simple term, and DGF gradient change while the conclusion
--   stays a state-oracle Lipschitz estimate.
-- counterargument checked: close to existing
--   `prox_points_dist_le_oracle_dist_add_base_grad_dist_of_variational` and
--   `SOptLib.proxStep_state_oracle_distance_bound`, but neither has this fixed
--   selector interface: the former needs two manually instantiated pointwise
--   inequalities, while the latter requires a prox map and FOC uniform in an
--   explicit stepsize argument.
-- coverage search: searched catalog/source for "proxStep state oracle distance
--   bound", "prox points oracle base grad variational", and "composite prox
--   selector stability"; coverage is partial and this statement packages the
--   fixed-stepsize selector call pattern used by dual/primal composite prox
--   continuity proofs.
-- minimal hypotheses: global setup assumptions are reduced to a uniform
--   fixed-stepsize variational inequality, pointwise strong monotonicity, and
--   positivity of the stepsize.

/-- A fixed-stepsize composite prox selector is stable in state and oracle data.

If every selected prox point satisfies the composite-prox variational
inequality at a fixed positive stepsize, and the gradient map is strongly
monotone after evaluation into the ambient Hilbert space, then two selected
prox points are controlled by the oracle gap and the base-gradient gap.

Layer: Layer0 | Gap: Level 1 (fixed-stepsize composite prox selector stability)
Proof: instantiate the pointwise SOptLib variational stability theorem at the
  two selected prox points; the supplied uniform selector variational
  inequality provides the two one-sided inequalities.
Source: Mathlib real inner-product Cauchy-Schwarz/order algebra and SOptLib
  prox variational-stability APIs
Used in: accelerated primal-dual dual Bregman prox-step continuity from selected
  composite prox optimality
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem dualCompositeProxSelector_state_oracle_distance_bound
    {P E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (prox : P → E → P) (eval grad : P → E) (h : P → ℝ)
    (γ : ℝ) (hγ : 0 < γ)
    (hvi :
      ∀ (x u : P) (g : E),
        0 ≤
          ⟪g, eval u - eval (prox x g)⟫_ℝ +
            γ⁻¹ * ⟪grad (prox x g) - grad x, eval u - eval (prox x g)⟫_ℝ +
            (h u - h (prox x g)))
    (hstrong :
      ∀ y z : P,
        ‖eval y - eval z‖ ^ 2 ≤
          ⟪eval y - eval z, grad y - grad z⟫_ℝ)
    (x₁ x₂ : P) (g₁ g₂ : E) :
    ‖eval (prox x₁ g₁) - eval (prox x₂ g₂)‖ ≤
      γ * ‖g₁ - g₂‖ + ‖grad x₁ - grad x₂‖ := by
  exact
    prox_points_dist_le_oracle_dist_add_base_grad_dist_of_variational
      (eval := eval) (grad := grad) (h := h)
      x₁ x₂ (prox x₁ g₁) (prox x₂ g₂) g₁ g₂ γ hγ
      (by simpa using hvi x₁ (prox x₂ g₂) g₁)
      (by simpa using hvi x₂ (prox x₁ g₁) g₂)
      (hstrong (prox x₁ g₁) (prox x₂ g₂))

-- Generalization plan (G0):
-- concept/name: composite prox selector variational inequality for a DGF
--   Bregman objective; orig was `dualProxSelector_variational`.
-- generality used: carrier `X` in a complete real Hilbert space, a concrete
--   `DistanceGeneratingFunctionOn E X`, ambient convex simple term
--   `ConvexOn ℝ X h`, positive stepsize, selector minimality, and objective
--   normalization. No measure, filtration, oracle distribution, finite
--   dimension, or SAPD setup fields.
-- portable call pattern: stochastic mirror descent, accelerated primal-dual,
--   and proximal-gradient composite steps where a selected argmin of
--   `⟪g, eval ·⟫ + γ⁻¹ Dν(eval ·, eval base) + h ·` is converted to the
--   unscaled variational inequality; the selector, oracle vector, carrier, and
--   simple term vary while the conclusion shape is unchanged.
-- counterargument checked: not a pure wrapper around
--   `prox_variational_inequality_of_isMinOn_linear_bregman`, whose statement is
--   closed-carrier and one-vector with no inverse-stepsize/simple-term selector
--   interface; not paper-local because it abstracts the selected composite prox
--   FOC used by several stochastic-optimization updates.
-- coverage search: searched "prox variational inequality argmin bregman convex
--   selector", "linear Bregman prox variational", and catalog hits
--   `prox_minimality_scaled_difference_nonneg`,
--   `prox_segment_majorized_lower_bound`,
--   `prox_scaled_variational_inequality_of_argmin`,
--   `prox_variational_inequality_of_argmin`,
--   `prox_variational_inequality_of_isMinOn_linear_bregman`, and
--   `two_center_bregman_residual_variational_of_isMinOn`; coverage is partial,
--   but no existing theorem packages the DGF selected-composite-prox route.
-- minimal hypotheses: global setup convexity is reduced to convexity of the
--   totalized simple term; selectedness is reduced to a pointwise minimizer
--   certificate; DGF use is reduced to membership of the selected prox point.

/-- A selected DGF composite prox point satisfies the unscaled variational inequality.

For a selector minimizing a composite prox objective with linear term, inverse
stepsize Bregman term, and convex simple term, every feasible comparison point
satisfies the standard unscaled first-order variational inequality.

Layer: Layer0 | Gap: Level 1 (selected composite prox variational inequality)
Proof: use prox minimality along the feasible segment, convexly majorize the
  simple term, obtain the DGF Bregman segment derivative from the selected
  point's gradient, and convert the resulting scaled inequality to unscaled form.
Source: Mathlib convex segment calculus and SOptLib DGF Bregman/prox first-order
  condition APIs
Used in: stochastic mirror and accelerated primal-dual selected composite
  Bregman prox-step optimality before variational-stability estimates
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem dualCompositeProxSelector_variational
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {X : Set E} (ν : SOptLib.DistanceGeneratingFunctionOn E X)
    (h : E → ℝ)
    (objective : {x : E // x ∈ X} → E → ℝ → {x : E // x ∈ X} → ℝ)
    (selector : E → {x : E // x ∈ X} → {x : E // x ∈ X})
    (hconv : ConvexOn ℝ X h)
    (hobjective :
      ∀ (x : {x : E // x ∈ X}) (g : E) (γ : ℝ) (y : {x : E // x ∈ X}),
        objective x g γ y = ⟪g, y.1⟫_ℝ + γ⁻¹ * ν.bregman y.1 x.1 + h y.1)
    {γ : ℝ}
    (hselector_min :
      ∀ (x : {x : E // x ∈ X}) (g : E) (y : {x : E // x ∈ X}),
        objective x g γ (selector g x) ≤ objective x g γ y)
    {base u : {x : E // x ∈ X}} {g : E} (hγ : 0 < γ) :
    0 ≤
      ⟪g, u.1 - (selector g base).1⟫_ℝ +
        γ⁻¹ *
          ⟪gradient ν.potential (selector g base).1 -
              gradient ν.potential base.1,
            u.1 - (selector g base).1⟫_ℝ +
        (h u.1 - h (selector g base).1) := by
  classical
  let P := {x : E // x ∈ X}
  let xp : P := selector g base
  let eval : P → E := fun y => y.1
  let grad : P → E := fun y => gradient ν.potential y.1
  let hcar : P → ℝ := fun y => h y.1
  let V : P → P → ℝ := fun x y => ν.bregman y.1 x.1
  have hconv_total : ConvexOn ℝ X (SOptLib.totalizeOn X hcar) := by
    refine ⟨hconv.1, ?_⟩
    intro x hx y hy a b ha hb hsum
    have hconv_xy := hconv.2 hx hy ha hb hsum
    have hx' : SOptLib.totalizeOn X hcar x = h x := by
      simpa [hcar] using SOptLib.totalizeOn_of_mem X hcar hx
    have hy' : SOptLib.totalizeOn X hcar y = h y := by
      simpa [hcar] using SOptLib.totalizeOn_of_mem X hcar hy
    have hxy :
        SOptLib.totalizeOn X hcar (a • x + b • y) = h (a • x + b • y) := by
      have hmem : a • x + b • y ∈ X := hconv.1 hx hy ha hb hsum
      simpa [hcar] using SOptLib.totalizeOn_of_mem X hcar hmem
    simpa [hx', hy', hxy] using hconv_xy
  have hmin :
      ∀ y : P, objective base g γ xp ≤ objective base g γ y := by
    intro y
    exact hselector_min base g y
  have hβderiv :
      let d : E := u.1 - xp.1
      let segment : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → P :=
        fun s hs => ⟨AffineMap.lineMap xp.1 u.1 s, hconv.1.lineMap_mem xp.2 u.2 hs⟩
      let β : ℝ → ℝ := fun s =>
        if hs : s ∈ Set.Icc (0 : ℝ) 1 then
          V base (segment s hs) - V base xp
        else 0
      HasDerivWithinAt β
        ⟪grad xp - grad base, d⟫_ℝ (Set.Icc (0 : ℝ) 1) 0 := by
    let d : E := u.1 - xp.1
    have h :=
      bregman_segment_difference_hasDerivWithinAt_zero
        (v := ν.potential) (grad := fun x : E => gradient ν.potential x)
        (x := base.1) (xp := xp.1) (u := u.1)
        (ν.gradient_at xp.1 xp.2)
    simpa [V, grad, d, SOptLib.DistanceGeneratingFunctionOn.bregman,
      carrierBregmanFormula] using h
  let d : E := u.1 - xp.1
  let segment : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → P :=
    fun s hs => ⟨AffineMap.lineMap xp.1 u.1 s, hconv.1.lineMap_mem xp.2 u.2 hs⟩
  let β : ℝ → ℝ := fun s =>
    if hs : s ∈ Set.Icc (0 : ℝ) 1 then
      V base (segment s hs) - V base xp
    else 0
  let φ : ℝ → ℝ := fun s =>
    γ * s * ⟪g, d⟫_ℝ + β s + γ * s * (hcar u - hcar xp)
  have hβderiv' :
      HasDerivWithinAt β
        ⟪grad xp - grad base, d⟫_ℝ (Set.Icc (0 : ℝ) 1) 0 := by
    simpa [β, segment, d] using hβderiv
  have hφ0 : φ 0 = 0 := by
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
    have hseg0 : segment 0 h0 = xp := by
      apply Subtype.ext
      simp [segment, AffineMap.lineMap_apply_module']
    have hβ0 : β 0 = 0 := by
      simp [β, hseg0]
    simp [φ, hβ0]
  have hφ_nonneg : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ φ s := by
    intro s hs
    have hbase :
        0 ≤
          γ * (⟪g, eval (segment s hs)⟫_ℝ - ⟪g, eval xp⟫_ℝ) +
            (V base (segment s hs) - V base xp) +
            γ * (hcar (segment s hs) - hcar xp) :=
      prox_minimality_scaled_difference_nonneg objective V eval hcar base xp
        (segment s hs) g hγ (hobjective base g γ) hmin
    have hline : eval (segment s hs) = AffineMap.lineMap (eval xp) (eval u) s := by
      rfl
    have hh : hcar (segment s hs) - hcar xp ≤ s * (hcar u - hcar xp) := by
      simpa [segment, eval] using
        convexOnCarrier_segment_sub_le_mul_sub hcar hconv_total xp u hs
    have hseg :=
      prox_segment_majorized_lower_bound eval V hcar base xp u (segment s hs)
        g γ s hγ.le hbase hline hh
    have hβs : β s = V base (segment s hs) - V base xp := by
      dsimp [β]
      rw [dif_pos hs]
    simpa [φ, hβs, d, hline, mul_assoc] using hseg
  have hφderiv :
      HasDerivWithinAt φ
        (γ * ⟪g, eval u - eval xp⟫_ℝ +
          ⟪grad xp - grad base, eval u - eval xp⟫_ℝ +
          γ * (hcar u - hcar xp))
        (Set.Icc (0 : ℝ) 1) 0 := by
    simpa [φ, d] using
      prox_majorant_hasDerivWithinAt_zero β g d
        (grad xp - grad base) γ (hcar u - hcar xp) hβderiv'
  have hscaled :
      0 ≤
        γ * ⟪g, eval u - eval xp⟫_ℝ +
          ⟪grad xp - grad base, eval u - eval xp⟫_ℝ +
          γ * (hcar u - hcar xp) :=
    prox_scaled_variational_inequality_of_argmin eval grad hcar base xp u
      g γ φ hφ0 hφ_nonneg hφderiv
  have hunscaled :
      0 ≤
        ⟪g, eval u - eval xp⟫_ℝ +
          γ⁻¹ * ⟪grad xp - grad base, eval u - eval xp⟫_ℝ +
          (hcar u - hcar xp) :=
    prox_variational_inequality_of_argmin eval grad hcar base xp u
      g γ hγ hscaled
  simpa [xp, eval, grad, hcar] using hunscaled

-- Generalization plan (G0):
-- concept/name: composite prox arbitrary-minimizer variational inequality for
--   a DGF Bregman objective; orig was `dual_prox_minimizer_variational`.
-- generality used: carrier `X` in a complete real Hilbert space, a concrete
--   `DistanceGeneratingFunctionOn E X`, ambient convex simple term
--   `ConvexOn ℝ X h`, positive stepsize, and a pointwise minimizer certificate
--   for the concrete `SOptLib.proxObjective`. No measure, filtration, oracle
--   distribution, finite dimension, or SAPD setup fields.
-- portable call pattern: stochastic mirror descent, accelerated primal-dual,
--   mirror-prox, and proximal-gradient composite steps where any argmin of
--   `⟪g, eval ·⟫ + γ⁻¹ Dν(eval ·, eval base) + h ·` is converted to the
--   unscaled variational inequality; the base point, oracle vector, carrier,
--   simple term, and minimizer certificate vary while the conclusion stays.
-- counterargument checked: close to the already staged selected-prox theorem
--   `selected_dgf_composite_prox_variational_inequality`, but that theorem
--   assumes a globally minimizing selector and cannot consume a single
--   arbitrary-minimizer certificate without extra equality/decidable structure;
--   not a pure wrapper around `prox_variational_inequality_of_isMinOn_linear_bregman`,
--   whose interface is closed-carrier and does not discharge the DGF segment
--   derivative from `DistanceGeneratingFunctionOn`.
-- coverage search: searched "prox variational inequality argmin bregman
--   composite minimizer", catalog hits `prox_minimality_scaled_difference_nonneg`,
--   `prox_segment_majorized_lower_bound`,
--   `prox_scaled_variational_inequality_of_argmin`,
--   `prox_variational_inequality_of_argmin`,
--   `prox_variational_inequality_of_isMinOn_linear_bregman`, and
--   `selected_dgf_composite_prox_variational_inequality`; LeanSearch found
--   Mathlib first-order minimizer lemmas but no composite Bregman prox
--   minimizer theorem. Coverage is partial; this arbitrary-minimizer DGF
--   composite prox adapter is genuinely different.
-- minimal hypotheses: global setup fields are reduced to convexity of `h` on
--   the carrier, positivity of `γ`, and one pointwise minimizer certificate;
--   all probability and finite-dimensional assumptions are removed.

/-- Any DGF composite prox minimizer satisfies the unscaled variational inequality.

For a minimizer of a composite prox objective with linear term, inverse
stepsize Bregman term, and convex simple term, every feasible comparison point
satisfies the standard unscaled first-order variational inequality.

Layer: Layer0 | Gap: Level 1 (arbitrary composite prox minimizer variational inequality)
Proof: use prox minimality along the feasible segment, convexly majorize the
  simple term, obtain the DGF Bregman segment derivative from the minimizer's
  gradient, and convert the resulting scaled inequality to unscaled form.
Source: Mathlib convex segment calculus and SOptLib DGF Bregman/prox
  first-order condition APIs
Used in: stochastic mirror, mirror-prox, and accelerated primal-dual composite
  Bregman prox-step optimality before variational-stability or uniqueness estimates
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem dualCompositeProx_minimizer_variational
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {X : Set E} (ν : SOptLib.DistanceGeneratingFunctionOn E X)
    (h : E → ℝ) (hconv : ConvexOn ℝ X h)
    {base z u : {x : E // x ∈ X}} {g : E} {γ : ℝ} (hγ : 0 < γ)
    (hmin :
      ∀ y : {x : E // x ∈ X},
        SOptLib.proxObjective
            (fun p q : {w : E // w ∈ X} => ν.bregman q.1 p.1)
            (fun y : {w : E // w ∈ X} => h y.1)
            (fun y : {w : E // w ∈ X} => y.1)
            base g γ z ≤
          SOptLib.proxObjective
            (fun p q : {w : E // w ∈ X} => ν.bregman q.1 p.1)
            (fun y : {w : E // w ∈ X} => h y.1)
            (fun y : {w : E // w ∈ X} => y.1)
            base g γ y) :
    0 ≤
      ⟪g, u.1 - z.1⟫_ℝ +
        γ⁻¹ *
          ⟪gradient ν.potential z.1 - gradient ν.potential base.1,
            u.1 - z.1⟫_ℝ +
        (h u.1 - h z.1) := by
  classical
  let P := {x : E // x ∈ X}
  let eval : P → E := fun y => y.1
  let grad : P → E := fun y => gradient ν.potential y.1
  let hcar : P → ℝ := fun y => h y.1
  let V : P → P → ℝ := fun x y => ν.bregman y.1 x.1
  have hconv_total : ConvexOn ℝ X (SOptLib.totalizeOn X hcar) := by
    refine ⟨hconv.1, ?_⟩
    intro x hx y hy a b ha hb hsum
    have hconv_xy := hconv.2 hx hy ha hb hsum
    have hx' : SOptLib.totalizeOn X hcar x = h x := by
      simpa [hcar] using SOptLib.totalizeOn_of_mem X hcar hx
    have hy' : SOptLib.totalizeOn X hcar y = h y := by
      simpa [hcar] using SOptLib.totalizeOn_of_mem X hcar hy
    have hxy :
        SOptLib.totalizeOn X hcar (a • x + b • y) = h (a • x + b • y) := by
      have hmem : a • x + b • y ∈ X := hconv.1 hx hy ha hb hsum
      simpa [hcar] using SOptLib.totalizeOn_of_mem X hcar hmem
    simpa [hx', hy', hxy] using hconv_xy
  have hmin' :
      ∀ y : P,
        SOptLib.proxObjective V hcar eval base g γ z ≤
          SOptLib.proxObjective V hcar eval base g γ y := by
    intro y
    simpa [V, hcar, eval] using hmin y
  have hβderiv :
      let d : E := u.1 - z.1
      let segment : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → P :=
        fun s hs => ⟨AffineMap.lineMap z.1 u.1 s, hconv.1.lineMap_mem z.2 u.2 hs⟩
      let β : ℝ → ℝ := fun s =>
        if hs : s ∈ Set.Icc (0 : ℝ) 1 then
          V base (segment s hs) - V base z
        else 0
      HasDerivWithinAt β
        ⟪grad z - grad base, d⟫_ℝ (Set.Icc (0 : ℝ) 1) 0 := by
    let d : E := u.1 - z.1
    have hseg :=
      bregman_segment_difference_hasDerivWithinAt_zero
        (v := ν.potential) (grad := fun x : E => gradient ν.potential x)
        (x := base.1) (xp := z.1) (u := u.1)
        (ν.gradient_at z.1 z.2)
    simpa [V, grad, d, SOptLib.DistanceGeneratingFunctionOn.bregman,
      carrierBregmanFormula] using hseg
  let d : E := u.1 - z.1
  let segment : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → P :=
    fun s hs => ⟨AffineMap.lineMap z.1 u.1 s, hconv.1.lineMap_mem z.2 u.2 hs⟩
  let β : ℝ → ℝ := fun s =>
    if hs : s ∈ Set.Icc (0 : ℝ) 1 then
      V base (segment s hs) - V base z
    else 0
  let φ : ℝ → ℝ := fun s =>
    γ * s * ⟪g, d⟫_ℝ + β s + γ * s * (hcar u - hcar z)
  have hβderiv' :
      HasDerivWithinAt β
        ⟪grad z - grad base, d⟫_ℝ (Set.Icc (0 : ℝ) 1) 0 := by
    simpa [β, segment, d] using hβderiv
  have hφ0 : φ 0 = 0 := by
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
    have hseg0 : segment 0 h0 = z := by
      apply Subtype.ext
      simp [segment, AffineMap.lineMap_apply_module']
    have hβ0 : β 0 = 0 := by
      simp [β, hseg0]
    simp [φ, hβ0]
  have hφ_nonneg : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ φ s := by
    intro s hs
    have hbase :
        0 ≤
          γ * (⟪g, eval (segment s hs)⟫_ℝ - ⟪g, eval z⟫_ℝ) +
            (V base (segment s hs) - V base z) +
            γ * (hcar (segment s hs) - hcar z) :=
      prox_minimality_scaled_difference_nonneg (SOptLib.proxObjective V hcar eval)
        V eval hcar base z (segment s hs) g hγ (by
          intro y
          rfl) hmin'
    have hline : eval (segment s hs) = AffineMap.lineMap (eval z) (eval u) s := by
      rfl
    have hh : hcar (segment s hs) - hcar z ≤ s * (hcar u - hcar z) := by
      simpa [segment, eval] using
        convexOnCarrier_segment_sub_le_mul_sub hcar hconv_total z u hs
    have hseg :=
      prox_segment_majorized_lower_bound eval V hcar base z u (segment s hs)
        g γ s hγ.le hbase hline hh
    have hβs : β s = V base (segment s hs) - V base z := by
      dsimp [β]
      rw [dif_pos hs]
    simpa [φ, hβs, d, hline, mul_assoc] using hseg
  have hφderiv :
      HasDerivWithinAt φ
        (γ * ⟪g, eval u - eval z⟫_ℝ +
          ⟪grad z - grad base, eval u - eval z⟫_ℝ +
          γ * (hcar u - hcar z))
        (Set.Icc (0 : ℝ) 1) 0 := by
    simpa [φ, d] using
      prox_majorant_hasDerivWithinAt_zero β g d
        (grad z - grad base) γ (hcar u - hcar z) hβderiv'
  have hscaled :
      0 ≤
        γ * ⟪g, eval u - eval z⟫_ℝ +
          ⟪grad z - grad base, eval u - eval z⟫_ℝ +
          γ * (hcar u - hcar z) :=
    prox_scaled_variational_inequality_of_argmin eval grad hcar base z u
      g γ φ hφ0 hφ_nonneg hφderiv
  have hunscaled :
      0 ≤
        ⟪g, eval u - eval z⟫_ℝ +
          γ⁻¹ * ⟪grad z - grad base, eval u - eval z⟫_ℝ +
          (hcar u - hcar z) :=
    prox_variational_inequality_of_argmin eval grad hcar base z u
      g γ hγ hscaled
  simpa [eval, grad, hcar] using hunscaled


-- Generalization plan (G0):
-- concept/name: two-center Bregman residual nonnegativity from an `IsMinOn`
--   certificate; orig was `lemma_3_5_residual_from_argmin`.
-- generality used: complete real Hilbert space, carrier set `X`, concrete
--   `SOptLib.DistanceGeneratingFunctionOn E X`, convex term `ConvexOn ℝ X p`,
--   pointwise minimizer membership plus `IsMinOn`; no measure/oracle assumptions.
-- portable call pattern: accelerated primal-dual, accelerated mirror descent,
--   and mirror-prox two-anchor prox steps after proving the local subproblem
--   minimizes a convex term plus weighted Bregman divergences; centers, weights,
--   and comparison point change while the residual statement stays fixed.
-- counterargument checked: this composes an existing inner-product residual
--   variational theorem with the one-center DGF residual identity, but it is not
--   a pure rename: downstream prox proofs need the Bregman-value residual form
--   directly before converting to a three-point inequality.
-- coverage search: searched project/SOptLib for `two_center_bregman_residual`,
--   `residual_nonneg`, `IsMinOn`, and LeanSearch
--   "convex minimizer two Bregman divergence residual nonnegative"; Mathlib has
--   generic convex extrema and line-derivative facts, SOptLib/staging has the
--   inner-product variational theorem and one-center residual identity but no
--   combined two-center Bregman residual conclusion.
-- minimal hypotheses: dropped center membership and weight nonnegativity from
--   the paper lemma because neither is used by the first-order residual proof;
--   minimizer membership is kept as the only pointwise feasibility hypothesis.

/-- A two-center Bregman minimizer has nonnegative Bregman-value residual.

For a distance-generating function on a carrier, a minimizer of a convex term
plus two weighted Bregman divergences satisfies the two-center residual
inequality written entirely in terms of Bregman values.

Layer: Layer0 | Gap: Level 1 (two-center Bregman residual nonnegativity)
Proof: first apply the two-center Bregman argmin variational theorem in
  inner-product form, then rewrite each center residual using the DGF
  Bregman three-point identity.
Source: Mathlib convex first-order conditions and SOptLib Bregman
  three-point identities
Used in: accelerated primal-dual and accelerated mirror-descent two-anchor
  prox residual conversion before scalar three-point rearrangement
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/key_lemmas
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem two_center_bregman_residual_nonneg_of_isMinOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {X : Set E} (ν : SOptLib.DistanceGeneratingFunctionOn E X)
    {p : E → ℝ} {xHat xTilde yTilde u : E} {mu1 mu2 : ℝ}
    (hp_convex : ConvexOn ℝ X p)
    (hxHat : xHat ∈ X)
    (hmin :
      IsMinOn
        (fun z => p z + mu1 * ν.bregman z xTilde + mu2 * ν.bregman z yTilde)
        X xHat)
    (hu : u ∈ X) :
    0 ≤ p u - p xHat +
      mu1 * (ν.bregman u xTilde - ν.bregman xHat xTilde - ν.bregman u xHat) +
      mu2 * (ν.bregman u yTilde - ν.bregman xHat yTilde - ν.bregman u xHat) := by
  have hinner :=
    two_center_bregman_residual_variational_of_isMinOn
      (ν := ν) (p := p) (xHat := xHat) (xTilde := xTilde)
      (yTilde := yTilde) (u := u) (mu1 := mu1) (mu2 := mu2)
      hp_convex hxHat hmin hu
  have hx_res :=
    SOptLib.DistanceGeneratingFunctionOn.bregman_residual_eq_inner
      ν xTilde xHat u
  have hy_res :=
    SOptLib.DistanceGeneratingFunctionOn.bregman_residual_eq_inner
      ν yTilde xHat u
  rw [hx_res, hy_res]
  exact hinner

-- Generalization plan (G0):
-- concept/name: counterexample showing that a two-center Bregman three-point
--   minimizer inequality requires a convex simple term; orig was
--   `lemma_3_5_retired_old_head_counterexample`.
-- generality used: real scalar carrier `Set.univ`, an abstract Bregman-like
--   kernel `V : ℝ → ℝ → ℝ`, pointwise normalization `V 0 0 = 0`, and the
--   half-square lower bound at base `0`; no measure, oracle, differentiability,
--   full DGF structure, or finite-dimensional assumptions are used.
-- portable call pattern: accelerated primal-dual, accelerated mirror descent,
--   and mirror-prox proof audits can cite this when checking that a proposed
--   three-point prox lemma has not dropped convexity of the nonsmooth/simple
--   term; the concrete Bregman kernel changes while the nonconvex witness
--   `p(u) = -u^2 / 4` and contradiction shape remain the same.
-- counterargument checked: this is not merely paper-local traceability because
--   it records a reusable negative boundary for two-anchor Bregman prox
--   arguments; it is not covered by the positive residual lemmas, which assume
--   `ConvexOn`, nor by Mathlib's generic convex extrema facts.
-- coverage search: searched SOptLib/Staging/catalog for `two_center_bregman`,
--   `three_point`, `requires_convex`, and `counterexample`; existing hits are
--   positive residual/variational lemmas and unrelated scalar counterexamples.
--   LeanSearch for "counterexample convexity necessary Bregman three point
--   inequality minimizer nonconvex" returned generic convex-analysis facts such
--   as `ConvexOn.secant_mono_aux1`, `StrongConvexOn`, and
--   `IsMinOn.of_isLocalMinOn_of_convexOn`, but no separation theorem.
-- minimal hypotheses: the proof uses only `V 0 0 = 0` and the base-zero
--   lower bound `∀ z, (1 / 2) * z^2 ≤ V z 0`; all DGF fields, center
--   membership, weight nonnegativity, and topology are removed.

/-- A two-center Bregman three-point minimizer inequality is false without convexity.

For any real-line Bregman-like kernel normalized at zero and bounded below by
`z^2 / 2` from the base `0`, the nonconvex simple term `p(z) = -z^2 / 4`
makes `0` minimize `p z + V z 0`, but the convexity-free three-point
conclusion at `z = 1` would imply `0 ≤ -1 / 4`.

Layer: Layer0 | Gap: Level 0 (two-center Bregman convexity necessity)
Proof: instantiate the alleged convexity-free three-point principle with the
  witness `p(z) = -z^2 / 4`, centers `0, 0`, and weights `1, 0`; the
  half-square lower bound proves the argmin hypothesis, and normalization
  reduces the conclusion to a contradiction.
Source: elementary real algebra for Bregman-prox counterexamples and Mathlib
  `IsMinOn` extrema predicates
Used in: accelerated primal-dual and mirror-prox audits of two-anchor Bregman
  prox lemmas before applying the corrected convex simple-term hypothesis
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/key_lemmas
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem two_center_bregman_three_point_requires_convex_counterexample
    (V : ℝ → ℝ → ℝ)
    (hV_zero : V 0 0 = 0)
    (hV_lower_zero : ∀ z : ℝ, (1 / 2 : ℝ) * z ^ 2 ≤ V z 0) :
    ¬ (∀ {pFun : ℝ → ℝ}
      {xHat xTilde yTilde : ℝ} {mu1 mu2 : ℝ}
      (_hArgmin :
        xHat ∈ Set.univ ∧
          IsMinOn
            (fun u => pFun u + mu1 * V u xTilde + mu2 * V u yTilde)
            Set.univ xHat)
      (u : ℝ) (_hu : u ∈ Set.univ),
      pFun xHat + mu1 * V xHat xTilde + mu2 * V xHat yTilde ≤
        pFun u + mu1 * V u xTilde + mu2 * V u yTilde -
          (mu1 + mu2) * V u xHat) := by
  intro hOld
  let pFun : ℝ → ℝ := fun x => - (x ^ 2) / 4
  have hArgmin :
      (0 : ℝ) ∈ Set.univ ∧
        IsMinOn
          (fun u : ℝ => pFun u + (1 : ℝ) * V u 0 + (0 : ℝ) * V u 0)
          Set.univ 0 := by
    refine ⟨Set.mem_univ 0, ?_⟩
    intro z _hz
    have hb : (1 / 2 : ℝ) * z ^ 2 ≤ V z 0 := hV_lower_zero z
    have hsq : 0 ≤ z ^ 2 := sq_nonneg z
    calc
      pFun 0 + (1 : ℝ) * V 0 0 + (0 : ℝ) * V 0 0 = 0 := by
        simp [pFun, hV_zero]
      _ ≤ pFun z + (1 : ℝ) * V z 0 + (0 : ℝ) * V z 0 := by
        simp [pFun]
        nlinarith
  have hconcl :=
    hOld (pFun := pFun) (xHat := (0 : ℝ)) (xTilde := (0 : ℝ))
      (yTilde := (0 : ℝ)) (mu1 := (1 : ℝ)) (mu2 := (0 : ℝ)) (u := (1 : ℝ))
      hArgmin (Set.mem_univ (1 : ℝ))
  have hbad : (0 : ℝ) ≤ -1 / 4 := by
    norm_num [pFun, hV_zero] at hconcl
  norm_num at hbad

-- Generalization plan (G0):
-- concept/name: coordinatewise `IsMinOn` certificates from an additive product
--   minimizer; orig was the local `hstep_minX`/`hstep_minY` block in
--   `lemma_4_10_product_argmin_coordinate_projection`.
-- generality used: arbitrary carrier types `E` and `F`, feasible sets `X` and
--   `Y`, real-valued coordinate objectives, and a product-set minimizer; no
--   topology, measure, convexity, smoothness, or oracle assumptions are used.
-- portable call pattern: two-block stochastic mirror descent, stochastic
--   primal-dual, and block-coordinate prox proofs after an additive product
--   subproblem is minimized; the spaces, feasible sets, and coordinate
--   objectives change while the coordinatewise minimizer conclusion stays the
--   same.
-- counterargument checked: this is a short order-cancellation lemma, but it is
--   not paper-local traceability or a pure rename; Mathlib has `IsMinOn.add`
--   and product-order extrema, while this statement projects a constrained
--   additive objective minimum on `X ×ˢ Y` to frozen-coordinate minima.
-- coverage search: queried SOptLib/project for `IsMinOn product coordinate
--   projection` and LeanSearch for product minimizers over coordinate sets;
--   hits were `IsMinOn`, `IsMinOn.add`, `IsMinOn.comp_mapsTo`, and
--   product-order `IsMin.fst`/`Prod.isMin_iff`, none of which cover additive
--   objective coordinate projection on product feasible sets.
-- minimal hypotheses: the product membership of the minimizer is explicit
--   because `IsMinOn` alone does not include feasibility; all other hypotheses
--   are used directly.

/-- An additive product-objective minimizer is coordinatewise minimal.

If `(x̂, ŷ)` minimizes `φ x + ψ y` over `X ×ˢ Y` and is feasible, then freezing
one coordinate gives an `IsMinOn` certificate for each coordinate objective on
its own feasible set.

Layer: Glue | Gap: Level 0 (additive product minimizer coordinate projection)
Proof: compare the product minimizer against `(x, ŷ)` and `(x̂, y)`, then cancel
  the frozen additive term on the right or left.
Source: Mathlib order extrema over sets and ordered additive cancellation on
  real-valued objectives
Used in: stochastic accelerated primal-dual auxiliary product prox step projected
  to primal and dual mirror-descent subproblems
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/key_lemmas
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem product_isMinOn_coordinate_isMinOn
    {E F : Type*} {X : Set E} {Y : Set F}
    {φ : E → ℝ} {ψ : F → ℝ} {xhat : E} {yhat : F}
    (hxy : (xhat, yhat) ∈ X ×ˢ Y)
    (hmin : IsMinOn (fun p : E × F => φ p.1 + ψ p.2) (X ×ˢ Y) (xhat, yhat)) :
    (xhat ∈ X ∧ IsMinOn φ X xhat) ∧
      (yhat ∈ Y ∧ IsMinOn ψ Y yhat) := by
  rcases hxy with ⟨hxhat, hyhat⟩
  have hmin' := (isMinOn_iff.mp hmin)
  constructor
  · refine ⟨hxhat, ?_⟩
    intro x hx
    exact (add_le_add_iff_right (ψ yhat)).mp (hmin' (x, yhat) ⟨hx, hyhat⟩)
  · refine ⟨hyhat, ?_⟩
    intro y hy
    exact (add_le_add_iff_left (φ xhat)).mp (hmin' (xhat, y) ⟨hxhat, hy⟩)

-- Generalization plan (G0):
-- concept/name: scaled composite prox variational inequality from a minimizer
--   and feasible segment; orig was `primal_prox_minimizer_scaled_variational`.
-- generality used: arbitrary candidate type `P` evaluated in a real Hilbert
--   space, canonical `SOptLib.proxObjective`, positive stepsize, a supplied
--   feasible segment from the minimizer to the comparison point, pointwise
--   simple-term segment majorization, and a pointwise Bregman-segment
--   derivative. No measure, filtration, finite-dimensional, or paper setup
--   assumptions are used.
-- portable call pattern: stochastic mirror descent, primal-dual mirror-prox,
--   and proximal-gradient proofs can turn a prox-subproblem minimizer into the
--   scaled variational inequality after supplying the feasible segment,
--   segment derivative, and convex/simple-term majorization; the oracle vector,
--   divergence, simple term, and carrier segment vary while the conclusion
--   shape stays fixed.
-- counterargument checked: not a pure wrapper around
--   `prox_scaled_variational_inequality_of_argmin`, which starts after the
--   scalar majorant `φ` and its derivative have already been assembled; not
--   duplicated by the staged DGF composite minimizer theorem, which is a
--   concrete DGF adapter producing an unscaled inequality and requiring a
--   convex carrier/DGF package.
-- coverage search: searched catalog and source for "prox scaled variational
--   argmin segment", "composite prox minimizer variational inequality", and
--   relevant hits `prox_minimality_scaled_difference_nonneg`,
--   `prox_segment_majorized_lower_bound`, `prox_majorant_hasDerivWithinAt_zero`,
--   `prox_scaled_variational_inequality_of_argmin`,
--   `prox_variational_inequality_of_argmin`, and
--   `dgf_composite_prox_minimizer_variational_inequality`; coverage is
--   partial, because no existing theorem composes minimizer minimality with a
--   supplied segment derivative into the scaled inequality at this generality.
-- minimal hypotheses: global convexity and DGF assumptions are reduced to the
--   exact pointwise segment majorization, endpoint, evaluation, derivative, and
--   minimizer facts consumed by the proof.

/-- A prox minimizer plus segment derivative gives the scaled variational inequality.

For the canonical composite prox objective, it is enough to know minimality of
`xp`, a feasible segment from `xp` to `u`, a segment majorization of the simple
term, and the derivative of the divergence term along that segment. These data
assemble the one-dimensional majorant whose right derivative is the scaled prox
variational expression.

Layer: Layer0 | Gap: Level 1 (prox minimizer segment variational inequality)
Proof: derive a scaled objective-difference lower bound at each segment point,
  majorize the simple term along the segment, assemble the scalar majorant
  derivative, and apply the one-sided derivative sign lemma.
Source: Mathlib one-dimensional derivative calculus and SOptLib prox
  first-order-condition APIs
Used in: stochastic mirror, proximal-gradient, and accelerated primal-dual
  prox-step optimality before uniqueness or stability estimates
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem prox_scaled_variational_of_minimizer_with_segment
    {P E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (eval grad : P → E) (V : P → P → ℝ) (h : P → ℝ)
    (x xp u : P) (g : E) {γ : ℝ} (hγ : 0 < γ)
    (segment : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → P)
    (hsegment_zero :
      ∀ h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1, segment 0 h0 = xp)
    (hsegment_eval :
      ∀ s (hs : s ∈ Set.Icc (0 : ℝ) 1),
        eval (segment s hs) = AffineMap.lineMap (eval xp) (eval u) s)
    (hh_segment :
      ∀ s (hs : s ∈ Set.Icc (0 : ℝ) 1),
        h (segment s hs) - h xp ≤ s * (h u - h xp))
    (hV_deriv :
      let β : ℝ → ℝ := fun s =>
        if hs : s ∈ Set.Icc (0 : ℝ) 1 then
          V x (segment s hs) - V x xp
        else 0
      HasDerivWithinAt β
        ⟪grad xp - grad x, eval u - eval xp⟫_ℝ (Set.Icc (0 : ℝ) 1) 0)
    (hmin :
      ∀ y : P,
        SOptLib.proxObjective V h eval x g γ xp ≤
          SOptLib.proxObjective V h eval x g γ y) :
    0 ≤
      γ * ⟪g, eval u - eval xp⟫_ℝ +
        ⟪grad xp - grad x, eval u - eval xp⟫_ℝ +
        γ * (h u - h xp) := by
  let β : ℝ → ℝ := fun s =>
    if hs : s ∈ Set.Icc (0 : ℝ) 1 then
      V x (segment s hs) - V x xp
    else 0
  let φ : ℝ → ℝ := fun s =>
    γ * s * ⟪g, eval u - eval xp⟫_ℝ + β s + γ * s * (h u - h xp)
  have hobjective :
      ∀ y : P,
        SOptLib.proxObjective V h eval x g γ y =
          ⟪g, eval y⟫_ℝ + γ⁻¹ * V x y + h y := by
    intro y
    rfl
  have hφ0 : φ 0 = 0 := by
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
    have hβ0 : β 0 = 0 := by
      simp [β, hsegment_zero h0]
    simp [φ, hβ0]
  have hφ_nonneg : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ φ s := by
    intro s hs
    have hbase :
        0 ≤
          γ * (⟪g, eval (segment s hs)⟫_ℝ - ⟪g, eval xp⟫_ℝ) +
            (V x (segment s hs) - V x xp) +
            γ * (h (segment s hs) - h xp) :=
      prox_minimality_scaled_difference_nonneg
        (SOptLib.proxObjective V h eval) V eval h x xp (segment s hs) g hγ
        hobjective hmin
    have hseg :=
      prox_segment_majorized_lower_bound eval V h x xp u (segment s hs)
        g γ s hγ.le hbase (hsegment_eval s hs) (hh_segment s hs)
    have hβs : β s = V x (segment s hs) - V x xp := by
      dsimp [β]
      rw [dif_pos hs]
    simpa [φ, hβs, mul_assoc, add_assoc] using hseg
  have hβderiv :
      HasDerivWithinAt β
        ⟪grad xp - grad x, eval u - eval xp⟫_ℝ (Set.Icc (0 : ℝ) 1) 0 := by
    simpa [β] using hV_deriv
  have hφderiv :
      HasDerivWithinAt φ
        (γ * ⟪g, eval u - eval xp⟫_ℝ +
          ⟪grad xp - grad x, eval u - eval xp⟫_ℝ +
          γ * (h u - h xp))
        (Set.Icc (0 : ℝ) 1) 0 := by
    simpa [φ, β] using
      prox_majorant_hasDerivWithinAt_zero β g (eval u - eval xp)
        (grad xp - grad x) γ (h u - h xp) hβderiv
  exact
    prox_scaled_variational_inequality_of_argmin eval grad h x xp u
      g γ φ hφ0 hφ_nonneg hφderiv

end SOptLib
