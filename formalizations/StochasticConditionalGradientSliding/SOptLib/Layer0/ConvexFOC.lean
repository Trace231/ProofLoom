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
import SOptLib.Model.Stationarity

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
--     "exists_linear_model_maximizer_on_compact",
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

end SOptLib

open scoped InnerProductSpace

/-- Nonnegative directed carrier Bregman divergences imply carrier-gradient monotonicity.

For any feasible carrier subtype, if every directed carrier Bregman divergence
generated by `v` and `grad` is nonnegative, then the selected carrier gradient is
monotone in the Hilbert pairing.

Layer: Layer0 | Gap: Level 0 (Bregman nonnegativity to carrier-gradient monotonicity)
Proof: add the two directed nonnegativity inequalities and rewrite the symmetric
  Bregman sum by the carrier Bregman gradient-pairing identity.
Source: Mathlib ordered real arithmetic and SOptLib carrier Bregman algebra
Used in: randomized accelerated proximal-gradient carrier objective convexity step
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem carrierGradient_monotone_of_bregman_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (v : {x : E // x ∈ X} → ℝ)
    (grad : {x : E // x ∈ X} → E)
    (hBreg_nonneg :
      ∀ x y : {x : E // x ∈ X}, 0 ≤ SOptLib.carrierBregmanDivergence v grad x y)
    (x y : {x : E // x ∈ X}) :
    0 ≤ ⟪grad x - grad y, x.1 - y.1⟫_ℝ := by
  have hsum :
      0 ≤
        SOptLib.carrierBregmanDivergence v grad y x +
          SOptLib.carrierBregmanDivergence v grad x y :=
    add_nonneg (hBreg_nonneg y x) (hBreg_nonneg x y)
  rwa [carrierBregmanDivergence_add_swap_eq_inner_grad_sub v grad y x] at hsum

open scoped BigOperators
open scoped InnerProductSpace

namespace Convex

/-- A constrained minimizer of a finite average plus a base term satisfies the
finite-sum first-order variational inequality.

If `x` minimizes `card ι` inverse times the component sum plus `phi` on a convex
set `X`, and `phi` and each component `psi i` have the supplied within-gradients
at `x`, then the averaged component gradient plus the base gradient has
nonnegative pairing with every feasible direction.

Layer: Layer0 | Gap: Level 1 (finite-sum constrained first-order condition)
Proof: assemble the within Fréchet derivative of the finite average and added
  base term, apply the constrained first-order condition for convex sets, and
  rewrite the resulting continuous-linear-map value as inner products.
Source: Mathlib convex first-order conditions, finite Fréchet-derivative sums,
  and Hilbert-space gradient APIs
Used in: randomized accelerated proximal-point finite-sum subproblem optimality
  and variance-reduced proximal subproblem optimality
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem first_order_condition_sum_add_of_isMinOn
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {X : Set E} {x y : E} {phi : E → ℝ} {psi : ι → E → ℝ}
    {gradPhi : E} {gradPsi : ι → E}
    (hX : Convex ℝ X) (hx : x ∈ X) (hy : y ∈ X)
    (hmin : ∀ u ∈ X,
      (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i : ι => psi i x) +
          phi x ≤
        (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i : ι => psi i u) +
          phi u)
    (hphi : HasGradientWithinAt phi gradPhi X x)
    (hpsi : ∀ i : ι, HasGradientWithinAt (psi i) (gradPsi i) X x) :
    0 ≤
      ⟪gradPhi, y - x⟫_ℝ +
        (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ (fun i : ι => ⟪gradPsi i, y - x⟫_ℝ) := by
  classical
  let F : E → ℝ := fun u =>
    (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i : ι => psi i u) +
      phi u
  let G : E := gradPhi +
    (Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ (fun i : ι => gradPsi i)
  have hsum : HasFDerivWithinAt
      (fun u : E => Finset.sum Finset.univ (fun i : ι => psi i u))
      (Finset.sum Finset.univ
        (fun i : ι => InnerProductSpace.toDual ℝ E (gradPsi i))) X x := by
    refine HasFDerivWithinAt.fun_sum ?_
    intro i _hi
    exact (hpsi i).hasFDerivWithinAt
  have hscaled := hsum.const_smul ((Fintype.card ι : ℝ)⁻¹)
  have hderiv0 := hscaled.add hphi.hasFDerivWithinAt
  have hderiv : HasFDerivWithinAt F (InnerProductSpace.toDual ℝ E G) X x := by
    convert hderiv0 using 1
    ext v
    simp [G, map_add, map_smul, map_sum, add_comm]
  have hdir :=
    Convex.first_order_condition_of_isMinOn_hasFDerivWithinAt hX hx hy
      (by simpa [F] using hmin) hderiv
  simpa [G, inner_add_left, inner_smul_left, sum_inner] using hdir

end Convex

open scoped InnerProductSpace

/-- A positive centered quadratic plus a linear term and nonnegative residual gives a
coercive lower-tail bound.

If `F` is bounded below on `X` by `a * ‖x - z‖ ^ 2 + ⟪g, x⟫ + Rterm x`,
where `a > 0` and the residual is nonnegative on `X`, then every real target is
eventually below `F` outside a sufficiently large ball centered at `z`.

Layer: Layer0 | Gap: Level 1 (positive quadratic objective lower-tail coercivity)
Proof: reduce to the scalar positive-quadratic tail lemma with radius
  `‖x - z‖`, use Cauchy-Schwarz to lower-bound the linear term, and add the
  nonnegative residual before applying the pointwise lower bound for `F`.
Source: Mathlib inner-product Cauchy-Schwarz inequality and ordered real arithmetic
Used in: randomized accelerated proximal-point prox-subproblem compact truncation
  after establishing a quadratic-plus-oracle lower model
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal point -/
theorem coercive_lower_bound_of_pos_quadratic_add_linear_add_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (x0 z g : E) {a : ℝ} (Rterm F : E → ℝ)
    (ha : 0 < a)
    (hF_lower :
      ∀ x : E, x ∈ X → a * ‖x - z‖ ^ 2 + ⟪g, x⟫_ℝ + Rterm x ≤ F x)
    (hRterm_nonneg : ∀ x : E, x ∈ X → 0 ≤ Rterm x) :
    ∀ B : ℝ, ∃ R : ℝ, ‖x0 - z‖ ≤ R ∧
      ∀ x : E, x ∈ X → R ≤ ‖x - z‖ → B ≤ F x := by
  intro B
  obtain ⟨R0, _hR0_nonneg, hR0_tail⟩ :=
    exists_nonneg_forall_le_quadratic_sub_linear_of_pos
      (a := a) ha ‖g‖ ⟪g, z⟫_ℝ B
  let R : ℝ := max R0 ‖x0 - z‖
  refine ⟨R, ?_, ?_⟩
  · dsimp [R]
    exact le_max_right _ _
  · intro x hx hfar
    have hR0_le_R : R0 ≤ R := by
      dsimp [R]
      exact le_max_left _ _
    have hR0_le_norm : R0 ≤ ‖x - z‖ := le_trans hR0_le_R hfar
    have hscalar :
        B ≤ a * ‖x - z‖ ^ 2 - ‖g‖ * ‖x - z‖ + ⟪g, z⟫_ℝ :=
      hR0_tail ‖x - z‖ hR0_le_norm
    have hinner_abs : |⟪g, x - z⟫_ℝ| ≤ ‖g‖ * ‖x - z‖ :=
      abs_real_inner_le_norm g (x - z)
    have hinner_lower : -(‖g‖ * ‖x - z‖) ≤ ⟪g, x - z⟫_ℝ := by
      have hneg_abs : -⟪g, x - z⟫_ℝ ≤ |⟪g, x - z⟫_ℝ| := neg_le_abs _
      linarith
    have hinner_decomp : ⟪g, x⟫_ℝ = ⟪g, z⟫_ℝ + ⟪g, x - z⟫_ℝ := by
      rw [inner_sub_right]
      abel
    have hlinear :
        ⟪g, z⟫_ℝ - ‖g‖ * ‖x - z‖ ≤ ⟪g, x⟫_ℝ := by
      nlinarith
    have hresidual : 0 ≤ Rterm x := hRterm_nonneg x hx
    have hmodel : B ≤ a * ‖x - z‖ ^ 2 + ⟪g, x⟫_ℝ + Rterm x := by
      nlinarith
    exact le_trans hmodel (hF_lower x hx)

open scoped InnerProductSpace

namespace SOptLib

/-- A constrained minimizer with a within-gradient has gradient in the negative
normal cone.

If `x` minimizes `f` over a convex feasible set `X` and `f` has within-gradient
`G` at `x` along `X`, then `G` is a negative normal-cone vector at `x`, i.e.
`-G ∈ N_X(x)`.

Layer: Layer0 | Gap: Level 0 (constrained minimizer stationarity certificate)
Proof: apply the constrained first-order condition for within Fréchet
  derivatives to each feasible direction, convert the dual action to the
  inner product with `G`, and unfold normal-cone membership.
Source: Mathlib and SOptLib convex first-order condition APIs for within
  derivatives in real Hilbert spaces
Used in: finite-sum proximal subproblem optimality as a normal-cone
  stationarity certificate
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem mem_negativeNormalCone_of_isMinOn_hasGradientWithinAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {X : Set E} {f : E → ℝ} {x G : E}
    (hXconv : Convex ℝ X) (hx : x ∈ X)
    (hmin : IsMinOn f X x) (hgrad : HasGradientWithinAt f G X x) :
    G ∈ {v : E | -v ∈ normalCone X x} := by
  change -G ∈ normalCone X x
  rw [mem_normalCone]
  intro y hy
  have hdir :
      0 ≤ (InnerProductSpace.toDual ℝ E G) (y - x) :=
    Convex.first_order_condition_of_isMinOn_hasFDerivWithinAt
      hXconv hx hy hmin hgrad.hasFDerivWithinAt
  have hdir_inner : 0 ≤ ⟪G, y - x⟫_ℝ := by
    simpa using hdir
  rw [inner_neg_left]
  exact neg_nonpos.mpr hdir_inner

end SOptLib

