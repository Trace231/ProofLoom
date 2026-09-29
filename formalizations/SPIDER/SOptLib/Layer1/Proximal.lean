import SOptLib.Model.Objective
-- SOptLib/Layer1/Proximal.lean
import SOptLib.Layer0.ConvexFOC
import SOptLib.Model.Bregman
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic
import SOptLib.Glue.Algebra
import SOptLib.Glue.Calculus
import SOptLib.Model.StochasticOracle
import SOptLib.Model.Subdifferential


open scoped Gradient InnerProductSpace

/-- Mirror descent three-point inequality from the variational inequality for the prox
subproblem and the Bregman three-point identity.
Layer: Layer1 | Gap: Level 1 (mirror-descent prox three-point algebra)
Proof: Expand the variational inequality into an inner-product bound, then combine it
  with the Bregman three-point identity.
Source: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  Lemma 3.4 and Eq. (3.2.6).
Used in: stochastic mirror descent Lemma 3.4 auxiliary inequality
Book citation: `book/FOML/StochasticMirrorDescent.json#/assumptions/5/math`
Origin algorithm: FOML stochastic mirror descent -/
theorem mirror_descent_three_point_of_variational
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {v : E → ℝ} {g : E} {x_t x_next x : E} {γ : ℝ}
    (h_variational :
      0 ≤ ⟪γ • g + ∇ v x_next - ∇ v x_t, x - x_next⟫_ℝ) :
    γ * ⟪g, x_next - x⟫_ℝ + bregmanDivergence v x_t x_next ≤
      bregmanDivergence v x_t x - bregmanDivergence v x_next x := by
  have hinner :
      γ * ⟪g, x_next - x⟫_ℝ ≤
        ⟪∇ v x_next - ∇ v x_t, x - x_next⟫_ℝ := by
    have hdiff :
        ⟪∇ v x_next - ∇ v x_t, x - x_next⟫_ℝ =
          ⟪∇ v x_next, x - x_next⟫_ℝ -
            ⟪∇ v x_t, x - x_next⟫_ℝ := by
      rw [inner_sub_left]
    have hopt_expanded :
        0 ≤ γ * ⟪g, x - x_next⟫_ℝ +
          ⟪∇ v x_next - ∇ v x_t, x - x_next⟫_ℝ := by
      calc
        0 ≤ ⟪γ • g + ∇ v x_next - ∇ v x_t, x - x_next⟫_ℝ := h_variational
        _ = γ * ⟪g, x - x_next⟫_ℝ +
              ⟪∇ v x_next - ∇ v x_t, x - x_next⟫_ℝ := by
          rw [hdiff, inner_sub_left, inner_add_left, inner_smul_left]
          simp
          ring
    have hneg : ⟪g, x_next - x⟫_ℝ = - ⟪g, x - x_next⟫_ℝ := by
      have hxsub : x_next - x = -(x - x_next) := by
        abel
      rw [hxsub, inner_neg_right]
    rw [hneg]
    nlinarith
  have h3 := bregmanDivergence_three_point_identity (v := v) (x := x_t) (y := x_next) (z := x)
  nlinarith [hinner, h3]

/-- Mirror descent three-point inequality from a variational inequality and a
carrier three-point identity.

Layer: Layer1 | Gap: Level 1 (mirror descent prox three-point inequality)
Proof: expand the variational inequality using inner-product linearity and
  rewrite the reversed difference by negation; combine the resulting scalar
  bound with the carrier identity using ordered-ring arithmetic.
Source: Mathlib inner product space algebra and linear ordered field arithmetic APIs
Used in: stochastic mirror descent prox-step three-point regret estimate
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem mirror_descent_three_point_of_variational_carrier
    {P E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (V : P → P → ℝ) (eval grad : P → E)
    (x z y : P) (g : E) (γ : ℝ)
    (h_variational :
      0 ≤ ⟪γ • g + grad z - grad x, eval y - eval z⟫_ℝ)
    (h_three_point :
      V x y = V x z + ⟪grad z - grad x, eval y - eval z⟫_ℝ + V z y) :
    γ * ⟪g, eval z - eval y⟫_ℝ + V x z ≤
      V x y - V z y := by
  have hinner :
      γ * ⟪g, eval z - eval y⟫_ℝ ≤
        ⟪grad z - grad x, eval y - eval z⟫_ℝ := by
    have hvar_expanded :
        0 ≤ γ * ⟪g, eval y - eval z⟫_ℝ +
          ⟪grad z - grad x, eval y - eval z⟫_ℝ := by
      have hdiff :
          ⟪grad z - grad x, eval y - eval z⟫_ℝ =
            ⟪grad z, eval y - eval z⟫_ℝ - ⟪grad x, eval y - eval z⟫_ℝ := by
        rw [inner_sub_left]
      calc
        0 ≤ ⟪γ • g + grad z - grad x, eval y - eval z⟫_ℝ := h_variational
        _ = γ * ⟪g, eval y - eval z⟫_ℝ +
              ⟪grad z - grad x, eval y - eval z⟫_ℝ := by
          rw [hdiff, inner_sub_left, inner_add_left, inner_smul_left]
          simp
          ring
    have hneg : ⟪g, eval z - eval y⟫_ℝ = - ⟪g, eval y - eval z⟫_ℝ := by
      have hsub : eval z - eval y = -(eval y - eval z) := by
        abel
      rw [hsub, inner_neg_right]
    rw [hneg]
    nlinarith
  nlinarith [hinner, h_three_point]

/-- An inner product minus a Bregman term is controlled by half the squared
dual norm under pointwise primal-dual support and Bregman lower bounds.

This is the standard Young-inequality step after a mirror/prox three-point
estimate: `⟪ζ, z - y⟫` is bounded by dual times primal, and the Bregman term
absorbs half the squared primal displacement.

Layer: Layer1 | Gap: Level 0 (Young inequality after Bregman lower bound)
Proof: combine the support bound with the Bregman lower bound, then apply the
  scalar square inequality `(a - b)^2 ≥ 0` to remove the primal displacement.
Source: Convex optimization mirror-descent algebra and Mathlib ordered-field
  arithmetic for real squares
Used in: stochastic block mirror descent Lemma 4.3 block prox-step scalar
  estimate
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem inner_sub_sub_bregman_le_half_dual_sq
    {P E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (eval : P → E) (V : P → P → ℝ) (primalNorm dualNorm : E → ℝ)
    (ζ : E) (z y : P)
    (hsupport :
      ⟪ζ, eval z - eval y⟫_ℝ ≤
        dualNorm ζ * primalNorm (eval z - eval y))
    (hlower :
      (1 / 2 : ℝ) * primalNorm (eval z - eval y) ^ 2 ≤ V z y) :
    ⟪ζ, eval z - eval y⟫_ℝ - V z y ≤
      (1 / 2 : ℝ) * dualNorm ζ ^ 2 := by
  have hyoung :
      dualNorm ζ * primalNorm (eval z - eval y) -
          (1 / 2 : ℝ) * primalNorm (eval z - eval y) ^ 2 ≤
        (1 / 2 : ℝ) * dualNorm ζ ^ 2 := by
    nlinarith [sq_nonneg (dualNorm ζ - primalNorm (eval z - eval y))]
  nlinarith

/-- A gamma-scaled prox three-point inequality plus dual support gives the
standard one-step mirror-descent bound.

The theorem is stated for an abstract carrier `P` evaluated in an inner-product
space `E`, an arbitrary directed potential `V`, and arbitrary primal/dual size
functionals.  The support and lower-bound hypotheses absorb the prox displacement
by Young's inequality, leaving the squared dual-size penalty.

Layer: Layer1 | Gap: Level 1 (gamma-scaled prox one-step descent)
Proof: scale the pointwise primal-dual support inequality by the nonnegative
  stepsize, absorb the displacement with the Bregman lower bound and Young's
  scalar square inequality, then split the current-to-comparator inner product
  through the prox point and combine with the three-point inequality.
Source: Convex optimization mirror-descent prox algebra and Mathlib real
  inner-product space arithmetic
Used in: stochastic block mirror descent sampled block prox step before aggregate
  Bregman-potential lifting
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem prox_gamma_step_bound_of_three_point_and_dual_support
    {P E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (V : P → P → ℝ) (eval : P → E) (primalNorm dualNorm : E → ℝ)
    (z y x : P) (g : E) (γ : ℝ)
    (hγ_nonneg : 0 ≤ γ)
    (hthree :
      γ * ⟪g, eval y - eval x⟫_ℝ + V z y ≤
        V z x - V y x)
    (hsupport :
      ⟪g, eval z - eval y⟫_ℝ ≤
        dualNorm g * primalNorm (eval z - eval y))
    (hlower :
      (1 / 2 : ℝ) * primalNorm (eval z - eval y) ^ 2 ≤ V z y) :
    γ * ⟪g, eval z - eval x⟫_ℝ ≤
      V z x - V y x + (1 / 2 : ℝ) * γ ^ 2 * dualNorm g ^ 2 := by
  have hscaled_support :
      γ * ⟪g, eval z - eval y⟫_ℝ ≤
        γ * (dualNorm g * primalNorm (eval z - eval y)) := by
    exact mul_le_mul_of_nonneg_left hsupport hγ_nonneg
  have hyoung :
      γ * (dualNorm g * primalNorm (eval z - eval y)) -
          (1 / 2 : ℝ) * primalNorm (eval z - eval y) ^ 2 ≤
        (1 / 2 : ℝ) * γ ^ 2 * dualNorm g ^ 2 := by
    nlinarith [sq_nonneg (γ * dualNorm g - primalNorm (eval z - eval y))]
  have hscaled_young :
      γ * ⟪g, eval z - eval y⟫_ℝ - V z y ≤
        (1 / 2 : ℝ) * γ ^ 2 * dualNorm g ^ 2 := by
    nlinarith
  have hsplit :
      γ * ⟪g, eval z - eval x⟫_ℝ =
        γ * ⟪g, eval z - eval y⟫_ℝ +
          γ * ⟪g, eval y - eval x⟫_ℝ := by
    have hvec : eval z - eval x = (eval z - eval y) + (eval y - eval x) := by
      abel
    rw [hvec, inner_add_right]
    ring
  rw [hsplit]
  nlinarith

/-- A minimizer of a linear plus carrier-Bregman objective satisfies the prox
three-point inequality.

For a convex feasible carrier, if `y` minimizes
`u ↦ ⟪ζ, u⟫ + D_ν(z,u)`, then every feasible comparison point `x` satisfies the
usual Bregman three-point prox inequality.

Layer: Layer1 | Gap: Level 1 (linear Bregman prox three-point inequality)
Proof: first derive the prox variational inequality from the `IsMinOn`
  hypothesis, then combine it with the carrier Bregman three-point identity via
  the abstract mirror-descent three-point algebra lemma.
Source: Mathlib inner-product algebra, SOptLib carrier Bregman calculus, and
  constrained first-order optimality APIs
Used in: stochastic block mirror descent block prox-step three-point regret
  estimate and mirror descent prox-step descent bounds
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem prox_three_point_of_isMinOn_linear_bregman
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
    ⟪ζ, y.1 - x.1⟫_ℝ + carrierBregmanDivergence nu grad z y ≤
      carrierBregmanDivergence nu grad z x -
        carrierBregmanDivergence nu grad y x := by
  have hvar :
      0 ≤ ⟪(1 : ℝ) • ζ + grad y - grad z, x.1 - y.1⟫_ℝ := by
    simpa using
      prox_variational_inequality_of_isMinOn_linear_bregman
        (hX_convex := hX_convex)
        (nu := nu) (nuAmbient := nuAmbient) (grad := grad)
        (z := z) (y := y) (x := x) (ζ := ζ)
        hnu_eq_segment hnu_diff hgrad_apply hmin
  have hthree :
      carrierBregmanDivergence nu grad z x =
        carrierBregmanDivergence nu grad z y +
          ⟪grad y - grad z, x.1 - y.1⟫_ℝ +
            carrierBregmanDivergence nu grad y x := by
    exact
      carrierBregmanDivergence_three_point_identity
        (v := nu) (eval := fun u : {x : E // x ∈ X} => u.1)
        (grad := grad) (V := carrierBregmanDivergence nu grad)
        (by
          intro a b
          rfl)
        z y x
  simpa using
    mirror_descent_three_point_of_variational_carrier
      (V := carrierBregmanDivergence nu grad)
      (eval := fun u : {x : E // x ∈ X} => u.1) (grad := grad)
      (x := z) (z := y) (y := x) (g := ζ) (γ := (1 : ℝ))
      hvar hthree

/-- Summing mirror-descent one-step bounds obtained from a three-point inequality and
Young absorption gives the finite-window regret bound.

The theorem is stated for an abstract carrier `P` evaluated in an inner-product
space `E`, an arbitrary directed potential `V`, and an arbitrary dual-size
functional.  The pointwise three-point and Young hypotheses are enough to produce
both the per-step mirror bound and its telescoped sum.

Layer: Layer1 | Gap: Level 1 (mirror-descent finite-window prox recursion)
Proof: split the current-to-comparator inner product through the next iterate,
combine the three-point and Young inequalities, sum the resulting one-step bounds,
and telescope the directed potential while dropping the nonnegative terminal tail.
Source: Lan mirror descent prox-recursion algebra and Mathlib finite-sum telescope APIs
Used in: stochastic block mirror descent block prox-recursion Lemma 4.3 summed regret bound
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/key_lemmas/0/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic block mirror descent -/
theorem mirror_descent_sum_bound_of_three_point_and_young
    {P E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (V : P → P → ℝ) (eval : P → E) (dualNorm : E → ℝ)
    (ζ : ℕ → E) (v : ℕ → P) (j : ℕ)
    (hthree :
      ∀ t x, t < j →
        ⟪ζ t, eval (v (t + 1)) - eval x⟫_ℝ + V (v t) (v (t + 1)) ≤
          V (v t) x - V (v (t + 1)) x)
    (hyoung :
      ∀ t, t < j →
        ⟪ζ t, eval (v t) - eval (v (t + 1))⟫_ℝ -
            V (v t) (v (t + 1)) ≤
          (1 / 2 : ℝ) * dualNorm (ζ t) ^ 2)
    (hterminal_nonneg : ∀ x, 0 ≤ V (v j) x) :
    (∀ t x, t < j →
      ⟪ζ t, eval (v t) - eval x⟫_ℝ ≤
        V (v t) x - V (v (t + 1)) x +
          (1 / 2 : ℝ) * dualNorm (ζ t) ^ 2) ∧
    ∀ x,
      Finset.sum (Finset.range j) (fun t => ⟪ζ t, eval (v t) - eval x⟫_ℝ) ≤
        V (v 0) x +
          (1 / 2 : ℝ) * Finset.sum (Finset.range j) (fun t => dualNorm (ζ t) ^ 2) := by
  have hstep :
      ∀ t x, t < j →
        ⟪ζ t, eval (v t) - eval x⟫_ℝ ≤
          V (v t) x - V (v (t + 1)) x +
            (1 / 2 : ℝ) * dualNorm (ζ t) ^ 2 := by
    intro t x ht
    have hsplit :
        ⟪ζ t, eval (v t) - eval x⟫_ℝ =
          ⟪ζ t, eval (v t) - eval (v (t + 1))⟫_ℝ +
            ⟪ζ t, eval (v (t + 1)) - eval x⟫_ℝ := by
      have hvec :
          eval (v t) - eval x =
            (eval (v t) - eval (v (t + 1))) +
              (eval (v (t + 1)) - eval x) := by
        abel
      rw [hvec, inner_add_right]
    rw [hsplit]
    nlinarith [hthree t x ht, hyoung t ht]
  constructor
  · exact hstep
  · intro x
    have hsum :
        Finset.sum (Finset.range j) (fun t => ⟪ζ t, eval (v t) - eval x⟫_ℝ) ≤
          Finset.sum (Finset.range j) (fun t =>
            V (v t) x - V (v (t + 1)) x +
              (1 / 2 : ℝ) * dualNorm (ζ t) ^ 2) := by
      exact Finset.sum_le_sum (fun t ht => hstep t x (Finset.mem_range.mp ht))
    have htel :
        Finset.sum (Finset.range j) (fun t => V (v t) x - V (v (t + 1)) x) ≤
          V (v 0) x := by
      have htel_eq :
          Finset.sum (Finset.range j) (fun t => V (v t) x - V (v (t + 1)) x) =
            V (v 0) x - V (v j) x := by
        simpa using
          (Finset.sum_range_sub' (fun t => V (v t) x) j)
      rw [htel_eq]
      nlinarith [hterminal_nonneg x]
    calc
      Finset.sum (Finset.range j) (fun t => ⟪ζ t, eval (v t) - eval x⟫_ℝ)
          ≤ Finset.sum (Finset.range j) (fun t =>
              V (v t) x - V (v (t + 1)) x +
                (1 / 2 : ℝ) * dualNorm (ζ t) ^ 2) := hsum
      _ =
          Finset.sum (Finset.range j) (fun t => V (v t) x - V (v (t + 1)) x) +
            (1 / 2 : ℝ) * Finset.sum (Finset.range j) (fun t => dualNorm (ζ t) ^ 2) := by
            simp [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ V (v 0) x +
          (1 / 2 : ℝ) * Finset.sum (Finset.range j) (fun t => dualNorm (ζ t) ^ 2) := by
            nlinarith

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
  have hvar := right_derivative_nonneg_of_min_on_Icc hφderiv hφmin
  have h3x := hV_three xTilde uHat u
  have h3y := hV_three yTilde uHat u
  nlinarith

/-- An alpha-scaled weighted Bregman bound absorbs a completed stochastic tail.

If a weighted Bregman budget dominates the quadratic with coefficient
`c / (2 * gamma)`, the active denominator is `c - L * a * gamma`, and the
stochastic residual has already been completed against that denominator, then
the smoothness quadratic, Lipschitz linear term, Bregman subtraction, and noise
inner product collapse to the completed-square tail.

Layer: Layer1 | Gap: Level 1 (alpha-scaled Bregman tail absorption)
Proof: scale the weighted Bregman lower bound by the nonnegative alpha, rewrite
  `den + L * a * gamma` to the weighted coefficient, move the Bregman term to
  the negative side, and insert the completion-square premise.
Source: Lan accelerated stochastic-gradient estimate-sequence algebra and
  Mathlib ordered-field arithmetic for denominator completion
Used in: stochastic accelerated gradient descent alpha-scaled stochastic-error
  tail before the one-step Bregman recurrence
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/steps/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem alpha_scaled_bregman_tail_absorption_of_weighted_bound
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {a L M gamma c den breg : ℝ} {δ d : E}
    (ha : 0 ≤ a)
    (hgamma : 0 < gamma)
    (hden_def : den = c - L * a * gamma)
    (hweighted_absorb :
      (c / (2 * gamma)) * ‖d‖ ^ 2 ≤ breg)
    (hDeltaSquare :
      a * (M * ‖d‖ - ⟪δ, d⟫_ℝ -
        den / (2 * gamma) * ‖d‖ ^ 2) ≤
          a * gamma * (M + ‖δ‖) ^ 2 / (2 * den)) :
    L / 2 * (a * ‖d‖) ^ 2 + M * (a * ‖d‖) - a * breg -
        a * ⟪δ, d⟫_ℝ ≤
      a * gamma * (M + ‖δ‖) ^ 2 / (2 * den) := by
  have hgamma_ne : gamma ≠ 0 := ne_of_gt hgamma
  have hBregScaled :
      a * (((den + L * a * gamma) / (2 * gamma)) * ‖d‖ ^ 2) ≤ a * breg := by
    have hbase :
        a * ((c / (2 * gamma)) * ‖d‖ ^ 2) ≤ a * breg :=
      mul_le_mul_of_nonneg_left hweighted_absorb ha
    have hden_add : den + L * a * gamma = c := by
      rw [hden_def]
      ring
    simpa [hden_add] using hbase
  have hquad :
      L / 2 * (a * ‖d‖) ^ 2 - a * breg ≤
        -a * (den / (2 * gamma) * ‖d‖ ^ 2) := by
    have hneg :
        -a * breg ≤
          -a * (((den + L * a * gamma) / (2 * gamma)) * ‖d‖ ^ 2) := by
      linarith
    have hident :
        L / 2 * (a * ‖d‖) ^ 2 -
            a * (((den + L * a * gamma) / (2 * gamma)) * ‖d‖ ^ 2) =
          -a * (den / (2 * gamma) * ‖d‖ ^ 2) := by
      field_simp [hgamma_ne]
      ring
    nlinarith
  have hcore :
      -a * (den / (2 * gamma) * ‖d‖ ^ 2) +
          (M * (a * ‖d‖) - a * ⟪δ, d⟫_ℝ) ≤
        a * gamma * (M + ‖δ‖) ^ 2 / (2 * den) := by
    calc
      -a * (den / (2 * gamma) * ‖d‖ ^ 2) +
          (M * (a * ‖d‖) - a * ⟪δ, d⟫_ℝ)
          =
        a * (M * ‖d‖ - ⟪δ, d⟫_ℝ -
          den / (2 * gamma) * ‖d‖ ^ 2) := by
          ring
      _ ≤ a * gamma * (M + ‖δ‖) ^ 2 / (2 * den) := hDeltaSquare
  calc
    L / 2 * (a * ‖d‖) ^ 2 + M * (a * ‖d‖) - a * breg -
        a * ⟪δ, d⟫_ℝ
        =
      (L / 2 * (a * ‖d‖) ^ 2 - a * breg) +
        (M * (a * ‖d‖) - a * ⟪δ, d⟫_ℝ) := by
        ring
    _ ≤ -a * (den / (2 * gamma) * ‖d‖ ^ 2) +
        (M * (a * ‖d‖) - a * ⟪δ, d⟫_ℝ) := by
        linarith
    _ ≤ a * gamma * (M + ‖δ‖) ^ 2 / (2 * den) := by
        linarith

/-- An accelerated Bregman recurrence gives a squared-norm endpoint bound.

If the current objective value dominates the reference value, the local
linearized model at the reference is bounded by that reference objective value,
and the terminal Bregman term lower-bounds half the squared endpoint distance,
then the accelerated recurrence controls the endpoint squared distance by the
previous objective gap, previous Bregman budget, and stochastic tail.

Layer: Layer1 | Gap: Level 1 (accelerated recurrence endpoint metric boundary)
Proof: relax the model term in the recurrence to the reference objective,
  isolate the terminal Bregman term, scale the one-sided Bregman lower bound,
  and use `1 ≤ 1 + μγ` to drop the extra terminal coefficient.
Source: Lan accelerated stochastic-gradient estimate-sequence algebra and
  Mathlib real inner-product/order arithmetic APIs
Used in: stochastic accelerated gradient descent conversion from the one-step
  Bregman recurrence at an optimizer to endpoint L2 control
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/steps/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem sq_norm_endpoint_le_of_accelerated_bregman_recurrence
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Psi f h : E → ℝ) (V : E → E → ℝ) (grad : E → E)
    (alpha gamma mu L M : ℝ)
    (prevBar prevCenter xUnder z xRef xPlus xBar eta : E)
    (halpha_pos : 0 < alpha)
    (hgamma_pos : 0 < gamma)
    (hmu_nonneg : 0 ≤ mu)
    (hPsi_ref_le_xBar : Psi xRef ≤ Psi xBar)
    (hmodel_le :
      f xUnder + ⟪grad xUnder, xRef - xUnder⟫_ℝ + h xRef +
          mu * V xUnder xRef ≤
        Psi xRef)
    (hVz_lower :
      (1 / 2 : ℝ) * ‖z - xRef‖ ^ 2 ≤ V z xRef)
    (hrec :
      Psi xBar ≤
        (1 - alpha) * Psi prevBar +
          alpha *
            (f xUnder + ⟪grad xUnder, xRef - xUnder⟫_ℝ + h xRef +
              mu * V xUnder xRef) +
          alpha / gamma *
            (V prevCenter xRef - (1 + mu * gamma) * V z xRef) +
          alpha * gamma * (M + ‖eta‖) ^ 2 /
            (2 * (1 + mu * gamma - L * alpha * gamma)) +
          alpha * ⟪eta, xRef - xPlus⟫_ℝ) :
    alpha / (2 * gamma) * ‖z - xRef‖ ^ 2 ≤
      (1 - alpha) * (Psi prevBar - Psi xRef) +
        alpha / gamma * V prevCenter xRef +
        alpha * gamma * (M + ‖eta‖) ^ 2 /
          (2 * (1 + mu * gamma - L * alpha * gamma)) +
        alpha * ⟪eta, xRef - xPlus⟫_ℝ := by
  let c : ℝ := 1 + mu * gamma
  let tail : ℝ :=
    alpha * gamma * (M + ‖eta‖) ^ 2 /
      (2 * (1 + mu * gamma - L * alpha * gamma))
  have halpha_nonneg : 0 ≤ alpha := le_of_lt halpha_pos
  have hgamma_nonneg : 0 ≤ gamma := le_of_lt hgamma_pos
  have hgamma_ne : gamma ≠ 0 := ne_of_gt hgamma_pos
  have hc_ge_one : 1 ≤ c := by
    dsimp [c]
    have hmul_nonneg : 0 ≤ mu * gamma := mul_nonneg hmu_nonneg hgamma_nonneg
    linarith
  have hc_nonneg : 0 ≤ c := by linarith
  have hmodel_scaled :
      alpha *
        (f xUnder + ⟪grad xUnder, xRef - xUnder⟫_ℝ + h xRef +
          mu * V xUnder xRef) ≤
        alpha * Psi xRef :=
    mul_le_mul_of_nonneg_left hmodel_le halpha_nonneg
  have hrec_relaxed :
      Psi xRef ≤
        (1 - alpha) * Psi prevBar +
          alpha * Psi xRef +
          alpha / gamma * (V prevCenter xRef - c * V z xRef) +
          tail +
          alpha * ⟪eta, xRef - xPlus⟫_ℝ := by
    have hrec' : Psi xBar ≤
        (1 - alpha) * Psi prevBar +
          alpha *
            (f xUnder + ⟪grad xUnder, xRef - xUnder⟫_ℝ + h xRef +
              mu * V xUnder xRef) +
          alpha / gamma * (V prevCenter xRef - c * V z xRef) +
          tail +
          alpha * ⟪eta, xRef - xPlus⟫_ℝ := by
      simpa [c, tail] using hrec
    linarith
  have hV_budget :
      alpha / gamma * (c * V z xRef) ≤
        (1 - alpha) * (Psi prevBar - Psi xRef) +
          alpha / gamma * V prevCenter xRef +
          tail +
          alpha * ⟪eta, xRef - xPlus⟫_ℝ := by
    nlinarith [hrec_relaxed]
  have hcoef_nonneg : 0 ≤ alpha / gamma * c := by positivity
  have hscaled_lower :
      (alpha / gamma * c) * ((1 / 2 : ℝ) * ‖z - xRef‖ ^ 2) ≤
        (alpha / gamma * c) * V z xRef :=
    mul_le_mul_of_nonneg_left hVz_lower hcoef_nonneg
  have hleft_to_scaled :
      alpha / (2 * gamma) * ‖z - xRef‖ ^ 2 ≤
        (alpha / gamma * c) * ((1 / 2 : ℝ) * ‖z - xRef‖ ^ 2) := by
    have hbase_nonneg : 0 ≤ alpha * ‖z - xRef‖ ^ 2 := by positivity
    have hmulc :
        alpha * ‖z - xRef‖ ^ 2 ≤
          alpha * ‖z - xRef‖ ^ 2 * c := by
      nlinarith [hc_ge_one, hbase_nonneg]
    field_simp [hgamma_ne]
    nlinarith [hmulc]
  have hscaled_to_V :
      (alpha / gamma * c) * ((1 / 2 : ℝ) * ‖z - xRef‖ ^ 2) ≤
        alpha / gamma * (c * V z xRef) := by
    calc
      (alpha / gamma * c) * ((1 / 2 : ℝ) * ‖z - xRef‖ ^ 2)
          ≤ (alpha / gamma * c) * V z xRef := hscaled_lower
      _ = alpha / gamma * (c * V z xRef) := by ring
  exact (hleft_to_scaled.trans hscaled_to_V).trans (by
    simpa [c, tail] using hV_budget)

/-- An accelerated composite recurrence from a two-Bregman descent inequality.

If a composite upper model at the averaged point, a two-anchor Bregman prox
descent inequality, and an alpha-scaled residual tail bound hold at one step,
then the reference-point accelerated recurrence follows after splitting the
stochastic residual inner product through the auxiliary center.

Layer: Layer1 | Gap: Level 1 (accelerated two-Bregman one-step recurrence)
Proof: divide the two-Bregman descent inequality by the positive stepsize to
  replace the local model term, scale by the nonnegative acceleration weight,
  absorb the Bregman/noise tail, and use inner-product linearity to recenter
  the stochastic residual at the auxiliary point.
Source: Lan accelerated composite-gradient estimate-sequence algebra and
  Mathlib real inner-product/order arithmetic APIs
Used in: stochastic accelerated gradient descent recurrence before the
  finite-window Bregman telescope
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem accelerated_composite_recurrence_of_two_bregman_descent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Psi f h : E → ℝ) (V : E → E → ℝ) (grad : E → E)
    (alpha gamma mu L M : ℝ)
    (prevBar prevCenter xUnder z xPlus xBar xRef g eta : E)
    (halpha_nonneg : 0 ≤ alpha)
    (hgamma_pos : 0 < gamma)
    (hnoise_decomp : g = grad xUnder + eta)
    (hUpper :
      Psi xBar ≤
        (1 - alpha) * Psi prevBar +
          alpha * (f xUnder + ⟪grad xUnder, z - xUnder⟫_ℝ + h z) +
          (L / 2) * (alpha * ‖z - xPlus‖) ^ 2 +
          M * (alpha * ‖z - xPlus‖))
    (htwo_bregman :
      gamma * (⟪g, z⟫_ℝ + h z) +
          (gamma * mu) * V xUnder z + (1 : ℝ) * V prevCenter z ≤
        gamma * (⟪g, xRef⟫_ℝ + h xRef) +
          (gamma * mu) * V xUnder xRef +
          (1 : ℝ) * V prevCenter xRef -
            ((gamma * mu) + (1 : ℝ)) * V z xRef)
    (htail :
      L / 2 * (alpha * ‖z - xPlus‖) ^ 2 +
          M * (alpha * ‖z - xPlus‖) -
          alpha * ((1 / gamma) * V prevCenter z + mu * V xUnder z) -
          alpha * ⟪eta, z - xPlus⟫_ℝ ≤
        alpha * gamma * (M + ‖eta‖) ^ 2 /
          (2 * (1 + mu * gamma - L * alpha * gamma))) :
    Psi xBar ≤
      (1 - alpha) * Psi prevBar +
        alpha *
          (f xUnder +
            ⟪grad xUnder, xRef - xUnder⟫_ℝ +
            h xRef +
            mu * V xUnder xRef) +
        alpha / gamma *
          (V prevCenter xRef - (1 + mu * gamma) * V z xRef) +
        alpha * gamma * (M + ‖eta‖) ^ 2 /
          (2 * (1 + mu * gamma - L * alpha * gamma)) +
        alpha * ⟪eta, xRef - xPlus⟫_ℝ := by
  let breg : ℝ := (1 / gamma) * V prevCenter z + mu * V xUnder z
  let tail : ℝ :=
    alpha * gamma * (M + ‖eta‖) ^ 2 /
      (2 * (1 + mu * gamma - L * alpha * gamma))
  have hgamma_ne : gamma ≠ 0 := ne_of_gt hgamma_pos
  have hprox_model :
      f xUnder + ⟪grad xUnder, z - xUnder⟫_ℝ + h z ≤
        f xUnder +
          ⟪grad xUnder, xRef - xUnder⟫_ℝ +
          h xRef +
          mu * V xUnder xRef +
          (1 / gamma) *
            (V prevCenter xRef - (1 + mu * gamma) * V z xRef) -
          breg +
          ⟪eta, xRef - z⟫_ℝ := by
    have hraw := htwo_bregman
    rw [hnoise_decomp] at hraw
    simp [inner_add_left] at hraw
    have hmul :
        gamma *
            (f xUnder + ⟪grad xUnder, z - xUnder⟫_ℝ + h z) ≤
          gamma *
            (f xUnder +
              ⟪grad xUnder, xRef - xUnder⟫_ℝ +
              h xRef +
              mu * V xUnder xRef +
              (1 / gamma) *
                (V prevCenter xRef - (1 + mu * gamma) * V z xRef) -
              breg +
              ⟪eta, xRef - z⟫_ℝ) := by
      dsimp [breg]
      simp [inner_sub_right]
      field_simp [hgamma_ne]
      nlinarith [hraw]
    nlinarith [hmul, hgamma_pos]
  have hModelScaled :
      alpha *
        (f xUnder + ⟪grad xUnder, z - xUnder⟫_ℝ + h z) ≤
      alpha *
        (f xUnder +
          ⟪grad xUnder, xRef - xUnder⟫_ℝ +
          h xRef +
          mu * V xUnder xRef +
          (1 / gamma) *
            (V prevCenter xRef - (1 + mu * gamma) * V z xRef) -
          breg +
          ⟪eta, xRef - z⟫_ℝ) :=
    mul_le_mul_of_nonneg_left hprox_model halpha_nonneg
  have htail_abbrev :
      L / 2 * (alpha * ‖z - xPlus‖) ^ 2 +
          M * (alpha * ‖z - xPlus‖) -
          alpha * breg -
          alpha * ⟪eta, z - xPlus⟫_ℝ ≤ tail := by
    simpa [breg, tail] using htail
  have hinner_split :
      ⟪eta, xRef - z⟫_ℝ =
        ⟪eta, xRef - xPlus⟫_ℝ - ⟪eta, z - xPlus⟫_ℝ := by
    have hvec : xRef - z = (xRef - xPlus) - (z - xPlus) := by
      abel
    rw [hvec, inner_sub_right]
  calc
    Psi xBar
        ≤ (1 - alpha) * Psi prevBar +
          alpha * (f xUnder + ⟪grad xUnder, z - xUnder⟫_ℝ + h z) +
          (L / 2) * (alpha * ‖z - xPlus‖) ^ 2 +
          M * (alpha * ‖z - xPlus‖) := hUpper
    _ ≤ (1 - alpha) * Psi prevBar +
          alpha *
            (f xUnder +
              ⟪grad xUnder, xRef - xUnder⟫_ℝ +
              h xRef +
              mu * V xUnder xRef +
              (1 / gamma) *
                (V prevCenter xRef - (1 + mu * gamma) * V z xRef) -
              breg +
              ⟪eta, xRef - z⟫_ℝ) +
          (L / 2) * (alpha * ‖z - xPlus‖) ^ 2 +
          M * (alpha * ‖z - xPlus‖) := by
        linarith
    _ = (1 - alpha) * Psi prevBar +
          alpha *
            (f xUnder +
              ⟪grad xUnder, xRef - xUnder⟫_ℝ +
              h xRef +
              mu * V xUnder xRef) +
          alpha / gamma *
            (V prevCenter xRef - (1 + mu * gamma) * V z xRef) +
          ((L / 2) * (alpha * ‖z - xPlus‖) ^ 2 +
            M * (alpha * ‖z - xPlus‖) -
            alpha * breg -
            alpha * ⟪eta, z - xPlus⟫_ℝ) +
          alpha * ⟪eta, xRef - xPlus⟫_ℝ := by
        rw [hinner_split]
        ring
    _ ≤ (1 - alpha) * Psi prevBar +
          alpha *
            (f xUnder +
              ⟪grad xUnder, xRef - xUnder⟫_ℝ +
              h xRef +
              mu * V xUnder xRef) +
          alpha / gamma *
            (V prevCenter xRef - (1 + mu * gamma) * V z xRef) +
          tail +
          alpha * ⟪eta, xRef - xPlus⟫_ℝ := by
        linarith
    _ = (1 - alpha) * Psi prevBar +
          alpha *
            (f xUnder +
              ⟪grad xUnder, xRef - xUnder⟫_ℝ +
              h xRef +
              mu * V xUnder xRef) +
          alpha / gamma *
            (V prevCenter xRef - (1 + mu * gamma) * V z xRef) +
          alpha * gamma * (M + ‖eta‖) ^ 2 /
            (2 * (1 + mu * gamma - L * alpha * gamma)) +
          alpha * ⟪eta, xRef - xPlus⟫_ℝ := by
        simp [tail]

/-- A scaled Bregman quadratic bound and a completed square absorb a smooth tail.

Once the scaled Bregman budget controls the quadratic coefficient
`(D + L * a * gamma) / (2 * gamma)` and the stochastic residual has been
completed against denominator `D`, the smoothness quadratic, Lipschitz linear
term, Bregman subtraction, stochastic inner product, and an additive tail term
collapse to the completed-square tail plus the same additive tail.

Layer: Layer1 | Gap: Level 1 (Bregman completion-square tail absorption)
Proof: move the scaled Bregman bound to the negative side, use field arithmetic
  to identify the remaining quadratic coefficient with `D / (2 * gamma)`, then
  insert the completion-square estimate and rearrange the additive tail.
Source: convex optimization estimate-sequence algebra and Mathlib real
  inner-product ordered-field arithmetic
Used in: stochastic accelerated gradient descent smoothness and stochastic-error
  tail absorption after the prox Bregman recurrence
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem smooth_quadratic_tail_absorption_of_bregman_and_completion_square
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {a L M gamma D breg tailNoise : ℝ} {δ d : E}
    (hgamma : 0 < gamma)
    (hBregScaled :
      a * (((D + L * a * gamma) / (2 * gamma)) * ‖d‖ ^ 2) ≤ a * breg)
    (hCompletionSquare :
      a * (M * ‖d‖ - ⟪δ, d⟫_ℝ -
        D / (2 * gamma) * ‖d‖ ^ 2) ≤
          a * gamma * (M + ‖δ‖) ^ 2 / (2 * D)) :
    L / 2 * (a * ‖d‖) ^ 2 + M * (a * ‖d‖) - a * breg +
        (a * tailNoise - a * ⟪δ, d⟫_ℝ) ≤
      a * gamma * (M + ‖δ‖) ^ 2 / (2 * D) + a * tailNoise := by
  have hgamma_ne : gamma ≠ 0 := ne_of_gt hgamma
  have hquad :
      L / 2 * (a * ‖d‖) ^ 2 - a * breg ≤
        -a * (D / (2 * gamma) * ‖d‖ ^ 2) := by
    have hneg :
        -a * breg ≤
          -a * (((D + L * a * gamma) / (2 * gamma)) * ‖d‖ ^ 2) := by
      linarith
    have hident :
        L / 2 * (a * ‖d‖) ^ 2 -
            a * (((D + L * a * gamma) / (2 * gamma)) * ‖d‖ ^ 2) =
          -a * (D / (2 * gamma) * ‖d‖ ^ 2) := by
      field_simp [hgamma_ne]
      ring
    nlinarith
  have hcore :
      -a * (D / (2 * gamma) * ‖d‖ ^ 2) +
          (M * (a * ‖d‖) - a * ⟪δ, d⟫_ℝ) ≤
        a * gamma * (M + ‖δ‖) ^ 2 / (2 * D) := by
    calc
      -a * (D / (2 * gamma) * ‖d‖ ^ 2) +
          (M * (a * ‖d‖) - a * ⟪δ, d⟫_ℝ)
          =
        a * (M * ‖d‖ - ⟪δ, d⟫_ℝ -
          D / (2 * gamma) * ‖d‖ ^ 2) := by
          ring
      _ ≤ a * gamma * (M + ‖δ‖) ^ 2 / (2 * D) := hCompletionSquare
  calc
    L / 2 * (a * ‖d‖) ^ 2 + M * (a * ‖d‖) - a * breg +
        (a * tailNoise - a * ⟪δ, d⟫_ℝ)
        =
      (L / 2 * (a * ‖d‖) ^ 2 - a * breg) +
        (M * (a * ‖d‖) - a * ⟪δ, d⟫_ℝ) + a * tailNoise := by
        ring
    _ ≤ -a * (D / (2 * gamma) * ‖d‖ ^ 2) +
        (M * (a * ‖d‖) - a * ⟪δ, d⟫_ℝ) + a * tailNoise := by
        linarith
    _ ≤ a * gamma * (M + ‖δ‖) ^ 2 / (2 * D) + a * tailNoise := by
        linarith

/-- A weighted center squared displacement is absorbed by two directed Bregman
lower bounds.

If `xPlus` is the normalized weighted center of `xUnder` and `xPrev` with
weight `mu * gamma`, and each directed kernel value lower-bounds one half of
the corresponding squared displacement to `xNext`, then the scaled distance
from `xNext` to `xPlus` is controlled by the weighted sum of the two kernel
values.

Layer: Layer1 | Gap: Level 1 (two-center Bregman weighted-center absorption)
Proof: apply the two-point weighted-center norm-square inequality with
  `r = mu * gamma`, scale by `1 / gamma`, and absorb both squared-distance
  terms with the supplied pointwise Bregman lower bounds.
Source: convex optimization Bregman coercivity algebra and Mathlib normed
  real vector-space ordered-field arithmetic
Used in: stochastic accelerated gradient descent two-center prox descent before
  the weighted Bregman recurrence is telescoped
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem two_center_bregman_absorbs_weighted_center_sq
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (V : E → E → ℝ) {mu gamma : ℝ} {xPrev xUnder xNext xPlus : E}
    (hmu_nonneg : 0 ≤ mu)
    (hgamma_pos : 0 < gamma)
    (hxplus :
      xPlus =
        (mu * gamma / (1 + mu * gamma)) • xUnder +
          (1 / (1 + mu * gamma)) • xPrev)
    (hVprev : (1 / 2 : ℝ) * ‖xPrev - xNext‖ ^ 2 ≤ V xPrev xNext)
    (hVunder : (1 / 2 : ℝ) * ‖xUnder - xNext‖ ^ 2 ≤ V xUnder xNext) :
    ((1 + mu * gamma) / (2 * gamma)) * ‖xNext - xPlus‖ ^ 2 ≤
      (1 / gamma) * V xPrev xNext + mu * V xUnder xNext := by
  have hgamma_nonneg : 0 ≤ gamma := le_of_lt hgamma_pos
  have hgamma_ne : gamma ≠ 0 := ne_of_gt hgamma_pos
  have hr_nonneg : 0 ≤ mu * gamma := mul_nonneg hmu_nonneg hgamma_nonneg
  have hgeom :
      ((1 + mu * gamma) / 2) *
          ‖xNext -
            ((mu * gamma / (1 + mu * gamma)) • xUnder +
              (1 / (1 + mu * gamma)) • xPrev)‖ ^ 2 ≤
        (1 / 2) * ‖xPrev - xNext‖ ^ 2 +
          (mu * gamma / 2) * ‖xUnder - xNext‖ ^ 2 :=
    weighted_sq_norm_sub_center_le (E := E) (u := xUnder) (v := xPrev)
      (y := xNext) (r := mu * gamma) hr_nonneg
  have hgeom_scaled :
      ((1 + mu * gamma) / (2 * gamma)) * ‖xNext - xPlus‖ ^ 2 ≤
        (1 / (2 * gamma)) * ‖xPrev - xNext‖ ^ 2 +
          (mu / 2) * ‖xUnder - xNext‖ ^ 2 := by
    rw [hxplus]
    have hinv_nonneg : 0 ≤ 1 / gamma := by positivity
    have hmul := mul_le_mul_of_nonneg_left hgeom hinv_nonneg
    convert hmul using 1 <;> field_simp [hgamma_ne] <;> ring
  have hVprev_scaled :
      (1 / (2 * gamma)) * ‖xPrev - xNext‖ ^ 2 ≤
        (1 / gamma) * V xPrev xNext := by
    have hinv_nonneg : 0 ≤ 1 / gamma := by positivity
    have hmul := mul_le_mul_of_nonneg_left hVprev hinv_nonneg
    convert hmul using 1 <;> ring
  have hVunder_scaled :
      (mu / 2) * ‖xUnder - xNext‖ ^ 2 ≤
        mu * V xUnder xNext := by
    have hmul := mul_le_mul_of_nonneg_left hVunder hmu_nonneg
    convert hmul using 1 <;> ring
  exact hgeom_scaled.trans (add_le_add hVprev_scaled hVunder_scaled)

/-- A two-center accelerated prox context gives a squared-norm endpoint bound.

The theorem packages the source-side one-step AC-SA boundary: a composite upper
model, a two-Bregman prox descent inequality, a weighted stochastic tail
absorption premise, and local minimizer/model comparison produce endpoint
squared-distance control while preserving the previous Bregman budget.

Layer: Layer1 | Gap: Level 1 (two-center accelerated prox endpoint boundary)
Proof: first absorb the alpha-scaled stochastic tail through the weighted
  Bregman bound, then form the accelerated composite recurrence from the
  two-Bregman descent inequality, and finally convert the terminal Bregman
  term into the endpoint squared norm.
Source: Lan accelerated stochastic-gradient estimate-sequence algebra and
  Mathlib real inner-product/order arithmetic APIs
Used in: stochastic accelerated gradient descent two-center prox bridge before
  the finite-window Bregman telescope
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/steps/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem sq_norm_endpoint_le_of_two_center_prox_context
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Psi f h : E → ℝ) (V : E → E → ℝ) (grad : E → E)
    (alpha gamma mu L M : ℝ)
    (prevBar prevCenter xUnder z xRef xPlus xBar g eta : E)
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_pos : 0 < alpha)
    (hgamma_pos : 0 < gamma)
    (hmu_nonneg : 0 ≤ mu)
    (hnoise_decomp : g = grad xUnder + eta)
    (hUpper :
      Psi xBar ≤
        (1 - alpha) * Psi prevBar +
          alpha * (f xUnder + ⟪grad xUnder, z - xUnder⟫_ℝ + h z) +
          (L / 2) * (alpha * ‖z - xPlus‖) ^ 2 +
          M * (alpha * ‖z - xPlus‖))
    (htwo_bregman :
      gamma * (⟪g, z⟫_ℝ + h z) +
          (gamma * mu) * V xUnder z + (1 : ℝ) * V prevCenter z ≤
        gamma * (⟪g, xRef⟫_ℝ + h xRef) +
          (gamma * mu) * V xUnder xRef +
          (1 : ℝ) * V prevCenter xRef -
            ((gamma * mu) + (1 : ℝ)) * V z xRef)
    (hweighted_absorb :
      ((1 + mu * gamma) / (2 * gamma)) * ‖z - xPlus‖ ^ 2 ≤
        (1 / gamma) * V prevCenter z + mu * V xUnder z)
    (hDeltaSquare :
      alpha *
          (M * ‖z - xPlus‖ - ⟪eta, z - xPlus⟫_ℝ -
            (1 + mu * gamma - L * alpha * gamma) /
              (2 * gamma) * ‖z - xPlus‖ ^ 2) ≤
        alpha * gamma * (M + ‖eta‖) ^ 2 /
          (2 * (1 + mu * gamma - L * alpha * gamma)))
    (hPsi_ref_le_xBar : Psi xRef ≤ Psi xBar)
    (hmodel_le :
      f xUnder + ⟪grad xUnder, xRef - xUnder⟫_ℝ + h xRef +
          mu * V xUnder xRef ≤
        Psi xRef)
    (hVz_lower :
      (1 / 2 : ℝ) * ‖z - xRef‖ ^ 2 ≤ V z xRef) :
    alpha / (2 * gamma) * ‖z - xRef‖ ^ 2 ≤
      (1 - alpha) * (Psi prevBar - Psi xRef) +
        alpha / gamma * V prevCenter xRef +
        alpha * gamma * (M + ‖eta‖) ^ 2 /
          (2 * (1 + mu * gamma - L * alpha * gamma)) +
        alpha * ⟪eta, xRef - xPlus⟫_ℝ := by
  have hsource_alpha_tail :
      L / 2 * (alpha * ‖z - xPlus‖) ^ 2 +
          M * (alpha * ‖z - xPlus‖) -
          alpha * ((1 / gamma) * V prevCenter z + mu * V xUnder z) -
          alpha * ⟪eta, z - xPlus⟫_ℝ ≤
        alpha * gamma * (M + ‖eta‖) ^ 2 /
          (2 * (1 + mu * gamma - L * alpha * gamma)) := by
    exact
      alpha_scaled_bregman_tail_absorption_of_weighted_bound
        (a := alpha) (L := L) (M := M) (gamma := gamma)
        (c := 1 + mu * gamma) (den := 1 + mu * gamma - L * alpha * gamma)
        (breg := (1 / gamma) * V prevCenter z + mu * V xUnder z)
        (δ := eta) (d := z - xPlus)
        halpha_nonneg hgamma_pos rfl hweighted_absorb hDeltaSquare
  have hrec :
      Psi xBar ≤
        (1 - alpha) * Psi prevBar +
          alpha *
            (f xUnder +
              ⟪grad xUnder, xRef - xUnder⟫_ℝ +
              h xRef +
              mu * V xUnder xRef) +
          alpha / gamma *
            (V prevCenter xRef -
              (1 + mu * gamma) * V z xRef) +
          alpha * gamma * (M + ‖eta‖) ^ 2 /
            (2 * (1 + mu * gamma - L * alpha * gamma)) +
          alpha * ⟪eta, xRef - xPlus⟫_ℝ :=
    accelerated_composite_recurrence_of_two_bregman_descent
      Psi f h V grad alpha gamma mu L M
      prevBar prevCenter xUnder z xPlus xBar xRef g eta
      halpha_nonneg hgamma_pos hnoise_decomp hUpper htwo_bregman
      hsource_alpha_tail
  exact
    sq_norm_endpoint_le_of_accelerated_bregman_recurrence
      Psi f h V grad alpha gamma mu L M
      prevBar prevCenter xUnder z xRef xPlus xBar eta
      halpha_pos hgamma_pos hmu_nonneg hPsi_ref_le_xBar hmodel_le
      hVz_lower hrec

-- Batch 7 promoted from Staging/accelerated_prox_core_step_descent_of_rel.lean
-- Generalization plan (G0):
-- concept/name: accelerated two-center prox descent from weighted bound; orig was
--   `lemma515_relational_core_step_inequality`, renamed away from theorem
--   numbering and paper-specific relational/core-step wording.
-- generality used: arbitrary real Hilbert-space carrier via
--   `[NormedAddCommGroup E] [InnerProductSpace ℝ E]`, with separate abstract
--   types for prox centers and feasible comparison points evaluated into `E`;
--   no measure, filtration, convexity, smoothness, probability, or
--   finite-dimensional hypotheses are used. The smooth objective appears only
--   through the named first-order linear model and the selected gradient
--   vector.
-- portable call pattern: accelerated proximal-gradient, stochastic
--   accelerated gradient, and variance-reduced proximal algorithms can call
--   this after proving a two-center prox descent relation and a Bregman
--   lower-bound absorption for the weighted auxiliary center; the objective,
--   potential, gradient, residual, and comparison point vary while the
--   conclusion stays fixed.
-- counterargument checked: not a paper-local traceability wrapper because it
--   exposes the reusable residual split and insertion of the weighted-center
--   Bregman lower bound between prox optimality and accelerated descent. It is
--   not covered by the downstream endpoint theorems, which additionally assume
--   smooth upper models and completion-square tails.
-- coverage search: searched CATALOG/SOptLib/Staging for `accelerated prox`,
--   `two center Bregman`, `endpoint`, `linear model`, and `residual split`;
--   top hits were `two_bregman_argmin_descent`,
--   `sq_norm_endpoint_le_of_two_center_prox_context`,
--   `accelerated_composite_one_step_recursion`, and
--   `first_order_linear_model_sub`, all partial rather than full.
-- minimal hypotheses: all hypotheses are pointwise one-step inequalities; the
--   center/comparator domains are separated only because accelerated prox
--   libraries often distinguish generated core points from feasible
--   comparison points.

/-- A two-center prox relation and weighted-center lower bound give accelerated
one-step descent.

The prox premise supplies the Bregman descent inequality for the full gradient
plus residual. The weighted-center lower bound inserts the explicit squared
prox displacement, and the residual is split from the first-order linear model.

Layer: Layer1 | Gap: Level 1 (accelerated two-center prox residual split)
Proof: rewrite the same-base first-order model difference as an inner product,
  expand the estimator gradient by inner-product linearity, and combine the
  prox descent premise with the weighted-center lower bound by ordered-ring
  arithmetic.
Source: accelerated proximal-gradient estimate-sequence algebra and Mathlib
  real Hilbert-space inner-product/order arithmetic APIs
Used in: variance-reduced accelerated proximal-gradient one-step
  linearization/Bregman descent before conditional-expectation aggregation
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem accelerated_two_center_prox_descent_of_weighted_bound
    {C Q E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (evalC : C → E) (evalQ : Q → E)
    (f : E → ℝ) (hC : C → ℝ) (hQ : Q → ℝ)
    (VCC : C → C → ℝ) (VCQ : C → Q → ℝ) (grad : C → E)
    (gamma mu : ℝ)
    (x : Q) (xPrev xUnder xNext : C) (xPlus delta : E)
    (hprox :
      gamma *
          (⟪grad xUnder + delta, evalC xNext - evalQ x⟫_ℝ +
            hC xNext - hQ x + mu * VCC xUnder xNext) +
          VCC xPrev xNext ≤
        gamma * mu * VCQ xUnder x + VCQ xPrev x -
          (1 + mu * gamma) * VCQ xNext x)
    (hweighted :
      (1 + mu * gamma) / 2 * ‖evalC xNext - xPlus‖ ^ 2 ≤
        gamma * mu * VCC xUnder xNext + VCC xPrev xNext) :
    gamma *
        (SOptLib.first_order_linear_model f (grad xUnder) (evalC xUnder) (evalC xNext) -
          SOptLib.first_order_linear_model f (grad xUnder) (evalC xUnder) (evalQ x) +
          hC xNext - hQ x) ≤
      gamma * mu * VCQ xUnder x + VCQ xPrev x -
        (1 + mu * gamma) * VCQ xNext x -
        (1 + mu * gamma) / 2 * ‖evalC xNext - xPlus‖ ^ 2 -
        gamma * ⟪delta, evalC xNext - evalQ x⟫_ℝ := by
  have hlin :
      SOptLib.first_order_linear_model f (grad xUnder) (evalC xUnder) (evalC xNext) -
          SOptLib.first_order_linear_model f (grad xUnder) (evalC xUnder) (evalQ x) =
        ⟪grad xUnder, evalC xNext - evalQ x⟫_ℝ :=
    SOptLib.first_order_linear_model_sub f (grad xUnder) (evalC xUnder)
      (evalC xNext) (evalQ x)
  rw [hlin]
  have hprox_split := hprox
  rw [inner_add_left] at hprox_split
  nlinarith [hprox_split, hweighted]

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: two-Bregman descent identity from an affine selected subgradient
--   relation; orig was `candidate_dual_bregman_descent_identity`, renamed away
--   from candidate/update/random-primal-dual-gradient block vocabulary.
-- generality used: arbitrary carrier `Y` evaluated in a real inner-product
--   space `E`, a scalar potential `J`, two selected base vectors, a linear
--   vector `x`, and a weight `τ`; no measure, filtration, convexity,
--   smoothness, oracle, completeness, or finite-dimensional hypotheses are
--   used.
-- portable call pattern: mirror-prox, primal-dual, and accelerated composite
--   prox proofs can reuse this pointwise algebra when a prox optimality or
--   selected-subgradient construction gives an affine relation between the
--   linear vector, the new selected subgradient, and the previous base
--   subgradient; the carrier, potential, evaluation map, vectors, and weights
--   vary while the two-Bregman conclusion is unchanged.
-- counterargument checked: not paper-local traceability because this is the
--   reusable algebra that converts an affine selected-subgradient relation into
--   a two-center Bregman descent display; not a caller-side expression because
--   it packages the simultaneous cancellation of three Bregman formulas and
--   the linear objective term. It is not a duplicate of the existing
--   accelerated recurrence lemmas, which consume a two-Bregman descent
--   inequality rather than prove this selected-subgradient identity.
-- coverage search: checked `docs/knowledge/CATALOG.md`, `SOptLib/Layer1/Proximal.lean`,
--   `SOptLib/Model/Bregman.lean`, staged selected-carrier Bregman files, project
--   tokens for `two_bregman_descent`, `affine selected subgradient`, and
--   LeanSearch queries "Bregman divergence affine subgradient two Bregman
--   descent identity" and "inner product affine relation Bregman descent
--   identity"; hits covered three-point Bregman identities, selected Bregman
--   nonnegativity, accelerated recurrence consumers, and inner-product
--   ingredients, but no theorem derives this two-Bregman descent identity from
--   an affine selected-subgradient relation.
-- minimal hypotheses: the original standing assumptions, positivity of
--   `1 + τ`, explicit quotient construction, subgradient membership, concrete
--   Fenchel-dual carrier, and finite-dimensionality are reduced to the single
--   pointwise affine relation `x = (1 + τ) • q - τ • base`.

/-- An affine selected-subgradient relation gives a two-center Bregman descent
identity.

If the linear vector `x` equals `(1 + τ) q - τ base`, then the linearized
potential gap at `yHat` is exactly the difference of the previous-base and
new-base Bregman formulas.  The theorem is stated as an inequality so it can be
used directly as a descent step.

Layer: Layer1 | Gap: Level 1 (two-center Bregman descent algebra)
Proof: unfold the generic carrier Bregman formula, substitute the affine
  selected-subgradient relation, expand inner-product linearity, and normalize
  the resulting ordered-ring identity.
Source: convex optimization Bregman three-point algebra and Mathlib real
  inner-product normalization APIs
Used in: random primal-dual gradient dual-block prox descent, mirror-prox
  selected-subgradient descent, and accelerated composite prox two-center
  Bregman steps
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem two_bregman_descent_of_affine_selected_subgradient
    {Y E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (J : Y → ℝ) (eval : Y → E) (τ : ℝ) (x q base : E)
    (yPrev yHat y : Y)
    (h_affine : x = (1 + τ) • q - τ • base) :
    ⟪-x, eval yHat - eval y⟫_ℝ + J yHat - J y ≤
      τ * _root_.carrierBregmanFormula J eval (fun _ : Y => base) yPrev y -
        (1 + τ) * _root_.carrierBregmanFormula J eval (fun _ : Y => q) yHat y -
        τ * _root_.carrierBregmanFormula J eval (fun _ : Y => base) yPrev yHat := by
  have hidentity :
      ⟪-x, eval yHat - eval y⟫_ℝ + J yHat - J y =
        τ * _root_.carrierBregmanFormula J eval (fun _ : Y => base) yPrev y -
          (1 + τ) * _root_.carrierBregmanFormula J eval (fun _ : Y => q) yHat y -
          τ * _root_.carrierBregmanFormula J eval (fun _ : Y => base) yPrev yHat := by
    subst x
    simp [_root_.carrierBregmanFormula, inner_sub_right, inner_sub_left,
      inner_smul_left]
    ring
  exact le_of_eq hidentity

-- Generalization plan (G0):
-- concept/name: carrier two-Bregman descent from a selected subgradient prox
--   residual; orig was `primal_two_bregman_descent_of_simple_subgradient`,
--   renamed away from primal and random-primal-dual-gradient vocabulary.
-- generality used: arbitrary feasible carrier subtype of a real inner-product
--   space, simple carrier term `h`, Bregman potential `v`, selected gradient
--   map `grad`, oracle vector `g`, weights `mu eta`, previous center, selected
--   prox point, and comparison point; no measure, filtration, convexity,
--   smoothness, completeness, or finite-dimensional hypotheses are used.
-- portable call pattern: composite mirror-prox, proximal-gradient, randomized
--   block mirror descent, and primal-dual proofs can call this immediately
--   after a selected carrier-subgradient first-order condition; the carrier,
--   simple term, Bregman potential, selected gradient, vector, weights, and
--   centers change while the two-Bregman descent conclusion stays the same.
-- counterargument checked: not paper-local traceability because the statement
--   packages the standard conversion from a selected prox FOC and Bregman
--   three-point algebra to a reusable two-Bregman descent inequality; not a
--   caller-side expression because it combines support, linear-objective
--   orientation, and weighted Bregman cancellation. It differs from the
--   already staged affine selected-subgradient identity, which assumes an
--   affine equality between selected gradients and has no simple-term support
--   hypothesis, and from `two_bregman_argmin_descent`, which starts from a
--   global argmin and segment-derivative API.
-- coverage search: checked `docs/knowledge/CATALOG.md`, full signatures in
--   `SOptLib/Layer1/Proximal.lean` and `SOptLib/Layer0/ConvexFOC.lean`,
--   staged `two_bregman_descent_of_affine_selected_subgradient` and
--   `carrierBregmanProxSelectedSubgradientCertificate`, project tokens
--   `two_bregman`, `selected_subgradient`, `carrierSubdifferential`, and
--   LeanSearch query "selected subgradient Bregman three point descent
--   inequality"; hits covered ingredients or adjacent argmin/affine shapes,
--   but not this selected-subgradient support-to-two-Bregman descent theorem.
-- minimal hypotheses: original standing assumptions, finite-dimensionality,
--   paper setup fields, positivity/solvability facts, and concrete objective
--   definitions are reduced to pointwise `carrierSubdifferential` membership.

/-- A selected carrier-subgradient prox residual implies two-Bregman descent.

If the negative residual assembled from `g`, `mu • grad xStar`, and the
weighted Bregman gradient displacement from `xPrev` supports the simple term
`h` at `xStar`, then the composite linearized gap at `xStar` is bounded by the
standard two-Bregman descent expression.

Layer: Layer1 | Gap: Level 1 (selected-subgradient two-Bregman descent)
Proof: specialize the carrier-subdifferential support inequality to the
  comparison point, unfold the carrier Bregman three-point identity, normalize
  inner-product orientation, and close the weighted scalar inequality by
  ordered-ring arithmetic.
Source: composite mirror-prox first-order optimality and carrier Bregman
  three-point algebra over real inner-product spaces
Used in: random primal-dual gradient primal prox update, composite mirror-prox
  selected-subgradient descent, and proximal-gradient two-Bregman estimates
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/steps/4
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem carrier_two_bregman_descent_of_selected_subgradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (h v : {x : E // x ∈ X} → ℝ)
    (grad : {x : E // x ∈ X} → E)
    (g : E) (xPrev xStar x : {x : E // x ∈ X}) (mu eta : ℝ)
    (hhSub :
      (-(g + mu • grad xStar + eta • (grad xStar - grad xPrev))) ∈
        carrierSubdifferential h xStar) :
    ⟪xStar.1 - x.1, g⟫_ℝ + h xStar + mu * v xStar -
        h x - mu * v x ≤
      eta * carrierBregmanDivergence v grad xPrev x -
        (mu + eta) * carrierBregmanDivergence v grad xStar x -
        eta * carrierBregmanDivergence v grad xPrev xStar := by
  have hsupport := (mem_carrierSubdifferential_iff.mp hhSub) x
  have hthree :
      carrierBregmanDivergence v grad xPrev x =
        carrierBregmanDivergence v grad xPrev xStar +
          ⟪grad xStar - grad xPrev, x.1 - xStar.1⟫_ℝ +
            carrierBregmanDivergence v grad xStar x := by
    exact
      carrierBregmanDivergence_three_point_identity
        (v := v)
        (eval := fun z : {x : E // x ∈ X} => z.1)
        (grad := grad)
        (V := carrierBregmanDivergence v grad)
        (by
          intro a b
          rfl)
        xPrev xStar x
  unfold carrierBregmanDivergence _root_.carrierBregmanDivergence at hthree ⊢
  simp [inner_add_left, inner_smul_left, inner_neg_left, inner_sub_left,
    inner_sub_right] at hsupport hthree ⊢
  have hgStar :
      ⟪xStar.1, g⟫_ℝ = ⟪g, xStar.1⟫_ℝ :=
    (real_inner_comm xStar.1 g).symm
  have hgx :
      ⟪x.1, g⟫_ℝ = ⟪g, x.1⟫_ℝ :=
    (real_inner_comm x.1 g).symm
  nlinarith [hgStar, hgx]

end SOptLib

-- Generalization plan (G0):
-- concept/name: negative inner-product Young absorption by a Bregman lower
--   bound; orig was
--   `proposition56_lagged_inner_adj_young_pointwise_positive_domain`.
-- generality used: arbitrary real inner-product space, abstract directed
--   potential `V`, abstract primal/dual size functionals, and pointwise support
--   and lower-bound hypotheses; no measure, convexity, oracle, filtration, or
--   finite-dimensional assumptions are used by the proof.
-- portable call pattern: mirror-descent, block-coordinate, variance-reduced,
--   and gradient-extrapolation residual proofs where a lagged residual pairing
--   is bounded by a dual/primal support inequality and the prox displacement is
--   absorbed by a Bregman lower bound; the displacement, residual, gauges,
--   Bregman lower bound, and scalar coefficients vary while the squared
--   dual-size conclusion has the same shape.
-- counterargument checked: not merely paper-local traceability because this
--   packages the reusable support-plus-Bregman Young step; not a pure wrapper
--   around Mathlib Young or SOptLib's positive-sign
--   `inner_sub_sub_bregman_le_half_dual_sq`, since this statement handles the
--   negative inner product, arbitrary positive Bregman coefficient, and an
--   externally supplied output coefficient.
-- coverage search: searched CATALOG/SOptLib/Staging for `Young Bregman lower
--   bound negative inner dualNorm squared`, `inner_sub_sub_bregman_le_half`,
--   `young_absorb_inner_of_norm_sq_budget`, and LeanSearch for the scalar
--   product-minus-quadratic Young shape; hits were partial generic Young or
--   ambient-norm lemmas, not this abstract primal-dual/Bregman absorption.
-- minimal hypotheses: all algorithm facts are pointwise hypotheses; `0 ≤ c`,
--   `0 < A`, support, lower bound, and coefficient domination are exactly the
--   facts used.

/-- A negative residual inner product minus a scaled Bregman term is controlled
by a squared dual-size term.

The support inequality controls `-<d,zeta>` by dual size times primal size, and
the Bregman lower bound absorbs the resulting primal-size square through a
one-dimensional Young inequality.

Layer: Layer1 | Gap: Level 0 (negative residual Bregman Young absorption)
Proof: scale the pointwise primal-dual support and Bregman lower-bound
  hypotheses, apply the scalar square completion
  `(A * primalNorm d - c * dualNorm zeta)^2 >= 0`, then enlarge the resulting
  coefficient by the supplied domination hypothesis.
Source: convex optimization mirror-descent algebra and Mathlib real
  inner-product/ordered-field arithmetic APIs
Used in: randomized gradient extrapolation lagged gradient-memory residual
  absorption by the adjacent Bregman prox displacement
Book citation: book/FOML/RandomGradientExtrapolation.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random gradient extrapolation method -/
theorem neg_inner_sub_bregman_young_le_scaled_dualNorm_sq
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (V : E → E → ℝ) (primalNorm dualNorm : E → ℝ)
    (c A coeffOut : ℝ) (x y d zeta : E)
    (hc_nonneg : 0 ≤ c) (hA_pos : 0 < A)
    (hsupport : -⟪d, zeta⟫_ℝ ≤ dualNorm zeta * primalNorm d)
    (hV_lower : (1 / 2 : ℝ) * primalNorm d ^ 2 ≤ V x y)
    (hcoeff : c ^ 2 / (2 * A) ≤ coeffOut) :
    -c * ⟪d, zeta⟫_ℝ - A * V x y ≤
      coeffOut * dualNorm zeta ^ 2 := by
  have hA_nonneg : 0 ≤ A := le_of_lt hA_pos
  have hyoung_base :
      c * (dualNorm zeta * primalNorm d) -
          A * ((1 / 2 : ℝ) * primalNorm d ^ 2) ≤
        (c ^ 2 / (2 * A)) * dualNorm zeta ^ 2 := by
    have hsq : 0 ≤ (A * primalNorm d - c * dualNorm zeta) ^ 2 := sq_nonneg _
    have hA_ne : A ≠ 0 := ne_of_gt hA_pos
    field_simp [hA_ne]
    nlinarith [hsq, hA_pos]
  have hinner_scaled :
      -c * ⟪d, zeta⟫_ℝ ≤ c * (dualNorm zeta * primalNorm d) := by
    nlinarith [mul_le_mul_of_nonneg_left hsupport hc_nonneg]
  have hV_scaled :
      -A * V x y ≤ -A * ((1 / 2 : ℝ) * primalNorm d ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hV_lower hA_nonneg]
  have hcoeff_scaled :
      (c ^ 2 / (2 * A)) * dualNorm zeta ^ 2 ≤
        coeffOut * dualNorm zeta ^ 2 := by
    exact mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)
  calc
    -c * ⟪d, zeta⟫_ℝ - A * V x y
        ≤ c * (dualNorm zeta * primalNorm d) -
            A * ((1 / 2 : ℝ) * primalNorm d ^ 2) := by
          nlinarith [hinner_scaled, hV_scaled]
    _ ≤ (c ^ 2 / (2 * A)) * dualNorm zeta ^ 2 := hyoung_base
    _ ≤ coeffOut * dualNorm zeta ^ 2 := hcoeff_scaled

namespace SOptLib

/-- A mirror step satisfying a variational inequality obeys the one-step
descent bound with a squared dual-gauge penalty.

The statement is carrier-level and mixed-domain: `step` is any selected
mirror/prox update on the base carrier, `V` is any directed Bregman-like
potential from base points to comparison points, and `primalNorm`/`dualNorm`
are any gauge pair for which the displayed support and lower-bound hypotheses
hold.

Layer: Layer1 | Gap: Level 1 (mirror-step one-step descent from variational data)
Proof: first turn the variational inequality and mixed Bregman three-point
  identity into the prox three-point inequality, then split the current-to-
  comparator pairing through the step and absorb the movement term by Young's
  inequality.
Source: SOptLib mirror-descent prox algebra and Mathlib real inner-product
  ordered-field arithmetic
Used in: stochastic convex-concave saddle-point mirror descent when a
  source-DGF product prox update is converted into the pathwise stochastic
  one-step prox inequality with squared dual oracle penalty
Book citation: book/FOML/StochasticConvexConcaveSaddlePoint.json#/key_lemmas/1/proof/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent for stochastic convex-concave
  saddle point problems -/
theorem sourceDGF_mirrorStep_one_step_bound
    {P Q E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (V : P → Q → ℝ) (evalBase : P → E) (evalCompare : Q → E)
    (grad : P → E) (toCompare : P → Q)
    (primalNorm dualNorm : E → ℝ) (step : P → E → ℝ → P)
    (z : P) (x : Q) (g : E) (γ : ℝ)
    (hγ_nonneg : 0 ≤ γ)
    (hvariational :
      0 ≤ ⟪γ • g + grad (step z g γ) - grad z,
        evalCompare x - evalBase (step z g γ)⟫_ℝ)
    (hthree_point :
      V z x =
        V z (toCompare (step z g γ)) +
          ⟪grad (step z g γ) - grad z,
            evalCompare x - evalBase (step z g γ)⟫_ℝ +
          V (step z g γ) x)
    (hsupport :
      ⟪g, evalBase z - evalBase (step z g γ)⟫_ℝ ≤
        dualNorm g * primalNorm (evalBase z - evalBase (step z g γ)))
    (hlower :
      (1 / 2 : ℝ) * primalNorm (evalBase z - evalBase (step z g γ)) ^ 2 ≤
        V z (toCompare (step z g γ))) :
    γ * ⟪g, evalBase z - evalCompare x⟫_ℝ ≤
      V z x - V (step z g γ) x + (1 / 2 : ℝ) * γ ^ 2 * dualNorm g ^ 2 := by
  let y : P := step z g γ
  have hthree :
      γ * ⟪g, evalBase y - evalCompare x⟫_ℝ + V z (toCompare y) ≤
        V z x - V y x := by
    have hinner :
        γ * ⟪g, evalBase y - evalCompare x⟫_ℝ ≤
          ⟪grad y - grad z, evalCompare x - evalBase y⟫_ℝ := by
      have hvar_expanded :
          0 ≤ γ * ⟪g, evalCompare x - evalBase y⟫_ℝ +
            ⟪grad y - grad z, evalCompare x - evalBase y⟫_ℝ := by
        have hdiff :
            ⟪grad y - grad z, evalCompare x - evalBase y⟫_ℝ =
              ⟪grad y, evalCompare x - evalBase y⟫_ℝ -
                ⟪grad z, evalCompare x - evalBase y⟫_ℝ := by
          rw [inner_sub_left]
        calc
          0 ≤ ⟪γ • g + grad y - grad z, evalCompare x - evalBase y⟫_ℝ := by
            simpa [y] using hvariational
          _ = γ * ⟪g, evalCompare x - evalBase y⟫_ℝ +
                ⟪grad y - grad z, evalCompare x - evalBase y⟫_ℝ := by
            rw [hdiff, inner_sub_left, inner_add_left, real_inner_smul_left]
            ring
      have hneg :
          ⟪g, evalBase y - evalCompare x⟫_ℝ =
            -⟪g, evalCompare x - evalBase y⟫_ℝ := by
        have hsub : evalBase y - evalCompare x = -(evalCompare x - evalBase y) := by
          abel
        rw [hsub, inner_neg_right]
      rw [hneg]
      nlinarith
    nlinarith [hinner, hthree_point]
  have hscaled_support :
      γ * ⟪g, evalBase z - evalBase y⟫_ℝ ≤
        γ * (dualNorm g * primalNorm (evalBase z - evalBase y)) := by
    exact mul_le_mul_of_nonneg_left (by simpa [y] using hsupport) hγ_nonneg
  have hyoung :
      γ * (dualNorm g * primalNorm (evalBase z - evalBase y)) -
          (1 / 2 : ℝ) * primalNorm (evalBase z - evalBase y) ^ 2 ≤
        (1 / 2 : ℝ) * γ ^ 2 * dualNorm g ^ 2 := by
    nlinarith [sq_nonneg (γ * dualNorm g - primalNorm (evalBase z - evalBase y))]
  have hscaled_young :
      γ * ⟪g, evalBase z - evalBase y⟫_ℝ - V z (toCompare y) ≤
        (1 / 2 : ℝ) * γ ^ 2 * dualNorm g ^ 2 := by
    have hlower_y :
        (1 / 2 : ℝ) * primalNorm (evalBase z - evalBase y) ^ 2 ≤
          V z (toCompare y) := by
      simpa [y] using hlower
    nlinarith
  have hsplit :
      γ * ⟪g, evalBase z - evalCompare x⟫_ℝ =
        γ * ⟪g, evalBase z - evalBase y⟫_ℝ +
          γ * ⟪g, evalBase y - evalCompare x⟫_ℝ := by
    have hvec :
        evalBase z - evalCompare x =
          (evalBase z - evalBase y) + (evalBase y - evalCompare x) := by
      abel
    rw [hvec, inner_add_right]
    ring
  rw [hsplit]
  nlinarith

end SOptLib
