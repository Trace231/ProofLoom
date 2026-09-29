-- SOptLib/Layer1/Proximal.lean
import SOptLib.Layer0.ConvexFOC
import SOptLib.Model.Bregman
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic
import SOptLib.Glue.Algebra
import SOptLib.Glue.Calculus
import SOptLib.Model.Iterates
import SOptLib.Model.StochasticOracle


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

-- Promoted from Staging/Layer1/prox_bregman_step_bound_of_variational.lean
namespace SOptLib

open scoped Gradient InnerProductSpace

-- Generalization plan (G0):
-- G0.1 naming: prox_bregman_step_bound_of_variational (orig was:
--   blockProx_selected_block_bregman_bound)
-- G0.2 typeclass level used:
--   E: NormedAddCommGroup + InnerProductSpace ℝ; finite-dimensionality is not used
--   measure: none; this is deterministic prox-step algebra
--   convexity: encoded only through the pointwise Bregman lower-bound hypothesis used
-- G0.3 reusability — could instantiate:
--   1. stochastic block mirror descent sampled block prox step
--   2. stochastic mirror descent carrier prox step before expectation/telescoping
-- G0.4 search trace:
--   queries: ["prox bregman variational", "gamma step bregman dual support"]
--   top hits: ["prox_variational_inequality_of_isMinOn_linear_bregman",
--     "prox_three_point_of_isMinOn_linear_bregman",
--     "prox_gamma_step_bound_of_three_point_and_dual_support",
--     "inner_sub_sub_bregman_le_half_dual_sq"]
--   coverage: partial — overlaps but does not subsume
--     prox_gamma_step_bound_of_three_point_and_dual_support, which assumes the
--     three-point inequality and lower/support premises are already assembled
-- G0.4 not-a-thin-wrapper rationale: the theorem converts the scaled prox
--   variational inequality to the unscaled carrier three-point inequality, derives
--   the carrier Bregman identity, applies support/lower Young absorption, and
--   rewrites the comparator inner product direction.
-- G0.5 structural-content rationale: it exposes the reusable prox-step invariant
--   that turns a carrier-Bregman variational inequality into the final one-step
--   descent bound used before stochastic aggregation.
-- G0.5c thin-wrapper self-detect: clean — body has multiple algebraic conversion
--   steps before invoking existing SOptLib lemmas.
-- G0.5d minimal-hypothesis check: all already minimal; support and lower bounds
--   are pointwise hypotheses and no global smoothness, convexity, or measure
--   assumption is retained.

/-- A carrier-Bregman prox variational inequality gives the standard one-step bound.

The scaled variational inequality for the selected prox point is converted to
the unscaled mirror-descent three-point inequality, then pointwise dual support
and Bregman quadratic lower bounds absorb the prox displacement by Young's
inequality.

Layer: Layer1 | Gap: Level 1 (carrier-Bregman prox-step variational descent)
Proof: rescale the variational inequality by the positive stepsize, derive the
  carrier Bregman three-point identity, apply the gamma-scaled prox Young
  absorption lemma, and rewrite the comparator inner-product direction.
Source: Convex optimization mirror-descent prox algebra, carrier Bregman
  three-point identities, and Mathlib real inner-product arithmetic
Used in: stochastic block mirror descent selected-block prox step before
  aggregate Bregman lifting
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem prox_bregman_step_bound_of_variational
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (v : {u : E // u ∈ X} → ℝ)
    (grad : {u : E // u ∈ X} → E)
    (primalNorm : Seminorm ℝ E) (dualNorm : E → ℝ)
    (z y x : {u : E // u ∈ X}) (g : E) (γ : {γ : ℝ // 0 < γ})
    (h_variational :
      0 ≤ ⟪g, x.1 - y.1⟫_ℝ +
        (γ.1)⁻¹ * ⟪grad y - grad z, x.1 - y.1⟫_ℝ)
    (hsupport :
      ∀ ζ d : E, |⟪ζ, d⟫_ℝ| ≤ dualNorm ζ * primalNorm d)
    (hlower :
      ∀ a b : {u : E // u ∈ X},
        (1 / 2 : ℝ) * primalNorm (b.1 - a.1) ^ 2 ≤
          carrierBregmanDivergence v grad a b) :
    carrierBregmanDivergence v grad y x ≤
      carrierBregmanDivergence v grad z x +
        γ.1 * ⟪g, x.1 - z.1⟫_ℝ +
          (1 / 2 : ℝ) * γ.1 ^ 2 * dualNorm g ^ 2 := by
  have hvar :
      0 ≤ ⟪γ.1 • g + grad y - grad z, x.1 - y.1⟫_ℝ := by
    have hscaled :
        0 ≤ γ.1 *
          (⟪g, x.1 - y.1⟫_ℝ +
            (γ.1)⁻¹ * ⟪grad y - grad z, x.1 - y.1⟫_ℝ) :=
      mul_nonneg (le_of_lt γ.2) h_variational
    have hrewrite :
        γ.1 *
          (⟪g, x.1 - y.1⟫_ℝ +
            (γ.1)⁻¹ * ⟪grad y - grad z, x.1 - y.1⟫_ℝ) =
        ⟪γ.1 • g + grad y - grad z, x.1 - y.1⟫_ℝ := by
      simp [inner_add_left, inner_sub_left, inner_smul_left]
      field_simp [γ.2.ne']
      ring
    simpa [hrewrite] using hscaled
  have hthree_identity :
      carrierBregmanDivergence v grad z x =
        carrierBregmanDivergence v grad z y +
          ⟪grad y - grad z, x.1 - y.1⟫_ℝ +
            carrierBregmanDivergence v grad y x := by
    exact
      carrierBregmanDivergence_three_point_identity
        (v := v) (eval := fun u : {u : E // u ∈ X} => u.1) (grad := grad)
        (V := carrierBregmanDivergence v grad) (by intro a b; rfl) z y x
  have hthree :
      γ.1 * ⟪g, y.1 - x.1⟫_ℝ +
          carrierBregmanDivergence v grad z y ≤
        carrierBregmanDivergence v grad z x -
          carrierBregmanDivergence v grad y x := by
    exact
      mirror_descent_three_point_of_variational_carrier
        (V := carrierBregmanDivergence v grad)
        (eval := fun u : {u : E // u ∈ X} => u.1) (grad := grad)
        (x := z) (z := y) (y := x)
        (g := g) (γ := γ.1) hvar hthree_identity
  have hsupport_point :
      ⟪g, z.1 - y.1⟫_ℝ ≤
        dualNorm g * primalNorm (z.1 - y.1) := by
    exact le_trans (le_abs_self _) (hsupport g (z.1 - y.1))
  have hlower_point :
      (1 / 2 : ℝ) * primalNorm (z.1 - y.1) ^ 2 ≤
        carrierBregmanDivergence v grad z y := by
    have hcore := hlower z y
    have hnorm :
        primalNorm (y.1 - z.1) = primalNorm (z.1 - y.1) := by
      have hsub : y.1 - z.1 = -(z.1 - y.1) := by
        abel
      rw [hsub]
      simpa using map_neg_eq_map primalNorm (z.1 - y.1)
    rwa [hnorm] at hcore
  have hstep :=
    prox_gamma_step_bound_of_three_point_and_dual_support
      (V := carrierBregmanDivergence v grad)
      (eval := fun u : {u : E // u ∈ X} => u.1)
      (primalNorm := primalNorm) (dualNorm := dualNorm)
      (z := z) (y := y) (x := x) (g := g) (γ := γ.1)
      (le_of_lt γ.2) hthree hsupport_point hlower_point
  have hinner_neg :
      ⟪g, z.1 - x.1⟫_ℝ = -⟪g, x.1 - z.1⟫_ℝ := by
    have hsub : z.1 - x.1 = -(x.1 - z.1) := by
      abel
    rw [hsub, inner_neg_right]
  rw [hinner_neg] at hstep
  nlinarith

end SOptLib

open scoped Gradient InnerProductSpace

-- Generalization plan (G0):
-- concept/name: two-center Bregman three-point inequality from an `IsMinOn`
--   prox certificate; orig was `lemma_3_5_three_point`.
-- generality used: complete real Hilbert space, carrier set `X`, concrete
--   `SOptLib.DistanceGeneratingFunctionOn E X`, convex term `ConvexOn ℝ X p`,
--   pointwise minimizer membership plus `IsMinOn`; no measure, oracle, or
--   stochastic-process assumptions.
-- portable call pattern: accelerated primal-dual, accelerated mirror descent,
--   and mirror-prox two-anchor prox steps after a local subproblem minimizes a
--   convex term plus two weighted Bregman divergences; centers, weights,
--   comparison point, and convex term vary while the conclusion shape stays.
-- counterargument checked: existing SOptLib has one-center prox three-point
--   lemmas and staging has separate two-center residual and scalar
--   rearrangement lemmas, but no combined `IsMinOn` to final two-center
--   Bregman three-point inequality. This is not paper-local traceability
--   because future algorithms can call it directly at the two-anchor prox step.
-- coverage search: searched catalog/project for `two_center_bregman`,
--   `three_point`, `residual_nonneg`, and `IsMinOn`; read
--   `prox_three_point_of_isMinOn_linear_bregman`,
--   `two_center_bregman_residual_nonneg_of_isMinOn`, and
--   `two_center_residual_nonneg_to_three_point_ineq`; LeanSearch for
--   "Bregman divergence two center prox three point inequality minimizer
--   convex" returned unrelated Mathlib metric/convex-hull facts.
-- minimal hypotheses: dropped center membership and weight nonnegativity from
--   the paper statement because the residual proof and scalar rearrangement use
--   neither; kept `CompleteSpace E` for canonical-gradient DGF calculus.

/-- A two-center Bregman minimizer satisfies the three-point prox inequality.

For a distance-generating function on a carrier, any minimizer of a convex term
plus two weighted Bregman divergences controls the same objective at a feasible
comparison point with the shared endpoint Bregman term subtracted.

Layer: Layer1 | Gap: Level 1 (two-center Bregman prox three-point inequality)
Proof: derive the two-center Bregman residual nonnegativity from the `IsMinOn`
  certificate, then apply the scalar residual-to-three-point rearrangement.
Source: Mathlib convex first-order optimality, SOptLib distance-generating
  Bregman identities, and ordered-ring rearrangement APIs
Used in: accelerated primal-dual and accelerated mirror-descent two-anchor prox
  descent before the Bregman terms are telescoped
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/key_lemmas
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem two_center_bregman_three_point_of_isMinOn
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
    p xHat + mu1 * ν.bregman xHat xTilde + mu2 * ν.bregman xHat yTilde ≤
      p u + mu1 * ν.bregman u xTilde + mu2 * ν.bregman u yTilde -
        (mu1 + mu2) * ν.bregman u xHat := by
  have hres :
      0 ≤ p u - p xHat +
        mu1 * (ν.bregman u xTilde - ν.bregman xHat xTilde - ν.bregman u xHat) +
        mu2 * (ν.bregman u yTilde - ν.bregman xHat yTilde - ν.bregman u xHat) :=
    SOptLib.two_center_bregman_residual_nonneg_of_isMinOn
      (ν := ν) (p := p) (xHat := xHat) (xTilde := xTilde)
      (yTilde := yTilde) (u := u) (mu1 := mu1) (mu2 := mu2)
      hp_convex hxHat hmin hu
  exact
    two_center_residual_nonneg_to_three_point_ineq
      (p u) (p xHat) (ν.bregman u xTilde) (ν.bregman xHat xTilde)
      (ν.bregman u yTilde) (ν.bregman xHat yTilde) (ν.bregman u xHat)
      mu1 mu2 hres

-- Generalization plan (G0):
-- concept/name: generated prox-component variational inequality transport;
--   orig was `generated_dual_prox_variational`, renamed to remove SAPD source
--   notation while retaining the dual/prox variational concept.
-- generality used: arbitrary sample space and recursive state type, with a
--   real Hilbert dual component, an abstract positive-time step map, component
--   projection, prox component map, stepsize schedule, gradient-like map, and
--   convex/simple term value function. No measure, filtration, independence,
--   integrability, compactness, convexity, or finite-dimensional hypotheses are
--   used once the pointwise prox variational inequality is supplied.
-- portable call pattern: stochastic mirror descent, mirror-prox, accelerated
--   primal-dual, and generated-oracle proximal recursions call this after
--   deriving prox optimality for the component step and proving the process
--   successor equals the one-step update; the process, step map, sample stream,
--   prox map, gradient, and simple term vary while the transported conclusion
--   has the same variational shape.
-- counterargument checked: this is close to a rewrite bridge, but it is not
--   paper-local traceability because recursive stochastic algorithms commonly
--   expose prox optimality at the step map while downstream estimates need it
--   at the generated process slice. It is not a duplicate of the DGF prox
--   minimizer lemmas, which prove the pointwise variational inequality before
--   the recursive-process transport performed here.
-- coverage search: searched "generated process prox variational update
--   component" in SOptLib/Staging/catalog and LeanSearch for recursive-process
--   update transport; relevant hits include
--   `dgf_composite_prox_minimizer_variational_inequality`,
--   `selected_dgf_composite_prox_variational_inequality`, and
--   `accelerated_primal_dual_one_step_gap_of_successor_process`. Coverage is
--   partial: existing prox lemmas produce the local inequality and existing
--   process lemmas transport gap recurrences, but no hit transports this
--   component variational inequality through a successor update.
-- minimal hypotheses: global setup fields are reduced to the successor-state
--   equality, the step's prox-component equality, and the already-proved
--   pointwise prox variational inequality.

/-- A generated prox component inherits its pointwise variational inequality.

If a positive-time recursive process slice is definitionally the one-step
update, the step's component is the prox point, and that prox point satisfies
the standard composite variational inequality, then the same inequality holds
with the generated process component in every occurrence.

Layer: Layer1 | Gap: Level 1 (generated prox variational transport)
Proof: rewrite the generated process slice to the one-step update and then
  rewrite the step component to the prox point inside the supplied pointwise
  variational inequality.
Source: Mathlib inner-product algebra and recursive stochastic-optimization
  process successor equations
Used in: generated-oracle accelerated primal-dual dual prox-step variational
  inequality before Bregman three-point descent
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem generated_dual_prox_variational_inequality
    {Ω State Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (process : (ℕ → Ω → Y) → ℕ → Ω → State)
    (step : (t : ℕ) → 1 ≤ t → Y → State → Ω → State)
    (yOf : State → Y)
    (proxY : (t : ℕ) → 1 ≤ t → Y → State → Ω → Y)
    (τ : ℕ → ℝ) (grad : Y → Y) (h : Y → ℝ)
    (sample : ℕ → Ω → Y) (i : ℕ) (hi : 1 ≤ i) (ω : Ω) (u : Y)
    (hstate :
      process sample i ω =
        step i hi (sample i ω) (process sample (i - 1) ω) ω)
    (hstep :
      yOf (step i hi (sample i ω) (process sample (i - 1) ω) ω) =
        proxY i hi (sample i ω) (process sample (i - 1) ω) ω)
    (hprox :
      0 ≤
        ⟪-sample i ω,
          u - proxY i hi (sample i ω) (process sample (i - 1) ω) ω⟫_ℝ +
          (τ i)⁻¹ *
            ⟪grad (proxY i hi (sample i ω) (process sample (i - 1) ω) ω) -
                grad (yOf (process sample (i - 1) ω)),
              u - proxY i hi (sample i ω) (process sample (i - 1) ω) ω⟫_ℝ +
          (h u - h (proxY i hi (sample i ω) (process sample (i - 1) ω) ω))) :
    0 ≤
      ⟪-sample i ω, u - yOf (process sample i ω)⟫_ℝ +
        (τ i)⁻¹ *
          ⟪grad (yOf (process sample i ω)) -
              grad (yOf (process sample (i - 1) ω)),
            u - yOf (process sample i ω)⟫_ℝ +
        (h u - h (yOf (process sample i ω))) := by
  simpa [hstate, hstep] using hprox

-- Generalization plan (G0):
-- concept/name: generated prox-component variational inequality transport;
--   orig was `generated_dual_prox_variational`, renamed to remove SAPD source
--   notation while retaining the dual/prox variational concept.
-- generality used: arbitrary sample space and recursive state type, with a
--   real Hilbert dual component, an abstract positive-time step map, component
--   projection, prox component map, stepsize schedule, gradient-like map, and
--   convex/simple term value function. No measure, filtration, independence,
--   integrability, compactness, convexity, or finite-dimensional hypotheses are
--   used once the pointwise prox variational inequality is supplied.
-- portable call pattern: stochastic mirror descent, mirror-prox, accelerated
--   primal-dual, and generated-oracle proximal recursions call this after
--   deriving prox optimality for the component step and proving the process
--   successor equals the one-step update; the process, step map, sample stream,
--   prox map, gradient, and simple term vary while the transported conclusion
--   has the same variational shape.
-- counterargument checked: this is close to a rewrite bridge, but it is not
--   paper-local traceability because recursive stochastic algorithms commonly
--   expose prox optimality at the step map while downstream estimates need it
--   at the generated process slice. It is not a duplicate of the DGF prox
--   minimizer lemmas, which prove the pointwise variational inequality before
--   the recursive-process transport performed here.
-- coverage search: searched "generated process prox variational update
--   component" in SOptLib/Staging/catalog and LeanSearch for recursive-process
--   update transport; relevant hits include
--   `dgf_composite_prox_minimizer_variational_inequality`,
--   `selected_dgf_composite_prox_variational_inequality`, and
--   `accelerated_primal_dual_one_step_gap_of_successor_process`. Coverage is
--   partial: existing prox lemmas produce the local inequality and existing
--   process lemmas transport gap recurrences, but no hit transports this
--   component variational inequality through a successor update.
-- minimal hypotheses: global setup fields are reduced to the successor-state
--   equality, the step's prox-component equality, and the already-proved
--   pointwise prox variational inequality.

/-- Alias for the generated prox component variational inequality transport. -/
theorem generated_dual_prox_variational
    {Ω State Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (process : (ℕ → Ω → Y) → ℕ → Ω → State)
    (step : (t : ℕ) → 1 ≤ t → Y → State → Ω → State)
    (yOf : State → Y)
    (proxY : (t : ℕ) → 1 ≤ t → Y → State → Ω → Y)
    (τ : ℕ → ℝ) (grad : Y → Y) (h : Y → ℝ)
    (sample : ℕ → Ω → Y) (i : ℕ) (hi : 1 ≤ i) (ω : Ω) (u : Y)
    (hstate :
      process sample i ω =
        step i hi (sample i ω) (process sample (i - 1) ω) ω)
    (hstep :
      yOf (step i hi (sample i ω) (process sample (i - 1) ω) ω) =
        proxY i hi (sample i ω) (process sample (i - 1) ω) ω)
    (hprox :
      0 ≤
        ⟪-sample i ω,
          u - proxY i hi (sample i ω) (process sample (i - 1) ω) ω⟫_ℝ +
          (τ i)⁻¹ *
            ⟪grad (proxY i hi (sample i ω) (process sample (i - 1) ω) ω) -
                grad (yOf (process sample (i - 1) ω)),
              u - proxY i hi (sample i ω) (process sample (i - 1) ω) ω⟫_ℝ +
          (h u - h (proxY i hi (sample i ω) (process sample (i - 1) ω) ω))) :
    0 ≤
      ⟪-sample i ω, u - yOf (process sample i ω)⟫_ℝ +
        (τ i)⁻¹ *
          ⟪grad (yOf (process sample i ω)) -
              grad (yOf (process sample (i - 1) ω)),
            u - yOf (process sample i ω)⟫_ℝ +
        (h u - h (yOf (process sample i ω))) := by
  simpa using
    (generated_dual_prox_variational_inequality
      (process := process) (step := step) (yOf := yOf) (proxY := proxY)
      (τ := τ) (grad := grad) (h := h) (sample := sample) (i := i) (hi := hi)
      (ω := ω) (u := u) hstate hstep hprox)

-- Generalization plan (G0):
-- concept/name: prox-step inner-product descent from a scaled variational
--   inequality and Bregman drop; orig was `generated_primal_prox_bregman_bound`.
-- generality used: arbitrary real Hilbert carrier with a pointwise gradient
--   map, a directed Bregman-like kernel, positive stepsize, the scaled
--   variational inequality, a three-point identity, and a pointwise
--   half-squared-norm lower bound. No measure, filtration, oracle, convexity,
--   or finite-dimensional hypotheses are used by this proof.
-- portable call pattern: mirror descent, proximal-gradient, mirror-prox, and
--   accelerated primal-dual one-step proofs can call this after deriving the
--   prox variational inequality; the sampled direction, centers, comparator,
--   divergence kernel, and stepsize vary while the conclusion shape stays the
--   same.
-- counterargument checked: not paper-local traceability because the theorem
--   removes generated-process fields entirely; not a duplicate of
--   `mirror_descent_three_point_of_variational_carrier`, which gives the
--   unnormalized three-point inequality but does not divide by the stepsize or
--   absorb the prox-center Bregman term by a squared-norm lower bound.
-- coverage search: checked catalog/source hits for `prox scaled variational`,
--   `mirror_descent_three_point_of_variational_carrier`,
--   `prox_gamma_step_bound_of_three_point_and_dual_support`,
--   `inner_sub_sub_bregman_le_half_dual_sq`, and staged
--   `prox_scaled_variational_of_minimizer_with_segment`; coverage is partial,
--   since no hit states this direct scaled-variational-to-Bregman-drop bound.
-- minimal hypotheses: global prox minimizer, convexity, differentiability, and
--   process/state assumptions are reduced to the three pointwise facts consumed
--   by the algebraic proof.

/-- A scaled prox variational inequality controls the direction inner product
by a Bregman drop minus the prox displacement square.

The kernel is oriented as `V target base`, matching carrier Bregman conventions
common in mirror-descent proofs. The proof only needs the local three-point
identity and the lower bound on the prox-center divergence.

Layer: Layer1 | Gap: Level 1 (prox variational Bregman-drop descent)
Proof: apply the abstract carrier three-point lemma to the reversed kernel,
  then use positivity of the stepsize to divide and the Bregman lower bound to
  absorb the center-to-center term.
Source: SOptLib mirror-descent three-point algebra and Mathlib ordered-field
  arithmetic for inner-product spaces
Used in: stochastic mirror, proximal-gradient, mirror-prox, and accelerated
  primal-dual prox-step descent estimates after prox optimality
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem prox_inner_le_bregman_drop_of_scaled_variational
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (V : E → E → ℝ) (grad : E → E)
    (c xPrev xNext target : E) {η : ℝ}
    (hη : 0 < η)
    (h_variational :
      0 ≤ ⟪η • c + grad xNext - grad xPrev, target - xNext⟫_ℝ)
    (h_three_point :
      V target xPrev =
        V xNext xPrev + ⟪grad xNext - grad xPrev, target - xNext⟫_ℝ +
          V target xNext)
    (hlower : (1 / 2 : ℝ) * ‖xNext - xPrev‖ ^ 2 ≤ V xNext xPrev) :
    ⟪c, xNext - target⟫_ℝ ≤
      η⁻¹ * (V target xPrev - V target xNext) -
        (1 / (2 * η)) * ‖xNext - xPrev‖ ^ 2 := by
  have hthree :
      η * ⟪c, xNext - target⟫_ℝ + V xNext xPrev ≤
        V target xPrev - V target xNext := by
    simpa using
      (mirror_descent_three_point_of_variational_carrier
        (V := fun a b => V b a) (eval := fun x : E => x) (grad := grad)
        (x := xPrev) (z := xNext) (y := target) (g := c) (γ := η)
        h_variational (by simpa using h_three_point))
  have hdrop :
      η * ⟪c, xNext - target⟫_ℝ ≤
        V target xPrev - V target xNext -
          (1 / 2 : ℝ) * ‖xNext - xPrev‖ ^ 2 := by
    nlinarith [hthree, hlower]
  have hη_inv_nonneg : 0 ≤ η⁻¹ := le_of_lt (inv_pos.mpr hη)
  have hscale := mul_le_mul_of_nonneg_left hdrop hη_inv_nonneg
  have hcancel : η⁻¹ * η = 1 := by
    field_simp [ne_of_gt hη]
  have hcoef :
      η⁻¹ * ((1 / 2 : ℝ) * ‖xNext - xPrev‖ ^ 2) =
        (1 / (2 * η)) * ‖xNext - xPrev‖ ^ 2 := by
    field_simp [ne_of_gt hη]
  have hleft :
      η⁻¹ * (η * ⟪c, xNext - target⟫_ℝ) =
        ⟪c, xNext - target⟫_ℝ := by
    rw [← mul_assoc, hcancel, one_mul]
  have hright :
      η⁻¹ * (V target xPrev - V target xNext -
          (1 / 2 : ℝ) * ‖xNext - xPrev‖ ^ 2) =
        η⁻¹ * (V target xPrev - V target xNext) -
          (1 / (2 * η)) * ‖xNext - xPrev‖ ^ 2 := by
    rw [mul_sub, hcoef]
  calc
    ⟪c, xNext - target⟫_ℝ =
        η⁻¹ * (η * ⟪c, xNext - target⟫_ℝ) := hleft.symm
    _ ≤ η⁻¹ * (V target xPrev - V target xNext -
          (1 / 2 : ℝ) * ‖xNext - xPrev‖ ^ 2) := hscale
    _ =
        η⁻¹ * (V target xPrev - V target xNext) -
          (1 / (2 * η)) * ‖xNext - xPrev‖ ^ 2 := hright

-- Generalization plan (G0):
-- concept/name: composite prox variational inequality converted to an
--   inner-product plus simple-term Bregman drop; orig was
--   `generated_dual_prox_bregman_bound`, renamed away from generated-process
--   and paper-local dual-query notation while retaining the composite prox
--   descent concept.
-- generality used: arbitrary real Hilbert carrier, an arbitrary directed
--   Bregman-like kernel `V`, gradient-like map, simple term `g`, sample
--   direction, previous/next/target points, positive stepsize, and the three
--   pointwise algebraic facts consumed by the proof. No measure, filtration,
--   independence, integrability, convexity, or finite-dimensional hypotheses
--   are used after prox optimality is available.
-- portable call pattern: composite mirror descent, proximal-gradient,
--   mirror-prox, and accelerated primal-dual one-step proofs call this after
--   deriving a prox variational inequality with a nonsmooth/simple term; the
--   sample direction, centers, comparator, Bregman kernel, and simple term
--   change while the conclusion shape stays fixed.
-- counterargument checked: not paper-local traceability because all generated
--   process/setup fields are removed; not a duplicate of
--   `prox_inner_le_bregman_drop_of_scaled_variational`, which covers the
--   smooth/linear prox case without the extra simple-term drop `g yNext -
--   g yTarget`; not covered by the SOptLib three-point lemmas, which stop
--   before the positive-stepsize rescaling and lower-bound absorption.
-- coverage search: searched catalog/source for `prox variational bregman`,
--   `composite prox`, `mirror_descent_three_point_of_variational_carrier`,
--   `prox_inner_le_bregman_drop_of_scaled_variational`, and LeanSearch query
--   "Bregman divergence prox variational inequality inner product bound";
--   coverage is partial, with no existing declaration stating this composite
--   simple-term Bregman-drop estimate.
-- minimal hypotheses: prox minimizer, convexity, differentiability, and
--   recursive stochastic-process assumptions are reduced to the pointwise
--   variational inequality, the local three-point identity, and the Bregman
--   half-squared-distance lower bound.

/-- A composite scaled prox variational inequality controls the sample inner
product plus simple-term drop by a Bregman drop minus the prox displacement
square.

The theorem is the nonsmooth/simple-term counterpart of the usual prox
Bregman-drop estimate. It is pointwise: convexity and minimizer assumptions are
only needed upstream to produce the supplied variational inequality.

Layer: Layer1 | Gap: Level 1 (composite prox variational Bregman-drop descent)
Proof: isolate the sample inner product and simple-term drop from the
  variational inequality, substitute the Bregman three-point identity, and use
  positive stepsize scaling plus the lower bound on the prox-center divergence.
Source: SOptLib mirror-descent prox algebra and Mathlib ordered-field
  arithmetic for real inner-product spaces
Used in: composite mirror, proximal-gradient, mirror-prox, and accelerated
  primal-dual prox-step descent estimates after prox optimality
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem dual_prox_g_inner_le_bregman_drop_of_variational
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (V : Y → Y → ℝ) (grad : Y → Y) (g : Y → ℝ)
    (sample yPrev yNext yTarget : Y) {τ : ℝ}
    (hτ : 0 < τ)
    (h_variational :
      0 ≤
        ⟪-sample, yTarget - yNext⟫_ℝ +
          τ⁻¹ * ⟪grad yNext - grad yPrev, yTarget - yNext⟫_ℝ +
          (g yTarget - g yNext))
    (h_three_point :
      ⟪grad yNext - grad yPrev, yTarget - yNext⟫_ℝ =
        V yTarget yPrev - V yNext yPrev - V yTarget yNext)
    (hlower : (1 / 2 : ℝ) * ‖yNext - yPrev‖ ^ 2 ≤ V yNext yPrev) :
    ⟪-sample, yNext - yTarget⟫_ℝ + (g yNext - g yTarget) ≤
      τ⁻¹ * (V yTarget yPrev - V yTarget yNext) -
        (1 / (2 * τ)) * ‖yNext - yPrev‖ ^ 2 := by
  have hτ_inv_nonneg : 0 ≤ τ⁻¹ := le_of_lt (inv_pos.mpr hτ)
  have hsamp_dir :
      ⟪-sample, yTarget - yNext⟫_ℝ =
        -⟪-sample, yNext - yTarget⟫_ℝ := by
    have hdir : yTarget - yNext = -(yNext - yTarget) := by
      abel
    rw [hdir, inner_neg_right]
  have hprox :
      ⟪-sample, yNext - yTarget⟫_ℝ + (g yNext - g yTarget) ≤
        τ⁻¹ * ⟪grad yNext - grad yPrev, yTarget - yNext⟫_ℝ := by
    nlinarith [h_variational, hsamp_dir]
  have hscaled_lbound :
      τ⁻¹ * ⟪grad yNext - grad yPrev, yTarget - yNext⟫_ℝ ≤
        τ⁻¹ * (V yTarget yPrev - V yTarget yNext) -
          (1 / (2 * τ)) * ‖yNext - yPrev‖ ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hlower hτ_inv_nonneg
    rw [h_three_point]
    have hcoef :
        τ⁻¹ * ((1 / 2 : ℝ) * ‖yNext - yPrev‖ ^ 2) =
          (1 / (2 * τ)) * ‖yNext - yPrev‖ ^ 2 := by
      field_simp [ne_of_gt hτ]
    nlinarith
  exact le_trans hprox hscaled_lbound

-- Generalization plan (G0):
-- concept/name: gamma-scaled primal prox Bregman-drop coefficient form; orig
--   was `generated_primal_prox_gamma_bregman_bound`, renamed away from
--   generated-process and paper-local notation while retaining the
--   mathematical coefficient-normalization step for a primal prox estimate.
-- generality used: arbitrary real Hilbert carrier, arbitrary directed
--   Bregman-like kernel `V`, direction vector, previous/next/comparator
--   points, and real scalars `gamma` and `eta`. No measure, filtration,
--   independence, integrability, convexity, or finite-dimensional hypotheses
--   are used once the unscaled prox Bregman-drop bound is available.
-- portable call pattern: stochastic mirror descent, proximal-gradient,
--   mirror-prox, and accelerated primal-dual one-step recurrences call this
--   after proving an unscaled primal prox bound; the sample direction,
--   comparator, Bregman kernel, and schedules change while the coefficient-form
--   conclusion remains the same.
-- counterargument checked: this is a short scalar wrapper, but it is not merely
--   paper traceability because the coefficient-normalized prox bound recurs at
--   recurrence-assembly boundaries; it is not a duplicate of
--   `prox_inner_le_bregman_drop_of_scaled_variational`, which proves the
--   unscaled bound from variational facts rather than the gamma-weighted
--   coefficient form consumed by summed algorithm recurrences.
-- coverage search: searched SOptLib/Staging/catalog for `gamma_mul`,
--   `primal prox bregman`, `scaled bregman`, `scalar prox`, and the full
--   declaration shape; existing coverage includes the dual/composite sibling
--   `gamma_mul_dual_prox_bregman_bound` and the unscaled primal theorem
--   `prox_inner_le_bregman_drop_of_scaled_variational`, but no hit states this
--   primal single-inner-product coefficient normalization. Coverage is partial.
-- minimal hypotheses: global prox optimality, convexity, differentiability,
--   process, and positivity assumptions are reduced to the unscaled bound and
--   nonnegativity of the gamma multiplier; `eta` need not be positive for this
--   algebraic rescaling step.

/-- Multiplying a primal prox Bregman-drop bound by a nonnegative stepsize gives
the coefficient form used in one-step recurrences.

This lemma starts from the unscaled primal prox estimate and rewrites the result
with `gamma / eta` and `gamma / (2 * eta)` coefficients, matching the form
usually summed in mirror and primal-dual descent proofs.

Layer: Layer1 | Gap: Level 1 (gamma-scaled primal prox Bregman-drop coefficient form)
Proof: multiply the supplied unscaled prox bound by the nonnegative `gamma`,
  then normalize the real coefficients by rewriting division as multiplication
  by inverses.
Source: Mathlib ordered-field arithmetic and SOptLib primal prox
  Bregman-drop algebra
Used in: stochastic mirror, proximal-gradient, mirror-prox, and accelerated
  primal-dual one-step recurrence assembly after primal prox descent
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem gamma_mul_primal_prox_bregman_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (V : E → E → ℝ) (c xPrev xNext target : E) {gamma eta : ℝ}
    (hgamma_nonneg : 0 ≤ gamma)
    (hprox :
      ⟪c, xNext - target⟫_ℝ ≤
        eta⁻¹ * (V target xPrev - V target xNext) -
          (1 / (2 * eta)) * ‖xNext - xPrev‖ ^ 2) :
    gamma * ⟪c, xNext - target⟫_ℝ ≤
      gamma / eta * (V target xPrev - V target xNext) -
        gamma / (2 * eta) * ‖xNext - xPrev‖ ^ 2 := by
  have hmul := mul_le_mul_of_nonneg_left hprox hgamma_nonneg
  simpa [mul_sub, mul_assoc, div_eq_mul_inv] using hmul

-- Generalization plan (G0):
-- concept/name: gamma-scaled dual/composite prox Bregman-drop coefficient
--   form; orig was `generated_dual_prox_gamma_bregman_bound`, renamed away
--   from generated-process and paper-local notation while retaining the
--   mathematical coefficient-normalization step for a dual prox estimate.
-- generality used: arbitrary real Hilbert carrier, arbitrary directed
--   Bregman-like kernel `V`, simple term `g`, sample direction, previous/next/
--   comparator points, and real scalars `gamma` and `tau`. No measure,
--   filtration, independence, integrability, convexity, or finite-dimensional
--   hypotheses are used once the unscaled prox Bregman-drop bound is available.
-- portable call pattern: stochastic mirror descent, composite
--   proximal-gradient, mirror-prox, and accelerated primal-dual one-step
--   recurrences call this after proving an unscaled composite prox bound; the
--   sample direction, comparator, Bregman kernel, simple term, and schedules
--   change while the coefficient-form conclusion remains the same.
-- counterargument checked: this is a short scalar wrapper, but it is not merely
--   paper traceability because the coefficient-normalized prox bound recurs at
--   recurrence-assembly boundaries; it is not a duplicate of
--   `composite_prox_inner_add_simple_le_bregman_drop_of_variational`, which
--   proves the unscaled bound from variational facts rather than the gamma-
--   weighted coefficient form consumed by summed algorithm recurrences.
-- coverage search: searched SOptLib/Staging/catalog for `gamma_mul`,
--   `scaled bregman`, `scalar prox`, `mul_le_mul_of_nonneg_left`, and
--   `weighted_mirror_descent_step_bound_of_scaled_gradient`; LeanSearch for
--   "multiply both sides of inequality by nonnegative scalar and rewrite
--   division" returned generic Mathlib order/division lemmas, not this
--   prox-shaped coefficient normalization. Existing coverage is partial.
-- minimal hypotheses: global prox optimality, convexity, differentiability,
--   process, and positivity assumptions are reduced to the unscaled bound and
--   nonnegativity of the gamma multiplier; `tau` need not be positive for this
--   algebraic rescaling step.

/-- Multiplying a dual composite prox Bregman-drop bound by a nonnegative
stepsize gives the coefficient form used in one-step recurrences.

This lemma starts from the unscaled dual/composite prox estimate and rewrites
the result with `gamma / tau` and `gamma / (2 * tau)` coefficients, matching the
form usually summed in mirror and primal-dual descent proofs.

Layer: Layer1 | Gap: Level 1 (gamma-scaled dual prox Bregman-drop coefficient form)
Proof: multiply the supplied unscaled prox bound by the nonnegative `gamma`,
  then normalize the real coefficients by rewriting division as multiplication
  by inverses.
Source: Mathlib ordered-field arithmetic and SOptLib composite prox
  Bregman-drop algebra
Used in: composite mirror, proximal-gradient, mirror-prox, and accelerated
  primal-dual one-step recurrence assembly after dual prox descent
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem gamma_mul_dual_prox_bregman_bound
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (V : Y → Y → ℝ) (g : Y → ℝ)
    (sample yPrev yNext yTarget : Y) {gamma tau : ℝ}
    (hgamma_nonneg : 0 ≤ gamma)
    (hprox :
      ⟪-sample, yNext - yTarget⟫_ℝ + (g yNext - g yTarget) ≤
        tau⁻¹ * (V yTarget yPrev - V yTarget yNext) -
          (1 / (2 * tau)) * ‖yNext - yPrev‖ ^ 2) :
    gamma * (⟪-sample, yNext - yTarget⟫_ℝ + (g yNext - g yTarget)) ≤
      gamma / tau * (V yTarget yPrev - V yTarget yNext) -
        gamma / (2 * tau) * ‖yNext - yPrev‖ ^ 2 := by
  have hmul := mul_le_mul_of_nonneg_left hprox hgamma_nonneg
  simpa [mul_sub, mul_assoc, div_eq_mul_inv] using hmul

-- Generalization plan (G0):
-- concept/name: weighted mirror-descent step bound from a scaled gradient
--   estimate; orig was the `hweightedX`/`hweightedY` local block inside
--   `lemma_4_10_auxiliary_prox_noise_bound`.
-- generality used: an arbitrary real Hilbert space, a directed Bregman-like
--   potential `V`, a pointwise unscaled mirror-descent step inequality for
--   `(-step i) • d i`, and positive step/weight scalars. No measure,
--   filtration, convexity, oracle, or finite-dimensional hypotheses are used.
-- portable call pattern: stochastic mirror descent, mirror-prox, block
--   mirror descent, and accelerated primal-dual proofs call this after a
--   prox three-point/Young step; the potential, iterate sequence, direction,
--   comparator, and schedules vary while the weighted conclusion is unchanged.
-- counterargument checked: this is not paper-local traceability because it
--   removes all SAPD setup fields and only states the scalar rescaling needed
--   after a standard mirror-descent one-step bound. It is not a duplicate of
--   `prox_inner_le_bregman_drop_of_scaled_variational`, which derives the
--   unweighted prox drop from a variational inequality rather than rescaling an
--   already-proved finite-window step bound.
-- coverage search: searched project/SOptLib for `weighted mirror descent step
--   bound scaled gradient Bregman`, `prox scaled variational`, and existing
--   `mirror_descent_sum_bound_of_three_point_and_young`; LeanSearch for the
--   semantic query returned unrelated Mathlib hits. Existing entries provide
--   prox and summation components but not this reusable schedule-rescaling
--   lemma.
-- minimal hypotheses: the theorem assumes only `0 < step i`, `0 < gamma i`,
--   and the one-step inequality being rescaled; global process, product-space,
--   convexity, and minimizer assumptions stay at the caller that proves that
--   one-step inequality.

/-- Rescale a mirror-descent one-step bound for a scaled negative direction.

If the one-step estimate is stated for the direction `(-step i) • d i`, then
multiplying it by `gamma i / step i` gives the usual `gamma i`-weighted
inner-product bound and the square penalty `step i * gamma i / 2 * ‖d i‖²`.

Layer: Layer1 | Gap: Level 1 (weighted mirror-descent step rescaling)
Proof: multiply the supplied one-step inequality by the nonnegative ratio
  `gamma i / step i`, rewrite the scaled inner product and scaled norm using
  positivity of `step i`, and simplify the real coefficients.
Source: Mathlib real inner-product scalar algebra and norm homogeneity used in
  mirror-descent Bregman one-step estimates
Used in: stochastic mirror descent, block mirror descent, mirror-prox, and
  accelerated primal-dual prox-step noise bounds after one-step Bregman descent
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/key_lemmas/4
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem weighted_mirror_descent_step_bound_of_scaled_gradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (V : E → E → ℝ) (d v : ℕ → E) (target : E)
    (step gamma : ℕ → ℝ) (i : ℕ)
    (hstep_pos : 0 < step i)
    (hgamma_pos : 0 < gamma i)
    (hstep_bound :
      ⟪(-step i) • d i, v i - target⟫_ℝ ≤
        V target (v i) - V target (v (i + 1)) +
          ‖(-step i) • d i‖ ^ 2 / 2) :
    gamma i * ⟪-d i, v i - target⟫_ℝ ≤
      gamma i / step i * (V target (v i) - V target (v (i + 1))) +
        step i * gamma i / 2 * ‖d i‖ ^ 2 := by
  have hnonneg : 0 ≤ gamma i / step i :=
    div_nonneg (le_of_lt hgamma_pos) (le_of_lt hstep_pos)
  have hscale := mul_le_mul_of_nonneg_left hstep_bound hnonneg
  have hleft :
      gamma i / step i *
          ⟪(-step i) • d i, v i - target⟫_ℝ =
        gamma i * ⟪-d i, v i - target⟫_ℝ := by
    rw [real_inner_smul_left, inner_neg_left]
    field_simp [ne_of_gt hstep_pos]
  have hnorm :
      ‖(-step i) • d i‖ = step i * ‖d i‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    have habs : |(-step i : ℝ)| = step i := by
      rw [abs_neg]
      exact abs_of_pos hstep_pos
    rw [habs]
  have hright :
      gamma i / step i *
          (V target (v i) - V target (v (i + 1)) +
            ‖(-step i) • d i‖ ^ 2 / 2) =
        gamma i / step i * (V target (v i) - V target (v (i + 1))) +
          step i * gamma i / 2 * ‖d i‖ ^ 2 := by
    rw [mul_add, hnorm]
    field_simp [ne_of_gt hstep_pos]
  rw [hleft] at hscale
  rw [hright] at hscale
  exact hscale

/-- A linear-Bregman mirror-descent sequence satisfies the standard finite
summation bound.

This specializes the abstract summed three-point-plus-Young recursion to a
distance-generating Bregman kernel and prox minimizers of
`u ↦ ⟪ζ_t,u⟫ + D(v_t,u)`.

Layer: Layer1 | Gap: Level 1 (linear Bregman mirror-descent summation)
Proof: derive each three-point inequality from the prox `IsMinOn` certificate,
  absorb the movement term by the DGF lower bound and Young's inequality, then
  invoke the abstract finite-window mirror-descent summation theorem.
Source: SOptLib Bregman prox three-point API, Mathlib finite interval sums, and
  real inner-product Young inequality
Used in: two-block stochastic mirror-prox auxiliary noise summation before
  weighted Bregman boundary aggregation
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/key_lemmas/4
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem mirror_descent_summation_of_linear_bregman_minimizers
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {X : Set E} (ν : SOptLib.DistanceGeneratingFunctionOn E X)
    (ζ v : ℕ → E) (j : ℕ) (x : E)
    (hX_convex : Convex ℝ X)
    (hx : x ∈ X)
    (hv₁ : v 1 ∈ X)
    (hstep_min :
      ∀ t, t ∈ Finset.Icc 1 j →
        v (t + 1) ∈ X ∧
          IsMinOn (fun u => ⟪ζ t, u⟫_ℝ + ν.bregman u (v t)) X (v (t + 1))) :
    (∀ t, t ∈ Finset.Icc 1 j →
        ⟪ζ t, v t - x⟫_ℝ ≤
          ν.bregman x (v t) - ν.bregman x (v (t + 1)) + (‖ζ t‖ ^ 2) / 2) ∧
      Finset.sum (Finset.Icc 1 j) (fun t => ⟪ζ t, v t - x⟫_ℝ) ≤
        ν.bregman x (v 1) + (1 / 2 : ℝ) *
          Finset.sum (Finset.Icc 1 j) (fun t => ‖ζ t‖ ^ 2) := by
  have hmem : ∀ i, 1 ≤ i → i ≤ j + 1 → v i ∈ X := by
    intro i hi hile
    rcases i with _ | k
    · omega
    cases k with
    | zero =>
        simpa using hv₁
    | succ k =>
        have ht : k + 1 ∈ Finset.Icc 1 j := by
          simp [Finset.mem_Icc]
          omega
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using (hstep_min (k + 1) ht).1
  let ζs : ℕ → E := fun t => ζ (t + 1)
  let P := {u : E // u ∈ X}
  let vs : ℕ → P := fun t =>
    if ht : t ≤ j then
      ⟨v (t + 1), hmem (t + 1) (by omega) (by omega)⟩
    else
      ⟨v 1, hv₁⟩
  let V : P → P → ℝ := fun a b => ν.bregman b.1 a.1
  have hthree :
      ∀ t y, t < j →
        ⟪ζs t, (vs (t + 1)).1 - y.1⟫_ℝ + V (vs t) (vs (t + 1)) ≤
          V (vs t) y - V (vs (t + 1)) y := by
    intro t y ht
    have hkI : t + 1 ∈ Finset.Icc 1 j := by
      simp [Finset.mem_Icc]
      omega
    have hstep := hstep_min (t + 1) hkI
    have hp_convex : ConvexOn ℝ X (fun u => ⟪ζ (t + 1), u⟫_ℝ) := by
      refine ⟨hX_convex, ?_⟩
      intro a ha b hb α β hα hβ hab
      change ⟪ζ (t + 1), α • a + β • b⟫_ℝ ≤
        α * ⟪ζ (t + 1), a⟫_ℝ + β * ⟪ζ (t + 1), b⟫_ℝ
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    have hArg :
        v ((t + 1) + 1) ∈ X ∧
          IsMinOn
            (fun u => ⟪ζ (t + 1), u⟫_ℝ +
              (1 : ℝ) * ν.bregman u (v (t + 1)) +
              (0 : ℝ) * ν.bregman u (v (t + 1))) X (v ((t + 1) + 1)) := by
      refine ⟨by simpa [Nat.add_assoc] using hstep.1, ?_⟩
      simpa only [Nat.add_assoc, one_mul, zero_mul, add_zero] using hstep.2
    have h35 := two_center_bregman_three_point_of_isMinOn ν
      (p := fun u => ⟪ζ (t + 1), u⟫_ℝ)
      (xHat := v ((t + 1) + 1)) (xTilde := v (t + 1))
      (yTilde := v (t + 1)) (u := y.1) (mu1 := (1 : ℝ)) (mu2 := (0 : ℝ))
      hp_convex hArg.1 hArg.2 y.2
    have ht_le : t ≤ j := le_of_lt ht
    have htp1_le : t + 1 ≤ j := Nat.succ_le_of_lt ht
    simp only [ζs, vs, V, ht_le, htp1_le, ↓reduceDIte, Subtype.coe_mk]
    rw [inner_sub_right]
    nlinarith [h35]
  have hyoung :
      ∀ t, t < j →
        ⟪ζs t, (vs t).1 - (vs (t + 1)).1⟫_ℝ - V (vs t) (vs (t + 1)) ≤
          (1 / 2 : ℝ) * ‖ζs t‖ ^ 2 := by
    intro t ht
    have hsupport :
        ⟪ζs t, (vs t).1 - (vs (t + 1)).1⟫_ℝ ≤
          ‖ζs t‖ * ‖(vs t).1 - (vs (t + 1)).1‖ := by
      exact real_inner_le_norm (ζs t) ((vs t).1 - (vs (t + 1)).1)
    have hlower :
        (1 / 2 : ℝ) * ‖(vs t).1 - (vs (t + 1)).1‖ ^ 2 ≤ V (vs t) (vs (t + 1)) := by
      have hlb :=
        bregman_lower_bound_of_strongConvexOn_hasGradientAt
          (X := X) (v := ν.potential)
          (grad := fun y => gradient ν.potential y) (m := (1 : ℝ))
          (a := (vs t).1) (b := (vs (t + 1)).1)
          ν.stronglyConvex_modulus_one
          (ν.gradient_at (vs t).1 (vs t).2) (vs t).2 (vs (t + 1)).2
      simpa [V, SOptLib.DistanceGeneratingFunctionOn.bregman_def] using hlb
    exact inner_sub_sub_bregman_le_half_dual_sq
      (eval := fun p : P => p.1) (V := V) (primalNorm := fun u : E => ‖u‖)
      (dualNorm := fun u : E => ‖u‖) (ζs t) (vs t) (vs (t + 1)) hsupport hlower
  have hterminal : ∀ y : P, 0 ≤ V (vs j) y := by
    intro y
    have hlb :=
      bregman_lower_bound_of_strongConvexOn_hasGradientAt
        (X := X) (v := ν.potential)
        (grad := fun y => gradient ν.potential y) (m := (1 : ℝ))
        (a := (vs j).1) (b := y.1)
        ν.stronglyConvex_modulus_one
        (ν.gradient_at (vs j).1 (vs j).2) (vs j).2 y.2
    have hsq : 0 ≤ (1 / 2 : ℝ) * ‖y.1 - (vs j).1‖ ^ 2 := by
      nlinarith [sq_nonneg ‖y.1 - (vs j).1‖]
    have hlower : (1 / 2 : ℝ) * ‖y.1 - (vs j).1‖ ^ 2 ≤ V (vs j) y := by
      simpa [V, SOptLib.DistanceGeneratingFunctionOn.bregman_def, norm_sub_rev] using hlb
    exact le_trans hsq hlower
  have hmd := mirror_descent_sum_bound_of_three_point_and_young
    (V := V) (eval := fun p : P => p.1) (dualNorm := fun u : E => ‖u‖)
    ζs vs j hthree hyoung hterminal
  have hshift_sum (F : ℕ → ℝ) :
      (Finset.sum (Finset.range j) (fun t => F (t + 1))) =
        Finset.sum (Finset.Icc 1 j) F := by
    exact Finset.sum_range_succ_eq_sum_Icc_one F j
  constructor
  · intro t ht
    rcases Finset.mem_Icc.mp ht with ⟨ht1, htj⟩
    have hslt : t - 1 < j := by omega
    have h := hmd.1 (t - 1) ⟨x, hx⟩ hslt
    have h' :
        ⟪ζ t, v t - x⟫_ℝ ≤
          ν.bregman x (v t) - ν.bregman x (v (t + 1)) +
            (1 / 2 : ℝ) * ‖ζ t‖ ^ 2 := by
      have htm1_le : t - 1 ≤ j := by omega
      simpa [ζs, vs, V, htm1_le, htj, Nat.sub_add_cancel ht1] using h
    nlinarith
  · have h := hmd.2 ⟨x, hx⟩
    have hsum_inner_shift :
        Finset.sum (Finset.range j)
            (fun t => ⟪ζs t, (fun p : P => p.1) (vs t) - (fun p : P => p.1) ⟨x, hx⟩⟫_ℝ) =
          Finset.sum (Finset.range j) (fun t => ⟪ζ (t + 1), v (t + 1) - x⟫_ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      have ht_le : t ≤ j := le_of_lt (Finset.mem_range.mp ht)
      simp [ζs, vs, ht_le]
    have hV0 : V (vs 0) ⟨x, hx⟩ = ν.bregman x (v 1) := by
      simp [V, vs]
    have hnorm_shift :
        Finset.sum (Finset.range j) (fun t => (fun u : E => ‖u‖) (ζs t) ^ 2) =
          Finset.sum (Finset.range j) (fun t => ‖ζ (t + 1)‖ ^ 2) := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      simp [ζs]
    have hleft := hshift_sum (fun t => ⟪ζ t, v t - x⟫_ℝ)
    have hright := hshift_sum (fun t => ‖ζ t‖ ^ 2)
    rw [hsum_inner_shift, hV0, hnorm_shift] at h
    rw [hleft, hright] at h
    exact h

-- Generalization plan (G0):
-- concept/name: two-block auxiliary prox noise bound; orig was
--   `lemma_4_10_auxiliary_prox_noise_bound`.
-- generality used: two complete real Hilbert spaces, carrier sets `X` and `Y`,
--   concrete `SOptLib.DistanceGeneratingFunctionOn` Bregman kernels, positive
--   scalar schedules on the finite window, an arbitrary noise sequence, and a
--   product `IsMinOn` prox certificate; no measure, filtration, oracle
--   independence, or finite-dimensional assumptions are used.
-- portable call pattern: stochastic accelerated primal-dual, mirror-prox, and
--   two-block stochastic mirror-descent proofs that introduce an auxiliary
--   prox sequence driven by noise; the spaces, carriers, schedules, noise
--   stream, and Bregman generators vary while the weighted boundary plus
--   squared-noise conclusion stays fixed.
-- counterargument checked: the paper theorem names Lan's `z_i^v`, but after
--   removing setup fields the remaining statement is a deterministic two-block
--   mirror-prox summation theorem, not paper-local traceability or a one-line
--   wrapper. Existing SOptLib has the one-block summed recursion and staged
--   product-coordinate projection/boundary definitions, but not this combined
--   product-prox-to-two-block weighted noise bound.
-- coverage search: queried project/SOptLib for `prox noise bound auxiliary
--   bregman inner product squared norm`, `mirror descent summation bregman prox
--   IsMinOn`, and `product IsMinOn coordinate minimizer`; relevant hits were
--   `mirror_descent_sum_bound_of_three_point_and_young`,
--   `product_isMinOn_coordinate_isMinOn`, and
--   `twoBlockWeightedBregmanBoundaryFor`, which are components rather than the
--   full two-block statement.
-- minimal hypotheses: the initial sequence equality and named start point are
--   dropped because feasibility of `zv 1` follows from its subtype; positivity
--   is only required on the summation support.

/-- A two-block product prox sequence controls weighted noise by a Bregman
boundary plus squared-noise penalties.

The statement is deterministic and pathwise: a product-space prox minimizer for
each positive-time index is projected to the two coordinate mirror-descent
subproblems, then the two weighted one-block bounds are added.

Layer: Layer1 | Gap: Level 1 (two-block auxiliary prox noise bound)
Proof: project the additive product `IsMinOn` certificate to coordinate
  minimizers, apply the linear-Bregman mirror-descent summation bound to each
  block, rescale by positive schedules, and fold the result into the two-block
  weighted Bregman boundary.
Source: SOptLib product minimizer projection, Bregman mirror-descent summation,
  and Mathlib real inner-product/finite-sum algebra
Used in: stochastic accelerated primal-dual auxiliary prox-process noise
  estimate before high-probability saddle-gap aggregation
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/key_lemmas/4
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem auxiliary_prox_noise_bound
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {X : Set E} {Y : Set F}
    (νX : SOptLib.DistanceGeneratingFunctionOn E X)
    (νY : SOptLib.DistanceGeneratingFunctionOn F Y)
    (eta tau gamma : ℕ → ℝ)
    (delta : ℕ → E × F)
    (zv : ℕ → {z : E × F // z ∈ X ×ˢ Y})
    (z : {z : E × F // z ∈ X ×ˢ Y})
    (t : ℕ)
    (heta_pos : ∀ i, i ∈ Finset.Icc 1 t → 0 < eta i)
    (htau_pos : ∀ i, i ∈ Finset.Icc 1 t → 0 < tau i)
    (hgamma_pos : ∀ i, i ∈ Finset.Icc 1 t → 0 < gamma i)
    (hX_convex : Convex ℝ X)
    (hY_convex : Convex ℝ Y)
    (hprox :
      ∀ i, i ∈ Finset.Icc 1 t →
        IsMinOn
          (fun u : E × F =>
            -eta i * ⟪(delta i).1, u.1⟫_ℝ -
              tau i * ⟪(delta i).2, u.2⟫_ℝ +
                νX.bregman u.1 (zv i).1.1 + νY.bregman u.2 (zv i).1.2)
          (X ×ˢ Y) (zv (i + 1)).1) :
    Finset.sum (Finset.Icc 1 t) (fun i =>
        gamma i *
          (⟪-(delta i).1, (zv i).1.1 - z.1.1⟫_ℝ +
            ⟪-(delta i).2, (zv i).1.2 - z.1.2⟫_ℝ)) ≤
      SOptLib.twoBlockWeightedBregmanBoundaryFor gamma eta tau
          (fun x u => νX.bregman x u) (fun y v => νY.bregman y v)
          (fun i => (zv i).1) t z.1 +
        Finset.sum (Finset.Icc 1 t) (fun i =>
          eta i * gamma i / 2 * ‖(delta i).1‖ ^ 2) +
        Finset.sum (Finset.Icc 1 t) (fun i =>
          tau i * gamma i / 2 * ‖(delta i).2‖ ^ 2) := by
  have hstep_minXY :
      ∀ i, i ∈ Finset.Icc 1 t →
        ((zv (i + 1)).1.1 ∈ X ∧
          IsMinOn
            (fun u : E =>
              ⟪(-eta i) • (delta i).1, u⟫_ℝ + νX.bregman u (zv i).1.1)
            X (zv (i + 1)).1.1) ∧
          ((zv (i + 1)).1.2 ∈ Y ∧
            IsMinOn
              (fun u : F =>
                ⟪(-tau i) • (delta i).2, u⟫_ℝ + νY.bregman u (zv i).1.2)
              Y (zv (i + 1)).1.2) := by
    intro i hi
    have hxhat : (zv (i + 1)).1.1 ∈ X := (zv (i + 1)).2.1
    have hyhat : (zv (i + 1)).1.2 ∈ Y := (zv (i + 1)).2.2
    have hmin_prod :
        IsMinOn
          (fun p : E × F =>
            (⟪(-eta i) • (delta i).1, p.1⟫_ℝ + νX.bregman p.1 (zv i).1.1) +
              (⟪(-tau i) • (delta i).2, p.2⟫_ℝ + νY.bregman p.2 (zv i).1.2))
          (X ×ˢ Y)
          ((zv (i + 1)).1.1, (zv (i + 1)).1.2) := by
      simpa only [real_inner_smul_left, Prod.fst, Prod.snd, sub_eq_add_neg,
        neg_mul, add_assoc, add_left_comm, add_comm] using (hprox i hi)
    exact
      SOptLib.product_isMinOn_coordinate_isMinOn
        (hxy := ⟨hxhat, hyhat⟩) (hmin := hmin_prod)
  have hstep_minX :
      ∀ i, i ∈ Finset.Icc 1 t →
        (zv (i + 1)).1.1 ∈ X ∧
          IsMinOn
            (fun u : E =>
              ⟪(-eta i) • (delta i).1, u⟫_ℝ + νX.bregman u (zv i).1.1)
            X (zv (i + 1)).1.1 := by
    intro i hi
    exact (hstep_minXY i hi).1
  have hstep_minY :
      ∀ i, i ∈ Finset.Icc 1 t →
        (zv (i + 1)).1.2 ∈ Y ∧
          IsMinOn
            (fun u : F =>
              ⟪(-tau i) • (delta i).2, u⟫_ℝ + νY.bregman u (zv i).1.2)
            Y (zv (i + 1)).1.2 := by
    intro i hi
    exact (hstep_minXY i hi).2
  have hzX : z.1.1 ∈ X := z.2.1
  have hzY : z.1.2 ∈ Y := z.2.2
  have hvX₁ : (zv 1).1.1 ∈ X := (zv 1).2.1
  have hvY₁ : (zv 1).1.2 ∈ Y := (zv 1).2.2
  have hmdX :=
    mirror_descent_summation_of_linear_bregman_minimizers νX
      (fun i => (-eta i) • (delta i).1)
      (fun i => (zv i).1.1) t z.1.1 hX_convex hzX hvX₁ hstep_minX
  have hmdY :=
    mirror_descent_summation_of_linear_bregman_minimizers νY
      (fun i => (-tau i) • (delta i).2)
      (fun i => (zv i).1.2) t z.1.2 hY_convex hzY hvY₁ hstep_minY
  have hweightedX :
      ∀ i, i ∈ Finset.Icc 1 t →
        gamma i * ⟪-(delta i).1, (zv i).1.1 - z.1.1⟫_ℝ ≤
          gamma i / eta i *
              (νX.bregman z.1.1 (zv i).1.1 -
                νX.bregman z.1.1 (zv (i + 1)).1.1) +
            eta i * gamma i / 2 * ‖(delta i).1‖ ^ 2 := by
    intro i hi
    have hη : 0 < eta i := heta_pos i hi
    have hγ : 0 < gamma i := hgamma_pos i hi
    have hnonneg : 0 ≤ gamma i / eta i :=
      div_nonneg (le_of_lt hγ) (le_of_lt hη)
    have hstep := (hmdX.1 i hi)
    have hscale := mul_le_mul_of_nonneg_left hstep hnonneg
    have hleft :
        gamma i / eta i *
            ⟪(-eta i) • (delta i).1, (zv i).1.1 - z.1.1⟫_ℝ =
          gamma i * ⟪-(delta i).1, (zv i).1.1 - z.1.1⟫_ℝ := by
      rw [real_inner_smul_left, inner_neg_left]
      field_simp [ne_of_gt hη]
    have hnorm :
        ‖(-eta i) • (delta i).1‖ = eta i * ‖(delta i).1‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      have habs : |(-eta i : ℝ)| = eta i := by
        rw [abs_neg]
        exact abs_of_pos hη
      rw [habs]
    have hright :
        gamma i / eta i *
            (νX.bregman z.1.1 (zv i).1.1 -
                νX.bregman z.1.1 (zv (i + 1)).1.1 +
              ‖(-eta i) • (delta i).1‖ ^ 2 / 2) =
          gamma i / eta i *
              (νX.bregman z.1.1 (zv i).1.1 -
                νX.bregman z.1.1 (zv (i + 1)).1.1) +
            eta i * gamma i / 2 * ‖(delta i).1‖ ^ 2 := by
      rw [mul_add, hnorm]
      field_simp [ne_of_gt hη]
    rw [hleft] at hscale
    rw [hright] at hscale
    exact hscale
  have hweightedY :
      ∀ i, i ∈ Finset.Icc 1 t →
        gamma i * ⟪-(delta i).2, (zv i).1.2 - z.1.2⟫_ℝ ≤
          gamma i / tau i *
              (νY.bregman z.1.2 (zv i).1.2 -
                νY.bregman z.1.2 (zv (i + 1)).1.2) +
            tau i * gamma i / 2 * ‖(delta i).2‖ ^ 2 := by
    intro i hi
    have hτ : 0 < tau i := htau_pos i hi
    have hγ : 0 < gamma i := hgamma_pos i hi
    have hnonneg : 0 ≤ gamma i / tau i :=
      div_nonneg (le_of_lt hγ) (le_of_lt hτ)
    have hstep := (hmdY.1 i hi)
    have hscale := mul_le_mul_of_nonneg_left hstep hnonneg
    have hleft :
        gamma i / tau i *
            ⟪(-tau i) • (delta i).2, (zv i).1.2 - z.1.2⟫_ℝ =
          gamma i * ⟪-(delta i).2, (zv i).1.2 - z.1.2⟫_ℝ := by
      rw [real_inner_smul_left, inner_neg_left]
      field_simp [ne_of_gt hτ]
    have hnorm :
        ‖(-tau i) • (delta i).2‖ = tau i * ‖(delta i).2‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      have habs : |(-tau i : ℝ)| = tau i := by
        rw [abs_neg]
        exact abs_of_pos hτ
      rw [habs]
    have hright :
        gamma i / tau i *
            (νY.bregman z.1.2 (zv i).1.2 -
                νY.bregman z.1.2 (zv (i + 1)).1.2 +
              ‖(-tau i) • (delta i).2‖ ^ 2 / 2) =
          gamma i / tau i *
              (νY.bregman z.1.2 (zv i).1.2 -
                νY.bregman z.1.2 (zv (i + 1)).1.2) +
            tau i * gamma i / 2 * ‖(delta i).2‖ ^ 2 := by
      rw [mul_add, hnorm]
      field_simp [ne_of_gt hτ]
    rw [hleft] at hscale
    rw [hright] at hscale
    exact hscale
  have hpoint :
      ∀ i, i ∈ Finset.Icc 1 t →
        gamma i *
            (⟪-(delta i).1, (zv i).1.1 - z.1.1⟫_ℝ +
              ⟪-(delta i).2, (zv i).1.2 - z.1.2⟫_ℝ) ≤
          (gamma i / eta i *
              (νX.bregman z.1.1 (zv i).1.1 -
                νX.bregman z.1.1 (zv (i + 1)).1.1) +
            gamma i / tau i *
              (νY.bregman z.1.2 (zv i).1.2 -
                νY.bregman z.1.2 (zv (i + 1)).1.2)) +
            eta i * gamma i / 2 * ‖(delta i).1‖ ^ 2 +
            tau i * gamma i / 2 * ‖(delta i).2‖ ^ 2 := by
    intro i hi
    have hx := hweightedX i hi
    have hy := hweightedY i hi
    have hxy := add_le_add hx hy
    simpa [mul_add, add_assoc, add_left_comm, add_comm] using hxy
  calc
    Finset.sum (Finset.Icc 1 t) (fun i =>
        gamma i *
          (⟪-(delta i).1, (zv i).1.1 - z.1.1⟫_ℝ +
            ⟪-(delta i).2, (zv i).1.2 - z.1.2⟫_ℝ)) ≤
        Finset.sum (Finset.Icc 1 t) (fun i =>
          (gamma i / eta i *
              (νX.bregman z.1.1 (zv i).1.1 -
                νX.bregman z.1.1 (zv (i + 1)).1.1) +
            gamma i / tau i *
              (νY.bregman z.1.2 (zv i).1.2 -
                νY.bregman z.1.2 (zv (i + 1)).1.2)) +
            eta i * gamma i / 2 * ‖(delta i).1‖ ^ 2 +
            tau i * gamma i / 2 * ‖(delta i).2‖ ^ 2) := by
          exact Finset.sum_le_sum hpoint
    _ = SOptLib.twoBlockWeightedBregmanBoundaryFor gamma eta tau
          (fun x u => νX.bregman x u) (fun y v => νY.bregman y v)
          (fun i => (zv i).1) t z.1 +
        Finset.sum (Finset.Icc 1 t) (fun i =>
          eta i * gamma i / 2 * ‖(delta i).1‖ ^ 2) +
        Finset.sum (Finset.Icc 1 t) (fun i =>
          tau i * gamma i / 2 * ‖(delta i).2‖ ^ 2) := by
        rw [SOptLib.twoBlockWeightedBregmanBoundaryFor_def]
        repeat rw [Finset.sum_add_distrib]

/-- A generated auxiliary prox process controls guarded proof-indexed noise by
a two-block Bregman boundary plus squared-noise penalties.

The theorem adapts the deterministic two-block prox summation bound to the
common generated-stream shape where residuals are indexed by a proof of
positive time and finite-window sums use `if hi : 1 ≤ i` guards.

Layer: Layer1 | Gap: Level 1 (generated auxiliary prox noise bound)
Proof: build an unguarded delta sequence from the proof-indexed residuals,
  convert the pointwise prox-step certificate into the `IsMinOn` hypothesis for
  the core two-block theorem, then rewrite guarded sums on the finite window.
Source: SOptLib two-block Bregman prox summation API and Mathlib finite-interval
  sum congruence for guarded generated streams
Used in: generated stochastic accelerated primal-dual auxiliary prox-process
  noise estimate before pathwise gap aggregation
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/key_lemmas/4
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem generated_auxiliary_prox_noise_bound
    {Ω E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {X : Set E} {Y : Set F}
    (νX : SOptLib.DistanceGeneratingFunctionOn E X)
    (νY : SOptLib.DistanceGeneratingFunctionOn F Y)
    (eta tau gamma : ℕ → ℝ)
    (deltaX : ∀ i, 1 ≤ i → Ω → E)
    (deltaY : ∀ i, 1 ≤ i → Ω → F)
    (auxiliaryProcess : Ω → ℕ → {z : E × F // z ∈ X ×ˢ Y})
    (auxiliaryStep :
      ∀ i, 1 ≤ i → {z : E × F // z ∈ X ×ˢ Y} → Ω →
        {z : E × F // z ∈ X ×ˢ Y})
    (t : ℕ) (z : {z : E × F // z ∈ X ×ˢ Y}) (ω : Ω)
    (heta_pos : ∀ i, i ∈ Finset.Icc 1 t → 0 < eta i)
    (htau_pos : ∀ i, i ∈ Finset.Icc 1 t → 0 < tau i)
    (hgamma_pos : ∀ i, i ∈ Finset.Icc 1 t → 0 < gamma i)
    (hX_convex : Convex ℝ X)
    (hY_convex : Convex ℝ Y)
    (hprocess_succ :
      ∀ i (hi : 1 ≤ i) (ω : Ω),
        auxiliaryProcess ω (i + 1) =
          auxiliaryStep i hi (auxiliaryProcess ω i) ω)
    (hstep_min :
      ∀ i (hi : 1 ≤ i) (current : {z : E × F // z ∈ X ×ˢ Y}) (ω : Ω)
        (u : E × F), u ∈ X ×ˢ Y →
          -eta i * ⟪deltaX i hi ω, (auxiliaryStep i hi current ω).1.1⟫_ℝ -
              tau i * ⟪deltaY i hi ω, (auxiliaryStep i hi current ω).1.2⟫_ℝ +
                νX.bregman (auxiliaryStep i hi current ω).1.1 current.1.1 +
                νY.bregman (auxiliaryStep i hi current ω).1.2 current.1.2 ≤
            -eta i * ⟪deltaX i hi ω, u.1⟫_ℝ -
              tau i * ⟪deltaY i hi ω, u.2⟫_ℝ +
                νX.bregman u.1 current.1.1 +
                νY.bregman u.2 current.1.2) :
    Finset.sum (Finset.Icc 1 t) (fun i =>
        if hi : 1 ≤ i then
          gamma i *
            (⟪-deltaX i hi ω, (auxiliaryProcess ω i).1.1 - z.1.1⟫_ℝ +
              ⟪-deltaY i hi ω, (auxiliaryProcess ω i).1.2 - z.1.2⟫_ℝ)
        else 0) ≤
      SOptLib.twoBlockWeightedBregmanBoundary gamma eta tau
          (fun x u => νX.bregman x u) (fun y v => νY.bregman y v)
          (fun i (_ : Unit) => (auxiliaryProcess ω i).1) t z.1 () +
        Finset.sum (Finset.Icc 1 t) (fun i =>
          if hi : 1 ≤ i then
            eta i * gamma i / 2 * ‖deltaX i hi ω‖ ^ 2
          else 0) +
        Finset.sum (Finset.Icc 1 t) (fun i =>
          if hi : 1 ≤ i then
            tau i * gamma i / 2 * ‖deltaY i hi ω‖ ^ 2
          else 0) := by
  classical
  let deltaGenerated : ℕ → E × F := fun i =>
    if hi : 1 ≤ i then
      (deltaX i hi ω, deltaY i hi ω)
    else 0
  have hmain := auxiliary_prox_noise_bound
    (νX := νX) (νY := νY)
    (eta := eta) (tau := tau) (gamma := gamma)
    (delta := deltaGenerated) (zv := fun i => auxiliaryProcess ω i)
    (z := z) (t := t)
    heta_pos htau_pos hgamma_pos hX_convex hY_convex
    (by
      intro i hiIcc
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hiIcc).1
      change IsMinOn
        (fun u : E × F =>
          -eta i * ⟪(deltaGenerated i).1, u.1⟫_ℝ -
            tau i * ⟪(deltaGenerated i).2, u.2⟫_ℝ +
              νX.bregman u.1 (auxiliaryProcess ω i).1.1 +
              νY.bregman u.2 (auxiliaryProcess ω i).1.2)
        (X ×ˢ Y) (auxiliaryProcess ω (i + 1)).1
      rw [hprocess_succ i hi1 ω]
      intro u hu
      simpa [deltaGenerated, hi1] using
        hstep_min i hi1 (auxiliaryProcess ω i) ω u hu)
  have hleft_eq :
      Finset.sum (Finset.Icc 1 t) (fun i =>
        if hi : 1 ≤ i then
          gamma i *
            (⟪-deltaX i hi ω, (auxiliaryProcess ω i).1.1 - z.1.1⟫_ℝ +
              ⟪-deltaY i hi ω, (auxiliaryProcess ω i).1.2 - z.1.2⟫_ℝ)
        else 0) =
        Finset.sum (Finset.Icc 1 t) (fun i =>
          gamma i *
            (⟪-(deltaGenerated i).1, (auxiliaryProcess ω i).1.1 - z.1.1⟫_ℝ +
              ⟪-(deltaGenerated i).2, (auxiliaryProcess ω i).1.2 - z.1.2⟫_ℝ)) := by
    refine Finset.sum_congr rfl ?_
    intro i hiIcc
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hiIcc).1
    simp [deltaGenerated, hi1]
  have hpenX_eq :
      Finset.sum (Finset.Icc 1 t) (fun i =>
        if hi : 1 ≤ i then
          eta i * gamma i / 2 * ‖deltaX i hi ω‖ ^ 2
        else 0) =
        Finset.sum (Finset.Icc 1 t) (fun i =>
          eta i * gamma i / 2 * ‖(deltaGenerated i).1‖ ^ 2) := by
    refine Finset.sum_congr rfl ?_
    intro i hiIcc
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hiIcc).1
    simp [deltaGenerated, hi1]
  have hpenY_eq :
      Finset.sum (Finset.Icc 1 t) (fun i =>
        if hi : 1 ≤ i then
          tau i * gamma i / 2 * ‖deltaY i hi ω‖ ^ 2
        else 0) =
        Finset.sum (Finset.Icc 1 t) (fun i =>
          tau i * gamma i / 2 * ‖(deltaGenerated i).2‖ ^ 2) := by
    refine Finset.sum_congr rfl ?_
    intro i hiIcc
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hiIcc).1
    simp [deltaGenerated, hi1]
  calc
    Finset.sum (Finset.Icc 1 t) (fun i =>
        if hi : 1 ≤ i then
          gamma i *
            (⟪-deltaX i hi ω, (auxiliaryProcess ω i).1.1 - z.1.1⟫_ℝ +
              ⟪-deltaY i hi ω, (auxiliaryProcess ω i).1.2 - z.1.2⟫_ℝ)
        else 0) =
        Finset.sum (Finset.Icc 1 t) (fun i =>
          gamma i *
            (⟪-(deltaGenerated i).1, (auxiliaryProcess ω i).1.1 - z.1.1⟫_ℝ +
              ⟪-(deltaGenerated i).2, (auxiliaryProcess ω i).1.2 - z.1.2⟫_ℝ)) := hleft_eq
    _ ≤ SOptLib.twoBlockWeightedBregmanBoundary gamma eta tau
          (fun x u => νX.bregman x u) (fun y v => νY.bregman y v)
          (fun i (_ : Unit) => (auxiliaryProcess ω i).1) t z.1 () +
        Finset.sum (Finset.Icc 1 t) (fun i =>
          eta i * gamma i / 2 * ‖(deltaGenerated i).1‖ ^ 2) +
        Finset.sum (Finset.Icc 1 t) (fun i =>
          tau i * gamma i / 2 * ‖(deltaGenerated i).2‖ ^ 2) := hmain
    _ = SOptLib.twoBlockWeightedBregmanBoundary gamma eta tau
          (fun x u => νX.bregman x u) (fun y v => νY.bregman y v)
          (fun i (_ : Unit) => (auxiliaryProcess ω i).1) t z.1 () +
        Finset.sum (Finset.Icc 1 t) (fun i =>
          if hi : 1 ≤ i then
            eta i * gamma i / 2 * ‖deltaX i hi ω‖ ^ 2
          else 0) +
        Finset.sum (Finset.Icc 1 t) (fun i =>
          if hi : 1 ≤ i then
            tau i * gamma i / 2 * ‖deltaY i hi ω‖ ^ 2
          else 0) := by
        rw [← hpenX_eq, ← hpenY_eq]
