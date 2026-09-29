import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Seminorm
import Mathlib.Topology.MetricSpace.Basic
import SOptLib.Glue.Analysis
import SOptLib.Model.Subdifferential
import Mathlib.Analysis.Convex.Approximation
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic
import SOptLib.Model.IsSimpleConvexTermOn
import SOptLib.Model.Carrier

open scoped BigOperators InnerProductSpace

namespace SOptLib

/-- Two one-sided bounded subgradient inequalities imply an absolute Lipschitz bound.

If `g x` and `g y` are supporting subgradients at two carrier points and both
subgradients have norm at most `M`, then the objective values differ by at most
`M` times the distance between the evaluated points.

Layer: Layer0 | Gap: Level 1 (subgradient Lipschitz bound)
Proof: rearrange the two support inequalities into upper bounds for
  `f x - f y` and `f y - f x`, control each inner product with
  `real_inner_le_norm`, and combine the two one-sided estimates using `abs_le`.
Source: Mathlib inner product norm inequalities and real absolute-value order APIs
Used in: stochastic mirror descent Lipschitz control from uniformly bounded subgradients
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
theorem abs_sub_le_of_subgradient_norm_bound
    {P E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : P → ℝ) (eval : P → E) (g : P → E) (M : ℝ) {x y : P}
    (hx_support : f x + ⟪g x, eval y - eval x⟫_ℝ ≤ f y)
    (hy_support : f y + ⟪g y, eval x - eval y⟫_ℝ ≤ f x)
    (hx_norm : ‖g x‖ ≤ M) (hy_norm : ‖g y‖ ≤ M) :
    ‖f x - f y‖ ≤ M * ‖eval x - eval y‖ := by
  have hxy :
      f x - f y ≤ M * ‖eval x - eval y‖ := by
    have hdiff :
        f x - f y ≤ ⟪g x, eval x - eval y⟫_ℝ := by
      calc
        f x - f y ≤ -⟪g x, eval y - eval x⟫_ℝ := by linarith
        _ = ⟪g x, eval x - eval y⟫_ℝ := by
          have hsub : eval x - eval y = -(eval y - eval x) := by
            abel
          rw [hsub, inner_neg_right]
    have hinner :
        ⟪g x, eval x - eval y⟫_ℝ ≤ ‖g x‖ * ‖eval x - eval y‖ :=
      real_inner_le_norm _ _
    have hM :
        ‖g x‖ * ‖eval x - eval y‖ ≤ M * ‖eval x - eval y‖ :=
      mul_le_mul_of_nonneg_right hx_norm (norm_nonneg _)
    exact hdiff.trans (hinner.trans hM)
  have hyx :
      f y - f x ≤ M * ‖eval x - eval y‖ := by
    have hdiff :
        f y - f x ≤ ⟪g y, eval y - eval x⟫_ℝ := by
      calc
        f y - f x ≤ -⟪g y, eval x - eval y⟫_ℝ := by linarith
        _ = ⟪g y, eval y - eval x⟫_ℝ := by
          have hsub : eval y - eval x = -(eval x - eval y) := by
            abel
          rw [hsub, inner_neg_right]
    have hinner :
        ⟪g y, eval y - eval x⟫_ℝ ≤ ‖g y‖ * ‖eval y - eval x‖ :=
      real_inner_le_norm _ _
    have hM :
        ‖g y‖ * ‖eval y - eval x‖ ≤ M * ‖eval y - eval x‖ :=
      mul_le_mul_of_nonneg_right hy_norm (norm_nonneg _)
    have hbound : f y - f x ≤ M * ‖eval y - eval x‖ :=
      hdiff.trans (hinner.trans hM)
    simpa [norm_sub_rev] using hbound
  have hneg : -(M * ‖eval x - eval y‖) ≤ f x - f y := by
    linarith
  simpa [Real.norm_eq_abs] using abs_le.mpr ⟨hneg, hxy⟩

/-- Bounded carrier subgradients make the objective Lipschitz along evaluation.

If every carrier point has a supporting subgradient with norm at most `M`, then
the objective values differ by at most `M` times the distance between evaluated
carrier points.

Layer: Layer0 | Gap: Level 1 (bounded subgradients imply Lipschitz on carrier)
Proof: apply the two supporting-subgradient inequalities in opposite directions
  and combine them with the uniform norm bound via the inner-product Cauchy
  Schwarz estimate packaged in `abs_sub_le_of_subgradient_norm_bound`.
Source: Mathlib inner product norm inequalities and real absolute-value order APIs
Used in: stochastic mirror descent Lipschitz control from bounded mean-oracle subgradients
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem lipschitzOn_of_forall_subgradient_norm_le
    {P E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : P → ℝ) (eval : P → E) (g : P → E) (M : ℝ)
    (h_subgradient : ∀ x y : P, f x + ⟪g x, eval y - eval x⟫_ℝ ≤ f y)
    (h_norm : ∀ x : P, ‖g x‖ ≤ M) :
    ∀ x y : P, ‖f x - f y‖ ≤ M * ‖eval x - eval y‖ := by
  intro x y
  exact abs_sub_le_of_subgradient_norm_bound f eval g M
    (h_subgradient x y) (h_subgradient y x) (h_norm x) (h_norm y)

/-- A pointwise mean-oracle subgradient hypothesis specializes to one carrier point.

If the mean oracle `g` belongs to the carrier subdifferential of `f` at every
carrier point, then it belongs to that carrier subdifferential at the chosen
carrier point `x`.

Layer: Layer0 | Gap: Level 0 (mean-oracle carrier subgradient specialization)
Proof: specialize the pointwise carrier-subdifferential assumption at `x`.
  The proof is direct implication elimination.
Source: Mathlib subtype and set membership APIs
Used in: stochastic mirror descent unbiased oracle carrier-subgradient check
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem meanOracle_mem_carrierSubdifferential
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (f : {x : E // x ∈ X} → ℝ) (g : {x : E // x ∈ X} → E)
    (h_meanOracle_subgradient : ∀ x : {x : E // x ∈ X},
      g x ∈ SOptLib.carrierSubdifferential f x) (x : {x : E // x ∈ X}) :
    g x ∈ SOptLib.carrierSubdifferential f x := by
  exact h_meanOracle_subgradient x

-- Batch 7 promoted from Staging/SOptLib_IsSimpleConvexTermOn_exists_strict_affine_minorant.lean
-- Generalization plan (G0):
-- concept/name: strict affine minorant for a simple convex term on a closed
--   carrier; orig was h_simple_exists_strict_affine_minorant.
-- generality used: Hilbert-space carrier `{E}` with `[NormedAddCommGroup E]`
--   and `[InnerProductSpace ℝ E]`; no measure, independence, integrability,
--   oracle, or finite-dimensional hypothesis is used. Convexity and structural
--   continuity come from `IsSimpleConvexTermOn X h`, and closedness is the only
--   separate carrier hypothesis required by Mathlib separation.
-- portable call pattern: nonsmooth support and proximal proofs supply a simple
--   composite penalty witness, a closed feasible carrier, a carrier point `z`,
--   and a strict subvalue `a < h z`; the same affine lower minorant conclusion
--   is used to build support functions or separating lower models.
-- counterargument checked: not merely paper traceability because the statement
--   packages the standard convex-analysis separation theorem behind the
--   promoted simple-term model predicate; not a pure wrapper at call sites
--   because it derives lower semicontinuity from the known expression witness
--   and returns the inequality over carrier subtype points.
-- coverage search: checked catalog/source hits for `IsSimpleConvexTermOn`,
--   `SimpleConvexTermExpr.continuous`, `continuousOn`, `carrier_measurable`,
--   `exists_affine_le_of_lt`, and LeanSearch for "convex lower semicontinuous
--   closed set strict affine minorant"; coverage is partial. Mathlib has
--   `ConvexOn.exists_affine_le_of_lt`, but no SOptLib bridge from a simple
--   convex term witness to the carrier-subtype affine minorant.
-- minimal hypotheses: all already minimal for this bridge; `hX_closed` is
--   required by Mathlib separation, while lower semicontinuity and convexity are
--   derived from the single `IsSimpleConvexTermOn X h` hypothesis.

namespace IsSimpleConvexTermOn

/-- A structurally simple convex term has strict affine lower minorants on a closed carrier.

For any carrier point `z` and any strict subvalue `a < h z`, there is a
continuous affine functional that lies below `h` on every carrier point and
takes the value `a` at `z`.

Layer: Layer0 | Gap: Level 1 (simple convex term affine minorant)
Proof: derive lower semicontinuity from the simple expression witness, combine
  it with stored `ConvexOn`, and apply Mathlib's closed-carrier Hahn-Banach
  affine-minorant theorem.
Source: Mathlib convex approximation by continuous affine functions and SOptLib
  simple-term expression continuity over real Hilbert spaces
Used in: variance-reduced accelerated gradient descent nonsmooth composite
  support construction for feasible prox proofs
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem exists_strict_affine_minorant
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} {h : E → ℝ}
    (hsimple : IsSimpleConvexTermOn X h) (hX_closed : IsClosed X)
    (z : {x : E // x ∈ X}) {a : ℝ} (ha : a < h z.1) :
    ∃ (l : E →L[ℝ] ℝ) (c : ℝ),
      (∀ y : {x : E // x ∈ X}, l y.1 + c ≤ h y.1) ∧
        l z.1 + c = a := by
  have hknown :
      ContinuousOn hsimple.knownStructure.eval X :=
    (SimpleConvexTermExpr.continuous hsimple.knownStructure).continuousOn
  have hcontinuous : ContinuousOn h X :=
    hknown.congr (fun x hx => (hsimple.agreesOn x hx).symm)
  have hlower : LowerSemicontinuousOn h X :=
    hcontinuous.lowerSemicontinuousOn
  obtain ⟨l, c, hle, heq⟩ :=
    hsimple.convex.exists_affine_le_of_lt (𝕜 := ℝ) z.2 ha hX_closed hlower
  refine ⟨l, c, ?_, heq⟩
  intro y
  simpa using hle y

end IsSimpleConvexTermOn

-- Batch 7 promoted from Staging/bounded_approx_supports_of_finite_subfamilies.lean
-- Generalization plan (G0):
-- concept/name: finite-intersection lift for bounded approximate carrier supports; orig was theorem59_bounded_approx_supports_of_finite_subfamilies, renamed away from the theorem number and paper setup.
-- generality used: carrier `X : Set E`, real-valued objective on `{x : E // x in X}`, one carrier point `z`, a uniform bound `B`, real Hilbert structure, and `[ProperSpace E]` for compact closed balls; no measure, convexity, smoothness, or oracle assumptions are used.
-- portable call pattern: proximal-gradient, mirror-descent, and variance-reduced KKT support proofs can first certify every finite comparison family with a uniform norm bound, then call this lemma to obtain the same epsilon-support certificate over the full carrier; `X`, `f`, `z`, `B`, and the finite certificates change while the conclusion shape stays fixed.
-- counterargument checked: not paper-local traceability because the statement packages the reusable compact finite-intersection step before approximate-support exactification; not a duplicate of `exists_carrierSubdifferential_of_bounded_approx_supports`, which sends epsilon to zero after full-carrier approximate supports are already available.
-- coverage search: searched CATALOG/SOptLib/Staging for `bounded approximate support`, `finite subfamilies`, `carrierSubdifferential`, and `support finite`; queried LeanSearch for compact finite-intersection closed-set nonempty intersections. Mathlib has `IsCompact.inter_iInter_nonempty` and directed compact-intersection APIs, and SOptLib has the later exactification lemma, but neither packages finite-family bounded approximate supports into a full-carrier epsilon support certificate.
-- minimal hypotheses: removed the paper setup, finite-dimensional Euclidean carrier, and unused `0 <= B`; `[ProperSpace E]` is the only compactness hypothesis needed for closed balls.

/-- Finite-family bounded approximate supports give a full-carrier approximate
support.

For a fixed positive `ε`, suppose every finite family of carrier comparisons
admits a support vector with norm at most `B` satisfying the same `ε`-relaxed
support inequalities. Compactness of the closed ball and the finite
intersection property produce one vector that satisfies all carrier comparisons.

Layer: Layer0 | Gap: Level 1 (finite-family approximate supports to full support)
Proof: define the closed subsets of the closed ball cut out by each finite
  comparison family, use the directed compact-intersection theorem for the
  union-directed family, and read the singleton comparison set from the
  resulting intersection point.
Source: Mathlib compact closed-ball, finite-set union, closed halfspace, and
  directed compact-intersection APIs
Used in: accelerated proximal-gradient KKT support recovery from finite
  comparison-family support certificates
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem bounded_approx_supports_of_finite_subfamilies
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
    {X : Set E} (f : {x : E // x ∈ X} → ℝ) (z : {x : E // x ∈ X})
    (B : ℝ)
    (hfinite :
      ∀ ε : ℝ, 0 < ε →
        ∀ Y : Finset {x : E // x ∈ X},
          ∃ p : E,
            ‖p‖ ≤ B ∧
              ∀ y : {x : E // x ∈ X}, y ∈ Y →
                f z - ε + ⟪p, y.1 - z.1⟫_ℝ ≤ f y) :
    ∀ ε : ℝ, 0 < ε →
      ∃ p : E,
        ‖p‖ ≤ B ∧
          ∀ y : {x : E // x ∈ X},
            f z - ε + ⟪p, y.1 - z.1⟫_ℝ ≤ f y := by
  classical
  intro ε hε
  let C : Finset {x : E // x ∈ X} → Set E :=
    fun Y =>
      {p | ‖p‖ ≤ B ∧
        ∀ y : {x : E // x ∈ X}, y ∈ Y →
          f z - ε + ⟪p, y.1 - z.1⟫_ℝ ≤ f y}
  have hC_nonempty : ∀ Y, (C Y).Nonempty := by
    intro Y
    rcases hfinite ε hε Y with ⟨p, hpB, hpY⟩
    exact ⟨p, hpB, hpY⟩
  have hC_closed : ∀ Y, IsClosed (C Y) := by
    intro Y
    have hball : IsClosed {p : E | ‖p‖ ≤ B} :=
      isClosed_le continuous_norm continuous_const
    have hineq :
        IsClosed
          {p : E |
            ∀ y : {x : E // x ∈ X}, y ∈ Y →
              f z - ε + ⟪p, y.1 - z.1⟫_ℝ ≤ f y} := by
      rw [show
          {p : E |
            ∀ y : {x : E // x ∈ X}, y ∈ Y →
              f z - ε + ⟪p, y.1 - z.1⟫_ℝ ≤ f y} =
            ⋂ y : {x : E // x ∈ X}, ⋂ _hy : y ∈ Y,
              {p : E |
                f z - ε + ⟪p, y.1 - z.1⟫_ℝ ≤ f y} by
        ext p
        simp]
      refine isClosed_iInter fun y => isClosed_iInter fun _hy => ?_
      exact isClosed_le (by fun_prop) continuous_const
    rw [show C Y =
        {p : E | ‖p‖ ≤ B} ∩
          {p : E |
            ∀ y : {x : E // x ∈ X}, y ∈ Y →
              f z - ε + ⟪p, y.1 - z.1⟫_ℝ ≤ f y} by
      ext p
      simp [C]]
    exact hball.inter hineq
  have hC_compact : ∀ Y, IsCompact (C Y) := by
    intro Y
    refine (isCompact_closedBall (0 : E) B).of_isClosed_subset (hC_closed Y) ?_
    intro p hp
    have hpB : ‖p‖ ≤ B := hp.1
    simpa [Metric.mem_closedBall, dist_eq_norm] using hpB
  have hC_directed : Directed (· ⊇ ·) C := by
    intro Y₁ Y₂
    refine ⟨Y₁ ∪ Y₂, ?_, ?_⟩
    · intro p hp
      refine ⟨hp.1, ?_⟩
      intro y hy
      exact hp.2 y (Finset.mem_union.mpr (Or.inl hy))
    · intro p hp
      refine ⟨hp.1, ?_⟩
      intro y hy
      exact hp.2 y (Finset.mem_union.mpr (Or.inr hy))
  obtain ⟨p, hp_all⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      C hC_directed hC_nonempty hC_compact hC_closed
  have hp_empty : p ∈ C ∅ := by
    simpa using (Set.mem_iInter.mp hp_all) (∅ : Finset {x : E // x ∈ X})
  refine ⟨p, hp_empty.1, ?_⟩
  intro y
  have hp_single : p ∈ C {y} := by
    simpa using (Set.mem_iInter.mp hp_all) ({y} : Finset {x : E // x ∈ X})
  exact hp_single.2 y (by simp)

-- Batch 7 promoted from Staging/bounded_approx_supports_of_convex_tilted_lower_model.lean
-- Generalization plan (G0):
-- concept/name: bounded approximate support vectors from a convex norm-tilted lower model; orig was theorem59_bounded_approx_supports_of_lipschitz_tilted_model_block, renamed away from theorem number, `nu`, and prox setup vocabulary.
-- generality used: a carrier set in a proper real Hilbert space, an ambient convex objective, one carrier point, positive model scale `c`, nonnegative tilt weight `beta`, and a pointwise norm-tilted lower-model inequality; no measure, stochastic oracle, smoothness, or algorithm update hypotheses are used.
-- portable call pattern: proximal-gradient, mirror-prox, variance-reduced, and composite KKT proofs can call this after a prox comparison yields a convex function lower model tilted by a norm and affine term; the carrier, objective, center, affine vector, scale, and tilt constant vary while the approximate-support conclusion is unchanged.
-- counterargument checked: not paper-local traceability because the proof packages a reusable convex Jensen plus finite-dimensional dual-feasibility step before compact exactification; not a duplicate of `bounded_approx_supports_of_finite_subfamilies`, which assumes finite-family approximate supports instead of deriving them from a convex tilted model.
-- coverage search: searched CATALOG/SOptLib/Staging for `bounded approximate support`, `tilted lower model`, `convex support`, and `finite subfamilies`; LeanSearch for "convex function weighted finite sum Jensen convexOn map_sum_le" returned `ConvexOn.map_sum_le`. Existing entries provide Jensen, finite halfspace feasibility, and finite-family compactness separately, but none derive bounded approximate supports from a convex norm-tilted lower model.
-- minimal hypotheses: the paper setup and Euclidean coordinate space are replaced by `[NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]`; `ConvexOn ℝ X f`, `0 < c`, and `0 ≤ beta` are exactly the hypotheses used to prove Jensen and divide the tilt bound.

/-- A convex norm-tilted lower model gives uniformly bounded approximate
carrier supports.

If a convex objective satisfies a lower-model inequality at `z` tilted by
`beta * K * ‖y - z‖` plus an affine term, then every positive tolerance admits a
support vector with a uniform norm bound and that tolerance loss.

Layer: Layer0 | Gap: Level 1 (convex tilted lower model to approximate supports)
Proof: reduce the all-carrier support requirement to finite comparison
  families, prove the finite-family dual inequalities using Jensen's inequality
  for `ConvexOn`, and apply the closed-ball halfspace feasibility theorem.
Source: Mathlib convex Jensen inequalities, finite halfspace separation, and
  real Hilbert inner-product norm estimates
Used in: variance-reduced accelerated and composite proximal KKT recovery from
  norm-tilted lower models
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem bounded_approx_supports_of_convex_tilted_lower_model
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
    {X : Set E} (f : E → ℝ) (z : {x : E // x ∈ X}) (A : E)
    {c beta : ℝ} (hc_pos : 0 < c) (hbeta_nonneg : 0 ≤ beta)
    (htilted :
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ y : {x : E // x ∈ X},
          c * (f z.1 - f y.1) ≤
            beta * K * ‖y.1 - z.1‖ + ⟪A, y.1 - z.1⟫_ℝ)
    (hconvex : ConvexOn ℝ X f) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ p : E,
          ‖p‖ ≤ B ∧
            ∀ y : {x : E // x ∈ X},
              f z.1 - ε + ⟪p, y.1 - z.1⟫_ℝ ≤ f y.1 := by
  classical
  rcases htilted with ⟨K, hK_nonneg, htilt⟩
  let B : ℝ := ‖A‖ / c + beta * K / c
  have hc_nonneg : 0 ≤ c := le_of_lt hc_pos
  have hB_nonneg : 0 ≤ B := by
    have hA_part : 0 ≤ ‖A‖ / c :=
      div_nonneg (norm_nonneg A) hc_nonneg
    have hK_part : 0 ≤ beta * K / c :=
      div_nonneg (mul_nonneg hbeta_nonneg hK_nonneg) hc_nonneg
    dsimp [B]
    exact add_nonneg hA_part hK_part
  refine ⟨B, hB_nonneg, ?_⟩
  exact
    bounded_approx_supports_of_finite_subfamilies
      (E := E) (X := X) (f := fun x : {x : E // x ∈ X} => f x.1) z B
      (by
        intro ε hε Y
        let ι := {y : {x : E // x ∈ X} // y ∈ Y}
        let dY : ι → E := fun y => y.1.1 - z.1
        let rhsY : ι → ℝ := fun y => f y.1.1 - f z.1 + ε
        have hdualY :
            ∀ w : ι → ℝ,
              (∀ i : ι, 0 ≤ w i) →
              Finset.univ.sum w = 1 →
                -B * ‖Finset.univ.sum (fun i : ι => w i • dY i)‖ ≤
                  Finset.univ.sum (fun i : ι => w i * rhsY i) := by
          intro w hw_nonneg hw_sum
          let ybar : E :=
            Finset.univ.sum (fun i : ι => w i • i.1.1)
          let Dvec : E :=
            Finset.univ.sum (fun i : ι => w i • dY i)
          have hy_mem :
              ∀ i ∈ (Finset.univ : Finset ι), (i : ι).1.1 ∈ X := by
            intro i _hi
            exact i.1.2
          have hybar_mem : ybar ∈ X := by
            dsimp [ybar]
            exact hconvex.1.sum_mem
              (fun i hi => hw_nonneg i) hw_sum hy_mem
          have hJensen :
              f ybar ≤
                Finset.univ.sum (fun i : ι => w i * f i.1.1) := by
            dsimp [ybar]
            simpa using
              hconvex.map_sum_le
                (t := (Finset.univ : Finset ι)) (w := w)
                (p := fun i : ι => i.1.1)
                (fun i hi => hw_nonneg i) hw_sum hy_mem
          have hDvec_eq : Dvec = ybar - z.1 := by
            dsimp [Dvec, dY, ybar]
            calc
              Finset.univ.sum
                  (fun i : ι => w i • (i.1.1 - z.1)) =
                Finset.univ.sum
                  (fun i : ι => (w i • i.1.1) - (w i • z.1)) := by
                    apply Finset.sum_congr rfl
                    intro i _hi
                    rw [smul_sub]
              _ =
                Finset.univ.sum (fun i : ι => w i • i.1.1) -
                  Finset.univ.sum (fun i : ι => w i • z.1) := by
                    rw [Finset.sum_sub_distrib]
              _ =
                Finset.univ.sum (fun i : ι => w i • i.1.1) - z.1 := by
                    rw [← Finset.sum_smul, hw_sum, one_smul]
          have htilt_bar := htilt (⟨ybar, hybar_mem⟩ : {x : E // x ∈ X})
          have htilt_D :
              c * (f z.1 - f ybar) ≤
                beta * K * ‖Dvec‖ + ⟪A, Dvec⟫_ℝ := by
            rw [hDvec_eq]
            exact htilt_bar
          have hinner_le :
              ⟪A, Dvec⟫_ℝ ≤ ‖A‖ * ‖Dvec‖ :=
            real_inner_le_norm A Dvec
          have hscaled_nonneg :
              0 ≤ c * (f ybar - f z.1) +
                (‖A‖ + beta * K) * ‖Dvec‖ := by
            nlinarith [htilt_D, hinner_le]
          have hscaled_eq :
              c * ((f ybar - f z.1) + B * ‖Dvec‖) =
                c * (f ybar - f z.1) +
                  (‖A‖ + beta * K) * ‖Dvec‖ := by
            dsimp [B]
            field_simp [ne_of_gt hc_pos]
          have hmodel_nonneg :
              0 ≤ (f ybar - f z.1) + B * ‖Dvec‖ := by
            have hc_mul :
                0 ≤ c * ((f ybar - f z.1) + B * ‖Dvec‖) := by
              rwa [hscaled_eq]
            exact nonneg_of_mul_nonneg_right hc_mul hc_pos
          have hsum_rhs_eq :
              Finset.univ.sum (fun i : ι => w i * rhsY i) =
                Finset.univ.sum (fun i : ι => w i * f i.1.1) -
                  f z.1 + ε := by
            dsimp [rhsY]
            calc
              Finset.univ.sum
                  (fun i : ι => w i * (f i.1.1 - f z.1 + ε)) =
                Finset.univ.sum
                  (fun i : ι =>
                    w i * f i.1.1 - w i * f z.1 + w i * ε) := by
                    apply Finset.sum_congr rfl
                    intro i _hi
                    ring
              _ =
                Finset.univ.sum (fun i : ι => w i * f i.1.1) -
                  Finset.univ.sum (fun i : ι => w i * f z.1) +
                    Finset.univ.sum (fun i : ι => w i * ε) := by
                    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
              _ =
                Finset.univ.sum (fun i : ι => w i * f i.1.1) -
                  (Finset.univ.sum (fun i : ι => w i)) * f z.1 +
                    (Finset.univ.sum (fun i : ι => w i)) * ε := by
                    rw [← Finset.sum_mul, ← Finset.sum_mul]
              _ =
                Finset.univ.sum (fun i : ι => w i * f i.1.1) -
                  f z.1 + ε := by
                    rw [hw_sum]
                    ring
          have hsum_rhs_ge :
              f ybar - f z.1 ≤
                Finset.univ.sum (fun i : ι => w i * rhsY i) := by
            rw [hsum_rhs_eq]
            nlinarith [hJensen, hε]
          have hdual_nonneg :
              0 ≤ Finset.univ.sum (fun i : ι => w i * rhsY i) +
                B * ‖Dvec‖ := by
            nlinarith [hmodel_nonneg, hsum_rhs_ge]
          change -B * ‖Dvec‖ ≤
            Finset.univ.sum (fun i : ι => w i * rhsY i)
          linarith
        rcases
          exists_closedBall_forall_inner_le_of_dual_simplex
            (E := E) B hB_nonneg dY rhsY hdualY with
          ⟨p, hpB, hpY⟩
        refine ⟨p, hpB, ?_⟩
        intro y hy
        have hy_support := hpY ⟨y, hy⟩
        dsimp [dY, rhsY] at hy_support
        linarith)

-- Batch 7 promoted from Staging/exists_carrierSubdifferential_of_bounded_approx_supports.lean
-- Generalization plan (G0):
-- concept/name: compactness exactification of bounded approximate carrier supports; orig was theorem59_exact_carrierSubgradient_of_bounded_approx_supports.
-- generality used: carrier `X : Set E`, real-valued objective on `{x // x in X}`, Hilbert structure, and `[ProperSpace E]` for compact closed balls; no measure, convexity, smoothness, or oracle assumptions.
-- portable call pattern: proximal and mirror-descent KKT proofs can produce epsilon-support vectors with a uniform norm bound, then call this lemma to obtain an exact carrier subgradient; `X`, `f`, `z`, `B`, and the approximate-support construction change while the conclusion stays `p in carrierSubdifferential f z`.
-- counterargument checked: not paper-local traceability or a one-line wrapper; the proof packages a reusable compactness limiting step, and the formula is not split into a def because it is an assumption shape rather than a named mathematical object.
-- coverage search: searched CATALOG/SOptLib for carrierSubdifferential, bounded approximate support, compact support exactification, and queried LeanSearch for directed compact intersections; existing entries define carrierSubdifferential and support Lipschitz facts but none convert uniformly bounded approximate supports to exact membership.
-- minimal hypotheses: removed the paper setup and finite-dimensional Euclidean carrier, replacing them by `[ProperSpace E]`; no `B >= 0` hypothesis is needed because nonempty approximate supports already imply the closed-ball family is nonempty.

/-- Uniformly bounded approximate carrier supports have an exact limiting carrier
subgradient.

For every positive `ε`, suppose there is a support vector of norm at most `B`
whose carrier support inequality is allowed an additive `ε` loss at `z`. In a
proper Hilbert space, compactness of the closed ball lets these approximate
support sets be intersected as `ε ↓ 0`, yielding an exact carrier subgradient.

Layer: Layer0 | Gap: Level 1 (bounded approximate supports to exact carrier subgradient)
Proof: form the closed subsets of the closed ball cut out by each positive
  epsilon support inequality, use directed compact intersection nonemptiness,
  then let epsilon tend to zero in the support inequality.
Source: Mathlib compact closed-ball, directed compact-intersection, and real
  inner-product continuity APIs
Used in: accelerated proximal-gradient KKT support recovery from bounded
  approximate support vectors
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem exists_carrierSubdifferential_of_bounded_approx_supports
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
    {X : Set E} (f : {x : E // x ∈ X} → ℝ) (z : {x : E // x ∈ X})
    (B : ℝ)
    (happrox :
      ∀ ε : ℝ, 0 < ε →
        ∃ p : E,
          ‖p‖ ≤ B ∧
            ∀ y : {x : E // x ∈ X},
              f z - ε + ⟪p, y.1 - z.1⟫_ℝ ≤ f y) :
    ∃ p : E, p ∈ carrierSubdifferential f z := by
  classical
  let C : {ε : ℝ // 0 < ε} → Set E :=
    fun ε =>
      {p | ‖p‖ ≤ B ∧
        ∀ y : {x : E // x ∈ X},
          f z - ε.1 + ⟪p, y.1 - z.1⟫_ℝ ≤ f y}
  have hC_nonempty : ∀ ε, (C ε).Nonempty := by
    intro ε
    rcases happrox ε.1 ε.2 with ⟨p, hpB, hp⟩
    exact ⟨p, hpB, hp⟩
  have hC_closed : ∀ ε, IsClosed (C ε) := by
    intro ε
    have hball : IsClosed {p : E | ‖p‖ ≤ B} :=
      isClosed_le continuous_norm continuous_const
    have hineq :
        IsClosed
          {p : E |
            ∀ y : {x : E // x ∈ X},
              f z - ε.1 + ⟪p, y.1 - z.1⟫_ℝ ≤ f y} := by
      rw [show
          {p : E |
            ∀ y : {x : E // x ∈ X},
              f z - ε.1 + ⟪p, y.1 - z.1⟫_ℝ ≤ f y} =
            ⋂ y : {x : E // x ∈ X},
              {p : E |
                f z - ε.1 + ⟪p, y.1 - z.1⟫_ℝ ≤ f y} by
        ext p
        simp]
      refine isClosed_iInter fun y => ?_
      exact isClosed_le (by fun_prop) continuous_const
    rw [show C ε =
        {p : E | ‖p‖ ≤ B} ∩
          {p : E |
            ∀ y : {x : E // x ∈ X},
              f z - ε.1 + ⟪p, y.1 - z.1⟫_ℝ ≤ f y} by
      ext p
      simp [C]]
    exact hball.inter hineq
  have hC_compact : ∀ ε, IsCompact (C ε) := by
    intro ε
    refine (isCompact_closedBall (0 : E) B).of_isClosed_subset (hC_closed ε) ?_
    intro p hp
    have hpB : ‖p‖ ≤ B := hp.1
    simpa [Metric.mem_closedBall, dist_eq_norm] using hpB
  have hC_directed : Directed (· ⊇ ·) C := by
    intro ε₁ ε₂
    refine ⟨⟨min ε₁.1 ε₂.1, lt_min ε₁.2 ε₂.2⟩, ?_, ?_⟩
    · intro p hp
      refine ⟨hp.1, ?_⟩
      intro y
      have hleft :
          f z - ε₁.1 + ⟪p, y.1 - z.1⟫_ℝ ≤
            f z - min ε₁.1 ε₂.1 + ⟪p, y.1 - z.1⟫_ℝ := by
        have hmin : min ε₁.1 ε₂.1 ≤ ε₁.1 := min_le_left _ _
        linarith
      exact hleft.trans (hp.2 y)
    · intro p hp
      refine ⟨hp.1, ?_⟩
      intro y
      have hleft :
          f z - ε₂.1 + ⟪p, y.1 - z.1⟫_ℝ ≤
            f z - min ε₁.1 ε₂.1 + ⟪p, y.1 - z.1⟫_ℝ := by
        have hmin : min ε₁.1 ε₂.1 ≤ ε₂.1 := min_le_right _ _
        linarith
      exact hleft.trans (hp.2 y)
  obtain ⟨p, hp_all⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      C hC_directed hC_nonempty hC_compact hC_closed
  refine ⟨p, ?_⟩
  rw [mem_carrierSubdifferential_iff]
  intro y
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  have hpε : p ∈ C ⟨ε, hε⟩ := by
    simpa using (Set.mem_iInter.mp hp_all) ⟨ε, hε⟩
  have hy := hpε.2 y
  linarith


-- Batch 7 promoted from Staging/exists_carrierSubdifferential_of_convex_tilted_lower_model.lean
-- Generalization plan (G0):
-- concept/name: exact carrier subgradient from a convex norm-tilted lower model; orig was theorem59_carrierSubgradient_nu_of_lipschitz_tilted_positive_minimizer, renamed away from theorem number, `nu`, and prox-minimizer setup vocabulary.
-- generality used: carrier `X : Set E`, objective `f : E -> Real`, point `z : {x // x in X}`, affine vector `A`, positive coefficient `c`, nonnegative tilt coefficient `beta`, `ConvexOn Real X f`, and a pointwise norm-tilted lower-model inequality; no measure, stochastic oracle, smoothness, or update assumptions are used.
-- portable call pattern: nonsmooth proximal-gradient, mirror-prox, and variance-reduced KKT proofs can call this after a prox/minimizer comparison yields a convex lower model tilted by a norm and affine residual; the carrier, objective, center, residual vector, scale, and tilt bound vary while the conclusion remains an actual carrier-subdifferential witness.
-- counterargument checked: not paper-local traceability and not a pure wrapper around a caller-side expression; it packages the reusable route from tilted convex lower model to approximate supports and then compact exactification. It is not a duplicate of either ingredient theorem, because this one exposes the direct final subdifferential API future proofs want.
-- coverage search: searched CATALOG/SOptLib/Staging for `carrierSubdifferential`, `bounded approximate support`, `tilted lower model`, and `convex support`; LeanSearch for "convex tilted lower model carrier subdifferential support vector" returned only generic convex APIs such as `ConvexOn.map_sum_le`/sublevel facts. Existing staged entries cover the two ingredients separately, but none states this composed final subgradient result.
-- minimal hypotheses: paper setup and finite Euclidean dimension are replaced by `[NormedAddCommGroup E] [InnerProductSpace Real E] [ProperSpace E]`; `0 < c`, `0 <= beta`, `ConvexOn Real X f`, and the tilted lower-model inequality are exactly the assumptions consumed by the two ingredient lemmas.

/-- A convex norm-tilted lower model exactifies to a carrier subgradient.

If a convex objective satisfies a lower-model inequality at `z` tilted by
`beta * K * ‖y - z‖` plus an affine term, then there is an actual carrier
subgradient at `z`. The proof first derives uniformly bounded approximate
support vectors, then sends the tolerance to zero by compactness.

Layer: Layer0 | Gap: Level 1 (convex tilted lower model to exact carrier subgradient)
Proof: apply the convex tilted lower-model theorem to get bounded approximate
  carrier supports, then apply compact exactification of bounded approximate
  supports to obtain exact carrier-subdifferential membership.
Source: Mathlib convex Jensen inequalities, finite halfspace separation,
  compact closed-ball intersections, and real Hilbert inner-product APIs
Used in: variance-reduced accelerated and composite proximal KKT recovery from
  norm-tilted lower models
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem exists_carrierSubdifferential_of_convex_tilted_lower_model
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
    {X : Set E} (f : E → ℝ) (z : {x : E // x ∈ X}) (A : E)
    {c beta : ℝ} (hc_pos : 0 < c) (hbeta_nonneg : 0 ≤ beta)
    (htilted :
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ y : {x : E // x ∈ X},
          c * (f z.1 - f y.1) ≤
            beta * K * ‖y.1 - z.1‖ + ⟪A, y.1 - z.1⟫_ℝ)
    (hconvex : ConvexOn ℝ X f) :
    ∃ p : E,
      p ∈ carrierSubdifferential
        (X := X) (fun x : {x : E // x ∈ X} => f x.1) z := by
  rcases
    bounded_approx_supports_of_convex_tilted_lower_model
      (E := E) (X := X) (f := f) z A hc_pos hbeta_nonneg htilted hconvex with
    ⟨B, _hB_nonneg, happrox⟩
  exact
    exists_carrierSubdifferential_of_bounded_approx_supports
      (E := E) (X := X) (f := fun x : {x : E // x ∈ X} => f x.1) z B happrox

-- Batch 7 promoted from Staging/neg_mem_carrierSubdifferential_of_isMinOn_affine_add.lean
-- Generalization plan (G0):
-- concept/name: affine-tilted minimizer certificate to carrier subgradient; orig was theorem59_carrierSubgradient_of_nu_support, renamed away from theorem number and `nu` setup vocabulary.
-- generality used: carrier `X : Set E`, real Hilbert space structure, subtype objective `f : {x // x in X} -> Real`, carrier point `z`, and affine vector `p`; no measure, convexity, smoothness, oracle, compactness, or update assumptions are used.
-- portable call pattern: proximal-gradient, mirror-descent, variance-reduced, and composite KKT proofs can call this after an affine optimality certificate for `u |-> <p,u> + f u` is obtained; the carrier, objective, minimizer, and affine vector change while the conclusion remains `-p in carrierSubdifferential f z`.
-- counterargument checked: not paper-local traceability and not a pure rename; the proof composes Mathlib's `IsMinOn` API with SOptLib's carrier-subdifferential API in the direction future KKT/subgradient calculus calls need. It is not covered by the existing support-to-Lipschitz or mean-oracle carrier-subgradient specialization lemmas.
-- coverage search: searched CATALOG/SOptLib/Staging for `carrierSubdifferential`, `IsMinOn`, `affine`, `support`, and `subgradient`; relevant hits were only `carrierSubdifferential`, `mem_carrierSubdifferential_iff`, `meanOracle_mem_carrierSubdifferential`, and the local paper wrappers. LeanSearch for "IsMinOn affine inner product plus function implies negative vector in subdifferential" returned `isMinOn_iff` and local-extremum derivative lemmas, with no subdifferential bridge.
-- minimal hypotheses: all already minimal; the minimizer certificate is stated directly on the feasible subtype with `Set.univ`, avoiding an ambient objective-extension hypothesis and avoiding finite-dimensionality.

/-- An affine-tilted carrier minimizer gives the negative tilt as a carrier subgradient.

If `z` minimizes `x |-> <p, x> + f x` over the feasible carrier subtype, then
the supporting inequality for `f` at `z` holds with support vector `-p`.

Layer: Layer0 | Gap: Level 0 (affine minimizer to carrier subgradient)
Proof: expand `IsMinOn` and `carrierSubdifferential`, then rearrange the affine
  inner-product term with bilinearity of the real inner product.
Source: Mathlib order argmin predicates and real Hilbert inner-product algebra
Used in: variance-reduced accelerated and composite proximal KKT recovery from
  affine optimality certificates
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem neg_mem_carrierSubdifferential_of_isMinOn_affine_add
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (f : {x : E // x ∈ X} → ℝ) (z : {x : E // x ∈ X})
    (p : E)
    (hmin : IsMinOn (fun x : {x : E // x ∈ X} => ⟪p, x.1⟫_ℝ + f x) Set.univ z) :
    (-p) ∈ carrierSubdifferential f z := by
  rw [mem_carrierSubdifferential_iff]
  rw [isMinOn_iff] at hmin
  intro y
  have hy :
      ⟪p, z.1⟫_ℝ + f z ≤ ⟪p, y.1⟫_ℝ + f y := by
    exact hmin y (Set.mem_univ y)
  have hinner :
      ⟪p, z.1⟫_ℝ =
        ⟪p, y.1⟫_ℝ + ⟪-p, y.1 - z.1⟫_ℝ := by
    rw [inner_neg_left, inner_sub_right]
    ring
  calc
    f z + ⟪-p, y.1 - z.1⟫_ℝ
        = (⟪p, z.1⟫_ℝ + f z) - ⟪p, y.1⟫_ℝ := by
          rw [hinner]
          ring
    _ ≤ (⟪p, y.1⟫_ℝ + f y) - ⟪p, y.1⟫_ℝ := by
          exact sub_le_sub_right hy ⟪p, y.1⟫_ℝ
    _ = f y := by
          ring

-- Batch 7 promoted from Staging/exists_isMinOn_affine_add_of_mem_carrierSubdifferential.lean
-- Generalization plan (G0):
-- concept/name: carrier subgradient to affine-tilted minimizer certificate; orig was theorem59_nu_support_of_carrierSubgradient, renamed away from theorem number, `nu`, and source support vocabulary.
-- generality used: carrier `X : Set E`, real Hilbert space structure, ambient objective `f : E -> Real` restricted through the carrier subtype, carrier point `z`, and support vector `p`; no measure, convexity, smoothness, oracle, compactness, or update assumptions are used.
-- portable call pattern: proximal-gradient, mirror-descent, variance-reduced, and composite KKT proofs can call this after deriving constrained subgradient membership for a nonsmooth/simple term; the feasible carrier, objective, point, and subgradient change while the conclusion stays an affine minimizer certificate with vector `-p`.
-- counterargument checked: not paper-local traceability because it is the reusable reverse bridge to the already staged affine-minimizer-to-subgradient theorem; not a pure wrapper because it converts SOptLib carrier-subdifferential API into Mathlib `IsMinOn` API over the ambient feasible set used by prox/support definitions.
-- coverage search: searched CATALOG/SOptLib/Staging for `carrierSubdifferential`, `IsMinOn`, `affine`, `support certificate`, and `subgradient`; relevant hits were `carrierSubdifferential`, `mem_carrierSubdifferential_iff`, `meanOracle_mem_carrierSubdifferential`, and the opposite-direction staged theorem `neg_mem_carrierSubdifferential_of_isMinOn_affine_add`. LeanSearch for "subgradient membership affine minimizer inner product IsMinOn" returned only generic `IsMinOn`/convex derivative APIs, with no carrier-subdifferential bridge.
-- minimal hypotheses: all already minimal; the objective is ambient only to state the resulting `IsMinOn` over `X`, while the hypothesis remains exactly carrier-subdifferential membership of its subtype restriction.

/-- Carrier-subdifferential membership gives an affine-tilted minimizer certificate.

If `p` supports the feasible-carrier restriction of `f` at `z`, then `z`
minimizes `u |-> <-p, u> + f u` over the ambient feasible set `X`.

Layer: Layer0 | Gap: Level 0 (carrier subgradient to affine minimizer)
Proof: expand `carrierSubdifferential` and `IsMinOn`, then rearrange the
  supporting inequality using bilinearity of the real inner product.
Source: Mathlib order argmin predicates and real Hilbert inner-product algebra
Used in: variance-reduced accelerated and composite proximal KKT conversion from
  constrained subgradients to affine support certificates
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem exists_isMinOn_affine_add_of_mem_carrierSubdifferential
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} (f : E → ℝ) (z : {x : E // x ∈ X}) (p : E)
    (hp : p ∈ carrierSubdifferential (X := X) (fun x : {x : E // x ∈ X} => f x.1) z) :
    ∃ q : E, IsMinOn (fun u : E => ⟪q, u⟫_ℝ + f u) X z.1 := by
  refine ⟨-p, ?_⟩
  rw [isMinOn_iff]
  intro y hy
  have hsupport :=
    (mem_carrierSubdifferential_iff.mp hp) (⟨y, hy⟩ : {x : E // x ∈ X})
  have hsupport' : f z.1 + ⟪p, y - z.1⟫_ℝ ≤ f y := by
    simpa using hsupport
  have hinner :
      ⟪-p, z.1⟫_ℝ =
        ⟪-p, y⟫_ℝ + ⟪p, y - z.1⟫_ℝ := by
    rw [inner_neg_left, inner_neg_left, inner_sub_right]
    ring
  calc
    ⟪-p, z.1⟫_ℝ + f z.1 =
        ⟪-p, y⟫_ℝ + ⟪p, y - z.1⟫_ℝ + f z.1 := by
          rw [hinner]
    _ = ⟪-p, y⟫_ℝ + (f z.1 + ⟪p, y - z.1⟫_ℝ) := by
          ring
    _ ≤ ⟪-p, y⟫_ℝ + f y := by
          have h := add_le_add_left hsupport' ⟪-p, y⟫_ℝ
          simpa [add_comm, add_left_comm, add_assoc] using h


end SOptLib

-- Generalization plan (G0):
-- concept/name: convexity of a carrier-totalized composite objective from a
--   convex simple term and a nonnegative multiple of a carrier-subgradient
--   supported regularizer; orig was objective_regularizer_totalize_convexOn.
-- generality used: real Hilbert-space carrier `{E}` with
--   `[NormedAddCommGroup E]` and `[InnerProductSpace ℝ E]`; no measure,
--   independence, integrability, smoothness, finite-dimensional, or oracle
--   assumptions are used. The simple term is supplied as `ConvexOn ℝ X
--   (SOptLib.totalizeOn X h)`, and the regularizer uses only pointwise
--   carrier-subdifferential membership for a selected support vector.
-- portable call pattern: composite stochastic-optimization proofs with a
--   feasible carrier can certify convexity of `h + μ • ν` before applying a
--   composite minimizer, Jensen, or prox inequality; the carrier, simple term,
--   regularizer, scalar multiplier, and subgradient selector vary while the
--   totalized composite convexity conclusion stays fixed.
-- counterargument checked: not paper-local traceability because the statement
--   packages a recurring convex-analysis composition step; not a pure wrapper
--   over Mathlib because Mathlib has `ConvexOn.add` and `ConvexOn.smul` but no
--   bridge deriving carrier-totalized convexity of `ν` from the selected
--   carrier-subdifferential support inequalities.
-- coverage search: checked catalog/source hits for `totalizeOn`,
--   `carrierSubdifferential`, `mem_carrierSubdifferential_iff`,
--   `ConvexOn.add`, `ConvexOn.smul`, and LeanSearch query "convex function
--   plus nonnegative multiple of function with subgradient support inequality
--   is convex"; coverage is partial. Existing APIs provide the ingredients,
--   but no Mathlib/SOptLib declaration covers this carrier-totalized composite
--   statement.
-- minimal hypotheses: reduced the original standing-assumption package to
--   exactly convexity of the totalized simple term, pointwise carrier support
--   for `ν`, and `0 ≤ μ`; all algorithm parameters and finite-dimensional
--   assumptions are unused.

/-- A convex carrier term plus a nonnegative multiple of a carrier-supported
regularizer has convex totalization on the carrier.

If `h` is convex after carrier totalization and every carrier point of `ν`
has the selected support vector `ν' x`, then the carrier totalization of
`h + μν` is convex for every nonnegative multiplier `μ`.

Layer: Layer0 | Gap: Level 1 (carrier-supported composite regularizer convexity)
Proof: use the support inequality for `ν` at the convex mixture point against
  both endpoints; the affine combination of the two support directions cancels,
  yielding Jensen convexity for `ν`, and nonnegative scaling combines it with
  the supplied convexity of `h`.
Source: Mathlib convex functions on sets, inner-product linearity, and SOptLib
  carrier subdifferential support inequalities
Used in: randomized primal-dual composite objective convexity before the primal
  optimality bridge and weighted Jensen step
Book citation: book/FOML/RandomPrimalDualGradient.json#/proofs/5.1/Lemma_5_1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem ConvexOn.totalizeOn_add_nonneg_mul_of_carrierSubdifferential
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} {h ν : {x : E // x ∈ X} → ℝ}
    {ν' : {x : E // x ∈ X} → E} {μ : ℝ}
    (hh : ConvexOn ℝ X (SOptLib.totalizeOn X h))
    (hν : ∀ x : {x : E // x ∈ X},
      ν' x ∈ SOptLib.carrierSubdifferential ν x)
    (hμ : 0 ≤ μ) :
    ConvexOn ℝ X (SOptLib.totalizeOn X (fun x => h x + μ * ν x)) := by
  classical
  refine ⟨hh.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hmix : a • x + b • y ∈ X := hh.1 hx hy ha hb hab
  let z : {x : E // x ∈ X} := ⟨a • x + b • y, hmix⟩
  have hhineq := hh.2 hx hy ha hb hab
  have hνSupportX :=
    (SOptLib.mem_carrierSubdifferential_iff.mp (hν z)) ⟨x, hx⟩
  have hνSupportY :=
    (SOptLib.mem_carrierSubdifferential_iff.mp (hν z)) ⟨y, hy⟩
  have hdir_zero :
      a * ⟪ν' z, x - z.1⟫_ℝ + b * ⟪ν' z, y - z.1⟫_ℝ = 0 := by
    have hvec : a • (x - z.1) + b • (y - z.1) = (0 : E) := by
      calc
        a • (x - z.1) + b • (y - z.1)
            = a • x + b • y - (a + b) • z.1 := by
              rw [smul_sub, smul_sub, add_smul]
              abel
        _ = 0 := by
              rw [hab]
              simp [z]
    calc
      a * ⟪ν' z, x - z.1⟫_ℝ + b * ⟪ν' z, y - z.1⟫_ℝ
          = ⟪ν' z, a • (x - z.1) + b • (y - z.1)⟫_ℝ := by
            simp [inner_add_right, inner_smul_right]
      _ = 0 := by simp [hvec]
  have hνIneq : ν z ≤ a * ν ⟨x, hx⟩ + b * ν ⟨y, hy⟩ := by
    have hx' : ν z + ⟪ν' z, x - z.1⟫_ℝ ≤ ν ⟨x, hx⟩ := by
      simpa using hνSupportX
    have hy' : ν z + ⟪ν' z, y - z.1⟫_ℝ ≤ ν ⟨y, hy⟩ := by
      simpa using hνSupportY
    have hxmul := mul_le_mul_of_nonneg_left hx' ha
    have hymul := mul_le_mul_of_nonneg_left hy' hb
    have hsum_le :
        a * (ν z + ⟪ν' z, x - z.1⟫_ℝ) +
            b * (ν z + ⟪ν' z, y - z.1⟫_ℝ) ≤
          a * ν ⟨x, hx⟩ + b * ν ⟨y, hy⟩ :=
      add_le_add hxmul hymul
    have hleft :
        a * (ν z + ⟪ν' z, x - z.1⟫_ℝ) +
            b * (ν z + ⟪ν' z, y - z.1⟫_ℝ) =
          ν z := by
      calc
        a * (ν z + ⟪ν' z, x - z.1⟫_ℝ) +
            b * (ν z + ⟪ν' z, y - z.1⟫_ℝ)
            = (a + b) * ν z +
                (a * ⟪ν' z, x - z.1⟫_ℝ +
                  b * ⟪ν' z, y - z.1⟫_ℝ) := by
              ring
        _ = ν z := by
              rw [hdir_zero, hab]
              ring
    nlinarith
  have hμν :
      μ * ν z ≤ μ * (a * ν ⟨x, hx⟩ + b * ν ⟨y, hy⟩) :=
    mul_le_mul_of_nonneg_left hνIneq hμ
  simp [SOptLib.totalizeOn_of_mem, hmix, hx, hy, smul_eq_mul] at hhineq ⊢
  nlinarith

/-- Root-namespace compatibility wrapper for carrier-subdifferential
membership transport.

Mirrors `SOptLib.meanOracle_mem_carrierSubdifferential` at the root
namespace so legacy callsites that look up the lemma without the `SOptLib`
prefix still resolve.

Layer: Layer0 | Gap: Level 0 (root-namespace alias for mean-oracle
  carrier-subgradient specialization)
Proof: direct delegation to `SOptLib.meanOracle_mem_carrierSubdifferential`.
Source: Mathlib subtype and set membership APIs
Used in: stochastic mirror descent unbiased oracle carrier-subgradient check
  (root-namespace callsites)
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem meanOracle_mem_carrierSubdifferential
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (f : {x : E // x ∈ X} → ℝ) (g : {x : E // x ∈ X} → E)
    (h_meanOracle_subgradient : ∀ x : {x : E // x ∈ X},
      g x ∈ SOptLib.carrierSubdifferential f x) (x : {x : E // x ∈ X}) :
    g x ∈ SOptLib.carrierSubdifferential f x := by
  exact SOptLib.meanOracle_mem_carrierSubdifferential X f g h_meanOracle_subgradient x

/-- Two-sided supporting inequalities plus an absolute pairing bound make a
real objective measurable.

If `g x` supports the real objective `f` at every carrier point and each
support pairing against a displacement is bounded by `C * dist x y`, then `f`
is Lipschitz, hence measurable.

Layer: Layer0 | Gap: Level 1 (supporting inequality to measurable objective)
Proof: rearrange the two support inequalities into opposite one-sided bounds
  for `f x - f y`, control both by the absolute pairing estimate, package the
  resulting norm-difference estimate as a Lipschitz map, then use Lipschitz
  measurability.
Source: Mathlib real inner-product support inequalities, ordered real absolute
  values, and metric Lipschitz measurability APIs
Used in: stochastic block mirror descent feasible-objective measurability from
  block-dual bounded mean subgradients
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem measurable_of_supporting_inequality_and_abs_inner_bound
    {P E : Type*} [PseudoMetricSpace P] [MeasurableSpace P] [OpensMeasurableSpace P]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : P → ℝ) (g : P → E) (eval : P → E) (C : ℝ)
    (hsupport : ∀ x y : P, f x + ⟪g x, eval y - eval x⟫_ℝ ≤ f y)
    (hinner : ∀ x y : P, |⟪g x, eval y - eval x⟫_ℝ| ≤ C * dist x y) :
    Measurable f := by
  have hdiff :
      ∀ x y : P, ‖f x - f y‖ ≤ C * dist x y := by
    intro x y
    have hxy_support := hsupport x y
    have hyx_support := hsupport y x
    have hxy :
        f x - f y ≤ C * dist x y := by
      have hgap :
          f x - f y ≤ -⟪g x, eval y - eval x⟫_ℝ := by
        linarith
      exact hgap.trans ((neg_le_abs _).trans (hinner x y))
    have hyx :
        f y - f x ≤ C * dist x y := by
      have hgap :
          f y - f x ≤ -⟪g y, eval x - eval y⟫_ℝ := by
        linarith
      exact hgap.trans ((neg_le_abs _).trans (by simpa [dist_comm] using hinner y x))
    have hneg : -(C * dist x y) ≤ f x - f y := by
      linarith
    simpa [Real.norm_eq_abs] using abs_le.mpr ⟨hneg, hxy⟩
  exact (lipschitzWith_of_norm_sub_le_mul f C hdiff).measurable

/-- Block-dual bounds control the absolute ambient pairing by carrier distance.

If an ambient vector field is reconstructed from finitely many lifted block
components, each block component satisfies a dual-support bound, and each block
primal seminorm is controlled by the ambient norm after a coordinate map, then
the ambient inner product against any carrier displacement is Lipschitz in the
carrier distance.

Layer: Layer0 | Gap: Level 1 (finite block-dual displacement support bound)
Proof: expand the ambient pairing through the finite block reconstruction,
apply the triangle inequality over the finite sum, bound each block term by
the dual-support and coordinate operator-norm estimates, then compare the
ambient displacement norm to the carrier distance.
Source: Mathlib finite sums, real Hilbert inner products, seminorms, and
  continuous-linear-map operator norm APIs
Used in: stochastic block mirror descent feasible-objective measurability from
  block-dual bounded mean subgradients
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem abs_inner_le_dist_of_block_dual_bounds
    {I P E : Type*} [Fintype I] [PseudoMetricSpace P]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {B : I → Type*} [∀ i, NormedAddCommGroup (B i)]
    [∀ i, InnerProductSpace ℝ (B i)]
    (eval : P → E) (coord : ∀ i, E →L[ℝ] B i) (lift : ∀ i, B i → E)
    (g : P → E) (gBlock : ∀ i, P → B i)
    (p : ∀ i, Seminorm ℝ (B i)) (dual : I → P → ℝ) (M : I → ℝ)
    (hM_nonneg : ∀ i, 0 ≤ M i)
    (hK_exists : ∀ i, ∃ K : ℝ, 0 ≤ K ∧ ∀ d : B i, p i d ≤ K * ‖d‖)
    (hrepr : ∀ x, g x = Finset.sum Finset.univ (fun i => lift i (gBlock i x)))
    (hpair : ∀ i ζ d, ⟪lift i ζ, d⟫_ℝ = ⟪ζ, coord i d⟫_ℝ)
    (hsupport : ∀ i x d, |⟪gBlock i x, coord i d⟫_ℝ| ≤
      dual i x * p i (coord i d))
    (hdual_le : ∀ i x, dual i x ≤ M i)
    (hdist : ∀ x y, ‖eval y - eval x‖ ≤ dist x y) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x y : P, |⟪g x, eval y - eval x⟫_ℝ| ≤ C * dist x y := by
  classical
  choose K hK_nonneg hK_bound using hK_exists
  let C : ℝ := Finset.sum Finset.univ (fun i => M i * K i * ‖coord i‖)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    refine Finset.sum_nonneg ?_
    intro i _hi
    exact mul_nonneg (mul_nonneg (hM_nonneg i) (hK_nonneg i)) (norm_nonneg _)
  refine ⟨C, hC_nonneg, ?_⟩
  intro x y
  let d : E := eval y - eval x
  have hsum :
      |⟪g x, d⟫_ℝ| ≤
        Finset.sum Finset.univ (fun i => (M i * K i * ‖coord i‖) * ‖d‖) := by
    calc
      |⟪g x, d⟫_ℝ|
          = |Finset.sum Finset.univ (fun i => ⟪lift i (gBlock i x), d⟫_ℝ)| := by
              rw [hrepr x, sum_inner]
      _ ≤ Finset.sum Finset.univ (fun i => |⟪lift i (gBlock i x), d⟫_ℝ|) := by
              simpa using
                (Finset.abs_sum_le_sum_abs
                  (fun i => ⟪lift i (gBlock i x), d⟫_ℝ) Finset.univ)
      _ ≤ Finset.sum Finset.univ (fun i => (M i * K i * ‖coord i‖) * ‖d‖) := by
              refine Finset.sum_le_sum ?_
              intro i _hi
              have hcoord : ‖coord i d‖ ≤ ‖coord i‖ * ‖d‖ :=
                (coord i).le_opNorm d
              have hprimal :
                  p i (coord i d) ≤ (K i * ‖coord i‖) * ‖d‖ := by
                calc
                  p i (coord i d) ≤ K i * ‖coord i d‖ := hK_bound i (coord i d)
                  _ ≤ K i * (‖coord i‖ * ‖d‖) :=
                    mul_le_mul_of_nonneg_left hcoord (hK_nonneg i)
                  _ = (K i * ‖coord i‖) * ‖d‖ := by ring
              have hdual_mul :
                  dual i x * p i (coord i d) ≤ M i * p i (coord i d) :=
                mul_le_mul_of_nonneg_right (hdual_le i x) (apply_nonneg (p i) (coord i d))
              have hprimal_mul :
                  M i * p i (coord i d) ≤
                    M i * ((K i * ‖coord i‖) * ‖d‖) :=
                mul_le_mul_of_nonneg_left hprimal (hM_nonneg i)
              calc
                |⟪lift i (gBlock i x), d⟫_ℝ|
                    = |⟪gBlock i x, coord i d⟫_ℝ| := by rw [hpair]
                _ ≤ dual i x * p i (coord i d) := hsupport i x d
                _ ≤ M i * p i (coord i d) := hdual_mul
                _ ≤ M i * ((K i * ‖coord i‖) * ‖d‖) := hprimal_mul
                _ = (M i * K i * ‖coord i‖) * ‖d‖ := by ring
  have hsum_const :
      Finset.sum Finset.univ (fun i => (M i * K i * ‖coord i‖) * ‖d‖) =
        (Finset.sum Finset.univ (fun i => M i * K i * ‖coord i‖)) * ‖d‖ := by
    simp [Finset.sum_mul]
  have hCx_nonneg : 0 ≤ Finset.sum Finset.univ (fun i => M i * K i * ‖coord i‖) := by
    refine Finset.sum_nonneg ?_
    intro i _hi
    exact mul_nonneg (mul_nonneg (hM_nonneg i) (hK_nonneg i)) (norm_nonneg _)
  calc
    |⟪g x, eval y - eval x⟫_ℝ| = |⟪g x, d⟫_ℝ| := by rfl
    _ ≤ Finset.sum Finset.univ (fun i => (M i * K i * ‖coord i‖) * ‖d‖) := hsum
    _ = (Finset.sum Finset.univ (fun i => M i * K i * ‖coord i‖)) * ‖d‖ := hsum_const
    _ ≤ (Finset.sum Finset.univ (fun i => M i * K i * ‖coord i‖)) * dist x y :=
      mul_le_mul_of_nonneg_left (hdist x y) hCx_nonneg
    _ ≤ C * dist x y := by
      have hleC :
          Finset.sum Finset.univ (fun i => M i * K i * ‖coord i‖) ≤ C := by
        rfl
      exact mul_le_mul_of_nonneg_right hleC (dist_nonneg)

/-- A block-decomposed vector has its absolute ambient pairing bounded by
the sum of block dual bounds times block radii.

If an ambient vector is reconstructed from finitely many lifted block
components, the lifts pair with ambient displacements through block coordinates,
and each block pairing is controlled by a dual bound and a radius, then the
ambient pairing is controlled by the finite sum of the majorizing products.

Layer: Layer0 | Gap: Level 1 (finite block-dual radius inner-product bound)
Proof: expand the ambient pairing through the finite block reconstruction,
apply the triangle inequality over the finite sum, transport each summand to
the block pairing, and use monotonicity of multiplication with nonnegative
block radii and dual majorants.
Source: Mathlib finite sums, real Hilbert inner products, absolute-value order,
  and ordered-ring product inequalities
Used in: stochastic block mirror descent deterministic mean-oracle displacement
  control before scalar oracle-noise domination
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem abs_inner_block_sum_le_sum_dual_bound_mul_radius
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {B : ι → Type*} [∀ i, NormedAddCommGroup (B i)]
    [∀ i, InnerProductSpace ℝ (B i)]
    (lift : ∀ i, B i → E) (coord : ∀ i, E → B i)
    (g : E) (gBlock : ∀ i, B i) (d : E)
    (dual radius M R : ι → ℝ)
    (hrepr : g = Finset.sum Finset.univ (fun i => lift i (gBlock i)))
    (hpair : ∀ i (ζ : B i) (v : E), ⟪lift i ζ, v⟫_ℝ = ⟪ζ, coord i v⟫_ℝ)
    (hsupport : ∀ i, |⟪gBlock i, coord i d⟫_ℝ| ≤ dual i * radius i)
    (hdual_le : ∀ i, dual i ≤ M i)
    (hradius_nonneg : ∀ i, 0 ≤ radius i)
    (hradius_le : ∀ i, radius i ≤ R i)
    (hM_nonneg : ∀ i, 0 ≤ M i) :
    |⟪g, d⟫_ℝ| ≤ Finset.sum Finset.univ (fun i => M i * R i) := by
  calc
    |⟪g, d⟫_ℝ|
        = |Finset.sum Finset.univ (fun i => ⟪lift i (gBlock i), d⟫_ℝ)| := by
            rw [hrepr, sum_inner]
    _ ≤ Finset.sum Finset.univ (fun i => |⟪lift i (gBlock i), d⟫_ℝ|) := by
            simpa using
              (Finset.abs_sum_le_sum_abs
                (fun i => ⟪lift i (gBlock i), d⟫_ℝ) Finset.univ)
    _ ≤ Finset.sum Finset.univ (fun i => M i * R i) := by
            refine Finset.sum_le_sum ?_
            intro i _hi
            have hmajor : dual i * radius i ≤ M i * R i :=
              mul_le_mul (hdual_le i) (hradius_le i) (hradius_nonneg i) (hM_nonneg i)
            calc
              |⟪lift i (gBlock i), d⟫_ℝ| = |⟪gBlock i, coord i d⟫_ℝ| := by
                rw [hpair]
              _ ≤ dual i * radius i := hsupport i
              _ ≤ M i * R i := hmajor
