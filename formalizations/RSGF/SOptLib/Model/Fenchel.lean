import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import SOptLib.Model.Carrier
import SOptLib.Model.Subdifferential
import SOptLib.Glue.Calculus

open scoped InnerProductSpace

namespace SOptLib

/-- The finite-value domain of the Fenchel conjugate of a scaled objective.

For a real inner-product space, `fenchelConjugateDomain c f` consists of the
dual vectors `y` for which the support family `x ↦ ⟪x, y⟫ - c * f x` is
bounded above, so its real supremum can be used as a carrier-valued conjugate.

Layer: Model | Concept: Fenchel
Proof: (definitional construction; bounded-above support range for the scaled
  Fenchel conjugate)
Source: convex analysis Fenchel conjugates and Mathlib order boundedness for
  real suprema
Used in: random primal-dual gradient component dual carrier for scaled
  finite-sum objectives
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
noncomputable def fenchelConjugateDomain
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (scale : ℝ) (f : E → ℝ) : Set E :=
  {y : E | BddAbove (Set.range fun x : E => ⟪x, y⟫_ℝ - scale * f x)}

/-- Defining equation for `fenchelConjugateDomain`.

Layer: Model | Gap: Level 0 (Fenchel conjugate domain unfolding)
Proof: by rfl after unfolding `fenchelConjugateDomain`.
Source: convex analysis Fenchel conjugates and Mathlib order boundedness for
  real suprema
Used in: random primal-dual gradient component dual carrier for scaled
  finite-sum objectives
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
@[simp] theorem fenchelConjugateDomain_def
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (scale : ℝ) (f : E → ℝ) :
    fenchelConjugateDomain scale f =
      {y : E | BddAbove (Set.range fun x : E => ⟪x, y⟫_ℝ - scale * f x)} := by
  rfl

/-- Convex-combination closure of the finite-value Fenchel-conjugate domain.

Layer: Model | Gap: Level 1 (Fenchel conjugate domain convex-combination API)
Proof: combine bounded-above witnesses for the two support families using the
  nonnegative coefficients, then rewrite the mixed support value by bilinearity
  of the inner product and the normalized-weight identity.
Source: convex analysis Fenchel conjugates and Mathlib order boundedness for
  real suprema
Used in: random primal-dual gradient component dual carrier convexity
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem fenchelConjugateDomain_mix_mem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (scale : ℝ) (f : E → ℝ) {y₁ y₂ : E} {a b : ℝ}
    (hy₁ : y₁ ∈ fenchelConjugateDomain scale f)
    (hy₂ : y₂ ∈ fenchelConjugateDomain scale f)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • y₁ + b • y₂ ∈ fenchelConjugateDomain scale f := by
  classical
  change BddAbove (Set.range fun x : E => ⟪x, y₁⟫_ℝ - scale * f x) at hy₁
  change BddAbove (Set.range fun x : E => ⟪x, y₂⟫_ℝ - scale * f x) at hy₂
  change BddAbove
    (Set.range fun x : E => ⟪x, a • y₁ + b • y₂⟫_ℝ - scale * f x)
  rcases hy₁ with ⟨M₁, hM₁⟩
  rcases hy₂ with ⟨M₂, hM₂⟩
  refine ⟨a * M₁ + b * M₂, ?_⟩
  rintro r ⟨x, rfl⟩
  let c : ℝ := scale * f x
  have h₁ : ⟪x, y₁⟫_ℝ - c ≤ M₁ := by
    simpa [c] using hM₁ ⟨x, rfl⟩
  have h₂ : ⟪x, y₂⟫_ℝ - c ≤ M₂ := by
    simpa [c] using hM₂ ⟨x, rfl⟩
  have hcomb :
      a * (⟪x, y₁⟫_ℝ - c) + b * (⟪x, y₂⟫_ℝ - c) ≤
        a * M₁ + b * M₂ := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left h₁ ha)
      (mul_le_mul_of_nonneg_left h₂ hb)
  have hrewrite :
      ⟪x, a • y₁ + b • y₂⟫_ℝ - c =
        a * (⟪x, y₁⟫_ℝ - c) + b * (⟪x, y₂⟫_ℝ - c) := by
    calc
      ⟪x, a • y₁ + b • y₂⟫_ℝ - c =
          a * ⟪x, y₁⟫_ℝ + b * ⟪x, y₂⟫_ℝ - c := by
        simp [inner_add_right, inner_smul_right]
      _ = a * ⟪x, y₁⟫_ℝ + b * ⟪x, y₂⟫_ℝ - (a + b) * c := by
        rw [hab]
        ring
      _ = a * (⟪x, y₁⟫_ℝ - c) + b * (⟪x, y₂⟫_ℝ - c) := by
        ring
  calc
    ⟪x, a • y₁ + b • y₂⟫_ℝ - scale * f x
        = ⟪x, a • y₁ + b • y₂⟫_ℝ - c := by rfl
    _ = a * (⟪x, y₁⟫_ℝ - c) + b * (⟪x, y₂⟫_ℝ - c) := hrewrite
    _ ≤ a * M₁ + b * M₂ := hcomb

/-- The finite-value Fenchel-conjugate domain is convex. -/
theorem convex_fenchelConjugateDomain
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (scale : ℝ) (f : E → ℝ) :
    Convex ℝ (fenchelConjugateDomain scale f) := by
  rw [convex_iff_add_mem]
  intro y₁ hy₁ y₂ hy₂ a b ha hb hab
  exact fenchelConjugateDomain_mix_mem scale f hy₁ hy₂ ha hb hab

/-- The real-valued Fenchel conjugate of a scaled objective on its finite-value carrier.

The carrier packages exactly the `BddAbove` proof for the range
`x ↦ ⟪x, y⟫ - c * f x`, so the definition remains a total real-valued object
without adding paper-specific component or dual-space data.

Layer: Model | Concept: Fenchel
Proof: (definitional construction; carrier-restricted supremum of the affine
  minorant family)
Source: convex analysis Fenchel conjugates and Mathlib real `sSup` API
Used in: random primal-dual gradient component conjugate on the finite dual
  carrier
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
noncomputable def fenchelConjugateOnCarrier
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : ℝ) (f : E → ℝ)
    (y : {y : E // BddAbove (Set.range fun x : E => ⟪x, y⟫_ℝ - c * f x)}) :
    ℝ :=
  sSup (Set.range fun x : E => ⟪x, y.1⟫_ℝ - c * f x)

/-- Defining equation for `fenchelConjugateOnCarrier`.

Layer: Model | Gap: Level 0 (Fenchel carrier supremum unfolding)
Proof: by rfl after unfolding `fenchelConjugateOnCarrier`.
Source: convex analysis Fenchel conjugates and Mathlib real `sSup` API
Used in: random primal-dual gradient component conjugate on the finite dual
  carrier
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
@[simp] theorem fenchelConjugateOnCarrier_def
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : ℝ) (f : E → ℝ)
    (y : {y : E // BddAbove (Set.range fun x : E => ⟪x, y⟫_ℝ - c * f x)}) :
    fenchelConjugateOnCarrier c f y =
      sSup (Set.range fun x : E => ⟪x, y.1⟫_ℝ - c * f x) := by
  rfl

/-- Evaluating the supremum family gives a lower bound on the carrier conjugate.

Layer: Model | Gap: Level 1 (Fenchel carrier evaluation lower bound)
Proof: unfold the carrier-restricted conjugate and apply `le_csSup` using the
  bounded-above certificate stored in the carrier.
Source: convex analysis Fenchel conjugates and Mathlib conditionally complete
  lattice supremum APIs for real ranges
Used in: random primal-dual gradient Fenchel minorant and conjugate
  subgradient verification
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem le_fenchelConjugateOnCarrier
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : ℝ) (f : E → ℝ)
    (y : {y : E // BddAbove (Set.range fun x : E => ⟪x, y⟫_ℝ - c * f x)})
    (x : E) :
    ⟪x, y.1⟫_ℝ - c * f x ≤ fenchelConjugateOnCarrier c f y := by
  exact le_csSup y.2 ⟨x, rfl⟩

/-- The carrier-restricted Fenchel conjugate is convex along a binary mixture.

For a scaled objective `scale * f`, evaluating the real-valued Fenchel conjugate
at a convex combination of two finite-domain dual vectors is bounded by the
same convex combination of the endpoint conjugate values.

Layer: Model | Gap: Level 1 (Fenchel conjugate binary convexity on finite-value carrier)
Proof: bound every support value at the mixed dual point by the corresponding
  weighted endpoint suprema, using the carrier evaluation bound and the affine
  inner-product offset rewrite; then apply `csSup_le`.
Source: convex analysis Fenchel conjugates, support-function convexity, and
  Mathlib real supremum APIs
Used in: random primal-dual gradient and finite-sum saddle dual averaging steps
  where a mixed dual coordinate is passed through a component conjugate
Book citation: book/FOML/RandomPrimalDualGradient.json#/setup/dual_conjugate_definition
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem fenchelConjugate_mix_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (scale : ℝ) (f : E → ℝ)
    (y₁ y₂ : {y : E // y ∈ fenchelConjugateDomain scale f}) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    fenchelConjugateOnCarrier scale f
        ⟨a • y₁.1 + b • y₂.1,
          fenchelConjugateDomain_mix_mem (scale := scale) (f := f)
            y₁.2 y₂.2 ha hb hab⟩ ≤
      a * fenchelConjugateOnCarrier scale f y₁ +
        b * fenchelConjugateOnCarrier scale f y₂ := by
  classical
  unfold fenchelConjugateOnCarrier
  refine csSup_le (Set.range_nonempty _) ?_
  rintro r ⟨x, rfl⟩
  let c : ℝ := scale * f x
  have h₁ :
      ⟪x, y₁.1⟫_ℝ - c ≤
        sSup (Set.range fun x : E => ⟪x, y₁.1⟫_ℝ - scale * f x) := by
    simpa [c, fenchelConjugateOnCarrier] using
      le_fenchelConjugateOnCarrier scale f y₁ x
  have h₂ :
      ⟪x, y₂.1⟫_ℝ - c ≤
        sSup (Set.range fun x : E => ⟪x, y₂.1⟫_ℝ - scale * f x) := by
    simpa [c, fenchelConjugateOnCarrier] using
      le_fenchelConjugateOnCarrier scale f y₂ x
  have hcomb :
      a * (⟪x, y₁.1⟫_ℝ - c) + b * (⟪x, y₂.1⟫_ℝ - c) ≤
        a * sSup (Set.range fun x : E => ⟪x, y₁.1⟫_ℝ - scale * f x) +
          b * sSup (Set.range fun x : E => ⟪x, y₂.1⟫_ℝ - scale * f x) := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left h₁ ha)
      (mul_le_mul_of_nonneg_left h₂ hb)
  have hrewrite :
      ⟪x, a • y₁.1 + b • y₂.1⟫_ℝ - c =
        a * (⟪x, y₁.1⟫_ℝ - c) + b * (⟪x, y₂.1⟫_ℝ - c) := by
    calc
      ⟪x, a • y₁.1 + b • y₂.1⟫_ℝ - c =
          a * ⟪x, y₁.1⟫_ℝ + b * ⟪x, y₂.1⟫_ℝ - c := by
        simp [inner_add_right, inner_smul_right]
      _ = a * ⟪x, y₁.1⟫_ℝ + b * ⟪x, y₂.1⟫_ℝ - (a + b) * c := by
        rw [hab]
        ring
      _ = a * (⟪x, y₁.1⟫_ℝ - c) + b * (⟪x, y₂.1⟫_ℝ - c) := by
        ring
  calc
    ⟪x, a • y₁.1 + b • y₂.1⟫_ℝ - scale * f x =
        ⟪x, a • y₁.1 + b • y₂.1⟫_ℝ - c := by
      rfl
    _ = a * (⟪x, y₁.1⟫_ℝ - c) + b * (⟪x, y₂.1⟫_ℝ - c) := hrewrite
    _ ≤ a * sSup (Set.range fun x : E => ⟪x, y₁.1⟫_ℝ - scale * f x) +
        b * sSup (Set.range fun x : E => ⟪x, y₂.1⟫_ℝ - scale * f x) := hcomb

/-- A point supporting `f` computes the scaled Fenchel-conjugate supremum.

If `g` is a supporting gradient or subgradient for `f` at `x`, then for every
nonnegative scale `c`, the supremum of `z ↦ ⟪z, c • g⟫ - c * f z` is attained
at `x` and has value `⟪x, c • g⟫ - c * f x`.

Layer: Model | Gap: Level 1 (scaled Fenchel conjugate support value)
Proof: the support inequality gives a pointwise upper bound on every element of
  the range; `le_csSup` gives the reverse inequality from evaluating at `x`.
Source: convex analysis Fenchel conjugates and Mathlib conditionally complete
  lattice supremum APIs for real ranges
Used in: random primal-dual gradient component conjugate value at the scaled
  component-gradient dual witness
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem fenchel_conjugate_smul_supporting_gradient_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (x g : E) {c : ℝ} (hc : 0 ≤ c)
    (hsupport : ∀ z : E, f x + ⟪g, z - x⟫_ℝ ≤ f z) :
    sSup (Set.range fun z : E => ⟪z, c • g⟫_ℝ - c * f z) =
      ⟪x, c • g⟫_ℝ - c * f x := by
  classical
  have hUpperPoint : ∀ z : E,
      ⟪z, c • g⟫_ℝ - c * f z ≤ ⟪x, c • g⟫_ℝ - c * f x := by
    intro z
    have hsupp_z := hsupport z
    have hsupp_bound : ⟪z, g⟫_ℝ - f z ≤ ⟪x, g⟫_ℝ - f x := by
      rw [inner_sub_right, real_inner_comm z g, real_inner_comm x g] at hsupp_z
      linarith
    have hmul := mul_le_mul_of_nonneg_left hsupp_bound hc
    calc
      ⟪z, c • g⟫_ℝ - c * f z = c * (⟪z, g⟫_ℝ - f z) := by
        simp [inner_smul_right]
        ring
      _ ≤ c * (⟪x, g⟫_ℝ - f x) := hmul
      _ = ⟪x, c • g⟫_ℝ - c * f x := by
        simp [inner_smul_right]
        ring
  have hBddAbove : BddAbove (Set.range fun z : E => ⟪z, c • g⟫_ℝ - c * f z) := by
    refine ⟨⟪x, c • g⟫_ℝ - c * f x, ?_⟩
    rintro r ⟨z, rfl⟩
    exact hUpperPoint z
  have hUpper :
      sSup (Set.range fun z : E => ⟪z, c • g⟫_ℝ - c * f z) ≤
        ⟪x, c • g⟫_ℝ - c * f x := by
    refine csSup_le (Set.range_nonempty _) ?_
    rintro r ⟨z, rfl⟩
    exact hUpperPoint z
  have hLower :
      ⟪x, c • g⟫_ℝ - c * f x ≤
        sSup (Set.range fun z : E => ⟪z, c • g⟫_ℝ - c * f z) := by
    exact le_csSup hBddAbove ⟨x, rfl⟩
  exact le_antisymm hUpper hLower

/-- The carrier-restricted Fenchel conjugate is convex after totalization to its finite domain.

For a scaled objective `scale * f`, the finite-value domain of the Fenchel
conjugate is convex, and the real-valued carrier conjugate satisfies the
binary convexity inequality needed for the totalized ambient function.

Layer: Model | Gap: Level 1 (Fenchel conjugate totalized convexity on finite-value domain)
Proof: combine convexity of the finite-value Fenchel domain with the binary
  carrier-conjugate convexity inequality, rewriting totalized values at domain
  points by `SOptLib.totalizeOn_of_mem`.
Source: convex analysis Fenchel conjugates, Mathlib `ConvexOn` APIs, and
  carrier totalization over subtype domains
Used in: random primal-dual gradient and finite-sum saddle Jensen steps for
  weighted dual outputs passed through component Fenchel conjugates
Book citation: book/FOML/RandomPrimalDualGradient.json#/setup/dual_conjugate_definition
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem fenchelConjugate_totalize_convexOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (scale : ℝ) (f : E → ℝ) :
    ConvexOn ℝ (fenchelConjugateDomain scale f)
      (SOptLib.totalizeOn (fenchelConjugateDomain scale f)
        (fun y : {y : E // y ∈ fenchelConjugateDomain scale f} =>
          fenchelConjugateOnCarrier scale f y)) := by
  classical
  refine ⟨convex_fenchelConjugateDomain scale f, ?_⟩
  intro y₁ hy₁ y₂ hy₂ a b ha hb hab
  have hmix : a • y₁ + b • y₂ ∈ fenchelConjugateDomain scale f :=
    fenchelConjugateDomain_mix_mem scale f hy₁ hy₂ ha hb hab
  have hle :=
    fenchelConjugate_mix_le (scale := scale) (f := f)
      ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩ ha hb hab
  let ψ : {y : E // y ∈ fenchelConjugateDomain scale f} → ℝ :=
    fun y => fenchelConjugateOnCarrier scale f y
  change
    SOptLib.totalizeOn (fenchelConjugateDomain scale f) ψ (a • y₁ + b • y₂) ≤
      a • SOptLib.totalizeOn (fenchelConjugateDomain scale f) ψ y₁ +
        b • SOptLib.totalizeOn (fenchelConjugateDomain scale f) ψ y₂
  calc
    SOptLib.totalizeOn (fenchelConjugateDomain scale f) ψ (a • y₁ + b • y₂) =
        fenchelConjugateOnCarrier scale f ⟨a • y₁ + b • y₂, hmix⟩ := by
      exact SOptLib.totalizeOn_of_mem (fenchelConjugateDomain scale f) ψ hmix
    _ ≤
        a * fenchelConjugateOnCarrier scale f ⟨y₁, hy₁⟩ +
          b * fenchelConjugateOnCarrier scale f ⟨y₂, hy₂⟩ := hle
    _ =
        a • SOptLib.totalizeOn (fenchelConjugateDomain scale f) ψ y₁ +
          b • SOptLib.totalizeOn (fenchelConjugateDomain scale f) ψ y₂ := by
      rw [SOptLib.totalizeOn_of_mem (fenchelConjugateDomain scale f) ψ hy₁,
        SOptLib.totalizeOn_of_mem (fenchelConjugateDomain scale f) ψ hy₂]
      simp [ψ, smul_eq_mul]

/-- The finite-value Fenchel-conjugate domain is convex.

For a scaled objective `scale * f`, the set of dual vectors whose support
family `x ↦ ⟪x, y⟫ - scale * f x` is bounded above is closed under normalized
binary convex combinations, hence is a convex set.

Layer: Model | Gap: Level 1 (Fenchel conjugate effective-domain convexity)
Proof: unfold `Convex` through `convex_iff_add_mem` and discharge the binary
  convex-combination goal with `fenchelConjugateDomain_mix_mem`.
Source: convex analysis Fenchel conjugates and Mathlib convex-set binary
  combination APIs
Used in: random primal-dual gradient dual-coordinate carrier convexity for
  weighted averages and product-domain constructions
Book citation: book/FOML/RandomPrimalDualGradient.json#/setup/dual_space_definition
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem fenchelConjugateDomain_convex
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (scale : ℝ) (f : E → ℝ) :
    Convex ℝ (fenchelConjugateDomain scale f) := by
  rw [convex_iff_add_mem]
  intro y₁ hy₁ y₂ hy₂ a b ha hb hab
  exact fenchelConjugateDomain_mix_mem scale f hy₁ hy₂ ha hb hab

/-- A sum of Fenchel conjugates induces an affine lower minorant of a weighted
finite objective.

For each component, the carrier-restricted conjugate dominates
`⟪x, yᵢ⟫ - wᵢ fᵢ x`. Summing those inequalities and rewriting the inner
product against `∑ᵢ yᵢ` gives the finite-product saddle minorant.

Layer: Model | Gap: Level 1 (finite-product Fenchel affine minorant)
Proof: apply the carrier Fenchel evaluation bound componentwise, sum the
  inequalities, and rewrite by `inner_sum` and finite-sum subtraction.
Source: convex analysis Fenchel conjugates and Mathlib finite-sum inner-product
  algebra
Used in: random primal-dual gradient product-dual affine minorant for the
  averaged primal objective
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem sum_fenchel_affine_minorant_le_weighted_objective
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w : ι → ℝ) (f : ι → E → ℝ) (y : ι → E)
    (hy : ∀ i : ι,
      BddAbove (Set.range fun x : E => ⟪x, y i⟫_ℝ - w i * f i x))
    (x : E) :
    ⟪x, ∑ i : ι, y i⟫_ℝ -
        ∑ i : ι, fenchelConjugateOnCarrier (w i) (f i) ⟨y i, hy i⟩ ≤
      ∑ i : ι, w i * f i x := by
  classical
  have hsum :
      (∑ i : ι, (⟪x, y i⟫_ℝ - w i * f i x)) ≤
        ∑ i : ι, fenchelConjugateOnCarrier (w i) (f i) ⟨y i, hy i⟩ := by
    exact Finset.sum_le_sum fun i _hi =>
      le_fenchelConjugateOnCarrier (w i) (f i) ⟨y i, hy i⟩ x
  have hrewrite :
      (∑ i : ι, (⟪x, y i⟫_ℝ - w i * f i x)) =
        ⟪x, ∑ i : ι, y i⟫_ℝ - ∑ i : ι, w i * f i x := by
    simp [inner_sum, Finset.sum_sub_distrib]
  linarith

/-- A finite weighted Fenchel-Bregman sum equals the average linearization gap.

If the Fenchel-conjugate values at the scaled component-gradient points are
computed at `x₀` and `x`, and `averageGradient x` is the corresponding weighted
sum of component gradients, then the sum of the dual Bregman increments from
`x₀` to `x` is exactly the finite-sum objective linearization residual.

Layer: Model | Gap: Level 1 (finite-sum Fenchel-Bregman linearization identity)
Proof: unfold the Bregman increments with the supplied Fenchel value equalities,
  rewrite the weighted gradient sum into the average gradient, and close by
  finite-sum and inner-product bilinearity.
Source: convex analysis Fenchel conjugate algebra and Mathlib finite-sum
  bilinear inner-product APIs
Used in: random primal-dual gradient initialization converting the dual
  Fenchel-Bregman sum into the average-objective first-order residual
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem sum_bregman_scaled_fenchel_gradient_eq_average_linearization_gap
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w : ι → ℝ) (f : ι → E → ℝ) (grad : ι → E → E)
    (averageGradient : E → E) (x0 x : E)
    (y0 y : ι → E)
    (hy0Bdd : ∀ i : ι,
      BddAbove (Set.range fun z : E => ⟪z, y0 i⟫_ℝ - w i * f i z))
    (hyBdd : ∀ i : ι,
      BddAbove (Set.range fun z : E => ⟪z, y i⟫_ℝ - w i * f i z))
    (hy0 : ∀ i : ι, y0 i = w i • grad i x0)
    (hy : ∀ i : ι, y i = w i • grad i x)
    (hValue0 : ∀ i : ι,
      fenchelConjugateOnCarrier (w i) (f i) ⟨y0 i, hy0Bdd i⟩ =
        ⟪x0, y0 i⟫_ℝ - w i * f i x0)
    (hValue : ∀ i : ι,
      fenchelConjugateOnCarrier (w i) (f i) ⟨y i, hyBdd i⟩ =
        ⟪x, y i⟫_ℝ - w i * f i x)
    (hAvgGrad : averageGradient x = ∑ i : ι, w i • grad i x) :
    (Finset.univ.sum fun i : ι =>
      fenchelConjugateOnCarrier (w i) (f i) ⟨y i, hyBdd i⟩ -
        (fenchelConjugateOnCarrier (w i) (f i) ⟨y0 i, hy0Bdd i⟩ +
          ⟪x0, (y i) - (y0 i)⟫_ℝ)) =
      (∑ i : ι, w i * f i x0) - (∑ i : ι, w i * f i x) -
        ⟪averageGradient x, x0 - x⟫_ℝ := by
  classical
  have hsumValue :
      (Finset.univ.sum fun i : ι =>
        fenchelConjugateOnCarrier (w i) (f i) ⟨y i, hyBdd i⟩ -
          (fenchelConjugateOnCarrier (w i) (f i) ⟨y0 i, hy0Bdd i⟩ +
            ⟪x0, (y i) - (y0 i)⟫_ℝ)) =
        (Finset.univ.sum fun i : ι =>
          (⟪x, y i⟫_ℝ - w i * f i x) -
            ((⟪x0, y0 i⟫_ℝ - w i * f i x0) +
              ⟪x0, (y i) - (y0 i)⟫_ℝ)) := by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [hValue i, hValue0 i]
  rw [hsumValue]
  simp [hy, hy0, hAvgGrad, inner_sub_right, inner_smul_right, inner_smul_left,
    sum_inner, Finset.sum_sub_distrib]
  rw [show
      (∑ i : ι, w i * ⟪x, grad i x⟫_ℝ) =
        ∑ i : ι, w i * ⟪grad i x, x⟫_ℝ by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [real_inner_comm]]
  rw [show
      (∑ i : ι, w i * ⟪x0, grad i x⟫_ℝ) =
        ∑ i : ι, w i * ⟪grad i x, x0⟫_ℝ by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [real_inner_comm]]
  ring_nf

/-- A nonnegative multiple of a supporting gradient lies in the Fenchel-conjugate domain.

If `g` supports `f` at `x`, then `c • g` has bounded support family
`z ↦ ⟪z, c • g⟫ - c * f z` for every nonnegative scale `c`.

Layer: Model | Gap: Level 1 (scaled supporting-gradient Fenchel-domain membership)
Proof: rewrite the support inequality as an upper bound on `⟪z, g⟫ - f z`,
  multiply by the nonnegative scale, and package the resulting uniform upper
  bound for the support range.
Source: convex analysis Fenchel conjugates and Mathlib ordered real arithmetic
  for bounded-above support families
Used in: random primal-dual gradient construction of the scaled component
  gradient as a finite Fenchel-dual carrier point
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem smul_gradient_mem_fenchelConjugateDomain_of_support
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (x g : E) {c : ℝ} (hc : 0 ≤ c)
    (hsupport : ∀ z : E, f x + ⟪g, z - x⟫_ℝ ≤ f z) :
    c • g ∈ fenchelConjugateDomain c f := by
  classical
  change BddAbove (Set.range fun z : E => ⟪z, c • g⟫_ℝ - c * f z)
  refine ⟨c * (⟪x, g⟫_ℝ - f x), ?_⟩
  rintro r ⟨z, rfl⟩
  have hsupp_z := hsupport z
  have hsupp_bound : ⟪z, g⟫_ℝ - f z ≤ ⟪x, g⟫_ℝ - f x := by
    rw [inner_sub_right, real_inner_comm z g, real_inner_comm x g] at hsupp_z
    linarith
  have hmul := mul_le_mul_of_nonneg_left hsupp_bound hc
  calc
    ⟪z, c • g⟫_ℝ - c * f z = c * (⟪z, g⟫_ℝ - f z) := by
      simp [inner_smul_right]
      ring
    _ ≤ c * (⟪x, g⟫_ℝ - f x) := hmul

/-- The canonical Fenchel-domain point generated by a scaled gradient.

This packages the value `c • g` together with a finite-conjugate-domain
certificate, typically produced by a supporting-gradient or subgradient lemma.

Layer: Model | Concept: Fenchel
Proof: (definitional construction; subtype point from a scaled-gradient
  Fenchel-domain certificate)
Source: convex analysis Fenchel conjugates and Mathlib subtype carriers for
  bounded-above real support families
Used in: random primal-dual gradient construction of the scaled component
  gradient as a finite Fenchel-dual carrier point
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
noncomputable def scaledGradientFenchelPoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : ℝ) (f : E → ℝ) (g : E)
    (hmem : c • g ∈ fenchelConjugateDomain c f) :
    {y : E // y ∈ fenchelConjugateDomain c f} :=
  ⟨c • g, hmem⟩

/-- The canonical scaled-gradient Fenchel point has value `c • g`.

Layer: Model | Gap: Level 0 (scaled-gradient Fenchel point coercion)
Proof: by rfl after unfolding `scaledGradientFenchelPoint`.
Source: convex analysis Fenchel conjugates and Mathlib subtype coercions
Used in: random primal-dual gradient algebra that rewrites the constructed dual
  carrier point back to the scaled component gradient
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
@[simp] theorem scaledGradientFenchelPoint_coe
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : ℝ) (f : E → ℝ) (g : E)
    (hmem : c • g ∈ fenchelConjugateDomain c f) :
    (scaledGradientFenchelPoint c f g hmem).1 = c • g := by
  rfl

/-- A supporting point is a carrier subgradient of the Fenchel conjugate at a scaled gradient.

If `g` supports `f` at `x`, then `x` belongs to the carrier subdifferential of
the real-valued Fenchel conjugate on its finite domain at the dual point
`c • g`, for every nonnegative scale `c`.

Layer: Model | Gap: Level 1 (scaled Fenchel conjugate carrier-subgradient certificate)
Proof: expand carrier-subdifferential membership, use the Fenchel carrier
  lower bound for every dual point, use the scaled-gradient conjugate equality
  at `c • g`, and rearrange the affine inner-product terms.
Source: convex analysis Fenchel conjugates and Mathlib carrier subdifferential
  support inequalities
Used in: random primal-dual gradient dual prox witness and finite-sum
  Fenchel saddle subgradient certification
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem mem_carrierSubdifferential_fenchelConjugateOnDomain_smul_gradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (x g : E) {c : ℝ} (hc : 0 ≤ c)
    (hsupport : ∀ z : E, f x + ⟪g, z - x⟫_ℝ ≤ f z)
    (hmem : c • g ∈ fenchelConjugateDomain c f) :
    x ∈ SOptLib.carrierSubdifferential (X := fenchelConjugateDomain c f)
      (fun y : {y : E // y ∈ fenchelConjugateDomain c f} =>
        fenchelConjugateOnCarrier c f y)
      ⟨c • g, hmem⟩ := by
  classical
  rw [SOptLib.mem_carrierSubdifferential_iff]
  intro y
  have hLower :
      ⟪x, y.1⟫_ℝ - c * f x ≤ fenchelConjugateOnCarrier c f y :=
    le_fenchelConjugateOnCarrier c f y x
  have hValue :
      fenchelConjugateOnCarrier c f
          (⟨c • g, hmem⟩ : {y : E // y ∈ fenchelConjugateDomain c f}) =
        ⟪x, (⟨c • g, hmem⟩ :
          {y : E // y ∈ fenchelConjugateDomain c f}).1⟫_ℝ - c * f x := by
    simpa [fenchelConjugateOnCarrier, fenchelConjugateDomain] using
      fenchel_conjugate_smul_supporting_gradient_eq
        (f := f) (x := x) (g := g) (c := c) hc hsupport
  show fenchelConjugateOnCarrier c f
        (⟨c • g, hmem⟩ : {y : E // y ∈ fenchelConjugateDomain c f}) +
      ⟪x, y.1 - (⟨c • g, hmem⟩ :
        {y : E // y ∈ fenchelConjugateDomain c f}).1⟫_ℝ ≤
        fenchelConjugateOnCarrier c f y
  calc
    fenchelConjugateOnCarrier c f
        (⟨c • g, hmem⟩ : {y : E // y ∈ fenchelConjugateDomain c f}) +
        ⟪x, y.1 - (⟨c • g, hmem⟩ :
          {y : E // y ∈ fenchelConjugateDomain c f}).1⟫_ℝ
        = (⟪x, (⟨c • g, hmem⟩ :
            {y : E // y ∈ fenchelConjugateDomain c f}).1⟫_ℝ - c * f x) +
            ⟪x, y.1 - (⟨c • g, hmem⟩ :
              {y : E // y ∈ fenchelConjugateDomain c f}).1⟫_ℝ := by
          rw [hValue]
    _ = ⟪x, y.1⟫_ℝ - c * f x := by
          rw [inner_sub_right]
          ring
    _ ≤ fenchelConjugateOnCarrier c f y := hLower

/-- A nonnegative multiple of a convex gradient lies in the Fenchel-conjugate domain.

For a globally convex function, a pointwise within-gradient gives the supporting
hyperplane inequality at `x`; hence every nonnegative multiple of that gradient
has bounded Fenchel support family for the scaled objective.

Layer: Model | Gap: Level 1 (convex-gradient Fenchel-domain membership)
Proof: derive the affine support inequality from `ConvexOn` and
  `HasGradientWithinAt`, then apply the scaled supporting-gradient Fenchel
  domain theorem.
Source: convex analysis Fenchel conjugates, Mathlib convex first-order
  inequalities, and SOptLib bounded support-family API
Used in: random primal-dual gradient construction of scaled component gradients
  as finite Fenchel-dual carrier points
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem smul_gradient_mem_fenchelConjugateDomain_of_convex
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (x g : E) {c : ℝ} (hc : 0 ≤ c)
    (hf : ConvexOn ℝ Set.univ f)
    (hgrad : HasGradientWithinAt f g Set.univ x) :
    c • g ∈ fenchelConjugateDomain c f := by
  refine smul_gradient_mem_fenchelConjugateDomain_of_support f x g hc ?_
  intro z
  exact ConvexOn.first_order_linear_model_le_of_hasGradientWithinAt
    hf (by simp) (by simp) hgrad

end SOptLib
