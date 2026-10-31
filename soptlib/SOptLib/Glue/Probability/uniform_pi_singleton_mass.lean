import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic

-- Generalization plan (G0):
-- concept/name: singleton atom of a finite product of uniform finite laws; orig was `uniform_pi_singleton_mass`
-- generality used: finite component and index types `A` and `C`, a nonempty value type, and the top measurable space on `A`; no optimization, topology, integrability, independence, or finite-dimensional assumptions are used.
-- portable call pattern: any finite uniform function-valued sample law can rewrite the mass of a fixed sample vector to the inverse cardinality of its function space while changing the finite domain, value type, and vector.
-- counterargument checked: Mathlib supplies `Measure.pi_singleton` and `PMF.uniformOfFintype_apply` separately, but no theorem combining them with the cardinality identity; the result is a reusable product-law atom calculation rather than paper traceability or a caller-side wrapper.
-- coverage search: searched `uniform product measure function space singleton inverse cardinality`, `finite product uniform singleton mass`, and the SOptLib catalog; only the PAGE-local theorem and unrelated finite-uniform integral/fiber lemmas were found, so coverage is partial.
-- minimal hypotheses: `[Fintype A] [Fintype C] [DecidableEq C] [Nonempty A]` are retained from the product-measure and finite-uniform APIs; no additional setup fields are needed.

/-- A finite product of uniform component laws assigns every function-valued atom
the inverse cardinality of the finite function space.

Layer: Glue | Gap: Level 1 (finite uniform product singleton mass)
Proof: Rewrite the product-measure singleton as the finite product of component singleton masses, simplify each uniform PMF atom, and identify the resulting power with the inverse cardinality of the function space.
Source: Mathlib finite product measures, finite uniform probability mass functions, and extended-nonnegative-real cardinality identities
Used in: finite mini-batch and recursive-sample proofs that convert a fixed function-valued row under an iid uniform product law into its atom weight
Book citation: book/research/PAGE.json#/algorithm_spec
Origin algorithm: Li, Bao, Zhang, and Richtárik, PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization -/
theorem uniform_pi_singleton_mass
    {A C : Type*} [Fintype A] [Fintype C] [DecidableEq C] [Nonempty A] (v : C → A) :
    letI : MeasurableSpace A := ⊤
    (MeasureTheory.Measure.pi
      (fun _ : C => PMF.toMeasure (PMF.uniformOfFintype (α := A))))
        ({v} : Set (C → A)) =
      ENNReal.ofReal ((Fintype.card (C → A) : ℝ)⁻¹) := by
  classical
  letI : MeasurableSpace A := ⊤
  rw [MeasureTheory.Measure.pi_singleton]
  simp [PMF.uniformOfFintype_apply]
  rw [ENNReal.ofReal_inv_of_pos (pow_pos (Nat.cast_pos.mpr Fintype.card_pos) _)]
  rw [ENNReal.ofReal_pow (Nat.cast_nonneg (Fintype.card A))]
  simpa using
    (ENNReal.inv_pow (a := (Fintype.card A : ENNReal)) (n := Fintype.card C)).symm
