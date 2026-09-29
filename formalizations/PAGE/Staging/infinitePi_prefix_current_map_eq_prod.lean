-- Generalization plan (G0):
-- concept/name: prefix/current pushforward law for an infinite product;
--   orig was branch_prefix_current_map_eq_prod.
-- generality used: arbitrary MeasurableSpace A and a Nat-indexed family of
--   probability measures; no finiteness, topology, or optimization assumptions.
-- portable call pattern: split history and a fresh draw in randomized
--   variance-reduced gradient or stochastic block-coordinate proofs; the
--   coordinate type, time-varying laws, and cutoff may all change.
-- counterargument checked: the window-independence bridge does not supply the
--   joint law or identify its second marginal. This theorem derives both from
--   the canonical product measure, without caller-supplied independence facts.
-- coverage search: "infinite product map prefix current coordinate product
--   measure independent finite windows" and "joint law prefix current
--   coordinate equals product marginal laws infinite product probability";
--   inspected iIndepFun_infinitePi, infinitePi_map_eval, and
--   iIndepFun.indepFun_fin_range_offset_windows_of_disjoint (partial coverage).
--   map_pair_eq_prod_map_of_indepFun_of_map_eq needs independence and a reference
--   random variable with equal law, so it does not establish this contract.
--   Mathlib semantic search timed out; local signatures and sources were read.
--   The active round registry contains no matching approved statement.
-- minimal hypotheses: probability instances for each coordinate measure;
--   projection measurability and finiteness of the product follow internally.

import Mathlib.Probability.Independence.InfinitePi
import SOptLib.Glue.Probability

open MeasureTheory ProbabilityTheory

/-- The strict prefix and current coordinate of a time-varying infinite product
have the product pushforward law.

Layer: Model | Gap: Level 1 (prefix/current product-law decomposition)
Proof: derive independence of the finite prefix and current singleton from the
coordinate independence of the infinite product, then use the product-law
characterization of `IndepFun` and the infinite-product marginal theorem.
Source: Mathlib infinite product measures and independence APIs, together with
SOptLib's finite-window independence bridge
`ProbabilityTheory.iIndepFun.indepFun_fin_range_offset_windows_of_disjoint`.
Used in: separating the current refresh decision from previous branch decisions
before combining with mini-batch histories to derive the estimator's conditional
branch law; also fresh-coordinate laws for stochastic block-coordinate updates.
Book citation: book/research/PAGE.json#/algorithm_spec/steps/1
Origin algorithm: Li, Bao, Zhang, Richtarik, PAGE: A Simple and Optimal
Probabilistic Gradient Estimator for Nonconvex Optimization, ICML 2021,
Algorithm 1 (PAGE) -/
theorem infinitePi_prefix_current_map_eq_prod
    {A : Type*} [MeasurableSpace A]
    (μ : ℕ → Measure A)
    [hμ : ∀ n, IsProbabilityMeasure (μ n)]
    (t : ℕ) :
    Measure.map
        (fun x : ℕ → A => (fun k : Fin t => x k.1, x t))
        (Measure.infinitePi μ) =
      (Measure.map (fun x : ℕ → A => fun k : Fin t => x k.1)
        (Measure.infinitePi μ)).prod (μ t) := by
  classical
  haveI hpiProb : IsProbabilityMeasure (Measure.infinitePi μ) := by
    infer_instance
  haveI hpiFinite : IsFiniteMeasure (Measure.infinitePi μ) := by
    infer_instance
  have hcoords_iIndep :
      iIndepFun
        (fun n (x : ℕ → A) => x n) (Measure.infinitePi μ) := by
    exact iIndepFun_infinitePi (fun _ => measurable_id)
  have hcoords_meas : ∀ n : ℕ, Measurable (fun x : ℕ → A => x n) := by
    intro n
    exact measurable_pi_apply n
  have hdisj :
      Disjoint (Finset.range t)
        (Finset.image (fun r : Fin 1 => t + r.1) Finset.univ) := by
    rw [Finset.disjoint_left]
    intro n hn hmem
    rcases Finset.mem_image.mp hmem with ⟨r, -, rfl⟩
    have hr0 : r.1 = 0 := Nat.lt_one_iff.mp r.2
    have hnlt : t + r.1 < t := by
      simpa [Finset.mem_range] using hn
    omega
  have hwindow :
      IndepFun
        (fun x : ℕ → A => fun r : Fin t => x r.1)
        (fun x : ℕ → A => fun r : Fin 1 => x (t + r.1))
        (Measure.infinitePi μ) :=
    iIndepFun.indepFun_fin_range_offset_windows_of_disjoint
      (fun n (x : ℕ → A) => x n) (Measure.infinitePi μ) t t 1
      hcoords_meas hcoords_iIndep hdisj
  let currentFromWindow : (Fin 1 → A) → A :=
    fun v => v ⟨0, by norm_num⟩
  have hcurrentFromWindow : Measurable currentFromWindow := by
    exact measurable_pi_apply (⟨0, by norm_num⟩ : Fin 1)
  have hindep :
      IndepFun
        (fun x : ℕ → A => fun k : Fin t => x k.1)
        (fun x : ℕ → A => x t)
        (Measure.infinitePi μ) := by
    have hcomp := hwindow.comp measurable_id hcurrentFromWindow
    simpa [currentFromWindow, Function.comp_def] using hcomp
  have hprefixAEM :
      AEMeasurable (fun x : ℕ → A => fun k : Fin t => x k.1)
        (Measure.infinitePi μ) := by
    have hprefixMeas :
        Measurable (fun x : ℕ → A => fun k : Fin t => x k.1) := by
      refine measurable_pi_lambda _ ?_
      intro k
      exact measurable_pi_apply k.1
    exact hprefixMeas.aemeasurable
  have hcurrentAEM :
      AEMeasurable (fun x : ℕ → A => x t) (Measure.infinitePi μ) :=
    (measurable_pi_apply t).aemeasurable
  have hcurrentMap :
      Measure.map (fun x : ℕ → A => x t) (Measure.infinitePi μ) = μ t := by
    simpa using (Measure.infinitePi_map_eval μ t)
  calc
    Measure.map
        (fun x : ℕ → A => (fun k : Fin t => x k.1, x t))
        (Measure.infinitePi μ) =
      (Measure.map (fun x : ℕ → A => fun k : Fin t => x k.1)
        (Measure.infinitePi μ)).prod
        (Measure.map (fun x : ℕ → A => x t) (Measure.infinitePi μ)) := by
        exact (indepFun_iff_map_prod_eq_prod_map_map
          hprefixAEM hcurrentAEM).mp hindep
    _ = (Measure.map (fun x : ℕ → A => fun k : Fin t => x k.1)
        (Measure.infinitePi μ)).prod (μ t) := by
        rw [hcurrentMap]
