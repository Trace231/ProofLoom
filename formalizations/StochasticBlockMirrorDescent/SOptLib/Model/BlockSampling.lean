import Mathlib.Data.Nat.Basic

/-- Natural-time stream of paired oracle samples and block indices.

For sample type `S` and block-index type `I`, `blockSamplePath S I` is the
path space whose `k`th coordinate is the pair generated at iteration `k`.  It
uses the canonical Pi-function representation so Mathlib's measurable-space
and coordinate-projection APIs apply directly.

Layer: Model | Concept: Sampling
Proof: (definitional construction; Nat-indexed Pi-function over the sample/block product type)
Source: Mathlib Pi-function, natural-number index, and product type APIs
Used in: stochastic block mirror descent iid product stream for oracle samples and sampled blocks
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic block mirror descent -/
abbrev blockSamplePath (S I : Type*) : Type _ :=
  ℕ → S × I
