import Mathlib.Data.Fin.Basic
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

namespace SOptLib

/-- The length-`t` sample window cut out of a Nat-indexed sample stream at an offset.

For a stochastic sample stream `sample : ℕ → Ω → S`, `sampleWindow sample offset t`
is the `Fin t`-indexed block `r ↦ sample (offset + r.val)`.  This keeps finite
sample blocks in Pi-vector form, which is the shape used by product-law and
finite-prefix determinism arguments.

Layer: Model | Concept: Sampling
Proof: (definitional construction; offset Nat-indexed stream restricted to a Fin-indexed window)
Source: Mathlib natural-number indices, Fin coordinates, and Pi-function APIs
Used in: randomized accelerated proximal-point fixed inner run finite sample blocks
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  randomized accelerated proximal-point method -/
def sampleWindow {Ω S : Type*} (sample : ℕ → Ω → S) (offset t : ℕ) : Ω → Fin t → S :=
  fun ω r => sample (offset + r.1) ω

/-- A sample window is the finite coordinate block cut out of the underlying stream.

Layer: Model | Gap: Level 0 (sample-window characterization)
Proof: by rfl after unfolding sampleWindow
Source: Mathlib natural-number indices, Fin coordinates, and Pi-function APIs
Used in: randomized accelerated proximal-point fixed inner run finite sample blocks
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  randomized accelerated proximal-point method -/
@[simp] theorem sampleWindow_def {Ω S : Type*} (sample : ℕ → Ω → S) (offset t : ℕ) :
    sampleWindow sample offset t = fun ω r => sample (offset + r.1) ω := rfl

/-- A sample window evaluates by reading the underlying stream at `offset + r.val`.

Layer: Model | Gap: Level 0 (sample-window coordinate unfolding)
Proof: by rfl after unfolding sampleWindow
Source: Mathlib natural-number indices, Fin coordinates, and Pi-function APIs
Used in: randomized accelerated proximal-point fixed inner run finite sample blocks
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  randomized accelerated proximal-point method -/
@[simp] theorem sampleWindow_apply {Ω S : Type*} (sample : ℕ → Ω → S)
    (offset t : ℕ) (ω : Ω) (r : Fin t) :
    sampleWindow sample offset t ω r = sample (offset + r.1) ω := rfl

/-- The window starting at `offset + 1` is the tail of the window starting at `offset`.

Layer: Model | Gap: Level 0 (sample-window offset successor reindexing)
Proof: extensionality and natural-number arithmetic after unfolding `sampleWindow`
Source: Mathlib natural-number indices, Fin coordinates, and Pi-function APIs
Used in: finite-prefix arguments that drop the first sample of a stochastic block
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  randomized accelerated proximal-point method -/
theorem sampleWindow_offset_succ_eq_tail {Ω S : Type*} (sample : ℕ → Ω → S)
    (offset t : ℕ) :
    (fun ω r => sampleWindow sample (offset + 1) t ω r) =
      fun ω r => sampleWindow sample offset (t + 1) ω r.succ := by
  funext ω r
  simp [sampleWindow, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

end SOptLib
