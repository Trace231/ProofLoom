import Mathlib.Data.Real.Basic

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: strictly positive real parameter; orig was CorollaryTwoEpsilon.
-- generality used: a real scalar together with a strict positivity witness; no
-- measure, independence, integrability, optimization, or finite-dimensional
-- assumptions are needed.
-- portable call pattern: PAGE-style and other stochastic-optimization rate
-- formulas can take this subtype for an accuracy tolerance, project its value
-- with `.1`, and use `.2` to discharge denominator positivity side conditions.
-- counterargument checked: this is a reusable denominator-domain type rather
-- than paper traceability or a caller-side expression; searches found no
-- existing SOptLib or Mathlib alias with the exact strict-positive-real
-- contract, and the nonnegative subtype would incorrectly admit zero.
-- coverage search: searched "positive real parameter subtype", "strictly
-- positive real subtype", and "positive accuracy tolerance" in SOptLib and
-- Mathlib; existing hits were unrelated positive constants, positive natural
-- indices, or algorithm-specific wrappers, so coverage was none.
-- minimal hypotheses: all already minimal for the fixed real-valued rate
-- formulas; the subtype witness supplies the only required hypothesis.

/-- A real parameter carrying a proof of strict positivity for accuracy and
tolerance formulas whose denominators must be nonzero.

Layer: Model | Concept: strictly positive real parameter
Proof: (definitional construction; subtype of real numbers satisfying strict positivity)
Source: Mathlib real-order and subtype APIs for denominator-domain parameters
Used in: PAGE-style stochastic-optimization rate formulas, where the projected value supplies the tolerance and the stored witness discharges positivity side conditions
Book citation: book/research/PAGE.json#/extension/additions/main_theorem/statement_math
Origin algorithm: Li, Bao, Zhang, and Richtárik, PAGE: A Simple and Optimal Probabilistic Gradient Estimator for Nonconvex Optimization -/
abbrev PositiveRealParameter : Type := {ε : ℝ // 0 < ε}

end SOptLib
