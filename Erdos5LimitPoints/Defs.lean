/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Mathlib

/-!
# Definitions

The definitions used in the statements of `Challenge.lean`. They must agree *verbatim* with
the definitions there, since `lake comparator` checks that every declaration reached from a
compared statement is identical in the challenge and in the solution.
-/

open Filter

namespace Erdos5

/-- A set `B ⊆ ℝ` has the *four-point property* if for all reals `β₀ ≤ β₁ ≤ β₂ ≤ β₃` one of
the six differences `βⱼ - βᵢ` (`i < j`) lies in `B`.

This is the conclusion of Merikoski's theorem [Me20, Theorem 1] for the set of limit points of
the normalised prime gaps. -/
def HasFourPointProperty (B : Set ℝ) : Prop :=
  ∀ β : Fin 4 → ℝ, Monotone β → ∃ i j, i < j ∧ β j - β i ∈ B

/-- The prime gap `pₙ₊₁ - pₙ`, where `pₙ = Nat.nth Nat.Prime n` is the `n`-th prime,
counting from `p₀ = 2`. -/
noncomputable def primeGap (n : ℕ) : ℕ := (n + 1).nth Nat.Prime - n.nth Nat.Prime

/-- The normalised prime gap `(pₙ₊₁ - pₙ) / log n`. -/
noncomputable def normalizedGap (n : ℕ) : ℝ := primeGap n / Real.log n

/-- The set `𝕃` of (finite) limit points of the sequence `(pₙ₊₁ - pₙ) / log n`. -/
def limitPointSet : Set ℝ := {x : ℝ | MapClusterPt x atTop normalizedGap}

/-- The prime gap normalised by the logarithm of the smaller prime,
`(pₙ₊₁ - pₙ) / log pₙ`. -/
noncomputable def normalizedGapLogPrime (n : ℕ) : ℝ :=
  primeGap n / Real.log (n.nth Nat.Prime)

/-- The set of (finite) limit points of the sequence `(pₙ₊₁ - pₙ) / log pₙ`; this is the set
`𝕃` of [Me20] (without the point `∞`). -/
def limitPointSetLogPrime : Set ℝ := {x : ℝ | MapClusterPt x atTop normalizedGapLogPrime}

end Erdos5
