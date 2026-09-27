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

Indices are `0`-based (`Fin 4`), so `β₀ ≤ ⋯ ≤ β₃` are the note's `β₁ ≤ ⋯ ≤ β₄`. The note
defines the property for `B ⊆ [0, ∞)`; since all differences `β j - β i` with `i < j` of a
monotone tuple are `≥ 0`, `B` has the property if and only if `B ∩ [0, ∞)` does, so allowing
arbitrary `B ⊆ ℝ` changes nothing. This is the conclusion of Merikoski's theorem
[Me20, Theorem 1] for the set of limit points of the normalised prime gaps. -/
def HasFourPointProperty (B : Set ℝ) : Prop :=
  ∀ β : Fin 4 → ℝ, Monotone β → ∃ i j, i < j ∧ β j - β i ∈ B

/-- The prime gap `pₙ₊₁ - pₙ`, where `pₙ = Nat.nth Nat.Prime n` is the `n`-th prime,
counting from `p₀ = 2`. The subtraction in `ℕ` is exact since `pₙ < pₙ₊₁`. -/
noncomputable def primeGap (n : ℕ) : ℕ := (n + 1).nth Nat.Prime - n.nth Nat.Prime

/-- The normalised prime gap `(pₙ₊₁ - pₙ) / log n`. (As `Real.log 0 = Real.log 1 = 0` and
`x / 0 = 0`, the values at `n = 0, 1` are `0`; finitely many values do not affect limit
points.) -/
noncomputable def normalizedGap (n : ℕ) : ℝ := primeGap n / Real.log n

/-- The set `𝕃` of (finite) limit points of the sequence `(pₙ₊₁ - pₙ) / log n`.

`MapClusterPt x atTop u` means that every neighbourhood of `x` contains `u n` for infinitely
many `n`; equivalently, `x = lim u (n i)` for some strictly increasing sequence `n i`, which is
the sense of "limit point" used by Erdős and [Me20]. The point `∞` is not included; it plays
no role in the measure statements. -/
def limitPointSet : Set ℝ := {x : ℝ | MapClusterPt x atTop normalizedGap}

/-- The prime gap normalised by the logarithm of the smaller prime,
`(pₙ₊₁ - pₙ) / log pₙ`. -/
noncomputable def normalizedGapLogPrime (n : ℕ) : ℝ :=
  primeGap n / Real.log (n.nth Nat.Prime)

/-- The set of (finite) limit points of the sequence `(pₙ₊₁ - pₙ) / log pₙ`; this is the set
`𝕃` of [Me20] (without the point `∞`). -/
def limitPointSetLogPrime : Set ℝ := {x : ℝ | MapClusterPt x atTop normalizedGapLogPrime}

end Erdos5
