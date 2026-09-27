/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Mathlib

/-!
# Sets with the four-point property have lower density at least 25/74

*Towards Erdős Problem #5 on limit points of normalised prime gaps.*

This file is the statement of record: it contains the definitions and the theorem statements
proved in `Solution.lean` (checked against this file by `lake comparator`, see
`comparator.json`). It imports only Mathlib.

Let `p₀ = 2, p₁ = 3, p₂ = 5, …` be the primes in increasing order and let `𝕃` be the set of
(finite) limit points of the normalised prime gaps `(pₙ₊₁ - pₙ) / log n`. Erdős asked whether
every `C ∈ [0, ∞]` is a limit point, i.e. whether `𝕃 = [0, ∞)` for the finite limit points
(Erdős Problem #5, <https://www.erdosproblems.com/5>).

A set `B ⊆ ℝ` has the **four-point property** if for all reals `β₀ ≤ β₁ ≤ β₂ ≤ β₃` some
difference `βⱼ - βᵢ` with `i < j` lies in `B`. Merikoski [Me20, Theorem 1] proved (by sieve
methods) that `𝕃` has the four-point property, and deduced `λ(𝕃 ∩ [0, T]) ≥ T / 3` for all
`T > 0`, where `λ` is Lebesgue measure.

The main result formalised here (Theorem 1.2 of the note cited below) is a purely
measure-theoretic statement about the four-point property:

* `Erdos5.HasFourPointProperty.exists_volume_inter_Icc_ge`: if `B ⊆ ℝ` has the four-point
  property, then `λ(B ∩ [0, T]) ≥ (25 / 74) T - C` for some constant `C` and all `T`.
  Note `25 / 74 = 1 / 3 + 1 / 222`.
* `Erdos5.HasFourPointProperty.le_liminf_volume_inter_Icc_div`: the `liminf` form
  `liminf_{T → ∞} λ(B ∩ [0, T]) / T ≥ 25 / 74` stated in the note.

The note assumes `B ⊆ [0, ∞)` Lebesgue measurable; no such assumption is needed here. Only
nonnegative differences occur in the four-point property, and `volume` is Lebesgue outer
measure: if `B̃ = toMeasurable volume B` is a measurable hull of `B`, then `B̃` also has the
four-point property and `λ(B̃ ∩ [0, T]) = λ(B ∩ [0, T])` for every `T`.

The consequence for prime gaps (Corollary 1.3 of the note) is proved **conditionally on
Merikoski's theorem**: combined with it, the main theorem gives `λ(𝕃 ∩ [0, T]) ≥ (76 / 225) T`
for all large `T` (note `76 / 225 < 25 / 74`). Merikoski's theorem is a deep result from sieve
theory that is **not** formalised here; the corollaries below take it as an explicit hypothesis
`merikoski`, which is the same proposition as `erdos_5.variants.merikoski` in the Formal
Conjectures project (for the `log n` normalisation used on erdosproblems.com), respectively as
[Me20, Theorem 1] (for the `log pₙ` normalisation used in [Me20] and in the note). We also
prove, unconditionally, that the two normalisations have the same limit points
(`Erdos5.limitPointSet_eq_limitPointSetLogPrime`), so either form of Merikoski's theorem gives
both corollaries.

## References

* The note: *More than one third of the positive reals are limit points of normalized prime
  gaps* (2026), Theorem 1.2 and Corollary 1.3.
* [Me20] J. Merikoski, *Limit points of normalized prime gaps*, J. Lond. Math. Soc. (2) 102
  (2020), 99–124, doi:10.1112/jlms.12314.
* [EP5] T. F. Bloom, *Erdős Problem #5*, <https://www.erdosproblems.com/5>.
* Formal Conjectures, `FormalConjectures/ErdosProblems/5.lean` at commit `6fbb54f`,
  <https://github.com/google-deepmind/formal-conjectures>.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Erdos5

/-! ### The four-point property -/

/-- A set `B ⊆ ℝ` has the *four-point property* if for all reals `β₀ ≤ β₁ ≤ β₂ ≤ β₃` one of
the six differences `βⱼ - βᵢ` (`i < j`) lies in `B`.

Indices are `0`-based (`Fin 4`), so `β₀ ≤ ⋯ ≤ β₃` are the note's `β₁ ≤ ⋯ ≤ β₄`. The note
defines the property for `B ⊆ [0, ∞)`; since all differences `β j - β i` with `i < j` of a
monotone tuple are `≥ 0`, `B` has the property if and only if `B ∩ [0, ∞)` does, so allowing
arbitrary `B ⊆ ℝ` changes nothing. This is the conclusion of Merikoski's theorem
[Me20, Theorem 1] for the set of limit points of the normalised prime gaps. -/
def HasFourPointProperty (B : Set ℝ) : Prop :=
  ∀ β : Fin 4 → ℝ, Monotone β → ∃ i j, i < j ∧ β j - β i ∈ B

/-- **Main theorem** (Theorem 1.2, in the stronger `O(1)` form given by its proof).
If `B ⊆ ℝ` has the four-point property, then there is a constant `C` such that
`λ(B ∩ [0, T]) ≥ (25 / 74) T - C` for every real `T`.

Here `volume` is Lebesgue outer measure (the Lebesgue measure for Lebesgue-measurable `B`). As
`volume (B ∩ Icc 0 T)` is finite and `ENNReal.ofReal` sends negative numbers to `0`, the
inequality is equivalent to the real inequality `(25 / 74) T - C ≤ λ(B ∩ [0, T])`; it is a
genuine statement `λ(B ∩ [0, T]) ≥ (25 / 74) T - O(1)` as `T → ∞`. -/
theorem HasFourPointProperty.exists_volume_inter_Icc_ge {B : Set ℝ}
    (hB : HasFourPointProperty B) :
    ∃ C : ℝ, ∀ T : ℝ, ENNReal.ofReal (25 / 74 * T - C) ≤ volume (B ∩ Icc 0 T) := by
  sorry

/-- **Main theorem** (Theorem 1.2). If `B ⊆ ℝ` has the four-point property, then
`liminf_{T → ∞} λ(B ∩ [0, T]) / T ≥ 25 / 74`.

The quotient is taken in `ℝ≥0∞`, where `liminf` is always meaningful. For `T > 0` the quotient
lies in `[0, 1]`, so this is the real `liminf` of the note; the values at `T ≤ 0` (where
`ENNReal.ofReal T = 0`) are irrelevant along `atTop`. -/
theorem HasFourPointProperty.le_liminf_volume_inter_Icc_div {B : Set ℝ}
    (hB : HasFourPointProperty B) :
    (25 / 74 : ℝ≥0∞) ≤ liminf (fun T : ℝ => volume (B ∩ Icc 0 T) / ENNReal.ofReal T) atTop := by
  sorry

/-! ### Limit points of normalised prime gaps (`log n` normalisation, as in Erdős Problem 5)

The following three definitions are copied from the Formal Conjectures project (`primeGap`
from `FormalConjecturesForMathlib/NumberTheory/PrimeGap.lean`, the other two from
`FormalConjectures/ErdosProblems/5.lean`), verbatim up to name qualification (Formal Conjectures
puts `primeGap` in the root namespace and writes `log` for `Real.log`).

`Nat.nth Nat.Prime` is `0`-indexed (`p₀ = 2`), while the note, [Me20] and erdosproblems.com
use `p₁ = 2`; thus `normalizedGap n` is `(p_{n+2} - p_{n+1}) / log n` in `1`-based notation.
Since `log (m - 1) / log m → 1`, this shift does not change the set of limit points. -/

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

/-- **Corollary 1.3** (`log n` normalisation), *conditional on Merikoski's theorem*.
If `limitPointSet` has the four-point property, then `λ(𝕃 ∩ [0, T]) ≥ (25 / 74) T - C` for
some constant `C` and all `T`.

The hypothesis `merikoski` is `HasFourPointProperty limitPointSet` unfolded; it is Merikoski's
theorem [Me20, Theorem 1] and the same proposition as `erdos_5.variants.merikoski` in Formal
Conjectures. All arithmetic information about primes enters through this hypothesis; the
statement is the main theorem applied to `B = 𝕃`. -/
theorem exists_volume_limitPointSet_inter_Icc_ge_of_merikoski
    (merikoski : ∀ β : Fin 4 → ℝ, Monotone β → ∃ i j, i < j ∧ β j - β i ∈ limitPointSet) :
    ∃ C : ℝ, ∀ T : ℝ,
      ENNReal.ofReal (25 / 74 * T - C) ≤ volume (limitPointSet ∩ Icc 0 T) := by
  sorry

/-- **Corollary 1.3** (`log n` normalisation), *conditional on Merikoski's theorem*:
`λ(𝕃 ∩ [0, T]) ≥ (76 / 225) T` for all sufficiently large `T`. The hypothesis `merikoski` is
as in `exists_volume_limitPointSet_inter_Icc_ge_of_merikoski`. -/
theorem eventually_volume_limitPointSet_inter_Icc_ge_of_merikoski
    (merikoski : ∀ β : Fin 4 → ℝ, Monotone β → ∃ i j, i < j ∧ β j - β i ∈ limitPointSet) :
    ∀ᶠ T : ℝ in atTop, ENNReal.ofReal (76 / 225 * T) ≤ volume (limitPointSet ∩ Icc 0 T) := by
  sorry

/-! ### Limit points of normalised prime gaps (`log pₙ` normalisation, as in [Me20]) -/

/-- The prime gap normalised by the logarithm of the smaller prime,
`(pₙ₊₁ - pₙ) / log pₙ`. -/
noncomputable def normalizedGapLogPrime (n : ℕ) : ℝ :=
  primeGap n / Real.log (n.nth Nat.Prime)

/-- The set of (finite) limit points of the sequence `(pₙ₊₁ - pₙ) / log pₙ`; this is the set
`𝕃` of [Me20] (without the point `∞`). -/
def limitPointSetLogPrime : Set ℝ := {x : ℝ | MapClusterPt x atTop normalizedGapLogPrime}

/-- **Corollary 1.3** (`log pₙ` normalisation), *conditional on Merikoski's theorem*
[Me20, Theorem 1], which is stated in [Me20] for this normalisation ("for any reals
`β₁ ≤ β₂ ≤ β₃ ≤ β₄`, `𝕃 ∩ {βⱼ - βᵢ} ≠ ∅`"; the point `∞ ∈ 𝕃` is irrelevant there since the
differences are finite): `λ(𝕃 ∩ [0, T]) ≥ (25 / 74) T - C` for some constant `C` and all
`T`. -/
theorem exists_volume_limitPointSetLogPrime_inter_Icc_ge_of_merikoski
    (merikoski : ∀ β : Fin 4 → ℝ, Monotone β →
      ∃ i j, i < j ∧ β j - β i ∈ limitPointSetLogPrime) :
    ∃ C : ℝ, ∀ T : ℝ,
      ENNReal.ofReal (25 / 74 * T - C) ≤ volume (limitPointSetLogPrime ∩ Icc 0 T) := by
  sorry

/-- **Corollary 1.3** (`log pₙ` normalisation), *conditional on Merikoski's theorem*:
`λ(𝕃 ∩ [0, T]) ≥ (76 / 225) T` for all sufficiently large `T`. -/
theorem eventually_volume_limitPointSetLogPrime_inter_Icc_ge_of_merikoski
    (merikoski : ∀ β : Fin 4 → ℝ, Monotone β →
      ∃ i j, i < j ∧ β j - β i ∈ limitPointSetLogPrime) :
    ∀ᶠ T : ℝ in atTop,
      ENNReal.ofReal (76 / 225 * T) ≤ volume (limitPointSetLogPrime ∩ Icc 0 T) := by
  sorry

/-! ### The two normalisations -/

/-- The two normalisations have the same limit points: since `log pₙ / log n → 1` (a consequence
of Chebyshev's elementary lower bound for the number of primes up to `x`), the sets of limit
points of `(pₙ₊₁ - pₙ) / log n` and of `(pₙ₊₁ - pₙ) / log pₙ` coincide. In particular the
conditional corollaries above for the two normalisations are equivalent, and Merikoski's
theorem as stated in [Me20] (for the `log pₙ` normalisation) is the same statement as its
Formal Conjectures version (for the `log n` normalisation). -/
theorem limitPointSet_eq_limitPointSetLogPrime : limitPointSet = limitPointSetLogPrime := by
  sorry

end Erdos5
