import Mathlib

/-!
# More than one third of the positive reals are limit points of normalised prime gaps

This file is the statement of record: it contains the definitions and the theorem statements
proved in `Solution.lean` (checked against this file by `lake comparator`, see
`comparator.json`). It imports only Mathlib.

Let `p₀ = 2, p₁ = 3, p₂ = 5, …` be the primes in increasing order and let `𝕃` be the set of
(finite) limit points of the normalised prime gaps `(pₙ₊₁ - pₙ) / log n`. Erdős asked whether
`𝕃 = [0, ∞)` (Erdős Problem #5, <https://www.erdosproblems.com/5>).

A set `B ⊆ ℝ` has the **four-point property** if for all reals `β₁ ≤ β₂ ≤ β₃ ≤ β₄` some
difference `βⱼ - βᵢ` with `i < j` lies in `B`. Merikoski [Me20, Theorem 1] proved (by sieve
methods) that `𝕃` has the four-point property, and deduced `λ(𝕃 ∩ [0, T]) ≥ T / 3` for all
`T > 0`, where `λ` is Lebesgue measure.

The main result formalised here is a purely measure-theoretic statement about the four-point
property:

* `Erdos5.HasFourPointProperty.exists_volume_inter_Icc_ge`: if `B ⊆ ℝ` has the four-point
  property, then `λ(B ∩ [0, T]) ≥ (25 / 74) T - C` for some constant `C` and all `T`.
  Note `25 / 74 = 1 / 3 + 1 / 222`.
* `Erdos5.HasFourPointProperty.le_liminf_volume_inter_Icc_div`: the same statement in the
  `liminf` form `liminf_{T → ∞} λ(B ∩ [0, T]) / T ≥ 25 / 74`.

No measurability assumption on `B` is needed (`volume` is Lebesgue outer measure, and
enlarging `B` to a measurable hull preserves the four-point property).

Combined with Merikoski's theorem, this gives `λ(𝕃 ∩ [0, T]) ≥ (76 / 225) T` for all large `T`
(note `76 / 225 < 25 / 74`). Merikoski's theorem is a deep result from sieve theory that is
**not** formalised here; the corollaries below take it as an explicit hypothesis, stated
exactly as `erdos_5.variants.merikoski` in the Formal Conjectures project (for the
`log n` normalisation used on erdosproblems.com), respectively as in [Me20] (for the `log pₙ`
normalisation).

## References

* [Me20] J. Merikoski, *Limit points of normalized prime gaps*, J. Lond. Math. Soc. (2) 102
  (2020), 99–124.
* [EP5] T. F. Bloom, *Erdős Problem #5*, <https://www.erdosproblems.com/5>.
* Formal Conjectures, `FormalConjectures/ErdosProblems/5.lean`,
  <https://github.com/google-deepmind/formal-conjectures>.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Erdos5

/-! ### The four-point property -/

/-- A set `B ⊆ ℝ` has the *four-point property* if for all reals `β₀ ≤ β₁ ≤ β₂ ≤ β₃` one of
the six differences `βⱼ - βᵢ` (`i < j`) lies in `B`.

This is the conclusion of Merikoski's theorem [Me20, Theorem 1] for the set of limit points of
the normalised prime gaps. -/
def HasFourPointProperty (B : Set ℝ) : Prop :=
  ∀ β : Fin 4 → ℝ, Monotone β → ∃ i j, i < j ∧ β j - β i ∈ B

/-- **Main theorem** (Theorem 1.2, in the stronger `O(1)` form given by its proof).
If `B ⊆ ℝ` has the four-point property, then there is a constant `C` such that
`λ(B ∩ [0, T]) ≥ (25 / 74) T - C` for every real `T`. -/
theorem HasFourPointProperty.exists_volume_inter_Icc_ge {B : Set ℝ}
    (hB : HasFourPointProperty B) :
    ∃ C : ℝ, ∀ T : ℝ, ENNReal.ofReal (25 / 74 * T - C) ≤ volume (B ∩ Icc 0 T) := by
  sorry

/-- **Main theorem** (Theorem 1.2). If `B ⊆ ℝ` has the four-point property, then
`liminf_{T → ∞} λ(B ∩ [0, T]) / T ≥ 25 / 74`.

The quotient is taken in `ℝ≥0∞`, where `liminf` is always meaningful. -/
theorem HasFourPointProperty.le_liminf_volume_inter_Icc_div {B : Set ℝ}
    (hB : HasFourPointProperty B) :
    (25 / 74 : ℝ≥0∞) ≤ liminf (fun T : ℝ => volume (B ∩ Icc 0 T) / ENNReal.ofReal T) atTop := by
  sorry

/-! ### Limit points of normalised prime gaps (`log n` normalisation, as in Erdős Problem 5)

The following three definitions are copied verbatim from the Formal Conjectures project
(`primeGap` from `FormalConjecturesForMathlib/NumberTheory/PrimeGap.lean`, the other two from
`FormalConjectures/ErdosProblems/5.lean`), up to the namespace of `primeGap`. -/

/-- The prime gap `pₙ₊₁ - pₙ`, where `pₙ = Nat.nth Nat.Prime n` is the `n`-th prime,
counting from `p₀ = 2`. -/
noncomputable def primeGap (n : ℕ) : ℕ := (n + 1).nth Nat.Prime - n.nth Nat.Prime

/-- The normalised prime gap `(pₙ₊₁ - pₙ) / log n`. -/
noncomputable def normalizedGap (n : ℕ) : ℝ := primeGap n / Real.log n

/-- The set `𝕃` of (finite) limit points of the sequence `(pₙ₊₁ - pₙ) / log n`. -/
def limitPointSet : Set ℝ := {x : ℝ | MapClusterPt x atTop normalizedGap}

/-- **Corollary 1.3** (`log n` normalisation), *conditional on Merikoski's theorem*.
If `limitPointSet` has the four-point property (this hypothesis is Merikoski's theorem
[Me20, Theorem 1], stated exactly as `erdos_5.variants.merikoski` in Formal Conjectures), then
`λ(𝕃 ∩ [0, T]) ≥ (25 / 74) T - C` for some constant `C` and all `T`. -/
theorem exists_volume_limitPointSet_inter_Icc_ge_of_merikoski
    (merikoski : ∀ β : Fin 4 → ℝ, Monotone β → ∃ i j, i < j ∧ β j - β i ∈ limitPointSet) :
    ∃ C : ℝ, ∀ T : ℝ,
      ENNReal.ofReal (25 / 74 * T - C) ≤ volume (limitPointSet ∩ Icc 0 T) := by
  sorry

/-- **Corollary 1.3** (`log n` normalisation), *conditional on Merikoski's theorem*:
`λ(𝕃 ∩ [0, T]) ≥ (76 / 225) T` for all sufficiently large `T`. -/
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
[Me20, Theorem 1], which is stated in [Me20] for this normalisation:
`λ(𝕃 ∩ [0, T]) ≥ (25 / 74) T - C` for some constant `C` and all `T`. -/
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

end Erdos5
