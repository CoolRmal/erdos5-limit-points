# Limit points of normalised prime gaps: the constant 25/74

[![CI](https://github.com/CoolRmal/erdos5-limit-points/actions/workflows/ci.yml/badge.svg)](https://github.com/CoolRmal/erdos5-limit-points/actions/workflows/ci.yml)

A Lean 4 / Mathlib formalisation of the main theorem (Theorem 1.2) of the note

> *More than one third of the positive reals are limit points of normalized prime gaps*
> (draft, September 2026)

which improves, in the direction of [Erdős Problem #5](https://www.erdosproblems.com/5), the
constant `1/3` of Merikoski [Me20] to `25/74 = 1/3 + 1/222`. The note's Corollary 1.3 about
prime gaps is proved conditionally on Merikoski's theorem [Me20, Theorem 1], which is taken as
a hypothesis.

## The mathematics

Let `pₙ` be the `n`-th prime and let `𝕃` be the set of limit points of the normalised prime gaps
`(pₙ₊₁ − pₙ) / log n` (equivalently, of `(pₙ₊₁ − pₙ) / log pₙ`; see below). Erdős asked whether
`𝕃 = [0, ∞]` (for the finite limit points: `𝕃 = [0, ∞)`). A set `B ⊆ ℝ` has the **four-point property** if for all reals
`β₁ ≤ β₂ ≤ β₃ ≤ β₄` one of the six differences `βⱼ − βᵢ` (`i < j`) lies in `B`.
Merikoski [Me20, Theorem 1] proved, using the Maynard–Tao sieve, that `𝕃` has the four-point
property, and deduced `λ(𝕃 ∩ [0, T]) ≥ T/3` for all `T > 0` (`λ` = Lebesgue measure). The bound
`1/3` is sharp for sets with the four-point property at any single scale `T`.

The note proves that asymptotically `1/3` is not sharp (Theorem 1.2 of the note, stated there
for Lebesgue-measurable `B ⊆ [0, ∞)` and in the `liminf` form; the formalisation proves it for
arbitrary `B ⊆ ℝ` and in the `O(1)` form):

> **Theorem.** If `B ⊆ ℝ` has the four-point property, then
> `liminf_{T→∞} λ(B ∩ [0, T]) / T ≥ 25/74`; in fact `λ(B ∩ [0, T]) ≥ (25/74) T − C` for a
> constant `C = C(B)` and all `T`.

Combined with Merikoski's theorem this gives `λ(𝕃 ∩ [0, T]) ≥ (76/225) T` for all large `T`.
The proof is purely measure-theoretic; its only analytic input is a rearrangement-type
inequality on the circle `ℝ / 3ℤ`.

## What is formalised

The statements of record are in [`Challenge.lean`](Challenge.lean) (imports Mathlib only, about
150 lines). [`Solution.lean`](Solution.lean) proves them from the library
[`Erdos5LimitPoints/`](Erdos5LimitPoints). `lake comparator` (configuration in
[`comparator.json`](comparator.json)) checks that the solution proves exactly the challenge
statements using only the axioms `propext`, `Quot.sound`, `Classical.choice`; this runs in CI.

| Declaration (`Challenge.lean`) | Content |
|---|---|
| `Erdos5.HasFourPointProperty` | the four-point property of a set `B ⊆ ℝ` |
| `Erdos5.HasFourPointProperty.exists_volume_inter_Icc_ge` | **Theorem 1.2**, `O(1)` form: `∃ C, ∀ T, λ(B ∩ [0,T]) ≥ (25/74) T − C` |
| `Erdos5.HasFourPointProperty.le_liminf_volume_inter_Icc_div` | **Theorem 1.2**: `liminf λ(B ∩ [0,T]) / T ≥ 25/74` (in `ℝ≥0∞`) |
| `Erdos5.limitPointSet` | limit points of `(pₙ₊₁ − pₙ) / log n` (verbatim from Formal Conjectures) |
| `Erdos5.exists_volume_limitPointSet_inter_Icc_ge_of_merikoski` | **Corollary 1.3** (`O(1)` form), assuming Merikoski's theorem |
| `Erdos5.eventually_volume_limitPointSet_inter_Icc_ge_of_merikoski` | **Corollary 1.3**: `λ(𝕃 ∩ [0,T]) ≥ (76/225) T` for large `T`, assuming Merikoski's theorem |
| `Erdos5.limitPointSetLogPrime`, `…LogPrime…_of_merikoski` | the same for the normalisation `(pₙ₊₁ − pₙ) / log pₙ` of [Me20] |
| `Erdos5.limitPointSet_eq_limitPointSetLogPrime` | the two normalisations have the same limit points (unconditional) |

**Important scope note.** Merikoski's theorem (the four-point property of `𝕃`) is a deep result
of sieve theory and is **not** formalised here. The corollaries about prime gaps take it as an
explicit hypothesis `merikoski`, stated exactly as `erdos_5.variants.merikoski` in the
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/5.lean)
project (for the `log n` normalisation) and as in [Me20] (for the `log pₙ` normalisation). The
main theorem about sets with the four-point property is proved unconditionally. There are no
`sorry`s and no custom axioms anywhere in the development.

Conventions: `pₙ = Nat.nth Nat.Prime n` with `p₀ = 2`; `𝕃` contains only the finite limit
points; `volume` is Lebesgue (outer) measure, so no measurability assumption on `B` is needed.

## Proof outline and map of the library

| Paper | Lean |
|---|---|
| Lemma 2.1 (`0 ∈ B`), Lemma 3.1, Lemma 3.2, Section 4 (hexagon lemma, Lemmas 4.2–4.6) | [`Setting.lean`](Erdos5LimitPoints/Setting.lean) |
| Section 5: `K₄` lemma (5.1), Lemma 5.2, Proposition 5.3 (additivity) | [`Additivity.lean`](Erdos5LimitPoints/Additivity.lean) |
| Pollard's theorem in `ℤ/pℤ` (used for Section 6) | [`Pollard.lean`](Erdos5LimitPoints/Pollard.lean) |
| Pollard's inequality on the circle (replaces Theorem 6.1) | [`CirclePollard.lean`](Erdos5LimitPoints/CirclePollard.lean) |
| Lemma 6.3 (circle lemma) | [`CircleLemma.lean`](Erdos5LimitPoints/CircleLemma.lean) |
| Section 7 (Lemmas 7.1, 7.3, Corollary 7.4) | [`LocalContradiction.lean`](Erdos5LimitPoints/LocalContradiction.lean) |
| Section 8 (averaging; Proposition 3.3) | [`Averaging.lean`](Erdos5LimitPoints/Averaging.lean) |
| Lemma 2.2, Theorem 1.2, Corollary 1.3 | [`Main.lean`](Erdos5LimitPoints/Main.lean) |
| `log pₙ / log n → 1` and equality of the two limit point sets | [`Normalization.lean`](Erdos5LimitPoints/Normalization.lean) |

### Differences from the paper

The formalisation follows the note closely, with these deliberate changes:

1. **No Riesz–Sobolev.** The note derives the circle lemma (Lemma 6.3) from the Riesz–Sobolev
   rearrangement inequality on the circle (Baernstein, Friedberg–Luttinger), which is not in
   Mathlib. We instead prove the continuous analogue of **Pollard's theorem** on the circle,
   `∫ min(𝟙_A * 𝟙_B, t) ≥ min(tλ(Γ), t(λA + λB − t), λA λB)`, by discretising at primes
   `N → ∞` and applying Pollard's theorem in `ℤ/Nℤ` [Po74] (proved following [HS08]). The
   circle lemma then follows by a short argument (for `a ∈ ℤ/3ℤ` the contribution is
   `∫ r G ≤ 3α/2 + 3/4` with `α = λ(K₁⁻¹(a))`; summing over `a` gives `27/4`). The constant
   `3/4` of Lemma 6.3 is unchanged.
2. **`c₀ = 7 r₂` instead of `3 r₂`.** With this choice every point of Section 8 can be compared
   with the same reference point, so the averaging argument gives `λ(E ∩ [0,T]) ≥ L/74` with no
   correction term. The constant `25/74` is unchanged.
3. **Stronger statement.** Theorem 1.2 is proved in the form `λ(B ∩ [0,T]) ≥ (25/74) T − C`
   (which the paper's proof gives), for arbitrary sets `B ⊆ ℝ` (no measurability, no
   `B ⊆ [0, ∞)`).
4. In Section 8 the averaging over `(p, q)` uses the joint density
   `(k+1) L⁻² ((P+Q)/L)^(k−1)` with `k = 24/13` directly rather than the `(S, V)`
   parametrisation; the marginals are the paper's `m` and `σ`.

## Building and checking

```bash
lake exe cache get
```

```bash
lake build
```

```bash
lake comparator --config comparator.json
```

`lake comparator` ships with the Lean toolchain (v4.35.0-rc3) and requires `bubblewrap` (Linux);
see [`.github/workflows/ci.yml`](.github/workflows/ci.yml), which runs it with `--paranoid`
(Lean kernel plus all bundled external checkers, including NanoDa).

## Provenance and AI disclosure

The Lean formalisation was produced by an AI agent (Claude Opus 5.5, Anthropic, in Claude Code
with parallel sub-agents) from the PDF of the note, under the direction of the repository
owner, who is the responsible maintainer. The note itself states that it was prepared with
substantial AI assistance. See [`formalization.yaml`](formalization.yaml) for structured
metadata. The proofs are machine-checked by Lean (and by the external kernels run by
`lake comparator --paranoid`); the faithfulness of the formal statements in `Challenge.lean` to
the note should be audited by a human reader.

## References

* [Me20] J. Merikoski, *Limit points of normalized prime gaps*, J. Lond. Math. Soc. (2) **102**
  (2020), 99–124.
* [Po74] J. M. Pollard, *A generalisation of the theorem of Cauchy and Davenport*, J. London
  Math. Soc. (2) **8** (1974), 460–462.
* [HS08] Y. O. Hamidoune, O. Serra, *A note on Pollard's theorem*, arXiv:0804.2593.
* [EP5] T. F. Bloom, *Erdős Problem #5*, <https://www.erdosproblems.com/5>.
* [CI] M. Christ, M. Iliopoulou, *Inequalities of Riesz–Sobolev type for compact connected
  abelian groups*, Amer. J. Math., arXiv:1808.08368.

## License

Apache-2.0, see [`LICENSE`](LICENSE).
