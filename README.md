# Limit points of normalised prime gaps: the constant 25/74

Lean 4 / Mathlib formalisation (work in progress) of the note
*More than one third of the positive reals are limit points of normalized prime gaps*,
which improves the constant 1/3 of Merikoski to 25/74 = 1/3 + 1/222 in the direction of
[Erdős Problem #5](https://www.erdosproblems.com/5).

* `Challenge.lean` — the statements of record (imports Mathlib only).
* `Solution.lean` — the same statements, with proofs from the library `Erdos5LimitPoints/`.
* `comparator.json` — configuration for `lake comparator`, run in CI.

Status: under active development; see the CI badge and the list of remaining `sorry`s.
