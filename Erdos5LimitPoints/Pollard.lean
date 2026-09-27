/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Mathlib

/-!
# Pollard's theorem

For finite sets `A, B` in `ZMod p` (`p` prime) and `x : ZMod p`, let `rep A B x` be the number
of representations `x = a + b` with `a ∈ A`, `b ∈ B`. Pollard's theorem [Po74] states that

  `∑ₓ min (rep A B x) t ≥ t * min p (|A| + |B| - t)`   for `t ≤ min |A| |B|`.

(For `t = 1` this is the Cauchy–Davenport theorem.) We follow the proof by induction on
`min |A| |B|` via the Dyson transform, as presented in [HS08, Lemma 3].

## References

* [Po74] J. M. Pollard, *A generalisation of the theorem of Cauchy and Davenport*,
  J. London Math. Soc. (2) 8 (1974), 460–462.
* [HS08] Y. O. Hamidoune, O. Serra, *A note on Pollard's theorem*, arXiv:0804.2593.
-/

open Finset

namespace Erdos5.Pollard

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The number of representations of `x` as `a + b` with `a ∈ A` and `b ∈ B`. -/
def rep (A B : Finset G) (x : G) : ℕ := #{a ∈ A | x - a ∈ B}

/-- **Pollard's theorem** for `ZMod p`, `p` prime. -/
theorem pollard {p : ℕ} [Fact p.Prime] (A B : Finset (ZMod p)) (t : ℕ) (hA : t ≤ #A)
    (hB : t ≤ #B) : t * min p (#A + #B - t) ≤ ∑ x, min (rep A B x) t := by
  sorry

/-- Pollard's theorem without size restrictions on `t`. -/
theorem pollard' {p : ℕ} [Fact p.Prime] (A B : Finset (ZMod p)) (t : ℕ) :
    min (t * p) (min (t * (#A + #B - t)) (#A * #B)) ≤ ∑ x, min (rep A B x) t := by
  sorry

end Erdos5.Pollard
