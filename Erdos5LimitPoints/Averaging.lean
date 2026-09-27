/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Erdos5LimitPoints.LocalContradiction

/-!
# Section 8: averaging, and the proof of Proposition 3.3

We average Corollary 7.4 over `(p, q) = (c₀ + P, c₀ + Q)`, where `(P, Q)` ranges over the
triangle `P, Q ≥ 0`, `P + Q ≤ L` with the weight
`ρ(P, Q) = (k + 1) L⁻² ((P + Q) / L) ^ (k - 1)`, `k = 24 / 13`.
Then `P` (and `Q`) has density `L⁻¹ m(P / L)` with `m(ξ) = (k + 1) / k (1 - ξ ^ k)`, and `P + Q`
has density `L⁻¹ σ(S / L)` with `σ(ξ) = (k + 1) ξ ^ k`; the choice of `k` makes
`12 m + (13 / 2) σ ≡ 37 / 2`. Bounding the probability of non-admissibility by the expected
number of the events `a point lies in E` gives `1 / 4 ≤ (37 / 2) λ(E ∩ [0, T]) / L`, i.e.
`λ(E ∩ [0, T]) ≥ L / 74 = T / 74 - O(1)`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos5.Setting

variable (S : Setting)

/-- **Proposition 3.3.** There is a constant `K` (depending on `r₁, r₂`) such that
`λ(E ∩ [0, T]) ≥ (T - K) / 74` for all `T`. -/
theorem exists_volume_E_ge : ∃ K : ℝ, ∀ T : ℝ,
    ENNReal.ofReal ((T - K) / 74) ≤ volume (S.E ∩ Icc 0 T) := by
  sorry

end Erdos5.Setting
