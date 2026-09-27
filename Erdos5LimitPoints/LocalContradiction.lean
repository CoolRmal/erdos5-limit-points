/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Erdos5LimitPoints.Additivity
import Erdos5LimitPoints.CircleLemma

/-!
# Section 7: the local contradiction

Fix `p, q ≥ c₀` with `p + q` not too large. For `z, w ∈ [0, 3)` put `u = p + z r₁`,
`v = q + w r₁`, and let `y ∈ [0, 3)` be `z + w` reduced modulo `3`, `x_y = p + q + y r₁`,
`x'_y = x_y + 3 r₁`; thus `u + v = x_y` if `z + w < 3` and `u + v = x'_y` otherwise.

We define three functions `K₁, K₂, K₃ : [0, 3) → ℤ/3ℤ` (`Setting.K₁raw`, `Setting.K₂raw`,
`Setting.K₃raw`) and the notion of an *admissible* pair `(z, w)` (`Setting.Admissible`), and show:

* `Setting.K₂raw_add_one`: `K₂` satisfies `K₂(ω + 1) = K₂(ω) - 1` on the circle `ℝ / 3ℤ`
  (Lemma 7.1);
* `Setting.K₃raw_eq_of_admissible`: for admissible `(z, w)`, `K₃(y) = K₁(z) + K₂(w)`
  (Lemma 7.3);
* `Setting.volume_not_admissible`: at least a quarter of the pairs `(z, w) ∈ [0, 3)²` are not
  admissible (Corollary 7.4), by the circle lemma.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos5.Setting

variable (S : Setting)

/-- `K₁(z) = κ(p + z r₁)` if this point is certified, and `0` otherwise. -/
noncomputable def K₁raw (p z : ℝ) : ZMod 3 := by
  classical
  exact if S.Certified (p + z * S.r₁) then S.kappa (p + z * S.r₁) else 0

/-- The value of `K₂` on the orbit `w' + {0, 1, 2}` is determined by `base q w'`: if `j₀` is the
least `j ∈ {0, 1, 2}` such that `q + (w' + j) r₁` is certified, then
`base q w' = κ(q + (w' + j₀) r₁) + j₀`, and `base q w' = 0` if there is no such `j`. -/
noncomputable def base (q w' : ℝ) : ZMod 3 := by
  classical
  exact if S.Certified (q + w' * S.r₁) then S.kappa (q + w' * S.r₁)
    else if S.Certified (q + (w' + 1) * S.r₁) then S.kappa (q + (w' + 1) * S.r₁) + 1
    else if S.Certified (q + (w' + 2) * S.r₁) then S.kappa (q + (w' + 2) * S.r₁) + 2
    else 0

/-- `K₂(ω) = base(ω - ⌊ω⌋) - ⌊ω⌋`. -/
noncomputable def K₂raw (q ω : ℝ) : ZMod 3 := S.base q (ω - ⌊ω⌋) - (⌊ω⌋ : ZMod 3)

/-- `K₃(y)`: the phase of the *preferred* point among `x_y, x'_y` if it is certified, else of
the other one if that is certified, else `0`. The preferred point is `x_y` if `y ≥ 3/2` and
`x'_y` if `y < 3/2`. -/
noncomputable def K₃raw (p q y : ℝ) : ZMod 3 := by
  classical
  exact
    if 3 / 2 ≤ y then
      (if S.Certified (p + q + y * S.r₁) then S.kappa (p + q + y * S.r₁)
        else if S.Certified (p + q + (y + 3) * S.r₁) then S.kappa (p + q + (y + 3) * S.r₁)
        else 0)
    else
      (if S.Certified (p + q + (y + 3) * S.r₁) then S.kappa (p + q + (y + 3) * S.r₁)
        else if S.Certified (p + q + y * S.r₁) then S.kappa (p + q + y * S.r₁)
        else 0)

/-- The bridge holds at `x` if the equations hold at `x⟨2, 0⟩` and `x⟨3, -1⟩`. -/
def Bridge (x : ℝ) : Prop := S.EqHolds (x + 2 * S.r₁) ∧ S.EqHolds (x + 3 * S.r₁ - S.r₂)

/-- The pair `(z, w)` is *admissible* (Definition 7.2): `u`, `v` and `u + v` are certified, and in
the non-preferred case (`z + w < 3/2`, or `z + w ≥ 9/2`) either the other point of
`{x_y, x'_y}` is not certified or the bridge holds at `x_y`. -/
def Admissible (p q z w : ℝ) : Prop :=
  S.Certified (p + z * S.r₁) ∧ S.Certified (q + w * S.r₁) ∧
    S.Certified (p + q + (z + w) * S.r₁) ∧
    (z + w < 3 / 2 → ¬ S.Certified (p + q + (z + w + 3) * S.r₁) ∨
      S.Bridge (p + q + (z + w) * S.r₁)) ∧
    (9 / 2 ≤ z + w → ¬ S.Certified (p + q + (z + w - 3) * S.r₁) ∨
      S.Bridge (p + q + (z + w - 3) * S.r₁))

/-- **Lemma 7.1**, second part: `K₂(ω + 1) = K₂(ω) - 1`. -/
theorem K₂raw_add_one (q ω : ℝ) : S.K₂raw q (ω + 1) = S.K₂raw q ω - 1 := by
  sorry

/-- **Lemma 7.1**, first part: `K₂(w) = κ(q + w r₁)` whenever `q + w r₁` is certified,
for `w ∈ [0, 3)`. -/
theorem K₂raw_eq_kappa {q w : ℝ} (hw : w ∈ Ico (0 : ℝ) 3) (hc : S.Certified (q + w * S.r₁)) :
    S.K₂raw q w = S.kappa (q + w * S.r₁) := by
  sorry

/-- **Lemma 7.3.** Under the smallness hypothesis of Proposition 5.3, for `p, q` with
`p + q + 6 r₁ ≤ T - 2 r₂` and admissible `(z, w) ∈ [0, 3)²`, `K₃(y) = K₁(z) + K₂(w)` where
`y ≡ z + w (mod 3)`. -/
theorem K₃raw_eq_of_admissible {T p q z w : ℝ}
    (hT : 36 * volume (S.E ∩ Icc 0 T) < ENNReal.ofReal (T - 2 * S.r₂ - 6 * S.c₀))
    (hpq : p + q + 6 * S.r₁ ≤ T - 2 * S.r₂) (hz : z ∈ Ico (0 : ℝ) 3) (hw : w ∈ Ico (0 : ℝ) 3)
    (h : S.Admissible p q z w) :
    S.K₃raw p q (if z + w < 3 then z + w else z + w - 3) = S.K₁raw p z + S.K₂raw q w := by
  sorry

/-- **Corollary 7.4.** At least a quarter of the pairs `(z, w) ∈ [0, 3)²` are not admissible. -/
theorem volume_not_admissible {T p q : ℝ}
    (hT : 36 * volume (S.E ∩ Icc 0 T) < ENNReal.ofReal (T - 2 * S.r₂ - 6 * S.c₀))
    (hpq : p + q + 6 * S.r₁ ≤ T - 2 * S.r₂) :
    ENNReal.ofReal (9 / 4) ≤
      volume {x : ℝ × ℝ | x ∈ Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3 ∧ ¬ S.Admissible p q x.1 x.2} := by
  sorry

end Erdos5.Setting
