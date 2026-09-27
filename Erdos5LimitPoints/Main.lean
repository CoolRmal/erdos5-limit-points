/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Erdos5LimitPoints.Averaging

/-!
# The main theorem

* `Erdos5.Main.exists_volume_ge_of_no_triangle`: Lemma 2.2 (the case without `G`-triangle).
* `Erdos5.Main.exists_volume_inter_Icc_ge`: Theorem 1.2 in the form
  `λ(B ∩ [0, T]) ≥ (25 / 74) T - C`, for any set `B` with the four-point property
  (no measurability assumption).
* `Erdos5.Main.le_liminf_volume_inter_Icc_div`: Theorem 1.2 in `liminf` form.
* `Erdos5.Main.eventually_volume_inter_Icc_ge`: the bound `(76 / 225) T` for large `T`
  (Corollary 1.3, for any set with the four-point property).
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Erdos5.Main

/-- **Lemma 2.2.** If `B` has the four-point property and there is no `G`-triangle, then
`λ(B ∩ [0, T]) ≥ (T - r) / 2` for some `r ≥ 0` and all `T`. -/
theorem exists_volume_ge_of_no_triangle {B : Set ℝ} (hB : HasFourPointProperty B)
    (h : ∀ r₁ r₂ : ℝ, 0 < r₁ → r₁ < r₂ → r₁ ∉ B → r₂ ∉ B → r₂ - r₁ ∉ B → False) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ T : ℝ, ENNReal.ofReal ((T - r) / 2) ≤ volume (B ∩ Icc 0 T) := by
  sorry

/-- Theorem 1.2 for measurable sets. -/
theorem exists_volume_inter_Icc_ge_of_measurableSet {B : Set ℝ} (hB : HasFourPointProperty B)
    (hmeas : MeasurableSet B) :
    ∃ C : ℝ, ∀ T : ℝ, ENNReal.ofReal (25 / 74 * T - C) ≤ volume (B ∩ Icc 0 T) := by
  sorry

/-- **Theorem 1.2** (`O(1)` form). -/
theorem exists_volume_inter_Icc_ge {B : Set ℝ} (hB : HasFourPointProperty B) :
    ∃ C : ℝ, ∀ T : ℝ, ENNReal.ofReal (25 / 74 * T - C) ≤ volume (B ∩ Icc 0 T) := by
  sorry

/-- **Theorem 1.2** (`liminf` form). -/
theorem le_liminf_volume_inter_Icc_div {B : Set ℝ} (hB : HasFourPointProperty B) :
    (25 / 74 : ℝ≥0∞) ≤ liminf (fun T : ℝ => volume (B ∩ Icc 0 T) / ENNReal.ofReal T) atTop := by
  sorry

/-- **Corollary 1.3** for any set with the four-point property. -/
theorem eventually_volume_inter_Icc_ge {B : Set ℝ} (hB : HasFourPointProperty B) :
    ∀ᶠ T : ℝ in atTop, ENNReal.ofReal (76 / 225 * T) ≤ volume (B ∩ Icc 0 T) := by
  sorry

end Erdos5.Main
