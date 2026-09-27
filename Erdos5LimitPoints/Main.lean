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

/-- Enlarging a set preserves the four-point property. -/
lemma _root_.Erdos5.HasFourPointProperty.mono {B B' : Set ℝ} (hB : HasFourPointProperty B)
    (h : B ⊆ B') : HasFourPointProperty B' := fun β hβ => by
  obtain ⟨i, j, hij, hmem⟩ := hB β hβ
  exact ⟨i, j, hij, h hmem⟩

/-- **Lemma 2.2.** If there is no `G`-triangle, then
`λ(B ∩ [0, T]) ≥ (T - r) / 2` for some `r ≥ 0` and all `T`. -/
theorem exists_volume_ge_of_no_triangle {B : Set ℝ}
    (h : ∀ r₁ r₂ : ℝ, 0 < r₁ → r₁ < r₂ → r₁ ∉ B → r₂ ∉ B → r₂ - r₁ ∉ B → False) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ T : ℝ, ENNReal.ofReal ((T - r) / 2) ≤ volume (B ∩ Icc 0 T) := by
  by_cases hG : ∃ r, 0 < r ∧ r ∉ B
  · obtain ⟨r, hr, hrB⟩ := hG
    refine ⟨r, hr.le, fun T => ?_⟩
    -- every `t ∈ (r, T]` has `t ∈ B` or `t - r ∈ B`
    have hcover : Ioc r T ⊆ (B ∩ Icc 0 T) ∪ (fun t => t + -r) ⁻¹' (B ∩ Icc 0 T) := by
      rintro t ⟨hrt, htT⟩
      by_cases ht : t ∈ B
      · exact Or.inl ⟨ht, by linarith, htT⟩
      · by_cases htr : t - r ∈ B
        · exact Or.inr ⟨by simpa [sub_eq_add_neg] using htr, by linarith, by linarith⟩
        · exact (h r t hr hrt hrB ht htr).elim
    have key : ENNReal.ofReal (T - r) ≤ 2 * volume (B ∩ Icc 0 T) := by
      calc ENNReal.ofReal (T - r) = volume (Ioc r T) := by rw [Real.volume_Ioc]
        _ ≤ volume (B ∩ Icc 0 T) + volume ((fun t => t + -r) ⁻¹' (B ∩ Icc 0 T)) :=
          (measure_mono hcover).trans (measure_union_le _ _)
        _ = 2 * volume (B ∩ Icc 0 T) := by rw [measure_preimage_add_right, two_mul]
    rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.div_le_iff (by norm_num) (by norm_num),
      ENNReal.ofReal_ofNat, mul_comm]
    exact key
  · push Not at hG
    refine ⟨0, le_rfl, fun T => ?_⟩
    rcases le_or_gt T 0 with hT | hT
    · rw [ENNReal.ofReal_of_nonpos (by linarith)]
      exact bot_le
    calc ENNReal.ofReal ((T - 0) / 2) ≤ ENNReal.ofReal T :=
          ENNReal.ofReal_le_ofReal (by linarith)
      _ = volume (Ioc 0 T) := by rw [Real.volume_Ioc, sub_zero]
      _ ≤ volume (B ∩ Icc 0 T) :=
          measure_mono fun t ht => ⟨hG t ht.1, ht.1.le, ht.2⟩

/-- Theorem 1.2 for measurable sets. -/
theorem exists_volume_inter_Icc_ge_of_measurableSet {B : Set ℝ} (hB : HasFourPointProperty B)
    (hmeas : MeasurableSet B) :
    ∃ C : ℝ, ∀ T : ℝ, ENNReal.ofReal (25 / 74 * T - C) ≤ volume (B ∩ Icc 0 T) := by
  by_cases htri : ∃ r₁ r₂ : ℝ, 0 < r₁ ∧ r₁ < r₂ ∧ r₁ ∉ B ∧ r₂ ∉ B ∧ r₂ - r₁ ∉ B
  · obtain ⟨r₁, r₂, h0, h12, h1, h2, h3⟩ := htri
    let S : Setting := ⟨B, r₁, r₂, hmeas, hB, h0, h12, h1, h2, h3⟩
    obtain ⟨K, hK⟩ := S.exists_volume_E_ge
    refine ⟨(r₂ + K / 74) / 3, fun T => ?_⟩
    have h3T := S.ofReal_add_volume_E_le T
    have hsum : ENNReal.ofReal (T - r₂ + (T - K) / 74) ≤ 3 * volume (B ∩ Icc 0 T) :=
      ENNReal.ofReal_add_le.trans ((add_le_add le_rfl (hK T)).trans h3T)
    have : 25 / 74 * T - (r₂ + K / 74) / 3 = (T - r₂ + (T - K) / 74) / 3 := by ring
    rw [this, ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.div_le_iff (by norm_num)
      (by norm_num), ENNReal.ofReal_ofNat, mul_comm]
    exact hsum
  · push Not at htri
    obtain ⟨r, hr, hr'⟩ := exists_volume_ge_of_no_triangle
      fun r₁ r₂ h0 h12 h1 h2 h3 => h3 (htri r₁ r₂ h0 h12 h1 h2)
    refine ⟨r / 2, fun T => ?_⟩
    rcases le_or_gt T 0 with hT | hT
    · rw [ENNReal.ofReal_of_nonpos (by nlinarith)]
      exact bot_le
    · exact (ENNReal.ofReal_le_ofReal (by nlinarith)).trans (hr' T)

/-- **Theorem 1.2** (`O(1)` form). -/
theorem exists_volume_inter_Icc_ge {B : Set ℝ} (hB : HasFourPointProperty B) :
    ∃ C : ℝ, ∀ T : ℝ, ENNReal.ofReal (25 / 74 * T - C) ≤ volume (B ∩ Icc 0 T) := by
  obtain ⟨C, hC⟩ := exists_volume_inter_Icc_ge_of_measurableSet
    (hB.mono (subset_toMeasurable volume B)) (measurableSet_toMeasurable volume B)
  refine ⟨C, fun T => ?_⟩
  rw [← Measure.measure_toMeasurable_inter_of_sFinite measurableSet_Icc]
  exact hC T

/-- **Theorem 1.2** (`liminf` form). -/
theorem le_liminf_volume_inter_Icc_div {B : Set ℝ} (hB : HasFourPointProperty B) :
    (25 / 74 : ℝ≥0∞) ≤ liminf (fun T : ℝ => volume (B ∩ Icc 0 T) / ENNReal.ofReal T) atTop := by
  obtain ⟨C, hC⟩ := exists_volume_inter_Icc_ge hB
  have hlim : Tendsto (fun T : ℝ => ENNReal.ofReal (25 / 74 - C / T)) atTop
      (𝓝 (25 / 74 : ℝ≥0∞)) := by
    have : Tendsto (fun T : ℝ => 25 / 74 - C / T) atTop (𝓝 (25 / 74 - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_id)
    convert ENNReal.tendsto_ofReal this using 2
    rw [sub_zero, ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_ofNat]
  rw [← hlim.liminf_eq]
  refine liminf_le_liminf ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hT)) (Or.inl ENNReal.ofReal_ne_top),
    ← ENNReal.ofReal_mul' hT.le]
  refine le_trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_)) (hC T)
  field_simp

/-- **Corollary 1.3** for any set with the four-point property. -/
theorem eventually_volume_inter_Icc_ge {B : Set ℝ} (hB : HasFourPointProperty B) :
    ∀ᶠ T : ℝ in atTop, ENNReal.ofReal (76 / 225 * T) ≤ volume (B ∩ Icc 0 T) := by
  obtain ⟨C, hC⟩ := exists_volume_inter_Icc_ge hB
  filter_upwards [eventually_ge_atTop (16650 * C)] with T hT
  exact (ENNReal.ofReal_le_ofReal (by linarith)).trans (hC T)

end Erdos5.Main
