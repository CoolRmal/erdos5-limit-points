/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Erdos5LimitPoints.Setting

/-!
# Section 5: the four-point property forces additivity

* `Erdos5.k4`: Lemma 5.1 (the `K₄` lemma), a finite statement about labellings of the
  edges of `K₄` by `ℤ/3ℤ`.
* `Erdos5.Setting.kappa_triangle`: Lemma 5.2. If `y₀ < y₁ < y₂ < y₃` have consecutive gaps
  `> r₂` and all six differences are good, the phases of the differences form a coboundary.
* `Erdos5.Setting.kappa_add`: Proposition 5.3 (additivity of `κ` on certified points).
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos5

-- The `Decidable` instance of the statement below is larger than the default limit.
set_option synthInstance.maxSize 256 in
/-- **Lemma 5.1** (`K₄` lemma), normalised by `s₀ = 0`. If every `s ∈ (ℤ/3ℤ)⁴` with `s₀ = 0`
satisfies `sⱼ - sᵢ = kᵢⱼ` for some `i < j`, then `k` is a coboundary. -/
theorem k4 (k₀₁ k₀₂ k₀₃ k₁₂ k₁₃ k₂₃ : ZMod 3)
    (h : ∀ s₁ s₂ s₃ : ZMod 3, s₁ = k₀₁ ∨ s₂ = k₀₂ ∨ s₃ = k₀₃ ∨ s₂ - s₁ = k₁₂ ∨
      s₃ - s₁ = k₁₃ ∨ s₃ - s₂ = k₂₃) :
    k₀₂ = k₀₁ + k₁₂ ∧ k₀₃ = k₀₁ + k₁₃ ∧ k₀₃ = k₀₂ + k₂₃ ∧ k₁₃ = k₁₂ + k₂₃ := by
  revert k₀₁ k₀₂ k₀₃ k₁₂ k₁₃ k₂₃
  decide +kernel

/-- The lattice point `e(s) ∈ {(0, 0), (1, 0), (0, 1)}` of phase `s`, used in the proof of
Lemma 5.2. -/
def phaseRep (s : ZMod 3) : ℤ × ℤ := if s = 0 then (0, 0) else if s = 1 then (1, 0) else (0, 1)

lemma phaseRep_sub_mem_hexQ (s t : ZMod 3) : phaseRep t - phaseRep s ∈ hexQ := by
  revert s t; decide

lemma ph_phaseRep_sub (s t : ZMod 3) : ph (phaseRep t - phaseRep s) = t - s := by
  revert s t; decide

/-- Lebesgue measure is invariant under `x ↦ x - a`. -/
lemma volume_setOf_sub_mem (N : Set ℝ) (a : ℝ) : volume {x | x - a ∈ N} = volume N := by
  have : {x : ℝ | x - a ∈ N} = (fun h => h + -a) ⁻¹' N := by ext; simp [sub_eq_add_neg]
  rw [this, measure_preimage_add_right]

/-- Lebesgue measure is invariant under `x ↦ a - x`. -/
lemma volume_setOf_sub_mem' (N : Set ℝ) (a : ℝ) : volume {x | a - x ∈ N} = volume N := by
  have : {x : ℝ | a - x ∈ N} = Neg.neg ⁻¹' ((fun h => h + a) ⁻¹' N) := by
    ext; simp [sub_eq_neg_add]
  rw [this, Measure.measure_preimage_neg, measure_preimage_add_right]

/-- The measure-theoretic heart of Proposition 5.3: if `6 λ(N) < T - 6 c` and `0 ≤ u ≤ w ≤ T`,
there is `x ∈ [w - T, T]` at distance at least `c` from each of `0, u, w` such that neither
`x - a` nor `a - x` lies in `N` for `a ∈ {0, u, w}`. -/
lemma exists_far_point {N : Set ℝ} {c T u w : ℝ} (hc : 0 ≤ c) (huw : u ≤ w) (hwT : w ≤ T)
    (hN : 6 * volume N < ENNReal.ofReal (T - 6 * c)) :
    ∃ x ∈ Icc (w - T) T, ∀ a ∈ ({0, u, w} : Set ℝ),
      (x ≤ a - c ∨ a + c ≤ x) ∧ x - a ∉ N ∧ a - x ∉ N := by
  set G : Set ℝ := Ioo (0 - c) (0 + c) ∪ Ioo (u - c) (u + c) ∪ Ioo (w - c) (w + c) with hG_def
  set Bad : Set ℝ := ({x | x - 0 ∈ N} ∪ {x | 0 - x ∈ N}) ∪ ({x | x - u ∈ N} ∪ {x | u - x ∈ N}) ∪
    ({x | x - w ∈ N} ∪ {x | w - x ∈ N}) with hBad_def
  have hG : volume G ≤ ENNReal.ofReal (6 * c) := calc
    volume G ≤ volume (Ioo (0 - c) (0 + c)) + volume (Ioo (u - c) (u + c)) +
        volume (Ioo (w - c) (w + c)) := by
      refine (measure_union_le _ _).trans ?_
      gcongr
      exact measure_union_le _ _
    _ = ENNReal.ofReal (6 * c) := by
      simp only [Real.volume_Ioo, ← ENNReal.ofReal_add (by linarith : (0 : ℝ) ≤ 0 + c - (0 - c))
        (by linarith : (0 : ℝ) ≤ u + c - (u - c)),
        ← ENNReal.ofReal_add (by linarith : (0 : ℝ) ≤ 0 + c - (0 - c) + (u + c - (u - c)))
        (by linarith : (0 : ℝ) ≤ w + c - (w - c))]
      ring_nf
  have hBad : volume Bad ≤ 6 * volume N := by
    have h2 (a : ℝ) : volume ({x | x - a ∈ N} ∪ {x | a - x ∈ N}) ≤ 2 * volume N :=
      (measure_union_le _ _).trans_eq <| by
        rw [volume_setOf_sub_mem, volume_setOf_sub_mem', two_mul]
    calc volume Bad ≤ 2 * volume N + 2 * volume N + 2 * volume N :=
          (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
            (add_le_add (h2 0) (h2 u))) (h2 w))
      _ = 6 * volume N := by ring
  have hJ : ENNReal.ofReal (T - 6 * c) ≤ volume (Icc (w - T) T \ G) := by
    calc ENNReal.ofReal (T - 6 * c) ≤ ENNReal.ofReal (T - (w - T)) - ENNReal.ofReal (6 * c) := by
          rw [← ENNReal.ofReal_sub _ (by positivity)]
          exact ENNReal.ofReal_le_ofReal (by linarith)
      _ ≤ volume (Icc (w - T) T) - volume G := by
          rw [Real.volume_Icc]; exact tsub_le_tsub_left hG _
      _ ≤ volume (Icc (w - T) T \ G) := le_measure_sdiff
  obtain ⟨x, ⟨hxI, hxG⟩, hxB⟩ : ((Icc (w - T) T \ G) \ Bad).Nonempty := by
    rw [nonempty_iff_ne_empty, Ne, sdiff_eq_empty]
    exact fun h => (hN.trans_le (hJ.trans (measure_mono h))).not_ge hBad
  refine ⟨x, hxI, ?_⟩
  simp only [hG_def, hBad_def, mem_union, mem_ofPred_eq, not_or, mem_Ioo, not_and_or,
    not_lt] at hxG hxB
  intro a ha
  simp only [mem_insert_iff, mem_singleton_iff] at ha
  obtain rfl | rfl | rfl := ha
  · exact ⟨hxG.1.1, hxB.1.1⟩
  · exact ⟨hxG.1.2, hxB.1.2⟩
  · exact ⟨hxG.2, hxB.2⟩

namespace Setting

variable (S : Setting)

/-- `ρ(s) = m r₁ + n r₂`, where `(m, n) = e(s)`; it is one of `0, r₁, r₂`. -/
noncomputable def phaseShift (s : ZMod 3) : ℝ := (phaseRep s).1 * S.r₁ + (phaseRep s).2 * S.r₂

@[simp] lemma phaseShift_zero : S.phaseShift 0 = 0 := by simp [phaseShift, phaseRep]

lemma phaseShift_nonneg (s : ZMod 3) : 0 ≤ S.phaseShift s := by
  unfold phaseShift phaseRep
  split_ifs <;> simp [S.r₁_pos.le, S.r₂_pos.le]

lemma phaseShift_le (s : ZMod 3) : S.phaseShift s ≤ S.r₂ := by
  unfold phaseShift phaseRep
  split_ifs <;> simp [S.r₁_lt_r₂.le, S.r₂_pos.le]

/-- If `b - a` is good, then `(b + ρ(t)) - (a + ρ(s)) ∈ B` iff `t - s = κ(b - a)`. -/
lemma add_phaseShift_sub_mem_iff {a b : ℝ} (h : S.Good (b - a)) (s t : ZMod 3) :
    b + S.phaseShift t - (a + S.phaseShift s) ∈ S.B ↔ t - s = S.kappa (b - a) := by
  have heq : b + S.phaseShift t - (a + S.phaseShift s) =
      S.pt (b - a) (phaseRep t - phaseRep s).1 (phaseRep t - phaseRep s).2 := by
    simp only [phaseShift, pt, Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
    ring
  rw [heq, h _ (phaseRep_sub_mem_hexQ s t), ph_phaseRep_sub]

/-- **Lemma 5.2.** -/
theorem kappa_triangle {y₀ y₁ y₂ y₃ : ℝ} (h₀₁ : y₀ + S.r₂ < y₁) (h₁₂ : y₁ + S.r₂ < y₂)
    (h₂₃ : y₂ + S.r₂ < y₃) (g₀₁ : S.Good (y₁ - y₀)) (g₀₂ : S.Good (y₂ - y₀))
    (g₀₃ : S.Good (y₃ - y₀)) (g₁₂ : S.Good (y₂ - y₁)) (g₁₃ : S.Good (y₃ - y₁))
    (g₂₃ : S.Good (y₃ - y₂)) :
    S.kappa (y₂ - y₀) = S.kappa (y₁ - y₀) + S.kappa (y₂ - y₁) ∧
    S.kappa (y₃ - y₀) = S.kappa (y₁ - y₀) + S.kappa (y₃ - y₁) ∧
    S.kappa (y₃ - y₀) = S.kappa (y₂ - y₀) + S.kappa (y₃ - y₂) ∧
    S.kappa (y₃ - y₁) = S.kappa (y₂ - y₁) + S.kappa (y₃ - y₂) := by
  refine k4 _ _ _ _ _ _ fun s₁ s₂ s₃ => ?_
  have hle := S.phaseShift_le
  have hnn := S.phaseShift_nonneg
  obtain ⟨i, j, hij, hB⟩ := S.fourPoint ![y₀ + S.phaseShift 0, y₁ + S.phaseShift s₁,
      y₂ + S.phaseShift s₂, y₃ + S.phaseShift s₃] <| Fin.monotone_iff_le_succ.2 fun i => by
    fin_cases i <;> simp <;> linarith [hle s₁, hle s₂, hnn s₁, hnn s₂, hnn s₃]
  fin_cases i <;> fin_cases j <;> try exact absurd hij (by decide)
  · exact Or.inl <| (sub_zero s₁).symm.trans <| (S.add_phaseShift_sub_mem_iff g₀₁ 0 s₁).1 hB
  · exact Or.inr <| Or.inl <| (sub_zero s₂).symm.trans <|
      (S.add_phaseShift_sub_mem_iff g₀₂ 0 s₂).1 hB
  · exact Or.inr <| Or.inr <| Or.inl <| (sub_zero s₃).symm.trans <|
      (S.add_phaseShift_sub_mem_iff g₀₃ 0 s₃).1 hB
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl <| (S.add_phaseShift_sub_mem_iff g₁₂ s₁ s₂).1 hB
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <|
      (S.add_phaseShift_sub_mem_iff g₁₃ s₁ s₃).1 hB
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      (S.add_phaseShift_sub_mem_iff g₂₃ s₂ s₃).1 hB

/-- **Proposition 5.3** (additivity). Let `T' = T - 2 r₂` and suppose
`36 λ(E ∩ [0, T]) < T' - 6 c₀`. If `u, v ≥ c₀`, `u + v ≤ T'` and `u, v, u + v` are certified,
then `κ(u + v) = κ(u) + κ(v)`. -/
theorem kappa_add {T u v : ℝ}
    (hT : 36 * volume (S.E ∩ Icc 0 T) < ENNReal.ofReal (T - 2 * S.r₂ - 6 * S.c₀))
    (huv : u + v ≤ T - 2 * S.r₂) (hu : S.Certified u) (hv : S.Certified v)
    (huv' : S.Certified (u + v)) :
    S.kappa (u + v) = S.kappa u + S.kappa v := by
  have hr : S.r₂ < S.c₀ := by unfold c₀; linarith [S.r₂_pos]
  have hc := S.c₀_pos
  have hu₀ := hu.1
  have hv₀ := hv.1
  set N := {d | d ∈ Icc S.c₀ (T - 2 * S.r₂) ∧ ¬ S.Certified d}
  have hN : 6 * volume N < ENNReal.ofReal (T - 2 * S.r₂ - 6 * S.c₀) := by
    refine lt_of_le_of_lt ?_ hT
    calc 6 * volume N ≤ 6 * (6 * volume (S.E ∩ Icc 0 (T - 2 * S.r₂ + S.r₁ + S.r₂))) := by
          gcongr; exact S.volume_not_certified_le le_rfl
      _ ≤ 6 * (6 * volume (S.E ∩ Icc 0 T)) := by
          gcongr
          linarith [S.r₁_lt_r₂]
      _ = 36 * volume (S.E ∩ Icc 0 T) := by rw [← mul_assoc]; norm_num
  have cert : ∀ d, S.c₀ ≤ d → d ≤ T - 2 * S.r₂ → d ∉ N → S.Good d := fun d h₁ h₂ h₃ =>
    Certified.good S <| by_contra fun h => h₃ ⟨⟨h₁, h₂⟩, h⟩
  obtain ⟨x, ⟨hxl, hxr⟩, hx⟩ := exists_far_point S.c₀_pos.le (le_add_of_nonneg_right
    (S.c₀_pos.le.trans hv₀)) huv hN
  obtain ⟨h₀, h₀a, h₀b⟩ := hx 0 (by simp)
  obtain ⟨h₁, h₁a, h₁b⟩ := hx u (by simp)
  obtain ⟨h₂, h₂a, h₂b⟩ := hx (u + v) (by simp)
  have gu : S.Good (u - 0) := by rw [sub_zero]; exact hu.good
  have gv : S.Good (u + v - u) := by rw [add_sub_cancel_left]; exact hv.good
  have guv : S.Good (u + v - 0) := by rw [sub_zero]; exact huv'.good
  rcases h₀ with h₀ | h₀
  · -- `x < 0 < u < u + v`
    simpa using (S.kappa_triangle (y₀ := x) (by linarith) (by linarith) (by linarith)
      (cert _ (by linarith) (by linarith) h₀b) (cert _ (by linarith) (by linarith) h₁b)
      (cert _ (by linarith) (by linarith) h₂b) gu guv gv).2.2.2
  rcases h₁ with h₁ | h₁
  · -- `0 < x < u < u + v`
    simpa using (S.kappa_triangle (y₀ := 0) (y₁ := x) (by linarith) (by linarith) (by linarith)
      (cert _ (by linarith) (by linarith) h₀a) gu guv (cert _ (by linarith) (by linarith) h₁b)
      (cert _ (by linarith) (by linarith) h₂b) gv).2.2.1
  rcases h₂ with h₂ | h₂
  · -- `0 < u < x < u + v`
    simpa using (S.kappa_triangle (y₀ := 0) (y₂ := x) (by linarith) (by linarith) (by linarith)
      gu (cert _ (by linarith) (by linarith) h₀a) guv (cert _ (by linarith) (by linarith) h₁a)
      gv (cert _ (by linarith) (by linarith) h₂b)).2.1
  · -- `0 < u < u + v < x`
    simpa using (S.kappa_triangle (y₀ := 0) (y₃ := x) (by linarith) (by linarith) (by linarith)
      gu guv (cert _ (by linarith) (by linarith) h₀a) gv (cert _ (by linarith) (by linarith) h₁a)
      (cert _ (by linarith) (by linarith) h₂a)).1

end Setting

end Erdos5
