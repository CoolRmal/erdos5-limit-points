/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Erdos5LimitPoints.CirclePollard

/-!
# The circle lemma

Let `Γ = ℝ / 3ℤ` with Haar measure `λ` of total mass `3`. The following is Lemma 6.3 of the
paper, in the form used in Section 7: if `K₁, K₂, K₃ : Γ → ℤ/3ℤ` are measurable and
`K₂(ω + 1) = K₂(ω) - 1` for all `ω` (so that the three level sets of `K₂` are translates of each
other and each has measure `1`), then

  `λ ⊗ λ {(z, w) | K₃ (z + w) = K₁ z + K₂ w} ≤ 27 / 4`,

i.e. for independent uniform `z, w` the identity `K₃(z + w) = K₁(z) + K₂(w)` holds with
probability at most `3 / 4`.

The paper deduces this from the Riesz–Sobolev rearrangement inequality on the circle. We use
instead Pollard's inequality on the circle (`Erdos5.Circle.circle_pollard`): writing
`A = K₁⁻¹(a)` and `B₀ = K₂⁻¹(0)`, the contribution of `a` equals `∫ r G` where `r = 𝟙_A * 𝟙_{B₀}`
and `0 ≤ G ≤ 3` with `∫ G = 3`; the pointwise inequality `r G + 3 min(r, t) ≤ 3 r + t G` and
Pollard's inequality at level `t = λ(A) / 2` give `∫ r G ≤ 3 / 4 + 3 / 2 λ(A)`, which sums to
`27 / 4` over `a`.

## Main statements

* `Erdos5.Circle.volume_setOf_eq_setLIntegral_conv`: the measure of
  `{(z, w) | z ∈ A, w + c ∈ B, z + w ∈ C}` is the integral of `𝟙_A * 𝟙_B` over `C + c`.
* `Erdos5.Circle.lintegral_conv_mul_le`: the key estimate `∫ (𝟙_A * 𝟙_B) G ≤ 3 / 4 + 3 / 2 λ(A)`
  for `λ(B) = 1` and a weight `0 ≤ G ≤ 3` with `∫ G ≤ 3`.
* `Erdos5.Circle.circle_lemma`: the circle lemma.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos5.Circle

instance : Fact (0 < (3 : ℝ)) := ⟨by norm_num⟩

section Conv

variable {T : ℝ} [Fact (0 < T)] {A B C : Set (AddCircle T)}

/-- The measure of `{(z, w) | z ∈ A, w + c ∈ B, z + w ∈ C}` is the integral of the convolution
`𝟙_A * 𝟙_B` over the translate `C + c`. -/
theorem volume_setOf_eq_setLIntegral_conv (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (c : AddCircle T) :
    volume {p : AddCircle T × AddCircle T | p.1 ∈ A ∧ p.2 + c ∈ B ∧ p.1 + p.2 ∈ C} =
      ∫⁻ x in (· - c) ⁻¹' C, conv A B x := by
  set S : Set (AddCircle T × AddCircle T) := {p | p.1 ∈ A ∧ p.2 - p.1 ∈ B ∧ p.2 - c ∈ C}
  have hS : MeasurableSet S := (measurable_fst hA).inter
    (((measurable_snd.sub measurable_fst) hB).inter ((measurable_snd.sub_const c) hC))
  -- The map `(z, w) ↦ (z, z + w + c)` preserves the measure and pulls `S` back to our set.
  have hmp : MeasurePreserving (fun p : AddCircle T × AddCircle T => (p.1, p.1 + (p.2 + c)))
      volume volume :=
    (measurePreserving_prod_add volume volume).comp
      ((MeasurePreserving.id volume).prod (measurePreserving_add_right volume c))
  have hpre : {p : AddCircle T × AddCircle T | p.1 ∈ A ∧ p.2 + c ∈ B ∧ p.1 + p.2 ∈ C} =
      (fun p : AddCircle T × AddCircle T => (p.1, p.1 + (p.2 + c))) ⁻¹' S := by
    ext ⟨z, w⟩
    change z ∈ A ∧ w + c ∈ B ∧ z + w ∈ C ↔ z ∈ A ∧ z + (w + c) - z ∈ B ∧ z + (w + c) - c ∈ C
    rw [add_sub_cancel_left, ← add_assoc, add_sub_cancel_right]
  rw [hpre, hmp.measure_preimage hS.nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_apply_symm hS, ← lintegral_indicator ((measurable_sub_const c) hC)]
  refine lintegral_congr fun x => ?_
  by_cases hx : x - c ∈ C
  · rw [indicator_of_mem (show x ∈ (· - c) ⁻¹' C from hx), conv]
    congr 1 with y
    simp [S, hx]
  · simp [S, hx]

end Conv

/-- The pointwise inequality `r g + 3 min(r, t) ≤ 3 r + t g`, valid whenever `g ≤ 3`. -/
theorem mul_add_three_mul_min_le {r g t : ℝ≥0∞} (hg : g ≤ 3) :
    r * g + 3 * min r t ≤ 3 * r + t * g := by
  rcases le_total r t with h | h
  · rw [min_eq_left h, add_comm]
    gcongr
  · rw [min_eq_right h]
    obtain ⟨d, rfl⟩ := exists_add_of_le h
    calc (t + d) * g + 3 * t = t * g + 3 * t + d * g := by ring
      _ ≤ t * g + 3 * t + d * 3 := by gcongr
      _ = 3 * (t + d) + t * g := by ring

section Circle3

variable {A B : Set (AddCircle (3 : ℝ))}

/-- The key estimate: if `λ(B) = 1` and `G` is a weight with `0 ≤ G ≤ 3` and `∫ G ≤ 3`, then
`∫ (𝟙_A * 𝟙_B) G ≤ 3 / 4 + 3 / 2 λ(A)`. This combines the pointwise inequality
`mul_add_three_mul_min_le` with Pollard's inequality `circle_pollard` at level `t = λ(A) / 2`. -/
theorem lintegral_conv_mul_le (hA : MeasurableSet A) (hB : MeasurableSet B) (hB₁ : volume B = 1)
    {G : AddCircle (3 : ℝ) → ℝ≥0∞} (hGm : Measurable G) (hG : ∀ x, G x ≤ 3)
    (hGi : ∫⁻ x, G x ≤ 3) :
    ∫⁻ x, conv A B x * G x ≤ ENNReal.ofReal (3 / 4 + 3 / 2 * (volume A).toReal) := by
  set a := (volume A).toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hαa : volume A = ENNReal.ofReal a := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have e3 : (3 : ℝ≥0∞) = ENNReal.ofReal 3 := (ENNReal.ofReal_ofNat 3).symm
  set t := ENNReal.ofReal (a / 2)
  -- The total mass of `𝟙_A * 𝟙_B` is `λ(A) λ(B) = λ(A)`.
  have hconv : ∫⁻ x, conv A B x = volume A := by
    have h := volume_setOf_eq_setLIntegral_conv hA hB MeasurableSet.univ 0
    simp only [add_zero, mem_univ, and_true, preimage_univ, Measure.restrict_univ] at h
    rw [← h, Measure.volume_eq_prod]
    exact (Measure.prod_prod A B).trans (by rw [hB₁, mul_one])
  -- Integrate the pointwise inequality.
  have h₁ : (∫⁻ x, conv A B x * G x) + 3 * ∫⁻ x, min (conv A B x) t ≤ 3 * volume A + t * 3 :=
    calc (∫⁻ x, conv A B x * G x) + 3 * ∫⁻ x, min (conv A B x) t
        ≤ (∫⁻ x, conv A B x * G x) + ∫⁻ x, 3 * min (conv A B x) t := by
          gcongr; exact lintegral_const_mul_le _ _
      _ ≤ ∫⁻ x, (conv A B x * G x + 3 * min (conv A B x) t) := le_lintegral_add _ _
      _ ≤ ∫⁻ x, (3 * conv A B x + t * G x) :=
          lintegral_mono fun x => mul_add_three_mul_min_le (hG x)
      _ = 3 * (∫⁻ x, conv A B x) + t * ∫⁻ x, G x := by
          rw [lintegral_add_right _ (hGm.const_mul t), lintegral_const_mul' _ _ (by norm_num),
            lintegral_const_mul _ hGm]
      _ ≤ 3 * volume A + t * 3 := by
          rw [hconv]; gcongr
  -- Pollard's inequality at level `t = λ(A) / 2`.
  have h₂ := circle_pollard hA hB t
  rw [hB₁, mul_one] at h₂
  have h₃ : ENNReal.ofReal (a - 1 / 4) ≤
      min (t * ENNReal.ofReal 3) (min (t * (volume A + 1 - t)) (volume A)) := by
    rw [hαa]
    refine le_min ?_ (le_min ?_ ?_)
    · rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    · rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add ha zero_le_one,
        ← ENNReal.ofReal_sub _ (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (a - 1)])
    · exact ENNReal.ofReal_le_ofReal (by linarith)
  -- Combine the two bounds and cancel the finite term `3 (λ(A) - 1 / 4)`.
  have h₄ : (∫⁻ x, conv A B x * G x) + 3 * ENNReal.ofReal (a - 1 / 4) ≤
      ENNReal.ofReal (3 / 4 + 3 / 2 * a) + 3 * ENNReal.ofReal (a - 1 / 4) :=
    calc _ ≤ (∫⁻ x, conv A B x * G x) + 3 * ∫⁻ x, min (conv A B x) t := by
          gcongr; exact h₃.trans h₂
      _ ≤ 3 * volume A + t * 3 := h₁
      _ = ENNReal.ofReal (3 / 4 + 3 / 2 * a + 3 * (a - 1 / 4)) := by
          rw [hαa, e3, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
      _ ≤ ENNReal.ofReal (3 / 4 + 3 / 2 * a) + ENNReal.ofReal (3 * (a - 1 / 4)) :=
          ENNReal.ofReal_add_le
      _ = ENNReal.ofReal (3 / 4 + 3 / 2 * a) + 3 * ENNReal.ofReal (a - 1 / 4) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  exact ENNReal.le_of_add_le_add_right (by finiteness : 3 * ENNReal.ofReal (a - 1 / 4) ≠ ∞) h₄

/-- A version of `lintegral_conv_mul_le` for a family of at most three sets `C i` of total
measure at most `3`: `∑ᵢ ∫_{C i} 𝟙_A * 𝟙_B ≤ 3 / 4 + 3 / 2 λ(A)`. -/
theorem sum_setLIntegral_conv_le {ι : Type*} [Fintype ι] (hι : Fintype.card ι ≤ 3)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hB₁ : volume B = 1)
    {C : ι → Set (AddCircle (3 : ℝ))} (hC : ∀ i, MeasurableSet (C i))
    (hCs : ∑ i, volume (C i) ≤ 3) :
    ∑ i, ∫⁻ x in C i, conv A B x ≤ ENNReal.ofReal (3 / 4 + 3 / 2 * (volume A).toReal) := by
  set G : AddCircle (3 : ℝ) → ℝ≥0∞ := fun x => ∑ i, (C i).indicator 1 x
  have hGm : Measurable G := Finset.measurable_sum _ fun i _ => measurable_one.indicator (hC i)
  have hG : ∀ x, G x ≤ 3 := fun x =>
    calc G x ≤ ∑ _i : ι, (1 : ℝ≥0∞) := Finset.sum_le_sum fun i _ => by
          by_cases hx : x ∈ C i <;> simp [hx]
      _ ≤ 3 := by simpa using (Nat.cast_le (α := ℝ≥0∞)).2 hι
  have hGi : ∫⁻ x, G x ≤ 3 := by
    rw [lintegral_finsetSum _ fun i _ => measurable_one.indicator (hC i)]
    simpa [lintegral_indicator_one (hC _)] using hCs
  -- The convolution `𝟙_A * 𝟙_B` is measurable.
  have hconv : Measurable (conv A B) :=
    measurable_measure_prodMk_left
      (s := {p : AddCircle (3 : ℝ) × AddCircle (3 : ℝ) | p.2 ∈ A ∧ p.1 - p.2 ∈ B})
      ((measurable_snd hA).inter ((measurable_fst.sub measurable_snd) hB))
  have heq : ∑ i, ∫⁻ x in C i, conv A B x = ∫⁻ x, conv A B x * G x := by
    simp_rw [G, Finset.mul_sum]
    rw [lintegral_finsetSum (f := fun i x => conv A B x * (C i).indicator 1 x) _ fun i _ =>
      hconv.mul (measurable_one.indicator (hC i))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← lintegral_indicator (hC i)]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ C i <;> simp [hx]
  rw [heq]
  exact lintegral_conv_mul_le hA hB hB₁ hGm hG hGi

/-- The fibres of a map `K : ℝ / 3ℤ → ℤ / 3ℤ` with measurable fibres have total measure `3`. -/
theorem sum_volume_preimage_singleton {K : AddCircle (3 : ℝ) → ZMod 3}
    (hK : ∀ c, MeasurableSet (K ⁻¹' {c})) : ∑ c, volume (K ⁻¹' {c}) = 3 := by
  rw [sum_measure_preimage_singleton _ fun c _ => hK c, Finset.coe_univ, preimage_univ,
    AddCircle.measure_univ, ENNReal.ofReal_ofNat]

variable {K : AddCircle (3 : ℝ) → ZMod 3}

/-- If `K (ω + 1) = K ω - 1`, then `K (ω + n) = K ω - n`. -/
theorem apply_add_nsmul_one (hK : ∀ ω, K (ω + ((1 : ℝ) : AddCircle (3 : ℝ))) = K ω - 1)
    (ω : AddCircle (3 : ℝ)) (n : ℕ) :
    K (ω + n • ((1 : ℝ) : AddCircle (3 : ℝ))) = K ω - n := by
  induction n with
  | zero =>
    rw [zero_nsmul, add_zero, Nat.cast_zero]
    exact (sub_zero _).symm
  | succ n ih => rw [succ_nsmul, ← add_assoc, hK, ih]; push_cast; ring

/-- If `K (ω + 1) = K ω - 1`, then `K ω = b` if and only if `K (ω + b) = 0`. -/
theorem apply_add_val_nsmul_one_eq_zero_iff
    (hK : ∀ ω, K (ω + ((1 : ℝ) : AddCircle (3 : ℝ))) = K ω - 1) (ω : AddCircle (3 : ℝ))
    (b : ZMod 3) : K (ω + b.val • ((1 : ℝ) : AddCircle (3 : ℝ))) = 0 ↔ K ω = b := by
  rw [apply_add_nsmul_one hK, ZMod.natCast_zmod_val, sub_eq_zero]

/-- If `K (ω + 1) = K ω - 1` and the fibres of `K` are measurable, then the fibre `K⁻¹(0)` has
measure `1`: the three fibres are translates of each other and partition the circle. -/
theorem volume_preimage_zero_eq_one (hKm : ∀ c, MeasurableSet (K ⁻¹' {c}))
    (hK : ∀ ω, K (ω + ((1 : ℝ) : AddCircle (3 : ℝ))) = K ω - 1) : volume (K ⁻¹' {0}) = 1 := by
  have hb : ∀ b, volume (K ⁻¹' {b}) = volume (K ⁻¹' {0}) := fun b => by
    have : K ⁻¹' {b} = (· + b.val • ((1 : ℝ) : AddCircle (3 : ℝ))) ⁻¹' (K ⁻¹' {0}) := by
      ext ω
      simp [apply_add_val_nsmul_one_eq_zero_iff hK]
    rw [this, measure_preimage_add_right]
  have h := sum_volume_preimage_singleton hKm
  rw [Finset.sum_congr rfl fun b _ => hb b, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul, Nat.cast_ofNat] at h
  exact (ENNReal.mul_right_inj (by norm_num) (by norm_num)).1 (h.trans (mul_one 3).symm)

end Circle3

/-- **Circle lemma** (Lemma 6.3 of the paper). -/
theorem circle_lemma (K₁ K₂ K₃ : AddCircle (3 : ℝ) → ZMod 3)
    (h₁ : ∀ c, MeasurableSet (K₁ ⁻¹' {c})) (h₂ : ∀ c, MeasurableSet (K₂ ⁻¹' {c}))
    (h₃ : ∀ c, MeasurableSet (K₃ ⁻¹' {c}))
    (hK₂ : ∀ ω, K₂ (ω + ((1 : ℝ) : AddCircle (3 : ℝ))) = K₂ ω - 1) :
    volume {x : AddCircle (3 : ℝ) × AddCircle (3 : ℝ) | K₃ (x.1 + x.2) = K₁ x.1 + K₂ x.2} ≤
      ENNReal.ofReal (27 / 4) := by
  set c : ZMod 3 → AddCircle (3 : ℝ) := fun b => b.val • ((1 : ℝ) : AddCircle (3 : ℝ))
  -- `X a b` is the set of `(z, w)` with `K₁ z = a`, `K₂ w = b` and `K₃ (z + w) = a + b`.
  set X : ZMod 3 → ZMod 3 → Set (AddCircle (3 : ℝ) × AddCircle (3 : ℝ)) := fun a b =>
    {p | p.1 ∈ K₁ ⁻¹' {a} ∧ p.2 + c b ∈ K₂ ⁻¹' {0} ∧ p.1 + p.2 ∈ K₃ ⁻¹' {a + b}}
  have hsub : {x : AddCircle (3 : ℝ) × AddCircle (3 : ℝ) | K₃ (x.1 + x.2) = K₁ x.1 + K₂ x.2} ⊆
      ⋃ a, ⋃ b, X a b := by
    rintro ⟨z, w⟩ h
    simp only [mem_iUnion]
    exact ⟨K₁ z, K₂ w, rfl, (apply_add_val_nsmul_one_eq_zero_iff hK₂ w (K₂ w)).2 rfl, h⟩
  have hX : ∀ a, ∑ b, volume (X a b) ≤
      ENNReal.ofReal (3 / 4 + 3 / 2 * (volume (K₁ ⁻¹' {a})).toReal) := by
    intro a
    refine (Finset.sum_congr rfl fun b _ =>
      volume_setOf_eq_setLIntegral_conv (h₁ a) (h₂ 0) (h₃ (a + b)) (c b)).trans_le ?_
    refine sum_setLIntegral_conv_le (by simp) (h₁ a) (h₂ 0) (volume_preimage_zero_eq_one h₂ hK₂)
      (fun b => (measurable_sub_const _) (h₃ _)) ?_
    calc ∑ b, volume ((· - c b) ⁻¹' (K₃ ⁻¹' {a + b})) = ∑ b, volume (K₃ ⁻¹' {a + b}) :=
          Finset.sum_congr rfl fun b _ =>
            (measurePreserving_sub_right volume (c b)).measure_preimage (h₃ _).nullMeasurableSet
      _ = ∑ b, volume (K₃ ⁻¹' {b}) := Fintype.sum_equiv (Equiv.addLeft a) _ _ fun b => rfl
      _ ≤ 3 := (sum_volume_preimage_singleton h₃).le
  calc volume {x : AddCircle (3 : ℝ) × AddCircle (3 : ℝ) | K₃ (x.1 + x.2) = K₁ x.1 + K₂ x.2}
      ≤ volume (⋃ a, ⋃ b, X a b) := measure_mono hsub
    _ ≤ ∑ a, ∑ b, volume (X a b) := (measure_iUnion_fintype_le _ _).trans
        (Finset.sum_le_sum fun a _ => measure_iUnion_fintype_le _ _)
    _ ≤ ∑ a, ENNReal.ofReal (3 / 4 + 3 / 2 * (volume (K₁ ⁻¹' {a})).toReal) :=
        Finset.sum_le_sum fun a _ => hX a
    _ = ENNReal.ofReal (27 / 4) := by
        rw [← ENNReal.ofReal_sum_of_nonneg fun a _ => by positivity, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← ENNReal.toReal_sum fun a _ => measure_ne_top _ _,
          sum_volume_preimage_singleton h₁]
        norm_num [ZMod.card]

end Erdos5.Circle
