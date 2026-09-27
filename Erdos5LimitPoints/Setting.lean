/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Erdos5LimitPoints.Defs

/-!
# The setting of Sections 2–4

We fix a measurable set `B ⊆ ℝ` with the four-point property and a *`G`-triangle*: reals
`0 < r₁ < r₂` such that none of `r₁, r₂, r₂ - r₁` lies in `B` (`G = [0, ∞) \ B`). This data is
bundled in the structure `Erdos5.Setting`.

* `f = 𝟙_B`; the *equation at `x`* (for `x ≥ r₂`) is `f(x) + f(x - r₁) + f(x - r₂) = 1`,
  encoded by `Setting.EqHolds`. By Lemma 3.1 the left-hand side is always `≥ 1`.
* `Setting.E` is the *overlap set* of `x ≥ r₂` where the equation fails.
* `Setting.pt d m n = d + m r₁ + n r₂` is the lattice point `d⟨m, n⟩`, and
  `ph (m, n) = m + 2n ∈ ℤ/3ℤ` its phase.
* A point `d` is *good* (`Setting.Good`) if `𝟙_B` agrees on the hexagon
  `d⟨Q⟩` with the pattern `q ↦ [ph q = κ(d)]`, and *certified* (`Setting.Certified`) if
  `d ≥ c₀` and the equation holds at `d⟨s⟩` for the six points `s ∈ S`.

Main results: the hexagon lemma (`Setting.Certified.good`, Lemma 4.2), the phase shifts at
distances `r₁, 2r₁, 3r₁` (Lemmas 4.3–4.5), and the bound for uncertified points (Lemma 4.6).
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos5

/-- **Lemma 2.1.** A set with the four-point property contains `0`. -/
theorem HasFourPointProperty.zero_mem {B : Set ℝ} (h : HasFourPointProperty B) : (0 : ℝ) ∈ B := by
  obtain ⟨i, j, -, hij⟩ := h (fun _ => 0) monotone_const
  simpa using hij

/-- `one3 a b c` holds iff exactly one of the three booleans is `true`. -/
def one3 (a b c : Bool) : Bool := (a && !b && !c) || (!a && b && !c) || (!a && !b && c)

/-- The phase `ph (m, n) = m + 2 n ∈ ℤ/3ℤ` of a lattice point. -/
def ph (q : ℤ × ℤ) : ZMod 3 := q.1 + 2 * q.2

/-- The hexagon `Q = {(0,0), ±(1,0), ±(0,1), ±(1,-1)}`. -/
def hexQ : Finset (ℤ × ℤ) := {(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1)}

/-- The six lattice points `S` at which the equations certify a point. -/
def hexS : Finset (ℤ × ℤ) := {(0, 0), (1, 0), (0, 1), (1, 1), (-1, 1), (1, -1)}

/-- The standing data of Sections 3–8 of the paper: a measurable set `B` with the four-point
property together with a `G`-triangle `0 < r₁ < r₂`, i.e. `r₁, r₂, r₂ - r₁ ∉ B`. -/
structure Setting where
  /-- The set with the four-point property. -/
  B : Set ℝ
  /-- The smaller side of the triangle. -/
  r₁ : ℝ
  /-- The larger side of the triangle. -/
  r₂ : ℝ
  measurableSet_B : MeasurableSet B
  fourPoint : HasFourPointProperty B
  r₁_pos : 0 < r₁
  r₁_lt_r₂ : r₁ < r₂
  r₁_notMem : r₁ ∉ B
  r₂_notMem : r₂ ∉ B
  sub_notMem : r₂ - r₁ ∉ B

namespace Setting

variable (S : Setting)

lemma r₂_pos : 0 < S.r₂ := S.r₁_pos.trans S.r₁_lt_r₂

/-- The threshold `c₀` above which points may be certified. (The paper takes `c₀ = 3 r₂`;
any `c₀ ≥ 4 r₁ + 2 r₂` works, and the larger value simplifies Section 8.) -/
noncomputable def c₀ : ℝ := 7 * S.r₂

lemma c₀_pos : 0 < S.c₀ := by unfold c₀; linarith [S.r₂_pos]

open Classical in
/-- `bit x = true ↔ x ∈ B`. -/
noncomputable def bit (x : ℝ) : Bool := decide (x ∈ S.B)

@[simp] lemma bit_eq_true {x : ℝ} : S.bit x = true ↔ x ∈ S.B := by simp [bit]

/-- `bit x` agrees with `decide p` iff `x ∈ B ↔ p`. -/
lemma bit_eq_decide {x : ℝ} {p : Prop} [Decidable p] : S.bit x = decide p ↔ (x ∈ S.B ↔ p) := by
  simp [bit]

/-- `bit = 𝟙_B` is measurable. -/
lemma measurable_bit : Measurable S.bit :=
  measurable_to_bool <| by
    convert S.measurableSet_B
    ext x
    simp

/-- The Boolean function `x ↦ one3 (f x) (f (x - r₁)) (f (x - r₂))` is measurable. -/
lemma measurable_one3_bit :
    Measurable fun x => one3 (S.bit x) (S.bit (x - S.r₁)) (S.bit (x - S.r₂)) :=
  (Measurable.of_discrete (f := fun p : Bool × Bool × Bool => one3 p.1 p.2.1 p.2.2)).comp
    (S.measurable_bit.prodMk ((S.measurable_bit.comp (measurable_sub_const _)).prodMk
      (S.measurable_bit.comp (measurable_sub_const _))))

/-- The equation `f(x) + f(x - r₁) + f(x - r₂) = 1` holds at `x ≥ r₂`. -/
def EqHolds (x : ℝ) : Prop :=
  S.r₂ ≤ x ∧ one3 (S.bit x) (S.bit (x - S.r₁)) (S.bit (x - S.r₂)) = true

/-- The overlap set `E` of points `x ≥ r₂` at which the equation fails. -/
def E : Set ℝ :=
  {x | S.r₂ ≤ x ∧ one3 (S.bit x) (S.bit (x - S.r₁)) (S.bit (x - S.r₂)) = false}

lemma eqHolds_iff {x : ℝ} : S.EqHolds x ↔ S.r₂ ≤ x ∧ x ∉ S.E := by
  simp only [EqHolds, E, mem_ofPred_eq, not_and, Bool.not_eq_false]
  tauto

lemma mem_E_of_not_eqHolds {x : ℝ} (hx : S.r₂ ≤ x) (h : ¬ S.EqHolds x) : x ∈ S.E := by
  rw [eqHolds_iff] at h; tauto

lemma E_subset : S.E ⊆ Ici S.r₂ := fun _ hx => hx.1

lemma measurableSet_E : MeasurableSet S.E :=
  measurableSet_Ici.inter (S.measurable_one3_bit (measurableSet_singleton false))

/-- The set where the equation holds is measurable. -/
lemma measurableSet_eqHolds : MeasurableSet {x | S.EqHolds x} :=
  measurableSet_Ici.inter (S.measurable_one3_bit (measurableSet_singleton true))

/-- **Lemma 3.1.** For `x ≥ r₂`, one of `x, x - r₁, x - r₂` lies in `B`. -/
lemma mem_or_mem_or_mem {x : ℝ} (hx : S.r₂ ≤ x) : x ∈ S.B ∨ x - S.r₁ ∈ S.B ∨ x - S.r₂ ∈ S.B := by
  have h₁ := S.r₁_pos
  have h₂ := S.r₁_lt_r₂
  have hmono : Monotone ![0, S.r₁, S.r₂, x] := by
    refine Fin.monotone_iff_le_succ.2 fun i => ?_
    fin_cases i <;> simp <;> linarith
  obtain ⟨i, j, hij, h⟩ := S.fourPoint _ hmono
  fin_cases i <;> fin_cases j <;> simp [S.r₁_notMem, S.r₂_notMem, S.sub_notMem] at hij h ⊢ <;>
    simp [h]

/-- Pointwise form of Lemma 3.2: for `t ≥ r₂`, `1 + 𝟙_E(t) ≤ f(t) + f(t - r₁) + f(t - r₂)`. -/
lemma one_add_indicator_E_le {t : ℝ} (ht : S.r₂ ≤ t) :
    1 + S.E.indicator 1 t ≤ S.B.indicator (1 : ℝ → ℝ≥0∞) t +
      ((fun t => t - S.r₁) ⁻¹' S.B).indicator 1 t +
      ((fun t => t - S.r₂) ⁻¹' S.B).indicator 1 t := by
  have h3 := S.mem_or_mem_or_mem ht
  simp only [E, indicator, mem_preimage, mem_ofPred_eq, Pi.one_apply]
  by_cases h0 : t ∈ S.B <;> by_cases h1 : t - S.r₁ ∈ S.B <;> by_cases h2 : t - S.r₂ ∈ S.B <;>
    simp [h0, h1, h2, ht, bit, one3] at h3 ⊢

/-- A translate of `B ∩ [r₂ - c, T - c]` has measure at most `λ(B ∩ [0, T])`. -/
lemma volume_preimage_sub_inter_Icc_le {c T : ℝ} (hc₀ : 0 ≤ c) (hc : c ≤ S.r₂) :
    volume ((fun t => t - c) ⁻¹' S.B ∩ Icc S.r₂ T) ≤ volume (S.B ∩ Icc 0 T) :=
  calc volume ((fun t => t - c) ⁻¹' S.B ∩ Icc S.r₂ T)
      ≤ volume ((fun t => t + -c) ⁻¹' (S.B ∩ Icc 0 T)) := by
        refine measure_mono ?_
        rintro t ⟨ht, ht₁, ht₂⟩
        simp only [mem_preimage, mem_inter_iff, mem_Icc, ← sub_eq_add_neg]
        exact ⟨ht, by linarith, by linarith⟩
    _ = volume (S.B ∩ Icc 0 T) := measure_preimage_add_right _ _ _

/-- **Lemma 3.2.** `3 λ(B ∩ [0, T]) ≥ T - r₂ + λ(E ∩ [0, T])`. -/
theorem ofReal_add_volume_E_le (T : ℝ) :
    ENNReal.ofReal (T - S.r₂) + volume (S.E ∩ Icc 0 T) ≤ 3 * volume (S.B ∩ Icc 0 T) := by
  rcases lt_or_ge T S.r₂ with hT | hT
  · have h : S.E ∩ Icc 0 T = ∅ :=
      eq_empty_of_forall_notMem fun x hx => (hx.1.1.trans hx.2.2).not_gt hT
    simp [h, ENNReal.ofReal_eq_zero.2 (sub_nonpos.2 hT.le)]
  have hEI : S.E ∩ Icc 0 T = S.E ∩ Icc S.r₂ T := by
    ext x
    simp only [mem_inter_iff, mem_Icc]
    constructor
    · rintro ⟨hx, -, hxT⟩
      exact ⟨hx, hx.1, hxT⟩
    · rintro ⟨hx, -, hxT⟩
      exact ⟨hx, S.r₂_pos.le.trans hx.1, hxT⟩
  have hB : ∀ c, MeasurableSet ((fun t => t - c) ⁻¹' S.B) :=
    fun c => measurable_sub_const c S.measurableSet_B
  have hr₁ := S.r₁_pos
  have hr₂ := S.r₁_lt_r₂
  calc ENNReal.ofReal (T - S.r₂) + volume (S.E ∩ Icc 0 T)
      = ∫⁻ t in Icc S.r₂ T, (1 + S.E.indicator 1 t) := by
        rw [lintegral_add_right _ (measurable_one.indicator S.measurableSet_E), setLIntegral_const,
          one_mul, Real.volume_Icc, lintegral_indicator_one S.measurableSet_E,
          Measure.restrict_apply S.measurableSet_E, hEI]
    _ ≤ ∫⁻ t in Icc S.r₂ T, (S.B.indicator 1 t + ((fun t => t - S.r₁) ⁻¹' S.B).indicator 1 t +
          ((fun t => t - S.r₂) ⁻¹' S.B).indicator 1 t) :=
        setLIntegral_mono (((measurable_one.indicator S.measurableSet_B).add
          (measurable_one.indicator (hB _))).add (measurable_one.indicator (hB _)))
          fun t ht => S.one_add_indicator_E_le ht.1
    _ = volume (S.B ∩ Icc S.r₂ T) + volume ((fun t => t - S.r₁) ⁻¹' S.B ∩ Icc S.r₂ T) +
          volume ((fun t => t - S.r₂) ⁻¹' S.B ∩ Icc S.r₂ T) := by
        rw [lintegral_add_right _ (measurable_one.indicator (hB _)),
          lintegral_add_right _ (measurable_one.indicator (hB _)),
          lintegral_indicator_one S.measurableSet_B, lintegral_indicator_one (hB _),
          lintegral_indicator_one (hB _), Measure.restrict_apply S.measurableSet_B,
          Measure.restrict_apply (hB _), Measure.restrict_apply (hB _)]
    _ ≤ volume (S.B ∩ Icc 0 T) + volume (S.B ∩ Icc 0 T) + volume (S.B ∩ Icc 0 T) :=
        add_le_add (add_le_add (measure_mono (inter_subset_inter_right _
          (Icc_subset_Icc_left S.r₂_pos.le)))
          (S.volume_preimage_sub_inter_Icc_le hr₁.le hr₂.le))
          (S.volume_preimage_sub_inter_Icc_le S.r₂_pos.le le_rfl)
    _ = 3 * volume (S.B ∩ Icc 0 T) := by ring

/-! ### Section 4: the hexagon and certified points -/

/-- The Boolean core of the hexagon lemma (Lemma 4.2): the six equations at the points of `S`
force the bits on `Q` to follow the pattern of the phase determined by the bits at `(0, 0)` and
`(1, 0)`. -/
theorem one3_hexagon :
    ∀ x00 x10 xm10 x01 x0m1 x1m1 xm11 x11 xm21 x1m2 : Bool,
    one3 x00 xm10 x0m1 = true → one3 x10 x00 x1m1 = true → one3 x01 xm11 x00 = true →
    one3 x11 x01 x10 = true → one3 xm11 xm21 xm10 = true → one3 x1m1 x0m1 x1m2 = true →
    x00 = decide (ph (0, 0) = if x00 then 0 else if x10 then 1 else 2) ∧
      x10 = decide (ph (1, 0) = if x00 then 0 else if x10 then 1 else 2) ∧
      xm10 = decide (ph (-1, 0) = if x00 then 0 else if x10 then 1 else 2) ∧
      x01 = decide (ph (0, 1) = if x00 then 0 else if x10 then 1 else 2) ∧
      x0m1 = decide (ph (0, -1) = if x00 then 0 else if x10 then 1 else 2) ∧
      x1m1 = decide (ph (1, -1) = if x00 then 0 else if x10 then 1 else 2) ∧
      xm11 = decide (ph (-1, 1) = if x00 then 0 else if x10 then 1 else 2) := by
  decide

/-- The Boolean core of Lemma 4.3. -/
theorem phase_shift_one :
    ∀ c c' : ZMod 3, decide (ph (0, 0) = c) = decide (ph (-1, 0) = c') →
      decide (ph (1, 0) = c) = decide (ph (0, 0) = c') → c' = c - 1 := by
  decide

/-- The Boolean core of Lemma 4.4. -/
theorem phase_shift_two :
    ∀ c c' : ZMod 3, decide (ph (1, 0) = c) = decide (ph (-1, 0) = c') →
      one3 (decide (ph (-1, 1) = c')) (decide (ph (0, 1) = c)) (decide (ph (1, 0) = c)) = true →
      c' = c - 2 := by
  decide

/-- The Boolean core of Lemma 4.5. -/
theorem phase_shift_three :
    ∀ (c c' : ZMod 3) (x y z : Bool),
      one3 x (decide (ph (0, 1) = c)) (decide (ph (1, 0) = c)) = true →
      one3 (decide (ph (-1, 1) = c')) x (decide (ph (-1, 0) = c')) = true →
      one3 (decide (ph (-1, 0) = c')) (decide (ph (1, 0) = c)) y = true →
      one3 (decide (ph (0, -1) = c')) y z = true → c' = c := by
  decide

/-- The lattice point `d⟨m, n⟩ = d + m r₁ + n r₂`. -/
noncomputable def pt (d : ℝ) (m n : ℤ) : ℝ := d + m * S.r₁ + n * S.r₂

@[simp] lemma pt_zero_zero (d : ℝ) : S.pt d 0 0 = d := by simp [pt]

lemma pt_one_zero (d : ℝ) : S.pt d 1 0 = d + S.r₁ := by simp [pt]

/-- `d⟨m, n⟩` is the translate of `d` by `m r₁ + n r₂`. -/
lemma pt_eq_add (d : ℝ) (m n : ℤ) : S.pt d m n = d + (m * S.r₁ + n * S.r₂) := by
  rw [pt, add_assoc]

/-- The equation at `d⟨m, n⟩` relates the bits at `d⟨m, n⟩`, `d⟨m - 1, n⟩` and `d⟨m, n - 1⟩`. -/
lemma one3_pt_of_eqHolds {d : ℝ} {m n m' n' : ℤ} (h : S.EqHolds (S.pt d m n))
    (hm : m' = m - 1 := by norm_num) (hn : n' = n - 1 := by norm_num) :
    one3 (S.bit (S.pt d m n)) (S.bit (S.pt d m' n)) (S.bit (S.pt d m n')) = true := by
  subst hm hn
  have h₁ : S.pt d (m - 1) n = S.pt d m n - S.r₁ := by simp only [pt]; push_cast; ring
  have h₂ : S.pt d m (n - 1) = S.pt d m n - S.r₂ := by simp only [pt]; push_cast; ring
  rw [h₁, h₂]
  exact h.2

open Classical in
/-- The phase `κ(d)` of a point `d`; for a good point it is the unique `c` such that `𝟙_B`
agrees on the hexagon around `d` with the pattern of phase `c`. -/
noncomputable def kappa (d : ℝ) : ZMod 3 :=
  if d ∈ S.B then 0 else if d + S.r₁ ∈ S.B then 1 else 2

/-- `κ(d)` in terms of the bits at `d⟨0, 0⟩ = d` and `d⟨1, 0⟩ = d + r₁`. -/
lemma kappa_eq_ite (d : ℝ) :
    S.kappa d = if S.bit (S.pt d 0 0) then 0 else if S.bit (S.pt d 1 0) then 1 else 2 := by
  rw [pt_zero_zero, pt_one_zero, kappa]
  by_cases hd : d ∈ S.B <;> by_cases hd₁ : d + S.r₁ ∈ S.B <;> simp [hd, hd₁]

/-- `d` is *good*: `𝟙_B (d⟨q⟩) = [ph q = κ(d)]` for all `q ∈ Q`. -/
def Good (d : ℝ) : Prop := ∀ q ∈ hexQ, (S.pt d q.1 q.2 ∈ S.B ↔ ph q = S.kappa d)

/-- `Good d` spelled out on the seven points of the hexagon `Q`. -/
lemma good_iff {d : ℝ} : S.Good d ↔
    S.bit (S.pt d 0 0) = decide (ph (0, 0) = S.kappa d) ∧
      S.bit (S.pt d 1 0) = decide (ph (1, 0) = S.kappa d) ∧
      S.bit (S.pt d (-1) 0) = decide (ph (-1, 0) = S.kappa d) ∧
      S.bit (S.pt d 0 1) = decide (ph (0, 1) = S.kappa d) ∧
      S.bit (S.pt d 0 (-1)) = decide (ph (0, -1) = S.kappa d) ∧
      S.bit (S.pt d 1 (-1)) = decide (ph (1, -1) = S.kappa d) ∧
      S.bit (S.pt d (-1) 1) = decide (ph (-1, 1) = S.kappa d) := by
  simp only [Good, hexQ, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
    bit_eq_decide]

/-- `d` is *certified*: `d ≥ c₀` and the equation holds at `d⟨s⟩` for all `s ∈ S`. -/
def Certified (d : ℝ) : Prop := S.c₀ ≤ d ∧ ∀ s ∈ hexS, S.EqHolds (S.pt d s.1 s.2)

lemma measurableSet_certified : MeasurableSet {d | S.Certified d} := by
  have : {d | S.Certified d} =
      Ici S.c₀ ∩ ⋂ s ∈ hexS, (fun d => S.pt d s.1 s.2) ⁻¹' {x | S.EqHolds x} := by
    ext d
    simp [Certified]
  rw [this]
  exact measurableSet_Ici.inter <| hexS.measurableSet_biInter fun s _ =>
    (measurable_add_const _).comp (measurable_add_const _) S.measurableSet_eqHolds

lemma measurableSet_kappa_preimage (c : ZMod 3) : MeasurableSet (S.kappa ⁻¹' {c}) := by
  let _ : MeasurableSpace (ZMod 3) := ⊤
  have hκ : Measurable S.kappa :=
    Measurable.ite S.measurableSet_B measurable_const <|
      Measurable.ite (measurable_add_const S.r₁ S.measurableSet_B) measurable_const
        measurable_const
  exact hκ MeasurableSpace.measurableSet_top

/-- The equation at `d⟨m, n⟩` for a certified `d` and `(m, n) ∈ S`. -/
lemma Certified.one3_pt {d : ℝ} (hd : S.Certified d) {m n m' n' : ℤ} (hs : (m, n) ∈ hexS)
    (hm : m' = m - 1 := by norm_num) (hn : n' = n - 1 := by norm_num) :
    one3 (S.bit (S.pt d m n)) (S.bit (S.pt d m' n)) (S.bit (S.pt d m n')) = true :=
  S.one3_pt_of_eqHolds (hd.2 _ hs) hm hn

/-- **Lemma 4.2** (hexagon lemma). Every certified point is good. -/
theorem Certified.good {d : ℝ} (hd : S.Certified d) : S.Good d := by
  rw [good_iff, kappa_eq_ite]
  -- the equations at the six points of `S`; the bits at `(1, 1)`, `(-2, 1)`, `(1, -2)` are free
  exact one3_hexagon _ _ _ _ _ _ _ _ (S.bit (S.pt d (-2) 1)) (S.bit (S.pt d 1 (-2)))
    (hd.one3_pt (hs := by decide)) (hd.one3_pt (hs := by decide)) (hd.one3_pt (hs := by decide))
    (hd.one3_pt (hs := by decide)) (hd.one3_pt (hs := by decide)) (hd.one3_pt (hs := by decide))

/-- **Lemma 4.3** (distance `r₁`). -/
theorem kappa_add_r₁ {d : ℝ} (hd : S.Good d) (hd' : S.Good (d + S.r₁)) :
    S.kappa (d + S.r₁) = S.kappa d - 1 := by
  obtain ⟨h00, h10, -⟩ := S.good_iff.1 hd
  obtain ⟨h'00, -, h'm10, -⟩ := S.good_iff.1 hd'
  have p₁ : S.pt (d + S.r₁) (-1) 0 = S.pt d 0 0 := by simp only [pt]; push_cast; ring
  have p₂ : S.pt (d + S.r₁) 0 0 = S.pt d 1 0 := by simp only [pt]; push_cast; ring
  rw [p₁] at h'm10
  rw [p₂] at h'00
  exact phase_shift_one _ _ (h00.symm.trans h'm10) (h10.symm.trans h'00)

/-- **Lemma 4.4** (distance `2 r₁`). -/
theorem kappa_add_two_r₁ {d : ℝ} (hd : S.Certified d) (hd' : S.Good (d + 2 * S.r₁)) :
    S.kappa (d + 2 * S.r₁) = S.kappa d - 2 := by
  obtain ⟨-, h10, -, h01, -⟩ := S.good_iff.1 hd.good
  obtain ⟨-, -, h'm10, -, -, -, h'm11⟩ := S.good_iff.1 hd'
  have p₁ : S.pt (d + 2 * S.r₁) (-1) 0 = S.pt d 1 0 := by simp only [pt]; push_cast; ring
  have p₂ : S.pt (d + 2 * S.r₁) (-1) 1 = S.pt d 1 1 := by simp only [pt]; push_cast; ring
  rw [p₁] at h'm10
  rw [p₂] at h'm11
  have e : one3 (S.bit (S.pt d 1 1)) (S.bit (S.pt d 0 1)) (S.bit (S.pt d 1 0)) = true :=
    hd.one3_pt (hs := by decide)
  rw [h'm11, h01, h10] at e
  exact phase_shift_two _ _ (h10.symm.trans h'm10) e

/-- **Lemma 4.5** (distance `3 r₁`: the bridge). -/
theorem kappa_add_three_r₁ {d : ℝ} (hd : S.Certified d) (hd' : S.Certified (d + 3 * S.r₁))
    (h₁ : S.EqHolds (S.pt d 2 0)) (h₂ : S.EqHolds (S.pt d 3 (-1))) :
    S.kappa (d + 3 * S.r₁) = S.kappa d := by
  obtain ⟨-, h10, -, h01, -⟩ := S.good_iff.1 hd.good
  obtain ⟨-, -, h'm10, -, h'0m1, -, h'm11⟩ := S.good_iff.1 hd'.good
  have e₁ : one3 (S.bit (S.pt d 1 1)) (S.bit (S.pt d 0 1)) (S.bit (S.pt d 1 0)) = true :=
    hd.one3_pt (hs := by decide)
  have e₂ : one3 (S.bit (S.pt (d + 3 * S.r₁) (-1) 1)) (S.bit (S.pt (d + 3 * S.r₁) (-2) 1))
      (S.bit (S.pt (d + 3 * S.r₁) (-1) 0)) = true :=
    hd'.one3_pt (hs := by decide)
  have e₃ := S.one3_pt_of_eqHolds h₁ (m' := 1) (n' := -1)
  have e₄ := S.one3_pt_of_eqHolds h₂ (m' := 2) (n' := -2)
  have p₁ : S.pt (d + 3 * S.r₁) (-2) 1 = S.pt d 1 1 := by simp only [pt]; push_cast; ring
  have p₂ : S.pt d 2 0 = S.pt (d + 3 * S.r₁) (-1) 0 := by simp only [pt]; push_cast; ring
  have p₃ : S.pt d 3 (-1) = S.pt (d + 3 * S.r₁) 0 (-1) := by simp only [pt]; push_cast; ring
  rw [p₁, h'm11, h'm10] at e₂
  rw [h01, h10] at e₁
  rw [p₂, h'm10, h10] at e₃
  rw [p₃, h'0m1] at e₄
  exact phase_shift_three _ _ _ _ _ e₁ e₂ e₃ e₄

/-- The offsets `s₁ r₁ + s₂ r₂` for `s ∈ S` lie in `[r₁ - r₂, r₁ + r₂]`. -/
lemma offset_mem_Icc {s : ℤ × ℤ} (hs : s ∈ hexS) :
    S.r₁ - S.r₂ ≤ s.1 * S.r₁ + s.2 * S.r₂ ∧ s.1 * S.r₁ + s.2 * S.r₂ ≤ S.r₁ + S.r₂ := by
  have h₁ := S.r₁_pos
  have h₂ := S.r₁_lt_r₂
  simp only [hexS, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> push_cast <;> constructor <;> linarith

/-- **Lemma 4.6** (uncertified points are rare). -/
theorem volume_not_certified_le {α β : ℝ} (hα : S.c₀ ≤ α) :
    volume {d | d ∈ Icc α β ∧ ¬ S.Certified d} ≤
      6 * volume (S.E ∩ Icc 0 (β + S.r₁ + S.r₂)) := by
  set A := S.E ∩ Icc 0 (β + S.r₁ + S.r₂)
  have hsub : {d | d ∈ Icc α β ∧ ¬ S.Certified d} ⊆
      ⋃ s ∈ hexS, (fun d => d + (s.1 * S.r₁ + s.2 * S.r₂)) ⁻¹' A := by
    rintro d ⟨⟨hαd, hdβ⟩, hd⟩
    obtain ⟨s, hs, hne⟩ : ∃ s ∈ hexS, ¬ S.EqHolds (S.pt d s.1 s.2) := by
      by_contra! h
      exact hd ⟨hα.trans hαd, h⟩
    obtain ⟨hlo, hhi⟩ := S.offset_mem_Icc hs
    have hc₀ : S.c₀ = 7 * S.r₂ := rfl
    have hr₁ := S.r₁_pos
    have hr₂ := S.r₂_pos
    rw [pt_eq_add] at hne
    refine mem_iUnion₂.2 ⟨s, hs, ?_⟩
    rw [mem_preimage]
    exact ⟨S.mem_E_of_not_eqHolds (by linarith) hne, by linarith, by linarith⟩
  calc volume {d | d ∈ Icc α β ∧ ¬ S.Certified d}
      ≤ volume (⋃ s ∈ hexS, (fun d => d + (s.1 * S.r₁ + s.2 * S.r₂)) ⁻¹' A) := measure_mono hsub
    _ ≤ ∑ s ∈ hexS, volume ((fun d => d + (s.1 * S.r₁ + s.2 * S.r₂)) ⁻¹' A) :=
        measure_biUnion_finset_le _ _
    _ = 6 * volume A := by
        rw [Finset.sum_congr rfl fun s _ => measure_preimage_add_right _ _ _, Finset.sum_const,
          nsmul_eq_mul, show hexS.card = 6 from rfl, Nat.cast_ofNat]

end Setting

end Erdos5
