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
  simp only [K₂raw, Int.floor_add_one, Int.cast_add, Int.cast_one]
  have : ω + 1 - ((⌊ω⌋ : ℝ) + 1) = ω - ⌊ω⌋ := by ring
  rw [this]
  ring

/-- `K₂` is `3`-periodic. -/
theorem K₂raw_periodic (q : ℝ) : Function.Periodic (S.K₂raw q) 3 := fun ω => by
  have h3 : ω + 3 = ω + 1 + 1 + 1 := by ring
  rw [h3, K₂raw_add_one, K₂raw_add_one, K₂raw_add_one]
  have : (3 : ZMod 3) = 0 := rfl
  linear_combination -this

/-- **Lemma 7.1**, first part: `K₂(w) = κ(q + w r₁)` whenever `q + w r₁` is certified,
for `w ∈ [0, 3)`. -/
theorem K₂raw_eq_kappa {q w : ℝ} (hw : w ∈ Ico (0 : ℝ) 3) (hc : S.Certified (q + w * S.r₁)) :
    S.K₂raw q w = S.kappa (q + w * S.r₁) := by
  classical
  obtain ⟨hw0, hw3⟩ := hw
  set j := ⌊w⌋ with hj
  set w' := w - j with hw'
  have hj0 : 0 ≤ j := Int.floor_nonneg.2 hw0
  have hj3 : j < 3 := Int.floor_lt.2 (by exact_mod_cast hw3)
  have hww : w = w' + j := by rw [hw']; ring
  simp only [K₂raw, ← hj, ← hw']
  -- the three points of the orbit
  have e1 : q + (w' + 1) * S.r₁ = (q + w' * S.r₁) + S.r₁ := by ring
  have e2 : q + (w' + 2) * S.r₁ = (q + w' * S.r₁) + 2 * S.r₁ := by ring
  have e21 : q + (w' + 2) * S.r₁ = (q + (w' + 1) * S.r₁) + S.r₁ := by ring
  have c2 : ((2 : ℤ) : ZMod 3) = 2 := rfl
  interval_cases j
  · -- `j = 0`
    have hw'w : w' = w := by rw [hww]; simp
    rw [hw'w]
    simp [base, hc]
  · -- `j = 1`
    have hv : q + w * S.r₁ = q + (w' + 1) * S.r₁ := by rw [hww]; push_cast; ring
    rw [hv] at hc ⊢
    simp only [base, Int.cast_one]
    by_cases h0 : S.Certified (q + w' * S.r₁)
    · rw [ite_eq_left h0, e1, S.kappa_add_r₁ h0.good (by rw [← e1]; exact hc.good)]
    · rw [ite_eq_right h0, ite_eq_left hc]
      ring
  · -- `j = 2`
    have hv : q + w * S.r₁ = q + (w' + 2) * S.r₁ := by rw [hww]; push_cast; ring
    rw [hv] at hc ⊢
    simp only [base, c2]
    by_cases h0 : S.Certified (q + w' * S.r₁)
    · rw [ite_eq_left h0, e2, S.kappa_add_two_r₁ h0 (by rw [← e2]; exact hc.good)]
    · rw [ite_eq_right h0]
      by_cases h1 : S.Certified (q + (w' + 1) * S.r₁)
      · rw [ite_eq_left h1, e21, S.kappa_add_r₁ h1.good (by rw [← e21]; exact hc.good)]
        ring
      · rw [ite_eq_right h1, ite_eq_left hc]
        ring

/-- **Lemma 7.3.** Under the smallness hypothesis of Proposition 5.3, for `p, q` with
`p + q + 6 r₁ ≤ T - 2 r₂` and admissible `(z, w) ∈ [0, 3)²`, `K₃(y) = K₁(z) + K₂(w)` where
`y ≡ z + w (mod 3)`. -/
theorem K₃raw_eq_of_admissible {T p q z w : ℝ}
    (hT : 36 * volume (S.E ∩ Icc 0 T) < ENNReal.ofReal (T - 2 * S.r₂ - 6 * S.c₀))
    (hpq : p + q + 6 * S.r₁ ≤ T - 2 * S.r₂) (hz : z ∈ Ico (0 : ℝ) 3) (hw : w ∈ Ico (0 : ℝ) 3)
    (h : S.Admissible p q z w) :
    S.K₃raw p q (if z + w < 3 then z + w else z + w - 3) = S.K₁raw p z + S.K₂raw q w := by
  classical
  obtain ⟨hu, hv, huv, hlow, hhigh⟩ := h
  have hr₁ := S.r₁_pos
  have huv_eq : p + z * S.r₁ + (q + w * S.r₁) = p + q + (z + w) * S.r₁ := by ring
  have hadd : S.kappa (p + q + (z + w) * S.r₁) =
      S.kappa (p + z * S.r₁) + S.kappa (q + w * S.r₁) := by
    rw [← huv_eq]
    refine S.kappa_add hT ?_ hu hv (by rw [huv_eq]; exact huv)
    rw [huv_eq]
    nlinarith [hz.2, hw.2]
  have hK₁ : S.K₁raw p z = S.kappa (p + z * S.r₁) := by
    simp only [K₁raw]
    exact ite_eq_left hu
  rw [hK₁, S.K₂raw_eq_kappa hw hv, ← hadd]
  -- `K₃(y) = κ(u + v)`
  have bridge : ∀ d, S.Certified d → S.Certified (d + 3 * S.r₁) → S.Bridge d →
      S.kappa (d + 3 * S.r₁) = S.kappa d := fun d hd hd' hb => by
    refine S.kappa_add_three_r₁ hd hd' ?_ ?_
    · have : S.pt d 2 0 = d + 2 * S.r₁ := by simp [pt]
      rw [this]; exact hb.1
    · have : S.pt d 3 (-1) = d + 3 * S.r₁ - S.r₂ := by simp [pt]; ring
      rw [this]; exact hb.2
  by_cases h3 : z + w < 3
  · rw [ite_eq_left h3]
    by_cases hy : 3 / 2 ≤ z + w
    · simp only [K₃raw]
      rw [ite_eq_left hy, ite_eq_left huv]
    · have hy' : z + w < 3 / 2 := lt_of_not_ge hy
      simp only [K₃raw]
      rw [ite_eq_right hy]
      have e : p + q + (z + w + 3) * S.r₁ = p + q + (z + w) * S.r₁ + 3 * S.r₁ := by ring
      by_cases hx' : S.Certified (p + q + (z + w + 3) * S.r₁)
      · rw [ite_eq_left hx']
        rcases hlow hy' with hn | hb
        · exact absurd hx' hn
        · rw [e] at hx' ⊢
          exact bridge _ huv hx' hb
      · rw [ite_eq_right hx', ite_eq_left huv]
  · rw [ite_eq_right h3]
    have e : p + q + (z + w - 3 + 3) * S.r₁ = p + q + (z + w) * S.r₁ := by ring
    simp only [K₃raw]
    by_cases hy : 3 / 2 ≤ z + w - 3
    · -- non-preferred case `z + w ≥ 9/2`
      rw [ite_eq_left hy]
      by_cases hx : S.Certified (p + q + (z + w - 3) * S.r₁)
      · rw [ite_eq_left hx]
        have e' : p + q + (z + w) * S.r₁ = p + q + (z + w - 3) * S.r₁ + 3 * S.r₁ := by ring
        rcases hhigh (by linarith) with hn | hb
        · exact absurd hx hn
        · rw [e']
          exact (bridge _ hx (by rw [← e']; exact huv) hb).symm
      · rw [ite_eq_right hx, e, ite_eq_left huv]
    · rw [ite_eq_right hy, e, ite_eq_left huv]

section Circle

/-! ### Transfer to the circle `ℝ / 3ℤ` -/

/-- The discrete σ-algebra on `ZMod 3`, used (locally) to express the measurability of
`K₁, K₂, K₃`. -/
@[instance_reducible]
def zmod3MeasurableSpace : MeasurableSpace (ZMod 3) := ⊤

attribute [local instance] zmod3MeasurableSpace

lemma zmod3_discreteMeasurableSpace : DiscreteMeasurableSpace (ZMod 3) := ⟨fun _ => trivial⟩

attribute [local instance] zmod3_discreteMeasurableSpace

/-- The representative in `[0, 3)` of a point of the circle `ℝ / 3ℤ`. -/
noncomputable def rep (ω : AddCircle (3 : ℝ)) : ℝ := (AddCircle.equivIco (3 : ℝ) 0 ω : ℝ)

lemma rep_mem (ω : AddCircle (3 : ℝ)) : rep ω ∈ Ico (0 : ℝ) 3 := by
  simpa [rep] using (AddCircle.equivIco (3 : ℝ) 0 ω).2

lemma rep_coe {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 3) : rep (x : AddCircle (3 : ℝ)) = x := by
  rw [rep, AddCircle.equivIco_coe_eq (by simpa using hx)]

lemma coe_rep (ω : AddCircle (3 : ℝ)) : ((rep ω : ℝ) : AddCircle (3 : ℝ)) = ω :=
  (AddCircle.equivIco (3 : ℝ) 0).symm_apply_apply ω

lemma measurable_rep : Measurable rep :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco (3 : ℝ) 0).measurable

lemma periodic_rep_coe {α : Type*} {f : ℝ → α} (hf : Function.Periodic f 3) (x : ℝ) :
    f (rep (x : AddCircle (3 : ℝ))) = f x := by
  rw [rep, AddCircle.coe_equivIco_mk_apply]
  have : Int.fract (x / 3) * 3 = x - ⌊x / 3⌋ * 3 := by
    rw [Int.fract]; field_simp
  rw [this, hf.sub_int_mul_eq]

lemma measurable_kappa : Measurable S.kappa :=
  measurable_to_countable' S.measurableSet_kappa_preimage

lemma measurableSet_certified_affine (a b : ℝ) :
    MeasurableSet {z : ℝ | S.Certified (a + z * b)} :=
  S.measurableSet_certified.preimage (by fun_prop : Measurable fun z : ℝ => a + z * b)

lemma measurable_kappa_affine (a b : ℝ) : Measurable fun z : ℝ => S.kappa (a + z * b) :=
  S.measurable_kappa.comp (by fun_prop)

lemma measurable_K₁raw (p : ℝ) : Measurable (S.K₁raw p) := by
  classical
  exact Measurable.ite (S.measurableSet_certified_affine p S.r₁)
    (S.measurable_kappa_affine p S.r₁) measurable_const

lemma measurable_base (q : ℝ) : Measurable (S.base q) := by
  classical
  have h1 : Measurable fun w' : ℝ => S.kappa (q + (w' + 1) * S.r₁) + 1 :=
    (S.measurable_kappa.comp (by fun_prop)).add_const _
  have h2 : Measurable fun w' : ℝ => S.kappa (q + (w' + 2) * S.r₁) + 2 :=
    (S.measurable_kappa.comp (by fun_prop)).add_const _
  have s1 : MeasurableSet {w' : ℝ | S.Certified (q + (w' + 1) * S.r₁)} :=
    S.measurableSet_certified.preimage (by fun_prop)
  have s2 : MeasurableSet {w' : ℝ | S.Certified (q + (w' + 2) * S.r₁)} :=
    S.measurableSet_certified.preimage (by fun_prop)
  exact Measurable.ite (S.measurableSet_certified_affine q S.r₁)
    (S.measurable_kappa_affine q S.r₁) (Measurable.ite s1 h1 (Measurable.ite s2 h2
      measurable_const))

lemma measurable_K₂raw (q : ℝ) : Measurable (S.K₂raw q) := by
  have hfl : Measurable fun ω : ℝ => ((⌊ω⌋ : ℤ) : ZMod 3) :=
    (measurable_of_countable _).comp Int.measurable_floor
  have hb : Measurable fun ω : ℝ => S.base q (ω - ⌊ω⌋) :=
    (S.measurable_base q).comp (measurable_id.sub (measurable_of_countable (fun n : ℤ =>
      (n : ℝ)) |>.comp Int.measurable_floor))
  exact (measurable_of_countable fun x : ZMod 3 × ZMod 3 => x.1 - x.2).comp (hb.prodMk hfl)

lemma measurable_K₃raw (p q : ℝ) : Measurable (S.K₃raw p q) := by
  classical
  exact Measurable.ite measurableSet_Ici
    (Measurable.ite (S.measurableSet_certified_affine (p + q) S.r₁)
      (S.measurable_kappa_affine (p + q) S.r₁)
      (Measurable.ite (S.measurableSet_certified.preimage (by fun_prop))
        (S.measurable_kappa.comp (by fun_prop)) measurable_const))
    (Measurable.ite (S.measurableSet_certified.preimage (by fun_prop))
        (S.measurable_kappa.comp (by fun_prop))
      (Measurable.ite (S.measurableSet_certified_affine (p + q) S.r₁)
        (S.measurable_kappa_affine (p + q) S.r₁) measurable_const))

lemma rep_coe_add {z w : ℝ} (hz : z ∈ Ico (0 : ℝ) 3) (hw : w ∈ Ico (0 : ℝ) 3) :
    rep ((z : AddCircle (3 : ℝ)) + (w : AddCircle (3 : ℝ))) =
      if z + w < 3 then z + w else z + w - 3 := by
  rw [← AddCircle.coe_add]
  split_ifs with h
  · exact rep_coe ⟨by linarith [hz.1, hw.1], h⟩
  · have : ((z + w : ℝ) : AddCircle (3 : ℝ)) = ((z + w - 3 : ℝ) : AddCircle (3 : ℝ)) := by
      rw [AddCircle.coe_sub, AddCircle.coe_period, sub_zero]
    rw [this]
    exact rep_coe ⟨by linarith, by linarith [hz.2, hw.2]⟩

/-- The covering map `[0, 3) → ℝ / 3ℤ` is measure preserving. -/
lemma measurePreserving_coe_Ico :
    MeasurePreserving (fun x : ℝ => (x : AddCircle (3 : ℝ)))
      (volume.restrict (Ico (0 : ℝ) 3)) volume := by
  have h := AddCircle.measurePreserving_mk (3 : ℝ) 0
  rw [zero_add] at h
  rwa [Measure.restrict_congr_set Ico_ae_eq_Ioc]

end Circle

/-- **Corollary 7.4.** At least a quarter of the pairs `(z, w) ∈ [0, 3)²` are not admissible. -/
theorem volume_not_admissible {T p q : ℝ}
    (hT : 36 * volume (S.E ∩ Icc 0 T) < ENNReal.ofReal (T - 2 * S.r₂ - 6 * S.c₀))
    (hpq : p + q + 6 * S.r₁ ≤ T - 2 * S.r₂) :
    ENNReal.ofReal (9 / 4) ≤
      volume {x : ℝ × ℝ | x ∈ Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3 ∧ ¬ S.Admissible p q x.1 x.2} := by
  classical
  -- the three functions on the circle
  set K₁ : AddCircle (3 : ℝ) → ZMod 3 := fun ω => S.K₁raw p (rep ω) with hK₁
  set K₂ : AddCircle (3 : ℝ) → ZMod 3 := fun ω => S.K₂raw q (rep ω) with hK₂
  set K₃ : AddCircle (3 : ℝ) → ZMod 3 := fun ω => S.K₃raw p q (rep ω) with hK₃
  have m₁ : Measurable K₁ := (S.measurable_K₁raw p).comp measurable_rep
  have m₂ : Measurable K₂ := (S.measurable_K₂raw q).comp measurable_rep
  have m₃ : Measurable K₃ := (S.measurable_K₃raw p q).comp measurable_rep
  have hK₂one : ∀ ω, K₂ (ω + ((1 : ℝ) : AddCircle (3 : ℝ))) = K₂ ω - 1 := fun ω => by
    simp only [hK₂]
    conv_lhs => rw [← coe_rep ω, ← AddCircle.coe_add]
    rw [periodic_rep_coe (S.K₂raw_periodic q), K₂raw_add_one]
  set X := {x : AddCircle (3 : ℝ) × AddCircle (3 : ℝ) | K₃ (x.1 + x.2) = K₁ x.1 + K₂ x.2}
    with hX
  have hXle : volume X ≤ ENNReal.ofReal (27 / 4) :=
    Circle.circle_lemma K₁ K₂ K₃ (fun c => m₁ (measurableSet_singleton c))
      (fun c => m₂ (measurableSet_singleton c)) (fun c => m₃ (measurableSet_singleton c)) hK₂one
  have hXm : MeasurableSet X :=
    measurableSet_eq_fun (m₃.comp measurable_add)
      ((measurable_of_countable fun x : ZMod 3 × ZMod 3 => x.1 + x.2).comp
        ((m₁.comp measurable_fst).prodMk (m₂.comp measurable_snd)))
  -- transfer to `[0, 3)²`
  set Z : Set (ℝ × ℝ) := Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3 with hZ
  have hZm : MeasurableSet Z := measurableSet_Ico.prod measurableSet_Ico
  set Φ : ℝ × ℝ → AddCircle (3 : ℝ) × AddCircle (3 : ℝ) :=
    Prod.map (fun x : ℝ => (x : AddCircle (3 : ℝ))) (fun x : ℝ => (x : AddCircle (3 : ℝ)))
  have hΦ : MeasurePreserving Φ (volume.restrict Z) volume := by
    have := measurePreserving_coe_Ico.prod measurePreserving_coe_Ico
    rwa [Measure.prod_restrict, ← Measure.volume_eq_prod, ← Measure.volume_eq_prod] at this
  have hadm : {x : ℝ × ℝ | x ∈ Z ∧ S.Admissible p q x.1 x.2} ⊆ Φ ⁻¹' X ∩ Z := by
    rintro ⟨z, w⟩ ⟨⟨hz, hw⟩, h⟩
    refine ⟨?_, hz, hw⟩
    simp only [Φ, hX, mem_preimage, Prod.map_apply, mem_ofPred_eq, hK₁, hK₂, hK₃]
    rw [rep_coe_add hz hw, rep_coe hz, rep_coe hw]
    exact S.K₃raw_eq_of_admissible hT hpq hz hw h
  have hvolZ : volume Z = ENNReal.ofReal 9 := by
    rw [hZ, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, sub_zero,
      ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have hA : volume {x : ℝ × ℝ | x ∈ Z ∧ S.Admissible p q x.1 x.2} ≤ ENNReal.ofReal (27 / 4) :=
    calc _ ≤ volume (Φ ⁻¹' X ∩ Z) := measure_mono hadm
      _ = volume.restrict Z (Φ ⁻¹' X) := (Measure.restrict_apply' hZm).symm
      _ = volume X := hΦ.measure_preimage hXm.nullMeasurableSet
      _ ≤ _ := hXle
  have hsplit : Z ⊆ {x : ℝ × ℝ | x ∈ Z ∧ S.Admissible p q x.1 x.2} ∪
      {x : ℝ × ℝ | x ∈ Z ∧ ¬ S.Admissible p q x.1 x.2} := fun x hx => by
    by_cases h : S.Admissible p q x.1 x.2
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  have h9 : ENNReal.ofReal 9 ≤ ENNReal.ofReal (27 / 4) +
      volume {x : ℝ × ℝ | x ∈ Z ∧ ¬ S.Admissible p q x.1 x.2} := by
    rw [← hvolZ]
    exact (measure_mono hsplit).trans ((measure_union_le _ _).trans (add_le_add hA le_rfl))
  have h94 : ENNReal.ofReal 9 = ENNReal.ofReal (27 / 4) + ENNReal.ofReal (9 / 4) := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  rw [h94] at h9
  exact (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).1 h9

end Erdos5.Setting
