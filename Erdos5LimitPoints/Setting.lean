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

/-- The equation `f(x) + f(x - r₁) + f(x - r₂) = 1` holds at `x ≥ r₂`. -/
def EqHolds (x : ℝ) : Prop :=
  S.r₂ ≤ x ∧ one3 (S.bit x) (S.bit (x - S.r₁)) (S.bit (x - S.r₂)) = true

/-- The overlap set `E` of points `x ≥ r₂` at which the equation fails. -/
def E : Set ℝ :=
  {x | S.r₂ ≤ x ∧ one3 (S.bit x) (S.bit (x - S.r₁)) (S.bit (x - S.r₂)) = false}

lemma eqHolds_iff {x : ℝ} : S.EqHolds x ↔ S.r₂ ≤ x ∧ x ∉ S.E := by
  simp only [EqHolds, E, mem_setOf_eq, not_and, Bool.not_eq_false]
  tauto

lemma mem_E_of_not_eqHolds {x : ℝ} (hx : S.r₂ ≤ x) (h : ¬ S.EqHolds x) : x ∈ S.E := by
  rw [eqHolds_iff] at h; tauto

lemma E_subset : S.E ⊆ Ici S.r₂ := fun _ hx => hx.1

lemma measurableSet_E : MeasurableSet S.E := by
  sorry

/-- **Lemma 3.1.** For `x ≥ r₂`, one of `x, x - r₁, x - r₂` lies in `B`. -/
lemma mem_or_mem_or_mem {x : ℝ} (hx : S.r₂ ≤ x) : x ∈ S.B ∨ x - S.r₁ ∈ S.B ∨ x - S.r₂ ∈ S.B := by
  sorry

/-- **Lemma 3.2.** `3 λ(B ∩ [0, T]) ≥ T - r₂ + λ(E ∩ [0, T])`. -/
theorem ofReal_add_volume_E_le (T : ℝ) :
    ENNReal.ofReal (T - S.r₂) + volume (S.E ∩ Icc 0 T) ≤ 3 * volume (S.B ∩ Icc 0 T) := by
  sorry

/-! ### Section 4: the hexagon and certified points -/

/-- The lattice point `d⟨m, n⟩ = d + m r₁ + n r₂`. -/
noncomputable def pt (d : ℝ) (m n : ℤ) : ℝ := d + m * S.r₁ + n * S.r₂

open Classical in
/-- The phase `κ(d)` of a point `d`; for a good point it is the unique `c` such that `𝟙_B`
agrees on the hexagon around `d` with the pattern of phase `c`. -/
noncomputable def kappa (d : ℝ) : ZMod 3 :=
  if d ∈ S.B then 0 else if d + S.r₁ ∈ S.B then 1 else 2

/-- `d` is *good*: `𝟙_B (d⟨q⟩) = [ph q = κ(d)]` for all `q ∈ Q`. -/
def Good (d : ℝ) : Prop := ∀ q ∈ hexQ, (S.pt d q.1 q.2 ∈ S.B ↔ ph q = S.kappa d)

/-- `d` is *certified*: `d ≥ c₀` and the equation holds at `d⟨s⟩` for all `s ∈ S`. -/
def Certified (d : ℝ) : Prop := S.c₀ ≤ d ∧ ∀ s ∈ hexS, S.EqHolds (S.pt d s.1 s.2)

lemma measurableSet_certified : MeasurableSet {d | S.Certified d} := by
  sorry

lemma measurableSet_kappa_preimage (c : ZMod 3) : MeasurableSet (S.kappa ⁻¹' {c}) := by
  sorry

/-- **Lemma 4.2** (hexagon lemma). Every certified point is good. -/
theorem Certified.good {d : ℝ} (hd : S.Certified d) : S.Good d := by
  sorry

/-- **Lemma 4.3** (distance `r₁`). -/
theorem kappa_add_r₁ {d : ℝ} (hd : S.Good d) (hd' : S.Good (d + S.r₁)) :
    S.kappa (d + S.r₁) = S.kappa d - 1 := by
  sorry

/-- **Lemma 4.4** (distance `2 r₁`). -/
theorem kappa_add_two_r₁ {d : ℝ} (hd : S.Certified d) (hd' : S.Good (d + 2 * S.r₁)) :
    S.kappa (d + 2 * S.r₁) = S.kappa d - 2 := by
  sorry

/-- **Lemma 4.5** (distance `3 r₁`: the bridge). -/
theorem kappa_add_three_r₁ {d : ℝ} (hd : S.Certified d) (hd' : S.Certified (d + 3 * S.r₁))
    (h₁ : S.EqHolds (S.pt d 2 0)) (h₂ : S.EqHolds (S.pt d 3 (-1))) :
    S.kappa (d + 3 * S.r₁) = S.kappa d := by
  sorry

/-- **Lemma 4.6** (uncertified points are rare). -/
theorem volume_not_certified_le {α β : ℝ} (hα : S.c₀ ≤ α) :
    volume {d | d ∈ Icc α β ∧ ¬ S.Certified d} ≤
      6 * volume (S.E ∩ Icc 0 (β + S.r₁ + S.r₂)) := by
  sorry

end Setting

end Erdos5
