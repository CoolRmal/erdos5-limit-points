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

## Main results

* `Erdos5.Pollard.rep_eq_rep_inter_union_add_rep_sdiff`: the Dyson decomposition
  `rep A B = rep (A ∩ B) (A ∪ B) + rep (A \ B) (B \ A)`, valid in any finite abelian group.
* `Erdos5.Pollard.pollard`: Pollard's theorem.
* `Erdos5.Pollard.pollard'`: Pollard's theorem without size restrictions on `t`.

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

section Rep

variable (A B : Finset G) (x : G)

omit [Fintype G] in
lemma rep_le_card_left : rep A B x ≤ #A := card_filter_le _ _

omit [Fintype G] in
lemma rep_comm : rep A B x = rep B A x :=
  card_nbij' (x - ·) (x - ·) (fun a ha ↦ by simp_all) (fun a ha ↦ by simp_all)
    (fun a _ ↦ by simp) (fun a _ ↦ by simp)

omit [Fintype G] in
lemma rep_le_card_right : rep A B x ≤ #B := rep_comm A B x ▸ rep_le_card_left B A x

/-- Every pair `(a, b) ∈ A × B` is a representation of exactly one `x`. -/
lemma sum_rep : ∑ x, rep A B x = #A * #B := by
  simp_rw [rep, card_filter]
  rw [sum_comm]
  have (a : G) : ∑ x, (if x - a ∈ B then 1 else 0) = #B := by
    rw [← Equiv.sum_comp (Equiv.addRight a)]
    simp
  simp [this]

omit [Fintype G] in
/-- Translating `A` by `g` translates the representation function by `g`. -/
lemma rep_map_addRight (g : G) :
    rep (A.map (Equiv.addRight g).toEmbedding) B x = rep A B (x - g) := by
  rw [rep, filter_map, card_map, rep]
  congr 1
  refine filter_congr fun a _ ↦ ?_
  simp [sub_add_eq_sub_sub, sub_right_comm]

lemma cast_rep_eq_sum : (rep A B x : ℤ) = ∑ a, if a ∈ A ∧ x - a ∈ B then 1 else 0 := by
  rw [sum_boole, rep]
  congr 2
  ext a
  simp

omit [Fintype G] in
/-- The **Dyson decomposition** of the representation function:
`rep A B = rep (A ∩ B) (A ∪ B) + rep (A \ B) (B \ A)`. -/
lemma rep_eq_rep_inter_union_add_rep_sdiff [Finite G] :
    rep A B x = rep (A ∩ B) (A ∪ B) x + rep (A \ B) (B \ A) x := by
  have := Fintype.ofFinite G
  zify
  rw [cast_rep_eq_sum, cast_rep_eq_sum, cast_rep_eq_sum, ← sub_eq_zero, ← sum_add_distrib,
    ← sum_sub_distrib]
  obtain ⟨F, hF⟩ : ∃ F : G → ℤ, ∀ a, F a = (if a ∈ A ∧ x - a ∈ B then 1 else 0) -
      ((if a ∈ A ∩ B ∧ x - a ∈ A ∪ B then 1 else 0) +
        if a ∈ A \ B ∧ x - a ∈ B \ A then 1 else 0) := ⟨_, fun _ ↦ rfl⟩
  simp_rw [← hF]
  -- The summand is antisymmetric under the involution `a ↦ x - a`.
  have hpair (a : G) : F a + F (x - a) = 0 := by
    simp only [hF, sub_sub_cancel, mem_inter, mem_union, mem_sdiff]
    by_cases h₁ : a ∈ A <;> by_cases h₂ : a ∈ B <;> by_cases h₃ : x - a ∈ A <;>
      by_cases h₄ : x - a ∈ B <;> simp [h₁, h₂, h₃, h₄]
  have h₁ : ∑ a, F a = ∑ a, F (x - a) := (Equiv.sum_comp (Equiv.subLeft x) F).symm
  have h₂ : ∑ a, F a + ∑ a, F (x - a) = 0 := by
    rw [← sum_add_distrib]
    exact sum_eq_zero fun a _ ↦ hpair a
  linarith

end Rep

section Sum

variable (A B : Finset G) (t : ℕ)

lemma sum_min_rep_comm : ∑ x, min (rep A B x) t = ∑ x, min (rep B A x) t :=
  sum_congr rfl fun x _ ↦ by rw [rep_comm]

lemma sum_min_rep_map_addRight (g : G) :
    ∑ x, min (rep (A.map (Equiv.addRight g).toEmbedding) B x) t = ∑ x, min (rep A B x) t := by
  simp_rw [rep_map_addRight]
  exact Equiv.sum_comp (Equiv.subRight g) (fun x ↦ min (rep A B x) t)

lemma sum_min_rep_of_card_left_le (h : #A ≤ t) : ∑ x, min (rep A B x) t = #A * #B := by
  rw [← sum_rep]
  exact sum_congr rfl fun x _ ↦ min_eq_left ((rep_le_card_left A B x).trans h)

lemma sum_min_rep_of_card_right_le (h : #B ≤ t) : ∑ x, min (rep A B x) t = #A * #B := by
  rw [← sum_rep]
  exact sum_congr rfl fun x _ ↦ min_eq_left ((rep_le_card_right A B x).trans h)

end Sum

/-- The arithmetic inequality closing the induction step in the proof of Pollard's theorem. -/
lemma mul_min_le_mul_add_mul_min {p K v t : ℕ} (hvt : v ≤ t) (htK : t + v ≤ K) :
    t * min p (K - t) ≤ v * (K - v) + (t - v) * min p (K - v - t) := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hvt
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le htK
  have e₁ : v + u + v + m - (v + u) = v + m := by omega
  have e₂ : v + u + v + m - v - (v + u) = m := by omega
  have e₃ : v + u + v + m - v = v + u + m := by omega
  rw [e₁, e₂, e₃, Nat.add_sub_cancel_left]
  rcases le_total p m with h | h
  · rw [min_eq_left h, min_eq_left (by omega)]
    nlinarith
  · rw [min_eq_right h]
    calc (v + u) * min p (v + m) ≤ (v + u) * (v + m) := Nat.mul_le_mul_left _ (min_le_right _ _)
      _ = v * (v + u + m) + u * m := by ring

omit [Fintype G] in
/-- If every translate `A + g` meeting `B` contains `B`, then `A` is stable under adding any
difference of two elements of `B`. -/
lemma add_mem_of_forall_card_inter_le {A B : Finset G} {b₀ b₁ : G} (hb₀ : b₀ ∈ B)
    (hb₁ : b₁ ∈ B) (H : ∀ g, 0 < #(A.map (Equiv.addRight g).toEmbedding ∩ B) →
      #B ≤ #(A.map (Equiv.addRight g).toEmbedding ∩ B)) {a : G} (ha : a ∈ A) :
    a + (b₁ - b₀) ∈ A := by
  have hmem : b₀ ∈ A.map (Equiv.addRight (b₀ - a)).toEmbedding ∩ B := by
    simp [mem_map_equiv, ha, hb₀]
  have hsub := eq_of_subset_of_card_le inter_subset_right (H _ (card_pos.mpr ⟨_, hmem⟩))
  have : b₁ ∈ A.map (Equiv.addRight (b₀ - a)).toEmbedding ∩ B := by rw [hsub]; exact hb₁
  simp only [mem_inter, mem_map_equiv, Equiv.addRight_symm, Equiv.coe_addRight] at this
  convert this.1 using 1
  abel

/-- A nonempty subset of `ZMod p` that is stable under adding a nonzero `d` is everything. -/
lemma eq_univ_of_add_mem {p : ℕ} [Fact p.Prime] {A : Finset (ZMod p)} (hA : A.Nonempty)
    {d : ZMod p} (hd : d ≠ 0) (h : ∀ a ∈ A, a + d ∈ A) : A = univ := by
  obtain ⟨a₀, ha₀⟩ := hA
  have hmul (n : ℕ) : a₀ + n * d ∈ A := by
    induction n with
    | zero => simpa using ha₀
    | succ n ih => simpa [add_mul, add_assoc] using h _ ih
  refine eq_univ_of_forall fun y ↦ ?_
  convert hmul ((y - a₀) / d).val using 1
  rw [ZMod.natCast_zmod_val, div_mul_cancel₀ _ hd]
  exact (add_sub_cancel a₀ y).symm

/-- The key step of the Dyson transform: if `A ≠ univ` and `|B| ≥ 2`, some translate of `A`
meets `B` in a nonempty proper subset of `B`. -/
lemma exists_card_inter_pos_lt {p : ℕ} [Fact p.Prime] {A B : Finset (ZMod p)}
    (hA : A.Nonempty) (hAu : A ≠ univ) (hB : 1 < #B) (t : ℕ) :
    ∃ A' : Finset (ZMod p), #A' = #A ∧ 0 < #(A' ∩ B) ∧ #(A' ∩ B) < #B ∧
      ∑ x, min (rep A' B x) t = ∑ x, min (rep A B x) t := by
  obtain ⟨b₀, hb₀, b₁, hb₁, hne⟩ := one_lt_card.mp hB
  by_contra! H
  refine hAu <| eq_univ_of_add_mem hA (sub_ne_zero.mpr hne.symm)
    fun a ha ↦ add_mem_of_forall_card_inter_le hb₀ hb₁ (fun g hg ↦ not_lt.mp fun hlt ↦ ?_) ha
  exact H _ (card_map _) hg hlt (sum_min_rep_map_addRight A B t g)

/-- **Pollard's theorem** in the case `|B| ≤ |A|`, proved by strong induction on `|B|`. -/
theorem pollard_of_card_le {p : ℕ} [Fact p.Prime] {A B : Finset (ZMod p)} {t : ℕ}
    (hBA : #B ≤ #A) (htB : t ≤ #B) : t * min p (#A + #B - t) ≤ ∑ x, min (rep A B x) t := by
  obtain ⟨n, hn⟩ : ∃ n, #B = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing A B t with
  | _ n ih =>
  obtain rfl | ht0 := Nat.eq_zero_or_pos t
  · simp
  obtain rfl | htB' := htB.eq_or_lt
  · rw [sum_min_rep_of_card_right_le A B _ le_rfl, Nat.add_sub_cancel, mul_comm]
    exact Nat.mul_le_mul_right _ (min_le_right _ _)
  by_cases hAu : A = univ
  · subst hAu
    have (x : ZMod p) : rep univ B x = #B := by
      rw [rep_comm]; simp [rep]
    simp only [this, min_eq_right htB, sum_const, card_univ, ZMod.card, smul_eq_mul]
    rw [mul_comm]
    exact Nat.mul_le_mul_right _ (min_le_left _ _)
  have hAne : A.Nonempty := by rw [← card_pos]; omega
  -- Replace `A` by a translate `A'` with `0 < |A' ∩ B| < |B|` and apply the Dyson transform.
  obtain ⟨A', hA', hv0, hvB, hsum⟩ := exists_card_inter_pos_lt hAne hAu (by omega : 1 < #B) t
  rw [← hsum]
  have hU := card_union_add_card_inter A' B
  have hD := card_sdiff_add_card_inter A' B
  have hE := card_sdiff_add_card_inter B A'
  rw [inter_comm B A'] at hE
  obtain ⟨v, hv⟩ : ∃ v, #(A' ∩ B) = v := ⟨_, rfl⟩
  have hdec (x : ZMod p) := rep_eq_rep_inter_union_add_rep_sdiff A' B x
  rcases le_or_gt t v with htv | htv
  · have := ih v (by omega) (A := A' ∪ B) (B := A' ∩ B) (t := t) (by omega) (by omega) hv
    rw [sum_min_rep_comm, show #(A' ∪ B) + #(A' ∩ B) = #A + #B by omega] at this
    refine this.trans (sum_le_sum fun x _ ↦ ?_)
    rw [hdec x]
    omega
  · have h₁ := sum_min_rep_of_card_left_le (A' ∩ B) (A' ∪ B) v hv.le
    have h₂ := ih _ (by omega) (A := A' \ B) (B := B \ A') (t := t - v) (by omega) (by omega)
      rfl
    calc t * min p (#A + #B - t)
        ≤ v * #(A' ∪ B) + (t - v) * min p (#(A' \ B) + #(B \ A') - (t - v)) := by
          rw [show #(A' ∪ B) = #A + #B - v by omega,
            show #(A' \ B) + #(B \ A') - (t - v) = #A + #B - v - t by omega]
          exact mul_min_le_mul_add_mul_min htv.le (by omega)
      _ ≤ ∑ x, min (rep (A' ∩ B) (A' ∪ B) x) v +
            ∑ x, min (rep (A' \ B) (B \ A') x) (t - v) := by
          rw [h₁, hv]
          exact Nat.add_le_add_left h₂ _
      _ = ∑ x, (min (rep (A' ∩ B) (A' ∪ B) x) v +
            min (rep (A' \ B) (B \ A') x) (t - v)) := sum_add_distrib.symm
      _ ≤ ∑ x, min (rep A' B x) t := sum_le_sum fun x _ ↦ by rw [hdec x]; omega

/-- **Pollard's theorem** for `ZMod p`, `p` prime. -/
theorem pollard {p : ℕ} [Fact p.Prime] (A B : Finset (ZMod p)) (t : ℕ) (hA : t ≤ #A)
    (hB : t ≤ #B) : t * min p (#A + #B - t) ≤ ∑ x, min (rep A B x) t := by
  rcases le_total #B #A with h | h
  · exact pollard_of_card_le h hB
  · rw [sum_min_rep_comm, add_comm]
    exact pollard_of_card_le h hA

/-- Pollard's theorem without size restrictions on `t`. -/
theorem pollard' {p : ℕ} [Fact p.Prime] (A B : Finset (ZMod p)) (t : ℕ) :
    min (t * p) (min (t * (#A + #B - t)) (#A * #B)) ≤ ∑ x, min (rep A B x) t := by
  by_cases hA : #A ≤ t
  · rw [sum_min_rep_of_card_left_le A B t hA]
    exact (min_le_right _ _).trans (min_le_right _ _)
  by_cases hB : #B ≤ t
  · rw [sum_min_rep_of_card_right_le A B t hB]
    exact (min_le_right _ _).trans (min_le_right _ _)
  refine le_trans ?_ (pollard A B t (not_le.mp hA).le (not_le.mp hB).le)
  rw [← min_mul_mul_left]
  exact min_le_min_left _ (min_le_left _ _)

end Erdos5.Pollard
