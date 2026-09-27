/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Erdos5LimitPoints.Pollard

/-!
# Pollard's inequality on the circle

For measurable sets `A, B` in the circle `𝕋 = ℝ / Tℤ` (with Haar measure `λ` of total mass `T`)
let `r(x) = λ(A ∩ (x - B))` be the convolution `𝟙_A * 𝟙_B`. We prove the continuous analogue of
Pollard's theorem:

  `∫ min (r x) t dx ≥ min (t T) (min (t (λA + λB - t)) (λA λB))`.

This is the only additive-combinatorial input on the circle needed in the proof of the circle
lemma (`Erdos5.Circle.circle_lemma`). It is deduced from Pollard's theorem in `ZMod N` for
primes `N → ∞` by discretisation: writing points of the circle as `φ + k T / N` with
`φ ∈ [0, T / N)` and `k ∈ ZMod N`, the convolution `r` is an average over `φ` of discrete
representation functions, and the sizes of the discretised sets `{k | φ + k T / N ∈ A}` converge
in mean (over `φ`) to `N λ(A) / T` as `N → ∞`.

## Implementation notes

Instead of integrating over a fundamental domain `[0, T / N)` we average over the whole circle:
for a measurable `g ≥ 0` we have `∫ φ, ∑ₖ g (φ + k T / N) = N ∫ g` by translation invariance
(`Erdos5.Circle.lintegral_sum_grid`), and all functions of `φ` that occur are invariant under
translation by `T / N`.

The convergence in mean of the discretised measures (`Erdos5.Circle.exists_riemannError_le`) is
proved by approximating `𝟙_A` in `L¹` by a continuous function, whose Riemann sums converge
uniformly.
-/

open MeasureTheory Set
open scoped ENNReal BoundedContinuousFunction

namespace Erdos5.Circle

/-! ### The real-valued Pollard bound -/

/-- The real-valued Pollard bound `min (s T) (min (s (a + b - s)) (a b))`. -/
noncomputable def pollardFun (T a b s : ℝ) : ℝ := min (s * T) (min (s * (a + b - s)) (a * b))

/-- The lower bound in Pollard's theorem in `ZMod p`. -/
def pollardBound (p a b t : ℕ) : ℕ := min (t * p) (min (t * (a + b - t)) (a * b))

/-- `pollardFun` is Lipschitz in all its arguments, as long as they lie in `[0, T]`. -/
theorem pollardFun_le_add {T a b s α β t : ℝ} (hT : 0 ≤ T) (ha : a ≤ T) (hb₀ : 0 ≤ b)
    (hb : b ≤ T) (hα₀ : 0 ≤ α) (hα : α ≤ T) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    pollardFun T α β t ≤
      pollardFun T a b s + (T * |α - a| + T * |β - b| + 2 * T * (t - s)) := by
  have ht₀ : 0 ≤ t := hs.trans hst
  have hαa : t * (α - a) ≤ T * |α - a| :=
    (mul_le_mul_of_nonneg_left (le_abs_self _) ht₀).trans
      (mul_le_mul_of_nonneg_right ht (abs_nonneg _))
  have hβb : t * (β - b) ≤ T * |β - b| :=
    (mul_le_mul_of_nonneg_left (le_abs_self _) ht₀).trans
      (mul_le_mul_of_nonneg_right ht (abs_nonneg _))
  have hαβ : α * (β - b) ≤ T * |β - b| :=
    (mul_le_mul_of_nonneg_left (le_abs_self _) hα₀).trans
      (mul_le_mul_of_nonneg_right hα (abs_nonneg _))
  have hbα : b * (α - a) ≤ T * |α - a| :=
    (mul_le_mul_of_nonneg_left (le_abs_self _) hb₀).trans
      (mul_le_mul_of_nonneg_right hb (abs_nonneg _))
  have hts : (t - s) * (a + b - t - s) ≤ (t - s) * (2 * T) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h₁ : 0 ≤ T * |α - a| := mul_nonneg hT (abs_nonneg _)
  have h₂ : 0 ≤ T * |β - b| := mul_nonneg hT (abs_nonneg _)
  have h₃ : 0 ≤ T * (t - s) := mul_nonneg hT (by linarith)
  unfold pollardFun
  rw [← sub_le_iff_le_add]
  refine le_min ?_ (le_min ?_ ?_) <;> rw [sub_le_iff_le_add]
  · exact (min_le_left _ _).trans (by nlinarith)
  · exact (min_le_right _ _).trans ((min_le_left _ _).trans (by nlinarith))
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (by nlinarith))

/-- The discrete Pollard bound, rescaled by `(T / N) ^ 2`, dominates the real Pollard bound. -/
theorem pollardFun_le_pollardBound {T : ℝ} {N : ℕ} (hN : N ≠ 0) (a b τ : ℕ) :
    pollardFun T (T / N * a) (T / N * b) (T / N * τ) ≤ (T / N) ^ 2 * pollardBound N a b τ := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hsub : (a + b - τ : ℝ) ≤ ((a + b - τ : ℕ) : ℝ) := by
    rcases le_total τ (a + b) with h | h
    · rw [Nat.cast_sub h]
      push_cast
      rfl
    · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero]
      have : ((a + b : ℕ) : ℝ) ≤ τ := Nat.cast_le.2 h
      push_cast at this
      linarith
  simp only [pollardBound, pollardFun, Nat.cast_min, Nat.cast_mul]
  rw [mul_min_of_nonneg _ _ (sq_nonneg _), mul_min_of_nonneg _ _ (sq_nonneg _)]
  refine min_le_min (le_of_eq ?_) (min_le_min ?_ (le_of_eq ?_))
  · field_simp
  · calc T / N * τ * (T / N * a + T / N * b - T / N * τ) = (T / N) ^ 2 * (τ * (a + b - τ)) := by
          ring
      _ ≤ (T / N) ^ 2 * (τ * ((a + b - τ : ℕ) : ℝ)) := by gcongr
  · ring

/-- The extended-real Pollard bound agrees with the real one. -/
theorem min_ofReal_eq_ofReal_pollardFun {T a b s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 ≤ s) :
    min (ENNReal.ofReal s * ENNReal.ofReal T)
        (min (ENNReal.ofReal s * (ENNReal.ofReal a + ENNReal.ofReal b - ENNReal.ofReal s))
          (ENNReal.ofReal a * ENNReal.ofReal b)) =
      ENNReal.ofReal (pollardFun T a b s) := by
  rw [pollardFun, ENNReal.ofReal_min, ENNReal.ofReal_min, ENNReal.ofReal_mul hs,
    ENNReal.ofReal_mul hs, ENNReal.ofReal_mul ha, ENNReal.ofReal_sub _ hs, ENNReal.ofReal_add ha hb]

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The convolution `(𝟙_A * 𝟙_B)(x) = λ(A ∩ (x - B))` of two subsets of the circle. -/
noncomputable def conv (A B : Set (AddCircle T)) (x : AddCircle T) : ℝ≥0∞ :=
  volume (A ∩ (fun y => x - y) ⁻¹' B)

/-- The discrete Pollard bound, rescaled, dominates the real Pollard bound (`ℝ≥0∞` version). -/
theorem ofReal_pollardFun_le_pollardBound {N : ℕ} (hN : N ≠ 0) (a b τ : ℕ) :
    ENNReal.ofReal (pollardFun T (T / N * a) (T / N * b) (T / N * τ)) ≤
      ENNReal.ofReal (T / N) ^ 2 * pollardBound N a b τ := by
  rw [← ENNReal.ofReal_pow (div_nonneg hT.out.le (Nat.cast_nonneg _)), ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (pollardFun_le_pollardBound hN a b τ)

/-! ### The grid `ZMod N → 𝕋` -/

section Grid

variable (N : ℕ) [NeZero N]

/-- The embedding `k ↦ k T / N` of `ZMod N` into the circle `ℝ / Tℤ`. -/
noncomputable def grid : ZMod N →+ AddCircle T :=
  ZMod.lift N ⟨zmultiplesHom _ ((T / N : ℝ) : AddCircle T), by
    rw [zmultiplesHom_apply, ← AddCircle.coe_zsmul, zsmul_eq_mul, Int.cast_natCast,
      mul_div_cancel₀ _ (Nat.cast_ne_zero.2 (NeZero.ne N)), AddCircle.coe_period]⟩

omit hT in
/-- The grid point `m T / N` for an integer `m`. -/
theorem grid_intCast (m : ℤ) : grid N (m : ZMod N) = ((m * (T / N) : ℝ) : AddCircle T) := by
  rw [grid, ZMod.lift_coe, zmultiplesHom_apply, ← AddCircle.coe_zsmul, zsmul_eq_mul]

/-- `N` grid steps make up the whole circle. -/
theorem ofReal_div_mul_natCast : ENNReal.ofReal (T / N) * N = ENNReal.ofReal T := by
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (div_nonneg hT.out.le (Nat.cast_nonneg _)),
    div_mul_cancel₀ _ (Nat.cast_ne_zero.2 (NeZero.ne N))]

/-- Every point of the circle is within `T / N` of a grid translate of `φ`. -/
theorem exists_dist_grid_le (φ ψ : AddCircle T) : ∃ j : ZMod N, dist (φ + grid N j) ψ ≤ T / N := by
  have hh : 0 < T / N := div_pos hT.out (Nat.cast_pos.2 (NeZero.pos N))
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective (ψ - φ)
  set m := ⌊r / (T / N)⌋
  have h₁ : (m : ℝ) * (T / N) ≤ r := (le_div_iff₀ hh).1 (Int.floor_le _)
  have h₂ : r < (m + 1) * (T / N) := (div_lt_iff₀ hh).1 (Int.lt_floor_add_one _)
  refine ⟨(m : ZMod N), ?_⟩
  calc dist (φ + grid N m) ψ = ‖((m * (T / N) - r : ℝ) : AddCircle T)‖ := by
        rw [dist_eq_norm, grid_intCast, QuotientAddGroup.mk_sub, hr]
        congr 1
        abel
    _ ≤ ‖(m * (T / N) - r : ℝ)‖ := QuotientAddGroup.norm_mk_le_norm
    _ ≤ T / N := by
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith

omit hT in
/-- Sums over the grid translates of `φ` are invariant under grid translations of `φ`. -/
theorem sum_grid_add_grid {M : Type*} [AddCommMonoid M] (g : AddCircle T → M) (φ : AddCircle T)
    (j : ZMod N) : ∑ k, g (φ + grid N j + grid N k) = ∑ k, g (φ + grid N k) := by
  simp_rw [add_assoc, ← map_add]
  exact Fintype.sum_equiv (Equiv.addLeft j) _ _ fun _ => rfl

/-- Summing a function over the grid translates of `φ` and integrating over `φ` gives `N` times
its integral. -/
theorem lintegral_sum_grid {g : AddCircle T → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ φ, ∑ k : ZMod N, g (φ + grid N k) = N * ∫⁻ x, g x := by
  rw [lintegral_finsetSum (f := fun k φ => g (φ + grid N k)) _ fun _ _ =>
    hg.comp (measurable_add_const _)]
  simp [lintegral_add_right_eq_self]

/-- Summing a function over the grid translates of `φ` and integrating over `φ` gives `N` times
its integral (Bochner integral version). -/
theorem integral_sum_grid {g : AddCircle T → ℝ} (hg : Integrable g) :
    ∫ φ, ∑ k : ZMod N, g (φ + grid N k) = N * ∫ x, g x := by
  rw [integral_finsetSum _ fun _ _ => hg.comp_add_right _]
  simp [integral_add_right_eq_self]

open Classical in
/-- The discretisation `{k | φ + k T / N ∈ A}` of a set `A` of the circle at offset `φ`. -/
noncomputable def gridSet (A : Set (AddCircle T)) (φ : AddCircle T) : Finset (ZMod N) :=
  Finset.univ.filter fun k => φ + grid N k ∈ A

omit hT in
@[simp]
theorem mem_gridSet {A : Set (AddCircle T)} {φ : AddCircle T} {k : ZMod N} :
    k ∈ gridSet N A φ ↔ φ + grid N k ∈ A := by
  simp [gridSet]

omit hT in
/-- A discretised set has at most `N` elements. -/
theorem card_gridSet_le (A : Set (AddCircle T)) (φ : AddCircle T) : (gridSet N A φ).card ≤ N :=
  (Finset.card_le_univ _).trans_eq (ZMod.card N)

omit hT in
/-- The size of a discretised set as a sum of indicator functions. -/
theorem natCast_card_gridSet (A : Set (AddCircle T)) (φ : AddCircle T) :
    ((gridSet N A φ).card : ℝ) = ∑ k : ZMod N, A.indicator 1 (φ + grid N k) := by
  classical
  rw [gridSet, Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Set.indicator_apply]

omit hT in
/-- The size of the discretisation of a measurable set depends measurably on the offset. -/
theorem measurable_natCast_card_gridSet {A : Set (AddCircle T)} (hA : MeasurableSet A) :
    Measurable fun φ : AddCircle T => ((gridSet N A φ).card : ℝ) := by
  simp_rw [natCast_card_gridSet]
  exact Finset.measurable_sum _ fun _ _ =>
    (measurable_one.indicator hA).comp (measurable_add_const _)

end Grid

/-! ### The convolution as an average of discrete convolutions -/

section Discrete

variable {A B : Set (AddCircle T)}

/-- The convolution as the integral of `y ↦ 𝟙_A(y) 𝟙_B(x - y)`. -/
theorem conv_eq_lintegral (hA : MeasurableSet A) (hB : MeasurableSet B) (x : AddCircle T) :
    conv A B x = ∫⁻ y, A.indicator 1 y * B.indicator 1 (x - y) := by
  rw [conv, ← lintegral_indicator_one (hA.inter (hB.preimage (measurable_const_sub x)))]
  congr 1 with y
  by_cases hy : y ∈ A <;> by_cases hy' : x - y ∈ B <;> simp [hy, hy']

/-- The total mass of the convolution is `λ(A) λ(B)`. -/
theorem lintegral_conv (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫⁻ x, conv A B x = volume A * volume B := by
  have hA' : Measurable (A.indicator (1 : AddCircle T → ℝ≥0∞)) := measurable_one.indicator hA
  have hB' : Measurable (B.indicator (1 : AddCircle T → ℝ≥0∞)) := measurable_one.indicator hB
  have hmeas : Measurable
      (Function.uncurry fun x y : AddCircle T =>
        A.indicator (1 : AddCircle T → ℝ≥0∞) y * B.indicator 1 (x - y)) := by
    fun_prop
  simp_rw [conv_eq_lintegral hA hB]
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  calc ∫⁻ y, ∫⁻ x, A.indicator 1 y * B.indicator 1 (x - y) = ∫⁻ y, A.indicator 1 y * volume B := by
        refine lintegral_congr fun y => ?_
        rw [lintegral_const_mul (f := fun x => B.indicator 1 (x - y)) _
            (hB'.comp (measurable_id.sub_const y)),
          lintegral_sub_right_eq_self (B.indicator 1) y, lintegral_indicator_one hB]
    _ = volume A * volume B := by
        rw [lintegral_mul_const _ hA', lintegral_indicator_one hA]

variable (N : ℕ) [NeZero N]

variable (A B) in
/-- The discrete convolution at offset `φ`: the number of `k` with `φ + k T / N ∈ A` and
`x - (φ + k T / N) ∈ B`. -/
noncomputable def gridCount (φ x : AddCircle T) : ℝ≥0∞ :=
  ∑ k : ZMod N, A.indicator 1 (φ + grid N k) * B.indicator 1 (x - (φ + grid N k))

omit hT in
/-- The discrete convolution is jointly measurable in the offset and the point. -/
theorem measurable_gridCount (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Measurable (Function.uncurry (gridCount A B N)) :=
  Finset.measurable_sum _ fun _ _ =>
    ((measurable_one.indicator hA).comp (measurable_fst.add_const _)).mul
      ((measurable_one.indicator hB).comp (measurable_snd.sub (measurable_fst.add_const _)))

/-- Averaging the discrete convolutions over the offset recovers `N` times the convolution. -/
theorem lintegral_gridCount (hA : MeasurableSet A) (hB : MeasurableSet B) (x : AddCircle T) :
    ∫⁻ φ, gridCount A B N φ x = N * conv A B x := by
  rw [conv_eq_lintegral hA hB, ← lintegral_sum_grid N]
  · rfl
  · exact (measurable_one.indicator hA).mul
      ((measurable_one.indicator hB).comp (measurable_const.sub measurable_id))

omit hT in
/-- At the points `ψ + k T / N + φ` the discrete convolution is a representation function
in `ZMod N`. -/
theorem gridCount_add_grid (φ ψ : AddCircle T) (m : ZMod N) :
    gridCount A B N φ (ψ + grid N m + φ) =
      (Pollard.rep (gridSet N A φ) (gridSet N B ψ) m : ℝ≥0∞) := by
  classical
  rw [Pollard.rep, Finset.natCast_card_filter, gridSet, Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show ψ + grid N m + φ - (φ + grid N k) = ψ + grid N (m - k) by rw [map_sub]; abel]
  by_cases h₁ : φ + grid N k ∈ A <;> by_cases h₂ : ψ + grid N (m - k) ∈ B <;>
    simp [h₁, Set.indicator_apply]

/-- Pollard's theorem in `ZMod N` bounds the integral of the truncated discrete convolution. -/
theorem lintegral_pollardBound_le [Fact N.Prime] {t : ℝ≥0∞} {τ : ℕ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hτ : ENNReal.ofReal (T / N) * τ ≤ t)
    (φ : AddCircle T) :
    ∫⁻ ψ, ENNReal.ofReal (T / N) *
        pollardBound N (gridSet N A φ).card (gridSet N B ψ).card τ ≤
      N * ∫⁻ x, min (ENNReal.ofReal (T / N) * gridCount A B N φ x) t := by
  set h := ENNReal.ofReal (T / N)
  set F : AddCircle T → ℝ≥0∞ := fun x => min (h * gridCount A B N φ x) t with hF
  have hFm : Measurable F :=
    ((measurable_gridCount N hA hB).of_uncurry_left.const_mul h).min measurable_const
  calc ∫⁻ ψ, h * pollardBound N (gridSet N A φ).card (gridSet N B ψ).card τ
      ≤ ∫⁻ ψ, ∑ m : ZMod N, F (ψ + grid N m + φ) := lintegral_mono fun ψ => ?_
    _ = N * ∫⁻ y, F (y + φ) := lintegral_sum_grid N (hFm.comp (measurable_add_const φ))
    _ = N * ∫⁻ x, F x := by rw [lintegral_add_right_eq_self F φ]
  have hP := Pollard.pollard' (gridSet N A φ) (gridSet N B ψ) τ
  calc h * (pollardBound N (gridSet N A φ).card (gridSet N B ψ).card τ : ℝ≥0∞)
      ≤ h * ∑ m : ZMod N, ((min (Pollard.rep (gridSet N A φ) (gridSet N B ψ) m) τ : ℕ) : ℝ≥0∞) := by
        gcongr
        exact_mod_cast hP
    _ = ∑ m : ZMod N, h * ((min (Pollard.rep (gridSet N A φ) (gridSet N B ψ) m) τ : ℕ) : ℝ≥0∞) :=
        Finset.mul_sum _ _ _
    _ ≤ ∑ m : ZMod N, F (ψ + grid N m + φ) := by
        gcongr with m
        simp only [hF, gridCount_add_grid]
        exact le_min (mul_le_mul_right (Nat.cast_le.2 (min_le_left _ _)) _)
          ((mul_le_mul_right (Nat.cast_le.2 (min_le_right _ _)) _).trans hτ)

/-- Averaging the truncated discrete convolutions over `φ` bounds the truncated convolution. -/
theorem lintegral_lintegral_min_gridCount_le (hA : MeasurableSet A) (hB : MeasurableSet B)
    (t : ℝ≥0∞) :
    ∫⁻ φ, ∫⁻ x, min (ENNReal.ofReal (T / N) * gridCount A B N φ x) t ≤
      ENNReal.ofReal T * ∫⁻ x, min (conv A B x) t := by
  set h := ENNReal.ofReal (T / N)
  have hmeas : Measurable (Function.uncurry fun φ x => min (h * gridCount A B N φ x) t) :=
    ((measurable_gridCount N hA hB).const_mul h).min measurable_const
  rw [lintegral_lintegral_swap hmeas.aemeasurable, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x => ?_
  rw [mul_min]
  refine le_min ?_ ?_
  · calc ∫⁻ φ, min (h * gridCount A B N φ x) t ≤ ∫⁻ φ, h * gridCount A B N φ x :=
          lintegral_mono fun _ => min_le_left _ _
      _ = ENNReal.ofReal T * conv A B x := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_gridCount N hA hB,
            ← mul_assoc, ofReal_div_mul_natCast]
  · calc ∫⁻ φ, min (h * gridCount A B N φ x) t ≤ ∫⁻ _, t := lintegral_mono fun _ => min_le_right _ _
      _ = ENNReal.ofReal T * t := by rw [lintegral_const, AddCircle.measure_univ, mul_comm]

/-- **Discretised Pollard bound**: for a prime `N` and `τ T / N ≤ t`, the average over `φ, ψ` of
the rescaled discrete Pollard bound for the discretisations of `A` at `φ` and of `B` at `ψ` is at
most `∫ min (conv A B x) t`. -/
theorem lintegral_lintegral_pollardBound_le [Fact N.Prime] {t : ℝ≥0∞} {τ : ℕ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hτ : ENNReal.ofReal (T / N) * τ ≤ t) :
    ∫⁻ φ, ∫⁻ ψ, ENNReal.ofReal (T / N) ^ 2 *
        pollardBound N (gridSet N A φ).card (gridSet N B ψ).card τ ≤
      ENNReal.ofReal T ^ 2 * ∫⁻ x, min (conv A B x) t := by
  set h := ENNReal.ofReal (T / N)
  calc ∫⁻ φ, ∫⁻ ψ, h ^ 2 * pollardBound N (gridSet N A φ).card (gridSet N B ψ).card τ
      = h * ∫⁻ φ, ∫⁻ ψ, h * pollardBound N (gridSet N A φ).card (gridSet N B ψ).card τ := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1 with φ
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1 with ψ
        ring
    _ ≤ h * ∫⁻ φ, N * ∫⁻ x, min (h * gridCount A B N φ x) t := by
        gcongr with φ
        exact lintegral_pollardBound_le N hA hB hτ φ
    _ = h * N * ∫⁻ φ, ∫⁻ x, min (h * gridCount A B N φ x) t := by
        rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top N), mul_assoc]
    _ ≤ ENNReal.ofReal T * (ENNReal.ofReal T * ∫⁻ x, min (conv A B x) t) := by
        rw [ofReal_div_mul_natCast]
        gcongr
        exact lintegral_lintegral_min_gridCount_le N hA hB t
    _ = ENNReal.ofReal T ^ 2 * ∫⁻ x, min (conv A B x) t := by ring

end Discrete

/-! ### Convergence of the discretised measures -/

section Riemann

variable (N : ℕ) [NeZero N]

/-- Riemann sums of a continuous function on the circle converge uniformly to its integral. -/
theorem abs_integral_sub_riemannSum_le (g : AddCircle T →ᵇ ℝ) {ω : ℝ}
    (hω : ∀ x y, dist x y ≤ T / N → |g x - g y| ≤ ω) (φ : AddCircle T) :
    |(∫ x, g x) - T / N * ∑ k : ZMod N, g (φ + grid N k)| ≤ T * ω := by
  have hT0 := hT.out
  have hN : (0 : ℝ) < N := Nat.cast_pos.2 (NeZero.pos N)
  set R : AddCircle T → ℝ := fun ψ => T / N * ∑ k : ZMod N, g (ψ + grid N k) with hR
  have hRφ : ∀ ψ, |R ψ - R φ| ≤ T * ω := by
    intro ψ
    obtain ⟨j, hj⟩ := exists_dist_grid_le N φ ψ
    have : R φ = T / N * ∑ k : ZMod N, g (φ + grid N j + grid N k) := by
      rw [sum_grid_add_grid]
    rw [this, hR, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (div_pos hT0 hN)]
    calc T / N * |∑ k : ZMod N, (g (ψ + grid N k) - g (φ + grid N j + grid N k))|
        ≤ T / N * ∑ _k : ZMod N, ω := by
          gcongr
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => hω _ _ ?_)
          rwa [dist_add_right, dist_comm]
      _ = T * ω := by
          simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
          field_simp
  have hRint : Integrable R :=
    (integrable_finsetSum _ fun k _ => (g.integrable _).comp_add_right _).const_mul _
  have hint : ∫ ψ, R ψ = T * ∫ x, g x := by
    rw [hR, integral_const_mul, integral_sum_grid N (g.integrable _)]
    field_simp
  have hdiff : ∫ ψ, (R ψ - R φ) = T * ((∫ x, g x) - R φ) := by
    rw [integral_sub hRint (integrable_const _), integral_const, hint]
    simp [measureReal_def, AddCircle.measure_univ, hT0.le]
    ring
  have hbound : ‖∫ ψ, (R ψ - R φ)‖ ≤ T * ω * volume.real (univ : Set (AddCircle T)) :=
    norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun ψ =>
      (Real.norm_eq_abs _).trans_le (hRφ ψ))
  rw [hdiff, Real.norm_eq_abs, abs_mul, abs_of_pos hT0, measureReal_def, AddCircle.measure_univ,
    ENNReal.toReal_ofReal hT0.le, mul_comm (T * ω)] at hbound
  exact le_of_mul_le_mul_left hbound hT0

variable (T) in
/-- The mean discretisation error `∫ |λ(A) - (T / N) #{k | φ + k T / N ∈ A}| dφ`. -/
noncomputable def riemannError (A : Set (AddCircle T)) : ℝ≥0∞ :=
  ∫⁻ φ, ENNReal.ofReal |(volume A).toReal - T / N * ((gridSet N A φ).card : ℝ)|

/-- The mean discretisation error of a measurable set tends to zero as `N → ∞`. -/
theorem exists_riemannError_le {A : Set (AddCircle T)} (hA : MeasurableSet A) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ (N : ℕ) [NeZero N], N₀ ≤ N → riemannError T N A ≤ ENNReal.ofReal ε := by
  have hT0 := hT.out
  set f : AddCircle T → ℝ := A.indicator 1 with hf
  have hfm : Measurable f := measurable_one.indicator hA
  have hfi : Integrable f := (integrable_const (1 : ℝ)).indicator hA
  set δ := ε / (3 * T) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨g, hg, -⟩ :=
    hfi.exists_boundedContinuous_lintegral_sub_le (ENNReal.ofReal_pos.2 hδ0).ne'
  set ω := ε / (3 * T ^ 2) with hω
  have hω0 : 0 < ω := by positivity
  obtain ⟨η, hη, hgη⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous g.continuous) ω hω0
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (T / η)
  refine ⟨N₀, fun N _ hN => ?_⟩
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (NeZero.pos N)
  have hTN : T / N < η := by
    have h₁ : (N₀ : ℝ) ≤ N := Nat.cast_le.2 hN
    rw [div_lt_iff₀ hNpos]
    rw [div_lt_iff₀ hη] at hN₀
    nlinarith
  have hunif := abs_integral_sub_riemannSum_le N g (ω := ω) fun x y hxy => by
    have := hgη (hxy.trans_lt hTN)
    rw [Real.dist_eq] at this
    exact this.le
  have hfg : |(∫ x, f x) - ∫ x, g x| ≤ δ := by
    rw [← integral_sub hfi (g.integrable _), ← ENNReal.ofReal_le_ofReal_iff hδ0.le,
      ← Real.enorm_eq_ofReal_abs]
    exact (enorm_integral_le_lintegral_enorm _).trans hg
  have hα : (volume A).toReal = ∫ x, f x := by rw [integral_indicator_one hA, measureReal_def]
  have hpt : ∀ φ, ENNReal.ofReal |(volume A).toReal - T / N * ((gridSet N A φ).card : ℝ)| ≤
      ENNReal.ofReal (δ + T * ω) +
        ENNReal.ofReal (T / N) * ∑ k : ZMod N, ‖f (φ + grid N k) - g (φ + grid N k)‖ₑ := by
    intro φ
    have h₂ : |T / N * ∑ k : ZMod N, g (φ + grid N k) - T / N * ((gridSet N A φ).card : ℝ)| ≤
        T / N * ∑ k : ZMod N, |f (φ + grid N k) - g (φ + grid N k)| := by
      rw [natCast_card_gridSet, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
        abs_of_pos (div_pos hT0 hNpos)]
      gcongr
      exact (Finset.abs_sum_le_sum_abs _ _).trans_eq
        (Finset.sum_congr rfl fun k _ => abs_sub_comm _ _)
    have h₃ : |(volume A).toReal - T / N * ((gridSet N A φ).card : ℝ)| ≤
        δ + T * ω + T / N * ∑ k : ZMod N, |f (φ + grid N k) - g (φ + grid N k)| := by
      rw [hα]
      have e₁ := abs_sub_le (∫ x, f x) (∫ x, g x) (T / N * ((gridSet N A φ).card : ℝ))
      have e₂ := abs_sub_le (∫ x, g x) (T / N * ∑ k : ZMod N, g (φ + grid N k))
        (T / N * ((gridSet N A φ).card : ℝ))
      linarith [hunif φ]
    calc _ ≤ ENNReal.ofReal
          (δ + T * ω + T / N * ∑ k : ZMod N, |f (φ + grid N k) - g (φ + grid N k)|) :=
          ENNReal.ofReal_le_ofReal h₃
      _ ≤ ENNReal.ofReal (δ + T * ω) +
          ENNReal.ofReal (T / N * ∑ k : ZMod N, |f (φ + grid N k) - g (φ + grid N k)|) :=
          ENNReal.ofReal_add_le
      _ = _ := by
          rw [ENNReal.ofReal_mul (div_nonneg hT0.le hNpos.le),
            ENNReal.ofReal_sum_of_nonneg fun k _ => abs_nonneg _]
          simp_rw [Real.enorm_eq_ofReal_abs]
  have hmeas : Measurable fun x => ‖f x - g x‖ₑ := (hfm.sub g.continuous.measurable).enorm
  calc riemannError T N A
      ≤ ∫⁻ φ, (ENNReal.ofReal (δ + T * ω) +
          ENNReal.ofReal (T / N) * ∑ k : ZMod N, ‖f (φ + grid N k) - g (φ + grid N k)‖ₑ) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (δ + T * ω) * ENNReal.ofReal T +
          ENNReal.ofReal (T / N) * (N * ∫⁻ x, ‖f x - g x‖ₑ) := by
        rw [lintegral_add_left measurable_const, lintegral_const, AddCircle.measure_univ,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_sum_grid N hmeas]
    _ ≤ ENNReal.ofReal (δ + T * ω) * ENNReal.ofReal T + ENNReal.ofReal T * ENNReal.ofReal δ := by
        rw [← mul_assoc, ofReal_div_mul_natCast]
        gcongr
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hT0.le,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        rw [hδ, hω]
        field_simp
        ring

end Riemann

/-! ### Proof of Pollard's inequality on the circle -/

section Main

variable {A B : Set (AddCircle T)}

/-- Integrating a pointwise bound `c ≤ f x + g x` over the circle. -/
theorem mul_le_lintegral_add {c : ℝ≥0∞} {f g : AddCircle T → ℝ≥0∞} (hg : Measurable g)
    (h : ∀ x, c ≤ f x + g x) : ENNReal.ofReal T * c ≤ (∫⁻ x, f x) + ∫⁻ x, g x := by
  calc ENNReal.ofReal T * c = ∫⁻ _, c := by rw [lintegral_const, AddCircle.measure_univ, mul_comm]
    _ ≤ ∫⁻ x, f x + g x := lintegral_mono h
    _ = (∫⁻ x, f x) + ∫⁻ x, g x := lintegral_add_right _ hg

/-- A double-averaging inequality: a pointwise bound `c ≤ X φ ψ + (T Y φ + T Z ψ + W)`
integrates to `T² c ≤ ∫∫ X + T² (∫ Y + ∫ Z + W)`. -/
theorem sq_mul_le_lintegral_lintegral_add {c W : ℝ≥0∞} {X : AddCircle T → AddCircle T → ℝ≥0∞}
    {Y Z : AddCircle T → ℝ≥0∞} (hY : Measurable Y) (hZ : Measurable Z)
    (h : ∀ φ ψ, c ≤ X φ ψ + (ENNReal.ofReal T * Y φ + ENNReal.ofReal T * Z ψ + W)) :
    ENNReal.ofReal T ^ 2 * c ≤
      (∫⁻ φ, ∫⁻ ψ, X φ ψ) + ENNReal.ofReal T ^ 2 * ((∫⁻ φ, Y φ) + (∫⁻ ψ, Z ψ) + W) := by
  set L := ENNReal.ofReal T
  have h₁ : ∀ φ, L * c ≤ (∫⁻ ψ, X φ ψ) + (L * (∫⁻ ψ, Z ψ) + L * (L * Y φ + W)) := by
    intro φ
    refine (mul_le_lintegral_add (f := X φ) (g := fun ψ => L * Z ψ + (L * Y φ + W))
      ((hZ.const_mul L).add measurable_const) fun ψ => (h φ ψ).trans_eq (by ring)).trans_eq ?_
    rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hZ, lintegral_const,
      AddCircle.measure_univ]
    ring
  have h₂ := mul_le_lintegral_add (c := L * c) (f := fun φ => ∫⁻ ψ, X φ ψ)
    (g := fun φ => L * (∫⁻ ψ, Z ψ) + L * (L * Y φ + W))
    (measurable_const.add (((hY.const_mul L).add measurable_const).const_mul L)) h₁
  rw [lintegral_add_left measurable_const, lintegral_const,
    lintegral_const_mul (f := fun φ => L * Y φ + W) _ ((hY.const_mul L).add measurable_const),
    lintegral_add_right _ measurable_const,
    lintegral_const_mul _ hY, lintegral_const, AddCircle.measure_univ] at h₂
  calc L ^ 2 * c = L * (L * c) := by ring
    _ ≤ _ := h₂
    _ = _ := by ring

/-- The main estimate for a fixed prime `N`: Pollard's bound for `A, B, t` holds up to the
discretisation errors. -/
theorem ofReal_pollardFun_le_add (N : ℕ) [Fact N.Prime] (hA : MeasurableSet A)
    (hB : MeasurableSet B) {t : ℝ≥0∞} (ht : t < volume A) :
    ENNReal.ofReal (pollardFun T (volume A).toReal (volume B).toReal t.toReal) ≤
      (∫⁻ x, min (conv A B x) t) +
        (riemannError T N A + riemannError T N B + ENNReal.ofReal (2 * T * (T / N))) := by
  have hT0 := hT.out
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (NeZero.pos N)
  have hh : 0 < T / N := div_pos hT0 hNpos
  set L := ENNReal.ofReal T
  have hvol : ∀ S : Set (AddCircle T), volume S ≤ L := fun S =>
    (measure_mono (subset_univ S)).trans_eq (AddCircle.measure_univ T)
  have hvolr : ∀ S : Set (AddCircle T), (volume S).toReal ≤ T := fun S =>
    ENNReal.toReal_le_of_le_ofReal hT0.le (hvol S)
  have htT : t ≤ L := ht.le.trans (hvol A)
  have htop : t ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top htT
  have htr : t.toReal ≤ T := ENNReal.toReal_le_of_le_ofReal hT0.le htT
  set τ := ⌊t.toReal / (T / N)⌋₊
  have hτ₁ : T / N * τ ≤ t.toReal :=
    (le_div_iff₀' hh).1 (Nat.floor_le (div_nonneg ENNReal.toReal_nonneg hh.le))
  have hτ₂ : t.toReal - T / N * τ ≤ T / N := by
    have h' : t.toReal / (T / N) < τ + 1 := Nat.lt_floor_add_one _
    rw [div_lt_iff₀' hh, mul_add, mul_one] at h'
    linarith
  have hτ : ENNReal.ofReal (T / N) * τ ≤ t := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hh.le, ← ENNReal.ofReal_toReal htop]
    exact ENNReal.ofReal_le_ofReal hτ₁
  have hcard : ∀ (S : Set (AddCircle T)) (χ : AddCircle T),
      T / N * ((gridSet N S χ).card : ℝ) ≤ T := fun S χ => by
    calc T / N * ((gridSet N S χ).card : ℝ) ≤ T / N * N := by
          gcongr
          exact_mod_cast card_gridSet_le N S χ
      _ = T := div_mul_cancel₀ _ hNpos.ne'
  have hpt : ∀ φ ψ, ENNReal.ofReal (pollardFun T (volume A).toReal (volume B).toReal t.toReal) ≤
      ENNReal.ofReal (T / N) ^ 2 * pollardBound N (gridSet N A φ).card (gridSet N B ψ).card τ +
        (L * ENNReal.ofReal |(volume A).toReal - T / N * ((gridSet N A φ).card : ℝ)| +
          L * ENNReal.ofReal |(volume B).toReal - T / N * ((gridSet N B ψ).card : ℝ)| +
          ENNReal.ofReal (2 * T * (T / N))) := by
    intro φ ψ
    have hlip := pollardFun_le_add (a := T / N * (gridSet N A φ).card)
      (b := T / N * (gridSet N B ψ).card) (s := T / N * τ) (α := (volume A).toReal)
      (β := (volume B).toReal) (t := t.toReal) hT0.le (hcard A φ) (by positivity) (hcard B ψ)
      ENNReal.toReal_nonneg (hvolr A) (by positivity) hτ₁ htr
    calc ENNReal.ofReal (pollardFun T (volume A).toReal (volume B).toReal t.toReal)
        ≤ ENNReal.ofReal (pollardFun T (T / N * (gridSet N A φ).card)
            (T / N * (gridSet N B ψ).card) (T / N * τ) +
            (T * |(volume A).toReal - T / N * (gridSet N A φ).card| +
              T * |(volume B).toReal - T / N * (gridSet N B ψ).card| + 2 * T * (T / N))) := by
          refine ENNReal.ofReal_le_ofReal (hlip.trans ?_)
          gcongr
      _ ≤ _ := ENNReal.ofReal_add_le
      _ ≤ _ := by
          gcongr
          · exact ofReal_pollardFun_le_pollardBound (NeZero.ne N) _ _ _
          · rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hT0.le,
              ENNReal.ofReal_mul hT0.le]
  have hY : Measurable fun φ : AddCircle T =>
      ENNReal.ofReal |(volume A).toReal - T / N * ((gridSet N A φ).card : ℝ)| :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.sub ((measurable_natCast_card_gridSet N hA).const_mul _)).abs
  have hZ : Measurable fun ψ : AddCircle T =>
      ENNReal.ofReal |(volume B).toReal - T / N * ((gridSet N B ψ).card : ℝ)| :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.sub ((measurable_natCast_card_gridSet N hB).const_mul _)).abs
  have hmain := sq_mul_le_lintegral_lintegral_add hY hZ hpt
  have hdisc := lintegral_lintegral_pollardBound_le N hA hB hτ
  have hL : L ^ 2 ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.2 hT0).ne'
  have hL' : L ^ 2 ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  rw [← ENNReal.mul_le_mul_iff_right hL hL', mul_add]
  exact hmain.trans (add_le_add hdisc le_rfl)

/-- **Pollard's inequality on the circle.** -/
theorem circle_pollard {A B : Set (AddCircle T)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (t : ℝ≥0∞) :
    min (t * ENNReal.ofReal T) (min (t * (volume A + volume B - t)) (volume A * volume B)) ≤
      ∫⁻ x, min (conv A B x) t := by
  rcases le_or_gt (volume A) t with hAt | htA
  · have hconv : ∀ x, conv A B x ≤ t := fun x => (measure_mono inter_subset_left).trans hAt
    calc _ ≤ volume A * volume B := (min_le_right _ _).trans (min_le_right _ _)
      _ = ∫⁻ x, conv A B x := (lintegral_conv hA hB).symm
      _ = ∫⁻ x, min (conv A B x) t := lintegral_congr fun x => (min_eq_left (hconv x)).symm
  have hT0 := hT.out
  have htop : t ≠ ∞ := htA.ne_top
  have hLHS : min (t * ENNReal.ofReal T) (min (t * (volume A + volume B - t))
      (volume A * volume B)) =
      ENNReal.ofReal (pollardFun T (volume A).toReal (volume B).toReal t.toReal) := by
    rw [← min_ofReal_eq_ofReal_pollardFun ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      ENNReal.toReal_nonneg, ENNReal.ofReal_toReal htop, ENNReal.ofReal_toReal (measure_ne_top _ _),
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hLHS]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε₀ : (0 : ℝ) < ε := hε
  have hε' : (0 : ℝ) < ε / 3 := by positivity
  obtain ⟨N₁, hN₁⟩ := exists_riemannError_le hA hε'
  obtain ⟨N₂, hN₂⟩ := exists_riemannError_le hB hε'
  obtain ⟨N₃, hN₃⟩ := exists_nat_gt (6 * T ^ 2 / ε)
  obtain ⟨N, hN, hNp⟩ := Nat.exists_infinite_primes (max N₁ (max N₂ N₃))
  have := Fact.mk hNp
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hNp.pos
  have hW : 2 * T * (T / N) ≤ ε / 3 := by
    have h₁ : 6 * T ^ 2 / ε < N :=
      hN₃.trans_le (Nat.cast_le.2 (le_of_max_le_right (le_of_max_le_right hN)))
    rw [div_lt_iff₀ hε₀] at h₁
    rw [mul_div_assoc', div_le_iff₀ hNpos]
    nlinarith
  calc ENNReal.ofReal (pollardFun T (volume A).toReal (volume B).toReal t.toReal)
      ≤ (∫⁻ x, min (conv A B x) t) +
          (riemannError T N A + riemannError T N B + ENNReal.ofReal (2 * T * (T / N))) :=
        ofReal_pollardFun_le_add N hA hB htA
    _ ≤ (∫⁻ x, min (conv A B x) t) +
          (ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3)) :=
        add_le_add le_rfl (add_le_add (add_le_add (hN₁ N (le_of_max_le_left hN))
          (hN₂ N (le_of_max_le_left (le_of_max_le_right hN)))) (ENNReal.ofReal_le_ofReal hW))
    _ = (∫⁻ x, min (conv A B x) t) + ε := by
        rw [← ENNReal.ofReal_add hε'.le hε'.le, ← ENNReal.ofReal_add (by positivity) hε'.le,
          show (ε : ℝ) / 3 + ε / 3 + ε / 3 = ε by ring, ENNReal.ofReal_coe_nnreal]

end Main

end Erdos5.Circle
