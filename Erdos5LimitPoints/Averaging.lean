/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Erdos5LimitPoints.LocalContradiction

/-!
# Section 8: averaging, and the proof of Proposition 3.3

We average Corollary 7.4 over `(p, q) = (c₀ + P, c₀ + Q)`, where `(P, Q)` ranges over the
triangle `P, Q ≥ 0`, `P + Q ≤ L` with the weight
`ρ(P, Q) = (k + 1) L⁻² ((P + Q) / L) ^ (k - 1)`, `k = 24 / 13`.
Then `P` (and `Q`) has density `L⁻¹ m(P / L)` with `m(ξ) = (k + 1) / k (1 - ξ ^ k)`, and `P + Q`
has density `L⁻¹ σ(S / L)` with `σ(ξ) = (k + 1) ξ ^ k`; the choice of `k` makes
`12 m + (13 / 2) σ ≡ 37 / 2`. Bounding the probability of non-admissibility by the expected
number of the events `a point lies in E` gives `1 / 4 ≤ (37 / 2) λ(E ∩ [0, T]) / L`, i.e.
`λ(E ∩ [0, T]) ≥ L / 74 = T / 74 - O(1)`.

## Implementation notes

* The weight is written in the coordinates `(S, P)` with `S = P + Q`
  (`Erdos5.Averaging.weight`), so that the density of `S` is an integral of a constant, and the
  density of `P` is a single `rpow` integral; the symmetry `P ↔ Q` becomes `P ↦ S - P`.
* The densities are extended to all of `ℝ` by clamping (`Erdos5.Averaging.mHat`,
  `Erdos5.Averaging.sHat`), which makes them monotone; since `c₀ = 7 r₂ ≥ 4 r₁ + 2 r₂`, all the
  shifts can then be compared with a single point `c₀ + 5 r₂`, and no correction term is needed.
* The union bound (`Erdos5.Setting.one_le_cnt`) counts the events `pt ∈ E` with the
  `ℝ≥0∞`-valued functions `Erdos5.Setting.cnt₁` (events depending on `P` or on `Q`) and
  `Erdos5.Setting.cnt₃` (events depending on `P + Q`).
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos5.Averaging

/-! ### The densities `m̂` and `σ̂` -/

/-- `clampPow ξ = (max 0 (min ξ 1)) ^ k`, `k = 24 / 13`: the power `ξ ^ k` of `ξ` clamped to
`[0, 1]`. -/
noncomputable def clampPow (ξ : ℝ) : ℝ := (max 0 (min ξ 1)) ^ (24 / 13 : ℝ)

lemma clampPow_of_mem {ξ : ℝ} (h0 : 0 ≤ ξ) (h1 : ξ ≤ 1) :
    clampPow ξ = ξ ^ (24 / 13 : ℝ) := by
  rw [clampPow, min_eq_left h1, max_eq_right h0]

lemma monotone_clampPow : Monotone clampPow := fun _ _ hab =>
  Real.rpow_le_rpow (le_max_left _ _) (max_le_max le_rfl (min_le_min hab le_rfl)) (by norm_num)

lemma clampPow_nonneg (ξ : ℝ) : 0 ≤ clampPow ξ := Real.rpow_nonneg (le_max_left _ _) _

lemma clampPow_le_one (ξ : ℝ) : clampPow ξ ≤ 1 :=
  Real.rpow_le_one (le_max_left _ _) (max_le zero_le_one (min_le_right _ _)) (by norm_num)

lemma measurable_clampPow : Measurable clampPow := by
  unfold clampPow
  fun_prop

/-- The (normalised) density `m̂(ξ) = (k + 1) / k · (1 - ξ ^ k)` of `P / L`, `k = 24 / 13`,
extended to `ℝ` by clamping. -/
noncomputable def mHat (ξ : ℝ) : ℝ := 37 / 24 * (1 - clampPow ξ)

/-- The (normalised) density `σ̂(ξ) = (k + 1) ξ ^ k` of `(P + Q) / L`, `k = 24 / 13`, extended
to `ℝ` by clamping. -/
noncomputable def sHat (ξ : ℝ) : ℝ := 37 / 13 * clampPow ξ

lemma mHat_nonneg (ξ : ℝ) : 0 ≤ mHat ξ := by
  have := clampPow_le_one ξ
  unfold mHat
  nlinarith

lemma sHat_nonneg (ξ : ℝ) : 0 ≤ sHat ξ := by
  have := clampPow_nonneg ξ
  unfold sHat
  positivity

lemma antitone_mHat : Antitone mHat := fun _ _ hab => by
  have := monotone_clampPow hab
  unfold mHat
  nlinarith

lemma monotone_sHat : Monotone sHat := fun _ _ hab => by
  have := monotone_clampPow hab
  unfold sHat
  nlinarith

/-- The choice `k = 24 / 13` makes `12 m̂ + (13 / 2) σ̂` constant. -/
lemma twelve_mul_mHat_add (ξ : ℝ) : 12 * mHat ξ + 13 / 2 * sHat ξ = 37 / 2 := by
  unfold mHat sHat
  ring

@[fun_prop]
lemma measurable_mHat : Measurable mHat :=
  measurable_const.mul (measurable_const.sub measurable_clampPow)

@[fun_prop]
lemma measurable_sHat : Measurable sHat := measurable_const.mul measurable_clampPow

/-- `∫_a^L (S / L) ^ r dS = L / (r + 1) · (1 - (a / L) ^ (r + 1))`. -/
lemma lintegral_Icc_div_rpow {a L r : ℝ} (hL : 0 < L) (ha : 0 ≤ a) (haL : a ≤ L)
    (hr : 0 ≤ r) :
    ∫⁻ S in Icc a L, ENNReal.ofReal ((S / L) ^ r) =
      ENNReal.ofReal (L / (r + 1) * (1 - (a / L) ^ (r + 1))) := by
  have hcont : Continuous fun S : ℝ => (S / L) ^ r :=
    (continuous_id.div_const L).rpow_const fun _ => Or.inr hr
  rw [← ofReal_integral_eq_lintegral_ofReal hcont.integrableOn_Icc
    ((ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ fun S hS =>
      Real.rpow_nonneg (div_nonneg (ha.trans hS.1) hL.le) _))]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le haL,
    intervalIntegral.integral_comp_div (fun S => S ^ r) hL.ne',
    integral_rpow (Or.inl (by linarith)), div_self hL.ne', Real.one_rpow, smul_eq_mul]
  ring

/-! ### The weight and its marginals -/

/-- The triangle `0 ≤ P ≤ S ≤ L` in the `(S, P)`-plane. -/
def triangle (L : ℝ) : Set (ℝ × ℝ) := {y | 0 ≤ y.2 ∧ y.2 ≤ y.1 ∧ y.1 ≤ L}

lemma measurableSet_triangle (L : ℝ) : MeasurableSet (triangle L) :=
  (measurableSet_le measurable_const measurable_snd).inter
    ((measurableSet_le measurable_snd measurable_fst).inter
      (measurableSet_le measurable_fst measurable_const))

/-- The averaging weight in the coordinates `(S, P)`, `S = P + Q`: the density
`(k + 1) L⁻² (S / L) ^ (k - 1)`, `k = 24 / 13`, on the triangle `0 ≤ P ≤ S ≤ L`. -/
noncomputable def weight (L : ℝ) : ℝ × ℝ → ℝ≥0∞ :=
  (triangle L).indicator fun y => ENNReal.ofReal (37 / 13 / L ^ 2 * (y.1 / L) ^ (11 / 13 : ℝ))

@[fun_prop]
lemma measurable_weight (L : ℝ) : Measurable (weight L) :=
  (Measurable.ennreal_ofReal (by fun_prop)).indicator (measurableSet_triangle L)

/-- The weight is invariant under `P ↦ S - P`, i.e. under exchanging `P` and `Q`. -/
lemma weight_sub (L S P : ℝ) : weight L (S, S - P) = weight L (S, P) := by
  simp only [weight, indicator, triangle, mem_ofPred_eq]
  congr 1
  apply propext
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨by linarith, by linarith, h3⟩

/-- The density of `P` under the weight: `L⁻¹ m̂(P / L)` on `[0, L]`. -/
noncomputable def margFst (L : ℝ) : ℝ → ℝ≥0∞ :=
  (Icc 0 L).indicator fun P => ENNReal.ofReal (mHat (P / L) / L)

/-- The density of `S = P + Q` under the weight: `L⁻¹ σ̂(S / L)` on `[0, L]`. -/
noncomputable def margSum (L : ℝ) : ℝ → ℝ≥0∞ :=
  (Icc 0 L).indicator fun S => ENNReal.ofReal (sHat (S / L) / L)

@[fun_prop]
lemma measurable_margFst (L : ℝ) : Measurable (margFst L) :=
  ((measurable_mHat.comp (measurable_id.div_const L)).div_const L).ennreal_ofReal.indicator
    measurableSet_Icc

@[fun_prop]
lemma measurable_margSum (L : ℝ) : Measurable (margSum L) :=
  ((measurable_sHat.comp (measurable_id.div_const L)).div_const L).ennreal_ofReal.indicator
    measurableSet_Icc

/-- The marginal density of `P`. -/
lemma lintegral_weight_eq_margFst {L : ℝ} (hL : 0 < L) (P : ℝ) :
    ∫⁻ S, weight L (S, P) = margFst L P := by
  by_cases hP : P ∈ Icc 0 L
  · have h : (fun S => weight L (S, P)) = (Icc P L).indicator fun S =>
        ENNReal.ofReal (37 / 13 / L ^ 2) * ENNReal.ofReal ((S / L) ^ (11 / 13 : ℝ)) := by
      ext S
      simp only [weight, indicator, triangle, mem_ofPred_eq, mem_Icc]
      rw [ENNReal.ofReal_mul (by positivity)]
      congr 1
      exact propext ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hP.1, h.1, h.2⟩⟩
    rw [h, lintegral_indicator measurableSet_Icc, lintegral_const_mul _ (by fun_prop),
      lintegral_Icc_div_rpow hL hP.1 hP.2 (by norm_num), ← ENNReal.ofReal_mul (by positivity),
      margFst, indicator_of_mem hP, mHat, clampPow_of_mem (div_nonneg hP.1 hL.le)
        ((div_le_one hL).2 hP.2), show (11 / 13 : ℝ) + 1 = 24 / 13 by norm_num]
    congr 1
    field_simp
  · have h : (fun S => weight L (S, P)) = fun _ => 0 := by
      ext S
      exact indicator_of_notMem (fun h => hP ⟨h.1, h.2.1.trans h.2.2⟩) _
    rw [h, lintegral_zero, margFst, indicator_of_notMem hP]

/-- The marginal density of `S = P + Q`. -/
lemma lintegral_weight_eq_margSum {L : ℝ} (hL : 0 < L) (S : ℝ) :
    ∫⁻ P, weight L (S, P) = margSum L S := by
  by_cases hS : S ∈ Icc 0 L
  · have h : (fun P => weight L (S, P)) = (Icc 0 S).indicator fun _ =>
        ENNReal.ofReal (37 / 13 / L ^ 2 * (S / L) ^ (11 / 13 : ℝ)) := by
      ext P
      simp only [weight, indicator, triangle, mem_ofPred_eq, mem_Icc]
      congr 1
      exact propext ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hS.2⟩⟩
    have hSL : 0 ≤ S / L := div_nonneg hS.1 hL.le
    rw [h, lintegral_indicator_const measurableSet_Icc, Real.volume_Icc, sub_zero,
      ← ENNReal.ofReal_mul (by positivity), margSum, indicator_of_mem hS, sHat,
      clampPow_of_mem hSL ((div_le_one hL).2 hS.2),
      show (24 / 13 : ℝ) = 11 / 13 + 1 by norm_num, Real.rpow_add' hSL (by norm_num),
      Real.rpow_one]
    congr 1
    field_simp
  · have h : (fun P => weight L (S, P)) = fun _ => 0 := by
      ext P
      exact indicator_of_notMem (fun h => hS ⟨h.1.trans h.2.1, h.2.2⟩) _
    rw [h, lintegral_zero, margSum, indicator_of_notMem hS]

lemma lintegral_margSum {L : ℝ} (hL : 0 < L) : ∫⁻ S, margSum L S = 1 := by
  rw [margSum, lintegral_indicator measurableSet_Icc,
    setLIntegral_congr_fun measurableSet_Icc (g := fun S =>
      ENNReal.ofReal (37 / 13 / L) * ENNReal.ofReal ((S / L) ^ (24 / 13 : ℝ))) fun S hS => by
      dsimp only
      rw [← ENNReal.ofReal_mul (by positivity), sHat,
        clampPow_of_mem (div_nonneg hS.1 hL.le) ((div_le_one hL).2 hS.2)]
      congr 1
      ring,
    lintegral_const_mul _ (by fun_prop), lintegral_Icc_div_rpow hL le_rfl hL.le (by norm_num),
    ← ENNReal.ofReal_mul (by positivity), zero_div, Real.zero_rpow (by norm_num)]
  convert ENNReal.ofReal_one using 2
  field_simp
  norm_num

/-- The weight is a probability density. -/
lemma lintegral_weight {L : ℝ} (hL : 0 < L) : ∫⁻ y, weight L y = 1 := by
  rw [Measure.volume_eq_prod, lintegral_prod _ (measurable_weight L).aemeasurable]
  simp_rw [lintegral_weight_eq_margSum hL]
  exact lintegral_margSum hL

/-- Averaging `g(P)` against the weight: `P` has density `margFst L`. -/
lemma lintegral_weight_mul_comp_snd {L : ℝ} (hL : 0 < L) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y, weight L y * g y.2 = ∫⁻ P, margFst L P * g P := by
  rw [Measure.volume_eq_prod, lintegral_prod_symm _ (by fun_prop)]
  refine lintegral_congr fun P => ?_
  dsimp only
  rw [lintegral_mul_const _ (by exact (measurable_weight L).comp measurable_prodMk_right),
    lintegral_weight_eq_margFst hL]

/-- Averaging `g(S)`, `S = P + Q`, against the weight: `S` has density `margSum L`. -/
lemma lintegral_weight_mul_comp_fst {L : ℝ} (hL : 0 < L) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y, weight L y * g y.1 = ∫⁻ S, margSum L S * g S := by
  rw [Measure.volume_eq_prod, lintegral_prod _ (by fun_prop)]
  refine lintegral_congr fun S => ?_
  dsimp only
  rw [lintegral_mul_const _ (by exact (measurable_weight L).comp measurable_prodMk_left),
    lintegral_weight_eq_margSum hL]

/-- The weight is symmetric in `P` and `Q = S - P`. -/
lemma lintegral_weight_mul_comp_sub (L : ℝ) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y, weight L y * g (y.1 - y.2) = ∫⁻ y, weight L y * g y.2 := by
  rw [Measure.volume_eq_prod, lintegral_prod _ (by fun_prop), lintegral_prod _ (by fun_prop)]
  refine lintegral_congr fun S => ?_
  dsimp only
  rw [← lintegral_sub_left_eq_self (fun P => weight L (S, P) * g P) S]
  simp only [weight_sub]

/-! ### Measure-theoretic helpers -/

/-- Exchanging an integral against a density with an integral over a set of parameters. -/
lemma lintegral_mul_setLIntegral_comm {w : ℝ → ℝ≥0∞} (hw : Measurable w)
    {f : ℝ → ℝ × ℝ → ℝ≥0∞} (hf : Measurable (Function.uncurry f)) (R : Set (ℝ × ℝ)) :
    ∫⁻ u, w u * ∫⁻ x in R, f u x = ∫⁻ x in R, ∫⁻ u, w u * f u x := by
  calc ∫⁻ u, w u * ∫⁻ x in R, f u x = ∫⁻ u, ∫⁻ x in R, w u * f u x :=
        lintegral_congr fun u => (lintegral_const_mul _ hf.of_uncurry_left).symm
    _ = ∫⁻ x in R, ∫⁻ u, w u * f u x :=
        lintegral_lintegral_swap ((hw.comp measurable_fst).mul hf).aemeasurable

/-- `f v * (if p then g v else 0)` is measurable. -/
lemma measurable_mul_ite {f g : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (p : Prop)
    {_ : Decidable p} : Measurable fun v => f v * (if p then g v else 0) := by
  by_cases hp : p <;> simp only [hp, ↓reduceIte, mul_zero] <;> fun_prop

lemma volume_square : volume (Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3) = ENNReal.ofReal 9 := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico,
    ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- The area of the region between the graphs of `f` and `g` over `[a, b]`. -/
lemma volume_region {a b : ℝ} {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g) :
    volume {x : ℝ × ℝ | x.1 ∈ Icc a b ∧ x.2 ∈ Icc (f x.1) (g x.1)} =
      ∫⁻ z in Icc a b, ENNReal.ofReal (g z - f z) := by
  have hmeas : MeasurableSet {x : ℝ × ℝ | x.1 ∈ Icc a b ∧ x.2 ∈ Icc (f x.1) (g x.1)} :=
    (measurable_fst measurableSet_Icc).inter
      ((measurableSet_le (hf.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hg.comp measurable_fst)))
  rw [Measure.volume_eq_prod, Measure.prod_apply hmeas, ← lintegral_indicator measurableSet_Icc]
  refine lintegral_congr fun z => ?_
  by_cases hz : z ∈ Icc a b
  · rw [indicator_of_mem hz, ← Real.volume_Icc]
    congr 1
    ext w
    exact ⟨fun h => h.2, fun h => ⟨hz, h⟩⟩
  · rw [indicator_of_notMem hz]
    convert measure_empty (μ := (volume : Measure ℝ))
    ext w
    exact ⟨fun h => hz h.1, fun h => h.elim⟩

/-- The triangle `{z + w < 3 / 2}` in `[0, 3)²` has area (at most) `9 / 8`. -/
lemma volume_lower_triangle_le :
    volume ({x : ℝ × ℝ | x.1 + x.2 < 3 / 2} ∩ Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3) ≤
      ENNReal.ofReal (9 / 8) := by
  calc _ ≤ volume {x : ℝ × ℝ | x.1 ∈ Icc 0 (3 / 2) ∧
        x.2 ∈ Icc ((fun _ => (0 : ℝ)) x.1) ((fun z => 3 / 2 - z) x.1)} := by
        refine measure_mono ?_
        rintro x ⟨h, ⟨h1, -⟩, h2, -⟩
        have h' : x.1 + x.2 < 3 / 2 := h
        exact ⟨⟨h1, by linarith⟩, h2, by dsimp only; linarith⟩
    _ = ∫⁻ z in Icc 0 (3 / 2), ENNReal.ofReal (3 / 2 - z - 0) :=
        volume_region measurable_const (by fun_prop)
    _ = ENNReal.ofReal (9 / 8) := by
        rw [← ofReal_integral_eq_lintegral_ofReal (by fun_prop : Continuous fun z : ℝ =>
          3 / 2 - z - 0).integrableOn_Icc ((ae_restrict_iff' measurableSet_Icc).mpr
            (ae_of_all _ fun z hz => by dsimp only [Pi.zero_apply]; linarith [hz.2])),
          integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
        simp only [sub_zero]
        rw [intervalIntegral.integral_comp_sub_left (fun z => z), integral_id]
        norm_num

/-- The triangle `{z + w ≥ 9 / 2}` in `[0, 3)²` has area (at most) `9 / 8`. -/
lemma volume_upper_triangle_le :
    volume ({x : ℝ × ℝ | 9 / 2 ≤ x.1 + x.2} ∩ Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3) ≤
      ENNReal.ofReal (9 / 8) := by
  calc _ ≤ volume {x : ℝ × ℝ | x.1 ∈ Icc (3 / 2) 3 ∧
        x.2 ∈ Icc ((fun z => 9 / 2 - z) x.1) ((fun _ => (3 : ℝ)) x.1)} := by
        refine measure_mono ?_
        rintro x ⟨h, ⟨-, h1⟩, -, h2⟩
        have h' : 9 / 2 ≤ x.1 + x.2 := h
        exact ⟨⟨by linarith, h1.le⟩, by dsimp only; linarith, h2.le⟩
    _ = ∫⁻ z in Icc (3 / 2) 3, ENNReal.ofReal (3 - (9 / 2 - z)) :=
        volume_region (by fun_prop) measurable_const
    _ = ENNReal.ofReal (9 / 8) := by
        rw [← ofReal_integral_eq_lintegral_ofReal (by fun_prop : Continuous fun z : ℝ =>
          3 - (9 / 2 - z)).integrableOn_Icc ((ae_restrict_iff' measurableSet_Icc).mpr
            (ae_of_all _ fun z hz => by dsimp only [Pi.zero_apply]; linarith [hz.1])),
          integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
        have e : ∀ z : ℝ, 3 - (9 / 2 - z) = z - 3 / 2 := fun z => by ring
        simp only [e]
        rw [intervalIntegral.integral_comp_sub_right (fun z => z), integral_id]
        norm_num

/-- The integral over `[0, 3)²` of the multiplicity `6 + 2 [z + w < 3 / 2] + 2 [z + w ≥ 9 / 2]`
of the events depending on `P + Q`. -/
lemma setLIntegral_six_add_ite_le :
    ∫⁻ x in Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3,
      (6 + (if x.1 + x.2 < 3 / 2 then (2 : ℝ≥0∞) else 0) +
        (if 9 / 2 ≤ x.1 + x.2 then 2 else 0)) ≤ ENNReal.ofReal (117 / 2) := by
  have hA₁ : MeasurableSet {x : ℝ × ℝ | x.1 + x.2 < 3 / 2} :=
    measurableSet_lt (by fun_prop) measurable_const
  have hA₂ : MeasurableSet {x : ℝ × ℝ | 9 / 2 ≤ x.1 + x.2} :=
    measurableSet_le measurable_const (by fun_prop)
  have e : ∀ x : ℝ × ℝ, (6 + (if x.1 + x.2 < 3 / 2 then (2 : ℝ≥0∞) else 0) +
      (if 9 / 2 ≤ x.1 + x.2 then 2 else 0)) =
      6 + {x : ℝ × ℝ | x.1 + x.2 < 3 / 2}.indicator (fun _ => 2) x +
        {x : ℝ × ℝ | 9 / 2 ≤ x.1 + x.2}.indicator (fun _ => 2) x := by
    intro x
    have i1 : (if x.1 + x.2 < 3 / 2 then (2 : ℝ≥0∞) else 0) =
        {x : ℝ × ℝ | x.1 + x.2 < 3 / 2}.indicator (fun _ => 2) x := by
      by_cases h : x.1 + x.2 < 3 / 2
      · rw [ite_eq_left h, indicator_of_mem (show x ∈ {x : ℝ × ℝ | x.1 + x.2 < 3 / 2} from h)]
      · rw [ite_eq_right h,
          indicator_of_notMem (show x ∉ {x : ℝ × ℝ | x.1 + x.2 < 3 / 2} from h)]
    have i2 : (if 9 / 2 ≤ x.1 + x.2 then (2 : ℝ≥0∞) else 0) =
        {x : ℝ × ℝ | 9 / 2 ≤ x.1 + x.2}.indicator (fun _ => 2) x := by
      by_cases h : 9 / 2 ≤ x.1 + x.2
      · rw [ite_eq_left h, indicator_of_mem (show x ∈ {x : ℝ × ℝ | 9 / 2 ≤ x.1 + x.2} from h)]
      · rw [ite_eq_right h,
          indicator_of_notMem (show x ∉ {x : ℝ × ℝ | 9 / 2 ≤ x.1 + x.2} from h)]
    rw [i1, i2]
  rw [lintegral_congr e, lintegral_add_right _ (measurable_const.indicator hA₂),
    lintegral_add_right _ (measurable_const.indicator hA₁), setLIntegral_const,
    lintegral_indicator_const hA₁, lintegral_indicator_const hA₂, Measure.restrict_apply hA₁,
    Measure.restrict_apply hA₂, volume_square]
  calc _ ≤ 6 * ENNReal.ofReal 9 + 2 * ENNReal.ofReal (9 / 8) + 2 * ENNReal.ofReal (9 / 8) := by
        gcongr
        · exact volume_lower_triangle_le
        · exact volume_upper_triangle_le
    _ = ENNReal.ofReal (117 / 2) := by
        rw [← ENNReal.ofReal_ofNat 6, ← ENNReal.ofReal_ofNat 2,
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (by norm_num) (by norm_num),
          ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        norm_num

lemma card_hexS : hexS.card = 6 := rfl

end Erdos5.Averaging

namespace Erdos5.Setting

open Averaging

variable (S : Setting)

/-! ### Counting the events -/

/-- The indicator function of the overlap set `E`, with values in `ℝ≥0∞`. -/
noncomputable def indE (t : ℝ) : ℝ≥0∞ := S.E.indicator 1 t

@[fun_prop]
lemma measurable_indE : Measurable S.indE := measurable_one.indicator S.measurableSet_E

lemma indE_eq_one {t : ℝ} (ht : S.r₂ ≤ t) (h : ¬ S.EqHolds t) : S.indE t = 1 :=
  indicator_of_mem (S.mem_E_of_not_eqHolds ht h) _

/-- The six points `d⟨s⟩`, `s ∈ S`, lie within `2 r₂` of `d`. -/
lemma pt_bounds_of_mem_hexS {s : ℤ × ℤ} (hs : s ∈ hexS) (d : ℝ) :
    d - 2 * S.r₂ ≤ S.pt d s.1 s.2 ∧ S.pt d s.1 s.2 ≤ d + 2 * S.r₂ := by
  have := S.r₁_pos
  have := S.r₁_lt_r₂
  simp only [hexS, Finset.mem_insert, Finset.mem_singleton] at hs
  unfold pt
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> push_cast <;> constructor <;> linarith

/-- If `d ≥ c₀` is not certified, one of the six points `d⟨s⟩`, `s ∈ S`, lies in `E`. -/
lemma one_le_sum_indE_of_not_certified {d : ℝ} (hd : S.c₀ ≤ d) (h : ¬ S.Certified d) :
    1 ≤ ∑ s ∈ hexS, S.indE (S.pt d s.1 s.2) := by
  have hc₀ : S.c₀ = 7 * S.r₂ := rfl
  obtain ⟨s, hs, hns⟩ : ∃ s ∈ hexS, ¬ S.EqHolds (S.pt d s.1 s.2) := by
    by_contra hc
    push Not at hc
    exact h ⟨hd, hc⟩
  calc 1 = S.indE (S.pt d s.1 s.2) :=
        (S.indE_eq_one (by linarith [(S.pt_bounds_of_mem_hexS hs d).1, S.r₂_pos]) hns).symm
    _ ≤ ∑ s ∈ hexS, S.indE (S.pt d s.1 s.2) :=
        Finset.single_le_sum (f := fun s : ℤ × ℤ => S.indE (S.pt d s.1 s.2))
          (fun _ _ => zero_le) hs

/-- `cnt₁ u z` counts the `s ∈ S` with `(c₀ + u + z r₁)⟨s⟩ ∈ E`: these are the events
responsible for `c₀ + u + z r₁` not being certified. -/
noncomputable def cnt₁ (u z : ℝ) : ℝ≥0∞ :=
  ∑ s ∈ hexS, S.indE (S.pt (S.c₀ + u + z * S.r₁) s.1 s.2)

/-- `cnt₃ v y` counts the events responsible for `2 c₀ + v + y r₁` not being certified and, in
the non-preferred cases `y < 3 / 2` and `y ≥ 9 / 2`, for the failure of the relevant bridge. -/
noncomputable def cnt₃ (v y : ℝ) : ℝ≥0∞ :=
  (∑ s ∈ hexS, S.indE (S.pt (2 * S.c₀ + v + y * S.r₁) s.1 s.2)) +
    (if y < 3 / 2 then S.indE (2 * S.c₀ + v + y * S.r₁ + 2 * S.r₁) +
      S.indE (2 * S.c₀ + v + y * S.r₁ + 3 * S.r₁ - S.r₂) else 0) +
    (if 9 / 2 ≤ y then S.indE (2 * S.c₀ + v + (y - 3) * S.r₁ + 2 * S.r₁) +
      S.indE (2 * S.c₀ + v + (y - 3) * S.r₁ + 3 * S.r₁ - S.r₂) else 0)

@[fun_prop]
lemma measurable_cnt₁_comp {α : Type*} [MeasurableSpace α] {f g : α → ℝ} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun a => S.cnt₁ (f a) (g a) := by
  unfold cnt₁ pt
  fun_prop

@[fun_prop]
lemma measurable_cnt₃_comp {α : Type*} [MeasurableSpace α] {f g : α → ℝ} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun a => S.cnt₃ (f a) (g a) := by
  unfold cnt₃ pt
  exact ((Finset.measurable_sum _ fun _ _ => by fun_prop).add
    (Measurable.ite (measurableSet_lt hg measurable_const) (by fun_prop) measurable_const)).add
    (Measurable.ite (measurableSet_le measurable_const hg) (by fun_prop) measurable_const)

/-- **Union bound.** If `(z, w)` is not admissible for `(p, q) = (c₀ + P, c₀ + Q)`, one of the
events counted by `cnt₁ P z`, `cnt₁ Q w`, `cnt₃ (P + Q) (z + w)` occurs. -/
lemma one_le_cnt {P Q z w : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hz : 0 ≤ z) (hw : 0 ≤ w)
    (h : ¬ S.Admissible (S.c₀ + P) (S.c₀ + Q) z w) :
    1 ≤ S.cnt₁ P z + S.cnt₁ Q w + S.cnt₃ (P + Q) (z + w) := by
  have hc₀ : S.c₀ = 7 * S.r₂ := rfl
  have hr₁ := S.r₁_pos
  have hr₂ := S.r₂_pos
  have hz' : 0 ≤ z * S.r₁ := mul_nonneg hz hr₁.le
  have hw' : 0 ≤ w * S.r₁ := mul_nonneg hw hr₁.le
  have hzw : 0 ≤ (z + w) * S.r₁ := mul_nonneg (add_nonneg hz hw) hr₁.le
  have e1 : S.c₀ + P + (S.c₀ + Q) + (z + w) * S.r₁ = 2 * S.c₀ + (P + Q) + (z + w) * S.r₁ := by
    ring
  have e2 : S.c₀ + P + (S.c₀ + Q) + (z + w + 3) * S.r₁ =
      2 * S.c₀ + (P + Q) + (z + w + 3) * S.r₁ := by ring
  have e3 : S.c₀ + P + (S.c₀ + Q) + (z + w - 3) * S.r₁ =
      2 * S.c₀ + (P + Q) + (z + w - 3) * S.r₁ := by ring
  simp only [Admissible, Bridge, e1, e2, e3, not_and_or, not_imp, not_or] at h
  rcases h with h | h | h | ⟨hlt, -, h⟩ | ⟨hge, -, h⟩
  · calc (1 : ℝ≥0∞) ≤ S.cnt₁ P z := S.one_le_sum_indE_of_not_certified (by linarith) h
      _ ≤ _ := le_add_right (le_add_right le_rfl)
  · calc (1 : ℝ≥0∞) ≤ S.cnt₁ Q w := S.one_le_sum_indE_of_not_certified (by linarith) h
      _ ≤ _ := le_add_right (le_add_left le_rfl)
  · calc (1 : ℝ≥0∞)
        ≤ ∑ s ∈ hexS, S.indE (S.pt (2 * S.c₀ + (P + Q) + (z + w) * S.r₁) s.1 s.2) :=
          S.one_le_sum_indE_of_not_certified (by linarith) h
      _ ≤ _ := le_add_left (by rw [cnt₃]; exact le_add_right (le_add_right le_rfl))
  · have key : 1 ≤ S.indE (2 * S.c₀ + (P + Q) + (z + w) * S.r₁ + 2 * S.r₁) +
        S.indE (2 * S.c₀ + (P + Q) + (z + w) * S.r₁ + 3 * S.r₁ - S.r₂) := by
      rcases h with h | h
      · exact (S.indE_eq_one (by linarith) h).symm.le.trans (le_add_right le_rfl)
      · exact (S.indE_eq_one (by linarith) h).symm.le.trans (le_add_left le_rfl)
    refine le_add_left ?_
    rw [cnt₃, ite_eq_left hlt]
    exact le_add_right (le_add_left key)
  · have h3 : 0 ≤ (z + w - 3) * S.r₁ := mul_nonneg (by linarith) hr₁.le
    have key : 1 ≤ S.indE (2 * S.c₀ + (P + Q) + (z + w - 3) * S.r₁ + 2 * S.r₁) +
        S.indE (2 * S.c₀ + (P + Q) + (z + w - 3) * S.r₁ + 3 * S.r₁ - S.r₂) := by
      rcases h with h | h
      · exact (S.indE_eq_one (by linarith) h).symm.le.trans (le_add_right le_rfl)
      · exact (S.indE_eq_one (by linarith) h).symm.le.trans (le_add_left le_rfl)
    refine le_add_left ?_
    rw [cnt₃, ite_eq_left hge]
    exact le_add_left key

/-- Bounding the measure of the non-admissible pairs by the expected number of events
(Markov's inequality). -/
lemma volume_not_admissible_le {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    volume {x : ℝ × ℝ | x ∈ Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3 ∧
        ¬ S.Admissible (S.c₀ + P) (S.c₀ + Q) x.1 x.2} ≤
      (∫⁻ x in Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3, S.cnt₁ P x.1) +
        (∫⁻ x in Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3, S.cnt₁ Q x.2) +
        ∫⁻ x in Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3, S.cnt₃ (P + Q) (x.1 + x.2) := by
  have h1 : Measurable fun x : ℝ × ℝ => S.cnt₁ P x.1 :=
    S.measurable_cnt₁_comp measurable_const measurable_fst
  have h2 : Measurable fun x : ℝ × ℝ => S.cnt₁ Q x.2 :=
    S.measurable_cnt₁_comp measurable_const measurable_snd
  have h3 : Measurable fun x : ℝ × ℝ => S.cnt₃ (P + Q) (x.1 + x.2) :=
    S.measurable_cnt₃_comp measurable_const (measurable_fst.add measurable_snd)
  have hm : Measurable fun x : ℝ × ℝ =>
      S.cnt₁ P x.1 + S.cnt₁ Q x.2 + S.cnt₃ (P + Q) (x.1 + x.2) := (h1.add h2).add h3
  have h12 : Measurable fun x : ℝ × ℝ => S.cnt₁ P x.1 + S.cnt₁ Q x.2 := h1.add h2
  rw [← lintegral_add_left h1, ← lintegral_add_left h12]
  calc _ ≤ volume ({x | 1 ≤ S.cnt₁ P x.1 + S.cnt₁ Q x.2 + S.cnt₃ (P + Q) (x.1 + x.2)} ∩
        Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3) :=
        measure_mono <| by
          rintro x ⟨hx, hna⟩
          exact ⟨S.one_le_cnt hP hQ hx.1.1 hx.2.1 hna, hx⟩
    _ = (volume.restrict (Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3))
          {x | 1 ≤ S.cnt₁ P x.1 + S.cnt₁ Q x.2 + S.cnt₃ (P + Q) (x.1 + x.2)} :=
        (Measure.restrict_apply (measurableSet_le measurable_const hm)).symm
    _ ≤ _ := (one_mul _).symm.trans_le (mul_meas_ge_le_lintegral₀ hm.aemeasurable 1)

/-! ### The probability of a single event -/

/-- The bound for the probability of an event depending on `P` (or on `Q`) alone. -/
noncomputable def boundFst (L T : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in S.E ∩ Icc 0 T, ENNReal.ofReal (mHat ((t - (S.c₀ + 5 * S.r₂)) / L) / L)

/-- The bound for the probability of an event depending on `P + Q`. -/
noncomputable def boundSum (L T : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in S.E ∩ Icc 0 T, ENNReal.ofReal (sHat ((t - (S.c₀ + 5 * S.r₂)) / L) / L)

/-- The probability that `c₀ + P + c ∈ E`, for a shift `c ≤ 5 r₂`. -/
lemma lintegral_margFst_mul_indE_le {L T c : ℝ} (hL : 0 < L) (hLT : S.c₀ + 5 * S.r₂ + L ≤ T)
    (hc : c ≤ 5 * S.r₂) :
    ∫⁻ P, margFst L P * S.indE (P + (S.c₀ + c)) ≤ S.boundFst L T := by
  calc ∫⁻ P, margFst L P * S.indE (P + (S.c₀ + c))
      = ∫⁻ P, (fun t => margFst L (t - (S.c₀ + c)) * S.indE t) (P + (S.c₀ + c)) := by
        simp only [add_sub_cancel_right]
    _ = ∫⁻ t, margFst L (t - (S.c₀ + c)) * S.indE t :=
        lintegral_add_right_eq_self (fun t => margFst L (t - (S.c₀ + c)) * S.indE t) _
    _ ≤ ∫⁻ t, (S.E ∩ Icc 0 T).indicator
          (fun t => ENNReal.ofReal (mHat ((t - (S.c₀ + 5 * S.r₂)) / L) / L)) t := by
        refine lintegral_mono fun t => ?_
        by_cases ht : t ∈ S.E
        · by_cases hm : t - (S.c₀ + c) ∈ Icc 0 L
          · have htT : t ∈ S.E ∩ Icc 0 T :=
              ⟨ht, S.r₂_pos.le.trans (S.E_subset ht), by linarith [hm.2]⟩
            rw [margFst, indicator_of_mem hm, indE, indicator_of_mem ht, Pi.one_apply, mul_one,
              indicator_of_mem htT]
            exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
              (antitone_mHat (div_le_div_of_nonneg_right (by linarith) hL.le)) hL.le)
          · rw [margFst, indicator_of_notMem hm, zero_mul]
            exact zero_le
        · rw [indE, indicator_of_notMem ht, mul_zero]
          exact zero_le
    _ = S.boundFst L T := lintegral_indicator (S.measurableSet_E.inter measurableSet_Icc) _

/-- The probability that `2 c₀ + (P + Q) + c ∈ E`, for a shift `-2 r₂ ≤ c ≤ 8 r₂`. -/
lemma lintegral_margSum_mul_indE_le {L T c : ℝ} (hL : 0 < L)
    (hLT : 2 * S.c₀ + 8 * S.r₂ + L ≤ T) (hc : -2 * S.r₂ ≤ c) (hc' : c ≤ 8 * S.r₂) :
    ∫⁻ v, margSum L v * S.indE (v + (2 * S.c₀ + c)) ≤ S.boundSum L T := by
  have hc₀ : S.c₀ = 7 * S.r₂ := rfl
  calc ∫⁻ v, margSum L v * S.indE (v + (2 * S.c₀ + c))
      = ∫⁻ v, (fun t => margSum L (t - (2 * S.c₀ + c)) * S.indE t) (v + (2 * S.c₀ + c)) := by
        simp only [add_sub_cancel_right]
    _ = ∫⁻ t, margSum L (t - (2 * S.c₀ + c)) * S.indE t :=
        lintegral_add_right_eq_self (fun t => margSum L (t - (2 * S.c₀ + c)) * S.indE t) _
    _ ≤ ∫⁻ t, (S.E ∩ Icc 0 T).indicator
          (fun t => ENNReal.ofReal (sHat ((t - (S.c₀ + 5 * S.r₂)) / L) / L)) t := by
        refine lintegral_mono fun t => ?_
        by_cases ht : t ∈ S.E
        · by_cases hm : t - (2 * S.c₀ + c) ∈ Icc 0 L
          · have htT : t ∈ S.E ∩ Icc 0 T :=
              ⟨ht, S.r₂_pos.le.trans (S.E_subset ht), by linarith [hm.2]⟩
            rw [margSum, indicator_of_mem hm, indE, indicator_of_mem ht, Pi.one_apply, mul_one,
              indicator_of_mem htT]
            exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
              (monotone_sHat (div_le_div_of_nonneg_right (by linarith) hL.le)) hL.le)
          · rw [margSum, indicator_of_notMem hm, zero_mul]
            exact zero_le
        · rw [indE, indicator_of_notMem ht, mul_zero]
          exact zero_le
    _ = S.boundSum L T := lintegral_indicator (S.measurableSet_E.inter measurableSet_Icc) _

/-- The expected number of events counted by `cnt₁ P z`, for fixed `z ∈ [0, 3]`. -/
lemma lintegral_margFst_mul_cnt₁_le {L T z : ℝ} (hL : 0 < L) (hLT : S.c₀ + 5 * S.r₂ + L ≤ T)
    (hz : z ∈ Icc (0 : ℝ) 3) :
    ∫⁻ u, margFst L u * S.cnt₁ u z ≤ 6 * S.boundFst L T := by
  have hr₁ := S.r₁_pos
  have hr₁₂ := S.r₁_lt_r₂
  simp only [cnt₁, Finset.mul_sum]
  rw [lintegral_finsetSum _ fun s _ => by unfold pt; fun_prop]
  calc _ ≤ ∑ _s ∈ hexS, S.boundFst L T := Finset.sum_le_sum fun s hs => by
        have hb := S.pt_bounds_of_mem_hexS hs 0
        unfold pt at hb
        have e : ∀ u, S.pt (S.c₀ + u + z * S.r₁) s.1 s.2 =
            u + (S.c₀ + (z * S.r₁ + s.1 * S.r₁ + s.2 * S.r₂)) := fun u => by unfold pt; ring
        simp only [e]
        exact S.lintegral_margFst_mul_indE_le hL hLT (by nlinarith [hz.1, hz.2])
    _ = 6 * S.boundFst L T := by rw [Finset.sum_const, card_hexS, nsmul_eq_mul]; norm_num

/-- The expected number of events counted by `cnt₃ (P + Q) y`, for fixed `y ∈ [0, 6]`. -/
lemma lintegral_margSum_mul_cnt₃_le {L T y : ℝ} (hL : 0 < L)
    (hLT : 2 * S.c₀ + 8 * S.r₂ + L ≤ T) (hy : y ∈ Icc (0 : ℝ) 6) :
    ∫⁻ v, margSum L v * S.cnt₃ v y ≤
      (6 + (if y < 3 / 2 then 2 else 0) + (if 9 / 2 ≤ y then 2 else 0)) * S.boundSum L T := by
  have hr₁ := S.r₁_pos
  have hr₁₂ := S.r₁_lt_r₂
  have hyr : 0 ≤ y * S.r₁ := mul_nonneg hy.1 hr₁.le
  have hyr' : y * S.r₁ ≤ 6 * S.r₂ := by nlinarith [hy.2]
  set B := S.boundSum L T
  have hone : ∀ c, -2 * S.r₂ ≤ c → c ≤ 8 * S.r₂ →
      ∫⁻ v, margSum L v * S.indE (v + (2 * S.c₀ + c)) ≤ B :=
    fun c hc hc' => S.lintegral_margSum_mul_indE_le hL hLT hc hc'
  have htwo : ∀ c c', -2 * S.r₂ ≤ c → c ≤ 8 * S.r₂ → -2 * S.r₂ ≤ c' → c' ≤ 8 * S.r₂ →
      ∫⁻ v, margSum L v * (S.indE (v + (2 * S.c₀ + c)) + S.indE (v + (2 * S.c₀ + c'))) ≤
        2 * B := by
    intro c c' h1 h2 h3 h4
    simp only [mul_add]
    rw [lintegral_add_left (by fun_prop), two_mul B]
    exact add_le_add (hone c h1 h2) (hone c' h3 h4)
  have hA : ∫⁻ v, margSum L v *
      ∑ s ∈ hexS, S.indE (S.pt (2 * S.c₀ + v + y * S.r₁) s.1 s.2) ≤ 6 * B := by
    simp only [Finset.mul_sum]
    rw [lintegral_finsetSum _ fun s _ => by unfold pt; fun_prop]
    calc _ ≤ ∑ _s ∈ hexS, B := Finset.sum_le_sum fun s hs => by
          have hb := S.pt_bounds_of_mem_hexS hs 0
          unfold pt at hb
          have e : ∀ v, S.pt (2 * S.c₀ + v + y * S.r₁) s.1 s.2 =
              v + (2 * S.c₀ + (y * S.r₁ + s.1 * S.r₁ + s.2 * S.r₂)) := fun v => by
            unfold pt; ring
          simp only [e]
          exact hone _ (by linarith) (by linarith)
      _ = 6 * B := by rw [Finset.sum_const, card_hexS, nsmul_eq_mul]; norm_num
  have hlow : ∫⁻ v, margSum L v * (if y < 3 / 2 then
      S.indE (2 * S.c₀ + v + y * S.r₁ + 2 * S.r₁) +
        S.indE (2 * S.c₀ + v + y * S.r₁ + 3 * S.r₁ - S.r₂) else 0) ≤
      (if y < 3 / 2 then 2 else 0) * B := by
    by_cases h : y < 3 / 2
    · have e1 : ∀ v, 2 * S.c₀ + v + y * S.r₁ + 2 * S.r₁ =
          v + (2 * S.c₀ + (y * S.r₁ + 2 * S.r₁)) := fun v => by ring
      have e2 : ∀ v, 2 * S.c₀ + v + y * S.r₁ + 3 * S.r₁ - S.r₂ =
          v + (2 * S.c₀ + (y * S.r₁ + 3 * S.r₁ - S.r₂)) := fun v => by ring
      simp only [h, ↓reduceIte, e1, e2]
      exact htwo _ _ (by linarith) (by linarith) (by linarith) (by linarith)
    · simp only [h, ↓reduceIte, mul_zero, lintegral_zero, zero_mul, le_refl]
  have hhigh : ∫⁻ v, margSum L v * (if 9 / 2 ≤ y then
      S.indE (2 * S.c₀ + v + (y - 3) * S.r₁ + 2 * S.r₁) +
        S.indE (2 * S.c₀ + v + (y - 3) * S.r₁ + 3 * S.r₁ - S.r₂) else 0) ≤
      (if 9 / 2 ≤ y then 2 else 0) * B := by
    by_cases h : 9 / 2 ≤ y
    · have h3 : 0 ≤ (y - 3) * S.r₁ := mul_nonneg (by linarith) hr₁.le
      have h3' : (y - 3) * S.r₁ ≤ 3 * S.r₂ := by nlinarith [hy.2]
      have e1 : ∀ v, 2 * S.c₀ + v + (y - 3) * S.r₁ + 2 * S.r₁ =
          v + (2 * S.c₀ + ((y - 3) * S.r₁ + 2 * S.r₁)) := fun v => by ring
      have e2 : ∀ v, 2 * S.c₀ + v + (y - 3) * S.r₁ + 3 * S.r₁ - S.r₂ =
          v + (2 * S.c₀ + ((y - 3) * S.r₁ + 3 * S.r₁ - S.r₂)) := fun v => by ring
      simp only [h, ↓reduceIte, e1, e2]
      exact htwo _ _ (by linarith) (by linarith) (by linarith) (by linarith)
    · simp only [h, ↓reduceIte, mul_zero, lintegral_zero, zero_mul, le_refl]
  calc ∫⁻ v, margSum L v * S.cnt₃ v y
      = (∫⁻ v, margSum L v *
          ∑ s ∈ hexS, S.indE (S.pt (2 * S.c₀ + v + y * S.r₁) s.1 s.2)) +
        (∫⁻ v, margSum L v * (if y < 3 / 2 then
          S.indE (2 * S.c₀ + v + y * S.r₁ + 2 * S.r₁) +
            S.indE (2 * S.c₀ + v + y * S.r₁ + 3 * S.r₁ - S.r₂) else 0)) +
        ∫⁻ v, margSum L v * (if 9 / 2 ≤ y then
          S.indE (2 * S.c₀ + v + (y - 3) * S.r₁ + 2 * S.r₁) +
            S.indE (2 * S.c₀ + v + (y - 3) * S.r₁ + 3 * S.r₁ - S.r₂) else 0) := by
        simp only [cnt₃, mul_add]
        rw [lintegral_add_right _ (measurable_mul_ite (by fun_prop) (by fun_prop) _),
          lintegral_add_right _ (measurable_mul_ite (by fun_prop) (by fun_prop) _)]
    _ ≤ 6 * B + (if y < 3 / 2 then 2 else 0) * B + (if 9 / 2 ≤ y then 2 else 0) * B :=
        add_le_add (add_le_add hA hlow) hhigh
    _ = _ := by ring

/-! ### The averaging argument -/

/-- **Upper bound.** The weighted average of the measure of the non-admissible pairs is at most
`108 · boundFst + (117 / 2) · boundSum`. -/
lemma lintegral_weight_mul_volume_le {L T : ℝ} (hL : 0 < L)
    (hLT : 2 * S.c₀ + 8 * S.r₂ + L ≤ T) :
    ∫⁻ y, weight L y * volume {x : ℝ × ℝ | x ∈ Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3 ∧
        ¬ S.Admissible (S.c₀ + y.2) (S.c₀ + (y.1 - y.2)) x.1 x.2} ≤
      ENNReal.ofReal 108 * S.boundFst L T + ENNReal.ofReal (117 / 2) * S.boundSum L T := by
  have hLT' : S.c₀ + 5 * S.r₂ + L ≤ T := by
    have hc₀ : S.c₀ = 7 * S.r₂ := rfl
    linarith [S.r₂_pos]
  have hR : MeasurableSet (Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3) :=
    measurableSet_Ico.prod measurableSet_Ico
  have hf₁ : Measurable (Function.uncurry fun u (x : ℝ × ℝ) => S.cnt₁ u x.1) :=
    S.measurable_cnt₁_comp measurable_fst measurable_snd.fst
  have hf₂ : Measurable (Function.uncurry fun u (x : ℝ × ℝ) => S.cnt₁ u x.2) :=
    S.measurable_cnt₁_comp measurable_fst measurable_snd.snd
  have hf₃ : Measurable (Function.uncurry fun v (x : ℝ × ℝ) => S.cnt₃ v (x.1 + x.2)) :=
    S.measurable_cnt₃_comp measurable_fst (measurable_snd.fst.add measurable_snd.snd)
  have hG₁ := hf₁.lintegral_prod_right (ν := volume.restrict (Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3))
  have hG₂ := hf₂.lintegral_prod_right (ν := volume.restrict (Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3))
  have hG₃ := hf₃.lintegral_prod_right (ν := volume.restrict (Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3))
  -- the events depending on `P`
  have hP : ∫⁻ y, weight L y * ∫⁻ x in Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3, S.cnt₁ y.2 x.1 ≤
      6 * S.boundFst L T * ENNReal.ofReal 9 := by
    rw [lintegral_weight_mul_comp_snd hL hG₁,
      lintegral_mul_setLIntegral_comm (measurable_margFst L) hf₁]
    calc _ ≤ ∫⁻ _ in Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3, 6 * S.boundFst L T :=
          setLIntegral_mono' hR fun x hx =>
            S.lintegral_margFst_mul_cnt₁_le hL hLT' ⟨hx.1.1, hx.1.2.le⟩
      _ = _ := by rw [setLIntegral_const, volume_square]
  -- the events depending on `Q`
  have hQ : ∫⁻ y, weight L y *
      ∫⁻ x in Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3, S.cnt₁ (y.1 - y.2) x.2 ≤
      6 * S.boundFst L T * ENNReal.ofReal 9 := by
    rw [lintegral_weight_mul_comp_sub L hG₂, lintegral_weight_mul_comp_snd hL hG₂,
      lintegral_mul_setLIntegral_comm (measurable_margFst L) hf₂]
    calc _ ≤ ∫⁻ _ in Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3, 6 * S.boundFst L T :=
          setLIntegral_mono' hR fun x hx =>
            S.lintegral_margFst_mul_cnt₁_le hL hLT' ⟨hx.2.1, hx.2.2.le⟩
      _ = _ := by rw [setLIntegral_const, volume_square]
  -- the events depending on `P + Q`
  have hS : ∫⁻ y, weight L y *
      ∫⁻ x in Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3, S.cnt₃ y.1 (x.1 + x.2) ≤
      ENNReal.ofReal (117 / 2) * S.boundSum L T := by
    have hcoef : Measurable fun x : ℝ × ℝ =>
        (6 + (if x.1 + x.2 < 3 / 2 then (2 : ℝ≥0∞) else 0) +
          (if 9 / 2 ≤ x.1 + x.2 then 2 else 0)) := by
      refine Measurable.fun_add (Measurable.fun_add measurable_const ?_) ?_
      · exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) measurable_const
          measurable_const
      · exact Measurable.ite (measurableSet_le measurable_const (by fun_prop)) measurable_const
          measurable_const
    rw [lintegral_weight_mul_comp_fst hL hG₃,
      lintegral_mul_setLIntegral_comm (measurable_margSum L) hf₃]
    calc _ ≤ ∫⁻ x in Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3,
          (6 + (if x.1 + x.2 < 3 / 2 then (2 : ℝ≥0∞) else 0) +
            (if 9 / 2 ≤ x.1 + x.2 then 2 else 0)) * S.boundSum L T :=
          setLIntegral_mono' hR fun x hx => S.lintegral_margSum_mul_cnt₃_le hL hLT
            ⟨add_nonneg hx.1.1 hx.2.1, by linarith [hx.1.2, hx.2.2]⟩
      _ = (∫⁻ x in Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3,
          (6 + (if x.1 + x.2 < 3 / 2 then (2 : ℝ≥0∞) else 0) +
            (if 9 / 2 ≤ x.1 + x.2 then 2 else 0))) * S.boundSum L T :=
          lintegral_mul_const _ hcoef
      _ ≤ _ := by
          gcongr
          exact setLIntegral_six_add_ite_le
  have h1 : Measurable fun y : ℝ × ℝ =>
      weight L y * ∫⁻ x in Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3, S.cnt₁ y.2 x.1 :=
    (measurable_weight L).mul (hG₁.comp measurable_snd)
  have h12 : Measurable fun y : ℝ × ℝ =>
      weight L y * (∫⁻ x in Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3, S.cnt₁ y.2 x.1) +
        weight L y * ∫⁻ x in Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3, S.cnt₁ (y.1 - y.2) x.2 :=
    h1.add ((measurable_weight L).mul (hG₂.comp (measurable_fst.sub measurable_snd)))
  calc _ ≤ ∫⁻ y, (weight L y * (∫⁻ x in Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3, S.cnt₁ y.2 x.1) +
        weight L y * (∫⁻ x in Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3, S.cnt₁ (y.1 - y.2) x.2) +
        weight L y * ∫⁻ x in Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3, S.cnt₃ y.1 (x.1 + x.2)) := by
        refine lintegral_mono fun y => ?_
        by_cases hy : y ∈ triangle L
        · rw [← mul_add, ← mul_add]
          gcongr
          have e : y.2 + (y.1 - y.2) = y.1 := by ring
          have := S.volume_not_admissible_le hy.1 (sub_nonneg.2 hy.2.1)
          rwa [e] at this
        · rw [weight, indicator_of_notMem hy, zero_mul]
          exact zero_le
    _ = _ := by rw [lintegral_add_left h12, lintegral_add_left h1]
    _ ≤ 6 * S.boundFst L T * ENNReal.ofReal 9 + 6 * S.boundFst L T * ENNReal.ofReal 9 +
        ENNReal.ofReal (117 / 2) * S.boundSum L T := add_le_add (add_le_add hP hQ) hS
    _ = _ := by
        rw [show (108 : ℝ) = 6 * 9 + 6 * 9 by norm_num,
          ENNReal.ofReal_add (by norm_num) (by norm_num), ENNReal.ofReal_mul (by norm_num)]
        simp only [ENNReal.ofReal_ofNat]
        ring

/-- Corollary 7.4 at `(p, q) = (c₀ + P, c₀ + Q)`. -/
lemma ofReal_nine_div_four_le_volume {T P Q : ℝ}
    (hT : 36 * volume (S.E ∩ Icc 0 T) < ENNReal.ofReal (T - 2 * S.r₂ - 6 * S.c₀))
    (hPQ : 2 * S.c₀ + (P + Q) + 6 * S.r₁ ≤ T - 2 * S.r₂) :
    ENNReal.ofReal (9 / 4) ≤ volume {x : ℝ × ℝ | x ∈ Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3 ∧
      ¬ S.Admissible (S.c₀ + P) (S.c₀ + Q) x.1 x.2} :=
  S.volume_not_admissible hT (by linarith)

/-- **Proposition 3.3 when `E` is small**: the averaging argument of Section 8. -/
lemma ofReal_div_le_volume_E {T : ℝ}
    (hT : 36 * volume (S.E ∩ Icc 0 T) < ENNReal.ofReal (T - 2 * S.r₂ - 6 * S.c₀)) :
    ENNReal.ofReal ((T - (2 * S.r₂ + 6 * S.c₀)) / 74) ≤ volume (S.E ∩ Icc 0 T) := by
  have hc₀ : S.c₀ = 7 * S.r₂ := rfl
  have hr₁ := S.r₁_pos
  have hr₁₂ := S.r₁_lt_r₂
  set L := T - (2 * S.r₂ + 6 * S.c₀) with hLdef
  have hL : 0 < L := by
    have := ENNReal.ofReal_pos.1 (zero_le.trans_lt hT)
    linarith
  have hLT : 2 * S.c₀ + 8 * S.r₂ + L ≤ T := by linarith
  -- lower bound: Corollary 7.4 for every `(P, Q)` in the triangle
  have hlow : ENNReal.ofReal (9 / 4) ≤ ∫⁻ y, weight L y *
      volume {x : ℝ × ℝ | x ∈ Ico (0 : ℝ) 3 ×ˢ Ico (0 : ℝ) 3 ∧
        ¬ S.Admissible (S.c₀ + y.2) (S.c₀ + (y.1 - y.2)) x.1 x.2} := by
    calc ENNReal.ofReal (9 / 4) = ∫⁻ y, weight L y * ENNReal.ofReal (9 / 4) := by
          rw [lintegral_mul_const _ (measurable_weight L), lintegral_weight hL, one_mul]
      _ ≤ _ := lintegral_mono fun y => by
          by_cases hy : y ∈ triangle L
          · gcongr
            exact S.ofReal_nine_div_four_le_volume hT (by linarith [hy.2.2])
          · rw [weight, indicator_of_notMem hy, zero_mul, zero_mul]
  -- upper bound, and the identity `12 m̂ + (13 / 2) σ̂ = 37 / 2`
  have hcomb : ENNReal.ofReal 108 * S.boundFst L T + ENNReal.ofReal (117 / 2) * S.boundSum L T =
      ENNReal.ofReal (333 / 2 / L) * volume (S.E ∩ Icc 0 T) := by
    calc ENNReal.ofReal 108 * S.boundFst L T + ENNReal.ofReal (117 / 2) * S.boundSum L T
        = ∫⁻ t in S.E ∩ Icc 0 T,
            (ENNReal.ofReal 108 * ENNReal.ofReal (mHat ((t - (S.c₀ + 5 * S.r₂)) / L) / L) +
              ENNReal.ofReal (117 / 2) *
                ENNReal.ofReal (sHat ((t - (S.c₀ + 5 * S.r₂)) / L) / L)) := by
          rw [lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop),
            lintegral_const_mul _ (by fun_prop)]
          rfl
      _ = ∫⁻ _ in S.E ∩ Icc 0 T, ENNReal.ofReal (333 / 2 / L) :=
          setLIntegral_congr_fun (S.measurableSet_E.inter measurableSet_Icc) fun t _ => ?_
      _ = _ := setLIntegral_const _ _
    set ξ := (t - (S.c₀ + 5 * S.r₂)) / L
    rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (mul_nonneg (by norm_num) (div_nonneg (mHat_nonneg ξ) hL.le))
        (mul_nonneg (by norm_num) (div_nonneg (sHat_nonneg ξ) hL.le))]
    congr 1
    calc 108 * (mHat ξ / L) + 117 / 2 * (sHat ξ / L) =
          9 * (12 * mHat ξ + 13 / 2 * sHat ξ) / L := by ring
      _ = 333 / 2 / L := by rw [twelve_mul_mHat_add]; ring
  have key : ENNReal.ofReal (9 / 4) ≤
      ENNReal.ofReal (333 / 2 / L) * volume (S.E ∩ Icc 0 T) :=
    hlow.trans ((S.lintegral_weight_mul_volume_le hL hLT).trans hcomb.le)
  calc ENNReal.ofReal (L / 74) = ENNReal.ofReal (2 * L / 333) * ENNReal.ofReal (9 / 4) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (2 * L / 333) *
        (ENNReal.ofReal (333 / 2 / L) * volume (S.E ∩ Icc 0 T)) := by gcongr
    _ = volume (S.E ∩ Icc 0 T) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          show 2 * L / 333 * (333 / 2 / L) = 1 by field_simp, ENNReal.ofReal_one, one_mul]

/-- **Proposition 3.3.** There is a constant `K` (depending on `r₁, r₂`) such that
`λ(E ∩ [0, T]) ≥ (T - K) / 74` for all `T`. -/
theorem exists_volume_E_ge : ∃ K : ℝ, ∀ T : ℝ,
    ENNReal.ofReal ((T - K) / 74) ≤ volume (S.E ∩ Icc 0 T) := by
  refine ⟨2 * S.r₂ + 6 * S.c₀, fun T => ?_⟩
  by_cases hT : 36 * volume (S.E ∩ Icc 0 T) < ENNReal.ofReal (T - 2 * S.r₂ - 6 * S.c₀)
  · exact S.ofReal_div_le_volume_E hT
  push Not at hT
  rcases le_or_gt (T - (2 * S.r₂ + 6 * S.c₀)) 0 with h | h
  · rw [ENNReal.ofReal_of_nonpos (by linarith)]
    exact zero_le
  calc ENNReal.ofReal ((T - (2 * S.r₂ + 6 * S.c₀)) / 74)
      ≤ ENNReal.ofReal (1 / 36) * ENNReal.ofReal (T - 2 * S.r₂ - 6 * S.c₀) := by
        rw [← ENNReal.ofReal_mul (by norm_num)]
        exact ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ ENNReal.ofReal (1 / 36) * (36 * volume (S.E ∩ Icc 0 T)) := by gcongr
    _ = volume (S.E ∩ Icc 0 T) := by
        rw [← mul_assoc, ← ENNReal.ofReal_ofNat 36, ← ENNReal.ofReal_mul (by norm_num)]
        norm_num

end Erdos5.Setting
