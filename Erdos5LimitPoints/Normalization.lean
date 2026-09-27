/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Erdos5LimitPoints.Defs

/-!
# The two normalisations of the prime gaps have the same limit points

Erdős Problem #5 normalises the prime gaps `pₙ₊₁ - pₙ` by `log n`, while Merikoski [Me20] (and
the note formalised here) normalise by `log pₙ`. Since `log pₙ / log n → 1`, the two sequences
have the same limit points. We prove `log pₙ / log n → 1` from Chebyshev's elementary lower
bound `ψ(x) ≥ x log 2 - log (x + 1)` (in Mathlib as `Chebyshev.psi_ge`), which gives
`(pₙ - 1) log 2 ≤ (n + 1) log pₙ`.

## Main results

* `Erdos5.Normalization.tendsto_log_nth_prime_div_log`: `log pₙ / log n → 1`.
* `Erdos5.Normalization.limitPointSet_eq_limitPointSetLogPrime`: the sets of limit points of
  `(pₙ₊₁ - pₙ) / log n` and of `(pₙ₊₁ - pₙ) / log pₙ` coincide.
-/

open Filter Real
open scoped Topology

namespace Erdos5.Normalization

/-- A form of Chebyshev's lower bound: `(pₙ - 1) log 2 ≤ (n + 1) log pₙ`. -/
lemma sub_one_mul_log_two_le (n : ℕ) :
    ((n.nth Nat.Prime : ℝ) - 1) * log 2 ≤ (n + 1) * log (n.nth Nat.Prime) := by
  set P := n.nth Nat.Prime with hPdef
  have hP : 2 ≤ P := (Nat.prime_nth_prime n).two_le
  have hπ : Nat.primeCounting (P - 1) = n := by
    rw [Nat.primeCounting_sub_one, hPdef, Nat.primeCounting'_nth_eq]
  have hN : ((P - 1 : ℕ) : ℝ) = P - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have h1 := Chebyshev.psi_ge (P - 1)
  have h2 := Chebyshev.psi_le_primeCounting_mul_log (P - 1)
  rw [hπ, hN] at h2
  rw [hN, sub_add_cancel] at h1
  have hP1 : (1 : ℝ) ≤ P - 1 := by
    have : (2 : ℝ) ≤ P := by exact_mod_cast hP
    linarith
  have hlog : log ((P : ℝ) - 1) ≤ log P := log_le_log (by linarith) (by linarith)
  have hlogP : 0 ≤ log (P : ℝ) := log_nonneg (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- `log y ≤ y / 2` for all `y > 0`. -/
lemma log_le_half {y : ℝ} (hy : 0 < y) : log y ≤ y / 2 := by
  have h := log_le_sub_one_of_pos (sqrt_pos.2 hy)
  rw [log_sqrt hy.le] at h
  nlinarith [sq_sqrt hy.le, sq_nonneg (sqrt y - 2)]

/-- `log pₙ ≤ log 3 + log (n + 1) + 2 √(2 (log 3 + log (n + 1)))` for `n ≥ 1`. -/
lemma log_nth_prime_le {n : ℕ} (hn : 1 ≤ n) :
    log (n.nth Nat.Prime) ≤
      log 3 + log (n + 1) + 2 * sqrt (2 * (log 3 + log (n + 1))) := by
  set P : ℝ := ((n.nth Nat.Prime : ℕ) : ℝ) with hPdef
  have hP : (2 : ℝ) ≤ P := by rw [hPdef]; exact_mod_cast (Nat.prime_nth_prime n).two_le
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl2 : 1 / 2 < log 2 := by
    have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
  have hlogP : log 2 ≤ log P := log_le_log (by norm_num) hP
  have hlogPpos : 0 < log P := (log_pos (by norm_num)).trans_le hlogP
  have hcheb := sub_one_mul_log_two_le n
  rw [← hPdef] at hcheb
  -- `P ≤ 3 (n + 1) log P`
  have hP3 : P ≤ 3 * (n + 1) * log P := by nlinarith
  have hkey : log P ≤ log 3 + log (n + 1) + log (log P) := by
    have h := log_le_log (by linarith) hP3
    rwa [log_mul (by positivity) hlogPpos.ne', log_mul (by norm_num) (by positivity)] at h
  -- bootstrap: `log (log P) ≤ log P / 2`, hence `log P ≤ 2 (log 3 + log (n + 1))`
  have hboot : log P ≤ 2 * (log 3 + log (n + 1)) := by
    have := log_le_half hlogPpos; linarith
  have hloglog : log (log P) ≤ 2 * sqrt (log P) := by
    have h := log_le_sub_one_of_pos (sqrt_pos.2 hlogPpos)
    rw [log_sqrt hlogPpos.le] at h
    nlinarith [sqrt_nonneg (log P)]
  have hsq : sqrt (log P) ≤ sqrt (2 * (log 3 + log (n + 1))) := sqrt_le_sqrt hboot
  linarith

/-- `log (n + 1) / log n → 1`. -/
lemma tendsto_log_add_one_div_log :
    Tendsto (fun n : ℕ => log ((n : ℝ) + 1) / log n) atTop (𝓝 1) := by
  have hlog : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h : Tendsto (fun n : ℕ => 1 + (log ((n : ℝ) + 1) - log n) / log n) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add (tendsto_log_nat_add_one_sub_log.div_atTop hlog)
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [hlog.eventually_gt_atTop 0] with n hn
  field_simp
  ring

/-- `(c + u + 2 √(2 (c + u))) / u → 1` as `u → ∞`. -/
lemma tendsto_add_sqrt_div (c : ℝ) :
    Tendsto (fun u : ℝ => (c + u + 2 * sqrt (2 * (c + u))) / u) atTop (𝓝 1) := by
  have h1 : Tendsto (fun u : ℝ => c / u) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  -- `0 ≤ √(2 (c + u)) / u ≤ 2 / √u` for large `u`
  have h2 : Tendsto (fun u : ℝ => sqrt (2 * (c + u)) / u) atTop (𝓝 0) := by
    have hlim : Tendsto (fun u : ℝ => 2 / sqrt u) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_sqrt_atTop
    refine squeeze_zero' ?_ ?_ hlim
    · filter_upwards [eventually_gt_atTop 0] with u hu
      positivity
    · filter_upwards [eventually_ge_atTop (max 1 |c|)] with u hu
      have hu1 : 1 ≤ u := le_of_max_le_left hu
      have huc : |c| ≤ u := le_of_max_le_right hu
      have hu0 : 0 < u := by linarith
      have hsu : 0 < sqrt u := sqrt_pos.2 hu0
      rw [div_le_div_iff₀ hu0 hsu]
      calc sqrt (2 * (c + u)) * sqrt u ≤ sqrt (4 * u) * sqrt u :=
            mul_le_mul_of_nonneg_right (sqrt_le_sqrt (by linarith [le_abs_self c]))
              (sqrt_nonneg u)
        _ = 2 * u := by
            rw [← sqrt_mul (by positivity), show 4 * u * u = (2 * u) ^ 2 by ring,
              sqrt_sq (by positivity)]
  have : Tendsto (fun u : ℝ => c / u + 1 + 2 * (sqrt (2 * (c + u)) / u)) atTop
      (𝓝 (0 + 1 + 2 * 0)) := (h1.add tendsto_const_nhds).add (h2.const_mul 2)
  rw [show (0 : ℝ) + 1 + 2 * 0 = 1 by ring] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with u hu
  field_simp

/-- `log pₙ / log n → 1`. -/
theorem tendsto_log_nth_prime_div_log :
    Tendsto (fun n : ℕ => log (n.nth Nat.Prime) / log n) atTop (𝓝 1) := by
  have hu : Tendsto (fun n : ℕ => log ((n : ℝ) + 1)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hup : Tendsto (fun n : ℕ => (log 3 + log ((n : ℝ) + 1) +
      2 * sqrt (2 * (log 3 + log ((n : ℝ) + 1)))) / log ((n : ℝ) + 1) *
      (log ((n : ℝ) + 1) / log n)) atTop (𝓝 (1 * 1)) :=
    ((tendsto_add_sqrt_div (log 3)).comp hu).mul tendsto_log_add_one_div_log
  rw [mul_one] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hlogn : 0 < log (n : ℝ) := log_pos (by linarith)
    rw [le_div_iff₀ hlogn, one_mul]
    have hp : n ≤ n.nth Nat.Prime := (Nat.add_two_le_nth_prime n).trans' (by omega)
    exact log_le_log (by linarith) (by exact_mod_cast hp)
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hlogn : 0 < log (n : ℝ) := log_pos (by linarith)
    have hlogn1 : 0 < log ((n : ℝ) + 1) := log_pos (by linarith)
    rw [div_mul_div_cancel₀ hlogn1.ne']
    exact div_le_div_of_nonneg_right (log_nth_prime_le (by omega)) hlogn.le

/-- If `g → 1`, then every cluster point of `f` is a cluster point of `f * g`. -/
lemma mapClusterPt_mul_of_tendsto_one {f g : ℕ → ℝ} {x : ℝ} (hf : MapClusterPt x atTop f)
    (hg : Tendsto g atTop (𝓝 1)) : MapClusterPt x atTop (fun n => f n * g n) := by
  obtain ⟨ψ, hψ, hfψ⟩ := hf.tendsto_subseq
  have : Tendsto ((fun n => f n * g n) ∘ ψ) atTop (𝓝 (x * 1)) :=
    hfψ.mul (hg.comp hψ.tendsto_atTop)
  rw [mul_one] at this
  exact this.mapClusterPt.of_comp hψ.tendsto_atTop

lemma mapClusterPt_congr {f g : ℕ → ℝ} {x : ℝ} (h : f =ᶠ[atTop] g) :
    MapClusterPt x atTop f ↔ MapClusterPt x atTop g := by
  rw [MapClusterPt, MapClusterPt, map_congr h]

/-- The sets of limit points of `(pₙ₊₁ - pₙ) / log n` and of `(pₙ₊₁ - pₙ) / log pₙ`
coincide. -/
theorem limitPointSet_eq_limitPointSetLogPrime : limitPointSet = limitPointSetLogPrime := by
  have hr := tendsto_log_nth_prime_div_log
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < log (n : ℝ) ∧ 0 < log (n.nth Nat.Prime : ℝ) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hp : (2 : ℝ) ≤ n.nth Nat.Prime := by exact_mod_cast (Nat.prime_nth_prime n).two_le
    exact ⟨log_pos (by linarith), log_pos (by linarith)⟩
  have e1 : normalizedGap =ᶠ[atTop] fun n =>
      normalizedGapLogPrime n * (log (n.nth Nat.Prime) / log n) := by
    filter_upwards [hpos] with n hn
    have := hn.1.ne'
    have := hn.2.ne'
    simp only [normalizedGap, normalizedGapLogPrime]
    field_simp
  have e2 : normalizedGapLogPrime =ᶠ[atTop] fun n =>
      normalizedGap n * (log (n.nth Nat.Prime) / log n)⁻¹ := by
    filter_upwards [hpos] with n hn
    have := hn.1.ne'
    have := hn.2.ne'
    simp only [normalizedGap, normalizedGapLogPrime]
    field_simp
  have hr' : Tendsto (fun n : ℕ => (log (n.nth Nat.Prime) / log n)⁻¹) atTop (𝓝 1) := by
    simpa using hr.inv₀ one_ne_zero
  ext x
  simp only [limitPointSet, limitPointSetLogPrime, Set.mem_ofPred_eq]
  constructor
  · intro h
    rw [mapClusterPt_congr e2]
    exact mapClusterPt_mul_of_tendsto_one h hr'
  · intro h
    rw [mapClusterPt_congr e1]
    exact mapClusterPt_mul_of_tendsto_one h hr

end Erdos5.Normalization
