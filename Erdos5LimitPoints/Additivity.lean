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

/-- **Lemma 5.1** (`K₄` lemma), normalised by `s₀ = 0`. If every `s ∈ (ℤ/3ℤ)⁴` with `s₀ = 0`
satisfies `sⱼ - sᵢ = kᵢⱼ` for some `i < j`, then `k` is a coboundary. -/
theorem k4 (k₀₁ k₀₂ k₀₃ k₁₂ k₁₃ k₂₃ : ZMod 3)
    (h : ∀ s₁ s₂ s₃ : ZMod 3, s₁ = k₀₁ ∨ s₂ = k₀₂ ∨ s₃ = k₀₃ ∨ s₂ - s₁ = k₁₂ ∨
      s₃ - s₁ = k₁₃ ∨ s₃ - s₂ = k₂₃) :
    k₀₂ = k₀₁ + k₁₂ ∧ k₀₃ = k₀₁ + k₁₃ ∧ k₀₃ = k₀₂ + k₂₃ ∧ k₁₃ = k₁₂ + k₂₃ := by
  sorry

namespace Setting

variable (S : Setting)

/-- **Lemma 5.2.** -/
theorem kappa_triangle {y₀ y₁ y₂ y₃ : ℝ} (h₀₁ : y₀ + S.r₂ < y₁) (h₁₂ : y₁ + S.r₂ < y₂)
    (h₂₃ : y₂ + S.r₂ < y₃) (g₀₁ : S.Good (y₁ - y₀)) (g₀₂ : S.Good (y₂ - y₀))
    (g₀₃ : S.Good (y₃ - y₀)) (g₁₂ : S.Good (y₂ - y₁)) (g₁₃ : S.Good (y₃ - y₁))
    (g₂₃ : S.Good (y₃ - y₂)) :
    S.kappa (y₂ - y₀) = S.kappa (y₁ - y₀) + S.kappa (y₂ - y₁) ∧
    S.kappa (y₃ - y₀) = S.kappa (y₁ - y₀) + S.kappa (y₃ - y₁) ∧
    S.kappa (y₃ - y₀) = S.kappa (y₂ - y₀) + S.kappa (y₃ - y₂) ∧
    S.kappa (y₃ - y₁) = S.kappa (y₂ - y₁) + S.kappa (y₃ - y₂) := by
  sorry

/-- **Proposition 5.3** (additivity). Let `T' = T - 2 r₂` and suppose
`36 λ(E ∩ [0, T]) < T' - 6 c₀`. If `u, v ≥ c₀`, `u + v ≤ T'` and `u, v, u + v` are certified,
then `κ(u + v) = κ(u) + κ(v)`. -/
theorem kappa_add {T u v : ℝ}
    (hT : 36 * volume (S.E ∩ Icc 0 T) < ENNReal.ofReal (T - 2 * S.r₂ - 6 * S.c₀))
    (huv : u + v ≤ T - 2 * S.r₂) (hu : S.Certified u) (hv : S.Certified v)
    (huv' : S.Certified (u + v)) :
    S.kappa (u + v) = S.kappa u + S.kappa v := by
  sorry

end Setting

end Erdos5
