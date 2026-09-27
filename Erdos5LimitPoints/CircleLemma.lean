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
Pollard's inequality give `∫ r G ≤ 3 φ(λ A)` with `φ(α) = α - α² / 4` (for `α ≤ 2`, and `1` for
`α ≥ 2`), and `φ(α) ≤ 3 / 4 + (α - 1) / 2` sums to `27 / 4`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos5.Circle

instance : Fact (0 < (3 : ℝ)) := ⟨by norm_num⟩

/-- **Circle lemma** (Lemma 6.3 of the paper). -/
theorem circle_lemma (K₁ K₂ K₃ : AddCircle (3 : ℝ) → ZMod 3)
    (h₁ : ∀ c, MeasurableSet (K₁ ⁻¹' {c})) (h₂ : ∀ c, MeasurableSet (K₂ ⁻¹' {c}))
    (h₃ : ∀ c, MeasurableSet (K₃ ⁻¹' {c}))
    (hK₂ : ∀ ω, K₂ (ω + ((1 : ℝ) : AddCircle (3 : ℝ))) = K₂ ω - 1) :
    volume {x : AddCircle (3 : ℝ) × AddCircle (3 : ℝ) | K₃ (x.1 + x.2) = K₁ x.1 + K₂ x.2} ≤
      ENNReal.ofReal (27 / 4) := by
  sorry

end Erdos5.Circle
