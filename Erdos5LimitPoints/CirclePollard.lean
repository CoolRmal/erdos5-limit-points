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
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos5.Circle

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The convolution `(𝟙_A * 𝟙_B)(x) = λ(A ∩ (x - B))` of two subsets of the circle. -/
noncomputable def conv (A B : Set (AddCircle T)) (x : AddCircle T) : ℝ≥0∞ :=
  volume (A ∩ (fun y => x - y) ⁻¹' B)

/-- **Pollard's inequality on the circle.** -/
theorem circle_pollard {A B : Set (AddCircle T)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (t : ℝ≥0∞) :
    min (t * ENNReal.ofReal T) (min (t * (volume A + volume B - t)) (volume A * volume B)) ≤
      ∫⁻ x, min (conv A B x) t := by
  sorry

end Erdos5.Circle
