/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Erdos5LimitPoints

/-!
# Solution

Proofs of the statements of `Challenge.lean`. The definitions (`Erdos5.HasFourPointProperty`,
`Erdos5.primeGap`, `Erdos5.normalizedGap`, `Erdos5.limitPointSet`,
`Erdos5.normalizedGapLogPrime`, `Erdos5.limitPointSetLogPrime`) are those of
`Erdos5LimitPoints/Defs.lean`, which coincide verbatim with the ones in `Challenge.lean`.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Erdos5

theorem HasFourPointProperty.exists_volume_inter_Icc_ge {B : Set ℝ}
    (hB : HasFourPointProperty B) :
    ∃ C : ℝ, ∀ T : ℝ, ENNReal.ofReal (25 / 74 * T - C) ≤ volume (B ∩ Icc 0 T) :=
  Main.exists_volume_inter_Icc_ge hB

theorem HasFourPointProperty.le_liminf_volume_inter_Icc_div {B : Set ℝ}
    (hB : HasFourPointProperty B) :
    (25 / 74 : ℝ≥0∞) ≤ liminf (fun T : ℝ => volume (B ∩ Icc 0 T) / ENNReal.ofReal T) atTop :=
  Main.le_liminf_volume_inter_Icc_div hB

theorem exists_volume_limitPointSet_inter_Icc_ge_of_merikoski
    (merikoski : ∀ β : Fin 4 → ℝ, Monotone β → ∃ i j, i < j ∧ β j - β i ∈ limitPointSet) :
    ∃ C : ℝ, ∀ T : ℝ,
      ENNReal.ofReal (25 / 74 * T - C) ≤ volume (limitPointSet ∩ Icc 0 T) :=
  Main.exists_volume_inter_Icc_ge merikoski

theorem eventually_volume_limitPointSet_inter_Icc_ge_of_merikoski
    (merikoski : ∀ β : Fin 4 → ℝ, Monotone β → ∃ i j, i < j ∧ β j - β i ∈ limitPointSet) :
    ∀ᶠ T : ℝ in atTop, ENNReal.ofReal (76 / 225 * T) ≤ volume (limitPointSet ∩ Icc 0 T) :=
  Main.eventually_volume_inter_Icc_ge merikoski

theorem exists_volume_limitPointSetLogPrime_inter_Icc_ge_of_merikoski
    (merikoski : ∀ β : Fin 4 → ℝ, Monotone β →
      ∃ i j, i < j ∧ β j - β i ∈ limitPointSetLogPrime) :
    ∃ C : ℝ, ∀ T : ℝ,
      ENNReal.ofReal (25 / 74 * T - C) ≤ volume (limitPointSetLogPrime ∩ Icc 0 T) :=
  Main.exists_volume_inter_Icc_ge merikoski

theorem eventually_volume_limitPointSetLogPrime_inter_Icc_ge_of_merikoski
    (merikoski : ∀ β : Fin 4 → ℝ, Monotone β →
      ∃ i j, i < j ∧ β j - β i ∈ limitPointSetLogPrime) :
    ∀ᶠ T : ℝ in atTop,
      ENNReal.ofReal (76 / 225 * T) ≤ volume (limitPointSetLogPrime ∩ Icc 0 T) :=
  Main.eventually_volume_inter_Icc_ge merikoski

theorem limitPointSet_eq_limitPointSetLogPrime : limitPointSet = limitPointSetLogPrime :=
  Normalization.limitPointSet_eq_limitPointSetLogPrime

end Erdos5
