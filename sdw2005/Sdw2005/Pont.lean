import Mathlib
import Sdw2005.Pont_Enonces
import Sdw2005.Cycles
import Sdw2005.Borne91

/-!
# Sdw2005 · proofs of the frozen statements of step 3 (`Sdw2005/Pont_Enonces.lean`)

From terms to distinct values. Over any `N`, distinct odd values are at most odd terms (`card_image_le`). Over the
minimal period, `j ↦ C^[j] n` is injective on `[0, N)` (`Function.iterate_injOn_Iio_minimalPeriod`), so both counts
agree, for odd values and for local-minimum values. Then `cycle_K_lt_thm` and `cycle_K_lt_91_thm` conclude.
-/

namespace Sdw2005

/-- Distinct odd values are at most odd terms. -/
theorem oddValues_card_le (n N : ℕ) : (oddValues n N).card ≤ oddCount n N := by
  unfold oddValues orbitSet oddCount
  rw [Finset.filter_image]
  exact Finset.card_image_le

/-- `j ↦ C^[j] n` is injective on any subset of `[0, minimalPeriod C n)`. -/
theorem injOn_minimalPeriod (n : ℕ) (s : Finset ℕ) (hs : ∀ j ∈ s, j < Function.minimalPeriod C n) :
    Set.InjOn (fun j => C^[j] n) (s : Set ℕ) := by
  intro i hi j hj hij
  exact Function.iterate_injOn_Iio_minimalPeriod (Set.mem_Iio.2 (hs i hi)) (Set.mem_Iio.2 (hs j hj)) hij

/-- Over the minimal period, distinct odd values = odd terms. -/
theorem oddValues_card_eq (n : ℕ) :
    (oddValues n (Function.minimalPeriod C n)).card = oddCount n (Function.minimalPeriod C n) := by
  unfold oddValues orbitSet oddCount
  rw [Finset.filter_image]
  apply Finset.card_image_of_injOn
  apply injOn_minimalPeriod
  intro j hj
  exact Finset.mem_range.1 (Finset.mem_filter.1 hj).1

/-- Over the minimal period, distinct local-minimum values = local-minimum terms. -/
theorem minValues_card_eq (n : ℕ) :
    (minValues n (Function.minimalPeriod C n)).card = minCount n (Function.minimalPeriod C n) := by
  unfold minValues minCount
  apply Finset.card_image_of_injOn
  apply injOn_minimalPeriod
  intro j hj
  exact Finset.mem_range.1 (Finset.mem_filter.1 hj).1

theorem pont_image_thm : pont_image := by
  intro n N hn hN hc hm
  exact lt_of_le_of_lt (oddValues_card_le n N) (cycle_K_lt_thm n N hn hN hc hm)

theorem pont_image_91_thm : pont_image_91 := by
  intro n N hn hN hc hm
  exact lt_of_le_of_lt (oddValues_card_le n N) (cycle_K_lt_91_thm n N hn hN hc hm)

theorem pont_minimal_thm : pont_minimal := by
  intro n hn hp hm
  rw [oddValues_card_eq]
  rw [minValues_card_eq] at hm
  exact cycle_K_lt_thm n _ hn hp (Function.iterate_minimalPeriod (f := C) (x := n)) hm

theorem pont_minimal_91_thm : pont_minimal_91 := by
  intro n hn hp hm
  rw [oddValues_card_eq]
  rw [minValues_card_eq] at hm
  exact cycle_K_lt_91_thm n _ hn hp (Function.iterate_minimalPeriod (f := C) (x := n)) hm

end Sdw2005
