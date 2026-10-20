import Mathlib
import Lagarias.Addenda_Enonces
import Lagarias.L4_Preuves

/-!
# Lagarias 1990 · addenda after the adversarial review · proofs
Statements: `Lagarias/Addenda_Enonces.lean` (frozen).
-/

namespace Lagarias

open LaboBP LaboHH

lemma C_eq_zero_iff (w : List Bool) : C w = 0 ↔ w.count true = 0 := by
  constructor
  · intro h
    have := C_ge w
    rw [h, zero_add] at this
    by_contra hc
    have : 2 ^ w.count true < 3 ^ w.count true := Nat.pow_lt_pow_left (by norm_num) hc
    omega
  · intro h
    rw [C_eq_S3_pos]
    have : pos w = [] := List.eq_nil_of_length_eq_zero (by rw [pos_length]; exact h)
    rw [this]; rfl

theorem thm4_1_printed_step_m1_thm : thm4_1_printed_step_m1 := by
  intro n M m hM hcop hm1 hmn h3m r
  unfold cntRes
  have hcard : ((words (n - m)) ×ˢ (Finset.Icc 1 m)).card = m * 2 ^ (n - m) := by
    rw [Finset.card_product, card_words, Nat.card_Icc, show m + 1 - 1 = m by omega, mul_comm]
  rw [← hcard]
  apply Finset.card_le_card_of_injOn (fun v => (v.drop m, max 1 ((v.take m).count true)))
  · intro v hv
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_words] at hv
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_words, Finset.mem_Icc,
      List.length_drop, hv.1]
    refine ⟨by simp, le_max_left _ _, max_le hm1 ?_⟩
    exact (List.count_le_length).trans (by simp)
  · intro v1 hv1 v2 hv2 h
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_words] at hv1 hv2
    simp only [Prod.mk.injEq] at h
    obtain ⟨hd, hc⟩ := h
    have hl1 : (v1.take m).length = m := by simp [hv1.1, hmn]
    have hl2 : (v2.take m).length = m := by simp [hv2.1, hmn]
    have e1 := eq4_5_thm (v1.take m) (v1.drop m)
    have e2 := eq4_5_thm (v2.take m) (v2.drop m)
    rw [List.take_append_drop, hl1] at e1
    rw [List.take_append_drop, hl2, ← hd] at e2
    have hmod : C (v1.take m) * 3 ^ (v1.drop m).count true ≡
        C (v2.take m) * 3 ^ (v1.drop m).count true [MOD M] := by
      have h12 : C v1 ≡ C v2 [MOD M] := by unfold Nat.ModEq; rw [hv1.2, hv2.2]
      rw [e1, e2] at h12
      exact Nat.ModEq.add_right_cancel' _ h12
    have hmod' := Nat.ModEq.cancel_right_of_coprime (Nat.Coprime.pow_right _ hcop) hmod
    have hlt : ∀ w : List Bool, w.length = m → C w < M := fun w hw => by
      have := C_le w; rw [hw] at this
      have : 0 < 2 ^ m := by positivity
      omega
    have hCeq := hmod'.eq_of_lt_of_lt (hlt _ hl1) (hlt _ hl2)
    have hc' : (v1.take m).count true = (v2.take m).count true := by
      by_cases h1 : (v1.take m).count true = 0
      · have : C (v2.take m) = 0 := by rw [← hCeq]; exact (C_eq_zero_iff _).mpr h1
        rw [h1, (C_eq_zero_iff _).mp this]
      · by_cases h2 : (v2.take m).count true = 0
        · have : C (v1.take m) = 0 := by rw [hCeq]; exact (C_eq_zero_iff _).mpr h2
          exact absurd ((C_eq_zero_iff _).mp this) h1
        · omega
    have hw := cor2_1a_words_thm _ _ (by rw [hl1, hl2]) hc' hCeq
    rw [← List.take_append_drop m v1, ← List.take_append_drop m v2, hw, hd]

theorem den_formal_thm : den_formal := by
  intro a q hq
  rcases lt_or_gt_of_ne (show q ≠ 0 by rintro rfl; simp at hq) with hneg | hpos
  · refine ⟨-Tk (-q) (-a), ?_⟩
    have e : (a : ℚ) / q = ((-a : ℤ) : ℚ) / ((-q : ℤ) : ℚ) := by push_cast; rw [neg_div_neg_eq]
    rw [e, collatzQ_div (-q) (-a) (by omega) (by simpa using hq.neg)]
    push_cast; rw [div_neg, neg_div]
  · exact ⟨Tk q a, collatzQ_div q a hpos hq⟩

theorem min_neg_printed_false_thm : min_neg_printed_false := by
  refine ⟨-10, by norm_num, ⟨odd_one, by decide, 3, by norm_num, by decide⟩, ?_, by decide⟩
  intro j
  have hP : Function.IsPeriodicPt (Tk 1) 3 (-10) := by decide
  rw [← hP.iterate_mod_apply j]
  have : j % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases (j % 3) <;> decide

end Lagarias
