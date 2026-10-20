import Mathlib
import Lagarias.L3_Preuves

/-!
# Lagarias 1990 · Section 4 · proofs (phase 2a)

(4.4) (printed exponent repaired), (4.5), (4.8), and Theorem 4.1, with the integer core of its proof.
The core is proved with the count `m + 1` (one head per weight `0…m`), which also covers `m = 0`. The printed
count "at most `m` choices" is right for `m ≥ 1` (`thm4_1_printed_step_m1`, `Lagarias/Addenda.lean`) and fails
only for `m = 0`, i.e. `M ∈ {1, 2}` (`thm4_1_printed_step_false` for `M = 2`).
Statements: `Lagarias/L1990_Enonces.lean` (frozen).
-/

namespace Lagarias

open LaboBP LaboHH

/-! ## (4.4), (4.5), (4.8) -/

theorem eq4_4_printed_false_thm : eq4_4_printed_false := ⟨1, by decide⟩

theorem eq4_4_thm : eq4_4 := by
  intro n
  refine ⟨?_, fun v hv => ?_⟩
  · induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, show n + 1 - 1 - n = 0 by omega, pow_zero, mul_one]
      have : ∑ j ∈ Finset.range n, (2 : ℤ) ^ j * 3 ^ (n + 1 - 1 - j)
          = 3 * ∑ j ∈ Finset.range n, (2 : ℤ) ^ j * 3 ^ (n - 1 - j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_range] at hj
        rw [show n + 1 - 1 - j = (n - 1 - j) + 1 by omega, pow_succ]; ring
      rw [this, ih]; ring
  · have h := C_le v
    rw [hv] at h
    have : ((C v + 2 ^ n : ℕ) : ℤ) ≤ ((3 ^ n : ℕ) : ℤ) := by exact_mod_cast h
    push_cast at this
    linarith

theorem eq4_5_thm : eq4_5 := by
  intro w w'
  induction w with
  | nil => simp [C]
  | cons b w ih =>
    simp only [List.cons_append, C, ih, List.count_append, List.length_cons, pow_succ, pow_add]
    cases b <;> simp <;> ring

theorem eq4_8_thm : eq4_8 := by
  intro w u w'
  rw [eq4_5_thm, eq4_5_thm, List.length_append, pow_add, pow_add]
  ring

/-! ## `{0,1}ⁿ` -/

lemma mem_words (n : ℕ) (v : List Bool) : v ∈ words n ↔ v.length = n := by
  induction n generalizing v with
  | zero => simp [words, List.length_eq_zero_iff]
  | succ n ih =>
    simp only [words, Finset.mem_union, Finset.mem_image, ih]
    constructor
    · rintro (⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩) <;> simp [hw]
    · intro hv
      rcases v with _ | ⟨b, w⟩
      · simp at hv
      · cases b
        · right; exact ⟨w, by simpa using hv, rfl⟩
        · left; exact ⟨w, by simpa using hv, rfl⟩

lemma card_words (n : ℕ) : (words n).card = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [words]
    rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (List.cons_injective),
      Finset.card_image_of_injective _ (List.cons_injective), ih, pow_succ]
    · ring
    · rw [Finset.disjoint_left]
      intro v h1 h2
      simp only [Finset.mem_image] at h1 h2
      obtain ⟨_, _, rfl⟩ := h1
      obtain ⟨_, _, h⟩ := h2
      simp at h

/-! ## Theorem 4.1 -/

/-- The integer core of the proof of Theorem 4.1: for a fixed tail `w̄` and a fixed weight of the head `w`
(`m + 1` possible weights), at most one head is in a given class. -/
theorem thm4_1_core_thm : thm4_1_core := by
  intro n M m hM hcop hmn h3m r
  unfold cntRes
  have hcard : ((words (n - m)) ×ˢ (Finset.range (m + 1))).card = (m + 1) * 2 ^ (n - m) := by
    rw [Finset.card_product, card_words, Finset.card_range]; ring
  rw [← hcard]
  apply Finset.card_le_card_of_injOn (fun v => (v.drop m, (v.take m).count true))
  · intro v hv
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_words] at hv
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_words, Finset.mem_range,
      List.length_drop, hv.1]
    refine ⟨by simp, Nat.lt_succ_of_le ?_⟩
    exact (List.count_le_length).trans (by simp)
  · intro v1 hv1 v2 hv2 h
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_words] at hv1 hv2
    simp only [Prod.mk.injEq] at h
    obtain ⟨hd, hc⟩ := h
    have hl1 : (v1.take m).length = m := by simp [hv1.1, hmn]
    have hl2 : (v2.take m).length = m := by simp [hv2.1, hmn]
    -- (4.5)
    have e1 := eq4_5_thm (v1.take m) (v1.drop m)
    have e2 := eq4_5_thm (v2.take m) (v2.drop m)
    rw [List.take_append_drop, hl1] at e1
    rw [List.take_append_drop, hl2, ← hd] at e2
    have hmod : C (v1.take m) * 3 ^ (v1.drop m).count true ≡ C (v2.take m) * 3 ^ (v1.drop m).count true [MOD M] := by
      have h12 : C v1 ≡ C v2 [MOD M] := by
        unfold Nat.ModEq; rw [hv1.2, hv2.2]
      rw [e1, e2] at h12
      exact Nat.ModEq.add_right_cancel' _ h12
    have hcop3 : M.gcd (3 ^ (v1.drop m).count true) = 1 :=
      Nat.Coprime.pow_right _ hcop
    have hmod' := Nat.ModEq.cancel_right_of_coprime hcop3 hmod
    have hlt1 : C (v1.take m) < M := by
      have := C_le (v1.take m); rw [hl1] at this
      have : 0 < 2 ^ m := by positivity
      omega
    have hlt2 : C (v2.take m) < M := by
      have := C_le (v2.take m); rw [hl2] at this
      have : 0 < 2 ^ m := by positivity
      omega
    have hCeq := hmod'.eq_of_lt_of_lt hlt1 hlt2
    have hw := cor2_1a_words_thm _ _ (by rw [hl1, hl2]) hc hCeq
    rw [← List.take_append_drop m v1, ← List.take_append_drop m v2, hw, hd]

theorem thm4_1_printed_step_false_thm : thm4_1_printed_step_false :=
  ⟨1, 2, 0, 0, by decide, by decide, by decide, by decide, by decide +kernel⟩

theorem thm4_1_thm : thm4_1 := by
  intro n M hn hM hcop
  refine ⟨fun h r => ?_, fun h r => ?_⟩
  · have := thm4_1_core_thm n M n hM hcop le_rfl h.le r
    simpa using this
  · -- `m = ⌊log₃ M⌋`
    set m := Nat.log 3 M with hm
    have h3m : 3 ^ m ≤ M := Nat.pow_log_le_self 3 hM.ne'
    have hM3 : M < 3 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) M
    have hMlt : M < 3 ^ n := by
      rcases h.lt_or_eq with h' | h'
      · exact h'
      · exfalso
        have : 3 ∣ M := by rw [h']; exact dvd_pow_self 3 hn.ne'
        exact absurd (Nat.Coprime.coprime_dvd_left this hcop : Nat.Coprime 3 3) (by decide)
    have hmn : m + 1 ≤ n := by
      by_contra hc
      have : 3 ^ n ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hcore := thm4_1_core_thm n M m hM hcop (by omega) h3m r
    -- real estimates
    set φ := Real.logb 3 2 with hφ
    have hφpos : 0 < φ := Real.logb_pos (by norm_num) (by norm_num)
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
    have hMφ : (0 : ℝ) < (M : ℝ) ^ φ := Real.rpow_pos_of_pos hMpos φ
    have h3pow : ((3 : ℝ) ^ (m + 1)) ^ φ = 2 ^ (m + 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
        Real.rpow_logb (by norm_num) (by norm_num) (by norm_num), Real.rpow_natCast]
    have hMlt' : (M : ℝ) ^ φ < 2 ^ (m + 1) := by
      rw [← h3pow]
      exact Real.rpow_lt_rpow hMpos.le (by exact_mod_cast hM3) hφpos
    rw [le_div_iff₀ hMφ]
    have hc : (cntRes n M r : ℝ) ≤ (m + 1) * 2 ^ (n - m) := by exact_mod_cast hcore
    have h2 : (2 : ℝ) ^ (n - m) * 2 ^ (m + 1) = 2 * 2 ^ n := by
      rw [← pow_add, show n - m + (m + 1) = n + 1 by omega, pow_succ]; ring
    have hmn' : ((m : ℝ) + 1) ≤ n := by exact_mod_cast hmn
    have hpos : (0 : ℝ) ≤ (m + 1) * 2 ^ (n - m) := by positivity
    calc (cntRes n M r : ℝ) * (M : ℝ) ^ φ ≤ ((m + 1) * 2 ^ (n - m)) * (M : ℝ) ^ φ :=
          mul_le_mul_of_nonneg_right hc hMφ.le
      _ ≤ ((m + 1) * 2 ^ (n - m)) * 2 ^ (m + 1) := mul_le_mul_of_nonneg_left hMlt'.le hpos
      _ = (m + 1) * (2 * 2 ^ n) := by rw [mul_assoc, h2]
      _ ≤ n * (2 * 2 ^ n) := by gcongr
      _ = 2 * n * 2 ^ n := by ring

end Lagarias
