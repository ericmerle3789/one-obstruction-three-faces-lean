import Mathlib
import Lagarias.L1990b_Enonces
import Lagarias.L4b_Preuves

/-!
# Lagarias 1990 · Theorem 4.2 with the printed constant `2n⁴`

The printed proof (p. 50) bounds the normal vectors by `n(n−1)·4n²·2^{(1−α)n}`: it uses `(n−m)·m ≤ n(n−1)` for
the number of window positions times the count per position, and gets `4n⁴`. The statement (4.7) prints `2n⁴`.
Keeping everything else (same window length `m`, `2n²·2^m ≤ M < 4n²·2^m`), the arithmetic–geometric mean bound
`(n−m+1)(m+1) ≤ (n+2)²/4` gives `n²(n+2)²·2ⁿ` for the normal vectors; with `≤ n·2ⁿ` for the exceptional ones,
`n²(n+2)² + n ≤ 2n⁴` as soon as `n ≥ 5`, and `n ≤ 4` is the trivial case `M ≤ 2n⁴`. So the printed constant is right;
only the printed proof is loose.
Statement: `Lagarias/L1990b_Enonces.lean` (frozen).
-/

namespace Lagarias

open LaboBP LaboHH

theorem thm4_2_printed_thm : thm4_2_printed := by
  intro n M hn hM hcop hMα r
  obtain ⟨hφ1, hφ2⟩ := phiL_bounds
  obtain ⟨hH0, hH1⟩ := Hb_bounds phiL (by linarith) hφ2
  set H := Hb phiL with hH
  have h2H : 0 < 2 - H := by linarith
  have hαc : (2 - H) * alphaC = 1 - H := by unfold alphaC; rw [← hH]; field_simp
  have hαc1 : alphaC ≤ 1 := by
    have : (2 - H) * alphaC ≤ (2 - H) * 1 := by rw [hαc]; linarith
    exact le_of_mul_le_mul_left this h2H
  have hcnt : cntRes n M r ≤ 2 ^ n := (Finset.card_filter_le _ _).trans (card_words n).le
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  by_cases hA : (M : ℝ) ≤ 2 * n ^ 4
  · have : (cntRes n M r : ℝ) ≤ 2 ^ n := by exact_mod_cast hcnt
    calc (cntRes n M r : ℝ) * M ≤ 2 ^ n * (2 * n ^ 4) :=
          mul_le_mul this hA (by positivity) (by positivity)
      _ = 2 * n ^ 4 * 2 ^ n := by ring
  push Not at hA
  -- `M ≤ 2ⁿ`, hence `n ≥ 5`
  have hMn : (M : ℝ) ≤ 2 ^ n := by
    calc (M : ℝ) ≤ 2 ^ (alphaC * n) := hMα
      _ ≤ 2 ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
      _ = 2 ^ n := Real.rpow_natCast 2 n
  have hn5 : 5 ≤ n := by
    by_contra h
    push Not at h
    have : (2 : ℝ) ^ n ≤ 2 * n ^ 4 := by
      interval_cases n <;> norm_num
    linarith
  -- the window length `m`: `2n²·2^m ≤ M < 4n²·2^m`
  have hnn : 0 < 2 * n ^ 2 := by positivity
  set q := M / (2 * n ^ 2) with hq
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hn24 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 := by nlinarith
  have hMq : 2 * n ^ 2 ≤ M := by
    have : ((2 * n ^ 2 : ℕ) : ℝ) ≤ M := by push_cast; nlinarith
    exact_mod_cast this
  have hq0 : q ≠ 0 := by rw [hq]; exact (Nat.div_pos hMq hnn).ne'
  set m := Nat.log 2 q with hm
  have hm1 : 2 ^ m ≤ q := Nat.pow_log_le_self 2 hq0
  have hm2 : q < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) q
  have hMlow : 2 * n ^ 2 * 2 ^ m ≤ M := (Nat.mul_le_mul_left _ hm1).trans (Nat.mul_div_le M _)
  have hMup : M < 4 * n ^ 2 * 2 ^ m := by
    have h1 : M < 2 * n ^ 2 * (q + 1) := Nat.lt_mul_div_succ M hnn
    have h2 : q + 1 ≤ 2 ^ (m + 1) := hm2
    calc M < 2 * n ^ 2 * (q + 1) := h1
      _ ≤ 2 * n ^ 2 * 2 ^ (m + 1) := Nat.mul_le_mul_left _ h2
      _ = 4 * n ^ 2 * 2 ^ m := by ring
  have hmn : m < n := by
    have h1 : 2 ^ m < 2 ^ n := by
      have : (M : ℝ) ≤ 2 ^ n := hMn
      have h2 : ((2 * n ^ 2 * 2 ^ m : ℕ) : ℝ) ≤ M := by exact_mod_cast hMlow
      push_cast at h2
      have hp : (0 : ℝ) < 2 ^ m := by positivity
      have h3 : (2 : ℝ) * 2 ^ m ≤ 2 * n ^ 2 * 2 ^ m := by nlinarith
      have : (2 : ℝ) ^ m < 2 ^ n := by linarith
      exact_mod_cast this
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp h1
  have hmα : (m : ℝ) ≤ alphaC * n := by
    have h1 : (2 : ℝ) ^ (m : ℝ) ≤ 2 ^ (alphaC * n) := by
      rw [Real.rpow_natCast]
      have : ((2 ^ m : ℕ) : ℝ) ≤ M := by exact_mod_cast (hm1.trans (Nat.div_le_self _ _))
      push_cast at this
      linarith
    exact (Real.rpow_le_rpow_left_iff (by norm_num)).mp h1
  -- covering of the class
  set S := (words n).filter (fun v => C v % M = r % M) with hS
  set Nor := fun l => (words n).filter (fun v => C v % M = r % M ∧ C ((v.drop l).take m) < M)
  set Exc := fun j => (words n).filter
    (fun v => phiL * ((n - j - 1 : ℕ) : ℝ) ≤ ((v.drop (j + 1)).count true : ℝ))
  have hcover : S ⊆ (Finset.range (n - m + 1)).biUnion Nor ∪ (Finset.range m).biUnion Exc := by
    intro v hv
    rw [hS, Finset.mem_filter, mem_words] at hv
    by_cases h : ∃ l, l + m ≤ n ∧ C ((v.drop l).take m) < M
    · obtain ⟨l, hl, hlt⟩ := h
      apply Finset.mem_union_left
      rw [Finset.mem_biUnion]
      exact ⟨l, Finset.mem_range.mpr (by omega), Finset.mem_filter.mpr ⟨(mem_words _ _).mpr hv.1, hv.2, hlt⟩⟩
    · push Not at h
      obtain ⟨j, hj, -, hjt⟩ := exceptional n m M v hv.1 hn hmn.le hMlow h
      apply Finset.mem_union_right
      rw [Finset.mem_biUnion]
      exact ⟨j, Finset.mem_range.mpr hj,
        Finset.mem_filter.mpr ⟨(mem_words _ _).mpr hv.1, count_of_term n j _ (by omega) hjt⟩⟩
  have hcard : cntRes n M r ≤ (n - m + 1) * ((m + 1) * 2 ^ (n - m)) +
      ∑ j ∈ Finset.range m, 2 ^ (j + 1) *
        ((words (n - j - 1)).filter (fun u => phiL * ((n - j - 1 : ℕ) : ℝ) ≤ (u.count true : ℝ))).card := by
    calc cntRes n M r = S.card := rfl
      _ ≤ ((Finset.range (n - m + 1)).biUnion Nor ∪ (Finset.range m).biUnion Exc).card :=
          Finset.card_le_card hcover
      _ ≤ ((Finset.range (n - m + 1)).biUnion Nor).card + ((Finset.range m).biUnion Exc).card :=
          Finset.card_union_le _ _
      _ ≤ ∑ l ∈ Finset.range (n - m + 1), (Nor l).card + ∑ j ∈ Finset.range m, (Exc j).card :=
          add_le_add Finset.card_biUnion_le Finset.card_biUnion_le
      _ ≤ _ := by
          apply add_le_add
          · calc ∑ l ∈ Finset.range (n - m + 1), (Nor l).card
                ≤ ∑ l ∈ Finset.range (n - m + 1), (m + 1) * 2 ^ (n - m) :=
                  Finset.sum_le_sum fun l hl => normal_count n M m l r hM hcop
                    (by rw [Finset.mem_range] at hl; omega)
              _ = (n - m + 1) * ((m + 1) * 2 ^ (n - m)) := by
                  rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
          · exact Finset.sum_le_sum fun j hj => exc_card n j (by rw [Finset.mem_range] at hj; omega) phiL
  -- real estimates
  have hcardR : (cntRes n M r : ℝ) ≤ ((n - m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) * 2 ^ (n - m)) +
      ∑ j ∈ Finset.range m, (2 : ℝ) ^ (j + 1) * 2 ^ (H * ((n - j - 1 : ℕ) : ℝ)) := by
    have h := (Nat.cast_le (α := ℝ)).mpr hcard
    push_cast at h
    refine h.trans (add_le_add (le_of_eq (by push_cast; ring)) (Finset.sum_le_sum fun j _ => ?_))
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact words_tail (n - j - 1) phiL hφ1 hφ2
  have hMR : (M : ℝ) < 4 * n ^ 2 * 2 ^ m := by exact_mod_cast hMup
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  -- normal part
  -- the only change: `(n−m+1)(m+1) ≤ (n+2)²/4` (arithmetic–geometric mean) instead of `≤ n(n−1)`
  have hnorm : ((n - m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) * 2 ^ (n - m)) * M ≤
      n ^ 2 * (n + 2) ^ 2 * 2 ^ n := by
    have hprod : ((n - m + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) ≤ (n + 2) ^ 2 / 4 := by
      have e1 : ((n - m + 1 : ℕ) : ℝ) = n - m + 1 := by push_cast [Nat.cast_sub hmn.le]; ring
      rw [e1]; push_cast
      nlinarith [sq_nonneg ((n : ℝ) - 2 * m)]
    have h2 : (2 : ℝ) ^ (n - m) * 2 ^ m = 2 ^ n := by rw [← pow_add, Nat.sub_add_cancel hmn.le]
    calc ((n - m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) * 2 ^ (n - m)) * M
        = (((n - m + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ)) * 2 ^ (n - m) * M := by ring
      _ ≤ ((n + 2) ^ 2 / 4) * 2 ^ (n - m) * (4 * n ^ 2 * 2 ^ m) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hprod (by positivity)) hMR.le hMpos.le
          positivity
      _ = n ^ 2 * (n + 2) ^ 2 * (2 ^ (n - m) * 2 ^ m) := by ring
      _ = n ^ 2 * (n + 2) ^ 2 * 2 ^ n := by rw [h2]
  -- exceptional part
  have hexc : (∑ j ∈ Finset.range m, (2 : ℝ) ^ (j + 1) * 2 ^ (H * ((n - j - 1 : ℕ) : ℝ))) * M ≤
      n * 2 ^ n := by
    rw [Finset.sum_mul]
    calc ∑ j ∈ Finset.range m, (2 : ℝ) ^ (j + 1) * 2 ^ (H * ((n - j - 1 : ℕ) : ℝ)) * M
        ≤ ∑ j ∈ Finset.range m, (2 : ℝ) ^ n := Finset.sum_le_sum fun j hj => by
          rw [Finset.mem_range] at hj
          have e1 : ((n - j - 1 : ℕ) : ℝ) = n - j - 1 := by
            rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
          have hexp : ((j + 1 : ℕ) : ℝ) + H * ((n - j - 1 : ℕ) : ℝ) + alphaC * n ≤ n := by
            rw [e1]; push_cast
            have hjm : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj
            nlinarith
          calc (2 : ℝ) ^ (j + 1) * 2 ^ (H * ((n - j - 1 : ℕ) : ℝ)) * M
              ≤ (2 : ℝ) ^ ((j + 1 : ℕ) : ℝ) * 2 ^ (H * ((n - j - 1 : ℕ) : ℝ)) * 2 ^ (alphaC * n) := by
                rw [Real.rpow_natCast]
                exact mul_le_mul_of_nonneg_left hMα (by positivity)
            _ = (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) + H * ((n - j - 1 : ℕ) : ℝ) + alphaC * n) := by
                rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num)]
            _ ≤ (2 : ℝ) ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
            _ = 2 ^ n := Real.rpow_natCast 2 n
      _ = m * 2 ^ n := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ n * 2 ^ n := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hmn.le
  -- total
  calc (cntRes n M r : ℝ) * M
      ≤ (((n - m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) * 2 ^ (n - m)) +
          ∑ j ∈ Finset.range m, (2 : ℝ) ^ (j + 1) * 2 ^ (H * ((n - j - 1 : ℕ) : ℝ))) * M :=
        mul_le_mul_of_nonneg_right hcardR hMpos.le
    _ = ((n - m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) * 2 ^ (n - m)) * M +
          (∑ j ∈ Finset.range m, (2 : ℝ) ^ (j + 1) * 2 ^ (H * ((n - j - 1 : ℕ) : ℝ))) * M := by ring
    _ ≤ n ^ 2 * (n + 2) ^ 2 * 2 ^ n + n * 2 ^ n := add_le_add hnorm hexc
    _ ≤ 2 * n ^ 4 * 2 ^ n := by
        have hp : (0 : ℝ) < 2 ^ n := by positivity
        have hn5R : (5 : ℝ) ≤ n := by exact_mod_cast hn5
        -- `2n⁴ − n²(n+2)² − n = n((n−4)n² − 4n − 1) ≥ 0` for `n ≥ 5`
        have h3 : (0 : ℝ) ≤ 2 * n ^ 4 - n ^ 2 * (n + 2) ^ 2 - n := by
          have h4 : (0 : ℝ) ≤ (n - 4) * n ^ 2 - 4 * n - 1 := by nlinarith
          have e : (2 : ℝ) * n ^ 4 - n ^ 2 * (n + 2) ^ 2 - n = n * ((n - 4) * n ^ 2 - 4 * n - 1) := by ring
          rw [e]; positivity
        have h := mul_nonneg h3 hp.le
        have e : (2 : ℝ) * n ^ 4 * 2 ^ n - (n ^ 2 * (n + 2) ^ 2 * 2 ^ n + n * 2 ^ n) =
            (2 * n ^ 4 - n ^ 2 * (n + 2) ^ 2 - n) * 2 ^ n := by ring
        linarith

end Lagarias
