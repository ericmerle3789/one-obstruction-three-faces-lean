import Mathlib
import Brox2000.Brox_Enonces
import Brox2000.Combinatoire
import Brox2000.Analyse

/-!
# Brox 2000 · proofs of the frozen statements of phase A (`Brox2000/Brox_Enonces.lean`)

Over the minimal period `p` of `n`: `|Γ| = oddCount n p` and `δ(Γ) = descCount n p = minCount n p`
(`Brox2000/Combinatoire.lean`). `Sdw2005.cycle_chain_thm` turns the cycle into a solution of the chain equation with
`m = minCount n p` blocks and `K = oddCount n p`; `chain_K_lt_brox` (`Brox2000/Analyse.lean`) gives `K < 2^1500` when
`m < 2 log K`. Finiteness: `p ≤ 2K` and `n ≤ p 3^K 2^p`.
-/

namespace Brox2000

open Sdw2005

theorem lemma22_pos_thm : lemma22_pos := by
  intro n hn hp
  rw [Gamma_card]
  exact period_le_two_odd hn Function.iterate_minimalPeriod

theorem lemma22_finite_pos_thm : lemma22_finite_pos := by
  intro K
  apply (Set.finite_Iic (2 * K * 3 ^ K * 2 ^ (2 * K))).subset
  rintro n ⟨hn, hp, hK⟩
  rw [Set.mem_Iic]
  have hc : C^[Function.minimalPeriod C n] n = n := Function.iterate_minimalPeriod
  have h1 := elem_le hn hp hc
  have h2 : Function.minimalPeriod C n ≤ 2 * K := (lemma22_pos_thm n hn hp).trans (by omega)
  rw [Gamma_card] at hK
  calc n ≤ Function.minimalPeriod C n * 3 ^ oddCount n (Function.minimalPeriod C n) *
        2 ^ Function.minimalPeriod C n := h1
    _ ≤ 2 * K * 3 ^ K * 2 ^ (2 * K) := by
      apply Nat.mul_le_mul (Nat.mul_le_mul h2 (Nat.pow_le_pow_right (by norm_num) hK))
        (Nat.pow_le_pow_right (by norm_num) h2)

theorem thm11_pos_explicit_thm : thm11_pos_explicit := by
  intro n hn hp hδ
  have hc : C^[Function.minimalPeriod C n] n = n := Function.iterate_minimalPeriod
  rw [descSet_card, descCount_eq_minCount hp hc, Gamma_card] at hδ
  rw [Gamma_card]
  obtain ⟨k, l, a, hs, hK⟩ := cycle_chain_thm n _ hn hp hc
  rw [← hK] at hδ ⊢
  exact chain_K_lt_brox _ k l a hs hδ

theorem thm11_pos_thm : thm11_pos := by
  apply (lemma22_finite_pos_thm (2 ^ 1500)).subset
  rintro n ⟨hn, hp, hδ⟩
  exact ⟨hn, hp, (thm11_pos_explicit_thm n hn hp hδ).le⟩

theorem cor12_pos_thm : cor12_pos := by
  intro ν
  apply (lemma22_finite_pos_thm (2 ^ 1500 + 3 ^ ν)).subset
  rintro n ⟨hn, hp, hδ⟩
  refine ⟨hn, hp, ?_⟩
  by_cases h : (ν : ℝ) < 2 * Real.log ((Gamma n).card : ℝ)
  · have hδ' : ((descSet n).card : ℝ) < 2 * Real.log ((Gamma n).card : ℝ) :=
      lt_of_le_of_lt (by exact_mod_cast hδ) h
    exact le_add_right (thm11_pos_explicit_thm n hn hp hδ').le
  · rw [not_lt] at h
    -- `|Γ| ≤ e^{ν/2} ≤ 3^ν`
    have hle : (Gamma n).card ≤ 3 ^ ν := by
      rcases Nat.eq_zero_or_pos (Gamma n).card with h0 | h0
      · rw [h0]; exact Nat.zero_le _
      have hr : (0 : ℝ) < (Gamma n).card := by exact_mod_cast h0
      have h1 : ((Gamma n).card : ℝ) ≤ Real.exp ν := by
        calc ((Gamma n).card : ℝ) = Real.exp (Real.log (Gamma n).card) := (Real.exp_log hr).symm
          _ ≤ Real.exp ν := Real.exp_le_exp.mpr (by
              have : 0 ≤ Real.log ((Gamma n).card : ℝ) :=
                Real.log_nonneg (by exact_mod_cast h0)
              linarith)
      have h2 : Real.exp ν ≤ (3 : ℝ) ^ ν := by
        rw [show (ν : ℝ) = (ν : ℕ) * 1 by ring, Real.exp_nat_mul]
        exact pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith [Real.exp_one_lt_d9]) ν
      exact_mod_cast h1.trans h2
    exact le_add_left hle

end Brox2000
