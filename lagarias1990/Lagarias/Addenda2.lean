import Mathlib
import Lagarias.Addenda2_Enonces
import Lagarias.L2b_Preuves

/-!
# Lagarias 1990 · addendum 2 · proof of (2.6)

By (2.4), `n·I(n) = 2ⁿ − Σ_{d∣n, d<n} d·I(d)`. Each `d·I(d)` counts irreducible words of length `d`, so it is at most
`2^d`, and a proper divisor `d` of `n` is at most `n/2`; hence `0 ≤ 2ⁿ − n·I(n) < 2^{⌊n/2⌋+1}` (`eq2_6_explicit`),
and (2.6) holds with the constant `c = 2`.
Statement: `Lagarias/Addenda2_Enonces.lean` (frozen).
-/

namespace Lagarias

open LaboBP LaboHH

lemma card_Irr_le (d : ℕ) : (Irr d).card ≤ 2 ^ d :=
  (Finset.card_filter_le _ _).trans (card_words d).le

lemma le_half_of_mem_properDivisors {n d : ℕ} (hd : d ∈ n.properDivisors) : d ≤ n / 2 := by
  obtain ⟨⟨k, rfl⟩, hlt⟩ := Nat.mem_properDivisors.mp hd
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  have hk : 2 ≤ k := by
    rcases k with _ | _ | k
    · simp at hlt
    · simp at hlt
    · omega
  calc d * 2 ≤ d * k := Nat.mul_le_mul_left _ hk

lemma sum_range_two_pow_lt (k : ℕ) : ∑ i ∈ Finset.range k, 2 ^ i < 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, pow_succ]; omega

/-- (2.6) with explicit error: `n·I(n) ≤ 2ⁿ < n·I(n) + 2^{⌊n/2⌋+1}`. -/
lemma eq2_6_explicit {n : ℕ} (hn : 0 < n) : n * Iirr n ≤ 2 ^ n ∧ 2 ^ n < n * Iirr n + 2 ^ (n / 2 + 1) := by
  have h := eq2_4_thm n hn
  rw [← Nat.cons_self_properDivisors hn.ne', Finset.sum_cons] at h
  have hrest : ∑ d ∈ n.properDivisors, d * Iirr d < 2 ^ (n / 2 + 1) := by
    calc ∑ d ∈ n.properDivisors, d * Iirr d
        ≤ ∑ d ∈ n.properDivisors, 2 ^ d := Finset.sum_le_sum fun d hd => by
          rw [mul_Iirr (Nat.pos_of_mem_properDivisors hd)]; exact card_Irr_le d
      _ ≤ ∑ d ∈ Finset.range (n / 2 + 1), 2 ^ d := by
          apply Finset.sum_le_sum_of_subset
          intro d hd
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le (le_half_of_mem_properDivisors hd))
      _ < 2 ^ (n / 2 + 1) := sum_range_two_pow_lt _
  omega

theorem eq2_6_thm : eq2_6 := by
  refine ⟨2, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := eq2_6_explicit hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  -- `E = 2ⁿ − n·I(n)`, `0 ≤ E < 2^{⌊n/2⌋+1}`
  have hE0 : (0 : ℝ) ≤ 2 ^ n - n * Iirr n := by
    have : ((n * Iirr n : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at this; linarith
  have hE1 : (2 : ℝ) ^ n - n * Iirr n ≤ 2 * 2 ^ ((n : ℝ) / 2) := by
    have : ((2 ^ n : ℕ) : ℝ) ≤ ((n * Iirr n + 2 ^ (n / 2 + 1) : ℕ) : ℝ) := by exact_mod_cast h2.le
    push_cast at this
    have hhalf : (2 : ℝ) ^ (n / 2) ≤ 2 ^ ((n : ℝ) / 2) := by
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have : ((n / 2 : ℕ) : ℝ) * 2 = ((n / 2 * 2 : ℕ) : ℝ) := by push_cast; ring
      rw [this]; exact_mod_cast Nat.div_mul_le_self n 2
    rw [pow_succ] at this
    linarith
  have e : (Iirr n : ℝ) - 2 ^ n / n = -((2 ^ n - n * Iirr n) / n) := by field_simp; ring
  rw [e, abs_neg, abs_of_nonneg (div_nonneg hE0 hn0.le), div_le_iff₀ hn0]
  have hp : (0 : ℝ) ≤ 2 * 2 ^ ((n : ℝ) / 2) := by positivity
  nlinarith

end Lagarias
