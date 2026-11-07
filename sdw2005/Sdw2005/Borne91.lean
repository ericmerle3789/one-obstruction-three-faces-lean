import Mathlib
import Sdw2005.Sdw91_Enonces
import Sdw2005.Bornes
import Sdw2005.Cycles

/-!
# Sdw2005 · `chain_K_lt_91`, `cycle_K_lt_91`: for `m ≤ 91`, `K < 2·10^21`, without hypothesis

As in `Sdw2005/Bornes.lean`, with `E = (δ − 1) K / (δ^m − 1) ≥ K / (3·10^18)` for `m ≤ 91` and
`Λ < 182 · 2^{−E}`. No pair of convergents other than the bridge of `../logs23/` is needed (unlike `chain_K_lt`,
which also uses `p₃₈/q₃₈` and `p₃₉/q₃₉`): if `2·10^21 ≤ K < qBr'`, the bridge gives `Λ ≥ 10^(−101) > 182 · 2^(−600)`;
if `K ≥ qBr' ≥ 2^334`, `Logs23.two_log_lower_thm` gives `Λ ≥ exp(−10^12 ν^5)` with `2^(ν−1) ≤ K`.
-/

namespace Sdw2005

/-- For `1 ≤ m ≤ 91`: `K / (3·10^18) ≤ (δ − 1) K / (δ^m − 1)`. -/
theorem K_div_le_E_91 {m : ℕ} (hm : 0 < m) (hm91 : m ≤ 91) (K : ℝ) (hK : 0 ≤ K) :
    K / (3 * 10 ^ 18) ≤ (δ - 1) * K / (δ ^ m - 1) := by
  have hδ := one_lt_delta
  have hB : 0 < δ ^ m - 1 := by linarith [one_lt_pow₀ hδ hm.ne']
  have hpow : δ ^ m ≤ (317 / 200 : ℝ) ^ 91 :=
    calc δ ^ m ≤ δ ^ 91 := pow_le_pow_right₀ hδ.le hm91
      _ ≤ (317 / 200 : ℝ) ^ 91 := pow_le_pow_left₀ (by linarith) delta_le 91
  have hc : (317 / 200 : ℝ) ^ 91 - 1 ≤ 58 / 100 * (3 * 10 ^ 18) := by norm_num
  have hA := delta_sub_one_ge
  rw [div_le_div_iff₀ (by norm_num) hB]
  have h1 : K * (δ ^ m - 1) ≤ K * (58 / 100 * (3 * 10 ^ 18)) := mul_le_mul_of_nonneg_left (by linarith) hK
  have h2 : K * (3 * 10 ^ 18) * (58 / 100) ≤ K * (3 * 10 ^ 18) * (δ - 1) :=
    mul_le_mul_of_nonneg_left hA (by positivity)
  linarith

theorem pow5_le_two_pow_40 {n : ℕ} (hn : 335 ≤ n) : 10 ^ 40 * n ^ 5 ≤ 2 ^ (n - 3) := by
  induction n, hn using Nat.le_induction with
  | base => decide +kernel
  | succ n hn ih =>
    have h1 : (n + 1) ^ 5 ≤ 2 * n ^ 5 := by
      have hn' : (335 : ℝ) ≤ n := by exact_mod_cast hn
      have h0 : (0 : ℝ) ≤ n := by linarith
      have a5 : 335 * (n : ℝ) ^ 4 ≤ (n : ℝ) ^ 5 := by
        have := mul_le_mul_of_nonneg_right hn' (pow_nonneg h0 4); nlinarith [this]
      have a4 : 335 * (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 4 := by
        have := mul_le_mul_of_nonneg_right hn' (pow_nonneg h0 3); nlinarith [this]
      have a3 : 335 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by
        have := mul_le_mul_of_nonneg_right hn' (pow_nonneg h0 2); nlinarith [this]
      have a2 : 335 * (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      have e : ((n : ℝ) + 1) ^ 5 = (n : ℝ) ^ 5 + 5 * n ^ 4 + 10 * n ^ 3 + 10 * n ^ 2 + 5 * n + 1 := by ring
      have hr : ((n : ℝ) + 1) ^ 5 ≤ 2 * (n : ℝ) ^ 5 := by rw [e]; linarith
      exact_mod_cast hr
    have h2 : 2 ^ (n + 1 - 3) = 2 * 2 ^ (n - 3) := by
      rw [show n + 1 - 3 = (n - 3) + 1 by omega, pow_succ]; ring
    rw [h2]
    calc 10 ^ 40 * (n + 1) ^ 5 ≤ 10 ^ 40 * (2 * n ^ 5) := Nat.mul_le_mul_left _ h1
      _ = 2 * (10 ^ 40 * n ^ 5) := by ring
      _ ≤ 2 * 2 ^ (n - 3) := Nat.mul_le_mul_left _ ih

set_option exponentiation.threshold 700 in
theorem chain_K_lt_91_thm : chain_K_lt_91 := by
  intro m k l a h hm91
  by_contra hK
  rw [not_lt] at hK
  have hm : 0 < m := h.1
  have hpos := (lemma4_thm m k l a h).1
  have h7 := lemma7_thm m k l a h
  set K := Ksum m k with hKdef
  set E : ℝ := (δ - 1) * (K : ℝ) / (δ ^ m - 1) with hE
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hEK : (K : ℝ) / (3 * 10 ^ 18) ≤ E := K_div_le_E_91 hm hm91 K hK0
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hKr : (2 * 10 ^ 21 : ℝ) ≤ K := by exact_mod_cast hK
  have hmr : (m : ℝ) ≤ 91 := by exact_mod_cast hm91
  have hup : Lam m k l < 182 * (2 : ℝ) ^ (-E) := by
    have h2 : (0 : ℝ) < (2 : ℝ) ^ (-E) := Real.rpow_pos_of_pos (by norm_num) _
    have : 2 * (m : ℝ) * (2 : ℝ) ^ (-E) ≤ 182 * (2 : ℝ) ^ (-E) :=
      mul_le_mul_of_nonneg_right (by linarith) h2.le
    linarith
  have hcast : ((((K + Lsum m l : ℕ) : ℤ)) : ℝ) = ((K + Lsum m l : ℕ) : ℝ) := Int.cast_natCast _
  have hLam : |((((K + Lsum m l : ℕ) : ℤ)) : ℝ) * Real.log 2 - (K : ℝ) * Real.log 3| = Lam m k l := by
    rw [hcast]; exact abs_of_pos hpos
  by_cases h2 : K < Logs23.qBr'
  · -- `2·10^21 ≤ K < qBr'`: the bridge
    have hg := Logs23.bridge_gap_thm K ((K + Lsum m l : ℕ) : ℤ) hKpos h2
    have hv := Logs23.bridge_value_thm
    rw [Logs23.bridge_value] at hv
    rw [hLam] at hg
    have hE600 : (600 : ℝ) ≤ E := by
      have : (600 : ℝ) ≤ (K : ℝ) / (3 * 10 ^ 18) := by
        rw [le_div_iff₀ (by norm_num)]; linarith
      linarith
    have hr : (2 : ℝ) ^ (-E) ≤ (2 : ℝ) ^ (-(600 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hc : (2 : ℝ) ^ (-(600 : ℝ)) = ((2 : ℝ) ^ 600)⁻¹ := by
      rw [Real.rpow_neg (by norm_num)]; congr 1; exact_mod_cast Real.rpow_natCast 2 600
    rw [hc] at hr
    have hnum : (182 : ℝ) * ((2 : ℝ) ^ 600)⁻¹ < 1 / 10 ^ 101 := by norm_num
    linarith [mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 182)]
  · -- `K ≥ qBr' ≥ 2^334`
    rw [not_lt] at h2
    have hq : 2 ^ 334 ≤ Logs23.qBr' := by unfold Logs23.qBr'; decide +kernel
    have hbig : 2 ^ 334 ≤ K := hq.trans h2
    have hlow := Logs23.two_log_lower_thm (K + Lsum m l) K hbig
    have hLam' : |((K + Lsum m l : ℕ) : ℝ) * Real.log 2 - (K : ℝ) * Real.log 3| = Lam m k l := by
      exact abs_of_pos hpos
    rw [hLam'] at hlow
    set ν := Nat.log 2 K + 1 with hν
    have hν335 : 335 ≤ ν := by have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hbig; omega
    have hge : 2 ^ (ν - 1) ≤ K := by
      have := Nat.pow_log_le_self 2 (by omega : K ≠ 0)
      rwa [show ν - 1 = Nat.log 2 K by omega]
    have hpow := pow5_le_two_pow_40 hν335
    have hpowr : (10 : ℝ) ^ 40 * (ν : ℝ) ^ 5 ≤ 2 ^ (ν - 3) := by exact_mod_cast hpow
    have hkr : (2 : ℝ) ^ (ν - 1) ≤ K := by exact_mod_cast hge
    have h4 : (2 : ℝ) ^ (ν - 1) = 4 * 2 ^ (ν - 3) := by
      rw [show ν - 1 = (ν - 3) + 2 by omega, pow_add]; ring
    have hν5 : (1 : ℝ) ≤ (ν : ℝ) ^ 5 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ ν))
    have hl2 := Real.log_two_gt_d9
    have hE0 : 0 ≤ E := le_trans (by positivity) hEK
    have hEl : (K : ℝ) / (3 * 10 ^ 18) * 0.6931471803 ≤ E * Real.log 2 :=
      mul_le_mul hEK hl2.le (by norm_num) hE0
    have hX : (10 : ℝ) ^ 12 * (ν : ℝ) ^ 5 + 182 ≤ E * Real.log 2 := by
      have : (K : ℝ) / (3 * 10 ^ 18) * 0.6931471803 = (K : ℝ) * (0.6931471803 / (3 * 10 ^ 18)) := by ring
      rw [this] at hEl
      linarith
    have h182 : (182 : ℝ) ≤ Real.exp 182 := by linarith [Real.add_one_le_exp (182 : ℝ)]
    have hrp : (2 : ℝ) ^ (-E) = Real.exp (-(E * Real.log 2)) := by
      rw [Real.rpow_def_of_pos (by norm_num)]; ring_nf
    have hfin : 182 * (2 : ℝ) ^ (-E) ≤ Real.exp (-(10 ^ 12 * ((ν : ℕ) : ℝ) ^ 5)) := by
      rw [hrp]
      calc 182 * Real.exp (-(E * Real.log 2)) ≤ Real.exp 182 * Real.exp (-(E * Real.log 2)) :=
            mul_le_mul_of_nonneg_right h182 (Real.exp_pos _).le
        _ = Real.exp (182 - E * Real.log 2) := by rw [← Real.exp_add]; ring_nf
        _ ≤ Real.exp (-(10 ^ 12 * ((ν : ℕ) : ℝ) ^ 5)) := Real.exp_le_exp.mpr (by linarith)
    linarith

theorem cycle_K_lt_91_thm : cycle_K_lt_91 := by
  intro n N hn hN hc hm91
  obtain ⟨k, l, a, hs, hK⟩ := cycle_chain_thm n N hn hN hc
  rw [← hK]
  exact chain_K_lt_91_thm _ k l a hs hm91

end Sdw2005
