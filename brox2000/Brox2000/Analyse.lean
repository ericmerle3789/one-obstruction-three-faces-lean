import Mathlib
import Sdw2005.Bornes
import Logs23.TwoLog

/-!
# Brox 2000 · the analytic step: few blocks force a bounded `K`

For a solution of the chain equation of Simons–de Weger with `m` blocks and `K` odd steps, Lemma 7 of
`Sdw2005/Chaine.lean` gives `0 < Λ < 2m · 2^{−E}`, `E = (δ − 1) K / (δ^m − 1)`. This is Brox's key inequality
(his §4 with Lemma 5.1: the same exponent `θ₁ n / (θ^ν − 1)`). If `m < 2 log K`, then `e^m < K²` and, with
`δ^200 ≤ e^93`, `(K/δ^m)^200 > K^14`, so `K/δ^m ≥ 2^q`, `q = ⌊7(ν − 1)/100⌋`, `2^{ν−1} ≤ K < 2^ν`. If `K ≥ 2^1500`,
`Logs23.two_log_lower_thm` (`Λ ≥ exp(−10^12 ν^5)`) contradicts `Λ < 2m 2^{−E}`: this replaces the bound of Baker and
Feldman used by Brox, explicitly.
-/

namespace Brox2000

open Sdw2005

theorem poly_le_two_pow {q : ℕ} (hq : 105 ≤ q) : 5 * 10 ^ 12 * (15 * q + 16) ^ 5 ≤ 2 ^ q := by
  induction q, hq using Nat.le_induction with
  | base => norm_num
  | succ q hq ih =>
    have h1 : (15 * (q + 1) + 16) ^ 5 ≤ 2 * (15 * q + 16) ^ 5 := by
      have hx : (1591 : ℝ) ≤ (15 * q + 16 : ℕ) := by exact_mod_cast (show 1591 ≤ 15 * q + 16 by omega)
      set x : ℝ := ((15 * q + 16 : ℕ) : ℝ) with hxdef
      have h0 : (0 : ℝ) ≤ x := by linarith
      have a4 : 1591 * x ^ 4 ≤ x ^ 5 := by
        have := mul_le_mul_of_nonneg_right hx (pow_nonneg h0 4); nlinarith [this]
      have a3 : 1591 * x ^ 3 ≤ x ^ 4 := by
        have := mul_le_mul_of_nonneg_right hx (pow_nonneg h0 3); nlinarith [this]
      have a2 : 1591 * x ^ 2 ≤ x ^ 3 := by
        have := mul_le_mul_of_nonneg_right hx (pow_nonneg h0 2); nlinarith [this]
      have a1 : 1591 * x ≤ x ^ 2 := by nlinarith
      have e : (x + 15) ^ 5 = x ^ 5 + 75 * x ^ 4 + 2250 * x ^ 3 + 33750 * x ^ 2 + 253125 * x + 759375 := by ring
      have hr : (x + 15) ^ 5 ≤ 2 * x ^ 5 := by rw [e]; nlinarith
      have hc : ((15 * (q + 1) + 16 : ℕ) : ℝ) = x + 15 := by rw [hxdef]; push_cast; ring
      have : (((15 * (q + 1) + 16) ^ 5 : ℕ) : ℝ) ≤ ((2 * (15 * q + 16) ^ 5 : ℕ) : ℝ) := by
        push_cast
        rw [show (15 * ((q : ℝ) + 1) + 16) = x + 15 by rw [hxdef]; push_cast; ring,
          show (15 * (q : ℝ) + 16) = x by rw [hxdef]; push_cast; ring]
        exact hr
      exact_mod_cast this
    rw [pow_succ]
    calc 5 * 10 ^ 12 * (15 * (q + 1) + 16) ^ 5 ≤ 5 * 10 ^ 12 * (2 * (15 * q + 16) ^ 5) :=
          Nat.mul_le_mul_left _ h1
      _ = 2 * (5 * 10 ^ 12 * (15 * q + 16) ^ 5) := by ring
      _ ≤ 2 * 2 ^ q := Nat.mul_le_mul_left _ ih
      _ = 2 ^ q * 2 := by ring

theorem delta_pow_200_le : δ ^ 200 ≤ Real.exp 93 := by
  have hδ := one_lt_delta
  have h1 : δ ^ 200 ≤ (317 / 200 : ℝ) ^ 200 := pow_le_pow_left₀ (by linarith) delta_le 200
  have h2 : (317 / 200 : ℝ) ^ 200 ≤ (2.7182818283 : ℝ) ^ 93 := by norm_num
  have h3 : (2.7182818283 : ℝ) ^ 93 ≤ Real.exp 1 ^ 93 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 93
  have h4 : Real.exp 1 ^ 93 = Real.exp 93 := by rw [← Real.exp_nat_mul]; norm_num
  linarith

set_option exponentiation.threshold 400 in
/-- If `m < 2 log K`, a solution of the chain equation has `K < 2^1500`. -/
theorem chain_K_lt_brox (m : ℕ) (k l a : ℕ → ℕ) (h : ChainSol m k l a)
    (hm : (m : ℝ) < 2 * Real.log (Ksum m k : ℝ)) : Ksum m k < 2 ^ 1500 := by
  by_contra hK
  rw [not_lt] at hK
  have hm0 : 0 < m := h.1
  have hpos := (lemma4_thm m k l a h).1
  have h7 := lemma7_thm m k l a h
  set K := Ksum m k with hKdef
  set E : ℝ := (δ - 1) * (K : ℝ) / (δ ^ m - 1) with hE
  have hKpos : 0 < K := lt_of_lt_of_le (by positivity) hK
  have hKr : (0 : ℝ) < K := by exact_mod_cast hKpos
  -- `ν = ⌊log₂ K⌋ + 1`
  set ν := Nat.log 2 K + 1 with hν
  have hν1501 : 1501 ≤ ν := by
    have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hK; omega
  have hge : 2 ^ (ν - 1) ≤ K := by
    have := Nat.pow_log_le_self 2 (by omega : K ≠ 0)
    rwa [show ν - 1 = Nat.log 2 K by omega]
  have hlt : K < 2 ^ ν := Nat.lt_pow_succ_log_self (by norm_num) K
  -- `e^m < K²`
  have hexp : Real.exp m < (K : ℝ) ^ 2 := by
    have e : Real.exp (2 * Real.log K) = (K : ℝ) ^ 2 := by
      rw [show (2 : ℝ) * Real.log K = ((2 : ℕ) : ℝ) * Real.log K by norm_num, Real.exp_nat_mul,
        Real.exp_log hKr]
    rw [← e]; exact Real.exp_lt_exp.mpr hm
  -- `(δ^m)^200 < K^186`
  have hδ := one_lt_delta
  have hδpos : 0 < δ := by linarith
  have hA : (δ ^ m) ^ 200 < (K : ℝ) ^ 186 := by
    calc (δ ^ m) ^ 200 = (δ ^ 200) ^ m := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (Real.exp 93) ^ m := pow_le_pow_left₀ (by positivity) delta_pow_200_le m
      _ = (Real.exp m) ^ 93 := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; congr 1; push_cast; ring
      _ < ((K : ℝ) ^ 2) ^ 93 := pow_lt_pow_left₀ hexp (Real.exp_pos _).le (by norm_num)
      _ = (K : ℝ) ^ 186 := by rw [← pow_mul]
  -- `K^14 < (K/δ^m)^200`
  have hdm : 0 < δ ^ m := pow_pos hδpos m
  have hB : (K : ℝ) ^ 14 < ((K : ℝ) / δ ^ m) ^ 200 := by
    rw [div_pow, lt_div_iff₀ (pow_pos hdm 200)]
    calc (K : ℝ) ^ 14 * (δ ^ m) ^ 200 < (K : ℝ) ^ 14 * (K : ℝ) ^ 186 :=
          mul_lt_mul_of_pos_left hA (pow_pos hKr 14)
      _ = (K : ℝ) ^ 200 := by rw [← pow_add]
  -- `2^q < K/δ^m`
  set q := 7 * (ν - 1) / 100 with hq
  have hq105 : 105 ≤ q := by omega
  have hC : ((2 : ℝ) ^ q) ^ 200 ≤ (K : ℝ) ^ 14 := by
    have h1 : 200 * q ≤ 14 * (ν - 1) := by omega
    have h2 : (2 : ℕ) ^ (200 * q) ≤ K ^ 14 :=
      calc (2 : ℕ) ^ (200 * q) ≤ 2 ^ (14 * (ν - 1)) := Nat.pow_le_pow_right (by norm_num) h1
        _ = (2 ^ (ν - 1)) ^ 14 := by rw [← pow_mul, mul_comm]
        _ ≤ K ^ 14 := Nat.pow_le_pow_left hge 14
    rw [← pow_mul, mul_comm]; exact_mod_cast h2
  have hD : (2 : ℝ) ^ q < (K : ℝ) / δ ^ m :=
    (pow_lt_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (200 : ℕ) ≠ 0)).mp
      (lt_of_le_of_lt hC hB)
  -- `E ≥ 0.58 · 2^q`
  have hδm1 : 0 < δ ^ m - 1 := by linarith [one_lt_pow₀ hδ hm0.ne']
  have hEge : 58 / 100 * (2 : ℝ) ^ q ≤ E := by
    have hA' := delta_sub_one_ge
    have h1 : (K : ℝ) / δ ^ m ≤ (K : ℝ) / (δ ^ m - 1) := div_le_div_of_nonneg_left hKr.le hδm1 (by linarith)
    calc 58 / 100 * (2 : ℝ) ^ q ≤ (δ - 1) * ((K : ℝ) / δ ^ m) := mul_le_mul hA' hD.le (by positivity) (by linarith)
      _ ≤ (δ - 1) * ((K : ℝ) / (δ ^ m - 1)) := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = E := by rw [hE]; ring
  -- `ν ≤ 15q + 16`, so `5·10^12 ν^5 ≤ 2^q`
  have hνq : ν ≤ 15 * q + 16 := by omega
  have hpoly : (5 * 10 ^ 12 : ℝ) * (ν : ℝ) ^ 5 ≤ (2 : ℝ) ^ q := by
    have h1 : 5 * 10 ^ 12 * ν ^ 5 ≤ 2 ^ q :=
      le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hνq 5)) (poly_le_two_pow hq105)
    exact_mod_cast h1
  -- `m < 2ν`
  have hm2 : (m : ℝ) < 2 * ν := by
    have h1 : Real.log K < ν * Real.log 2 := by
      rw [← Real.log_pow]
      exact Real.log_lt_log hKr (by exact_mod_cast hlt)
    have h2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    have h3 : (0 : ℝ) ≤ ν := Nat.cast_nonneg _
    have h4 : (ν : ℝ) * Real.log 2 ≤ ν := mul_le_of_le_one_right h3 h2.le
    linarith only [hm, h1, h4]
  -- `10^12 ν^5 + 2m ≤ E log 2`
  have hl2 := Real.log_two_gt_d9
  have hν1 : (1 : ℝ) ≤ ν := by exact_mod_cast (show 1 ≤ ν by omega)
  have hν5 : (ν : ℝ) ≤ (ν : ℝ) ^ 5 := by
    calc (ν : ℝ) = (ν : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (ν : ℝ) ^ 5 := pow_le_pow_right₀ hν1 (by norm_num)
  have hX : (10 : ℝ) ^ 12 * (ν : ℝ) ^ 5 + 2 * m ≤ E * Real.log 2 := by
    have hE0 : 0 ≤ E := le_trans (by positivity) hEge
    have h1 : 58 / 100 * (2 : ℝ) ^ q * 0.6931471803 ≤ E * Real.log 2 :=
      mul_le_mul hEge hl2.le (by norm_num) hE0
    linarith only [h1, hpoly, hm2, hν5, hν1]
  -- the contradiction with `Logs23.two_log_lower_thm`
  have hbig : 2 ^ 334 ≤ K := le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hK
  have hlow := Logs23.two_log_lower_thm (K + Lsum m l) K hbig
  try rw [← hν] at hlow
  have hLam' : |((K + Lsum m l : ℕ) : ℝ) * Real.log 2 - (K : ℝ) * Real.log 3| = Lam m k l :=
    abs_of_pos hpos
  rw [hLam'] at hlow
  have h2m : 2 * (m : ℝ) ≤ Real.exp (2 * m) := by linarith [Real.add_one_le_exp (2 * (m : ℝ))]
  have hrp : (2 : ℝ) ^ (-E) = Real.exp (-(E * Real.log 2)) := by
    rw [Real.rpow_def_of_pos (by norm_num)]; ring_nf
  have hfin : 2 * (m : ℝ) * (2 : ℝ) ^ (-E) ≤ Real.exp (-(10 ^ 12 * ((ν : ℕ) : ℝ) ^ 5)) := by
    rw [hrp]
    calc 2 * (m : ℝ) * Real.exp (-(E * Real.log 2)) ≤ Real.exp (2 * m) * Real.exp (-(E * Real.log 2)) :=
          mul_le_mul_of_nonneg_right h2m (Real.exp_pos _).le
      _ = Real.exp (2 * m - E * Real.log 2) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-(10 ^ 12 * ((ν : ℕ) : ℝ) ^ 5)) := Real.exp_le_exp.mpr (by linarith)
  linarith

end Brox2000
