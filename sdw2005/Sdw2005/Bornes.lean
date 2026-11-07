import Mathlib
import Sdw2005.Chaine
import Logs23.Pont
import Logs23.TwoLog

/-!
# Sdw2005 · `chain_K_lt`: for `m ≤ 82`, `K < 4·10^18`, without hypothesis

Lemma 7 (`X0 = 1`) gives `0 < Λ < 2m · 2^{−E}` with `E = (δ − 1) K / (δ^m − 1) ≥ K / (5·10^16)` for `m ≤ 82`
(`58/100 ≤ δ − 1`, `δ ≤ 317/200`). Lower bounds for `Λ = (K + L) log 2 − K log 3` when `K ≥ 4·10^18`:

* `K < q₃₉`: best approximation (`Logs23.gap_of_unimodular`) with the convergents `p₃₈/q₃₈ < δ < p₃₉/q₃₉` of
  `log₂ 3`: `Λ ≥ |p₃₈ log 2 − q₃₈ log 3| ≥ 10^(−20)`, against `Λ < 164 · 2^(−80)`;
* `q₃₉ ≤ K < qBr'`: the bridge of `../logs23/` (`Λ ≥ 10^(−101)`), against `Λ < 164 · 2^(−500)`;
* `K ≥ qBr' ≥ 2^334`: `Logs23.two_log_lower_thm` (`Λ ≥ exp(−10^12 ν^5)`, `2^(ν − 1) ≤ K`), against
  `Λ < 164 · 2^(−K/(5·10^16))`.

The signs and sizes of the two linear forms are compared with the rational enclosures of `log 2` and `log (3/2)`
of `Logs23/Encadrements.lean`, by the kernel.
-/

namespace Sdw2005

/-! ## Two convergents of `log₂ 3` -/

/-- Numerator of the convergent of index 38 of `log₂ 3` (`p₃₈/q₃₈ < log₂ 3`). -/
def p38 : ℕ := 36143248623210700400
/-- Denominator of the convergent of index 38. -/
def q38 : ℕ := 22803850947114245497
/-- Numerator of the convergent of index 39 (`p₃₉/q₃₉ > log₂ 3`). -/
def p39 : ℕ := 43497921996957973433
/-- Denominator of the convergent of index 39. -/
def q39 : ℕ := 27444133206411171953

theorem unimod_38 : (p39 : ℤ) * q38 - p38 * q39 = 1 := by decide +kernel

theorem e38_rat : (p38 : ℚ) * Logs23.L2hi - q38 * (Logs23.L2lo + Logs23.L32lo) ≤ -(1 / 10 ^ 20) := by
  decide +kernel

theorem e39_rat : 0 < (p39 : ℚ) * Logs23.L2lo - q39 * (Logs23.L2hi + Logs23.L32hi) := by decide +kernel

theorem e38_le : (p38 : ℝ) * Real.log 2 - (q38 : ℝ) * Real.log 3 ≤ -(1 / 10 ^ 20) := by
  obtain ⟨-, h2⟩ := Logs23.log_two_bounds
  obtain ⟨h3, -⟩ := Logs23.log_three_bounds
  have hr : ((p38 : ℚ) * Logs23.L2hi - q38 * (Logs23.L2lo + Logs23.L32lo) : ℝ) ≤ ((-(1 / 10 ^ 20) : ℚ) : ℝ) := by
    exact_mod_cast e38_rat
  push_cast at hr h3
  have hp : (0 : ℝ) ≤ p38 := by positivity
  have hq : (0 : ℝ) ≤ q38 := by positivity
  nlinarith

theorem e39_pos : 0 < (p39 : ℝ) * Real.log 2 - (q39 : ℝ) * Real.log 3 := by
  obtain ⟨h1, -⟩ := Logs23.log_two_bounds
  obtain ⟨-, h4⟩ := Logs23.log_three_bounds
  have hr : ((0 : ℚ) : ℝ) < ((p39 : ℚ) * Logs23.L2lo - q39 * (Logs23.L2hi + Logs23.L32hi) : ℝ) := by
    exact_mod_cast e39_rat
  push_cast at hr h4
  have hp : (0 : ℝ) ≤ p39 := by positivity
  have hq : (0 : ℝ) ≤ q39 := by positivity
  nlinarith

/-- For `0 < K < q₃₉`: `10^(−20) ≤ |L log 2 − K log 3|`. -/
theorem gap_38 (K : ℕ) (L : ℤ) (hK : 0 < K) (hK' : K < q39) :
    (1 : ℝ) / 10 ^ 20 ≤ |(L : ℝ) * Real.log 2 - (K : ℝ) * Real.log 3| := by
  have h₁ := e38_le
  have hneg : (p38 : ℝ) * Real.log 2 - (q38 : ℝ) * Real.log 3 < 0 := by
    have : (0 : ℝ) < 1 / 10 ^ 20 := by positivity
    linarith
  have hg := Logs23.gap_of_unimodular unimod_38 hneg e39_pos K L hK hK'
  rw [abs_of_neg hneg] at hg
  linarith

/-! ## `δ` and the exponent `E` -/

theorem delta_le : δ ≤ 317 / 200 := by
  have hr : (200 : ℚ) * Logs23.L32hi ≤ 117 * Logs23.L2lo := by decide +kernel
  have hr' : (200 : ℝ) * (Logs23.L32hi : ℝ) ≤ 117 * (Logs23.L2lo : ℝ) := by exact_mod_cast hr
  obtain ⟨h2lo, -⟩ := Logs23.log_two_bounds
  obtain ⟨-, h32hi⟩ := Logs23.log_three_halves_bounds
  unfold δ
  rw [div_le_iff₀ (Real.log_pos (by norm_num)), Logs23.log_three_eq]
  linarith

theorem delta_sub_one_ge : 58 / 100 ≤ δ - 1 := by
  have hr : (58 : ℚ) * Logs23.L2hi ≤ 100 * Logs23.L32lo := by decide +kernel
  have hr' : (58 : ℝ) * (Logs23.L2hi : ℝ) ≤ 100 * (Logs23.L32lo : ℝ) := by exact_mod_cast hr
  obtain ⟨-, h2hi⟩ := Logs23.log_two_bounds
  obtain ⟨h32lo, -⟩ := Logs23.log_three_halves_bounds
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold δ
  rw [le_sub_iff_add_le, le_div_iff₀ hl, Logs23.log_three_eq]
  linarith

/-- For `1 ≤ m ≤ 82`: `K / (5·10^16) ≤ (δ − 1) K / (δ^m − 1)`. -/
theorem K_div_le_E {m : ℕ} (hm : 0 < m) (hm82 : m ≤ 82) (K : ℝ) (hK : 0 ≤ K) :
    K / (5 * 10 ^ 16) ≤ (δ - 1) * K / (δ ^ m - 1) := by
  have hδ := one_lt_delta
  have hB : 0 < δ ^ m - 1 := by linarith [one_lt_pow₀ hδ hm.ne']
  have hpow : δ ^ m ≤ (317 / 200 : ℝ) ^ 82 :=
    calc δ ^ m ≤ δ ^ 82 := pow_le_pow_right₀ hδ.le hm82
      _ ≤ (317 / 200 : ℝ) ^ 82 := pow_le_pow_left₀ (by linarith) delta_le 82
  have hc : (317 / 200 : ℝ) ^ 82 - 1 ≤ 58 / 100 * (5 * 10 ^ 16) := by norm_num
  have hA := delta_sub_one_ge
  rw [div_le_div_iff₀ (by norm_num) hB]
  have h1 : K * (δ ^ m - 1) ≤ K * (58 / 100 * (5 * 10 ^ 16)) := mul_le_mul_of_nonneg_left (by linarith) hK
  have h2 : K * (5 * 10 ^ 16) * (58 / 100) ≤ K * (5 * 10 ^ 16) * (δ - 1) :=
    mul_le_mul_of_nonneg_left hA (by positivity)
  linarith

/-! ## A polynomial against an exponential -/

theorem pow5_le_two_pow' {n : ℕ} (hn : 335 ≤ n) : 10 ^ 30 * n ^ 5 ≤ 2 ^ (n - 3) := by
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
    calc 10 ^ 30 * (n + 1) ^ 5 ≤ 10 ^ 30 * (2 * n ^ 5) := Nat.mul_le_mul_left _ h1
      _ = 2 * (10 ^ 30 * n ^ 5) := by ring
      _ ≤ 2 * 2 ^ (n - 3) := Nat.mul_le_mul_left _ ih

/-! ## The target of layer 1 -/

set_option exponentiation.threshold 600 in
theorem chain_K_lt_thm : chain_K_lt := by
  intro m k l a h hm82
  by_contra hK
  rw [not_lt] at hK
  have hm : 0 < m := h.1
  have hpos := (lemma4_thm m k l a h).1
  have h7 := lemma7_thm m k l a h
  set K := Ksum m k with hKdef
  set E : ℝ := (δ - 1) * (K : ℝ) / (δ ^ m - 1) with hE
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hEK : (K : ℝ) / (5 * 10 ^ 16) ≤ E := K_div_le_E hm hm82 K hK0
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hKr : (4 * 10 ^ 18 : ℝ) ≤ K := by exact_mod_cast hK
  have hmr : (m : ℝ) ≤ 82 := by exact_mod_cast hm82
  have hup : Lam m k l < 164 * (2 : ℝ) ^ (-E) := by
    have h2 : (0 : ℝ) < (2 : ℝ) ^ (-E) := Real.rpow_pos_of_pos (by norm_num) _
    have : 2 * (m : ℝ) * (2 : ℝ) ^ (-E) ≤ 164 * (2 : ℝ) ^ (-E) :=
      mul_le_mul_of_nonneg_right (by linarith) h2.le
    linarith
  -- `Λ` as a linear form
  have hcast : ((((K + Lsum m l : ℕ) : ℤ)) : ℝ) = ((K + Lsum m l : ℕ) : ℝ) := Int.cast_natCast _
  have hLam : |((((K + Lsum m l : ℕ) : ℤ)) : ℝ) * Real.log 2 - (K : ℝ) * Real.log 3| = Lam m k l := by
    rw [hcast]; exact abs_of_pos hpos
  by_cases h1 : K < q39
  · -- `4·10^18 ≤ K < q₃₉`
    have hg := gap_38 K ((K + Lsum m l : ℕ) : ℤ) hKpos h1
    rw [hLam] at hg
    have hE80 : (80 : ℝ) ≤ E := by
      have : (80 : ℝ) ≤ (K : ℝ) / (5 * 10 ^ 16) := by
        rw [le_div_iff₀ (by norm_num)]; linarith
      linarith
    have hr : (2 : ℝ) ^ (-E) ≤ (2 : ℝ) ^ (-(80 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hc : (2 : ℝ) ^ (-(80 : ℝ)) = ((2 : ℝ) ^ 80)⁻¹ := by
      rw [Real.rpow_neg (by norm_num)]; congr 1; exact_mod_cast Real.rpow_natCast 2 80
    rw [hc] at hr
    have hnum : (164 : ℝ) * ((2 : ℝ) ^ 80)⁻¹ < 1 / 10 ^ 20 := by norm_num
    linarith [mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 164)]
  rw [not_lt] at h1
  by_cases h2 : K < Logs23.qBr'
  · -- `q₃₉ ≤ K < qBr'`
    have hg := Logs23.bridge_gap_thm K ((K + Lsum m l : ℕ) : ℤ) hKpos h2
    have hv := Logs23.bridge_value_thm
    rw [Logs23.bridge_value] at hv
    rw [hLam] at hg
    have hK39 : (25 * 10 ^ 18 : ℝ) ≤ K := by
      have : 25 * 10 ^ 18 ≤ K := le_trans (by unfold q39; norm_num) h1
      exact_mod_cast this
    have hE500 : (500 : ℝ) ≤ E := by
      have : (500 : ℝ) ≤ (K : ℝ) / (5 * 10 ^ 16) := by
        rw [le_div_iff₀ (by norm_num)]; linarith
      linarith
    have hr : (2 : ℝ) ^ (-E) ≤ (2 : ℝ) ^ (-(500 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hc : (2 : ℝ) ^ (-(500 : ℝ)) = ((2 : ℝ) ^ 500)⁻¹ := by
      rw [Real.rpow_neg (by norm_num)]; congr 1; exact_mod_cast Real.rpow_natCast 2 500
    rw [hc] at hr
    have hnum : (164 : ℝ) * ((2 : ℝ) ^ 500)⁻¹ < 1 / 10 ^ 101 := by norm_num
    linarith [mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 164)]
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
    have hpow := pow5_le_two_pow' hν335
    have hpowr : (10 : ℝ) ^ 30 * (ν : ℝ) ^ 5 ≤ 2 ^ (ν - 3) := by exact_mod_cast hpow
    have hkr : (2 : ℝ) ^ (ν - 1) ≤ K := by exact_mod_cast hge
    have h4 : (2 : ℝ) ^ (ν - 1) = 4 * 2 ^ (ν - 3) := by
      rw [show ν - 1 = (ν - 3) + 2 by omega, pow_add]; ring
    have hν5 : (1 : ℝ) ≤ (ν : ℝ) ^ 5 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ ν))
    have hl2 := Real.log_two_gt_d9
    have hE0 : 0 ≤ E := le_trans (by positivity) hEK
    have hEl : (K : ℝ) / (5 * 10 ^ 16) * 0.6931471803 ≤ E * Real.log 2 :=
      mul_le_mul hEK hl2.le (by norm_num) hE0
    -- `10^12 ν^5 + 164 ≤ E log 2`
    have hX : (10 : ℝ) ^ 12 * (ν : ℝ) ^ 5 + 164 ≤ E * Real.log 2 := by
      have : (K : ℝ) / (5 * 10 ^ 16) * 0.6931471803 = (K : ℝ) * (0.6931471803 / (5 * 10 ^ 16)) := by ring
      rw [this] at hEl
      linarith
    -- `164 · 2^(−E) ≤ exp (164 − E log 2) ≤ exp (−10^12 ν^5)`
    have h164 : (164 : ℝ) ≤ Real.exp 164 := by linarith [Real.add_one_le_exp (164 : ℝ)]
    have hrp : (2 : ℝ) ^ (-E) = Real.exp (-(E * Real.log 2)) := by
      rw [Real.rpow_def_of_pos (by norm_num)]; ring_nf
    have hfin : 164 * (2 : ℝ) ^ (-E) ≤ Real.exp (-(10 ^ 12 * ((ν : ℕ) : ℝ) ^ 5)) := by
      rw [hrp]
      calc 164 * Real.exp (-(E * Real.log 2)) ≤ Real.exp 164 * Real.exp (-(E * Real.log 2)) :=
            mul_le_mul_of_nonneg_right h164 (Real.exp_pos _).le
        _ = Real.exp (164 - E * Real.log 2) := by rw [← Real.exp_add]; ring_nf
        _ ≤ Real.exp (-(10 ^ 12 * ((ν : ℕ) : ℝ) ^ 5)) := Real.exp_le_exp.mpr (by linarith)
    linarith

end Sdw2005
