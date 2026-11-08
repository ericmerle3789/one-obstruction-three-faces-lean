import Mathlib
import Sdw2005.Chaine
import Sdw2005.Bornes
import Logs23.TwoLog
import Brox2000.Analyse

/-!
# Brox 2000 · phase B: the chain equation of the `3x − 1` map

The cycles of Brox's `T` on the negative integers are, through `x ↦ −x`, the cycles of
`D(y) = y/2` (`y` even), `(3y − 1)/2` (`y` odd) on the positive integers (`Brox2000/MiroirCycles.lean`). Between two
consecutive local minima `x_i < x_{i+1}` of such a cycle, `k_i ≥ 1` odd steps and `l_i ≥ 1` even steps give, with
`x_i = 2^{k_i} a_i + 1`, the chain equation `3^{k_i} a_i + 1 = 2^{l_i} x_{i+1}` (mirror of `Sdw2005.ChainSol`).

With `Y_i = x_i − 1 = 2^{k_i} a_i` and `P_i = 3^{k_i} a_i`:
* `Λ' = K log 3 − (K + L) log 2 = Σ (log(1 + 1/Y_i) − log(1 + 1/P_i))`, so `0 < Λ' < Σ 1/Y_i` (`lemma4M`);
* `Y_{i+1} < P_i ≤ Y_i^δ` (`Y_succ_lt`), so `log Y_i ≥ (δ − 1) K log 2/(δ^m − 1)` (`lemma7M_min`), and
  `Λ' < m 2^{−E}` (`lemma7M`), the mirror of Lemma 7 of Simons–de Weger (`Sdw2005.lemma7_thm`);
* if `m < 2 log K`, then `K < 2^1500` (`chain_K_lt_brox_M`, as `chain_K_lt_brox`).
-/

namespace Brox2000.Miroir

open Sdw2005 Finset

/-- The chain equation of the `3x − 1` map: local minima `x_i = 2^{k_i} a_i + 1`, and
`3^{k_i} a_i + 1 = 2^{l_i} x_{i+1}`. -/
def ChainSolM (m : ℕ) (k l a : ℕ → ℕ) : Prop :=
  0 < m ∧ ∀ i < m, 0 < k i ∧ 0 < l i ∧ 0 < a i ∧
    (3 : ℤ) ^ k i * a i + 1 = 2 ^ (k ((i + 1) % m) + l i) * a ((i + 1) % m) + 2 ^ l i

/-- `Y_i = 2^{k_i} a_i` (the local minimum minus one). -/
noncomputable def Y (k a : ℕ → ℕ) (i : ℕ) : ℝ := (2 : ℝ) ^ k i * a i

/-- `P_i = 3^{k_i} a_i`. -/
noncomputable def P (k a : ℕ → ℕ) (i : ℕ) : ℝ := (3 : ℝ) ^ k i * a i

section

variable {m : ℕ} {k l a : ℕ → ℕ} (h : ChainSolM m k l a)
include h

theorem a_pos {i : ℕ} (hi : i < m) : (1 : ℝ) ≤ a i := by exact_mod_cast (h.2 i hi).2.2.1

theorem Y_pos {i : ℕ} (hi : i < m) : 0 < Y k a i := by
  have := a_pos h hi; unfold Y; positivity

theorem P_pos {i : ℕ} (hi : i < m) : 0 < P k a i := by
  have := a_pos h hi; unfold P; positivity

theorem Y_lt_P {i : ℕ} (hi : i < m) : Y k a i < P k a i := by
  have ha := a_pos h hi
  have hk := (h.2 i hi).1
  unfold Y P
  apply mul_lt_mul_of_pos_right _ (by linarith)
  exact pow_lt_pow_left₀ (by norm_num) (by norm_num) hk.ne'

/-- The chain equation in the reals: `P_i + 1 = 2^{l_i} (Y_{i+1} + 1)`. -/
theorem chain_realM {i : ℕ} (hi : i < m) :
    P k a i + 1 = (2 : ℝ) ^ l i * (Y k a ((i + 1) % m) + 1) := by
  obtain ⟨-, -, -, he⟩ := h.2 i hi
  have hr : (3 : ℝ) ^ k i * a i + 1 = 2 ^ (k ((i + 1) % m) + l i) * a ((i + 1) % m) + 2 ^ l i := by
    exact_mod_cast he
  unfold P Y
  rw [pow_add] at hr
  linear_combination hr

theorem Y_succ_lt {i : ℕ} (hi : i < m) : Y k a ((i + 1) % m) < P k a i := by
  have hc := chain_realM h hi
  have hj : (i + 1) % m < m := Nat.mod_lt _ h.1
  have hY := Y_pos h hj
  have hl2 : (2 : ℝ) ≤ 2 ^ l i := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ l i := pow_le_pow_right₀ (by norm_num) (h.2 i hi).2.1
  have := mul_le_mul_of_nonneg_right hl2 (by linarith : (0 : ℝ) ≤ Y k a ((i + 1) % m) + 1)
  linarith

/-- `P_i ≤ Y_i^δ` (`2^δ = 3`, `a_i ≤ a_i^δ`). -/
theorem P_le_rpow {i : ℕ} (hi : i < m) : P k a i ≤ (Y k a i) ^ δ := by
  have ha := a_pos h hi
  unfold P Y
  rw [Real.mul_rpow (by positivity) (by positivity)]
  have h2 : ((2 : ℝ) ^ k i) ^ δ = (3 : ℝ) ^ k i := by
    rw [← Real.rpow_natCast (2 : ℝ), ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
      two_rpow_delta, Real.rpow_natCast]
  rw [h2]
  have h3 : (a i : ℝ) ≤ (a i : ℝ) ^ δ := by
    calc (a i : ℝ) = (a i : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (a i : ℝ) ^ δ := Real.rpow_le_rpow_of_exponent_le ha one_lt_delta.le
  exact mul_le_mul_of_nonneg_left h3 (by positivity)

end

/-! ## Lemma 4, mirrored -/

theorem lemma4M {m : ℕ} {k l a : ℕ → ℕ} (h : ChainSolM m k l a) :
    0 < -Lam m k l ∧ -Lam m k l < ∑ i ∈ range m, 1 / Y k a i := by
  have hm : 0 < m := h.1
  have hj : ∀ i, (i + 1) % m < m := fun i => Nat.mod_lt _ hm
  set g : ℝ → ℝ := fun x => Real.log ((x + 1) / x) with hg
  have hkey : ∀ i ∈ range m, g (Y k a i) - g (P k a i) =
      Real.log (Y k a i + 1) - Real.log (Y k a ((i + 1) % m) + 1)
        + ((k i : ℝ) * Real.log 3 - (k i : ℝ) * Real.log 2 - (l i : ℝ) * Real.log 2) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hY := Y_pos h hi
    have hP := P_pos h hi
    have hY' := Y_pos h (hj i)
    have ha : (0 : ℝ) < a i := by linarith [a_pos h hi]
    have hc := chain_realM h hi
    have hlogP1 : Real.log (P k a i + 1) = (l i : ℝ) * Real.log 2 + Real.log (Y k a ((i + 1) % m) + 1) := by
      rw [hc, Real.log_mul (by positivity) (by linarith), Real.log_pow]
    have hlogY : Real.log (Y k a i) = (k i : ℝ) * Real.log 2 + Real.log (a i) := by
      unfold Y; rw [Real.log_mul (by positivity) ha.ne', Real.log_pow]
    have hlogP : Real.log (P k a i) = (k i : ℝ) * Real.log 3 + Real.log (a i) := by
      unfold P; rw [Real.log_mul (by positivity) ha.ne', Real.log_pow]
    simp only [hg]
    rw [Real.log_div (by linarith) hY.ne', Real.log_div (by linarith) hP.ne', hlogP1, hlogY, hlogP]
    ring
  have hsum : -Lam m k l = ∑ i ∈ range m, (g (Y k a i) - g (P k a i)) := by
    have r : ∑ i ∈ range m, Real.log (Y k a ((i + 1) % m) + 1) = ∑ i ∈ range m, Real.log (Y k a i + 1) :=
      sum_rot_one m hm (fun j => Real.log (Y k a j + 1))
    rw [Finset.sum_congr rfl hkey, Finset.sum_add_distrib, Finset.sum_sub_distrib, r, sub_self, zero_add,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    unfold Lam Ksum Lsum
    push_cast
    simp only [add_mul, Finset.sum_mul]
    ring
  -- `g` on `(0, ∞)`: `g x = log (1 + 1/x)`
  have hg1 : ∀ x : ℝ, 0 < x → (x + 1) / x = 1 + 1 / x := fun x hx => by field_simp
  have hgpos : ∀ x : ℝ, 0 < x → 0 < g x := fun x hx => by
    simp only [hg]; rw [hg1 x hx]; exact Real.log_pos (by have := one_div_pos.mpr hx; linarith)
  have hganti : ∀ x y : ℝ, 0 < x → x < y → g y < g x := fun x y hx hxy => by
    simp only [hg]
    rw [hg1 x hx, hg1 y (by linarith)]
    have h1 : 1 / y < 1 / x := one_div_lt_one_div_of_lt hx hxy
    exact Real.log_lt_log (by have := one_div_pos.mpr (show 0 < y by linarith); linarith) (by linarith)
  have hgle : ∀ x : ℝ, 0 < x → g x ≤ 1 / x := fun x hx => by
    simp only [hg]; rw [hg1 x hx]
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / x by have := one_div_pos.mpr hx; linarith)
    linarith
  refine ⟨?_, ?_⟩
  · rw [hsum]
    apply Finset.sum_pos
    · intro i hi
      rw [Finset.mem_range] at hi
      have := hganti _ _ (Y_pos h hi) (Y_lt_P h hi)
      linarith
    · exact ⟨0, Finset.mem_range.mpr hm⟩
  · rw [hsum]
    apply Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.mpr hm⟩
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 := hgpos _ (P_pos h hi)
    have h2 := hgle _ (Y_pos h hi)
    linarith

/-! ## Lemma 7, mirrored -/

/-- `Y_i ≥ 2^E`, `E = (δ − 1) K/(δ^m − 1)`. -/
theorem lemma7M_min {m : ℕ} {k l a : ℕ → ℕ} (h : ChainSolM m k l a) {i0 : ℕ} (hi0 : i0 < m) :
    (2 : ℝ) ^ ((δ - 1) * (Ksum m k : ℝ) / (δ ^ m - 1)) ≤ Y k a i0 := by
  have hm : 0 < m := h.1
  have hδ := one_lt_delta
  set w : ℕ → ℝ := fun j => Real.log (Y k a ((i0 + j) % m)) with hw
  have hrec : ∀ j, w (j + 1) ≤ δ * w j := by
    intro j
    have hij : (i0 + j) % m < m := Nat.mod_lt _ hm
    have hstep : Y k a (((i0 + j) % m + 1) % m) ≤ (Y k a ((i0 + j) % m)) ^ δ :=
      ((Y_succ_lt h hij).trans_le (P_le_rpow h hij)).le
    rw [Nat.mod_add_mod] at hstep
    simp only [hw]
    rw [show i0 + (j + 1) = i0 + j + 1 by omega, ← Real.log_rpow (Y_pos h hij)]
    exact Real.log_le_log (Y_pos h (Nat.mod_lt _ hm)) hstep
  have hpow : ∀ j, w j ≤ δ ^ j * w 0 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc w (j + 1) ≤ δ * w j := hrec j
        _ ≤ δ * (δ ^ j * w 0) := mul_le_mul_of_nonneg_left ih (by linarith)
        _ = δ ^ (j + 1) * w 0 := by ring
  have hlow : (Ksum m k : ℝ) * Real.log 2 ≤ ∑ j ∈ range m, w j := by
    have hr := sum_rot m hm (fun i => Real.log (Y k a i)) i0
    simp only [hw]
    rw [hr, Ksum, Nat.cast_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_range] at hi
    have ha := a_pos h hi
    have h2k : (2 : ℝ) ^ k i ≤ Y k a i := le_mul_of_one_le_right (by positivity) ha
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) h2k
  have hup : ∑ j ∈ range m, w j ≤ w 0 * ((δ ^ m - 1) / (δ - 1)) := by
    calc ∑ j ∈ range m, w j ≤ ∑ j ∈ range m, δ ^ j * w 0 := Finset.sum_le_sum (fun j _ => hpow j)
      _ = w 0 * ((δ ^ m - 1) / (δ - 1)) := by
          rw [← Finset.sum_mul, geom_sum_eq hδ.ne', mul_comm]
  have hA : 0 < δ - 1 := by linarith
  have hB : 0 < δ ^ m - 1 := by linarith [one_lt_pow₀ hδ hm.ne']
  have hw0 : Real.log 2 * ((δ - 1) * (Ksum m k : ℝ) / (δ ^ m - 1)) ≤ w 0 := by
    calc Real.log 2 * ((δ - 1) * (Ksum m k : ℝ) / (δ ^ m - 1))
        = ((Ksum m k : ℝ) * Real.log 2) * ((δ - 1) / (δ ^ m - 1)) := by ring
      _ ≤ (w 0 * ((δ ^ m - 1) / (δ - 1))) * ((δ - 1) / (δ ^ m - 1)) :=
          mul_le_mul_of_nonneg_right (hlow.trans hup) (div_nonneg hA.le hB.le)
      _ = w 0 := by field_simp
  have hw0' : w 0 = Real.log (Y k a i0) := by
    simp only [hw]; rw [Nat.add_zero, Nat.mod_eq_of_lt hi0]
  rw [hw0'] at hw0
  rw [Real.rpow_def_of_pos (by norm_num)]
  calc Real.exp (Real.log 2 * ((δ - 1) * (Ksum m k : ℝ) / (δ ^ m - 1)))
      ≤ Real.exp (Real.log (Y k a i0)) := Real.exp_le_exp.mpr hw0
    _ = Y k a i0 := Real.exp_log (Y_pos h hi0)

/-- `Λ' < m · 2^{−E}`. -/
theorem lemma7M {m : ℕ} {k l a : ℕ → ℕ} (h : ChainSolM m k l a) :
    -Lam m k l < (m : ℝ) * (2 : ℝ) ^ (-((δ - 1) * (Ksum m k : ℝ) / (δ ^ m - 1))) := by
  set E : ℝ := (δ - 1) * (Ksum m k : ℝ) / (δ ^ m - 1) with hE
  have h4 := (lemma4M h).2
  have hterm : ∀ i ∈ range m, 1 / Y k a i ≤ (2 : ℝ) ^ (-E) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h7 := lemma7M_min h hi
    have hpos : (0 : ℝ) < (2 : ℝ) ^ E := Real.rpow_pos_of_pos (by norm_num) _
    calc 1 / Y k a i ≤ 1 / (2 : ℝ) ^ E := one_div_le_one_div_of_le hpos h7
      _ = (2 : ℝ) ^ (-E) := by rw [Real.rpow_neg (by norm_num), one_div]
  calc -Lam m k l < ∑ i ∈ range m, 1 / Y k a i := h4
    _ ≤ ∑ i ∈ range m, (2 : ℝ) ^ (-E) := Finset.sum_le_sum hterm
    _ = (m : ℝ) * (2 : ℝ) ^ (-E) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ## Few blocks force a bounded `K` -/

set_option exponentiation.threshold 400 in
/-- If `m < 2 log K`, a solution of the chain equation of the `3x − 1` map has `K < 2^1500` (as
`Brox2000.chain_K_lt_brox`). -/
theorem chain_K_lt_brox_M (m : ℕ) (k l a : ℕ → ℕ) (h : ChainSolM m k l a)
    (hm : (m : ℝ) < 2 * Real.log (Ksum m k : ℝ)) : Ksum m k < 2 ^ 1500 := by
  by_contra hK
  rw [not_lt] at hK
  have hm0 : 0 < m := h.1
  have hpos := (lemma4M h).1
  have h7M := lemma7M h
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
  have hLam' : |((K + Lsum m l : ℕ) : ℝ) * Real.log 2 - (K : ℝ) * Real.log 3| = -Lam m k l :=
    abs_of_neg (neg_pos.mp hpos)
  have h7 : -Lam m k l < 2 * (m : ℝ) * (2 : ℝ) ^ (-E) := by
    have h2E : 0 < (2 : ℝ) ^ (-E) := Real.rpow_pos_of_pos (by norm_num) _
    have hm0' : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have h2m : (m : ℝ) * (2 : ℝ) ^ (-E) ≤ 2 * (m : ℝ) * (2 : ℝ) ^ (-E) :=
      mul_le_mul_of_nonneg_right (by linarith only [hm0']) h2E.le
    linarith only [h7M, h2m]
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

end Brox2000.Miroir
