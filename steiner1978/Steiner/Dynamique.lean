import Mathlib
import Labo.Blueprint
import Steiner.Steiner_Enonces

/-!
# Steiner 1978 · proofs (1): circuits and Davison's equation

`circuit_iff_thm`: a circuit-cycle from `n` with `k ≥ 1` odd iterates and `l` even iterates exists iff
`n + 1 = 2^k h` with `(2^(k+l) − 3^k) h = 2^l − 1`.
-/

namespace Steiner

open LaboBP

/-- `T` on an odd number `2a + 1`. -/
theorem T_odd_eq (a : ℤ) : T (2 * a + 1) = 3 * a + 2 := by
  unfold T
  split_ifs with h <;> omega

/-- `T` on an even number `2a`. -/
theorem T_even_eq (a : ℤ) : T (2 * a) = a := by
  unfold T
  split_ifs with h <;> omega

/-- On an odd number, `2 T(x) = 3x + 1`. -/
theorem two_mul_T_odd {x : ℤ} (hx : Odd x) : 2 * T x = 3 * x + 1 := by
  obtain ⟨a, rfl⟩ := hx
  rw [T_odd_eq]
  ring

/-- On an even number, `2 T(x) = x`. -/
theorem two_mul_T_even {x : ℤ} (hx : Even x) : 2 * T x = x := by
  obtain ⟨a, rfl⟩ := hx
  rw [← two_mul, T_even_eq]

/-- The odd run: `2^i (T^i(n) + 1) = 3^i (n + 1)` while the iterates are odd. -/
theorem run_odd (n : ℤ) (k : ℕ) (hodd : ∀ i < k, Odd (T^[i] n)) :
    ∀ i ≤ k, 2 ^ i * (T^[i] n + 1) = 3 ^ i * (n + 1) := by
  intro i hi
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 := ih (by omega)
    have h2 := two_mul_T_odd (hodd i (by omega))
    rw [Function.iterate_succ_apply']
    calc (2 : ℤ) ^ (i + 1) * (T (T^[i] n) + 1) = 2 ^ i * (2 * T (T^[i] n) + 2) := by ring
      _ = 3 * (2 ^ i * (T^[i] n + 1)) := by rw [h2]; ring
      _ = 3 ^ (i + 1) * (n + 1) := by rw [h1]; ring

/-- The even run: `2^i T^i(y) = y` while the iterates are even. -/
theorem run_even (y : ℤ) (l : ℕ) (heven : ∀ i < l, Even (T^[i] y)) :
    ∀ i ≤ l, 2 ^ i * T^[i] y = y := by
  intro i hi
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 := ih (by omega)
    have h2 := two_mul_T_even (heven i (by omega))
    rw [Function.iterate_succ_apply']
    calc (2 : ℤ) ^ (i + 1) * T (T^[i] y) = 2 ^ i * (2 * T (T^[i] y)) := by ring
      _ = y := by rw [h2, h1]

theorem iterate_split (n : ℤ) (k i : ℕ) : T^[k + i] n = T^[i] (T^[k] n) := by
  rw [add_comm, Function.iterate_add_apply]

/-- From the starting point `n = 2^k h − 1`, the first `k` iterates are `3^i 2^(k−i) h − 1`. -/
theorem odd_phase (h : ℤ) (k : ℕ) :
    ∀ i ≤ k, T^[i] (2 ^ k * h - 1) = 3 ^ i * 2 ^ (k - i) * h - 1 := by
  intro i hi
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    obtain ⟨j, hj⟩ : ∃ j, k - i = j + 1 := ⟨k - i - 1, by omega⟩
    have hj' : k - (i + 1) = j := by omega
    rw [hj, hj']
    have : (3 : ℤ) ^ i * 2 ^ (j + 1) * h - 1 = 2 * (3 ^ i * 2 ^ j * h - 1) + 1 := by ring
    rw [this, T_odd_eq]
    ring

/-- From `y = 2^l n`, the next `l` iterates are `2^(l−i) n`. -/
theorem even_phase (n : ℤ) (l : ℕ) : ∀ i ≤ l, T^[i] (2 ^ l * n) = 2 ^ (l - i) * n := by
  intro i hi
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    obtain ⟨j, hj⟩ : ∃ j, l - i = j + 1 := ⟨l - i - 1, by omega⟩
    have hj' : l - (i + 1) = j := by omega
    rw [hj, hj', pow_succ, mul_comm (2 ^ j : ℤ) 2, mul_assoc, T_even_eq]

theorem coprime_two_three_pow (k : ℕ) : IsCoprime ((2 : ℤ) ^ k) (3 ^ k) :=
  (Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num)).pow

theorem circuit_iff_thm : circuit_iff := by
  intro n k l hk
  constructor
  · rintro ⟨hodd, heven, hcyc⟩
    have e1 := run_odd n k hodd k le_rfl
    have hdvd : (2 : ℤ) ^ k ∣ n + 1 :=
      (coprime_two_three_pow k).dvd_of_dvd_mul_left ⟨T^[k] n + 1, by rw [← e1]⟩
    obtain ⟨h, hh⟩ := hdvd
    refine ⟨h, hh, ?_⟩
    have e2 : T^[k] n + 1 = 3 ^ k * h := by
      have h2k : (2 : ℤ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
      apply mul_left_cancel₀ h2k
      rw [e1, hh]; ring
    have heven' : ∀ i < l, Even (T^[i] (T^[k] n)) := fun i hi => by
      rw [← iterate_split]; exact heven i hi
    have e3 := run_even (T^[k] n) l heven' l le_rfl
    rw [← iterate_split, hcyc] at e3
    unfold DavisonEq
    rw [pow_add]
    linear_combination (-(2 : ℤ) ^ l) * hh + e3 + e2
  · rintro ⟨h, hh, heq⟩
    have hn : n = 2 ^ k * h - 1 := by linarith
    have hodd : ∀ i < k, Odd (T^[i] n) := by
      intro i hi
      rw [hn, odd_phase h k i hi.le]
      obtain ⟨j, hj⟩ : ∃ j, k - i = j + 1 := ⟨k - i - 1, by omega⟩
      rw [hj]
      exact ⟨3 ^ i * 2 ^ j * h - 1, by ring⟩
    have hk' : T^[k] n = 2 ^ l * n := by
      rw [hn, odd_phase h k k le_rfl, Nat.sub_self, pow_zero, mul_one]
      unfold DavisonEq at heq
      rw [pow_add] at heq
      linear_combination -heq
    have hev : ∀ i ≤ l, T^[k + i] n = 2 ^ (l - i) * n := fun i hi => by
      rw [iterate_split, hk', even_phase n l i hi]
    refine ⟨hodd, fun i hi => ?_, ?_⟩
    · rw [hev i hi.le]
      obtain ⟨j, hj⟩ : ∃ j, l - i = j + 1 := ⟨l - i - 1, by omega⟩
      rw [hj]
      exact ⟨2 ^ j * n, by ring⟩
    · rw [hev l le_rfl, Nat.sub_self, pow_zero, one_mul]

end Steiner
