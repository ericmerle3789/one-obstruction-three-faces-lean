import Mathlib
import Labo.Blueprint
import Steiner.Steiner_Enonces
import Steiner.Dynamique
import Steiner.Fini
import Steiner.Analyse

/-!
# Steiner 1978 · proofs (4): the theorem, its integer form, circuits, T★ for `1^k 0^l`

`k ≤ 20000` is settled by the finite check (`Steiner/Fini.lean`), `k > 20000` by `rhin_k_le_thm`.
-/

namespace Steiner

open LaboBP

/-! ## From Davison's equation to the inequalities of the finite check -/

theorem two_le_two_pow {k : ℕ} (hk : 1 ≤ k) : (2 : ℤ) ≤ 2 ^ k := by
  calc (2 : ℤ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk

/-- A positive solution: `0 < D` and `D (2^k − 1) ≤ 3^k − 2^k`. -/
theorem pos_le {k l : ℕ} {h : ℤ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hh : 1 ≤ h) (he : DavisonEq k l h) :
    0 < (2 : ℤ) ^ (k + l) - 3 ^ k ∧ ((2 : ℤ) ^ (k + l) - 3 ^ k) * (2 ^ k - 1) ≤ 3 ^ k - 2 ^ k := by
  obtain ⟨hD, hDn⟩ := pos_facts hl hh he
  refine ⟨hD, ?_⟩
  rw [← hDn]
  apply mul_le_mul_of_nonneg_left _ hD.le
  nlinarith [two_le_two_pow hk]

/-- A negative solution: `0 < E` and `E (2^k + 1) ≤ 3^k − 2^k`. -/
theorem neg_le {k l : ℕ} {h : ℤ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hh : h ≤ -1) (he : DavisonEq k l h) :
    0 < (3 : ℤ) ^ k - 2 ^ (k + l) ∧ ((3 : ℤ) ^ k - 2 ^ (k + l)) * (2 ^ k + 1) ≤ 3 ^ k - 2 ^ k := by
  obtain ⟨hE, hEn⟩ := neg_facts hl hh he
  refine ⟨hE, ?_⟩
  rw [← hEn]
  apply mul_le_mul_of_nonneg_left _ hE.le
  nlinarith [two_le_two_pow hk]

/-- The positive inequalities, in `ℕ`. -/
theorem pos_nat {k L : ℕ} (hD : 0 < (2 : ℤ) ^ L - 3 ^ k)
    (hle : ((2 : ℤ) ^ L - 3 ^ k) * (2 ^ k - 1) ≤ 3 ^ k - 2 ^ k) :
    3 ^ k < 2 ^ L ∧ (2 ^ L - 3 ^ k) * (2 ^ k - 1) ≤ 3 ^ k - 2 ^ k := by
  have h1 : 3 ^ k < 2 ^ L := by
    have : (3 : ℤ) ^ k < 2 ^ L := by linarith
    exact_mod_cast this
  refine ⟨h1, ?_⟩
  have h23 : 2 ^ k ≤ 3 ^ k := Nat.pow_le_pow_left (by norm_num) k
  have h1k : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  zify [h1.le, h23, h1k]
  exact hle

/-- The negative inequalities, in `ℕ`. -/
theorem neg_nat {k L : ℕ} (hE : 0 < (3 : ℤ) ^ k - 2 ^ L)
    (hle : ((3 : ℤ) ^ k - 2 ^ L) * (2 ^ k + 1) ≤ 3 ^ k - 2 ^ k) :
    2 ^ L < 3 ^ k ∧ (3 ^ k - 2 ^ L) * (2 ^ k + 1) ≤ 3 ^ k - 2 ^ k := by
  have h1 : 2 ^ L < 3 ^ k := by
    have : (2 : ℤ) ^ L < 3 ^ k := by linarith
    exact_mod_cast this
  refine ⟨h1, ?_⟩
  have h23 : 2 ^ k ≤ 3 ^ k := Nat.pow_le_pow_left (by norm_num) k
  zify [h1.le, h23]
  exact hle

theorem posOK_of_le {k : ℕ} (h1 : 2 ≤ k) (h2 : k ≤ 20000) : posOK k = true := by
  have := chk_of_le h1 h2
  simp only [chk, Bool.and_eq_true] at this
  exact this.1

theorem negOK_of_le {k : ℕ} (h1 : 3 ≤ k) (h2 : k ≤ 20000) : negOK k = true := by
  have := chk_of_le (by omega) h2
  simp only [chk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at this
  rcases this.2 with h | h
  · omega
  · exact h

/-! ## The theorem -/

theorem steiner_small_thm : steiner_small := by
  intro k l h hk hk2 hl hh he
  obtain ⟨hD, hle⟩ := pos_le hk hl hh he
  rcases Nat.lt_or_ge k 2 with hk1 | hk1
  · obtain rfl : k = 1 := by omega
    -- `2^(1+l) ≤ 4`, so `l = 1`, then `h = 1`
    obtain rfl : l = 1 := by
      by_contra hl1
      have : (2 : ℤ) ^ 3 ≤ 2 ^ (1 + l) := pow_le_pow_right₀ (by norm_num) (by omega)
      norm_num at hle this
      linarith
    unfold DavisonEq at he
    norm_num at he
    exact ⟨rfl, rfl, he⟩
  · obtain ⟨h1, h2⟩ := pos_nat hD hle
    exact (pos_exclude hk (posOK_of_le hk1 hk2) h1 h2).elim

theorem steiner_thm : steiner := by
  intro hR k l h hk hl hh he
  rcases Nat.lt_or_ge 20000 k with hbig | hsmall
  · have := rhin_k_le_thm hR k l h hk hl (by omega) he
    omega
  · exact steiner_small_thm k l h hk hsmall hl hh he

theorem steiner_int_thm : steiner_int := by
  intro hR k l h hk he
  rcases Nat.eq_zero_or_pos l with hl0 | hl
  · subst hl0
    left
    refine ⟨rfl, ?_⟩
    unfold DavisonEq at he
    have h23 : (2 : ℤ) ^ k < 3 ^ k := pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
    simp only [add_zero, pow_zero, sub_self] at he
    rcases mul_eq_zero.mp he with h0 | h0
    · linarith
    · exact h0
  · rcases lt_trichotomy h 0 with hneg | h0 | hpos
    · right; right
      obtain ⟨hE, hle⟩ := neg_le hk hl (by omega) he
      rcases Nat.lt_or_ge k 3 with hk3 | hk3
      · -- `k ∈ {1, 2}`
        have h2l : (2 : ℤ) ^ (k + 2) ≤ 2 ^ (k + l) ∨ l = 1 := by
          rcases Nat.lt_or_ge l 2 with hl2 | hl2
          · right; omega
          · left; exact pow_le_pow_right₀ (by norm_num) (by omega)
        interval_cases k
        · -- `k = 1`: `3 − 2^(1+l) > 0` is impossible
          have : (2 : ℤ) ^ 2 ≤ 2 ^ (1 + l) := pow_le_pow_right₀ (by norm_num) (by omega)
          norm_num at hE this
          linarith
        · -- `k = 2`: `l = 1`, `h = −1`
          rcases h2l with h2l | rfl
          · norm_num at hE h2l
            linarith
          · unfold DavisonEq at he
            norm_num at he
            exact ⟨rfl, rfl, by linarith⟩
      · rcases Nat.lt_or_ge 20000 k with hbig | hsmall
        · have := rhin_k_le_thm hR k l h hk hl (by omega) he
          omega
        · obtain ⟨h1, h2⟩ := neg_nat hE hle
          exact (neg_exclude hk (posOK_of_le (by omega) hsmall) (negOK_of_le hk3 hsmall) h1 h2).elim
    · subst h0
      unfold DavisonEq at he
      have : (2 : ℤ) ≤ 2 ^ l := two_le_two_pow hl
      simp at he
      linarith
    · right; left
      exact steiner_thm hR k l h hk hl hpos he

/-! ## Circuits -/

/-- From a circuit-cycle on the positive integers: `h ≥ 1` and `l ≥ 1`. -/
theorem circuit_pos {n : ℤ} {k l : ℕ} {h : ℤ} (hn : 0 < n) (hk : 1 ≤ k) (hh : n + 1 = 2 ^ k * h)
    (he : DavisonEq k l h) : 1 ≤ h ∧ 1 ≤ l := by
  have h2k : (0 : ℤ) < 2 ^ k := by positivity
  have hpos : 0 < h := by
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith
  refine ⟨hpos, ?_⟩
  by_contra hl
  obtain rfl : l = 0 := by omega
  unfold DavisonEq at he
  have h23 : (2 : ℤ) ^ k < 3 ^ k := pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
  simp only [add_zero, pow_zero, sub_self] at he
  rcases mul_eq_zero.mp he with h0 | h0
  · linarith
  · omega

theorem steiner_cycle_thm : steiner_cycle := by
  intro hR n k l hn hk hc
  obtain ⟨h, hh, he⟩ := (circuit_iff_thm n k l hk).mp hc
  obtain ⟨h1, hl⟩ := circuit_pos hn hk hh he
  obtain ⟨rfl, rfl, rfl⟩ := steiner_thm hR k l h hk hl h1 he
  refine ⟨by norm_num at hh; linarith, rfl, rfl⟩

theorem steiner_cycle_small_thm : steiner_cycle_small := by
  intro n k l hn hk hk2 hc
  obtain ⟨h, hh, he⟩ := (circuit_iff_thm n k l hk).mp hc
  obtain ⟨h1, hl⟩ := circuit_pos hn hk hh he
  obtain ⟨rfl, rfl, rfl⟩ := steiner_small_thm k l h hk hk2 hl h1 he
  refine ⟨by norm_num at hh; linarith, rfl, rfl⟩

theorem steiner_cycle_int_thm : steiner_cycle_int := by
  intro hR n k l hk hc
  obtain ⟨h, hh, he⟩ := (circuit_iff_thm n k l hk).mp hc
  rcases steiner_int_thm hR k l h hk he with ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · left; exact ⟨by linarith, rfl⟩
  · right; left; exact ⟨by norm_num at hh; linarith, rfl, rfl⟩
  · right; right; exact ⟨by norm_num at hh; linarith, rfl, rfl⟩

theorem circuit_large_thm : circuit_large := by
  intro n k l hn hk hc hn1
  rcases Nat.lt_or_ge 20000 k with hbig | hsmall
  · obtain ⟨h, hh, he⟩ := (circuit_iff_thm n k l hk).mp hc
    obtain ⟨h1, -⟩ := circuit_pos hn hk hh he
    have hpow : (2 : ℤ) ^ 20001 ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
    have h2k : (0 : ℤ) < 2 ^ k := by positivity
    have : (2 : ℤ) ^ k ≤ 2 ^ k * h := le_mul_of_one_le_right h2k.le h1
    generalize (2 : ℤ) ^ 20001 = B at hpow ⊢
    linarith
  · exact absurd (steiner_cycle_small_thm n k l hn hk hsmall hc).1 hn1

/-! ## T★ for the words `1^k 0^l` -/

theorem count_oneBlock (k l : ℕ) : (oneBlock k l).count true = k := by
  simp [oneBlock, List.count_replicate]

theorem length_oneBlock (k l : ℕ) : (oneBlock k l).length = k + l := by
  simp [oneBlock]

theorem C_zeros (l : ℕ) : C (List.replicate l false) = 0 := by
  induction l with
  | zero => rfl
  | succ l ih => simp [List.replicate_succ, C, ih]

theorem C_oneBlock (k l : ℕ) : (C (oneBlock k l) : ℤ) = 3 ^ k - 2 ^ k := by
  induction k with
  | zero => simp [oneBlock, C_zeros]
  | succ k ih =>
    have hw : oneBlock (k + 1) l = true :: oneBlock k l := by
      simp [oneBlock, List.replicate_succ]
    rw [hw, C, count_oneBlock]
    push_cast
    rw [ih]
    simp only [ite_true]
    ring

theorem d_oneBlock (k l : ℕ) : d (oneBlock k l) = 2 ^ (k + l) - 3 ^ k := by
  rw [d, length_oneBlock, count_oneBlock]

theorem tstar_circuit_thm : tstar_circuit := by
  intro hR k l hd htrue hdvd
  rw [d_oneBlock] at hd hdvd
  rw [C_oneBlock] at hdvd
  have hk : 1 ≤ k := by
    by_contra hk0
    obtain rfl : k = 0 := by omega
    simp [oneBlock] at htrue
  have hl : 1 ≤ l := by
    by_contra hl0
    obtain rfl : l = 0 := by omega
    have : (2 : ℤ) ^ k < 3 ^ k := pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
    simp at hd
    linarith
  obtain ⟨x, hx⟩ := hdvd
  -- `D` is odd, hence coprime to `2^k`
  have hodd : Odd ((2 : ℤ) ^ (k + l) - 3 ^ k) := by
    have h3 : Odd ((3 : ℤ) ^ k) := Odd.pow (by decide)
    have h2 : Even ((2 : ℤ) ^ (k + l)) := (even_two).pow_of_ne_zero (by omega)
    exact h2.sub_odd h3
  have hcop : IsCoprime ((2 : ℤ) ^ k) ((2 : ℤ) ^ (k + l) - 3 ^ k) := by
    obtain ⟨m, hm⟩ := hodd
    have h2 : IsCoprime (2 : ℤ) ((2 : ℤ) ^ (k + l) - 3 ^ k) := ⟨-m, 1, by rw [hm]; ring⟩
    exact h2.pow_left
  -- `2^k (2^l − 1) = D (1 + x)`, so `2^k ∣ 1 + x`
  have hkey : (2 : ℤ) ^ k * (2 ^ l - 1) = ((2 : ℤ) ^ (k + l) - 3 ^ k) * (1 + x) := by
    rw [pow_add] at hx ⊢
    linear_combination hx
  obtain ⟨h, hh⟩ := hcop.dvd_of_dvd_mul_left ⟨2 ^ l - 1, hkey.symm⟩
  have heq : DavisonEq k l h := by
    unfold DavisonEq
    have h2k : (2 : ℤ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    apply mul_left_cancel₀ h2k
    rw [hkey, hh]
    ring
  have h1 : 1 ≤ h := by
    have h2l : (2 : ℤ) ≤ 2 ^ l := two_le_two_pow hl
    unfold DavisonEq at heq
    by_contra hneg
    rw [not_le] at hneg
    nlinarith
  obtain ⟨rfl, rfl, -⟩ := steiner_thm hR k l h hk hl h1 heq
  exact ⟨1, 0, rfl⟩

end Steiner
