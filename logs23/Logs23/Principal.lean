import Mathlib
import Labo.Blueprint
import Steiner.Steiner_Enonces
import Steiner.Dynamique
import Steiner.Fini
import Steiner.Analyse
import Steiner.Principal
import Logs23.Logs23_Enonces
import Logs23.Pont

/-!
# Logs23 · proofs (3): Steiner's theorem from the lower bound for `Λ`

In `../steiner1978/`, `H_Rhin` is used through a single lemma, `rhin_k_le` ("`k ≤ 108`"). Here `k_le_of_lam` replaces it:
a lower bound `1/(2^k − 1) ≤ |Λ|` for the `k > 20000` of a class `B` gives `k ≤ 20000` for every solution with
`l ≥ 1`, `h ≠ 0` and `B k`, of either sign. The proofs below are those of `../steiner1978/Steiner/Principal.lean`
with `rhin_k_le_thm` replaced by `k_le_of_lam`; they are stated for an arbitrary class `B`, then used with
`B k := k < qBr'` (the bridge, no hypothesis) and with `B k := True` (`reduction`).
-/

namespace Logs23

open Steiner LaboBP

/-- A solution with `k ≥ 1`, `l ≥ 1`, `h ≠ 0` has `|Λ| < 1/(2^k − 1)`, whatever the sign of `h`. -/
theorem lam_small {k l : ℕ} {h : ℤ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hh : h ≠ 0) (he : DavisonEq k l h) :
    |Lam k l| < 1 / ((2 : ℝ) ^ k - 1) := by
  have h2k : (2 : ℝ) ≤ 2 ^ k := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  rcases lt_or_gt_of_ne hh with hneg | hpos
  · obtain ⟨hE, hEn⟩ := neg_facts hl (by omega) he
    have hEr : (0 : ℝ) < (3 : ℝ) ^ k - 2 ^ (k + l) := by exact_mod_cast hE
    have hEnr : ((3 : ℝ) ^ k - 2 ^ (k + l)) * (2 ^ k * (-(h : ℝ)) + 1) = 3 ^ k - 2 ^ k := by
      exact_mod_cast hEn
    have hmh : (1 : ℝ) ≤ -(h : ℝ) := by
      have : (1 : ℤ) ≤ -h := by omega
      exact_mod_cast this
    -- `E (2^k + 1) ≤ 3^k − 2^k`
    have hEle : ((3 : ℝ) ^ k - 2 ^ (k + l)) * (2 ^ k + 1) ≤ 3 ^ k - 2 ^ k := by
      rw [← hEnr]
      apply mul_le_mul_of_nonneg_left _ hEr.le
      nlinarith
    obtain ⟨hlt, hle⟩ := Lam_neg_le (k := k) (l := l) (by linarith)
    have h2L : (0 : ℝ) < 2 ^ (k + l) := by positivity
    have h2k1 : (0 : ℝ) < 2 ^ k - 1 := by linarith
    -- `E / 2^L < 1/(2^k − 1)`, i.e. `E (2^k − 1) < 2^L = 3^k − E`
    have hfin : ((3 : ℝ) ^ k - 2 ^ (k + l)) / 2 ^ (k + l) < 1 / ((2 : ℝ) ^ k - 1) := by
      rw [div_lt_div_iff₀ h2L h2k1]
      nlinarith
    rw [abs_of_neg hlt]
    linarith
  · obtain ⟨hpos', hlt, -⟩ := ineq4_thm k l h hk hl (by omega) he
    have hle := (ineq4_thm k l h hk hl (by omega) he).2.2
    rw [abs_of_pos hpos']
    exact lt_of_lt_of_le hlt hle

/-- The lower bound for `Λ` on a class `B` forces `k ≤ 20000` for the solutions with `l ≥ 1`, `h ≠ 0`, `B k`. -/
theorem k_le_of_lam (B : ℕ → Prop) (hL : ∀ k l : ℕ, 20000 < k → B k → 1 / ((2 : ℝ) ^ k - 1) ≤ |Lam k l|)
    {k l : ℕ} {h : ℤ} (hk : 1 ≤ k) (hB : B k) (hl : 1 ≤ l) (hh : h ≠ 0) (he : DavisonEq k l h) :
    k ≤ 20000 := by
  by_contra hbig
  rw [not_le] at hbig
  have := hL k l hbig hB
  have := lam_small hk hl hh he
  linarith

theorem steiner_gen (B : ℕ → Prop) (hL : ∀ k l : ℕ, 20000 < k → B k → 1 / ((2 : ℝ) ^ k - 1) ≤ |Lam k l|) :
    ∀ (k l : ℕ) (h : ℤ), 1 ≤ k → B k → 1 ≤ l → 1 ≤ h → DavisonEq k l h → k = 1 ∧ l = 1 ∧ h = 1 := by
  intro k l h hk hB hl hh he
  exact steiner_small_thm k l h hk (k_le_of_lam B hL hk hB hl (by omega) he) hl hh he

theorem steiner_int_gen (B : ℕ → Prop)
    (hL : ∀ k l : ℕ, 20000 < k → B k → 1 / ((2 : ℝ) ^ k - 1) ≤ |Lam k l|) :
    ∀ (k l : ℕ) (h : ℤ), 1 ≤ k → B k → DavisonEq k l h →
      (l = 0 ∧ h = 0) ∨ (k = 1 ∧ l = 1 ∧ h = 1) ∨ (k = 2 ∧ l = 1 ∧ h = -1) := by
  intro k l h hk hB he
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
      · have hsmall := k_le_of_lam B hL hk hB hl (by omega) he
        obtain ⟨h1, h2⟩ := neg_nat hE hle
        exact (neg_exclude hk (posOK_of_le (by omega) hsmall) (negOK_of_le hk3 hsmall) h1 h2).elim
    · subst h0
      unfold DavisonEq at he
      have : (2 : ℤ) ≤ 2 ^ l := two_le_two_pow hl
      simp at he
      linarith
    · right; left
      exact steiner_gen B hL k l h hk hB hl hpos he

theorem steiner_cycle_gen (B : ℕ → Prop)
    (hL : ∀ k l : ℕ, 20000 < k → B k → 1 / ((2 : ℝ) ^ k - 1) ≤ |Lam k l|) :
    ∀ (n : ℤ) (k l : ℕ), 0 < n → 1 ≤ k → B k → CircuitCycle n k l → n = 1 ∧ k = 1 ∧ l = 1 := by
  intro n k l hn hk hB hc
  obtain ⟨h, hh, he⟩ := (circuit_iff_thm n k l hk).mp hc
  obtain ⟨h1, hl⟩ := circuit_pos hn hk hh he
  obtain ⟨rfl, rfl, rfl⟩ := steiner_gen B hL k l h hk hB hl h1 he
  refine ⟨by norm_num at hh; linarith, rfl, rfl⟩

theorem steiner_cycle_int_gen (B : ℕ → Prop)
    (hL : ∀ k l : ℕ, 20000 < k → B k → 1 / ((2 : ℝ) ^ k - 1) ≤ |Lam k l|) :
    ∀ (n : ℤ) (k l : ℕ), 1 ≤ k → B k → CircuitCycle n k l →
      (n = -1 ∧ l = 0) ∨ (n = 1 ∧ k = 1 ∧ l = 1) ∨ (n = -5 ∧ k = 2 ∧ l = 1) := by
  intro n k l hk hB hc
  obtain ⟨h, hh, he⟩ := (circuit_iff_thm n k l hk).mp hc
  rcases steiner_int_gen B hL k l h hk hB he with ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · left; exact ⟨by linarith, rfl⟩
  · right; left; exact ⟨by norm_num at hh; linarith, rfl, rfl⟩
  · right; right; exact ⟨by norm_num at hh; linarith, rfl, rfl⟩

theorem tstar_circuit_gen (B : ℕ → Prop)
    (hL : ∀ k l : ℕ, 20000 < k → B k → 1 / ((2 : ℝ) ^ k - 1) ≤ |Lam k l|) :
    ∀ k l : ℕ, B k → 0 < d (oneBlock k l) → true ∈ oneBlock k l →
      d (oneBlock k l) ∣ (C (oneBlock k l) : ℤ) → TrivialWord (oneBlock k l) := by
  intro k l hB hd htrue hdvd
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
  obtain ⟨rfl, rfl, -⟩ := steiner_gen B hL k l h hk hB hl h1 heq
  exact ⟨1, 0, rfl⟩

/-! ## The bridge: no hypothesis, `k < qBr'` -/

theorem steiner_bridge_thm : steiner_bridge := by
  intro k l h hk hk' hl hh he
  exact steiner_gen (· < qBr') (fun k l hk hk' => lam_lower_bridge_thm k l hk hk') k l h hk hk' hl hh he

theorem steiner_cycle_bridge_thm : steiner_cycle_bridge := by
  intro n k l hn hk hk' hc
  exact steiner_cycle_gen (· < qBr') (fun k l hk hk' => lam_lower_bridge_thm k l hk hk') n k l hn hk hk' hc

/-! ## The reduction -/

theorem reduction_thm : reduction := by
  intro hL
  have hL' : ∀ k l : ℕ, 20000 < k → True → 1 / ((2 : ℝ) ^ k - 1) ≤ |Lam k l| :=
    fun k l hk _ => hL k l hk
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k l h hk hl hh he
    exact steiner_gen (fun _ => True) hL' k l h hk trivial hl hh he
  · intro k l h hk he
    exact steiner_int_gen (fun _ => True) hL' k l h hk trivial he
  · intro n k l hn hk hc
    exact steiner_cycle_gen (fun _ => True) hL' n k l hn hk trivial hc
  · intro n k l hk hc
    exact steiner_cycle_int_gen (fun _ => True) hL' n k l hk trivial hc
  · intro k l hd htrue hdvd
    exact tstar_circuit_gen (fun _ => True) hL' k l trivial hd htrue hdvd

end Logs23
