import Mathlib
import Steiner.Steiner_Enonces

/-!
# Steiner 1978 · proofs (3): the inequality, the convergent, Rhin's bound

* `ineq4_thm`: `0 < Λ < 1/(2^k h − 1) ≤ 1/(2^k − 1)` for a positive solution;
* `convergent4_thm`: for `k ≥ 4` the inequality makes `(k+l)/k` a convergent of `log₂ 3` (Legendre's theorem,
  `Real.exists_rat_eq_convergent` of Mathlib);
* `rhin_k_le_thm`: under `H_Rhin`, `k ≤ 108` (both signs of `h`).
-/

namespace Steiner

/-! ## Davison's equation, in integers -/

/-- A positive solution: `D = 2^(k+l) − 3^k > 0` and `D·(2^k h − 1) = 3^k − 2^k`. -/
theorem pos_facts {k l : ℕ} {h : ℤ} (hl : 1 ≤ l) (hh : 1 ≤ h) (he : DavisonEq k l h) :
    0 < (2 : ℤ) ^ (k + l) - 3 ^ k ∧ ((2 : ℤ) ^ (k + l) - 3 ^ k) * (2 ^ k * h - 1) = 3 ^ k - 2 ^ k := by
  unfold DavisonEq at he
  have h2l : (2 : ℤ) ≤ 2 ^ l := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ l := pow_le_pow_right₀ (by norm_num) hl
  refine ⟨?_, ?_⟩
  · by_contra hD
    rw [not_lt] at hD
    nlinarith
  · rw [pow_add] at he ⊢
    linear_combination (2 : ℤ) ^ k * he

/-- A negative solution: `E = 3^k − 2^(k+l) > 0` and `E·(2^k (−h) + 1) = 3^k − 2^k`. -/
theorem neg_facts {k l : ℕ} {h : ℤ} (hl : 1 ≤ l) (hh : h ≤ -1) (he : DavisonEq k l h) :
    0 < (3 : ℤ) ^ k - 2 ^ (k + l) ∧ ((3 : ℤ) ^ k - 2 ^ (k + l)) * (2 ^ k * (-h) + 1) = 3 ^ k - 2 ^ k := by
  unfold DavisonEq at he
  have h2l : (2 : ℤ) ≤ 2 ^ l := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ l := pow_le_pow_right₀ (by norm_num) hl
  refine ⟨?_, ?_⟩
  · by_contra hE
    rw [not_lt] at hE
    nlinarith
  · rw [pow_add] at he ⊢
    linear_combination (2 : ℤ) ^ k * he

/-! ## The linear form -/

theorem Lam_eq (k l : ℕ) : Lam k l = Real.log ((2 : ℝ) ^ (k + l) / 3 ^ k) := by
  unfold Lam
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]

/-- If `3^k < 2^L`: `0 < Λ ≤ (2^L − 3^k)/3^k`. -/
theorem Lam_pos_le {k l : ℕ} (h : (3 : ℝ) ^ k < 2 ^ (k + l)) :
    0 < Lam k l ∧ Lam k l ≤ ((2 : ℝ) ^ (k + l) - 3 ^ k) / 3 ^ k := by
  have h3 : (0 : ℝ) < 3 ^ k := by positivity
  rw [Lam_eq]
  refine ⟨Real.log_pos ((one_lt_div h3).mpr h), ?_⟩
  calc Real.log ((2 : ℝ) ^ (k + l) / 3 ^ k) ≤ (2 : ℝ) ^ (k + l) / 3 ^ k - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
    _ = ((2 : ℝ) ^ (k + l) - 3 ^ k) / 3 ^ k := by field_simp

/-- If `2^L < 3^k`: `Λ < 0` and `−Λ ≤ (3^k − 2^L)/2^L`. -/
theorem Lam_neg_le {k l : ℕ} (h : (2 : ℝ) ^ (k + l) < 3 ^ k) :
    Lam k l < 0 ∧ -Lam k l ≤ ((3 : ℝ) ^ k - 2 ^ (k + l)) / 2 ^ (k + l) := by
  have h2 : (0 : ℝ) < 2 ^ (k + l) := by positivity
  have hneg : -Lam k l = Real.log ((3 : ℝ) ^ k / 2 ^ (k + l)) := by
    unfold Lam
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    ring
  have hpos : 0 < Real.log ((3 : ℝ) ^ k / 2 ^ (k + l)) := Real.log_pos ((one_lt_div h2).mpr h)
  refine ⟨by linarith, ?_⟩
  rw [hneg]
  calc Real.log ((3 : ℝ) ^ k / 2 ^ (k + l)) ≤ (3 : ℝ) ^ k / 2 ^ (k + l) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
    _ = ((3 : ℝ) ^ k - 2 ^ (k + l)) / 2 ^ (k + l) := by field_simp

/-! ## `ineq4` -/

theorem ineq4_thm : ineq4 := by
  intro k l h hk hl hh he
  obtain ⟨hD, hDn⟩ := pos_facts hl hh he
  have hDr : (0 : ℝ) < (2 : ℝ) ^ (k + l) - 3 ^ k := by exact_mod_cast hD
  have hDnr : ((2 : ℝ) ^ (k + l) - 3 ^ k) * (2 ^ k * h - 1) = 3 ^ k - 2 ^ k := by exact_mod_cast hDn
  have h2k : (2 : ℝ) ≤ 2 ^ k := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hhr : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hn1 : (2 : ℝ) ^ k - 1 ≤ 2 ^ k * h - 1 := by nlinarith
  have hn0 : (0 : ℝ) < 2 ^ k - 1 := by linarith
  obtain ⟨hpos, hle⟩ := Lam_pos_le (k := k) (l := l) (by linarith)
  refine ⟨hpos, ?_, one_div_le_one_div_of_le hn0 hn1⟩
  calc Lam k l ≤ ((2 : ℝ) ^ (k + l) - 3 ^ k) / 3 ^ k := hle
    _ < 1 / ((2 : ℝ) ^ k * h - 1) := by
      rw [div_lt_div_iff₀ (by positivity) (by linarith)]
      have : (0 : ℝ) < 2 ^ k := by positivity
      nlinarith

/-! ## `convergent4` -/

theorem three_mul_add_one_le_two_pow (k : ℕ) (hk : 4 ≤ k) : 3 * k + 1 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ]; omega

theorem convergent4_thm : convergent4 := by
  intro k l hk hpos hlt
  apply Real.exists_rat_eq_convergent
  set q : ℚ := ((k + l : ℕ) : ℚ) / k with hq
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2 : (0 : ℝ) < Real.log 2 := by linarith
  -- `log₂ 3 − q = −Λ/(k log 2)`
  have hdiff : Real.logb 2 3 - (q : ℝ) = -Lam k l / (k * Real.log 2) := by
    rw [hq, Real.logb]
    push_cast
    unfold Lam
    push_cast
    field_simp
    ring
  -- `q.den ≤ k`
  have hden : (q.den : ℝ) ≤ k := by
    have hq' : q = Rat.divInt ((k + l : ℕ) : ℤ) (k : ℤ) := by
      rw [Rat.divInt_eq_div, hq]; push_cast; rfl
    have hdvd : ((q.den : ℕ) : ℤ) ∣ (k : ℤ) := by rw [hq']; exact Rat.den_dvd _ _
    have : q.den ≤ k := by
      have := Int.le_of_dvd (by exact_mod_cast (by omega : 0 < k)) hdvd
      exact_mod_cast this
    exact_mod_cast this
  have hden0 : (0 : ℝ) < q.den := by exact_mod_cast q.pos
  -- `2k Λ < log 2`
  have h3k : (3 * k + 1 : ℝ) ≤ 2 ^ k := by exact_mod_cast three_mul_add_one_le_two_pow k hk
  have hkey : 2 * k * Lam k l < Real.log 2 := by
    have hn0 : (0 : ℝ) < 2 ^ k - 1 := by linarith
    have h1 : 2 * k * Lam k l < 2 * k * (1 / ((2 : ℝ) ^ k - 1)) := mul_lt_mul_of_pos_left hlt (by positivity)
    have h2 : 2 * k * (1 / ((2 : ℝ) ^ k - 1)) ≤ Real.log 2 := by
      rw [mul_one_div, div_le_iff₀ hn0]
      nlinarith
    linarith
  rw [hdiff, abs_div, abs_neg, abs_of_pos hpos, abs_of_pos (by positivity)]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have hdk : (q.den : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := pow_le_pow_left₀ hden0.le hden 2
  nlinarith

/-! ## Rhin's bound -/

/-- `H_Rhin` applied to `u₁ = k + l`, `u₂ = −k`: `(k+l)^(−13.3) ≤ |Λ|`. -/
theorem rhin_apply (hR : H_Rhin) {k l : ℕ} (hl : 1 ≤ l) (hk : 1 ≤ k) :
    1 / ((k + l : ℕ) : ℝ) ^ 14 ≤ |Lam k l| := by
  have hmax : max |((k + l : ℕ) : ℤ)| |(-(k : ℤ))| = ((k + l : ℕ) : ℤ) := by
    rw [abs_neg, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    exact max_eq_left (by push_cast; omega)
  have h := hR ((k + l : ℕ) : ℤ) (-(k : ℤ)) (by rw [hmax]; push_cast; omega)
  rw [hmax] at h
  have hL1 : (1 : ℝ) ≤ ((k + l : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + l)
  have h14 : ((k + l : ℕ) : ℝ) ^ (-(14 : ℝ)) ≤ ((k + l : ℕ) : ℝ) ^ (-(133 / 10 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hrw : ((k + l : ℕ) : ℝ) ^ (-(14 : ℝ)) = 1 / ((k + l : ℕ) : ℝ) ^ 14 := by
    rw [Real.rpow_neg (by positivity), one_div]
    norm_cast
  have hLam : |(((k + l : ℕ) : ℤ) : ℝ) * Real.log 2 + ((-(k : ℤ) : ℤ) : ℝ) * Real.log 3| = |Lam k l| := by
    unfold Lam; push_cast; ring_nf
  rw [hLam, Int.cast_natCast] at h
  rw [← hrw]
  exact h14.trans h

/-- The positive side under `H_Rhin`: `2^k − 1 < (k+l)^14`. -/
theorem rhin_pos (hR : H_Rhin) {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l)
    (h1 : (3 : ℝ) ^ k < 2 ^ (k + l))
    (h2 : ((2 : ℝ) ^ (k + l) - 3 ^ k) * (2 ^ k - 1) ≤ 3 ^ k - 2 ^ k) :
    (2 : ℝ) ^ k - 1 < ((k + l : ℕ) : ℝ) ^ 14 := by
  obtain ⟨hpos, hle⟩ := Lam_pos_le h1
  have hR' := rhin_apply hR hl hk
  rw [abs_of_pos hpos] at hR'
  have hD : (0 : ℝ) < 2 ^ (k + l) - 3 ^ k := by linarith
  have hL : (0 : ℝ) < ((k + l : ℕ) : ℝ) ^ 14 := by positivity
  have h3 : (0 : ℝ) < 3 ^ k := by positivity
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  -- `3^k ≤ D·L^14`
  have hA : (3 : ℝ) ^ k ≤ ((2 : ℝ) ^ (k + l) - 3 ^ k) * ((k + l : ℕ) : ℝ) ^ 14 := by
    have := hR'.trans hle
    rw [div_le_div_iff₀ hL h3] at this
    linarith
  -- `D (2^k − 1) < D L^14`
  have hB : ((2 : ℝ) ^ (k + l) - 3 ^ k) * (2 ^ k - 1) < ((2 : ℝ) ^ (k + l) - 3 ^ k) * ((k + l : ℕ) : ℝ) ^ 14 := by
    linarith
  exact lt_of_mul_lt_mul_left hB hD.le

/-- The negative side under `H_Rhin`: `2^k < (k+l)^14`. -/
theorem rhin_neg (hR : H_Rhin) {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l)
    (h1 : (2 : ℝ) ^ (k + l) < 3 ^ k)
    (h2 : ((3 : ℝ) ^ k - 2 ^ (k + l)) * (2 ^ k + 1) ≤ 3 ^ k - 2 ^ k) :
    (2 : ℝ) ^ k < ((k + l : ℕ) : ℝ) ^ 14 := by
  obtain ⟨hneg, hle⟩ := Lam_neg_le h1
  have hR' := rhin_apply hR hl hk
  rw [abs_of_neg hneg] at hR'
  have hE : (0 : ℝ) < 3 ^ k - 2 ^ (k + l) := by linarith
  have hL : (0 : ℝ) < ((k + l : ℕ) : ℝ) ^ 14 := by positivity
  have h2L : (0 : ℝ) < 2 ^ (k + l) := by positivity
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  -- `2^L ≤ E·L^14`
  have hA : (2 : ℝ) ^ (k + l) ≤ ((3 : ℝ) ^ k - 2 ^ (k + l)) * ((k + l : ℕ) : ℝ) ^ 14 := by
    have := hR'.trans hle
    rw [div_le_div_iff₀ hL h2L] at this
    linarith
  -- `E (2^k + 1) < E (L^14 + 1)`
  have hB : ((3 : ℝ) ^ k - 2 ^ (k + l)) * (2 ^ k + 1) <
      ((3 : ℝ) ^ k - 2 ^ (k + l)) * (((k + l : ℕ) : ℝ) ^ 14 + 1) := by
    nlinarith
  have := lt_of_mul_lt_mul_left hB hE.le
  linarith

/-- `(2k)^14 + 1 < 2^k` for `k ≥ 109`. -/
theorem big (k : ℕ) (hk : 109 ≤ k) : (2 * k) ^ 14 + 1 < 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h28 : (28 * (k + 1)) ^ 14 ≤ (29 * k) ^ 14 := Nat.pow_le_pow_left (by omega) 14
    rw [mul_pow, mul_pow] at h28
    have h29 : (29 : ℕ) ^ 14 ≤ 2 * 28 ^ 14 := by norm_num
    have hk1 : (k + 1) ^ 14 ≤ 2 * k ^ 14 := by
      have : 28 ^ 14 * (k + 1) ^ 14 ≤ 28 ^ 14 * (2 * k ^ 14) := by
        calc 28 ^ 14 * (k + 1) ^ 14 ≤ 29 ^ 14 * k ^ 14 := h28
          _ ≤ 2 * 28 ^ 14 * k ^ 14 := Nat.mul_le_mul_right _ h29
          _ = 28 ^ 14 * (2 * k ^ 14) := by ring
      exact Nat.le_of_mul_le_mul_left this (by positivity)
    have : (2 * (k + 1)) ^ 14 ≤ 2 * (2 * k) ^ 14 := by
      rw [mul_pow, mul_pow]
      calc 2 ^ 14 * (k + 1) ^ 14 ≤ 2 ^ 14 * (2 * k ^ 14) := Nat.mul_le_mul_left _ hk1
        _ = 2 * (2 ^ 14 * k ^ 14) := by ring
    rw [pow_succ (2 : ℕ) k]
    omega

theorem rhin_k_le_thm : rhin_k_le := by
  intro hR k l h hk hl hh0 he
  by_contra hk108
  rw [not_le] at hk108
  have hbig := big k hk108
  rcases lt_or_gt_of_ne hh0 with hneg | hpos
  · obtain ⟨hE, hEn⟩ := neg_facts hl (by omega) he
    -- `E (2^k + 1) ≤ 3^k − 2^k`
    have hEle : ((3 : ℤ) ^ k - 2 ^ (k + l)) * (2 ^ k + 1) ≤ 3 ^ k - 2 ^ k := by
      rw [← hEn]
      apply mul_le_mul_of_nonneg_left _ hE.le
      have : (1 : ℤ) ≤ -h := by omega
      nlinarith [pow_pos (by norm_num : (0 : ℤ) < 2) k]
    have h1 : (2 : ℝ) ^ (k + l) < 3 ^ k := by
      have : (2 : ℤ) ^ (k + l) < 3 ^ k := by linarith
      exact_mod_cast this
    have h2 : ((3 : ℝ) ^ k - 2 ^ (k + l)) * (2 ^ k + 1) ≤ 3 ^ k - 2 ^ k := by exact_mod_cast hEle
    have hr := rhin_neg hR hk hl h1 h2
    -- `k + l < 2k`
    have hL : k + l ≤ 2 * k := by
      have : 2 ^ (k + l) < 2 ^ (2 * k) := by
        have h' : (2 : ℕ) ^ (k + l) < 3 ^ k := by exact_mod_cast h1
        calc 2 ^ (k + l) < 3 ^ k := h'
          _ ≤ 4 ^ k := Nat.pow_le_pow_left (by norm_num) k
          _ = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
      exact ((Nat.pow_lt_pow_iff_right (by norm_num)).mp this).le
    have hLr : ((k + l : ℕ) : ℝ) ^ 14 ≤ ((2 * k : ℕ) : ℝ) ^ 14 :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast hL) 14
    have : (2 : ℝ) ^ k < ((2 * k : ℕ) : ℝ) ^ 14 := lt_of_lt_of_le hr hLr
    have : 2 ^ k < (2 * k) ^ 14 := by exact_mod_cast this
    omega
  · obtain ⟨hD, hDn⟩ := pos_facts hl (by omega) he
    have hDle : ((2 : ℤ) ^ (k + l) - 3 ^ k) * (2 ^ k - 1) ≤ 3 ^ k - 2 ^ k := by
      rw [← hDn]
      apply mul_le_mul_of_nonneg_left _ hD.le
      have : (1 : ℤ) ≤ h := by omega
      nlinarith [pow_pos (by norm_num : (0 : ℤ) < 2) k]
    have h1 : (3 : ℝ) ^ k < 2 ^ (k + l) := by
      have : (3 : ℤ) ^ k < 2 ^ (k + l) := by linarith
      exact_mod_cast this
    have h2 : ((2 : ℝ) ^ (k + l) - 3 ^ k) * (2 ^ k - 1) ≤ 3 ^ k - 2 ^ k := by exact_mod_cast hDle
    have hr := rhin_pos hR hk hl h1 h2
    -- `k + l ≤ 2k`: `2^L ≤ 2·3^k − 2^k < 2^(2k+1)`
    have hL : k + l ≤ 2 * k := by
      have h2k1 : (1 : ℤ) ≤ 2 ^ k - 1 := by
        have : (2 : ℤ) ≤ 2 ^ k := by
          calc (2 : ℤ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
        linarith
      have hDle' : (2 : ℤ) ^ (k + l) - 3 ^ k ≤ 3 ^ k - 2 ^ k := by nlinarith
      have h43 : (3 : ℤ) ^ k ≤ 4 ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
      have : (2 : ℤ) ^ (k + l) < 2 ^ (2 * k + 1) := by
        rw [pow_succ, pow_mul]
        norm_num
        nlinarith [pow_pos (by norm_num : (0 : ℤ) < 2) k]
      have : (2 : ℕ) ^ (k + l) < 2 ^ (2 * k + 1) := by exact_mod_cast this
      have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
      omega
    have hLr : ((k + l : ℕ) : ℝ) ^ 14 ≤ ((2 * k : ℕ) : ℝ) ^ 14 :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast hL) 14
    have : (2 : ℝ) ^ k - 1 < ((2 * k : ℕ) : ℝ) ^ 14 := lt_of_lt_of_le hr hLr
    have : (2 : ℝ) ^ k < ((2 * k : ℕ) : ℝ) ^ 14 + 1 := by linarith
    have : 2 ^ k < (2 * k) ^ 14 + 1 := by exact_mod_cast this
    omega

end Steiner
