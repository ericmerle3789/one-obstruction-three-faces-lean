import Mathlib
import Labo.HH1997d_Pont_Enonces
import Labo.HH1997d_Preuves

/-!
# LABO-COLLATZ · HH1997d · formaliste (2026-10-19) — PROOFS of `Labo/HH1997d_Pont_Enonces.lean`

* `thm1_cond_gap`: Theorem 1 from the continued-fraction gap alone.  Route (shorter than through Lemma 8):
  Eliahou's `2^l ≤ (3 + 1/m)^n` gives `l − nθ ≤ n·log₂(1 + 1/(3m)) ≤ n/(3m log 2)`; if `n ≤ q_k` the gap gives
  `l − nθ > 1/S` (`S = q_k + q_{k+1}`); with `n ≤ 2m/S` this forces `log 2 < 2/3`, false.  No size of `S` is needed.
* `thm3_line_of`, `thm3_of`: the displayed line of the proof of Theorem 3 from `prop2` and `lemma6` (batch c), using
  `M/(2^l − 3^n) = (M/3^n)/(x − 1)` and `3x^{1/n} = 2^{l/n}` for `x = 2^l/3^n`.
-/

namespace LaboHH

open LaboBP

/-! ## Theorem 1 from the gap alone -/

lemma thm1_analytic2 (m : ℝ) (n l : ℕ) (S : ℝ) (hm : 1 < m) (hSpos : 0 < S)
    (hgap : 1 / S < (l : ℝ) - n * theta) (hE : (2 : ℝ) ^ l ≤ (3 + 1 / m) ^ n)
    (hnS : (n : ℝ) * S ≤ 2 * m) : False := by
  have hm0 : 0 < m := by linarith
  have L2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hL : 0 < Real.log 2 := by linarith
  have ht : 0 < 1 / (3 * m) := by positivity
  have hfac : (3 : ℝ) + 1 / m = 3 * (1 + 1 / (3 * m)) := by field_simp
  have hlog : (l : ℝ) ≤ n * (theta + Real.logb 2 (1 + 1 / (3 * m))) := by
    have := (Real.logb_le_logb (b := 2) one_lt_two (by positivity) (by positivity)).mpr hE
    rwa [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one, hfac,
      Real.logb_mul (by norm_num) (by positivity)] at this
  have hlog1 : Real.log (1 + 1 / (3 * m)) ≤ 1 / (3 * m) := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (3 * m) by positivity)
    linarith
  have hlb : Real.logb 2 (1 + 1 / (3 * m)) ≤ 1 / (3 * m) / Real.log 2 :=
    div_le_div_of_nonneg_right hlog1 hL.le
  have h1 : 1 / S < n * (1 / (3 * m) / Real.log 2) := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_le_mul_of_nonneg_left hlb hn0]
  rw [show (n : ℝ) * (1 / (3 * m) / Real.log 2) = n * (1 / (3 * m)) / Real.log 2 by ring,
    div_lt_div_iff₀ hSpos hL, one_mul] at h1
  have h2 : (n : ℝ) * (1 / (3 * m)) * S ≤ 2 / 3 := by
    calc (n : ℝ) * (1 / (3 * m)) * S = (n * S) * (1 / (3 * m)) := by ring
      _ ≤ (2 * m) * (1 / (3 * m)) := mul_le_mul_of_nonneg_right hnS ht.le
      _ = 2 / 3 := by field_simp
  linarith

lemma qCF_pos (k : ℕ) : 0 < qCF k := by
  have h := qCF_ge_fib k
  have : (1 : ℝ) ≤ Nat.fib (k + 1) := by exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos k)
  linarith

theorem thm1_cond_gap_thm : thm1_cond_gap := by
  intro hgap k hk l n s hS hnl m hm1 hm
  obtain ⟨hn2, hD, -⟩ := lemma8_facts l n s hS hnl m hm1 hm
  obtain ⟨hsl, hsn⟩ := hS
  have hs : s ≠ [] := by
    rintro rfl
    simp at hsn
    omega
  obtain ⟨-, -, horb, hper⟩ := lemma2_cycle_thm s hs
  obtain ⟨-, hE⟩ := eliahou_core _ m s hs (fun i hi => (horb i hi).1) hper (by linarith)
    (fun i => hm.2 ⟨i, rfl⟩)
  rw [hsl, hsn] at hE
  by_contra hcon
  obtain ⟨hnq, hn2m⟩ := le_min_iff.mp (not_lt.mp hcon)
  have hSpos : 0 < qCF k + qCF (k + 1) := add_pos (qCF_pos k) (qCF_pos (k + 1))
  have hg := hgap k hk (l : ℤ) (n : ℤ) (by exact_mod_cast (show 1 ≤ n by omega)) (by exact_mod_cast hnq)
  push_cast at hg
  have hD' : (3 : ℝ) ^ n < 2 ^ l := by exact_mod_cast hD
  have hθ : (n : ℝ) * theta < l := by
    have := Real.logb_lt_logb (b := 2) one_lt_two (by positivity) hD'
    rwa [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one] at this
  rw [abs_sub_comm, abs_of_pos (by linarith)] at hg
  have hE' : (2 : ℝ) ^ l ≤ (3 + 1 / (m : ℝ)) ^ n := by exact_mod_cast hE
  have hnS : (n : ℝ) * (qCF k + qCF (k + 1)) ≤ 2 * m := by
    rwa [le_div_iff₀ hSpos] at hn2m
  exact thm1_analytic2 m n l _ (by exact_mod_cast hm1) hSpos hg hE' hnS

theorem thm1_from_gap_all_thm : thm1_from_gap_all :=
  fun h => thm1_cond_gap_thm fun k hk => h k (by omega)

/-! ## Theorem 3 from Prop. 2 and Lemma 6 -/

theorem thm3_line_of_thm : thm3_line_of := by
  intro hP2 hL6 l hl
  obtain ⟨-, hP⟩ := hP2 l (by omega)
  have hn1 : 1 ≤ nOf l := nOf_pos_of_two_le (by omega)
  obtain ⟨h3, h2⟩ := nOf_spec_thm l (by omega)
  have h3r : (3 : ℝ) ^ nOf l < 2 ^ l := by exact_mod_cast h3
  have h2r : (2 : ℝ) ^ l < 3 ^ (nOf l + 1) := by exact_mod_cast h2
  have h3pos : (0 : ℝ) < 3 ^ nOf l := by positivity
  have hx1 : 1 < xP l := by
    unfold xP
    rw [lt_div_iff₀ h3pos]
    linarith
  have hx3 : xP l < 3 := by
    unfold xP
    rw [div_lt_iff₀ h3pos]
    rw [pow_succ] at h2r
    linarith
  have hf := hL6 (xP l) hx1 hx3 l hl
  have hn0 : (nOf l : ℝ) ≠ 0 := by exact_mod_cast (show nOf l ≠ 0 by omega)
  have hnpos : (0 : ℝ) < 1 / (nOf l : ℝ) := by
    have : (0 : ℝ) < nOf l := by exact_mod_cast (show 0 < nOf l by omega)
    positivity
  -- `3 x^{1/n} = 2^{l/n}`
  have hxroot : xP l ^ (1 / (nOf l : ℝ)) * 3 = (2 : ℝ) ^ ((l : ℝ) / nOf l) := by
    unfold xP
    rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_natCast (2 : ℝ) l,
      ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast (3 : ℝ) (nOf l), ← Real.rpow_mul (by norm_num),
      mul_one_div_cancel hn0, Real.rpow_one, mul_one_div]
    field_simp
  have hroot1 : 1 < xP l ^ (1 / (nOf l : ℝ)) := Real.one_lt_rpow hx1 hnpos
  have hD : (2 : ℝ) ^ l - 3 ^ nOf l = 3 ^ nOf l * (xP l - 1) := by
    unfold xP
    field_simp
  have hf6 : f6 l (xP l)
      = (alpha1 l * xP l ^ (1 - 1 / mR l) + alpha2 l * (xP l ^ (1 - 1 / mR l) - 1) / (xP l ^ (1 / mR l) - 1))
        * (3 * (xP l ^ (1 / (nOf l : ℝ)) - 1) / (xP l - 1)) := rfl
  have hx1' : 0 < xP l - 1 := by linarith
  have hr1' : 0 < 3 * (xP l ^ (1 / (nOf l : ℝ)) - 1) := by linarith
  have hr0 : xP l ^ (1 / (nOf l : ℝ)) - 1 ≠ 0 := by linarith
  have hx0 : xP l - 1 ≠ 0 := by linarith
  calc (M l (nOf l) : ℝ) / ((2 : ℝ) ^ l - 3 ^ nOf l)
      = ((M l (nOf l) : ℝ) / 3 ^ nOf l) / (xP l - 1) := by
        rw [hD, div_div]
    _ ≤ (alpha1 l * xP l ^ (1 - 1 / mR l) + alpha2 l * (xP l ^ (1 - 1 / mR l) - 1) / (xP l ^ (1 / mR l) - 1))
          / (xP l - 1) := div_le_div_of_nonneg_right hP hx1'.le
    _ = f6 l (xP l) / (3 * (xP l ^ (1 / (nOf l : ℝ)) - 1)) := by
        rw [hf6]
        field_simp
    _ ≤ (9 / 10) / (3 * (xP l ^ (1 / (nOf l : ℝ)) - 1)) := div_le_div_of_nonneg_right hf hr1'.le
    _ = alphaHH * ((2 : ℝ) ^ ((l : ℝ) / nOf l) - 3)⁻¹ := by
        rw [← hxroot]
        unfold alphaHH
        field_simp

theorem thm3_of_thm : thm3_of := fun hP2 hL6 => thm3_cond_thm (thm3_line_of_thm hP2 hL6)

end LaboHH
