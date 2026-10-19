import Mathlib
import Labo.HH1997d_Fort_Enonces
import Labo.HH1997d_CF_Preuves

/-!
# LABO-COLLATZ · HH1997d · formaliste (2026-10-19) — PROOF of `thm1_all_k` (Theorem 1 for every `k`)

Same argument as `thm1_cond_gap_thm`, at a single index `k`: it only uses the gap `cf_gap k`, proved for every `k ≥ 1`
(`cf_gap_all_thm`).  For `k = 0`, `q₀ = 1 < 2 ≤ n` (Lemma 8 gives `n ≥ 2`).
-/

namespace LaboHH

open LaboBP

lemma thm1_at (k : ℕ) (hgap : cf_gap k) (l n : ℕ) (s : List Bool) (hS : s ∈ Sln l n) (hnl : n ≤ nOf l)
    (m : ℚ) (hm1 : 1 < m) (hm : IsLeast (cycle ((phi s : ℚ) / (d s : ℚ))) m) :
    min (qCF k) (2 * (m : ℝ) / (qCF k + qCF (k + 1))) < n := by
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
  have hg := hgap (l : ℤ) (n : ℤ) (by exact_mod_cast (show 1 ≤ n by omega)) (by exact_mod_cast hnq)
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

theorem thm1_all_k_thm : thm1_all_k := by
  intro k l n s hS hnl m hm1 hm
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain ⟨hn2, -, -⟩ := lemma8_facts l n s hS hnl m hm1 hm
    have hq0 : qCF 0 = 1 := GenContFract.zeroth_den_eq_one
    have hn : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    calc min (qCF 0) (2 * (m : ℝ) / (qCF 0 + qCF (0 + 1))) ≤ qCF 0 := min_le_left _ _
      _ < n := by rw [hq0]; linarith
  · exact thm1_at k (cf_gap_all_thm k hk) l n s hS hnl m hm1 hm

end LaboHH
