import Mathlib
import Lagarias.Tables_Enonces
import Lagarias.L3_Preuves

/-!
# Lagarias 1990 · Tables · proofs (kernel computation)

Table 2.2 (values, completeness, the `110000` remark), Table 3.1 (48 rows, and the two corrected rows with
the minimality of the corrected `n0`), p. 41, and the count in the proof of Theorem 3.3.
All computations are checked by the kernel (`decide +kernel`); no `native_decide`.
Statements: `Lagarias/L1990_Enonces.lean`, `Lagarias/Tables_Enonces.lean` (frozen).
-/

namespace Lagarias

open LaboBP LaboHH

/-! ## Table 2.2 -/

lemma xv_eq_of_cross (v : List Bool) (a b : ℤ) (hb : 0 < b) (hd : d v ≠ 0)
    (h : (C v : ℤ) * b = a * d v) : xv v = (a : ℚ) / b := by
  rw [xv, div_eq_div_iff (by exact_mod_cast hd) (by exact_mod_cast hb.ne')]
  exact_mod_cast h

lemma table2_2_check : ∀ r ∈ table2_2,
    (C (bw r.1) : ℤ) * r.2.2 = r.2.1 * d (bw r.1) ∧ 0 < r.2.2 ∧ d (bw r.1) ≠ 0 ∧
      Int.gcd r.2.1 r.2.2 = 1 := by
  decide +kernel

theorem table2_2_values_thm : table2_2_values := by
  intro r hr
  obtain ⟨h1, h2, h3, h4⟩ := table2_2_check r hr
  have hx := xv_eq_of_cross _ _ _ h2 h3 h1
  refine ⟨hx, ?_⟩
  rw [hx]
  have h5 := Rat.den_div_eq_of_coprime h2 (show Nat.Coprime r.2.1.natAbs r.2.2.natAbs from h4)
  omega

theorem table2_2_complete_thm : table2_2_complete := by
  unfold table2_2_complete
  decide +kernel

theorem table2_2_gcd_thm : table2_2_gcd := by
  refine ⟨by decide +kernel, ?_, by decide +kernel⟩
  have := (table2_2_values_thm ([1,1,0,0,0,0], 1, 11) (by decide)).2
  exact this

/-! ## Table 3.1 -/

theorem table3_1_rows_thm : table3_1_rows := by
  unfold table3_1_rows PrimCycleOfLength
  decide +kernel

/-- A certificate of non-periodicity: the orbit of `n` enters a cycle that avoids `n`. -/
lemma not_periodic_of_cert (f : ℤ → ℤ) (n : ℤ) (j0 L : ℕ) (hL : 0 < L)
    (hcyc : f^[j0 + L] n = f^[j0] n) (hne : ∀ i < L, f^[j0 + i] n ≠ n) :
    ¬ ∃ p, 0 < p ∧ f^[p] n = n := by
  rintro ⟨p, hp, hper⟩
  have hy : Function.IsPeriodicPt f L (f^[j0] n) := by
    show f^[L] (f^[j0] n) = f^[j0] n
    rw [← Function.iterate_add_apply, add_comm]; exact hcyc
  have hP : Function.IsPeriodicPt f p n := hper
  have hmul : f^[p * j0] n = n := (hP.mul_const j0).eq
  have hge : j0 ≤ p * j0 := Nat.le_mul_of_pos_left j0 hp
  set i := p * j0 - j0
  have e : f^[p * j0] n = f^[j0 + i % L] n := by
    rw [show p * j0 = i + j0 by omega, Function.iterate_add_apply, ← hy.iterate_mod_apply i,
      ← Function.iterate_add_apply, add_comm]
  exact hne (i % L) (Nat.mod_lt _ hL) (by rw [← e, hmul])

theorem table3_1_row35_thm : table3_1_row35 := by
  refine ⟨by decide +kernel, by decide, by unfold PrimCycleOfLength; decide +kernel, ?_⟩
  intro n hn1 hn2 hg
  have cert : ∀ (j0 : ℕ), (Tk 35)^[j0 + 8] n = (Tk 35)^[j0] n → (∀ i < 8, (Tk 35)^[j0 + i] n ≠ n) →
      ¬ ∃ p, 0 < p ∧ (Tk 35)^[p] n = n := fun j0 h1 h2 => not_periodic_of_cert _ n j0 8 (by norm_num) h1 h2
  interval_cases n
  all_goals first
    | exact absurd hg (by decide)
    | exact cert 4 (by decide +kernel) (by decide +kernel)
    | exact cert 5 (by decide +kernel) (by decide +kernel)
    | exact cert 3 (by decide +kernel) (by decide +kernel)
    | exact cert 6 (by decide +kernel) (by decide +kernel)
    | exact cert 7 (by decide +kernel) (by decide +kernel)
    | exact cert 12 (by decide +kernel) (by decide +kernel)
    | exact cert 1 (by decide +kernel) (by decide +kernel)

theorem table3_1_row73_thm : table3_1_row73 := by
  refine ⟨by unfold PrimCycleOfLength; decide +kernel, by unfold PrimCycleOfLength; decide +kernel, ?_⟩
  intro n hn1 hn2 hg
  have cert : ∀ (j0 : ℕ), (Tk 73)^[j0 + 60] n = (Tk 73)^[j0] n → (∀ i < 60, (Tk 73)^[j0 + i] n ≠ n) →
      ¬ ∃ p, 0 < p ∧ (Tk 73)^[p] n = n := fun j0 h1 h2 => not_periodic_of_cert _ n j0 60 (by norm_num) h1 h2
  interval_cases n
  · exact cert 1 (by decide +kernel) (by decide +kernel)
  · exact cert 2 (by decide +kernel) (by decide +kernel)
  · exact cert 1 (by decide +kernel) (by decide +kernel)
  · exact cert 3 (by decide +kernel) (by decide +kernel)

/-! ## p. 41 and the count of the proof of Theorem 3.3 -/

theorem p41_thm : p41 := by
  unfold p41 PrimCycleOfLength
  decide +kernel

theorem thm3_3_count_printed_false_thm : thm3_3_count_printed_false := by
  refine ⟨by decide, ?_, ?_, by norm_num [collatzQ], by norm_num [collatzQ]⟩
  · rw [xv_eq_of_cross _ 1 1 (by norm_num) (by decide) (by decide)]; norm_num
  · rw [xv_eq_of_cross _ 2 1 (by norm_num) (by decide) (by decide)]; norm_num

end Lagarias
