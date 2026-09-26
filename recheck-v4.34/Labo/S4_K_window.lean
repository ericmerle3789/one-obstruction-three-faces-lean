import Labo.S4_K_orbitProd

/-!
# S4-A · prouveur P1 · window (FEN)
Idea: absolute value of B18o (`orbitProd_thm`, KEEP): `2^n · ∏|x_i| = ∏|3x_i+1| ≤ 4^r · ∏|x_i|`
(odd `y`: `|3y+1| ≤ 4|y|`, strict unless `y = 1`), so `2^n ≤ 2^(2r)`.  If `n = 2r` every factor
is tight (`Finset.prod_lt_prod₀` otherwise), so every odd orbit value is `1`; `r ≥ 1` gives one,
and `x = T^[n] x = T^[n-i] 1 ∈ {1, 2}`.
-/

namespace LaboF.P1W

open LaboBP LaboF

theorem odd_bound (y : ℤ) (hy : y % 2 = 1) : |3 * y + 1| ≤ 4 * |y| := by
  rcases abs_cases (3 * y + 1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases abs_cases y with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega

theorem odd_bound_strict (y : ℤ) (hy : y % 2 = 1) (h1 : y ≠ 1) : |3 * y + 1| < 4 * |y| := by
  rcases abs_cases (3 * y + 1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases abs_cases y with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega

theorem iterate_one (k : ℕ) : T^[k] (1 : ℤ) = 1 ∨ T^[k] (1 : ℤ) = 2 := by
  induction k with
  | zero => left; rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | h <;> rw [h] <;> decide

end LaboF.P1W

open LaboBP LaboF in
theorem window_thm : LaboF.window_enonce := by
  intro x n hx hn hper
  set O := oddIdx x n with hO
  have hmem : ∀ i ∈ O, i < n ∧ T^[i] x % 2 = 1 := by
    intro i hi
    simpa [hO, oddIdx] using hi
  -- absolute value of B18o
  have hprod := orbitProd_thm x n hx hper
  have habs : (2 : ℤ) ^ n * ∏ i ∈ O, |T^[i] x| = ∏ i ∈ O, |3 * T^[i] x + 1| := by
    have := congrArg abs hprod
    rwa [abs_mul, abs_pow, Finset.abs_prod, Finset.abs_prod, abs_two] at this
  have hPpos : 0 < ∏ i ∈ O, |T^[i] x| :=
    Finset.prod_pos (fun i _ => abs_pos.mpr (LaboF.P1.iterate_T_ne_zero x hx i))
  have hle : ∏ i ∈ O, |3 * T^[i] x + 1| ≤ ∏ i ∈ O, (4 * |T^[i] x|) :=
    Finset.prod_le_prod₀ (fun i _ => abs_nonneg _)
      (fun i hi => LaboF.P1W.odd_bound _ (hmem i hi).2)
  have h4 : ∏ i ∈ O, (4 * |T^[i] x|) = (2 : ℤ) ^ (2 * O.card) * ∏ i ∈ O, |T^[i] x| := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, pow_mul]; norm_num
  have hpow : (2 : ℤ) ^ n ≤ 2 ^ (2 * O.card) := by
    have := habs ▸ hle
    rw [h4] at this
    exact le_of_mul_le_mul_right this hPpos
  refine ⟨(pow_le_pow_iff_right₀ (by norm_num : (1 : ℤ) < 2)).mp hpow, ?_⟩
  intro heq
  -- every odd orbit value is 1
  have hall : ∀ i ∈ O, T^[i] x = 1 := by
    intro j hj
    by_contra hj1
    have hlt : ∏ i ∈ O, |3 * T^[i] x + 1| < ∏ i ∈ O, (4 * |T^[i] x|) :=
      Finset.prod_lt_prod₀
        (fun i _ => abs_pos.mpr (by have := (hmem i ‹_›).2; omega))
        (fun i hi => LaboF.P1W.odd_bound _ (hmem i hi).2)
        ⟨j, hj, LaboF.P1W.odd_bound_strict _ (hmem j hj).2 hj1⟩
    rw [← habs, h4, ← heq] at hlt
    exact lt_irrefl _ hlt
  have hne : O.Nonempty := by
    rw [← Finset.card_pos]; omega
  obtain ⟨i, hi⟩ := hne
  have hin := (hmem i hi).1
  have hx1 : T^[i] x = 1 := hall i hi
  have : T^[n] x = T^[n - i] (T^[i] x) := by
    rw [← Function.iterate_add_apply]; congr 1; omega
  rw [hper, hx1] at this
  rw [this]
  exact LaboF.P1W.iterate_one (n - i)
