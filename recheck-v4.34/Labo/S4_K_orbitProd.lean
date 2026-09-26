import Labo.S4_Enonces

/-!
# S4-A · prouveur P1 · orbitProd (B18o)
Idea: `2·x_{i+1} = (x_i odd ? 3x_i+1 : x_i)`; multiply over `i < n`; periodicity turns
`∏ x_{i+1}` into `∏ x_i`; split both sides along odd/even indices (`Finset.prod_ite`,
`Finset.prod_filter_mul_prod_filter_not`) and cancel the even part, nonzero because the orbit of a
nonzero integer never meets `0`.
-/

namespace LaboF.P1

open LaboBP LaboF

theorem two_mul_T_step (y : ℤ) :
    2 * T y = if y % 2 = 1 then 3 * y + 1 else y := by
  unfold T
  by_cases h : y % 2 = 1
  · rw [if_pos h, if_neg (by omega)]; omega
  · rw [if_neg h, if_pos (by omega)]; omega

theorem T_ne_zero (y : ℤ) (hy : y ≠ 0) : T y ≠ 0 := by
  intro h0
  have := two_mul_T_step y
  rw [h0] at this
  split_ifs at this <;> omega

theorem iterate_T_ne_zero (x : ℤ) (hx : x ≠ 0) (i : ℕ) : T^[i] x ≠ 0 := by
  induction i with
  | zero => simpa using hx
  | succ i ih => rw [Function.iterate_succ_apply']; exact T_ne_zero _ ih

theorem prod_shift_periodic (x : ℤ) (n : ℕ) (hx : x ≠ 0) (hper : T^[n] x = x) :
    ∏ i ∈ Finset.range n, T^[i + 1] x = ∏ i ∈ Finset.range n, T^[i] x := by
  have h1 := Finset.prod_range_succ' (fun i => T^[i] x) n
  have h2 := Finset.prod_range_succ (fun i => T^[i] x) n
  simp only [Function.iterate_zero_apply] at h1 h2
  rw [hper] at h2
  exact mul_right_cancel₀ hx (h1.symm.trans h2)

end LaboF.P1

open LaboBP LaboF in
theorem orbitProd_thm : LaboF.orbitProd_enonce := by
  intro x n hx hper
  set s := Finset.range n
  have hstep : ∀ i ∈ s, 2 * T^[i + 1] x = if T^[i] x % 2 = 1 then 3 * T^[i] x + 1 else T^[i] x := by
    intro i _
    rw [Function.iterate_succ_apply']
    exact LaboF.P1.two_mul_T_step _
  have hL : (2 : ℤ) ^ n * ∏ i ∈ s, T^[i] x = ∏ i ∈ s, (2 * T^[i + 1] x) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      LaboF.P1.prod_shift_periodic x n hx hper]
  rw [Finset.prod_congr rfl hstep, Finset.prod_ite] at hL
  rw [← Finset.prod_filter_mul_prod_filter_not s (fun i => T^[i] x % 2 = 1)] at hL
  have hB : ∏ i ∈ s.filter (fun i => ¬ (T^[i] x % 2 = 1)), T^[i] x ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => LaboF.P1.iterate_T_ne_zero x hx i)
  have hL' : ((2 : ℤ) ^ n * ∏ i ∈ s.filter (fun i => T^[i] x % 2 = 1), T^[i] x)
      * ∏ i ∈ s.filter (fun i => ¬ (T^[i] x % 2 = 1)), T^[i] x
      = (∏ i ∈ s.filter (fun i => T^[i] x % 2 = 1), (3 * T^[i] x + 1))
      * ∏ i ∈ s.filter (fun i => ¬ (T^[i] x % 2 = 1)), T^[i] x := by
    rw [← hL]; ring
  exact mul_right_cancel₀ hB hL'
