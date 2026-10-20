import Mathlib
import Lagarias.L1990b_Enonces
import Lagarias.Mots

/-!
# Lagarias 1990 · (2.4), (2.5), Table 2.1 · proofs

* (2.4) is `Σ_{d∣n} #Irr(d) = 2ⁿ` (every word is a power of exactly one irreducible word) together with
  `d ∣ #Irr(d)` (rotations act freely), both from `Lagarias/Mots.lean`.
* (2.5) is the Möbius inversion of (2.4) (`ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq` of Mathlib).
* Table 2.1: (2.4) gives `I(n) = (2ⁿ − Σ_{d∣n, d<n} d·I(d))/n` (`Iirr_rec`); the list `Ilist 20`, computed by
  this recursion, is checked against the printed table by the kernel (`decide +kernel`, no `native_decide`).
  Counting the `2²⁰` words directly would be out of reach of the kernel.
Statements: `Lagarias/L1990b_Enonces.lean` (frozen).
-/

namespace Lagarias

open LaboBP LaboHH

/-! ## (2.4) and (2.5) -/

theorem eq2_4_thm : eq2_4 := by
  intro n hn
  rw [← sum_card_Irr hn]
  exact Finset.sum_congr rfl fun d hd => mul_Iirr (Nat.pos_of_mem_divisors hd)

theorem eq2_5_thm : eq2_5 := by
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℤ)
    (f := fun d => ((d * Iirr d : ℕ) : ℤ)) (g := fun n => (2 : ℤ) ^ n)).mp (fun n hn => by
      have := eq2_4_thm n hn
      exact_mod_cast this)
  intro n hn
  rw [← h n hn]
  simp only [Int.cast_id]
  exact Nat.sum_divisorsAntidiagonal (fun x y => (ArithmeticFunction.moebius x : ℤ) * 2 ^ y)

/-! ## Table 2.1 -/

/-- (2.4) solved for `I(n)`. -/
lemma Iirr_rec {n : ℕ} (hn : 0 < n) : Iirr n = (2 ^ n - ∑ d ∈ n.properDivisors, d * Iirr d) / n := by
  have h := eq2_4_thm n hn
  rw [← Nat.cons_self_properDivisors hn.ne', Finset.sum_cons] at h
  rw [← h, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ hn]

/-- `[I(1), …, I(n)]`, computed by the recursion `Iirr_rec`. -/
def Ilist : ℕ → List ℕ
  | 0 => []
  | n + 1 => Ilist n ++ [(2 ^ (n + 1) - ∑ d ∈ (n + 1).properDivisors, d * (Ilist n).getD (d - 1) 0) / (n + 1)]

lemma Ilist_spec (n : ℕ) : (Ilist n).length = n ∧ ∀ i < n, (Ilist n).getD i 0 = Iirr (i + 1) := by
  induction n with
  | zero => simp [Ilist]
  | succ n ih =>
    obtain ⟨hl, hv⟩ := ih
    refine ⟨by simp [Ilist, hl], fun i hi => ?_⟩
    simp only [Ilist]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [List.getD_append _ _ _ _ (by rw [hl]; exact hi), hv i hi]
    · rw [List.getD_append_right _ _ _ _ (by rw [hl]), hl, Nat.sub_self, Iirr_rec (Nat.succ_pos i)]
      simp only [List.getD_cons_zero]
      congr 2
      apply Finset.sum_congr rfl
      intro d hd
      obtain ⟨hdv, hdl⟩ := Nat.mem_properDivisors.mp hd
      have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdv (Nat.succ_pos i)
      rw [hv (d - 1) (by omega), Nat.sub_add_cancel hd0]

theorem table2_1_thm : table2_1 := by
  have h : (List.range 20).map (fun i => Iirr (i + 1)) = Ilist 20 := by
    obtain ⟨hl, hv⟩ := Ilist_spec 20
    apply List.ext_getElem (by simp [hl])
    intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    rw [List.getElem_map, List.getElem_range, ← hv i h1, List.getD_eq_getElem]
  unfold table2_1
  rw [h]
  decide +kernel

end Lagarias
