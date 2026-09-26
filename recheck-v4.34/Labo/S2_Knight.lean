import Mathlib
import Labo.Blueprint
import Labo.S2_Pont
import Labo.S2_Bits

/-!
# LABO-COLLATZ · S2 · A4 Formaliste — the "Knight swap" lemma of A7 (Bibliothécaire, S2 tour 0)

`C_a` for any multiplier `a` (C3 cousin: `a = 5`).  A7's key lemma:
`C_a(u ++ [0,1]) − C_a(u ++ [1,0]) = 2^{|u|}`, for every `a`.
Consequence (`knight_core`): if `d = 2^N − 3^r` divides BOTH `C(u01)` and `C(u10)`, then `d = ±1`.
This is the core of Knight's exclusion of balanced cycles (K1), in the form "two neighbouring rotations
cannot both be integral unless |d| = 1".  It holds for both signs of `d` (C1: the cycle −5, word 110,
has d = −1 and is saved exactly by |d| = 1).  No `sorry`, no `native_decide`; `decide` only in the finite
named witness `knight_C1_witness`.  (Header corrected by the director on 2026-09-26, RT-2 S2 écart 6.)
-/

namespace LaboBP

/-- `C_a [] = 0`, `C_a (b :: w) = [b]·a^{r(w)} + 2·C_a w`. -/
def Ca (a : ℕ) : List Bool → ℕ
  | [] => 0
  | b :: w => (if b then a ^ (w.count true) else 0) + 2 * Ca a w

theorem Ca_three : Ca 3 = C := by
  funext w
  induction w with
  | nil => rfl
  | cons b w ih => simp [Ca, C, ih]

/-- Concatenation rule: `C_a(u ++ v) = a^{r(v)}·C_a(u) + 2^{|u|}·C_a(v)`. -/
theorem Ca_append (a : ℕ) (u v : List Bool) :
    Ca a (u ++ v) = a ^ (v.count true) * Ca a u + 2 ^ u.length * Ca a v := by
  induction u with
  | nil => simp [Ca]
  | cons b u ih =>
    rw [List.cons_append, Ca, Ca, ih, List.count_append, List.length_cons]
    cases b <;> simp <;> ring

/-- **A7's swap lemma** (all `a`). -/
theorem knight_swap (a : ℕ) (u : List Bool) :
    (Ca a (u ++ [false, true]) : ℤ) - Ca a (u ++ [true, false]) = 2 ^ u.length := by
  rw [Ca_append, Ca_append]
  simp [Ca]
  ring

theorem d_odd (w : List Bool) (hne : w ≠ []) : Odd (d w) := by
  obtain ⟨b, v, rfl⟩ := List.exists_cons_of_ne_nil hne
  unfold d
  rw [List.length_cons, pow_succ]
  obtain ⟨k, hk⟩ := (Odd.pow (⟨1, by norm_num⟩ : Odd (3 : ℤ)) : Odd ((3 : ℤ) ^ (b :: v).count true))
  rw [hk]
  exact ⟨2 ^ v.length - k - 1, by ring⟩

/-- **Knight core.**  If `d` divides `C(u01)` and `C(u10)`, then `d = 1` or `d = −1`. -/
theorem knight_core (u : List Bool)
    (h1 : d (u ++ [false, true]) ∣ (C (u ++ [false, true]) : ℤ))
    (h2 : d (u ++ [false, true]) ∣ (C (u ++ [true, false]) : ℤ)) :
    d (u ++ [false, true]) = 1 ∨ d (u ++ [false, true]) = -1 := by
  set D := d (u ++ [false, true]) with hD
  have hsw : D ∣ (2 : ℤ) ^ u.length := by
    rw [← knight_swap 3 u, Ca_three]
    exact dvd_sub h1 h2
  have hodd : Odd D := d_odd _ (by simp)
  have hc : IsCoprime D ((2 : ℤ) ^ u.length) :=
    ((isCoprime_two_of_odd D hodd).symm).pow_right
  have hu : IsUnit D := hc.isUnit_of_dvd' dvd_rfl hsw
  exact Int.isUnit_iff.mp hu

/-- The two words have the same `d` (same length, same number of ones). -/
theorem d_swap (u : List Bool) : d (u ++ [true, false]) = d (u ++ [false, true]) := by
  simp [d]

/-- C1 consistency witness: `u = [true]` gives the words `101` / `110`; `d = 2^3 − 3^2 = −1`
(the cycle −5 lives on `110`): the conclusion `|d| = 1` is exactly what saves it. -/
theorem knight_C1_witness : d ([true] ++ [false, true]) = -1 ∧
    (C ([true] ++ [false, true]) : ℤ) - C ([true] ++ [true, false]) = 2 := by decide

end LaboBP
