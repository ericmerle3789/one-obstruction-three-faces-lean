import Mathlib
import Labo.Blueprint

/-!
# LABO-COLLATZ · S2 · A4 Formaliste — parity-bit bijection (A2, S1; core of B4)

For every odd `p` and the map `Tp p : x ↦ x/2 | (p x + 1)/2`:
* `parity_bits` : same first `k` parity bits ⇔ `x ≡ y (mod 2^k)`;
* `parity_bits_surj` : every bit pattern occurs.
Classical (Terras 1976, Lagarias 1985 — de seconde main).  No `sorry`, no `native_decide`, no `decide`.
Cousin note: the statement holds for EVERY odd `p` (C3 included) and on all of `ℤ` (C1 included):
it is a barrier-type fact — it cannot see "3 and not 5" nor "d > 0".
-/

namespace LaboBP

theorem two_mul_Tp_even (p x : ℤ) (h : x % 2 = 0) : 2 * Tp p x = x := by
  unfold Tp; split_ifs; omega

theorem two_mul_Tp_odd (p x : ℤ) (hp : Odd p) (h : x % 2 = 1) : 2 * Tp p x = p * x + 1 := by
  unfold Tp
  rw [if_neg (by omega)]
  obtain ⟨a, rfl⟩ := hp
  obtain ⟨b, rfl⟩ : ∃ b, x = 2 * b + 1 := ⟨x / 2, by omega⟩
  have : (2 : ℤ) ∣ (2 * a + 1) * (2 * b + 1) + 1 := ⟨2 * a * b + a + b + 1, by ring⟩
  exact Int.mul_ediv_cancel' this

theorem isCoprime_two_of_odd (p : ℤ) (hp : Odd p) : IsCoprime (2 : ℤ) p := by
  obtain ⟨a, rfl⟩ := hp
  exact ⟨-a, 1, by ring⟩

theorem parity_bit_eq_iff (x y : ℤ) : (x % 2 == 1) = (y % 2 == 1) ↔ x % 2 = y % 2 := by
  rcases Int.emod_two_eq_zero_or_one x with hx | hx <;>
    rcases Int.emod_two_eq_zero_or_one y with hy | hy <;> simp [hx, hy]

/-- **Parity-bit bijection, injective half (and its converse).** -/
theorem parity_bits : ParityBits_statement := by
  intro p hp k
  induction k with
  | zero => intro x y; simp [pw]
  | succ k ih =>
    intro x y
    simp only [pw, List.cons.injEq, parity_bit_eq_iff, ih]
    have hc : IsCoprime ((2 : ℤ) ^ (k + 1)) p := (isCoprime_two_of_odd p hp).pow_left
    rw [pow_succ']
    constructor
    · rintro ⟨hpar, hk⟩
      rcases Int.emod_two_eq_zero_or_one x with hx | hx
      · have hy : y % 2 = 0 := by omega
        have e : x - y = 2 * (Tp p x - Tp p y) := by
          linear_combination (two_mul_Tp_even p x hx).symm - (two_mul_Tp_even p y hy).symm
        rw [e]; exact mul_dvd_mul_left 2 hk
      · have hy : y % 2 = 1 := by omega
        have e : p * (x - y) = 2 * (Tp p x - Tp p y) := by
          linear_combination (two_mul_Tp_odd p x hp hx).symm - (two_mul_Tp_odd p y hp hy).symm
        have h1 : (2 : ℤ) * 2 ^ k ∣ p * (x - y) := by rw [e]; exact mul_dvd_mul_left 2 hk
        rw [← pow_succ'] at h1 ⊢
        exact hc.dvd_of_dvd_mul_left h1
    · intro h
      have h2 : (2 : ℤ) ∣ x - y := dvd_trans (dvd_mul_right 2 _) h
      have hpar : x % 2 = y % 2 := by omega
      refine ⟨hpar, ?_⟩
      rcases Int.emod_two_eq_zero_or_one x with hx | hx
      · have hy : y % 2 = 0 := by omega
        have e : x - y = 2 * (Tp p x - Tp p y) := by
          linear_combination (two_mul_Tp_even p x hx).symm - (two_mul_Tp_even p y hy).symm
        rw [e] at h
        exact (mul_dvd_mul_iff_left two_ne_zero).mp h
      · have hy : y % 2 = 1 := by omega
        have e : p * (x - y) = 2 * (Tp p x - Tp p y) := by
          linear_combination (two_mul_Tp_odd p x hp hx).symm - (two_mul_Tp_odd p y hp hy).symm
        have h1 : (2 : ℤ) * 2 ^ k ∣ 2 * (Tp p x - Tp p y) := by
          rw [← e]; exact dvd_mul_of_dvd_right h p
        exact (mul_dvd_mul_iff_left two_ne_zero).mp h1

/-- **Every bit pattern occurs.** -/
theorem parity_bits_surj : ParityBitsSurj_statement := by
  intro p hp w
  induction w with
  | nil => exact ⟨0, rfl⟩
  | cons b w ih =>
    obtain ⟨y, hy⟩ := ih
    cases b with
    | false =>
      refine ⟨2 * y, ?_⟩
      have hT : Tp p (2 * y) = y := by unfold Tp; split_ifs <;> omega
      simp only [List.length_cons, pw, hT, hy]
      have : (2 * y) % 2 = 0 := by omega
      simp [this]
    | true =>
      set k := w.length
      obtain ⟨u, v, huv⟩ := ((isCoprime_two_of_odd p hp).pow_left (m := k + 1)).symm
      set x := u * (2 * y - 1) with hxdef
      have hpx : p * x = 2 * y - 1 - 2 * (v * 2 ^ k * (2 * y - 1)) := by
        rw [hxdef]; linear_combination (2 * y - 1) * huv
      have hx : x % 2 = 1 := by
        rcases Int.emod_two_eq_zero_or_one x with h | h
        · exfalso
          obtain ⟨m, hm⟩ : ∃ m, x = 2 * m := ⟨x / 2, by omega⟩
          have e : 2 * (p * m) = 2 * y - 1 - 2 * (v * 2 ^ k * (2 * y - 1)) := by
            rw [← hpx, hm]; ring
          generalize p * m = a at e
          generalize v * 2 ^ k * (2 * y - 1) = c at e
          omega
        · exact h
      have hT : Tp p x - y = 2 ^ k * (-(v * (2 * y - 1))) := by
        have := two_mul_Tp_odd p x hp hx
        have e2 : 2 * (Tp p x - y) = 2 * (2 ^ k * (-(v * (2 * y - 1)))) := by
          linear_combination this + hpx
        exact mul_left_cancel₀ two_ne_zero e2
      have hbits : pw (Tp p) (Tp p x) k = pw (Tp p) y k :=
        (parity_bits p hp k (Tp p x) y).mpr ⟨_, hT⟩
      refine ⟨x, ?_⟩
      show (x % 2 == 1) :: pw (Tp p) (Tp p x) k = true :: w
      rw [hbits, hy, hx]
      rfl

end LaboBP
