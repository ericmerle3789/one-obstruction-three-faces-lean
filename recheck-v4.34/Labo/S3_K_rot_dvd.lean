import Labo.S3_Enonces
-- S3-A · A4 formaliste (2026-09-26) : copie signée de Labo/Tent_rot_dvd_P1.lean (sha16 67b497fa26b15190), re-jugée sous l'oracle.

/-! LABO-COLLATZ · S3-A · prouveur P1 — B7 `rot_dvd` (base 3).
One rotation step: `2·C(v·b) = 3^b·C(b·v) + b·d(b·v)`, so `d ∣ 2·C(ρu)`, and `d` is odd.
`d` is rotation-invariant (same length, same number of ones). Induction on `k`. -/

open LaboBP LaboK

namespace LaboP1.RotDvd

theorem step_three (b : Bool) (v : List Bool) :
    2 * (C (v ++ [b]) : ℤ) =
      (if b then (3 : ℤ) else 1) * (C (b :: v) : ℤ) + (if b then d (b :: v) else 0) := by
  rw [← Ca_three, Ca_append]
  cases b <;> simp [Ca, d, List.count_cons] <;> push_cast <;> ring

theorem d_rotate (w : List Bool) (k : ℕ) : d (w.rotate k) = d w := by
  unfold d
  rw [List.length_rotate, (List.rotate_perm w k).count_eq]

theorem dvd_rotate_one (u : List Bool) (h : d u ∣ (C u : ℤ)) : d u ∣ (C (u.rotate 1) : ℤ) := by
  cases u with
  | nil => simpa using h
  | cons b v =>
    have hrot : (b :: v).rotate 1 = v ++ [b] := by simp [List.rotate_cons_succ]
    rw [hrot]
    have h2 : d (b :: v) ∣ 2 * (C (v ++ [b]) : ℤ) := by
      rw [step_three]
      cases b
      · simpa using h
      · simp only [if_true]
        exact dvd_add (dvd_mul_of_dvd_right h _) dvd_rfl
    have hodd : Odd (d (b :: v)) := d_odd _ (by simp)
    have hc : IsCoprime (d (b :: v)) 2 := (isCoprime_two_of_odd _ hodd).symm
    exact hc.dvd_of_dvd_mul_left h2

end LaboP1.RotDvd

open LaboP1.RotDvd in
theorem rot_dvd_thm : LaboK.rot_dvd_enonce := by
  intro w k h
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [← List.rotate_rotate]
    have := dvd_rotate_one (w.rotate k) (by rw [d_rotate]; exact ih)
    rwa [d_rotate] at this
