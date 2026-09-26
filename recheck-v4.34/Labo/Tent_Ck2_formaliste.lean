import Labo.S4_K_window
import Labo.S4_K_oddCount
import Labo.S4_K_k2NormalForm
import Labo.S2_B5
import Labo.Tent_k2Long_formaliste

/-!
# LABO-COLLATZ · S4-A · A4 formaliste (2026-09-26) — assemblage de Ck2
`x·d = C` ⇒ (`B4_int`) `Follows x w` et `T^[N] x = x` ; `C w > 0` (`C_pos`, il y a un 1 car
`1 ≤ lam < r`) ⇒ `x ≠ 0` ; FEN (`window`) + `oddCount` ⇒ `N ≤ 2 r` ; `k2Long` ⇒ `2 r + 1 ≤ N`. Absurde.
-/

open LaboBP LaboF in
theorem Ck2_thm : LaboF.Ck2_enonce := by
  intro w hcop hb x hx
  have hlong := k2Long_thm w hcop hb
  obtain ⟨_, _, lam, _, hlam, hlr, _⟩ := k2NormalForm_thm w hcop hb
  have htrue : true ∈ w := List.count_pos_iff.mp (by omega)
  have hC : 0 < C w := C_pos w htrue
  have hx0 : x ≠ 0 := by
    rintro rfl
    have : ((C w : ℕ) : ℤ) = 0 := by rw [← hx]; ring
    omega
  obtain ⟨hf, hper⟩ := B4_int x w hx
  have hN : 0 < w.length := by omega
  have hwin := (window_thm x w.length hx0 hN hper).1
  have hcnt := oddCount_thm x w.length
  unfold Follows at hf
  rw [hf] at hcnt
  omega
