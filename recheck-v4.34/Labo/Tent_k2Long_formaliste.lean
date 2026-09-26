import Labo.S4_K_k2NormalForm
import Labo.S4_K_k2ValidBound

/-!
# LABO-COLLATZ · S4-A · A4 formaliste (2026-09-26) — assemblage de k2Long
`k2NormalForm` donne `(s, g, lam)` avec `g ≥ 1`, `1 ≤ lam < r` ; `k2ValidBound` donne `g + 1 ≤ N / r`,
donc `2 r ≤ N`. L'égalité `N = 2 r` est tuée par `gcd(N, r) = 1` et `r ≥ 2` (car `1 ≤ lam < r`).
-/

open LaboF in
theorem k2Long_thm : LaboF.k2Long_enonce := by
  intro w hcop hb
  obtain ⟨s, g, lam, hg, hlam, hlr, heq⟩ := k2NormalForm_thm w hcop hb
  have hv := k2ValidBound_thm w s g lam hcop hg hlam hlr heq
  have hr2 : 2 ≤ w.count true := by omega
  have h2 : 2 ≤ w.length / w.count true := by omega
  have h2r : 2 * w.count true ≤ w.length :=
    le_trans (Nat.mul_le_mul_right _ h2) (Nat.div_mul_le_self _ _)
  by_contra hcon
  have hN : w.length = 2 * w.count true := by omega
  have hgcd : Nat.gcd w.length (w.count true) = w.count true := by
    rw [hN]; exact Nat.gcd_eq_right (Dvd.intro_left 2 rfl)
  have h1 : Nat.gcd w.length (w.count true) = 1 := hcop
  omega
