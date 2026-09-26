import Labo.S4_Enonces
import Labo.S2_B5
import Labo.Tent_Kstar_formaliste

/-!
# LABO-COLLATZ · S4-A · A4 formaliste (2026-09-26) — assemblage de K★ sous forme d'orbite
`w = pw T x n` suit `x` (`follows_pw`) et a pour longueur `n` (`length_pw`) ; `T^[n] x = x` ⇒ (`B2`)
`x·d(w) = C(w)` ; `r ≥ 1` car `knightWord n 0 = []` n'a pas la longueur `n > 0` ; `r ≤ n` ; puis
`Kstar_x_cor` (corollaire de `Kstar_thm`, KEEP S3, Tent_Kstar_formaliste) donne `x ∈ {1, 2}`.
-/

open LaboBP LaboK in
theorem Kstar_orbit_thm : LaboF.Kstar_orbit_enonce := by
  intro x n r k hx hn hper hr hcop hw
  have hlen : (pw T x n).length = n := length_pw T x n
  have hf : Follows x (pw T x n) := follows_pw x n
  have hcyc := (B2 x (pw T x n) hf).mp (by rw [hlen]; exact hper)
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · subst h0
      have hk : knightWord n 0 = [] := by simp [knightWord]
      rw [hk, List.rotate_nil] at hw
      rw [hw] at hlen
      simp at hlen
      omega
    · exact h0
  have hrn : r ≤ n := by
    have := List.count_le_length (a := true) (l := pw T x n)
    omega
  rw [hw] at hcyc
  exact (Kstar_x_cor n r k x hcop hr1 hrn hx hcyc).2.2
