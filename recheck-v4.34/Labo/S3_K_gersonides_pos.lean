import Labo.S3_Enonces
-- S3-A · A4 formaliste (2026-09-26) : copie signée de Labo/Tent_gersonides_pos_P1.lean (sha16 5f3ee2429034919c), re-jugée sous l'oracle.

/-! LABO-COLLATZ · S3-A · prouveur P1 — B11+ (Gersonides, positive side), via 3^r mod 8 ∈ {1, 3}. -/

namespace LaboP1.GersPos

theorem three_pow_mod_eight (r : ℕ) : (3 : ℤ) ^ r % 8 = 1 ∨ (3 : ℤ) ^ r % 8 = 3 := by
  induction r with
  | zero => left; norm_num
  | succ r ih =>
    rw [pow_succ]
    generalize (3 : ℤ) ^ r = Y at ih ⊢
    omega

end LaboP1.GersPos

open LaboP1.GersPos in
theorem gersonides_pos_thm : LaboK.gersonides_pos_enonce := by
  intro N r h
  have hY : (0 : ℤ) < 3 ^ r := by positivity
  have hm := three_pow_mod_eight r
  match N, r with
  | 0, _ => norm_num at h <;> omega
  | 1, 0 => left; exact ⟨rfl, rfl⟩
  | 1, r + 1 =>
    have h3 : (0 : ℤ) < 3 ^ r := by positivity
    rw [pow_succ] at h; norm_num at h <;> omega
  | 2, 0 => norm_num at h
  | 2, 1 => right; exact ⟨rfl, rfl⟩
  | 2, r + 2 =>
    have h3 : (0 : ℤ) < 3 ^ r := by positivity
    rw [pow_add] at h; norm_num at h <;> omega
  | N + 3, r =>
    have hX : (0 : ℤ) < 2 ^ N := by positivity
    rw [pow_add] at h; norm_num at h
    generalize (3 : ℤ) ^ r = Y at h hm hY
    generalize (2 : ℤ) ^ N = X at h hX
    omega
