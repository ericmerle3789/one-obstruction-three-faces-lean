import Labo.S3_Enonces
import Labo.S3_K_rot_dvd
import Labo.S3_K_kgeo
import Labo.S3_K_chrisSum_eq
import Labo.S3_K_knightWord_shape
import Labo.S3_K_gersonides_pos

/-!
# LABO-COLLATZ · S3-A · A4 formaliste (2026-09-26) — assemblage de K★(c)

`Kstar_thm : LaboK.Kstar_enonce`, à partir des KEEP signés (S3_K_*) :
x·d(ρ^k w) = C(ρ^k w) ⇒ d ∣ C(ρ^k w) ⇒ (B7, rotation retour ρ^{|w|k−k}) d ∣ C(w) = ChrisSum 3 N r
⇒ (B14, a = 3) d unité ⇒ d = ±1 ; d = 1 ⇒ (B11+) (N, r) = (2, 1) ; d = −1 ⇒ −x = C ≥ 0, absurde (x > 0).
Nœuds utilisés : rot_dvd, kgeo, chrisSum_eq, knightWord_shape, gersonides_pos. B11− n'est pas utilisé :
le cas d = −1 est tué par le signe (x > 0), pas par Gersonides−.
-/

open LaboBP LaboK

theorem Kstar_thm : LaboK.Kstar_enonce := by
  intro N r k x hcop h1 h2 hx hcyc
  obtain ⟨hlen, hcnt⟩ := knightWord_shape_thm N r h1 h2
  set w := knightWord N r with hw
  -- d(ρ^k w) divides C(ρ^k w)
  have hdvd' : d (w.rotate k) ∣ (C (w.rotate k) : ℤ) := ⟨x, by rw [← hcyc]; ring⟩
  -- rotate back to w
  have hback : (w.rotate k).rotate (w.length * k - k) = w := by
    rw [List.rotate_rotate]
    have : k + (w.length * k - k) = w.length * k := by
      have : k ≤ w.length * k := Nat.le_mul_of_pos_left k (by rw [hlen]; omega)
      omega
    rw [this, List.rotate_length_mul]
  have hdvd : d w ∣ (C w : ℤ) := by
    have := rot_dvd_thm (w.rotate k) (w.length * k - k) hdvd'
    rwa [hback, LaboP1.RotDvd.d_rotate] at this
  have hD : d w = (2 : ℤ) ^ N - 3 ^ r := by
    simp only [d, hlen, hcnt]
  have hC : (C w : ℤ) = (ChrisSum 3 N r : ℤ) := by
    rw [chrisSum_eq_thm N r h2]
  have hcopZ : IsCoprime (ChrisSum 3 N r : ℤ) ((2 : ℤ) ^ N - 3 ^ r) := by
    have := kgeo_thm 3 N r (by decide) h1 h2 hcop
    simpa using this
  have hunit : IsUnit ((2 : ℤ) ^ N - 3 ^ r) := by
    rw [← hD]
    exact hcopZ.isUnit_of_dvd' (by rw [← hC]; exact hdvd) (by rw [hD])
  rcases Int.isUnit_iff.mp hunit with h | h
  · rcases gersonides_pos_thm N r h with ⟨_, h0⟩ | hh
    · omega
    · exact hh
  · exfalso
    have hdr : d (w.rotate k) = d w := LaboP1.RotDvd.d_rotate w k
    rw [hdr, hD, h] at hcyc
    have : (0 : ℤ) ≤ (C (w.rotate k) : ℤ) := by positivity
    omega

/-- Corollaire non gelé (forme BLUEPRINT K★(c)) : de plus `x ∈ {1, 2}`. -/
theorem Kstar_x_cor (N r k : ℕ) (x : ℤ) (hcop : Nat.Coprime N r) (h1 : 1 ≤ r) (h2 : r ≤ N) (hx : 0 < x)
    (hcyc : x * d ((knightWord N r).rotate k) = (C ((knightWord N r).rotate k) : ℤ)) :
    N = 2 ∧ r = 1 ∧ (x = 1 ∨ x = 2) := by
  obtain ⟨rfl, rfl⟩ := Kstar_thm N r k x hcop h1 h2 hx hcyc
  refine ⟨rfl, rfl, ?_⟩
  have hw : knightWord 2 1 = [true, false] := by decide
  rw [hw, ← List.rotate_mod] at hcyc
  have hk : k % [true, false].length < 2 := by simp; omega
  interval_cases h : k % [true, false].length
  · left; simpa [d, C] using hcyc
  · right; norm_num [d, C] at hcyc; omega
