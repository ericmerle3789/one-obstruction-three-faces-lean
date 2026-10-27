import Mathlib
import Logs23.Interpolation

/-!
# Logs23 · the main inequality (step 2b; outline in `README.md`)

If the parameters satisfy the condition `(P)`, then
`|Λ| ≥ b₂ T' / (N · N! · (3 X(1))^N · L S)`, `T' = (∏_{k<N} 1/k!) ((log 2)/2)^(tri N) |V(ζ)|`.
The case `det M = 0` is not excluded: it is harmless because `|G(0)| ≥ T' > 0`.
-/

namespace Logs23

open Matrix Finset

open scoped Nat

noncomputable section

variable {L K : ℕ}

/-- The leading lower bound `T'`. -/
def Tlow (N : ℕ) (ζ : Fin N → ℝ) : ℝ :=
  (∏ k : Fin N, (1 / ((k : ℕ)! : ℝ))) * (Real.log 2 / 2) ^ tri N * |vprod ζ|

theorem prop_main (rr ss : Fin (L * (K + 1)) → ℕ) (b₁ b₂ S : ℕ) (hb₂ : 0 < b₂)
    (hr : ∀ j, 1 ≤ rr j) (hs : ∀ j, ss j < S)
    (hinj : Function.Injective fun j => rr j * b₂ + ss j * b₁)
    {zmax lmax : ℝ} (hz : ∀ j, (rr j : ℝ) + ss j * ((b₁ : ℝ) / b₂) ≤ zmax)
    (hlmax : ∀ l : Fin L, lam l ≤ lmax)
    (hδ : (L : ℝ) * S * |((b₁ : ℝ) * Real.log 2 - (b₂ : ℝ) * Real.log 3) / b₂| ≤ 1)
    {x : ℝ} (hx : 1 ≤ x)
    (hP : ((L * (K + 1) : ℕ) ! : ℝ) * Xb K lmax zmax x ^ (L * (K + 1)) / x ^ tri (L * (K + 1)) ≤
      1 / (2 * (b₂ : ℝ) ^ sig L K)) :
    (b₂ : ℝ) * Tlow (L * (K + 1)) (fun j => (rr j : ℝ) + ss j * ((b₁ : ℝ) / b₂)) /
        ((L * (K + 1) : ℕ) * ((L * (K + 1) : ℕ) ! : ℝ) * (3 * Xb K lmax zmax 1) ^ (L * (K + 1)) * (L * S)) ≤
      |(b₁ : ℝ) * Real.log 2 - (b₂ : ℝ) * Real.log 3| := by
  set θ : ℝ := (b₁ : ℝ) / b₂ with hθ
  set ζ : Fin (L * (K + 1)) → ℝ := fun j => (rr j : ℝ) + ss j * θ with hζ
  set Λ : ℝ := (b₁ : ℝ) * Real.log 2 - (b₂ : ℝ) * Real.log 3 with hΛ
  set δ : ℝ := -Λ / b₂ with hδdef
  have hb : (0 : ℝ) < b₂ := by exact_mod_cast hb₂
  have hθ0 : 0 ≤ θ := by positivity
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- the points
  have hζ1 : ∀ j, 1 ≤ ζ j := fun j => by
    have : (1 : ℝ) ≤ rr j := by exact_mod_cast hr j
    simp only [hζ]; nlinarith [(Nat.cast_nonneg (ss j) : (0 : ℝ) ≤ ss j)]
  have hζp : ∀ j, 0 < ζ j := fun j => lt_of_lt_of_le one_pos (hζ1 j)
  have hζinj : Function.Injective ζ := by
    intro i j hij
    apply hinj
    have : ((rr i * b₂ + ss i * b₁ : ℕ) : ℝ) = ((rr j * b₂ + ss j * b₁ : ℕ) : ℝ) := by
      push_cast
      have h2 : (rr i : ℝ) * b₂ + ss i * b₁ = b₂ * ζ i := by simp only [hζ, hθ]; field_simp
      have h3 : (rr j : ℝ) * b₂ + ss j * b₁ = b₂ * ζ j := by simp only [hζ, hθ]; field_simp
      rw [h2, h3, hij]
    exact_mod_cast this
  have hlam0 : ∀ l : Fin L, 0 ≤ lam l := fun l => by simp only [lam]; positivity
  -- `|G(0)| ≤ 1/(2 b₂^σ)`
  have hG0 : Gt rr ss θ 0 = Dc ζ 1 := Gt_zero rr ss θ
  have hDx : |Dc ζ x| ≤ ((L * (K + 1)) ! : ℝ) * Xb K lmax zmax x ^ (L * (K + 1)) := by
    apply abs_det_le
    intro i j
    simp only [Matrix.of_apply]
    exact entry_le (Nat.lt_succ_iff.mp (pr i).2.2) hx (hζ1 j) (hz j) (hlam0 _) (hlmax _)
  have hup : |Gt rr ss θ 0| ≤ 1 / (2 * (b₂ : ℝ) ^ sig L K) := by
    rw [hG0]
    calc |Dc ζ 1| ≤ (x ^ tri (L * (K + 1)))⁻¹ * |Dc ζ x| := abs_Dc_le hζinj hζp hx
      _ ≤ (x ^ tri (L * (K + 1)))⁻¹ * (((L * (K + 1)) ! : ℝ) * Xb K lmax zmax x ^ (L * (K + 1))) := by gcongr
      _ = ((L * (K + 1)) ! : ℝ) * Xb K lmax zmax x ^ (L * (K + 1)) / x ^ tri (L * (K + 1)) := by ring
      _ ≤ _ := hP
  -- `|G(δ) − G(0)| ≥ |G(0)|`
  have hdet := det_Mint rr ss b₁ b₂ hb₂
  have hsep : |Gt rr ss θ 0| ≤ |Gt rr ss θ δ - Gt rr ss θ 0| := by
    by_cases hM : (Mint rr ss b₁ b₂).det = 0
    · have : Gt rr ss θ δ = 0 := by
        have h' : (b₂ : ℝ) ^ sig L K * Gt rr ss θ δ = 0 := by
          rw [← hdet]; simp [hM]
        rcases mul_eq_zero.mp h' with h | h
        · exact absurd h (by positivity)
        · exact h
      rw [this, zero_sub, abs_neg]
    · have h1 : (1 : ℝ) ≤ |((Mint rr ss b₁ b₂).det : ℝ)| := by exact_mod_cast Int.one_le_abs hM
      rw [hdet, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (b₂ : ℝ) ^ sig L K)] at h1
      have hσ : (0 : ℝ) < (b₂ : ℝ) ^ sig L K := by positivity
      have hGd : 1 / (b₂ : ℝ) ^ sig L K ≤ |Gt rr ss θ δ| := by
        rw [div_le_iff₀ hσ]; linarith
      have : |Gt rr ss θ δ| - |Gt rr ss θ 0| ≤ |Gt rr ss θ δ - Gt rr ss θ 0| := abs_sub_abs_le_abs_sub _ _
      have h2 : 1 / (2 * (b₂ : ℝ) ^ sig L K) = (1 / (b₂ : ℝ) ^ sig L K) / 2 := by ring
      rw [h2] at hup
      linarith
  -- `|G(0)| ≥ T'`
  have hlow : Tlow (L * (K + 1)) ζ ≤ |Gt rr ss θ 0| := by
    rw [hG0, Tlow]; exact abs_Dc_ge hζinj hζp
  -- the perturbation bound
  rcases Nat.eq_zero_or_pos (L * (K + 1)) with hN0 | hNpos
  · -- no rows: the left side is `0`
    have : (((L * (K + 1)) : ℕ) : ℝ) = 0 := by exact_mod_cast hN0
    rw [this, zero_mul, zero_mul, zero_mul, div_zero]
    exact abs_nonneg _
  set X1 := Xb K lmax zmax 1 with hX1
  have j0 : Fin (L * (K + 1)) := ⟨0, hNpos⟩
  have hzmax : 1 ≤ zmax := le_trans (hζ1 j0) (hz j0)
  have hX1p : 0 < X1 := by
    simp only [hX1, Xb]; exact mul_pos (pow_pos (by linarith) K) (Real.exp_pos _)
  have hentry : ∀ i j : Fin (L * (K + 1)), |ζ j ^ ((pr i).2 : ℕ) * Real.exp (lam (pr i).1 * ζ j)| ≤ X1 := by
    intro i j
    have := entry_le (Nat.lt_succ_iff.mp (pr i).2.2) le_rfl (hζ1 j) (hz j) (hlam0 (pr i).1) (hlmax (pr i).1)
    simpa using this
  have hcoef : ∀ i j : Fin (L * (K + 1)), |((((pr i).1 : ℕ) + 1 : ℝ) * ss j * δ)| ≤ (L : ℝ) * S * |δ| := by
    intro i j
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((pr i).1 : ℕ) + 1),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ss j)]
    have h1 : (((pr i).1 : ℕ) + 1 : ℝ) ≤ L := by exact_mod_cast (pr i).1.2
    have h2 : (ss j : ℝ) ≤ S := by exact_mod_cast (hs j).le
    have := abs_nonneg δ
    calc (((pr i).1 : ℕ) + 1 : ℝ) * ss j * |δ| ≤ L * ss j * |δ| := by gcongr
      _ ≤ L * S * |δ| := by gcongr
  have hδ' : (L : ℝ) * S * |δ| ≤ 1 := by
    rw [hδdef, neg_div, abs_neg]; exact hδ
  have hpert : |Gt rr ss θ δ - Gt rr ss θ 0| ≤
      ((L * (K + 1) : ℕ) : ℝ) * ((L * (K + 1)) ! : ℝ) * (3 * X1) ^ ((L * (K + 1)) - 1) * (2 * X1 * ((L : ℝ) * S * |δ|)) := by
    unfold Gt
    apply abs_det_sub_det_le
    · positivity
    · intro i j
      simp only [Matrix.of_apply]
      rw [abs_mul]
      have he : |Real.exp ((((pr i).1 : ℕ) + 1 : ℝ) * ss j * δ)| ≤ 3 := by
        rw [abs_of_pos (Real.exp_pos _)]
        calc Real.exp ((((pr i).1 : ℕ) + 1 : ℝ) * ss j * δ) ≤ Real.exp 1 :=
              Real.exp_le_exp.mpr (le_trans (le_abs_self _) ((hcoef i j).trans hδ'))
          _ ≤ 3 := Real.exp_one_lt_three.le
      calc |ζ j ^ ((pr i).2 : ℕ) * Real.exp (lam (pr i).1 * ζ j)| *
            |Real.exp ((((pr i).1 : ℕ) + 1 : ℝ) * ss j * δ)| ≤ X1 * 3 :=
            mul_le_mul (hentry i j) he (abs_nonneg _) hX1p.le
        _ = 3 * X1 := by ring
    · intro i j
      simp only [Matrix.of_apply, mul_zero, Real.exp_zero, mul_one]
      linarith [hentry i j]
    · intro i j
      simp only [Matrix.of_apply, mul_zero, Real.exp_zero, mul_one]
      rw [← mul_sub_one, abs_mul]
      have hu := Real.abs_exp_sub_one_le ((hcoef i j).trans hδ')
      calc |ζ j ^ ((pr i).2 : ℕ) * Real.exp (lam (pr i).1 * ζ j)| *
            |Real.exp ((((pr i).1 : ℕ) + 1 : ℝ) * ss j * δ) - 1|
          ≤ X1 * (2 * |(((pr i).1 : ℕ) + 1 : ℝ) * ss j * δ|) :=
            mul_le_mul (hentry i j) hu (abs_nonneg _) hX1p.le
        _ ≤ X1 * (2 * ((L : ℝ) * S * |δ|)) := by gcongr; exact hcoef i j
        _ = 2 * X1 * ((L : ℝ) * S * |δ|) := by ring
  have hpow : (3 * X1) ^ ((L * (K + 1)) - 1) * (2 * X1) ≤ (3 * X1) ^ (L * (K + 1)) := by
    have : (3 * X1) ^ (L * (K + 1)) = (3 * X1) ^ ((L * (K + 1)) - 1) * (3 * X1) := by
      rw [← pow_succ]; congr 1; omega
    rw [this]
    gcongr
    linarith
  have hchain : Tlow (L * (K + 1)) ζ ≤ ((L * (K + 1) : ℕ) : ℝ) * ((L * (K + 1)) ! : ℝ) * (3 * X1) ^ (L * (K + 1)) * ((L : ℝ) * S) * (|Λ| / b₂) := by
    have h1 := hlow.trans (hsep.trans hpert)
    have hδabs : |δ| = |Λ| / b₂ := by rw [hδdef, neg_div, abs_neg, abs_div, abs_of_pos hb]
    rw [hδabs] at h1
    calc Tlow (L * (K + 1)) ζ ≤ ((L * (K + 1) : ℕ) : ℝ) * ((L * (K + 1)) ! : ℝ) * (3 * X1) ^ ((L * (K + 1)) - 1) * (2 * X1 * ((L : ℝ) * S * (|Λ| / b₂))) := h1
      _ = ((L * (K + 1) : ℕ) : ℝ) * ((L * (K + 1)) ! : ℝ) * ((3 * X1) ^ ((L * (K + 1)) - 1) * (2 * X1)) * ((L : ℝ) * S * (|Λ| / b₂)) := by ring
      _ ≤ ((L * (K + 1) : ℕ) : ℝ) * ((L * (K + 1)) ! : ℝ) * (3 * X1) ^ (L * (K + 1)) * ((L : ℝ) * S * (|Λ| / b₂)) := by
          gcongr
      _ = ((L * (K + 1) : ℕ) : ℝ) * ((L * (K + 1)) ! : ℝ) * (3 * X1) ^ (L * (K + 1)) * ((L : ℝ) * S) * (|Λ| / b₂) := by ring
  -- conclusion
  have hLpos : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · rw [h, zero_mul] at hNpos; exact absurd hNpos (lt_irrefl 0)
    · exact h
  have hSpos : 0 < S := lt_of_le_of_lt (Nat.zero_le _) (hs j0)
  have hden : 0 < ((L * (K + 1) : ℕ) : ℝ) * ((L * (K + 1)) ! : ℝ) * (3 * X1) ^ (L * (K + 1)) * ((L : ℝ) * S) := by
    have : (0 : ℝ) < (L * (K + 1)) := by exact_mod_cast hNpos
    have : (0 : ℝ) < L := by exact_mod_cast hLpos
    have : (0 : ℝ) < S := by exact_mod_cast hSpos
    positivity
  rw [div_le_iff₀ hden]
  have := mul_le_mul_of_nonneg_left hchain hb.le
  calc (b₂ : ℝ) * Tlow (L * (K + 1)) ζ ≤ b₂ * (((L * (K + 1) : ℕ) : ℝ) * ((L * (K + 1)) ! : ℝ) * (3 * X1) ^ (L * (K + 1)) * ((L : ℝ) * S) * (|Λ| / b₂)) := this
    _ = |Λ| * (((L * (K + 1) : ℕ) : ℝ) * ((L * (K + 1)) ! : ℝ) * (3 * X1) ^ (L * (K + 1)) * ((L : ℝ) * S)) := by field_simp

end

end Logs23
