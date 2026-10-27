import Mathlib
import Logs23.Confluence

/-!
# Logs23 · the integer interpolation determinant and bounds for determinants

Columns `j` carry natural numbers `r_j ≥ 1`, `s_j < S`; for natural numbers `b₁, b₂ ≥ 1` put `θ = b₁/b₂`,
`ζ_j = r_j + s_j θ`, `Λ = b₁ log 2 − b₂ log 3`, `δ = −Λ/b₂`. The integer matrix
`M[(l,κ), j] = (r_j b₂ + s_j b₁)^κ (2^{r_j} 3^{s_j})^{l+1}` satisfies `det M = b₂^σ G(δ)`,
`G(t) = det [ζ_j^κ e^{λ_l ζ_j} e^{(l+1) s_j t}]` (`λ_l = (l+1) log 2`). With the bounds of `Logs23/Confluence.lean`
and a perturbation bound, a condition `(P)` on the parameters gives an explicit lower bound for `|Λ|`.
-/

namespace Logs23

open Matrix Finset

open scoped Nat

noncomputable section

/-! ## Bounds for determinants -/

theorem abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ) {M D : ℝ} (hM : 0 ≤ M)
    (ha : ∀ i ∈ s, |a i| ≤ M) (hb : ∀ i ∈ s, |b i| ≤ M) (hd : ∀ i ∈ s, |a i - b i| ≤ D) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ s.card * M ^ (s.card - 1) * D := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    have ha' : ∀ i ∈ s, |a i| ≤ M := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hb' : ∀ i ∈ s, |b i| ≤ M := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have hd' : ∀ i ∈ s, |a i - b i| ≤ D := fun i hi => hd i (Finset.mem_insert_of_mem hi)
    have hD : 0 ≤ D := le_trans (abs_nonneg _) (hd x (Finset.mem_insert_self x s))
    have hpb : |∏ i ∈ s, b i| ≤ M ^ s.card := by
      rw [Finset.abs_prod]
      calc ∏ i ∈ s, |b i| ≤ ∏ _i ∈ s, M := Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) hb'
        _ = M ^ s.card := Finset.prod_const _
    rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.card_insert_of_notMem hx]
    have key : a x * ∏ i ∈ s, a i - b x * ∏ i ∈ s, b i =
        a x * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a x - b x) * ∏ i ∈ s, b i := by ring
    rw [key]
    have h1 := ha x (Finset.mem_insert_self x s)
    have h2 := hd x (Finset.mem_insert_self x s)
    have ih' := ih ha' hb' hd'
    calc |a x * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a x - b x) * ∏ i ∈ s, b i|
        ≤ |a x| * |∏ i ∈ s, a i - ∏ i ∈ s, b i| + |a x - b x| * |∏ i ∈ s, b i| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ M * (s.card * M ^ (s.card - 1) * D) + D * M ^ s.card := by
          gcongr
      _ ≤ ((s.card + 1 : ℕ) : ℝ) * M ^ (s.card + 1 - 1) * D := by
          rcases Nat.eq_zero_or_pos s.card with h0 | h0
          · rw [h0]; simp
          · have : M * M ^ (s.card - 1) = M ^ s.card := by
              rw [← pow_succ']; congr 1; omega
            rw [Nat.add_sub_cancel]
            push_cast
            have e : M * (↑s.card * M ^ (s.card - 1) * D) + D * M ^ s.card =
                (↑s.card + 1) * M ^ s.card * D := by rw [← this]; ring
            rw [e]

/-- `|det A − det B| ≤ N · N! · M^(N−1) · D` when all entries are bounded by `M` and differ by at most `D`. -/
theorem abs_det_sub_det_le {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℝ) {M D : ℝ} (hM : 0 ≤ M)
    (hA : ∀ i j, |A i j| ≤ M) (hB : ∀ i j, |B i j| ≤ M) (hd : ∀ i j, |A i j - B i j| ≤ D) :
    |A.det - B.det| ≤ N * N ! * M ^ (N - 1) * D := by
  rw [det_apply', det_apply', ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ σ : Equiv.Perm (Fin N), |(↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ i, A (σ i) i -
      (↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ i, B (σ i) i| ≤ N * M ^ (N - 1) * D := by
    intro σ
    rw [← mul_sub, abs_mul]
    have hs : |((↑↑(Equiv.Perm.sign σ) : ℤ) : ℝ)| = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    rw [hs, one_mul]
    have := abs_prod_sub_prod_le (Finset.univ : Finset (Fin N)) (fun i => A (σ i) i) (fun i => B (σ i) i) hM
      (fun i _ => hA _ _) (fun i _ => hB _ _) (fun i _ => hd _ _)
    simpa using this
  calc ∑ σ : Equiv.Perm (Fin N), |(↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ i, A (σ i) i -
        (↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ i, B (σ i) i|
      ≤ ∑ _σ : Equiv.Perm (Fin N), (N * M ^ (N - 1) * D : ℝ) := Finset.sum_le_sum fun σ _ => hterm σ
    _ = N * N ! * M ^ (N - 1) * D := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- `|det A| ≤ N! · M^N` when all entries are bounded by `M`. -/
theorem abs_det_le {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) {M : ℝ} (hA : ∀ i j, |A i j| ≤ M) :
    |A.det| ≤ N ! * M ^ N := by
  have := Matrix.det_le (abv := AbsoluteValue.abs) hA
  simpa [nsmul_eq_mul] using this

/-! ## The integer matrix -/

variable {L K : ℕ}

/-- The real model `G(t)`. -/
def Gt (rr ss : Fin (L * (K + 1)) → ℕ) (θ t : ℝ) : ℝ :=
  (Matrix.of fun i j => ((rr j : ℝ) + ss j * θ) ^ ((pr i).2 : ℕ) *
    Real.exp (lam (pr i).1 * ((rr j : ℝ) + ss j * θ)) * Real.exp ((((pr i).1 : ℕ) + 1 : ℝ) * ss j * t)).det

/-- The integer matrix. -/
def Mint (rr ss : Fin (L * (K + 1)) → ℕ) (b₁ b₂ : ℕ) : Matrix (Fin (L * (K + 1))) (Fin (L * (K + 1))) ℤ :=
  Matrix.of fun i j => ((rr j * b₂ + ss j * b₁ : ℕ) : ℤ) ^ ((pr i).2 : ℕ) * (2 ^ rr j * 3 ^ ss j : ℤ) ^ (((pr i).1 : ℕ) + 1)

theorem det_Mint (rr ss : Fin (L * (K + 1)) → ℕ) (b₁ b₂ : ℕ) (hb₂ : 0 < b₂) :
    ((Mint rr ss b₁ b₂).det : ℝ) = (b₂ : ℝ) ^ sig L K *
      Gt rr ss ((b₁ : ℝ) / b₂) (-((b₁ : ℝ) * Real.log 2 - (b₂ : ℝ) * Real.log 3) / b₂) := by
  have hb : (b₂ : ℝ) ≠ 0 := by exact_mod_cast hb₂.ne'
  have hmd := RingHom.map_det (Int.castRingHom ℝ) (Mint rr ss b₁ b₂)
  simp only [eq_intCast] at hmd
  rw [hmd]
  have hmat : (Int.castRingHom ℝ).mapMatrix (Mint rr ss b₁ b₂) = Matrix.of fun i j =>
      (b₂ : ℝ) ^ ((pr i).2 : ℕ) * (Matrix.of fun i j => ((rr j : ℝ) + ss j * ((b₁ : ℝ) / b₂)) ^ ((pr i).2 : ℕ) *
        Real.exp (lam (pr i).1 * ((rr j : ℝ) + ss j * ((b₁ : ℝ) / b₂))) *
        Real.exp ((((pr i).1 : ℕ) + 1 : ℝ) * ss j *
          (-((b₁ : ℝ) * Real.log 2 - (b₂ : ℝ) * Real.log 3) / b₂))) i j := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Mint, Matrix.of_apply, eq_intCast, Int.cast_mul,
      Int.cast_pow, Int.cast_natCast, Int.cast_ofNat]
    push_cast
    -- `(r b₂ + s b₁)^κ = b₂^κ ζ^κ` and `(2^r 3^s)^(l+1) = e^{λ_l ζ} e^{(l+1) s δ}`
    have hz : ((rr j : ℝ) * b₂ + ss j * b₁) = b₂ * ((rr j : ℝ) + ss j * ((b₁ : ℝ) / b₂)) := by
      field_simp
    have he : ((2 : ℝ) ^ rr j * 3 ^ ss j) ^ (((pr i).1 : ℕ) + 1) =
        Real.exp (lam (pr i).1 * ((rr j : ℝ) + ss j * ((b₁ : ℝ) / b₂))) *
        Real.exp ((((pr i).1 : ℕ) + 1 : ℝ) * ss j * (-((b₁ : ℝ) * Real.log 2 - (b₂ : ℝ) * Real.log 3) / b₂)) := by
      rw [← Real.exp_add, ← Real.exp_log (by positivity : (0 : ℝ) < ((2 : ℝ) ^ rr j * 3 ^ ss j) ^ (((pr i).1 : ℕ) + 1))]
      congr 1
      rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, lam]
      field_simp
      push_cast
      ring
    rw [hz, mul_pow, he]
    ring
  rw [hmat, det_mul_column, Finset.prod_pow_eq_pow_sum, sig, Gt]

theorem Gt_zero (rr ss : Fin (L * (K + 1)) → ℕ) (θ : ℝ) :
    Gt rr ss θ 0 = Dc (fun j => (rr j : ℝ) + ss j * θ) 1 := by
  simp [Gt, Dc]

/-! ## The perturbation bound -/

/-- Entry bound `X(x) = (x ζ_max)^K e^{λ_max x ζ_max}`. -/
def Xb (K : ℕ) (lmax zmax x : ℝ) : ℝ := (x * zmax) ^ K * Real.exp (lmax * x * zmax)

theorem entry_le {κ : ℕ} (hκ : κ ≤ K) {lam0 lmax z zmax x : ℝ} (hx : 1 ≤ x) (hz1 : 1 ≤ z) (hz : z ≤ zmax)
    (hl0 : 0 ≤ lam0) (hl : lam0 ≤ lmax) :
    |(x * z) ^ κ * Real.exp (lam0 * (x * z))| ≤ Xb K lmax zmax x := by
  have hxz : 1 ≤ x * z := one_le_mul_of_one_le_of_one_le hx hz1
  rw [abs_of_nonneg (by positivity), Xb]
  apply mul_le_mul
  · calc (x * z) ^ κ ≤ (x * z) ^ K := pow_le_pow_right₀ hxz hκ
      _ ≤ (x * zmax) ^ K := pow_le_pow_left₀ (by linarith) (by nlinarith) K
  · apply Real.exp_le_exp.mpr
    have : x * z ≤ x * zmax := by nlinarith
    calc lam0 * (x * z) ≤ lmax * (x * z) := by nlinarith
      _ ≤ lmax * (x * zmax) := by nlinarith [le_trans hl0 hl]
      _ = lmax * x * zmax := by ring
  · positivity
  · exact pow_nonneg (by nlinarith) K

end

end Logs23
