import Seifert1988.Corollaires
import Logs23.TwoLog

/-!
# Seifert 1988 · proofs (4): Corollary 1, repaired

The proof of Corollary 1 in the paper ends at `d ∣ 2^|z(1)−z(2)| − 1` (`cor1_divides`). To conclude one needs `d`
larger than `2^|z(1)−z(2)|`, that is a lower bound for `|2^l − 3^r|` (`near_miss`):

* for `r > 20000` it follows from `lam_lower` of `../logs23/`;
* for `3 ≤ r ≤ 20000` it is a finite check by the kernel, on the model of `../steiner1978/Steiner/Fini.lean`.
-/

namespace Seifert

open Function

/-! ## The finite check -/

/-- An approximation of `⌊r log₂ 3⌋ + 1` (40 digits of `log₂ 3`), re-checked by `nearOK`. -/
def Lr (r : ℕ) : ℕ := r * 1584962500721156181453738943947816508759 / 10 ^ 39 + 1

/-- `2^(M−1) ≤ 3^r < 2^M` for `M = Lr r`, and the bound at `l = M` and at `l = M − 1`. -/
def nearOK (r : ℕ) : Bool :=
  decide (2 ^ Lr r / 2 ≤ 3 ^ r) && decide (3 ^ r < 2 ^ Lr r) &&
    decide (2 ^ Lr r ≤ 2 ^ r * (2 ^ Lr r - 3 ^ r)) &&
    decide (2 ^ Lr r / 2 ≤ 2 ^ r * (3 ^ r - 2 ^ Lr r / 2))

/-- `nearOK r` for `3 ≤ r ≤ N + 2`. -/
def allNear : ℕ → Bool
  | 0 => true
  | n + 1 => nearOK (n + 3) && allNear n

theorem allNear_spec : ∀ N, allNear N = true → ∀ r, 3 ≤ r → r < N + 3 → nearOK r = true := by
  intro N
  induction N with
  | zero => intro _ r h1 h2; omega
  | succ N ih =>
    intro hN r h1 h2
    simp only [allNear, Bool.and_eq_true] at hN
    rcases Nat.lt_or_ge r (N + 3) with h | h
    · exact ih hN.2 r h1 h
    · obtain rfl : r = N + 3 := by omega
      exact hN.1

/-- **The finite check**, by the kernel. -/
theorem allNear_19998 : allNear 19998 = true := by decide +kernel

theorem nearOK_of_le {r : ℕ} (h1 : 3 ≤ r) (h2 : r ≤ 20000) : nearOK r = true :=
  allNear_spec 19998 allNear_19998 r h1 (by omega)

/-- The bound for `3 ≤ r ≤ 20000`, every `l`. -/
theorem near_small {r l : ℕ} (h1 : 3 ≤ r) (h2 : r ≤ 20000) :
    (2 : ℤ) ^ l ≤ 2 ^ r * |(2 : ℤ) ^ l - 3 ^ r| := by
  have hok := nearOK_of_le h1 h2
  simp only [nearOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hA, hB⟩, hC⟩, hD⟩ := hok
  set M := Lr r with hM
  have hM1 : 1 ≤ M := by simp [hM, Lr]
  obtain ⟨N, hN⟩ : ∃ N, M = N + 1 := ⟨M - 1, by omega⟩
  have hhalf : 2 ^ M / 2 = 2 ^ N := by rw [hN, pow_succ]; simp
  rw [hhalf] at hA hD
  have hrpos : (2 : ℤ) ≤ 2 ^ r := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) (by omega)
  have hAZ : (2 : ℤ) ^ N ≤ 3 ^ r := by exact_mod_cast hA
  have hBZ : (3 : ℤ) ^ r < 2 ^ (N + 1) := by rw [← hN]; exact_mod_cast hB
  have hCZ : (2 : ℤ) ^ (N + 1) ≤ 2 ^ r * (2 ^ (N + 1) - 3 ^ r) := by
    rw [← hN]
    have : ((2 ^ M - 3 ^ r : ℕ) : ℤ) = 2 ^ M - 3 ^ r := by
      rw [Nat.cast_sub hB.le]; push_cast; ring
    have hC' : ((2 ^ M : ℕ) : ℤ) ≤ ((2 ^ r * (2 ^ M - 3 ^ r) : ℕ) : ℤ) := by exact_mod_cast hC
    push_cast [this] at hC'
    exact hC'
  have hDZ : (2 : ℤ) ^ N ≤ 2 ^ r * (3 ^ r - 2 ^ N) := by
    have : ((3 ^ r - 2 ^ N : ℕ) : ℤ) = 3 ^ r - 2 ^ N := by
      rw [Nat.cast_sub hA]; push_cast; ring
    have hD' : ((2 ^ N : ℕ) : ℤ) ≤ ((2 ^ r * (3 ^ r - 2 ^ N) : ℕ) : ℤ) := by exact_mod_cast hD
    push_cast [this] at hD'
    exact hD'
  have hP2 : (0 : ℤ) < 2 ^ r := by positivity
  rcases lt_trichotomy l N with hl | rfl | hl
  · -- `l < N`: `2^(l+1) ≤ 2^N ≤ 3^r`
    have h3 : (2 : ℤ) ^ (l + 1) ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hl
    have h4 : (2 : ℤ) ^ (l + 1) = 2 * 2 ^ l := by ring
    have h5 : (0 : ℤ) ≤ 3 ^ r - 2 ^ l := by linarith [pow_pos (by norm_num : (0 : ℤ) < 2) l]
    rw [abs_sub_comm, abs_of_nonneg h5]
    nlinarith [pow_pos (by norm_num : (0 : ℤ) < 2) l]
  · have h5 : (0 : ℤ) ≤ 3 ^ r - 2 ^ l := by linarith
    rw [abs_sub_comm, abs_of_nonneg h5]
    exact hDZ
  · rcases Nat.lt_or_ge (N + 1) l with hl2 | hl2
    · -- `l > N + 1`: `2^l ≥ 2·2^(N+1) > 2·3^r`
      obtain ⟨t, rfl⟩ : ∃ t, l = t + 1 := ⟨l - 1, by omega⟩
      have h3 : (2 : ℤ) ^ (N + 1) ≤ 2 ^ t := pow_le_pow_right₀ (by norm_num) (by omega)
      have h4 : (2 : ℤ) ^ (t + 1) = 2 * 2 ^ t := by ring
      have h5 : (0 : ℤ) ≤ 2 ^ (t + 1) - 3 ^ r := by rw [h4]; linarith [pow_pos (by norm_num : (0 : ℤ) < 2) t]
      rw [abs_of_nonneg h5, h4]
      nlinarith [pow_pos (by norm_num : (0 : ℤ) < 2) t]
    · obtain rfl : l = N + 1 := by omega
      have h5 : (0 : ℤ) ≤ 2 ^ (N + 1) - 3 ^ r := by linarith
      rw [abs_of_nonneg h5]
      exact hCZ

/-! ## From `lam_lower` -/

/-- `1 ≤ 2^r |1 − exp(−L)|` from `1/(2^r − 1) ≤ |L|`. -/
theorem exp_gap {A L : ℝ} (hA : 0 < A) (hL : 1 / A ≤ |L|) : 1 ≤ (A + 1) * |1 - Real.exp (-L)| := by
  have hinv : 0 < 1 / A := by positivity
  rcases le_or_gt 0 L with h0 | h0
  · have hLpos : 1 / A ≤ L := by rwa [abs_of_nonneg h0] at hL
    have h1 : Real.exp (-L) ≤ 1 / (1 + L) := by
      rw [Real.exp_neg, ← one_div]
      apply one_div_le_one_div_of_le (by linarith)
      linarith [Real.add_one_le_exp L]
    have h2 : (0 : ℝ) ≤ 1 - Real.exp (-L) := by
      have : 1 / (1 + L) ≤ 1 := by
        rw [div_le_one (by linarith)]; linarith
      linarith
    rw [abs_of_nonneg h2]
    have h3 : L / (1 + L) ≤ 1 - Real.exp (-L) := by
      have : 1 - 1 / (1 + L) = L / (1 + L) := by field_simp; ring
      linarith
    have h4 : 1 / (A + 1) ≤ L / (1 + L) := by
      rw [div_le_div_iff₀ (by positivity) (by linarith)]
      have hAL : 1 ≤ A * L := by
        have := mul_le_mul_of_nonneg_left hLpos hA.le
        rwa [mul_one_div_cancel hA.ne'] at this
      nlinarith
    have h5 : 1 / (A + 1) ≤ 1 - Real.exp (-L) := h4.trans h3
    calc (1 : ℝ) = (A + 1) * (1 / (A + 1)) := by field_simp
      _ ≤ (A + 1) * (1 - Real.exp (-L)) := mul_le_mul_of_nonneg_left h5 (by positivity)
  · have hLneg : 1 / A ≤ -L := by rwa [abs_of_neg h0] at hL
    have h1 : -L + 1 ≤ Real.exp (-L) := Real.add_one_le_exp (-L)
    have h2 : 1 - Real.exp (-L) ≤ 0 := by linarith
    rw [abs_of_nonpos h2]
    have h3 : 1 / A ≤ Real.exp (-L) - 1 := by linarith
    have h4 : 1 ≤ A * (Real.exp (-L) - 1) := by
      have := mul_le_mul_of_nonneg_left h3 hA.le
      rwa [mul_one_div_cancel hA.ne'] at this
    nlinarith [Real.add_one_le_exp (-L)]

theorem near_large {r l : ℕ} (h1 : 20000 < r) (h2 : r ≤ l) :
    (2 : ℤ) ^ l ≤ 2 ^ r * |(2 : ℤ) ^ l - 3 ^ r| := by
  obtain ⟨t, rfl⟩ : ∃ t, l = r + t := ⟨l - r, by omega⟩
  have hlam := Logs23.lam_lower_thm r t h1
  have hr1 : (1 : ℝ) < 2 ^ r := one_lt_pow₀ (by norm_num) (by omega)
  have hA : (0 : ℝ) < 2 ^ r - 1 := by linarith
  have hgap := exp_gap hA hlam
  set L := Steiner.Lam r t with hL
  have hx : Real.exp (r * Real.log 3) = 3 ^ r := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hy : Real.exp (((r + t : ℕ) : ℝ) * Real.log 2) = 2 ^ (r + t) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hratio : (2 : ℝ) ^ (r + t) * Real.exp (-L) = 3 ^ r := by
    rw [← hy, ← Real.exp_add, ← hx]
    congr 1
    rw [hL, Steiner.Lam]
    ring
  have hpow : (0 : ℝ) < 2 ^ (r + t) := by positivity
  have hmain : (2 : ℝ) ^ (r + t) ≤ 2 ^ r * |(2 : ℝ) ^ (r + t) - 3 ^ r| := by
    have h3 : |(2 : ℝ) ^ (r + t) - 3 ^ r| = 2 ^ (r + t) * |1 - Real.exp (-L)| := by
      rw [← hratio]
      have : (2 : ℝ) ^ (r + t) - 2 ^ (r + t) * Real.exp (-L) = 2 ^ (r + t) * (1 - Real.exp (-L)) := by ring
      rw [this, abs_mul, abs_of_pos hpow]
    rw [h3]
    have h4 : (2 : ℝ) ^ r - 1 + 1 = 2 ^ r := by ring
    rw [h4] at hgap
    nlinarith
  exact_mod_cast hmain

theorem near_miss_thm : near_miss := by
  intro r l h3
  rcases Nat.lt_or_ge 20000 r with hbig | hsmall
  · rcases Nat.lt_or_ge l r with hl | hl
    · -- `l < r`: the distance is at least 1
      have hodd : (2 : ℤ) ^ l ≠ 3 ^ r := by
        intro h
        have h1 : (2 : ℤ) ^ l < 2 ^ r := pow_lt_pow_right₀ (by norm_num) hl
        have h2 : (2 : ℤ) ^ r ≤ 3 ^ r := pow_le_pow_left₀ (by norm_num) (by norm_num) _
        linarith
      have habs : 1 ≤ |(2 : ℤ) ^ l - 3 ^ r| := Int.one_le_abs (sub_ne_zero.mpr hodd)
      have h1 : (2 : ℤ) ^ l ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) hl.le
      nlinarith [pow_pos (by norm_num : (0 : ℤ) < 2) r]
    · exact near_large hbig hl
  · exact near_small h3 hsmall

/-! ## Corollary 1, repaired -/

theorem cor1_exact_thm : cor1_exact := by
  intro ε a b w hε h1 h2 hab
  obtain ⟨hd, _⟩ := IsLengthVector.dvd hε h1
  have hdiv := cor1_divides_thm ε a b w hε h1 h2
  obtain ⟨_, hpos⟩ := IsLengthVector.pos hε h1
  have ha : 0 < a := hpos a (by simp)
  have hb : 0 < b := hpos b (by simp)
  have hwp : ∀ x ∈ w, 1 ≤ x := fun x hx => hpos x (by simp [hx])
  have hwsum : w.length ≤ w.sum := List.length_le_sum_of_one_le w hwp
  set D := max a b - min a b with hD
  have hD1 : 1 ≤ D := by
    rcases lt_or_gt_of_ne hab with h | h
    · rw [hD, max_eq_right h.le, min_eq_left h.le]; omega
    · rw [hD, max_eq_left h.le, min_eq_right h.le]; omega
  have hDle : D + 2 ≤ a + b := by
    rcases le_total a b with h | h
    · rw [hD, max_eq_right h, min_eq_left h]; omega
    · rw [hD, max_eq_left h, min_eq_right h]; omega
  have h2D : (1 : ℤ) ≤ 2 ^ D - 1 := by
    have : (2 : ℤ) ^ 1 ≤ 2 ^ D := pow_le_pow_right₀ (by norm_num) hD1
    linarith
  have hle : d ε (a :: b :: w) ≤ 2 ^ D - 1 := Int.le_of_dvd (by linarith) hdiv
  have hsum : (a :: b :: w).sum = a + (b + w.sum) := by simp
  have hlen : (a :: b :: w).length = w.length + 2 := by simp
  have habs : d ε (a :: b :: w) = |(2 : ℤ) ^ (a :: b :: w).sum - 3 ^ (a :: b :: w).length| := by
    rcases hε with rfl | rfl
    · simp only [d, one_mul] at hd ⊢
      exact (abs_of_pos hd).symm
    · simp only [d, neg_mul, one_mul] at hd ⊢
      have : (2 : ℤ) ^ (a :: b :: w).sum - 3 ^ (a :: b :: w).length < 0 := by linarith
      rw [abs_of_neg this]
  -- `r ≥ 3` is impossible
  have hw0 : w = [] := by
    by_contra hne
    have hl : 1 ≤ w.length := List.length_pos_iff.mpr hne
    have hnear := near_miss_thm (a :: b :: w).length (a :: b :: w).sum (by rw [hlen]; omega)
    rw [← habs] at hnear
    rw [hlen] at hnear
    have hexp : w.length + 2 + D ≤ (a :: b :: w).sum := by rw [hsum]; omega
    have h3 : (2 : ℤ) ^ (w.length + 2 + D) ≤ 2 ^ (a :: b :: w).sum := pow_le_pow_right₀ (by norm_num) hexp
    have h4 : (2 : ℤ) ^ (w.length + 2) * d ε (a :: b :: w) ≤ 2 ^ (w.length + 2) * (2 ^ D - 1) :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    have h5 : (2 : ℤ) ^ (w.length + 2 + D) = 2 ^ (w.length + 2) * 2 ^ D := by rw [pow_add]
    have h6 : (0 : ℤ) < 2 ^ (w.length + 2) := by positivity
    nlinarith
  subst hw0
  -- `r = 2`
  have hs : (a :: b :: ([] : List ℕ)).sum = a + b := by simp
  have hl2 : (a :: b :: ([] : List ℕ)).length = 2 := by simp
  simp only [d, hs, hl2] at hd hle
  rcases hε with rfl | rfl
  · exfalso
    simp only [one_mul] at hd hle
    have hs4 : 4 ≤ a + b := by
      by_contra hc
      have : (2 : ℤ) ^ (a + b) ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) (by omega)
      norm_num at this hd
      linarith
    have h3 : (2 : ℤ) ^ D ≤ 2 ^ (a + b - 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h4 : (2 : ℤ) ^ (a + b) = 4 * 2 ^ (a + b - 2) := by
      obtain ⟨t, ht⟩ : ∃ t, a + b = t + 2 := ⟨a + b - 2, by omega⟩
      rw [ht, Nat.add_sub_cancel, pow_add]; ring
    have h5 : (2 : ℤ) ^ 2 ≤ 2 ^ (a + b - 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at h5 hle
    linarith
  · refine ⟨rfl, rfl, ?_⟩
    simp only [neg_mul, one_mul] at hd
    have hs3 : a + b ≤ 3 := by
      by_contra hc
      have : (2 : ℤ) ^ 4 ≤ 2 ^ (a + b) := pow_le_pow_right₀ (by norm_num) (by omega)
      norm_num at this hd
      linarith
    omega

theorem cor1_exact_anywhere_thm : cor1_exact_anywhere := by
  intro ε u a b v hε h1 h2 hab
  have r1 := IsLengthVector.rotate hε h1 u.length
  have r2 := IsLengthVector.rotate hε h2 u.length
  rw [rotate_append_length, List.cons_append, List.cons_append] at r1 r2
  obtain ⟨h3, h4, h5⟩ := cor1_exact_thm ε a b (v ++ u) hε r1 r2 hab
  obtain ⟨hv, hu⟩ := List.append_eq_nil_iff.mp h4
  exact ⟨h3, hu, hv, h5⟩

end Seifert
