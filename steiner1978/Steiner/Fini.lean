import Mathlib

/-!
# Steiner 1978 · proofs (2): the finite check, `2 ≤ k ≤ 20000`

For each `k`, a positive solution of Davison's equation forces `0 < 2^L − 3^k` and
`(2^L − 3^k)(2^k − 1) ≤ 3^k − 2^k` (`L = k + l`); a negative one forces `0 < 3^k − 2^L` and
`(3^k − 2^L)(2^k + 1) ≤ 3^k − 2^k`. Each inequality leaves one possible `L`, and `chk k` tests it.

`Lk k` approximates `⌊k log₂ 3⌋ + 1` through 40 digits of `log₂ 3`; `posOK` re-checks `2^(Lk−1) ≤ 3^k < 2^Lk`,
so a wrong approximation could only make the computation fail. The computation is checked by the kernel
(`decide +kernel`); `Nat.log2` is avoided: in our tests its kernel evaluation was slow on large numbers.
-/

namespace Steiner

/-- An approximation of `⌊k log₂ 3⌋ + 1` (40 digits of `log₂ 3`), re-checked by `posOK`. -/
def Lk (k : ℕ) : ℕ := k * 1584962500721156181453738943947816508759 / 10 ^ 39 + 1

/-- Positive side: `2^(Lk−1) ≤ 3^k < 2^Lk` and `(2^Lk − 3^k)(2^k − 1) > 3^k − 2^k`. -/
def posOK (k : ℕ) : Bool :=
  decide (2 ^ Lk k / 2 ≤ 3 ^ k) && decide (3 ^ k < 2 ^ Lk k) &&
    decide (3 ^ k - 2 ^ k < (2 ^ Lk k - 3 ^ k) * (2 ^ k - 1))

/-- Negative side: `2^(Lk−1) < 3^k` and `(3^k − 2^(Lk−1))(2^k + 1) > 3^k − 2^k`. -/
def negOK (k : ℕ) : Bool :=
  decide (2 ^ Lk k / 2 < 3 ^ k) && decide (3 ^ k - 2 ^ k < (3 ^ k - 2 ^ Lk k / 2) * (2 ^ k + 1))

/-- The test for one `k`; the negative side is skipped at `k = 2` (the solution `(2, 1, −1)`). -/
def chk (k : ℕ) : Bool := posOK k && (k == 2 || negOK k)

/-- `chk k` for `2 ≤ k ≤ N`. -/
def allChk : ℕ → Bool
  | 0 => true
  | 1 => true
  | n + 2 => chk (n + 2) && allChk (n + 1)

theorem allChk_spec : ∀ N, allChk N = true → ∀ k, 2 ≤ k → k ≤ N → chk k = true := by
  intro N
  induction N with
  | zero => intro _ k h1 h2; omega
  | succ N ih =>
    intro hN k h1 h2
    match N, hN, ih with
    | 0, _, _ => omega
    | N + 1, hN, ih =>
      simp only [allChk, Bool.and_eq_true] at hN
      rcases Nat.lt_or_ge k (N + 2) with h | h
      · exact ih hN.2 k h1 (by omega)
      · obtain rfl : k = N + 2 := by omega
        exact hN.1

/-- **The finite check**, by the kernel. -/
theorem allChk_20000 : allChk 20000 = true := by decide +kernel

theorem chk_of_le {k : ℕ} (h1 : 2 ≤ k) (h2 : k ≤ 20000) : chk k = true :=
  allChk_spec 20000 allChk_20000 k h1 h2

theorem pow_half {M : ℕ} (h : 1 ≤ M) : 2 ^ M / 2 = 2 ^ (M - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, M = j + 1 := ⟨M - 1, by omega⟩
  simp [pow_succ]

/-- `posOK` excludes every `L` with `3^k < 2^L` and `(2^L − 3^k)(2^k − 1) ≤ 3^k − 2^k`. -/
theorem pos_exclude {k L : ℕ} (hk : 1 ≤ k) (hok : posOK k = true) (h1 : 3 ^ k < 2 ^ L)
    (h2 : (2 ^ L - 3 ^ k) * (2 ^ k - 1) ≤ 3 ^ k - 2 ^ k) : False := by
  simp only [posOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hA, hB⟩, hC⟩ := hok
  set M := Lk k with hM
  have hM1 : 1 ≤ M := by simp [hM, Lk]
  have hhalf : 2 ^ M / 2 = 2 ^ (M - 1) := pow_half hM1
  rw [hhalf] at hA
  have hs : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  -- `M ≤ L`
  have hML : M ≤ L := by
    by_contra hlt
    have : 2 ^ L ≤ 2 ^ (M - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rcases Nat.eq_or_lt_of_le hML with heq | hlt
  · subst heq; omega
  · -- `2^L ≥ 2·2^M > 2·3^k`
    have : 2 ^ (M + 1) ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hlt
    rw [pow_succ] at this
    have h3 : 3 ^ k - 2 ^ k < 2 ^ L - 3 ^ k := by omega
    have h4 : 2 ^ L - 3 ^ k ≤ (2 ^ L - 3 ^ k) * (2 ^ k - 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega

/-- `posOK` and `negOK` exclude every `L` with `2^L < 3^k` and `(3^k − 2^L)(2^k + 1) ≤ 3^k − 2^k`. -/
theorem neg_exclude {k L : ℕ} (hk : 1 ≤ k) (hok : posOK k = true) (hneg : negOK k = true)
    (h1 : 2 ^ L < 3 ^ k) (h2 : (3 ^ k - 2 ^ L) * (2 ^ k + 1) ≤ 3 ^ k - 2 ^ k) : False := by
  simp only [posOK, negOK, Bool.and_eq_true, decide_eq_true_eq] at hok hneg
  obtain ⟨⟨hA, hB⟩, -⟩ := hok
  obtain ⟨-, hD⟩ := hneg
  set M := Lk k with hM
  have hM1 : 1 ≤ M := by simp [hM, Lk]
  have hhalf : 2 ^ M / 2 = 2 ^ (M - 1) := pow_half hM1
  rw [hhalf] at hA hD
  have hs : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  -- `3^k < 2^(L+1)`: otherwise `3^k − 2^L ≥ 3^k/2` and the inequality fails
  have hL1 : 3 ^ k < 2 ^ (L + 1) := by
    by_contra hge
    rw [not_lt] at hge
    rw [pow_succ] at hge
    have h5 : (3 ^ k - 2 ^ L) * 3 ≤ (3 ^ k - 2 ^ L) * (2 ^ k + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  -- `L < M` and `M − 1 ≤ L`, so `L = M − 1`
  have hLM : L < M := by
    by_contra hge
    rw [not_lt] at hge
    have : 2 ^ M ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hge
    omega
  have hML : M - 1 ≤ L := by
    by_contra hlt
    rw [not_le] at hlt
    have : 2 ^ (L + 1) ≤ 2 ^ (M - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain rfl : L = M - 1 := by omega
  omega

end Steiner
