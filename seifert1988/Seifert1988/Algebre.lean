import Seifert1988.Seifert_Enonces

/-!
# Seifert 1988 · proofs (1): the algebra of `e` and `d`
-/

namespace Seifert

theorem e_nil : e [] = 0 := by simp [e]

theorem e_cons (a : ℕ) (w : List ℕ) : e (a :: w) = 3 ^ w.length + 2 ^ a * e w := by
  simp only [e, List.length_cons, Finset.mul_sum]
  rw [Finset.sum_range_succ, add_comm]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < w.length := Finset.mem_range.mp hj
    have : w.length + 1 - 1 - j = (w.length - 1 - j) + 1 := by omega
    rw [this, List.take_succ_cons, List.sum_cons, pow_add]
    ring

theorem e_append (u v : List ℕ) : e (u ++ v) = 3 ^ v.length * e u + 2 ^ u.sum * e v := by
  induction u with
  | nil => simp [e_nil]
  | cons a u ih =>
    simp only [List.cons_append, e_cons, ih, List.length_append, List.sum_cons, pow_add]
    ring

theorem e_singleton (a : ℕ) : e [a] = 1 := by simp [e_cons, e_nil]

theorem e_snoc (w : List ℕ) (a : ℕ) : e (w ++ [a]) = 3 * e w + 2 ^ w.sum := by
  rw [e_append, e_singleton]; simp

theorem e_pos {z : List ℕ} (hz : z ≠ []) : 0 < e z := by
  cases z with
  | nil => exact absurd rfl hz
  | cons a w => rw [e_cons]; positivity

theorem e_odd {z : List ℕ} (hz : z ≠ []) (hp : ∀ a ∈ z, 0 < a) : Odd (e z) := by
  cases z with
  | nil => exact absurd rfl hz
  | cons a w =>
    rw [e_cons]
    have ha : 0 < a := hp a (by simp)
    have h1 : Odd (3 ^ w.length) := (by decide : Odd 3).pow
    have h2 : Even (2 ^ a * e w) := by
      obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      exact ⟨2 ^ b * e w, by ring⟩
    exact h1.add_even h2

theorem IsSign.sq {ε : ℤ} (h : IsSign ε) : ε * ε = 1 := by
  rcases h with rfl | rfl <;> norm_num

theorem d_rotate (ε : ℤ) (z : List ℕ) (k : ℕ) : d ε (z.rotate k) = d ε z := by
  simp only [d, List.length_rotate, (List.rotate_perm z k).sum_eq]

theorem d_perm_thm : d_perm := by
  intro ε z z' h
  simp only [d, h.sum_eq, h.length_eq]

theorem d_neg_thm : d_neg := by
  intro z; simp only [d]; ring

/-- The transport identity behind Theorem 1: one step of the orbit in terms of `e` and `d`. -/
theorem transport {ε : ℤ} (hε : IsSign ε) (a : ℕ) (w : List ℕ) :
    (2 : ℤ) ^ a * (e (w ++ [a]) : ℤ) = 3 * (e (a :: w) : ℤ) + ε * d ε (a :: w) := by
  have h := hε.sq
  simp only [e_snoc, e_cons, d, List.sum_cons, List.length_cons]
  push_cast
  have : ε * (ε * ((2 : ℤ) ^ (a + w.sum) - 3 ^ (w.length + 1))) = (ε * ε) * ((2 : ℤ) ^ (a + w.sum) - 3 ^ (w.length + 1)) := by
    ring
  rw [this, h, pow_add, pow_succ]
  ring

theorem rotate_one_cons (a : ℕ) (w : List ℕ) : (a :: w).rotate 1 = w ++ [a] := by
  simp [List.rotate_cons_succ]

/-- `d` is odd, and prime to 3, on a non-empty vector with positive coordinates. -/
theorem d_coprime_two {ε : ℤ} (hε : IsSign ε) {z : List ℕ} (hz : z ≠ []) (hp : ∀ a ∈ z, 0 < a) :
    IsCoprime (d ε z) 2 := by
  have hs : 0 < z.sum := by
    cases z with
    | nil => exact absurd rfl hz
    | cons a w => have := hp a (by simp); simp only [List.sum_cons]; omega
  obtain ⟨s, hs'⟩ : ∃ s, z.sum = s + 1 := ⟨z.sum - 1, by omega⟩
  have hodd : Odd (d ε z) := by
    have h3 : Odd ((3 : ℤ) ^ z.length) := (by decide : Odd (3 : ℤ)).pow
    have h2 : Even ((2 : ℤ) ^ z.sum) := by rw [hs', pow_succ]; exact ⟨2 ^ s, by ring⟩
    have : Odd ((2 : ℤ) ^ z.sum - 3 ^ z.length) := h2.sub_odd h3
    rcases hε with rfl | rfl
    · simpa [d] using this
    · simpa [d] using this.neg
  obtain ⟨c, hc⟩ := hodd
  exact ⟨1, -c, by rw [hc]; ring⟩

theorem d_coprime_three {ε : ℤ} (hε : IsSign ε) {z : List ℕ} (hz : z ≠ []) : IsCoprime (d ε z) 3 := by
  have hl : 0 < z.length := List.length_pos_iff.mpr hz
  have hp3 : Prime (3 : ℤ) := by norm_num
  have h2 : IsCoprime ((2 : ℤ) ^ z.sum) 3 := by
    apply IsCoprime.pow_left; exact ⟨-1, 1, by norm_num⟩
  have h3 : (3 : ℤ) ∣ 3 ^ z.length := dvd_pow_self _ hl.ne'
  obtain ⟨c, hc⟩ := h3
  have hsub : IsCoprime ((2 : ℤ) ^ z.sum - 3 ^ z.length) 3 := by
    rw [hc]
    have : (2 : ℤ) ^ z.sum - 3 * c = (2 : ℤ) ^ z.sum + 3 * (-c) := by ring
    rw [this]
    exact IsCoprime.add_mul_left_left h2 (-c)
  rcases hε with rfl | rfl
  · simpa [d] using hsub
  · simpa [d] using hsub.neg_left

/-- One divisibility propagates to all the rotations. -/
theorem dvd_rotate {ε : ℤ} (hε : IsSign ε) {z : List ℕ} (hz : z ≠ []) (hp : ∀ a ∈ z, 0 < a)
    (h : d ε z ∣ (e z : ℤ)) (k : ℕ) : d ε z ∣ (e (z.rotate k) : ℤ) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have hne : z.rotate k ≠ [] := by simpa [List.rotate_eq_nil_iff] using hz
    obtain ⟨a, w, hw⟩ := List.exists_cons_of_ne_nil hne
    have hstep : z.rotate (k + 1) = w ++ [a] := by
      rw [← List.rotate_rotate, hw, rotate_one_cons]
    have ht := transport hε a w
    have hd : d ε (a :: w) = d ε z := by rw [← hw, d_rotate]
    rw [hd] at ht
    rw [hw] at ih
    have h1 : d ε z ∣ (2 : ℤ) ^ a * (e (w ++ [a]) : ℤ) := by
      rw [ht]; exact dvd_add (Dvd.dvd.mul_left ih 3) (Dvd.intro_left ε rfl)
    have hc : IsCoprime (d ε z) ((2 : ℤ) ^ a) := (d_coprime_two hε hz hp).pow_right
    rw [hstep]
    exact hc.dvd_of_dvd_mul_left h1

/-- The difference in the proof of Corollary 1, for `e`. -/
theorem cor1_difference_thm : cor1_difference := by
  intro a b w
  simp only [e_cons, List.length_cons]
  push_cast
  ring

theorem rotate_append_length (u v : List ℕ) : (u ++ v).rotate u.length = v ++ u :=
  List.rotate_append_length_eq u v

end Seifert
