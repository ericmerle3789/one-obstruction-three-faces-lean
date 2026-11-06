import Seifert1988.Dynamique

/-!
# Seifert 1988 · proofs (3): the examples, the printed formula, Corollaries 1 and 2 up to the arithmetic of
`Seifert1988/Voisins.lean`, Theorem 2
-/

namespace Seifert

open Function

/-! ## A cycle from a vector -/

/-- A free vector with `d > 0` and `d ∣ e` is the length vector of `e / d`. -/
theorem cycle_of_free {ε : ℤ} (hε : IsSign ε) {z : List ℕ} (hz : z ≠ []) (hp : ∀ a ∈ z, 0 < a)
    (hfree : Free z) (hd : 0 < d ε z) (hdvd : d ε z ∣ (e z : ℤ)) {n : ℤ} (hn : d ε z * n = e z) :
    IsCyclic ε n ∧ lengthVector ε n = z := by
  have h := exists_cycle hε hz hp hd hdvd hfree
  have h0 : pt ε z 0 = n := by
    apply mul_left_cancel₀ hd.ne'
    rw [pt_mul hε hz hp hdvd 0, hn]; simp
  rwa [h0] at h

theorem free_12 : Free [1, 2] := by
  intro k h0 h1 h
  have : k = 1 := by simp at h1; omega
  subst this; simp at h

theorem free_21 : Free [2, 1] := by
  intro k h0 h1 h
  have : k = 1 := by simp at h1; omega
  subst this; simp at h

theorem free_17 : Free [1, 1, 1, 2, 1, 1, 4] := by
  intro k h0 h1 h
  simp at h1
  interval_cases k <;> simp at h

theorem free_singleton (a : ℕ) : Free [a] := by
  intro k h0 h1
  simp at h1; omega

theorem sign_plus : IsSign 1 := Or.inl rfl
theorem sign_minus : IsSign (-1) := Or.inr rfl

theorem cyc5 : IsCyclic (-1) 5 ∧ lengthVector (-1) 5 = [1, 2] :=
  cycle_of_free sign_minus (by simp) (by simp) free_12 (by norm_num [d]) (by simp [d, e_cons, e_nil])
    (by norm_num [d, e_cons, e_nil])

theorem cyc7 : IsCyclic (-1) 7 ∧ lengthVector (-1) 7 = [2, 1] :=
  cycle_of_free sign_minus (by simp) (by simp) free_21 (by norm_num [d]) (by simp [d, e_cons, e_nil])
    (by norm_num [d, e_cons, e_nil])

theorem cyc17 : IsCyclic (-1) 17 ∧ lengthVector (-1) 17 = [1, 1, 1, 2, 1, 1, 4] :=
  cycle_of_free sign_minus (by simp) (by simp) free_17 (by norm_num [d])
    ⟨17, by norm_num [d, e_cons, e_nil]⟩ (by norm_num [d, e_cons, e_nil])

theorem cyc1_plus : IsCyclic 1 1 ∧ lengthVector 1 1 = [2] :=
  cycle_of_free sign_plus (by simp) (by simp) (free_singleton 2) (by norm_num [d])
    (by simp [d, e_cons, e_nil]) (by norm_num [d, e_cons, e_nil])

theorem cyc1_minus : IsCyclic (-1) 1 ∧ lengthVector (-1) 1 = [1] :=
  cycle_of_free sign_minus (by simp) (by simp) (free_singleton 1) (by norm_num [d])
    (by simp [d, e_cons, e_nil]) (by norm_num [d, e_cons, e_nil])

theorem examples_thm : examples := by
  refine ⟨cyc5.1, cyc5.2, by simp [e_cons, e_nil], by norm_num [d], cyc17.1, cyc17.2,
    by norm_num [e_cons, e_nil], by norm_num [d], cyc1_plus.1, cyc1_plus.2, cyc1_minus.1, cyc1_minus.2⟩

theorem free_essential_thm : free_essential := by
  refine ⟨by norm_num [d], by norm_num [d, e_cons, e_nil], ?_⟩
  rintro ⟨n, hn, hv⟩
  have hf := free_lengthVector sign_minus hn
  rw [hv] at hf
  exact hf 1 (by norm_num) (by simp) (by simp)

theorem e_ones (r : ℕ) : (e (List.replicate r 1) : ℤ) = 3 ^ r - 2 ^ r := by
  induction r with
  | zero => simp [e_nil]
  | succ r ih =>
    rw [List.replicate_succ, e_cons]
    push_cast
    rw [ih, List.length_replicate, pow_succ, pow_succ]
    ring

theorem e_twos (r : ℕ) : (e (List.replicate r 2) : ℤ) = 4 ^ r - 3 ^ r := by
  induction r with
  | zero => simp [e_nil]
  | succ r ih =>
    rw [List.replicate_succ, e_cons]
    push_cast
    rw [ih, List.length_replicate, pow_succ, pow_succ]
    ring

theorem remark_constant_thm : remark_constant := by
  intro r _
  refine ⟨e_ones r, ?_, ?_, ?_⟩
  · simp [d, List.sum_replicate]
  · simp [d, List.sum_replicate]
  · rw [e_twos]
    simp only [d, List.sum_replicate, List.length_replicate, smul_eq_mul, one_mul]
    rw [mul_comm r 2, pow_mul]
    norm_num

/-! ## The printed formula -/

theorem printed_e_reverse_thm : printed_e_reverse := by
  intro z
  simp only [ePrinted, e, List.length_reverse]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < z.length := Finset.mem_range.mp hj
  have h1 : z.length - (z.length - 1 - j) = j + 1 := by omega
  rw [List.take_reverse, h1, List.sum_reverse]

theorem printed_e_examples_thm : printed_e_examples := by
  refine ⟨by decide, by decide, by norm_num⟩

theorem thm1b_printed_false_thm : thm1b_printed_false := by
  intro h
  have h1 := h _ ⟨17, cyc17.1, cyc17.2⟩ 0
  rw [List.rotate_zero] at h1
  have h2 : ePrinted [1, 1, 1, 2, 1, 1, 4] = 13801 := by decide
  rw [h2] at h1
  have h3 : d (-1) [1, 1, 1, 2, 1, 1, 4] = 139 := by norm_num [d]
  rw [h3] at h1
  norm_num at h1

theorem free_reverse {z : List ℕ} (h : Free z) : Free z.reverse := by
  intro k h0 h1 hk
  rw [List.length_reverse] at h1
  have h2 := congrArg List.reverse hk
  rw [List.reverse_rotate, List.reverse_reverse, List.length_reverse, Nat.mod_eq_of_lt (by simpa using h1)] at h2
  exact h (z.length - k) (by omega) (by omega) h2

theorem thm1b_reversed_thm : thm1b_reversed := by
  intro ε z hε hz hp
  have hz' : z.reverse ≠ [] := by simpa using hz
  have hp' : ∀ a ∈ z.reverse, 0 < a := fun a ha => hp a (by simpa using ha)
  have hdd : d ε z.reverse = d ε z := d_perm_thm ε _ _ (List.reverse_perm z)
  rw [thm1b_single_thm ε _ hε hz' hp', hdd]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by simpa using free_reverse h1, h2, fun k => ?_⟩
    rw [printed_e_reverse_thm, List.reverse_rotate]
    rw [← hdd] at h3 ⊢
    exact dvd_rotate hε hz' hp' h3 _
  · rintro ⟨h1, h2, h3⟩
    refine ⟨free_reverse h1, h2, ?_⟩
    have := h3 0
    rwa [List.rotate_zero, printed_e_reverse_thm] at this

/-! ## Corollary 1: what its proof gives -/

theorem cor1_difference_printed_thm : cor1_difference_printed := by
  intro a b w
  have hr : ∀ z, ePrinted z = e z.reverse := printed_e_reverse_thm
  simp only [hr, List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
  rw [e_append, e_append]
  simp only [e_cons, e_nil, List.length_cons, List.length_nil, List.sum_reverse]
  push_cast
  ring

theorem cor1_printed_false_thm : cor1_printed_false := by
  intro h
  exact h (-1) 1 2 [] sign_minus ⟨5, cyc5.1, cyc5.2⟩ (by simp) ⟨7, cyc7.1, cyc7.2⟩

theorem IsLengthVector.dvd {ε : ℤ} (hε : IsSign ε) {z : List ℕ} (h : IsLengthVector ε z) :
    0 < d ε z ∧ d ε z ∣ (e z : ℤ) := by
  obtain ⟨n, hn, rfl⟩ := h
  exact ⟨d_lengthVector_pos hε hn, n, (formula_1_2'_thm ε n hε hn).symm⟩

theorem IsLengthVector.pos {ε : ℤ} (hε : IsSign ε) {z : List ℕ} (h : IsLengthVector ε z) :
    z ≠ [] ∧ ∀ a ∈ z, 0 < a := by
  obtain ⟨n, hn, rfl⟩ := h
  exact lengthVector_pos_thm ε n hε hn

theorem IsLengthVector.rotate {ε : ℤ} (hε : IsSign ε) {z : List ℕ} (h : IsLengthVector ε z) (k : ℕ) :
    IsLengthVector ε (z.rotate k) := by
  obtain ⟨n, hn, rfl⟩ := h
  obtain ⟨h1, h2⟩ := thm1a_rotate_thm ε n k hε hn
  exact ⟨_, h1, h2⟩

theorem cor1_divides_thm : cor1_divides := by
  intro ε a b w hε h1 h2
  obtain ⟨hd1, hdv1⟩ := IsLengthVector.dvd hε h1
  obtain ⟨_, hdv2⟩ := IsLengthVector.dvd hε h2
  have hne : a :: b :: w ≠ [] := by simp
  have hdd : d ε (b :: a :: w) = d ε (a :: b :: w) := d_perm_thm ε _ _ (List.Perm.swap _ _ _)
  rw [hdd] at hdv2
  have hdiff : d ε (a :: b :: w) ∣ ((2 : ℤ) ^ a - 2 ^ b) * 3 ^ w.length := by
    rw [← cor1_difference_thm a b w]; exact dvd_sub hdv1 hdv2
  have hc3 : IsCoprime (d ε (a :: b :: w)) ((3 : ℤ) ^ w.length) := (d_coprime_three hε hne).pow_right
  have h3 : d ε (a :: b :: w) ∣ (2 : ℤ) ^ a - 2 ^ b := hc3.dvd_of_dvd_mul_right hdiff
  have hc2 := d_coprime_two hε hne (IsLengthVector.pos hε h1).2
  rcases le_total a b with hab | hab
  · rw [max_eq_right hab, min_eq_left hab]
    obtain ⟨t, rfl⟩ : ∃ t, b = a + t := ⟨b - a, by omega⟩
    have h4 : (2 : ℤ) ^ a - 2 ^ (a + t) = (2 : ℤ) ^ a * (-(2 ^ t - 1)) := by rw [pow_add]; ring
    rw [h4] at h3
    have h5 := (hc2.pow_right (n := a)).dvd_of_dvd_mul_left h3
    rw [Nat.add_sub_cancel_left]
    exact (dvd_neg.mp h5)
  · rw [max_eq_left hab, min_eq_right hab]
    obtain ⟨t, rfl⟩ : ∃ t, a = b + t := ⟨a - b, by omega⟩
    have h4 : (2 : ℤ) ^ (b + t) - 2 ^ b = (2 : ℤ) ^ b * (2 ^ t - 1) := by rw [pow_add]; ring
    rw [h4] at h3
    rw [Nat.add_sub_cancel_left]
    exact (hc2.pow_right (n := b)).dvd_of_dvd_mul_left h3

/-! ## Corollary 2 -/

theorem three_pow_mod_even (s : ℕ) : (3 : ℕ) ^ (2 * s) % 8 = 1 := by
  induction s with
  | zero => rfl
  | succ s ih =>
    have : (3 : ℕ) ^ (2 * (s + 1)) = 3 ^ (2 * s) * 9 := by ring
    omega

theorem three_pow_mod_odd (s : ℕ) : (3 : ℕ) ^ (2 * s + 1) % 8 = 3 := by
  have : (3 : ℕ) ^ (2 * s + 1) = 3 ^ (2 * s) * 3 := by ring
  have := three_pow_mod_even s
  omega

theorem three_pow_ge (r : ℕ) (hr : 2 ≤ r) : 3 ^ r ≥ 2 ^ r + 5 := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r _ ih => rw [pow_succ, pow_succ]; omega

/-- `2^l = 3^r + 1` with `r > 0`. -/
theorem gers_plus_nat {l r : ℕ} (hr : 0 < r) (h : 2 ^ l = 3 ^ r + 1) : l = 2 ∧ r = 1 := by
  have hmod : 3 ^ r % 8 = 1 ∨ 3 ^ r % 8 = 3 := by
    rcases Nat.even_or_odd' r with ⟨s, rfl | rfl⟩
    · exact Or.inl (three_pow_mod_even s)
    · exact Or.inr (three_pow_mod_odd s)
  have hge : 3 ≤ 3 ^ r := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ r := Nat.pow_le_pow_right (by norm_num) hr
  have hl : l < 3 := by
    by_contra hc
    obtain ⟨t, rfl⟩ : ∃ t, l = t + 3 := ⟨l - 3, by omega⟩
    have : 2 ^ (t + 3) = 2 ^ t * 8 := by ring
    omega
  interval_cases l
  · omega
  · omega
  · refine ⟨rfl, ?_⟩
    have h3 : 3 ^ r = 3 ^ 1 := by omega
    exact Nat.pow_right_injective (by norm_num) h3

/-- `3^r = 2^l + 1` with `l, r > 0`. -/
theorem gers_minus_nat {l r : ℕ} (hl0 : 0 < l) (hr : 0 < r) (h : 3 ^ r = 2 ^ l + 1) :
    (l = 1 ∧ r = 1) ∨ (l = 3 ∧ r = 2) := by
  rcases Nat.even_or_odd' r with ⟨s, rfl | rfl⟩
  · -- `r = 2s`: `3^s + 1` divides `2^l`
    have hs : 0 < s := by omega
    have hge : 3 ≤ 3 ^ s := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ s := Nat.pow_le_pow_right (by norm_num) hs
    have hfac : (3 ^ s + 1) * (3 ^ s - 1) = 2 ^ l := by
      obtain ⟨x, hx⟩ : ∃ x, 3 ^ s = x + 1 := ⟨3 ^ s - 1, by omega⟩
      have hsq : 3 ^ (2 * s) = (3 ^ s) ^ 2 := by rw [mul_comm, pow_mul]
      rw [hsq, hx] at h
      rw [hx, Nat.add_sub_cancel]
      nlinarith
    obtain ⟨q, _, hq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro _ hfac)
    obtain ⟨_, rfl⟩ := gers_plus_nat hs hq.symm
    right
    refine ⟨?_, rfl⟩
    have h8 : 2 ^ l = 2 ^ 3 := by norm_num at h ⊢; omega
    exact Nat.pow_right_injective (by norm_num) h8
  · -- `r` odd: `2^l ≡ 2` modulo 8
    have hmod := three_pow_mod_odd s
    have hl : l = 1 := by
      by_contra hc
      have h2 : 2 ≤ l := by omega
      obtain ⟨t, rfl⟩ : ∃ t, l = t + 2 := ⟨l - 2, by omega⟩
      have h4 : 2 ^ (t + 2) = 2 ^ t * 4 := by ring
      rcases t with _ | t
      · norm_num at h; omega
      · have h5 : 2 ^ (t + 1) = 2 ^ t * 2 := by ring
        omega
    subst hl
    left
    refine ⟨rfl, ?_⟩
    have h3 : 3 ^ (2 * s + 1) = 3 ^ 1 := by norm_num at h ⊢; omega
    exact Nat.pow_right_injective (by norm_num) h3

theorem gersonides_plus_thm : gersonides_plus := by
  intro l r hr h
  apply gers_plus_nat hr
  have : (2 : ℤ) ^ l = 3 ^ r + 1 := by linarith
  exact_mod_cast this

theorem gersonides_minus_thm : gersonides_minus := by
  intro l r hl hr h
  apply gers_minus_nat hl hr
  have : (3 : ℤ) ^ r = 2 ^ l + 1 := by linarith
  exact_mod_cast this

theorem solution_gives_cycle_thm : solution_gives_cycle := by
  intro ε l r hε hr h
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  -- `l > r`
  have hlr : m + 2 < l := by
    have hge := three_pow_ge (m + 2) hr
    have hge' : (3 : ℤ) ^ (m + 2) ≥ 2 ^ (m + 2) + 5 := by exact_mod_cast hge
    have hlt : (2 : ℤ) ^ (m + 2) < 2 ^ l := by rcases hε with rfl | rfl <;> linarith
    have hlt' : 2 ^ (m + 2) < 2 ^ l := by exact_mod_cast hlt
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt'
  set a := l - (m + 2) + 1 with ha
  have ha2 : 2 ≤ a := by omega
  have hrr : m + 2 - 1 = m + 1 := by omega
  rw [hrr]
  set z := a :: List.replicate (m + 1) 1 with hz
  have hsum : z.sum = l := by
    simp [hz, List.sum_replicate]; omega
  have hlen : z.length = m + 2 := by simp [hz]
  have hd : d ε z = 1 := by
    simp only [d, hsum, hlen, h]; exact hε.sq
  have hne : z ≠ [] := by simp [hz]
  have hpos : ∀ x ∈ z, 0 < x := by
    intro x hx
    simp only [hz, List.mem_cons, List.mem_replicate] at hx
    rcases hx with rfl | ⟨_, rfl⟩ <;> omega
  have hfree : Free z := by
    intro k h0 h1 hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hh := congrArg List.head? hk
    rw [List.head?_rotate h1] at hh
    have hk' : k' < m + 1 := by rw [hlen] at h1; omega
    simp [hz, hk'] at hh
    omega
  have hdvd : d ε z ∣ (e z : ℤ) := by rw [hd]; exact one_dvd _
  exact ⟨_, exists_cycle hε hne hpos (by rw [hd]; norm_num) hdvd hfree⟩

theorem f_one : f 1 1 = 1 := f_eq (m := 1) (a := 2) (by decide) (by norm_num)

theorem cor2_plus_thm : cor2_plus := by
  intro hS l r hl hr h
  by_cases hr1 : r = 1
  · subst hr1
    have h4 : 2 ^ l = 2 ^ 2 := by
      have : (2 : ℤ) ^ l = 4 := by linarith
      norm_num; exact_mod_cast this
    exact ⟨Nat.pow_right_injective (by norm_num) h4, rfl⟩
  · exfalso
    obtain ⟨n, hn, hv⟩ := solution_gives_cycle_thm 1 l r sign_plus (by omega) h
    obtain ⟨k, hk⟩ := hS n hn.1
    have h1 : minimalPeriod (f 1) ((f 1)^[k] n) = minimalPeriod (f 1) n := minimalPeriod_apply_iterate hn.mem k
    have h2 : minimalPeriod (f 1) (1 : ℤ) = 1 := minimalPeriod_eq_one_iff_isFixedPt.mpr f_one
    have h3 := lengthVector_length 1 n
    rw [hv] at h3
    rw [hk, h2] at h1
    have h4 : r - 1 + 1 = r := by omega
    simp [h4] at h3
    omega

/-- The minimal periods of the points of the three cycles of (S'). -/
theorem period_list {x : ℤ} (hx : x ∈ ({1, 5, 7, 17, 25, 37, 55, 41, 61, 91} : Set ℤ)) :
    minimalPeriod (f (-1)) x = 1 ∨ minimalPeriod (f (-1)) x = 2 ∨ minimalPeriod (f (-1)) x = 7 := by
  have p1 : minimalPeriod (f (-1)) (1 : ℤ) = 1 := by
    have := lengthVector_length (-1) 1; rw [cyc1_minus.2] at this; simpa using this.symm
  have p5 : minimalPeriod (f (-1)) (5 : ℤ) = 2 := by
    have := lengthVector_length (-1) 5; rw [cyc5.2] at this; simpa using this.symm
  have p7 : minimalPeriod (f (-1)) (7 : ℤ) = 2 := by
    have := lengthVector_length (-1) 7; rw [cyc7.2] at this; simpa using this.symm
  have p17 : minimalPeriod (f (-1)) (17 : ℤ) = 7 := by
    have := lengthVector_length (-1) 17; rw [cyc17.2] at this; simpa using this.symm
  have hmem := cyc17.1.mem
  have s1 : f (-1) 17 = 25 := f_eq (a := 1) (by decide) (by norm_num)
  have s2 : f (-1) 25 = 37 := f_eq (a := 1) (by decide) (by norm_num)
  have s3 : f (-1) 37 = 55 := f_eq (a := 1) (by decide) (by norm_num)
  have s4 : f (-1) 55 = 41 := f_eq (a := 2) (by decide) (by norm_num)
  have s5 : f (-1) 41 = 61 := f_eq (a := 1) (by decide) (by norm_num)
  have s6 : f (-1) 61 = 91 := f_eq (a := 1) (by decide) (by norm_num)
  have q : ∀ (i : ℕ) (y : ℤ), (f (-1))^[i] 17 = y → minimalPeriod (f (-1)) y = 7 := by
    intro i y hy
    rw [← hy, minimalPeriod_apply_iterate hmem i, p17]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl p1
  · exact Or.inr (Or.inl p5)
  · exact Or.inr (Or.inl p7)
  · exact Or.inr (Or.inr p17)
  · exact Or.inr (Or.inr (q 1 _ s1))
  · exact Or.inr (Or.inr (q 2 _ (by simp [iterate_succ_apply', s1, s2])))
  · exact Or.inr (Or.inr (q 3 _ (by simp [iterate_succ_apply', s1, s2, s3])))
  · exact Or.inr (Or.inr (q 4 _ (by simp [iterate_succ_apply', s1, s2, s3, s4])))
  · exact Or.inr (Or.inr (q 5 _ (by simp [iterate_succ_apply', s1, s2, s3, s4, s5])))
  · exact Or.inr (Or.inr (q 6 _ (by simp [iterate_succ_apply', s1, s2, s3, s4, s5, s6])))

theorem cor2_minus_thm : cor2_minus := by
  intro hS l r hl hr h
  by_cases hr1 : r = 1
  · subst hr1
    left
    have h4 : 2 ^ l = 2 ^ 1 := by
      have : (2 : ℤ) ^ l = 2 := by linarith
      norm_num; exact_mod_cast this
    exact ⟨Nat.pow_right_injective (by norm_num) h4, rfl⟩
  · obtain ⟨n, hn, hv⟩ := solution_gives_cycle_thm (-1) l r sign_minus (by omega) h
    obtain ⟨k, hk⟩ := hS n hn.1
    have h1 : minimalPeriod (f (-1)) ((f (-1))^[k] n) = minimalPeriod (f (-1)) n :=
      minimalPeriod_apply_iterate hn.mem k
    have h3 := lengthVector_length (-1) n
    rw [hv] at h3
    have h4 : r - 1 + 1 = r := by omega
    simp [h4] at h3
    have hper := period_list hk
    rw [h1, ← h3] at hper
    rcases hper with h5 | h5 | h5
    · omega
    · subst h5
      right
      have h8 : 2 ^ l = 2 ^ 3 := by
        have : (2 : ℤ) ^ l = 8 := by linarith
        norm_num; exact_mod_cast this
      exact ⟨Nat.pow_right_injective (by norm_num) h8, rfl⟩
    · subst h5
      have := gersonides_minus_thm l 7 hl (by norm_num) h
      omega

/-! ## Theorem 2 -/

theorem sum_dropLast_ge {w : List ℕ} (hp : ∀ x ∈ w, 0 < x) : w.length - 1 ≤ w.dropLast.sum := by
  have := List.length_le_sum_of_one_le w.dropLast (fun i hi => hp i (List.mem_of_mem_dropLast hi))
  simpa using this

theorem H_cons {a : ℕ} {w : List ℕ} (ha : 0 < a) (hw : w ≠ []) (hp : ∀ x ∈ w, 0 < x) :
    H (a :: w) + 1 = a + H w := by
  have hsum := sum_dropLast_ge hp
  have hl : 0 < w.length := List.length_pos_iff.mpr hw
  simp only [H, List.dropLast_cons_of_ne_nil hw, List.sum_cons, List.length_cons, Nat.add_sub_cancel]
  omega

/-- The inequality (1.3), repaired. -/
theorem e_le : ∀ z : List ℕ, z ≠ [] → (∀ x ∈ z, 0 < x) →
    (e z : ℤ) ≤ 2 ^ H z * (3 ^ z.length - 2 ^ z.length)
  | [], h, _ => absurd rfl h
  | [a], _, _ => by norm_num [e_singleton, H]
  | a :: b :: w, _, hp => by
    have hw : b :: w ≠ [] := by simp
    have hp' : ∀ x ∈ b :: w, 0 < x := fun x hx => hp x (List.mem_cons_of_mem _ hx)
    have ih := e_le (b :: w) hw hp'
    have hH := H_cons (hp a (by simp)) hw hp'
    generalize hW : b :: w = W at ih hH ⊢
    have hY : (2 : ℤ) * 2 ^ H (a :: W) = 2 ^ a * 2 ^ H W := by
      have := congrArg (fun t => (2 : ℤ) ^ t) hH
      simp only [pow_succ, pow_add] at this
      linarith
    have hP : (0 : ℤ) ≤ 3 ^ W.length := by positivity
    have hPQ : (0 : ℤ) ≤ 3 ^ W.length - 2 ^ W.length :=
      sub_nonneg.mpr (pow_le_pow_left₀ (by norm_num) (by norm_num) _)
    have hY1 : (1 : ℤ) ≤ 2 ^ H (a :: W) := one_le_pow₀ (by norm_num)
    have h1 : (2 : ℤ) ^ a * (e W : ℤ) ≤ 2 ^ a * (2 ^ H W * (3 ^ W.length - 2 ^ W.length)) :=
      mul_le_mul_of_nonneg_left ih (by positivity)
    have h2 : (3 : ℤ) ^ W.length ≤ 2 ^ H (a :: W) * 3 ^ W.length := le_mul_of_one_le_left hP hY1
    rw [e_cons, List.length_cons, pow_succ, pow_succ]
    push_cast
    have key : (2 : ℤ) ^ H (a :: W) * (3 ^ W.length * 3 - 2 ^ W.length * 2) =
        2 ^ a * (2 ^ H W * (3 ^ W.length - 2 ^ W.length)) + 2 ^ H (a :: W) * 3 ^ W.length := by
      linear_combination ((3 : ℤ) ^ W.length - 2 ^ W.length) * hY
    rw [key]
    linarith

theorem thm2_thm : thm2 := by
  intro ε n z hε hn hz
  subst hz
  rw [formula_1_2'_thm ε n hε hn]
  obtain ⟨h1, h2⟩ := lengthVector_pos_thm ε n hε hn
  exact e_le _ h1 h2

theorem thm2_plus_thm : thm2_plus := by
  intro n z hn hz
  subst hz
  refine (thm2_thm 1 n _ sign_plus hn rfl).trans ?_
  have hd := d_lengthVector_pos sign_plus hn
  simp only [d, one_mul] at hd
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith

theorem thm2_printed_false_thm : thm2_printed_false :=
  ⟨cyc7.1, cyc7.2, by norm_num [d]⟩

theorem thm2_reversed_thm : thm2_reversed := by
  intro z
  simp only [H, List.drop_one, List.tail_reverse, List.sum_reverse]

end Seifert
