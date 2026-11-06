import Seifert1988.Algebre

/-!
# Seifert 1988 · proofs (2): the map, formulas (1.2) and (1.2'), Theorem 1
-/

namespace Seifert

open Function

/-! ## One step of `f` -/

theorem val_eq {ε n m : ℤ} {a : ℕ} (hm : Odd m) (h : (2 : ℤ) ^ a * m = 3 * n + ε) : val ε n = a := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have h1 : padicValInt 2 ((2 : ℤ) ^ a) = a := by simp [padicValInt, Int.natAbs_pow]
  have h2 : padicValInt 2 m = 0 := by
    apply padicValInt.eq_zero_of_not_dvd
    intro hd
    have : Even m := even_iff_two_dvd.mpr (by exact_mod_cast hd)
    exact (Int.not_even_iff_odd.mpr hm) this
  unfold val
  rw [← h, padicValInt.mul (pow_ne_zero _ two_ne_zero) hm0, h1, h2, add_zero]

theorem f_eq {ε n m : ℤ} {a : ℕ} (hm : Odd m) (h : (2 : ℤ) ^ a * m = 3 * n + ε) : f ε n = m := by
  unfold f
  rw [val_eq hm h, ← h]
  exact Int.mul_ediv_cancel_left _ (pow_ne_zero _ two_ne_zero)

theorem f_maps_thm : f_maps := by
  intro ε n hε ⟨hn0, hn1⟩
  set x := 3 * n + ε with hx
  have hx0 : 0 < x := by rcases hε with rfl | rfl <;> omega
  have hxeven : Even x := by
    have h3 : Odd (3 * n) := (by decide : Odd (3 : ℤ)).mul hn1
    have hε' : Odd ε := by rcases hε with rfl | rfl <;> decide
    exact h3.add_odd hε'
  have hk : padicValInt 2 x = val ε n := rfl
  obtain ⟨m, hm⟩ : (2 : ℤ) ^ val ε n ∣ x := by
    have := padicValInt_dvd (p := 2) (a := x)
    rw [hk] at this; exact_mod_cast this
  have hne : x ≠ 0 := hx0.ne'
  have hk1 : 0 < val ε n := by
    have h := (padicValInt_dvd_iff (p := 2) 1 x).mp (by simpa using even_iff_two_dvd.mp hxeven)
    rcases h with h | h
    · exact absurd h hne
    · rw [hk] at h; omega
  have hmodd : Odd m := by
    rw [← Int.not_even_iff_odd]
    rintro ⟨c, rfl⟩
    have hdvd : ((2 : ℕ) : ℤ) ^ (val ε n + 1) ∣ x := ⟨c, by rw [hm]; push_cast; ring⟩
    rcases (padicValInt_dvd_iff (p := 2) (val ε n + 1) x).mp hdvd with h | h
    · exact hne h
    · rw [hk] at h; omega
  have hmpos : 0 < m := by
    by_contra hc
    have : (2 : ℤ) ^ val ε n * m ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_lt.mp hc)
    omega
  have hfm : f ε n = m := f_eq hmodd hm.symm
  rw [hfm]
  exact ⟨⟨hmpos, hmodd⟩, hk1, hm.symm⟩

theorem iter_posOdd {ε n : ℤ} (hε : IsSign ε) (hn : PosOdd n) (i : ℕ) : PosOdd ((f ε)^[i] n) := by
  induction i with
  | zero => simpa using hn
  | succ i ih => rw [iterate_succ_apply']; exact (f_maps_thm ε _ hε ih).1

/-! ## Formulas (1.2) and (1.2') -/

/-- The exponents along a piece of orbit. -/
def vec (ε n : ℤ) (r : ℕ) : List ℕ := (List.range r).map fun i => val ε ((f ε)^[i] n)

theorem vec_length (ε n : ℤ) (r : ℕ) : (vec ε n r).length = r := by simp [vec]

theorem vec_succ (ε n : ℤ) (r : ℕ) : vec ε n (r + 1) = vec ε n r ++ [val ε ((f ε)^[r] n)] := by
  simp [vec, List.range_succ]

theorem formula_vec {ε n : ℤ} (hε : IsSign ε) (hn : PosOdd n) (r : ℕ) :
    3 ^ r * n + ε * (e (vec ε n r) : ℤ) = 2 ^ (vec ε n r).sum * (f ε)^[r] n := by
  induction r with
  | zero => simp [vec, e_nil]
  | succ r ih =>
    have hf := (f_maps_thm ε _ hε (iter_posOdd hε hn r)).2.2
    rw [vec_succ, e_snoc, List.sum_append, iterate_succ_apply']
    simp only [List.sum_cons, List.sum_nil, add_zero]
    push_cast
    rw [pow_add, pow_succ]
    linear_combination 3 * ih - 2 ^ (vec ε n r).sum * hf

theorem formula_1_2_thm : formula_1_2 := by
  intro ε n r hε hn z hz
  subst hz
  exact formula_vec hε hn r

theorem lengthVector_eq_vec (ε n : ℤ) : lengthVector ε n = vec ε n (minimalPeriod (f ε) n) := rfl

theorem IsCyclic.mem {ε n : ℤ} (h : IsCyclic ε n) : n ∈ periodicPts (f ε) := by
  obtain ⟨_, r, hr, hrn⟩ := h
  exact mk_mem_periodicPts hr hrn

theorem IsCyclic.period_pos {ε n : ℤ} (h : IsCyclic ε n) : 0 < minimalPeriod (f ε) n :=
  minimalPeriod_pos_of_mem_periodicPts h.mem

theorem lengthVector_length (ε n : ℤ) : (lengthVector ε n).length = minimalPeriod (f ε) n :=
  vec_length _ _ _

theorem formula_1_2'_thm : formula_1_2' := by
  intro ε n hε hn
  have h := formula_vec hε hn.1 (minimalPeriod (f ε) n)
  rw [iterate_minimalPeriod] at h
  have hl : (vec ε n (minimalPeriod (f ε) n)).length = minimalPeriod (f ε) n := vec_length _ _ _
  simp only [d, lengthVector_eq_vec, hl]
  linear_combination (-ε) * h + (e (vec ε n (minimalPeriod (f ε) n)) : ℤ) * hε.sq

theorem lengthVector_pos_thm : lengthVector_pos := by
  intro ε n hε hn
  constructor
  · intro h0
    have := lengthVector_length ε n
    rw [h0] at this
    have hp := hn.period_pos
    simp at this
    omega
  · intro a ha
    simp only [lengthVector, List.mem_map] at ha
    obtain ⟨i, _, rfl⟩ := ha
    exact (f_maps_thm ε _ hε (iter_posOdd hε hn.1 i)).2.1

/-! ## Theorem 1(a) -/

theorem d_lengthVector_pos {ε n : ℤ} (hε : IsSign ε) (hn : IsCyclic ε n) : 0 < d ε (lengthVector ε n) := by
  have h := formula_1_2'_thm ε n hε hn
  have hne := (lengthVector_pos_thm ε n hε hn).1
  have he : (0 : ℤ) < e (lengthVector ε n) := by exact_mod_cast e_pos hne
  rw [← h] at he
  exact (mul_pos_iff_of_pos_right hn.1.1).1 he

theorem thm1a_unique_thm : thm1a_unique := by
  intro ε n m hε hn hm h
  have h1 := formula_1_2'_thm ε n hε hn
  have h2 := formula_1_2'_thm ε m hε hm
  rw [← h] at h2
  have hd := d_lengthVector_pos hε hn
  exact mul_left_cancel₀ hd.ne' (h1.trans h2.symm)

theorem thm1a_rotate_thm : thm1a_rotate := by
  intro ε n k hε hn
  have hmem := hn.mem
  have hcyc : IsCyclic ε ((f ε)^[k] n) := by
    refine ⟨iter_posOdd hε hn.1 k, minimalPeriod (f ε) n, hn.period_pos, ?_⟩
    rw [← iterate_add_apply, add_comm, iterate_add_apply, iterate_minimalPeriod]
  refine ⟨hcyc, ?_⟩
  have hper : minimalPeriod (f ε) ((f ε)^[k] n) = minimalPeriod (f ε) n :=
    minimalPeriod_apply_iterate hmem k
  apply List.ext_getElem
  · simp [lengthVector_length, hper]
  · intro i h1 h2
    rw [List.getElem_rotate]
    simp only [lengthVector, List.getElem_map, List.getElem_range]
    rw [← iterate_add_apply, List.length_map, List.length_range, iterate_mod_minimalPeriod_eq]

/-! ## Theorem 1(b) -/

theorem free_lengthVector {ε n : ℤ} (hε : IsSign ε) (hn : IsCyclic ε n) : Free (lengthVector ε n) := by
  intro k hk hkr hrot
  obtain ⟨hcyc, hv⟩ := thm1a_rotate_thm ε n k hε hn
  have heq : (f ε)^[k] n = n :=
    thm1a_unique_thm ε _ _ hε hcyc hn (hv.trans hrot)
  have := IsPeriodicPt.minimalPeriod_le hk (show IsPeriodicPt (f ε) k n from heq)
  rw [lengthVector_length] at hkr
  omega

/-- The head of a rotation. -/
theorem head_rotate {z : List ℕ} (hz : 0 < z.length) {k a : ℕ} {w : List ℕ} (hw : z.rotate k = a :: w) :
    z[k % z.length]'(Nat.mod_lt _ hz) = a := by
  have h0 : 0 < (z.rotate k).length := by simpa using hz
  have h := List.getElem_rotate (l := z) (n := k) (k := 0) h0
  simp only [Nat.zero_add] at h
  rw [← h]
  simp [hw]

section Construct

variable {ε : ℤ} (hε : IsSign ε) {z : List ℕ} (hz : z ≠ []) (hp : ∀ a ∈ z, 0 < a)
  (hd : 0 < d ε z) (hdvd : d ε z ∣ (e z : ℤ))

/-- The candidate points: `e(g^k z) / d`. -/
def pt (ε : ℤ) (z : List ℕ) (k : ℕ) : ℤ := (e (z.rotate k) : ℤ) / d ε z

include hε hz hp hdvd in
theorem pt_mul (k : ℕ) : d ε z * pt ε z k = e (z.rotate k) :=
  Int.mul_ediv_cancel' (dvd_rotate hε hz hp hdvd k)

include hε hz hp hd hdvd in
theorem pt_posOdd (k : ℕ) : PosOdd (pt ε z k) := by
  have h := pt_mul hε hz hp hdvd k
  have hne : z.rotate k ≠ [] := by simpa [List.rotate_eq_nil_iff] using hz
  have hp' : ∀ a ∈ z.rotate k, 0 < a := fun a ha => hp a (List.mem_rotate.mp ha)
  constructor
  · have he : (0 : ℤ) < e (z.rotate k) := by exact_mod_cast e_pos hne
    rw [← h] at he
    exact (mul_pos_iff_of_pos_left hd).1 he
  · have ho : Odd ((e (z.rotate k) : ℕ) : ℤ) := (Int.odd_coe_nat _).2 (e_odd hne hp')
    rw [← h] at ho
    exact (Int.odd_mul.mp ho).2

include hε hz hp hd hdvd in
theorem pt_step {k a : ℕ} {w : List ℕ} (hw : z.rotate k = a :: w) :
    (2 : ℤ) ^ a * pt ε z (k + 1) = 3 * pt ε z k + ε := by
  have h1 := pt_mul hε hz hp hdvd k
  have h2 := pt_mul hε hz hp hdvd (k + 1)
  have hstep : z.rotate (k + 1) = w ++ [a] := by rw [← List.rotate_rotate, hw, rotate_one_cons]
  rw [hstep] at h2
  rw [hw] at h1
  have ht := transport hε a w
  have hdd : d ε (a :: w) = d ε z := by rw [← hw, d_rotate]
  rw [hdd, ← h1, ← h2] at ht
  apply mul_left_cancel₀ hd.ne'
  linear_combination ht

include hε hz hp hd hdvd in
theorem pt_f {k a : ℕ} {w : List ℕ} (hw : z.rotate k = a :: w) :
    f ε (pt ε z k) = pt ε z (k + 1) ∧ val ε (pt ε z k) = a := by
  have hs := pt_step hε hz hp hd hdvd hw
  have ho := (pt_posOdd hε hz hp hd hdvd (k + 1)).2
  exact ⟨f_eq ho hs, val_eq ho hs⟩

include hε hz hp hd hdvd in
theorem pt_iter (k i : ℕ) : (f ε)^[i] (pt ε z k) = pt ε z (k + i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hne : z.rotate (k + i) ≠ [] := by simpa [List.rotate_eq_nil_iff] using hz
    obtain ⟨a, w, hw⟩ := List.exists_cons_of_ne_nil hne
    rw [iterate_succ_apply', ih, (pt_f hε hz hp hd hdvd hw).1]
    rfl

include hε hz hp hd hdvd in
theorem pt_val (k : ℕ) (hl : 0 < z.length) : val ε (pt ε z k) = z[k % z.length]'(Nat.mod_lt _ hl) := by
  have hne : z.rotate k ≠ [] := by simpa [List.rotate_eq_nil_iff] using hz
  obtain ⟨a, w, hw⟩ := List.exists_cons_of_ne_nil hne
  rw [(pt_f hε hz hp hd hdvd hw).2, head_rotate hl hw]

include hε hz hp hd hdvd in
/-- The direction (ii) ⇒ (i) of Theorem 1(b), with the point. -/
theorem exists_cycle (hfree : Free z) :
    IsCyclic ε (pt ε z 0) ∧ lengthVector ε (pt ε z 0) = z := by
  have hl : 0 < z.length := List.length_pos_iff.mpr hz
  have hiter := pt_iter hε hz hp hd hdvd 0
  have hcyc : IsCyclic ε (pt ε z 0) := by
    refine ⟨pt_posOdd hε hz hp hd hdvd 0, z.length, hl, ?_⟩
    rw [hiter, Nat.zero_add]
    simp [pt, List.rotate_length]
  refine ⟨hcyc, ?_⟩
  set n := pt ε z 0 with hn
  have hval : ∀ i, val ε ((f ε)^[i] n) = z[i % z.length]'(Nat.mod_lt _ hl) := by
    intro i
    rw [hiter, Nat.zero_add, pt_val hε hz hp hd hdvd i hl]
  have hper : minimalPeriod (f ε) n = z.length := by
    set p := minimalPeriod (f ε) n with hpdef
    have hp0 : 0 < p := hcyc.period_pos
    have hple : p ≤ z.length := by
      apply IsPeriodicPt.minimalPeriod_le hl
      show (f ε)^[z.length] n = n
      rw [hiter, Nat.zero_add]; simp [hn, pt, List.rotate_length]
    by_contra hne
    have hlt : p < z.length := lt_of_le_of_ne hple hne
    refine hfree p hp0 hlt ?_
    apply List.ext_getElem (by simp)
    intro i h1 h2
    rw [List.getElem_rotate]
    have hi : i % z.length = i := Nat.mod_eq_of_lt h2
    have h3 := hval i
    have h4 := hval (i + p)
    have hsame : (f ε)^[i + p] n = (f ε)^[i] n := by
      rw [iterate_add_apply, hpdef, iterate_minimalPeriod]
    rw [hsame] at h4
    have : z[(i + p) % z.length]'(Nat.mod_lt _ hl) = z[i % z.length]'(Nat.mod_lt _ hl) := by
      rw [← h4, ← h3]
    rw [this]
    simp only [hi]
  simp only [lengthVector, hper]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [hval i]
  simp only [Nat.mod_eq_of_lt h2]

end Construct

theorem thm1b_single_thm : thm1b_single := by
  intro ε z hε hz hp
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨free_lengthVector hε hn, d_lengthVector_pos hε hn, ?_⟩
    exact ⟨n, (formula_1_2'_thm ε n hε hn).symm⟩
  · rintro ⟨hfree, hd, hdvd⟩
    exact ⟨_, exists_cycle hε hz hp hd hdvd hfree⟩

theorem thm1b_thm : thm1b := by
  intro ε z hε hz hp
  rw [thm1b_single_thm ε z hε hz hp]
  have hspan : (Ideal.span (Set.range fun k : ℕ => (e (z.rotate k) : ℤ)) ≤ Ideal.span {d ε z}) ↔
      ∀ k : ℕ, d ε z ∣ (e (z.rotate k) : ℤ) := by
    rw [Ideal.span_le, Set.range_subset_iff]
    simp only [SetLike.mem_coe, Ideal.mem_span_singleton]
  rw [hspan]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, dvd_rotate hε hz hp h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by simpa using h3 0⟩

end Seifert
