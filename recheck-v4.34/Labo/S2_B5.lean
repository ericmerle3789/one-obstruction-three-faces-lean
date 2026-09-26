import Mathlib
import Labo.Blueprint
import Labo.S2_Pont
import Labo.S2_Bits

/-!
# LABO-COLLATZ · S2 · A4 Formaliste — B4 (integer form) and B5 (T★ ⇔ positive cycles trivial)

`follows_iff_dvd` : `Follows x w ↔ 2^N ∣ 3^r x + C(w)`  (B4, integer form: both sides are ONE
residue class mod 2^N — by B1 and the parity-bit bijection).
`B4_int` : `x · d(w) = C(w)` ⇒ `x` follows `w` and is an `N`-cycle.
`B5` : `Tstar ↔ PositiveCyclesTrivial`.  No `sorry`, no `native_decide`, no `decide`.
-/

namespace LaboBP

theorem T_eq_Tp3 : T = Tp 3 := by funext x; rfl

theorem length_pw (f : ℤ → ℤ) (x : ℤ) (n : ℕ) : (pw f x n).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [pw, ih]

theorem follows_pw (x : ℤ) (n : ℕ) : Follows x (pw T x n) := by
  unfold Follows; rw [length_pw]

/-- **B4 (integer form).** -/
theorem follows_iff_dvd (x : ℤ) (w : List Bool) :
    Follows x w ↔ (2 : ℤ) ^ w.length ∣ 3 ^ (w.count true) * x + C w := by
  constructor
  · intro h
    exact ⟨_, (B1 x w h).symm⟩
  · intro h
    obtain ⟨y, hy⟩ := parity_bits_surj 3 ⟨1, by norm_num⟩ w
    rw [← T_eq_Tp3] at hy
    have hyf : Follows y w := hy
    have h2 : (2 : ℤ) ^ w.length ∣ 3 ^ (w.count true) * (x - y) := by
      have := dvd_sub h ⟨_, (B1 y w hyf).symm⟩
      rw [show (3 : ℤ) ^ (w.count true) * (x - y)
        = 3 ^ (w.count true) * x + C w - (3 ^ (w.count true) * y + C w) by ring]
      exact this
    have hc : IsCoprime ((2 : ℤ) ^ w.length) (3 ^ (w.count true)) :=
      (isCoprime_two_of_odd 3 ⟨1, by norm_num⟩).pow
    have hxy := hc.dvd_of_dvd_mul_left h2
    have := (parity_bits 3 ⟨1, by norm_num⟩ w.length x y).mpr hxy
    rw [← T_eq_Tp3] at this
    unfold Follows; rw [this]; exact hy

/-- **B4 (integer form), cycle half.**  An integer solution of `x·d = C` follows `w` and is an `N`-cycle. -/
theorem B4_int (x : ℤ) (w : List Bool) (h : x * d w = C w) :
    Follows x w ∧ T^[w.length] x = x := by
  have hf : Follows x w := by
    rw [follows_iff_dvd]
    refine ⟨x, ?_⟩
    unfold d at h
    linear_combination -h
  exact ⟨hf, (B2 x w hf).mpr h⟩

theorem C_pos (w : List Bool) (h : true ∈ w) : 0 < C w := by
  induction w with
  | nil => simp at h
  | cons b w ih =>
    cases b with
    | true => simp [C]
    | false =>
      have : true ∈ w := by simpa using h
      simp [C]; exact ih this

theorem C_eq_zero (w : List Bool) (h : true ∉ w) : C w = 0 := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b with
    | true => simp at h
    | false =>
      have : true ∉ w := by simpa using h
      simp [C, ih this]

/-! ## The trivial cycle {1, 2} -/

def W10 (k : ℕ) : List Bool := (List.replicate k [true, false]).flatten
def W01 (k : ℕ) : List Bool := (List.replicate k [false, true]).flatten

theorem T_one : T 1 = 2 := by unfold T; norm_num
theorem T_two : T 2 = 1 := by unfold T; norm_num

theorem iter_one (k : ℕ) : T^[2 * k] 1 = 1 ∧ T^[2 * k + 1] 1 = 2 := by
  induction k with
  | zero => exact ⟨rfl, T_one⟩
  | succ k ih =>
    have e1 : T^[2 * (k + 1)] 1 = T^[2 * k + 1] (T 1) := by
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Function.iterate_succ_apply]
    have e2 : T^[2 * (k + 1) + 1] 1 = T^[2 * k + 1] (T (T 1)) := by
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 by ring, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
    have e3 : T^[2 * k + 1] 1 = T^[2 * k] (T 1) := Function.iterate_succ_apply _ _ _
    refine ⟨?_, ?_⟩
    · rw [e1, T_one, show 2 * k + 1 = (2 * k) + 1 from rfl, Function.iterate_succ_apply, T_two, ih.1]
    · rw [e2, T_one, T_two, ih.2]

theorem iter_two (k : ℕ) : T^[2 * k] 2 = 2 ∧ T^[2 * k + 1] 2 = 1 := by
  refine ⟨?_, ?_⟩
  · calc T^[2 * k] 2 = T^[2 * k] (T 1) := by rw [T_one]
      _ = T^[2 * k + 1] 1 := (Function.iterate_succ_apply T (2 * k) 1).symm
      _ = 2 := (iter_one k).2
  · calc T^[2 * k + 1] 2 = T^[2 * k] (T 2) := Function.iterate_succ_apply T (2 * k) 2
      _ = T^[2 * k] 1 := by rw [T_two]
      _ = 1 := (iter_one k).1

theorem pw_one (k : ℕ) : pw T 1 (2 * k) = W10 k ∧ pw T 2 (2 * k) = W01 k := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
    simp only [pw, T_one, T_two, ih.1, ih.2, W10, W01, List.replicate_succ, List.flatten_cons]
    constructor <;> rfl

theorem W10_append (j : ℕ) : W10 j ++ [true] = true :: W01 j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [W10, W01, List.replicate_succ, List.flatten_cons] at ih ⊢
    simp [ih]

theorem W01_append (j : ℕ) : W01 j ++ [false] = false :: W10 j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [W10, W01, List.replicate_succ, List.flatten_cons] at ih ⊢
    simp [ih]

theorem W10_rotate_one (k : ℕ) : (W10 k).rotate 1 = W01 k := by
  cases k with
  | zero => rfl
  | succ j =>
    have : W10 (j + 1) = true :: false :: W10 j := by
      simp [W10, List.replicate_succ, List.flatten_cons]
    rw [this, List.rotate_cons_succ, List.rotate_zero, List.cons_append, W10_append]
    simp [W01, List.replicate_succ, List.flatten_cons]

theorem W01_rotate_one (k : ℕ) : (W01 k).rotate 1 = W10 k := by
  cases k with
  | zero => rfl
  | succ j =>
    have : W01 (j + 1) = false :: true :: W01 j := by
      simp [W01, List.replicate_succ, List.flatten_cons]
    rw [this, List.rotate_cons_succ, List.rotate_zero, List.cons_append, W01_append]
    simp [W01, List.replicate_succ, List.flatten_cons, W10]

theorem rotate_W10 (k m : ℕ) : (W10 k).rotate m = W10 k ∨ (W10 k).rotate m = W01 k := by
  induction m with
  | zero => left; simp
  | succ m ih =>
    rw [← List.rotate_rotate]
    rcases ih with h | h <;> rw [h]
    · right; exact W10_rotate_one k
    · left; exact W01_rotate_one k

/-- Two integer cycles with the same nonempty word are equal (uniqueness in B2). -/
theorem cycle_unique (x y : ℤ) (w : List Bool) (hne : w ≠ [])
    (hx : Follows x w) (hy : Follows y w) (cx : T^[w.length] x = x) (cy : T^[w.length] y = y) :
    x = y := by
  have ex := (B2 x w hx).mp cx
  have ey := (B2 y w hy).mp cy
  have : (x - y) * d w = 0 := by linear_combination ex - ey
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · exact absurd h (d_ne_zero w hne)

/-- **B5, proved.** `T★ ↔` every positive cycle of `T` is `{1, 2}`. -/
theorem B5 : B5_statement := by
  constructor
  · -- T★ ⇒ positive cycles trivial
    intro hT x hx n hn hc
    set w := pw T x n with hw
    have hf : Follows x w := follows_pw x n
    have hl : w.length = n := length_pw T x n
    have hne : w ≠ [] := by intro h; rw [h] at hl; simp at hl; omega
    have hc' : T^[w.length] x = x := by rw [hl]; exact hc
    have hd := B3 x w hx hf hne hc'
    have e := (B2 x w hf).mp hc'
    have hone : true ∈ w := by
      by_contra h
      rw [C_eq_zero w h] at e
      push_cast at e
      rcases mul_eq_zero.mp e with h1 | h1 <;> linarith
    obtain ⟨k, m, hkm⟩ := hT w hd hone ⟨x, by rw [← e]; ring⟩
    have hW : w = W10 k ∨ w = W01 k := by rw [hkm]; exact rotate_W10 k m
    have hlen : w.length = 2 * k := by
      rcases hW with h | h <;> rw [h] <;> simp [W10, W01, List.length_flatten] <;> ring
    rcases hW with h | h
    · left
      have h1 : Follows 1 w := by
        unfold Follows; rw [hlen, (pw_one k).1, h]
      have c1 : T^[w.length] 1 = 1 := by rw [hlen]; exact (iter_one k).1
      exact cycle_unique x 1 w hne hf h1 hc' c1
    · right
      have h2 : Follows 2 w := by
        unfold Follows; rw [hlen, (pw_one k).2, h]
      have c2 : T^[w.length] 2 = 2 := by rw [hlen]; exact (iter_two k).1
      exact cycle_unique x 2 w hne hf h2 hc' c2
  · -- positive cycles trivial ⇒ T★
    intro hP w hd hone hdvd
    obtain ⟨x, hx⟩ := hdvd
    have e : x * d w = C w := by rw [hx]; ring
    obtain ⟨hf, hc⟩ := B4_int x w e
    have hCpos : (0 : ℤ) < C w := by exact_mod_cast C_pos w hone
    have hxpos : 0 < x := by
      by_contra hneg
      push Not at hneg
      have : x * d w ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hd.le
      linarith
    have hne : w ≠ [] := by rintro rfl; simp at hone
    have hlpos : 0 < w.length := List.length_pos_of_ne_nil hne
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' w.length
    · rcases hP x hxpos w.length hlpos hc with h1 | h2
      · subst h1
        refine ⟨k, 0, ?_⟩
        have : w = pw T 1 (2 * k) := by rw [← hk]; exact hf.symm
        rw [List.rotate_zero, this, (pw_one k).1]; rfl
      · subst h2
        refine ⟨k, 1, ?_⟩
        have : w = pw T 2 (2 * k) := by rw [← hk]; exact hf.symm
        rw [this, (pw_one k).2]
        exact (W10_rotate_one k).symm
    · exfalso
      rcases hP x hxpos w.length hlpos hc with h1 | h2
      · subst h1; rw [hk, (iter_one k).2] at hc; norm_num at hc
      · subst h2; rw [hk, (iter_two k).2] at hc; norm_num at hc

end LaboBP
