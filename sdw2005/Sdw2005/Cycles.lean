import Mathlib
import Sdw2005.Sdw_Enonces
import Sdw2005.Bornes

/-!
# Sdw2005 · layer 2: a cycle of the 3x+1 map gives a solution of the chain equation

For a cycle `C^[N] n = n` on the positive integers, write `y j = C^[j] n` (periodic of period `N`). A local
minimum is an index `j` with `y j` odd and `y (j + N − 1)` (that is, `y (j − 1)`, cyclically) even. Local minima
exist (the orbit has odd and even values, else it would be strictly monotone), so there are infinitely many, and
`T i = Nat.nth isMin i` lists them. Between two consecutive minima `T i < T (i + 1)` the orbit has a run of
`k_i ≥ 1` odd values followed by a run of `l_i ≥ 1` even values; with `a_i = (y (T i) + 1) / 2^{k_i}`,
`y (T i) + 1 = 2^{k_i} a_i`, `y (T i + k_i) + 1 = 3^{k_i} a_i` and `2^{l_i} y (T (i + 1)) = y (T i + k_i)`, which is
the chain equation. With `m = minCount n N`, `T m = T 0 + N`, and the odd values in `[T 0, T m)` are counted by
`k_0 + ⋯ + k_{m−1}`.
-/

namespace Sdw2005

/-! ## The orbit -/

/-- The orbit `y j = C^[j] n`. -/
def orb (n j : ℕ) : ℕ := C^[j] n

theorem orb_succ (n j : ℕ) : orb n (j + 1) = C (orb n j) := Function.iterate_succ_apply' C j n

theorem orb_add_period {n N : ℕ} (hc : C^[N] n = n) (j : ℕ) : orb n (j + N) = orb n j := by
  unfold orb; rw [Function.iterate_add_apply, hc]

theorem orb_add_mul {n N : ℕ} (hc : C^[N] n = n) (j c : ℕ) : orb n (j + N * c) = orb n j := by
  induction c with
  | zero => simp
  | succ c ih => rw [Nat.mul_succ, ← Nat.add_assoc, orb_add_period hc, ih]

theorem orb_mod {n N : ℕ} (hc : C^[N] n = n) (j : ℕ) : orb n (j % N) = orb n j := by
  conv_rhs => rw [← Nat.mod_add_div j N]
  rw [orb_add_mul hc]

theorem C_pos {x : ℕ} (hx : 0 < x) : 0 < C x := by
  unfold C; split_ifs with h <;> omega

theorem orb_pos {n : ℕ} (hn : 0 < n) (j : ℕ) : 0 < orb n j := by
  induction j with
  | zero => exact hn
  | succ j ih => rw [orb_succ]; exact C_pos ih

theorem C_even {x : ℕ} (h : x % 2 = 0) : 2 * C x = x := by
  unfold C; rw [if_pos h]; omega

theorem C_odd {x : ℕ} (h : x % 2 = 1) : 2 * C x = 3 * x + 1 := by
  unfold C; rw [if_neg (by omega)]; omega

section Cycle

variable {n N : ℕ} (hn : 0 < n) (hN : 0 < N) (hc : C^[N] n = n)
include hn hN hc

theorem exists_odd : ∃ j, orb n j % 2 = 1 := by
  by_contra hno
  push_neg at hno
  have hanti : StrictAnti (orb n) := strictAnti_nat_of_succ_lt (fun j => by
    have h0 : orb n j % 2 = 0 := by have := hno j; omega
    have h1 := C_even h0
    have h2 := orb_pos hn j
    rw [orb_succ]; omega)
  have h1 := hanti hN
  have h2 : orb n N = orb n 0 := by simpa using orb_add_period hc 0
  omega

theorem exists_even : ∃ j, orb n j % 2 = 0 := by
  by_contra hno
  push_neg at hno
  have hmono : StrictMono (orb n) := strictMono_nat_of_lt_succ (fun j => by
    have h0 : orb n j % 2 = 1 := by have := hno j; omega
    have h1 := C_odd h0
    rw [orb_succ]; omega)
  have h1 := hmono hN
  have h2 : orb n N = orb n 0 := by simpa using orb_add_period hc 0
  omega

omit hn in
theorem exists_shift (t e : ℕ) : ∃ d, orb n (t + d) = orb n e := by
  refine ⟨N * (t + 1) + e - t, ?_⟩
  have h1 : t + 1 ≤ N * (t + 1) := Nat.le_mul_of_pos_left _ hN
  have h2 : t + (N * (t + 1) + e - t) = e + N * (t + 1) := by
    generalize N * (t + 1) = M at h1 ⊢; omega
  rw [h2, orb_add_mul hc]

theorem exists_even_after (t : ℕ) : ∃ d, orb n (t + d) % 2 = 0 := by
  obtain ⟨e, he⟩ := exists_even hn hN hc
  obtain ⟨d, hd⟩ := exists_shift hN hc t e
  exact ⟨d, by rw [hd]; exact he⟩

end Cycle

/-- Local minima: `y j` odd and `y (j + N − 1)` even. -/
def isMin (n N j : ℕ) : Prop := orb n j % 2 = 1 ∧ orb n (j + N - 1) % 2 = 0

instance (n N : ℕ) : DecidablePred (isMin n N) := fun j => inferInstanceAs (Decidable (_ ∧ _))

theorem isMin_add_period {n N : ℕ} (hN : 0 < N) (hc : C^[N] n = n) (j : ℕ) :
    isMin n N (j + N) ↔ isMin n N j := by
  unfold isMin
  rw [orb_add_period hc, show j + N + N - 1 = (j + N - 1) + N by omega, orb_add_period hc]

theorem isMin_add_mul {n N : ℕ} (hN : 0 < N) (hc : C^[N] n = n) (j c : ℕ) :
    isMin n N (j + N * c) ↔ isMin n N j := by
  induction c with
  | zero => simp
  | succ c ih => rw [Nat.mul_succ, ← Nat.add_assoc, isMin_add_period hN hc, ih]

/-- The predecessor of a local minimum `j ≥ 1` is even. -/
theorem isMin_pred {n N : ℕ} (hN : 0 < N) (hc : C^[N] n = n) {j : ℕ} (hj : 1 ≤ j) (h : isMin n N j) :
    orb n (j - 1) % 2 = 0 := by
  have := h.2
  rwa [show j + N - 1 = (j - 1) + N by omega, orb_add_period hc] at this

theorem exists_isMin {n N : ℕ} (hn : 0 < n) (hN : 0 < N) (hc : C^[N] n = n) : ∃ j, isMin n N j := by
  obtain ⟨e, he⟩ := exists_even hn hN hc
  obtain ⟨o, ho⟩ := exists_odd hn hN hc
  have hex : ∃ d, orb n (e + 1 + d) % 2 = 1 := by
    obtain ⟨d, hd⟩ := exists_shift hN hc (e + 1) o
    exact ⟨d, by rw [hd]; exact ho⟩
  obtain ⟨d, hd1, hd2⟩ : ∃ d, orb n (e + 1 + d) % 2 = 1 ∧ ∀ d' < d, ¬ orb n (e + 1 + d') % 2 = 1 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun _ h => Nat.find_min hex h⟩
  refine ⟨e + 1 + d, hd1, ?_⟩
  rw [show e + 1 + d + N - 1 = (e + d) + N by omega, orb_add_period hc]
  rcases Nat.eq_zero_or_pos d with h0 | h0
  · rw [h0, Nat.add_zero]; exact he
  · have := hd2 (d - 1) (by omega)
    rw [show e + 1 + (d - 1) = e + d by omega] at this
    omega

theorem isMin_infinite {n N : ℕ} (hn : 0 < n) (hN : 0 < N) (hc : C^[N] n = n) :
    (Set.ofPred (isMin n N)).Infinite := by
  obtain ⟨j, hj⟩ := exists_isMin hn hN hc
  apply Set.infinite_of_forall_exists_gt
  intro b
  refine ⟨j + N * (b + 1), (isMin_add_mul hN hc j (b + 1)).mpr hj, ?_⟩
  have : b + 1 ≤ N * (b + 1) := Nat.le_mul_of_pos_left _ hN
  generalize N * (b + 1) = M at this ⊢
  omega

/-! ## Counting -/

theorem count_all {p : ℕ → Prop} [DecidablePred p] {n : ℕ} (h : ∀ k < n, p k) : Nat.count p n = n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.count_succ, ih (fun k hk => h k (by omega)), if_pos (h n (by omega))]

theorem count_none {p : ℕ → Prop} [DecidablePred p] {n : ℕ} (h : ∀ k < n, ¬ p k) : Nat.count p n = 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.count_succ, ih (fun k hk => h k (by omega)), if_neg (h n (by omega))]

/-- A window of length `N` of a predicate of period `N`. -/
theorem count_window {p : ℕ → Prop} [DecidablePred p] {N : ℕ} (hp : ∀ j, p (j + N) ↔ p j) (s : ℕ) :
    Nat.count (fun k => p (s + k)) N = Nat.count p N := by
  induction s with
  | zero => simp
  | succ s ih =>
    have h1 := Nat.count_succ' (fun k => p (s + k)) N
    have h2 := Nat.count_succ (fun k => p (s + k)) N
    simp only [Nat.add_zero] at h1
    have h3 : (if p (s + N) then 1 else 0) = (if p s then 1 else 0) := by
      by_cases hs : p s
      · rw [if_pos hs, if_pos ((hp s).mpr hs)]
      · rw [if_neg hs, if_neg (fun h => hs ((hp s).mp h))]
    have h4 : Nat.count (fun k => p (s + (k + 1))) N = Nat.count (fun k => p (s + 1 + k)) N := by
      congr 1; funext k; rw [show s + (k + 1) = s + 1 + k by omega]
    rw [← ih]
    omega

/-! ## The blocks between two consecutive local minima -/

section Block

variable {n N : ℕ} (hn : 0 < n) (hN : 0 < N) (hc : C^[N] n = n)

/-- The length of the run of odd values starting at `t`: the first `d` with `y (t + d)` even. -/
noncomputable def run (t : ℕ) : ℕ := Nat.find (exists_even_after hn hN hc t)

theorem run_spec (t : ℕ) : orb n (t + run hn hN hc t) % 2 = 0 := Nat.find_spec (exists_even_after hn hN hc t)

theorem run_min (t : ℕ) {j : ℕ} (hj : j < run hn hN hc t) : orb n (t + j) % 2 = 1 := by
  have := Nat.find_min (exists_even_after hn hN hc t) hj
  omega

theorem run_le (t : ℕ) {d : ℕ} (hd : orb n (t + d) % 2 = 0) : run hn hN hc t ≤ d :=
  Nat.find_min' (exists_even_after hn hN hc t) hd

variable {t t' : ℕ} (ht : isMin n N t) (ht' : isMin n N t') (htt : t < t')
  (hbetween : ∀ j, t < j → j < t' → ¬ isMin n N j)
include ht ht' htt hbetween

omit ht' htt hbetween in
theorem run_pos : 0 < run hn hN hc t := by
  by_contra h0
  have h := run_spec hn hN hc t
  rw [show run hn hN hc t = 0 by omega, Nat.add_zero] at h
  have := ht.1
  omega

omit hbetween in
theorem run_lt : t + run hn hN hc t < t' := by
  have hp := isMin_pred hN hc (by omega) ht'
  have hle := run_le hn hN hc t (d := t' - 1 - t) (by rw [show t + (t' - 1 - t) = t' - 1 by omega]; exact hp)
  have hne : t' - 1 ≠ t := by
    intro h; rw [h] at hp; have := ht.1; omega
  omega

omit ht ht' htt in
theorem even_tail : ∀ j, t + run hn hN hc t ≤ j → j < t' → orb n j % 2 = 0 := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => intro _; exact run_spec hn hN hc t
  | succ j hj ih =>
    intro hj'
    have he := ih (by omega)
    by_contra ho
    have hmin : isMin n N (j + 1) := by
      refine ⟨by omega, ?_⟩
      rw [show j + 1 + N - 1 = j + N by omega, orb_add_period hc]
      exact he
    exact hbetween (j + 1) (by omega) hj' hmin

omit ht ht' htt hbetween in
/-- `2^j (y (t + j) + 1) = 3^j (y t + 1)` along the run of odd values. -/
theorem odd_run_eq : ∀ j ≤ run hn hN hc t, 2 ^ j * (orb n (t + j) + 1) = 3 ^ j * (orb n t + 1) := by
  intro j hj
  induction j with
  | zero => simp
  | succ j ih =>
    have hodd := run_min hn hN hc t (j := j) (by omega)
    have h2 := C_odd hodd
    rw [← orb_succ, show t + j + 1 = t + (j + 1) by omega] at h2
    have ih' := ih (by omega)
    calc 2 ^ (j + 1) * (orb n (t + (j + 1)) + 1) = 2 ^ j * (2 * orb n (t + (j + 1)) + 2) := by ring
      _ = 2 ^ j * (3 * orb n (t + j) + 3) := by rw [h2]
      _ = 3 * (2 ^ j * (orb n (t + j) + 1)) := by ring
      _ = 3 * (3 ^ j * (orb n t + 1)) := by rw [ih']
      _ = 3 ^ (j + 1) * (orb n t + 1) := by ring

omit ht in
/-- `2^j y (t + k + j) = y (t + k)` along the run of even values. -/
theorem even_run_eq : ∀ j, t + run hn hN hc t + j ≤ t' →
    2 ^ j * orb n (t + run hn hN hc t + j) = orb n (t + run hn hN hc t) := by
  intro j hj
  induction j with
  | zero => simp
  | succ j ih =>
    have he := even_tail hn hN hc hbetween (t + run hn hN hc t + j) (by omega) (by omega)
    have h2 := C_even he
    rw [← orb_succ] at h2
    calc 2 ^ (j + 1) * orb n (t + run hn hN hc t + (j + 1))
        = 2 ^ j * (2 * orb n (t + run hn hN hc t + j + 1)) := by ring_nf
      _ = 2 ^ j * orb n (t + run hn hN hc t + j) := by rw [h2]
      _ = orb n (t + run hn hN hc t) := ih (by omega)

omit ht ht' htt hbetween in
theorem two_pow_run_dvd : 2 ^ run hn hN hc t ∣ orb n t + 1 := by
  have h := odd_run_eq hn hN hc (t := t) (run hn hN hc t) le_rfl
  have hd : 2 ^ run hn hN hc t ∣ (orb n t + 1) * 3 ^ run hn hN hc t := ⟨_, by rw [mul_comm _ (3 ^ _), ← h]⟩
  exact (Nat.Coprime.pow _ _ (by norm_num : Nat.Coprime 2 3)).dvd_of_dvd_mul_right hd

theorem count_block (p : ℕ → Prop) [DecidablePred p] (hp : ∀ j, p j ↔ orb n j % 2 = 1) :
    Nat.count p t' = Nat.count p t + run hn hN hc t := by
  have hlt := run_lt hn hN hc ht ht' htt
  obtain ⟨L, hL⟩ : ∃ L, t' = t + run hn hN hc t + L := ⟨t' - (t + run hn hN hc t), by omega⟩
  rw [hL, Nat.count_add p (t + run hn hN hc t) L, Nat.count_add p t (run hn hN hc t)]
  have h1 : Nat.count (fun k => p (t + k)) (run hn hN hc t) = run hn hN hc t :=
    count_all (p := fun k => p (t + k)) (fun k hk => (hp _).mpr (run_min hn hN hc t hk))
  have h2 : Nat.count (fun k => p (t + run hn hN hc t + k)) L = 0 := by
    apply count_none (p := fun k => p (t + run hn hN hc t + k))
    intro k hk hpk
    have := even_tail hn hN hc hbetween (t + run hn hN hc t + k) (by omega) (by omega)
    have := (hp _).mp hpk
    omega
  rw [h1, h2, Nat.add_zero]

end Block

/-! ## Layer 2 -/

theorem cycle_chain_thm : cycle_chain := by
  intro n N hn hN hc
  classical
  have hinf := isMin_infinite hn hN hc
  set T : ℕ → ℕ := Nat.nth (isMin n N) with hT
  have hTmin : ∀ i, isMin n N (T i) := Nat.nth_mem_of_infinite hinf
  have hTlt : ∀ i, T i < T (i + 1) := fun i => (Nat.nth_lt_nth hinf).mpr (by omega)
  have hTbetween : ∀ i j, T i < j → j < T (i + 1) → ¬ isMin n N j := by
    intro i j h1 h2 hj
    have : j ≤ T i := Nat.le_nth_of_lt_nth_succ h2 hj
    omega
  set m := minCount n N with hm
  -- `T m = T 0 + N`
  have hcountN : Nat.count (isMin n N) N = m := by
    rw [Nat.count_eq_card_filter_range, hm, minCount]
    congr 1
    apply Finset.filter_congr
    intro j _
    unfold isMin
    rw [← orb_mod hc (j + N - 1)]
    rfl
  have hcountT : Nat.count (isMin n N) (T 0 + N) = m := by
    rw [Nat.count_add, Nat.count_nth_zero, count_window (isMin_add_period hN hc), hcountN, Nat.zero_add]
  have hTm : T m = T 0 + N := by
    have hP : isMin n N (T 0 + N) := (isMin_add_period hN hc _).mpr (hTmin 0)
    rw [← hcountT, hT]
    exact Nat.nth_count hP
  have hmpos : 0 < m := by
    have h1 : Nat.count (isMin n N) (T 0 + 1) = Nat.count (isMin n N) (T 0) + 1 :=
      Nat.count_succ_eq_succ_count_iff.mpr (hTmin 0)
    have h2 := Nat.count_monotone (isMin n N) (show T 0 + 1 ≤ T 0 + N by omega)
    omega
  -- the solution
  set k : ℕ → ℕ := fun i => run hn hN hc (T i) with hk
  set a : ℕ → ℕ := fun i => (orb n (T i) + 1) / 2 ^ k i with ha
  set l : ℕ → ℕ := fun i => T (i + 1) - T i - k i with hl
  have hka : ∀ i, orb n (T i) + 1 = 2 ^ k i * a i := fun i =>
    (Nat.mul_div_cancel' (two_pow_run_dvd hn hN hc (t := T i))).symm
  have hk3 : ∀ i, orb n (T i + k i) + 1 = 3 ^ k i * a i := by
    intro i
    have h := odd_run_eq hn hN hc (t := T i) (k i) le_rfl
    rw [hka i] at h
    have h' : 2 ^ k i * (orb n (T i + k i) + 1) = 2 ^ k i * (3 ^ k i * a i) := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h'
  have hl2 : ∀ i, 2 ^ l i * orb n (T (i + 1)) = orb n (T i + k i) := by
    intro i
    have hlt := run_lt hn hN hc (hTmin i) (hTmin (i + 1)) (hTlt i)
    have h := even_run_eq hn hN hc (hTmin (i + 1)) (hTlt i) (hTbetween i) (l i) (by simp only [hl, hk]; omega)
    simp only [hl, hk] at h ⊢
    rwa [show T i + run hn hN hc (T i) + (T (i + 1) - T i - run hn hN hc (T i)) = T (i + 1) by omega] at h
  have hnext : ∀ i < m, orb n (T ((i + 1) % m)) = orb n (T (i + 1)) := by
    intro i hi
    rcases Nat.lt_or_ge (i + 1) m with h | h
    · rw [Nat.mod_eq_of_lt h]
    · have he : i + 1 = m := by omega
      rw [he, Nat.mod_self, hTm, orb_add_period hc]
  refine ⟨k, l, a, ⟨hmpos, fun i hi => ⟨run_pos hn hN hc (hTmin i), ?_, ?_, ?_⟩⟩, ?_⟩
  · have := run_lt hn hN hc (hTmin i) (hTmin (i + 1)) (hTlt i)
    simp only [hl, hk]; omega
  · have h := hka i
    have := orb_pos hn (T i)
    by_contra h0
    rw [show a i = 0 by omega, mul_zero] at h
    omega
  · -- the chain equation
    have e1 := hk3 i
    have e2 := hl2 i
    have e3 := hka ((i + 1) % m)
    rw [hnext i hi] at e3
    have e1' : ((orb n (T i + k i) : ℤ) + 1) = (3 : ℤ) ^ k i * a i := by exact_mod_cast e1
    have e2' : (2 : ℤ) ^ l i * orb n (T (i + 1)) = orb n (T i + k i) := by exact_mod_cast e2
    have e3' : ((orb n (T (i + 1)) : ℤ) + 1) = (2 : ℤ) ^ k ((i + 1) % m) * a ((i + 1) % m) := by
      exact_mod_cast e3
    rw [pow_add]
    linear_combination -e1' - e2' + (2 : ℤ) ^ l i * e3'
  · -- `K` is the number of odd steps
    have hodd : ∀ i, Nat.count (fun j => orb n j % 2 = 1) (T i) =
        Nat.count (fun j => orb n j % 2 = 1) (T 0) + ∑ j ∈ Finset.range i, k j := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        rw [count_block hn hN hc (hTmin i) (hTmin (i + 1)) (hTlt i) (hTbetween i) _ (fun _ => Iff.rfl), ih,
          Finset.sum_range_succ]
        ring
    have hw : Nat.count (fun j => orb n j % 2 = 1) (T 0 + N) =
        Nat.count (fun j => orb n j % 2 = 1) (T 0) + Nat.count (fun j => orb n j % 2 = 1) N := by
      rw [Nat.count_add, count_window (p := fun j => orb n j % 2 = 1) (fun j => by rw [orb_add_period hc])]
    have hN' : Nat.count (fun j => orb n j % 2 = 1) N = oddCount n N := by
      rw [Nat.count_eq_card_filter_range]; rfl
    have h := hodd m
    rw [hTm, hw, hN'] at h
    unfold Ksum
    omega

theorem cycle_K_lt_thm : cycle_K_lt := by
  intro n N hn hN hc hm82
  obtain ⟨k, l, a, hs, hK⟩ := cycle_chain_thm n N hn hN hc
  rw [← hK]
  exact chain_K_lt_thm _ k l a hs hm82

end Sdw2005
