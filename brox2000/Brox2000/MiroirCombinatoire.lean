import Mathlib
import Brox2000.Combinatoire
import Brox2000.MiroirCycles

/-!
# Brox 2000 · phase B: the combinatorial facts on a cycle of the `3x − 1` map

The mirror of `Brox2000/Combinatoire.lean` for `D(y) = y/2`, `(3y − 1)/2` on the positive integers (`y j = D^[j] n`):
* descents and local minima are equally many over a cycle (the same telescoping of the parity sequence);
* over the minimal period, `|Γ|` and `δ(Γ)` of the cycle of `D` are counts of terms;
* `2^j y_j ≤ 4^{K_j} y_0`, hence `N ≤ 2K`;
* `2^j y_j + G_j = 3^{K_j} y_0` with `0 ≤ G_j ≤ j 3^{K_j} 2^j`, hence `n ≤ N 3^K 2^N`.
None of this needs `n > 1`.
-/

namespace Brox2000.Miroir

open Finset
open Sdw2005 (sum_rot)

/-- The odd values of the cycle of `n` under `D` (the mirror of `Brox2000.Gamma`). -/
noncomputable def GammaD (n : ℕ) : Finset ℕ :=
  ((range (Function.minimalPeriod D n)).image (fun j => D^[j] n)).filter (fun x => x % 2 = 1)

/-- The `x ∈ GammaD n` with `D x` even. -/
noncomputable def descSetD (n : ℕ) : Finset ℕ := (GammaD n).filter (fun x => D x % 2 = 0)

/-- The descending terms over `N` steps: `j < N` with `D^[j] n` odd and `D^[j + 1] n` even. -/
def descCountD (n N : ℕ) : ℕ :=
  ((range N).filter (fun j => D^[j] n % 2 = 1 ∧ D^[j + 1] n % 2 = 0)).card

/-! ## `|Γ|` and `δ(Γ)` as counts of terms -/

theorem injOn_minimalPeriodD (n : ℕ) (s : Finset ℕ) (hs : ∀ j ∈ s, j < Function.minimalPeriod D n) :
    Set.InjOn (fun j => D^[j] n) (s : Set ℕ) := by
  intro i hi j hj hij
  exact Function.iterate_injOn_Iio_minimalPeriod (Set.mem_Iio.2 (hs i hi)) (Set.mem_Iio.2 (hs j hj)) hij

theorem GammaD_card (n : ℕ) : (GammaD n).card = oddCountD n (Function.minimalPeriod D n) := by
  unfold GammaD oddCountD
  rw [Finset.filter_image]
  apply Finset.card_image_of_injOn
  apply injOn_minimalPeriodD
  intro j hj
  exact Finset.mem_range.1 (Finset.mem_filter.1 hj).1

theorem descSetD_card (n : ℕ) : (descSetD n).card = descCountD n (Function.minimalPeriod D n) := by
  unfold descSetD GammaD descCountD
  rw [Finset.filter_filter, Finset.filter_image, Finset.card_image_of_injOn]
  · congr 1
    apply Finset.filter_congr
    intro j _
    simp only [Function.iterate_succ_apply']
  · apply injOn_minimalPeriodD
    intro j hj
    exact Finset.mem_range.1 (Finset.mem_filter.1 hj).1

/-! ## Descents and local minima -/

theorem descCountD_eq_minCountD {n N : ℕ} (hN : 0 < N) (hc : D^[N] n = n) : descCountD n N = minCountD n N := by
  set o : ℕ → ℕ := fun j => D^[j] n % 2 with ho
  have hper : ∀ j, o (j + N) = o j := fun j => by
    simp only [ho]; rw [Function.iterate_add_apply, hc]
  have hmod : ∀ j, (o (j % N)) = o j := fun j => by
    conv_rhs => rw [← Nat.mod_add_div j N]
    induction j / N with
    | zero => simp
    | succ c ih => rw [Nat.mul_succ, ← Nat.add_assoc, hper, ih]
  have h01 : ∀ j, o j = 0 ∨ o j = 1 := fun j => by simp only [ho]; omega
  -- down and up transitions
  let Dn : ℕ → Prop := fun j => o j = 1 ∧ o (j + 1) = 0
  let U : ℕ → Prop := fun j => o j = 0 ∧ o (j + 1) = 1
  have hD : (descCountD n N : ℝ) = ∑ j ∈ range N, ind (Dn j) := by
    rw [← card_filter_eq_sum]; rfl
  have hUper : ∀ j, ind (U (j % N)) = ind (U j) := fun j => by
    have h1 : o (j % N + 1) = o (j + 1) := by
      rw [← hmod (j + 1), ← hmod (j % N + 1), Nat.add_mod (j % N), Nat.mod_mod, ← Nat.add_mod]
    simp only [U, hmod j, h1]
  -- `minCountD` counts `U (j + N − 1)`
  have hM : (minCountD n N : ℝ) = ∑ j ∈ range N, ind (U ((N - 1 + j) % N)) := by
    unfold minCountD
    rw [card_filter_eq_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hUper]
    have h2 : o (N - 1 + j + 1) = o j := by rw [show N - 1 + j + 1 = j + N by omega, hper]
    have h4 : o ((j + N - 1) % N) = o (N - 1 + j) := by rw [hmod, show j + N - 1 = N - 1 + j by omega]
    have key : (D^[j] n % 2 = 1 ∧ D^[(j + N - 1) % N] n % 2 = 0) ↔ U (N - 1 + j) := by
      show (o j = 1 ∧ o ((j + N - 1) % N) = 0) ↔ (o (N - 1 + j) = 0 ∧ o (N - 1 + j + 1) = 1)
      rw [h2, h4]; exact And.comm
    unfold ind
    exact if_congr key rfl rfl
  have hM' : (minCountD n N : ℝ) = ∑ j ∈ range N, ind (U j) := by
    rw [hM, sum_rot N hN (fun j => ind (U j)) (N - 1)]
  -- telescoping: as many down as up transitions
  have htel : ∑ j ∈ range N, ((o j : ℝ) - o (j + 1)) = 0 := by
    rw [Finset.sum_range_sub' (fun j => (o j : ℝ)), show o N = o 0 by simpa using hper 0, sub_self]
  have hpt : ∀ j, ((o j : ℝ) - o (j + 1)) = ind (Dn j) - ind (U j) := by
    intro j
    rcases h01 j with h | h <;> rcases h01 (j + 1) with h' | h' <;> simp [Dn, U, ind, h, h']
  rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_sub_distrib, ← hD, ← hM', sub_eq_zero] at htel
  exact_mod_cast htel

/-! ## Lemma 2.2: `N ≤ 2K` (the period of `D` is at most twice the number of odd terms) -/

theorem oddCountD_succ (n j : ℕ) :
    oddCountD n (j + 1) = oddCountD n j + if D^[j] n % 2 = 1 then 1 else 0 := by
  unfold oddCountD
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]
    intro hm
    exact (Finset.notMem_range_self) (Finset.mem_filter.1 hm).1
  · rfl

theorem two_pow_orbD_le {n : ℕ} (j : ℕ) : 2 ^ j * D^[j] n ≤ 4 ^ oddCountD n j * n := by
  induction j with
  | zero => simp [oddCountD]
  | succ j ih =>
    rw [oddCountD_succ, Function.iterate_succ_apply']
    rcases Nat.mod_two_eq_zero_or_one (D^[j] n) with h | h
    · have e := D_even h
      rw [ite_eq_right (by omega), Nat.add_zero, pow_succ]
      calc 2 ^ j * 2 * D (D^[j] n) = 2 ^ j * (2 * D (D^[j] n)) := by ring
        _ = 2 ^ j * D^[j] n := by rw [e]
        _ ≤ 4 ^ oddCountD n j * n := ih
    · have e := D_odd h
      rw [ite_eq_left h, pow_succ, pow_succ]
      calc 2 ^ j * 2 * D (D^[j] n) = 2 ^ j * (2 * D (D^[j] n)) := by ring
        _ ≤ 2 ^ j * (4 * D^[j] n) := Nat.mul_le_mul_left _ (by omega)
        _ = 4 * (2 ^ j * D^[j] n) := by ring
        _ ≤ 4 * (4 ^ oddCountD n j * n) := Nat.mul_le_mul_left _ ih
        _ = 4 ^ oddCountD n j * 4 * n := by ring

theorem period_le_two_oddD {n N : ℕ} (hn : 0 < n) (hc : D^[N] n = n) : N ≤ 2 * oddCountD n N := by
  have h := two_pow_orbD_le (n := n) N
  rw [hc] at h
  have h2 : 2 ^ N ≤ 4 ^ oddCountD n N := Nat.le_of_mul_le_mul_right h hn
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul] at h2
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2

/-! ## A bound for the elements -/

theorem orb_eqD {n : ℕ} (j : ℕ) : ∃ G : ℕ, 2 ^ j * D^[j] n + G = 3 ^ oddCountD n j * n ∧
    G ≤ j * 3 ^ oddCountD n j * 2 ^ j ∧ (oddCountD n j = 0 → G = 0) := by
  induction j with
  | zero => exact ⟨0, by simp [oddCountD], by simp, fun _ => rfl⟩
  | succ j ih =>
    obtain ⟨G, hG, hGle, hG0⟩ := ih
    rw [oddCountD_succ, Function.iterate_succ_apply']
    rcases Nat.mod_two_eq_zero_or_one (D^[j] n) with h | h
    · have e := D_even h
      rw [ite_eq_right (by omega), Nat.add_zero]
      refine ⟨G, ?_, ?_, hG0⟩
      · calc 2 ^ (j + 1) * D (D^[j] n) + G = 2 ^ j * (2 * D (D^[j] n)) + G := by ring
          _ = 3 ^ oddCountD n j * n := by rw [e, hG]
      · calc G ≤ j * 3 ^ oddCountD n j * 2 ^ j := hGle
          _ ≤ (j + 1) * 3 ^ oddCountD n j * 2 ^ (j + 1) := by
            apply Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) (Nat.pow_le_pow_right (by norm_num) (by omega))
    · have e := D_odd h
      rw [ite_eq_left h]
      refine ⟨3 * G + 2 ^ j, ?_, ?_, fun h0 => by omega⟩
      · calc 2 ^ (j + 1) * D (D^[j] n) + (3 * G + 2 ^ j) = 2 ^ j * (2 * D (D^[j] n) + 1) + 3 * G := by ring
          _ = 2 ^ j * (3 * D^[j] n) + 3 * G := by rw [e]
          _ = 3 * (2 ^ j * D^[j] n + G) := by ring
          _ = 3 ^ (oddCountD n j + 1) * n := by rw [hG]; ring
      · have h3 : 1 ≤ 3 ^ oddCountD n j := Nat.one_le_pow _ _ (by norm_num)
        calc 3 * G + 2 ^ j ≤ 3 * (j * 3 ^ oddCountD n j * 2 ^ j) + 3 ^ oddCountD n j * 2 ^ j := by
              have : 2 ^ j ≤ 3 ^ oddCountD n j * 2 ^ j := Nat.le_mul_of_pos_left _ h3
              omega
          _ = (3 * j + 1) * 3 ^ oddCountD n j * 2 ^ j := by ring
          _ ≤ (j + 1) * 3 ^ (oddCountD n j + 1) * 2 ^ (j + 1) := by
            have e1 : (j + 1) * 3 ^ (oddCountD n j + 1) * 2 ^ (j + 1) =
                (6 * j + 6) * 3 ^ oddCountD n j * 2 ^ j := by ring
            rw [e1]
            apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; omega

theorem elem_leD {n N : ℕ} (hn : 0 < n) (hN : 0 < N) (hc : D^[N] n = n) :
    n ≤ N * 3 ^ oddCountD n N * 2 ^ N := by
  obtain ⟨G, hG, hGle, hG0⟩ := orb_eqD (n := n) N
  rw [hc] at hG
  by_cases hK : oddCountD n N = 0
  · -- no odd step: `2^N n = n`, impossible
    rw [hG0 hK, hK, pow_zero, one_mul, Nat.add_zero] at hG
    have : 2 ≤ 2 ^ N := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN
    nlinarith
  · -- `2^N n + G = 3^K n` with `G ≥ n`
    have hGpos : 0 < G := by
      by_contra h0
      have hG' : 2 ^ N * n = 3 ^ oddCountD n N * n := by omega
      have h23 : 2 ^ N = 3 ^ oddCountD n N := Nat.eq_of_mul_eq_mul_right hn hG'
      have h2 : 2 ∣ 3 ^ oddCountD n N := by
        rw [← h23]; exact dvd_pow_self 2 hN.ne'
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2) (by norm_num)
    have hlt : 2 ^ N < 3 ^ oddCountD n N := by
      by_contra hle
      rw [not_lt] at hle
      have : 3 ^ oddCountD n N * n ≤ 2 ^ N * n := Nat.mul_le_mul_right n hle
      omega
    have hnG : n ≤ G := by
      have h1 : (2 ^ N + 1) * n ≤ 3 ^ oddCountD n N * n := Nat.mul_le_mul_right n hlt
      nlinarith
    exact hnG.trans hGle

end Brox2000.Miroir
