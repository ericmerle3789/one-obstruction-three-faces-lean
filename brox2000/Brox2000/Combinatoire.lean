import Mathlib
import Brox2000.Brox_Enonces
import Sdw2005.Cycles
import Sdw2005.Pont

/-!
# Brox 2000 · the combinatorial facts on a positive cycle

For a cycle `C^[N] n = n` on the positive integers (`y j = C^[j] n`):
* descents (odd `y j` with `y (j + 1)` even) and local minima (odd `y j` with `y (j − 1)` even, cyclically) are
  equally many over `N` steps: both count the parity changes of one kind along the cycle;
* over the minimal period, `|Γ|` and `δ(Γ)` are these counts (values and terms agree, `Sdw2005/Pont.lean`);
* `2^j y_j ≤ 4^{K_j} y_0` (`K_j` odd terms among the first `j`), hence `N ≤ 2K` (Brox's Lemma 2.2);
* `2^j y_j = 3^{K_j} y_0 + G_j` with `0 ≤ G_j ≤ j 3^{K_j} 2^j`, hence `n ≤ N 3^K 2^N`.
-/

namespace Brox2000

open Sdw2005 Finset

/-- The descending terms over `N` steps: the `j < N` with `C^[j] n` odd and `C^[j + 1] n` even. -/
def descCount (n N : ℕ) : ℕ :=
  ((range N).filter (fun j => C^[j] n % 2 = 1 ∧ C^[j + 1] n % 2 = 0)).card

/-! ## `|Γ|` and `δ(Γ)` as counts of terms -/

theorem Gamma_card (n : ℕ) : (Gamma n).card = oddCount n (Function.minimalPeriod C n) :=
  oddValues_card_eq n

theorem descSet_card (n : ℕ) : (descSet n).card = descCount n (Function.minimalPeriod C n) := by
  unfold descSet Gamma oddValues orbitSet descCount
  rw [Finset.filter_filter, Finset.filter_image, Finset.card_image_of_injOn]
  · congr 1
    apply Finset.filter_congr
    intro j _
    simp only [Function.iterate_succ_apply']
  · apply injOn_minimalPeriod
    intro j hj
    exact Finset.mem_range.1 (Finset.mem_filter.1 hj).1

/-! ## Descents and local minima -/

/-- The indicator of a proposition, as a real number. -/
noncomputable def ind (p : Prop) [Decidable p] : ℝ := if p then 1 else 0

theorem card_filter_eq_sum (N : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (((range N).filter p).card : ℝ) = ∑ j ∈ range N, ind (p j) := by
  unfold ind
  rw [Finset.sum_boole]

theorem descCount_eq_minCount {n N : ℕ} (hN : 0 < N) (hc : C^[N] n = n) : descCount n N = minCount n N := by
  set o : ℕ → ℕ := fun j => C^[j] n % 2 with ho
  have hper : ∀ j, o (j + N) = o j := fun j => by
    simp only [ho]; rw [Function.iterate_add_apply, hc]
  have hmod : ∀ j, (o (j % N)) = o j := fun j => by
    conv_rhs => rw [← Nat.mod_add_div j N]
    induction j / N with
    | zero => simp
    | succ c ih => rw [Nat.mul_succ, ← Nat.add_assoc, hper, ih]
  have h01 : ∀ j, o j = 0 ∨ o j = 1 := fun j => by simp only [ho]; omega
  -- down and up transitions
  let D : ℕ → Prop := fun j => o j = 1 ∧ o (j + 1) = 0
  let U : ℕ → Prop := fun j => o j = 0 ∧ o (j + 1) = 1
  have hD : (descCount n N : ℝ) = ∑ j ∈ range N, ind (D j) := by
    rw [← card_filter_eq_sum]; rfl
  have hUper : ∀ j, ind (U (j % N)) = ind (U j) := fun j => by
    have h1 : o (j % N + 1) = o (j + 1) := by
      rw [← hmod (j + 1), ← hmod (j % N + 1), Nat.add_mod (j % N), Nat.mod_mod, ← Nat.add_mod]
    simp only [U, hmod j, h1]
  -- `minCount` counts `U (j + N − 1)`
  have hM : (minCount n N : ℝ) = ∑ j ∈ range N, ind (U ((N - 1 + j) % N)) := by
    unfold minCount
    rw [card_filter_eq_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hUper]
    have h2 : o (N - 1 + j + 1) = o j := by rw [show N - 1 + j + 1 = j + N by omega, hper]
    have h4 : o ((j + N - 1) % N) = o (N - 1 + j) := by rw [hmod, show j + N - 1 = N - 1 + j by omega]
    have key : (C^[j] n % 2 = 1 ∧ C^[(j + N - 1) % N] n % 2 = 0) ↔ U (N - 1 + j) := by
      show (o j = 1 ∧ o ((j + N - 1) % N) = 0) ↔ (o (N - 1 + j) = 0 ∧ o (N - 1 + j + 1) = 1)
      rw [h2, h4]; exact And.comm
    unfold ind
    exact if_congr key rfl rfl
  have hM' : (minCount n N : ℝ) = ∑ j ∈ range N, ind (U j) := by
    rw [hM, sum_rot N hN (fun j => ind (U j)) (N - 1)]
  -- telescoping: as many down as up transitions
  have htel : ∑ j ∈ range N, ((o j : ℝ) - o (j + 1)) = 0 := by
    rw [Finset.sum_range_sub' (fun j => (o j : ℝ)), show o N = o 0 by simpa using hper 0, sub_self]
  have hpt : ∀ j, ((o j : ℝ) - o (j + 1)) = ind (D j) - ind (U j) := by
    intro j
    rcases h01 j with h | h <;> rcases h01 (j + 1) with h' | h' <;> simp [D, U, ind, h, h']
  rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_sub_distrib, ← hD, ← hM', sub_eq_zero] at htel
  exact_mod_cast htel

/-! ## Lemma 2.2: `N ≤ 2K` -/

theorem oddCount_succ (n j : ℕ) :
    oddCount n (j + 1) = oddCount n j + if C^[j] n % 2 = 1 then 1 else 0 := by
  unfold oddCount
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]
    intro hm
    exact (Finset.notMem_range_self) (Finset.mem_filter.1 hm).1
  · rfl

theorem two_pow_orb_le {n : ℕ} (hn : 0 < n) (j : ℕ) : 2 ^ j * C^[j] n ≤ 4 ^ oddCount n j * n := by
  induction j with
  | zero => simp [oddCount]
  | succ j ih =>
    rw [oddCount_succ, Function.iterate_succ_apply']
    have hy : 0 < C^[j] n := orb_pos hn j
    rcases Nat.mod_two_eq_zero_or_one (C^[j] n) with h | h
    · have e := C_even h
      rw [ite_eq_right (by omega), Nat.add_zero, pow_succ]
      calc 2 ^ j * 2 * C (C^[j] n) = 2 ^ j * (2 * C (C^[j] n)) := by ring
        _ = 2 ^ j * C^[j] n := by rw [e]
        _ ≤ 4 ^ oddCount n j * n := ih
    · have e := C_odd h
      rw [ite_eq_left h, pow_succ, pow_succ]
      calc 2 ^ j * 2 * C (C^[j] n) = 2 ^ j * (2 * C (C^[j] n)) := by ring
        _ = 2 ^ j * (3 * C^[j] n + 1) := by rw [e]
        _ ≤ 2 ^ j * (4 * C^[j] n) := Nat.mul_le_mul_left _ (by omega)
        _ = 4 * (2 ^ j * C^[j] n) := by ring
        _ ≤ 4 * (4 ^ oddCount n j * n) := Nat.mul_le_mul_left _ ih
        _ = 4 ^ oddCount n j * 4 * n := by ring

theorem period_le_two_odd {n N : ℕ} (hn : 0 < n) (hc : C^[N] n = n) : N ≤ 2 * oddCount n N := by
  have h := two_pow_orb_le hn N
  rw [hc] at h
  have h2 : 2 ^ N ≤ 4 ^ oddCount n N := Nat.le_of_mul_le_mul_right h hn
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul] at h2
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2

/-! ## A bound for the elements -/

theorem orb_eq {n : ℕ} (j : ℕ) : ∃ G : ℕ, 2 ^ j * C^[j] n = 3 ^ oddCount n j * n + G ∧
    G ≤ j * 3 ^ oddCount n j * 2 ^ j ∧ (oddCount n j = 0 → G = 0) := by
  induction j with
  | zero => exact ⟨0, by simp [oddCount], by simp, fun _ => rfl⟩
  | succ j ih =>
    obtain ⟨G, hG, hGle, hG0⟩ := ih
    rw [oddCount_succ, Function.iterate_succ_apply']
    rcases Nat.mod_two_eq_zero_or_one (C^[j] n) with h | h
    · have e := C_even h
      rw [ite_eq_right (by omega), Nat.add_zero]
      refine ⟨G, ?_, ?_, hG0⟩
      · calc 2 ^ (j + 1) * C (C^[j] n) = 2 ^ j * (2 * C (C^[j] n)) := by ring
          _ = 3 ^ oddCount n j * n + G := by rw [e, hG]
      · calc G ≤ j * 3 ^ oddCount n j * 2 ^ j := hGle
          _ ≤ (j + 1) * 3 ^ oddCount n j * 2 ^ (j + 1) := by
            apply Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) (Nat.pow_le_pow_right (by norm_num) (by omega))
    · have e := C_odd h
      rw [ite_eq_left h]
      refine ⟨3 * G + 2 ^ j, ?_, ?_, fun h0 => by omega⟩
      · calc 2 ^ (j + 1) * C (C^[j] n) = 2 ^ j * (2 * C (C^[j] n)) := by ring
          _ = 2 ^ j * (3 * C^[j] n + 1) := by rw [e]
          _ = 3 * (2 ^ j * C^[j] n) + 2 ^ j := by ring
          _ = 3 ^ (oddCount n j + 1) * n + (3 * G + 2 ^ j) := by rw [hG]; ring
      · have h3 : 1 ≤ 3 ^ oddCount n j := Nat.one_le_pow _ _ (by norm_num)
        calc 3 * G + 2 ^ j ≤ 3 * (j * 3 ^ oddCount n j * 2 ^ j) + 3 ^ oddCount n j * 2 ^ j := by
              have : 2 ^ j ≤ 3 ^ oddCount n j * 2 ^ j := Nat.le_mul_of_pos_left _ h3
              omega
          _ = (3 * j + 1) * 3 ^ oddCount n j * 2 ^ j := by ring
          _ ≤ (j + 1) * 3 ^ (oddCount n j + 1) * 2 ^ (j + 1) := by
            have e1 : (j + 1) * 3 ^ (oddCount n j + 1) * 2 ^ (j + 1) =
                (6 * j + 6) * 3 ^ oddCount n j * 2 ^ j := by ring
            rw [e1]
            apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; omega

theorem elem_le {n N : ℕ} (hn : 0 < n) (hN : 0 < N) (hc : C^[N] n = n) :
    n ≤ N * 3 ^ oddCount n N * 2 ^ N := by
  obtain ⟨G, hG, hGle, hG0⟩ := orb_eq (n := n) N
  rw [hc] at hG
  by_cases hK : oddCount n N = 0
  · -- no odd step: `2^N n = n`, impossible
    rw [hG0 hK, hK, pow_zero, one_mul, Nat.add_zero] at hG
    have : 2 ≤ 2 ^ N := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN
    nlinarith
  · -- `2^N n = 3^K n + G` with `G ≥ 1`... in fact `G ≥ n`
    have hGpos : 0 < G := by
      by_contra h0
      have hG' : 2 ^ N * n = 3 ^ oddCount n N * n := by omega
      have h23 : 2 ^ N = 3 ^ oddCount n N := Nat.eq_of_mul_eq_mul_right hn hG'
      have h2 : 2 ∣ 3 ^ oddCount n N := by
        rw [← h23]; exact dvd_pow_self 2 hN.ne'
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2) (by norm_num)
    have hlt : 3 ^ oddCount n N < 2 ^ N := by
      by_contra hle
      rw [not_lt] at hle
      have : 2 ^ N * n ≤ 3 ^ oddCount n N * n := Nat.mul_le_mul_right n hle
      omega
    have hnG : n ≤ G := by
      have h1 : (3 ^ oddCount n N + 1) * n ≤ 2 ^ N * n := Nat.mul_le_mul_right n hlt
      nlinarith
    exact hnG.trans hGle

end Brox2000
