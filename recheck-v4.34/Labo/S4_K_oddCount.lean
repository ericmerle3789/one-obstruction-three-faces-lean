import Labo.S4_Enonces

/-!
# S4-A · prouveur P1 · oddCount (plumbing)
Idea: `card (filter p (range n)) = Σ_{i<n} [p i]`, then induction on `n` generalizing `x`,
peeling index `0` with `Finset.sum_range_succ'` and `T^[i+1] x = T^[i] (T x)`.
-/

namespace LaboF.P1

open LaboBP LaboF

theorem oddIdx_card_eq_sum (x : ℤ) (n : ℕ) :
    (oddIdx x n).card = ∑ i ∈ Finset.range n, (if T^[i] x % 2 = 1 then 1 else 0) := by
  unfold oddIdx
  rw [Finset.card_filter]

theorem count_pw_eq_sum (x : ℤ) (n : ℕ) :
    (pw T x n).count true = ∑ i ∈ Finset.range n, (if T^[i] x % 2 = 1 then 1 else 0) := by
  induction n generalizing x with
  | zero => simp [pw]
  | succ n ih =>
    rw [Finset.sum_range_succ']
    have hs : (∑ k ∈ Finset.range n, (if T^[k + 1] x % 2 = 1 then 1 else 0))
        = ∑ k ∈ Finset.range n, (if T^[k] (T x) % 2 = 1 then 1 else 0) :=
      Finset.sum_congr rfl (fun k _ => by rw [Function.iterate_succ_apply])
    rw [hs, ← ih (T x), Function.iterate_zero_apply]
    simp only [pw, List.count_cons]
    by_cases h : x % 2 = 1 <;> simp [h]

end LaboF.P1

theorem oddCount_thm : LaboF.oddCount_enonce := by
  intro x n
  rw [LaboF.P1.count_pw_eq_sum, LaboF.P1.oddIdx_card_eq_sum]
