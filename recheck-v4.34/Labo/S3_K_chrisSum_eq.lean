import Labo.S3_Enonces
-- S3-A · A4 formaliste (2026-09-26) : copie signée de Labo/Tent_chrisSum_eq_P2.lean (sha16 b47fde8eedb7daa9), re-jugée sous l'oracle.

/-!
# S3-A · prouveur P2 · node `chrisSum_eq` (K★(b), plumbing)
Idea: induction on the number `k` of blocks with `S k = Σ_{j<k} 2^{⌊Nj/r⌋} 3^{k-1-j}`:
`C_3(P (k+1)) = 3 · C_3(P k) + 2^{|P k|}` by `Ca_append`, with `|P k| = ⌊Nk/r⌋`; `r = 0` apart.
-/

namespace P2Chris
open LaboBP LaboK

/-- Block `j` of the Knight word. -/
def blk (N r j : ℕ) : List Bool :=
  true :: List.replicate (N * (j + 1) / r - N * j / r - 1) false

theorem step_pos (N r j : ℕ) (hr : 0 < r) (hrN : r ≤ N) :
    N * j / r + 1 ≤ N * (j + 1) / r := by
  have h1 : (N * j + r) / r = N * j / r + 1 := Nat.add_div_right _ hr
  have h2 : (N * j + r) / r ≤ (N * j + N) / r := Nat.div_le_div_right (by omega)
  have h3 : N * (j + 1) = N * j + N := by ring
  rw [h3]; omega

theorem prefix_len (N r : ℕ) (hr : 0 < r) (hrN : r ≤ N) (k : ℕ) :
    (((List.range k).map (blk N r)).flatten).length = N * k / r := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.flatten_append]
    have hs := step_pos N r k hr hrN
    simp only [List.length_append, ih, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.append_nil, blk, List.length_cons, List.length_replicate]
    omega

theorem Ca_rep (n : ℕ) : Ca 3 (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, Ca, ih]

theorem prefix_C (N r : ℕ) (hr : 0 < r) (hrN : r ≤ N) (k : ℕ) :
    Ca 3 (((List.range k).map (blk N r)).flatten) =
      ∑ j ∈ Finset.range k, 2 ^ (N * j / r) * 3 ^ (k - 1 - j) := by
  induction k with
  | zero => simp [Ca]
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, Ca_append, ih, prefix_len N r hr hrN k]
    have hc : (([k].map (blk N r)).flatten).count true = 1 := by
      simp [blk, List.count_replicate]
    have hC : Ca 3 (([k].map (blk N r)).flatten) = 1 := by
      simp [blk, Ca, Ca_rep, List.count_replicate]
    rw [hc, hC, Finset.sum_range_succ, pow_one, mul_one, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl (fun j hj => ?_)
      have hj' := Finset.mem_range.mp hj
      have e : k + 1 - 1 - j = (k - 1 - j) + 1 := by omega
      rw [e, pow_succ]; ring
    · simp

end P2Chris

theorem chrisSum_eq_thm : LaboK.chrisSum_eq_enonce := by
  intro N r hrN
  rcases Nat.eq_zero_or_pos r with h0 | hr
  · subst h0; simp [LaboK.ChrisSum, LaboK.knightWord, LaboBP.C]
  · have e : LaboK.knightWord N r = ((List.range r).map (P2Chris.blk N r)).flatten := rfl
    rw [e, ← LaboBP.Ca_three, P2Chris.prefix_C N r hr hrN r]
    rfl
