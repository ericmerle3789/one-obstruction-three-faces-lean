import Labo.S3_Enonces
-- S3-A · A4 formaliste (2026-09-26) : copie signée de Labo/Tent_knightWord_shape_P2.lean (sha16 9d529ef2bafdf1ea), re-jugée sous l'oracle.

/-!
# S3-A · prouveur P2 · node `knightWord_shape` (K★(b), plumbing)
Idea: induction on the number `k` of blocks; the prefix of `k` blocks has length `⌊Nk/r⌋`
(each block has length `⌊N(j+1)/r⌋ - ⌊Nj/r⌋ ≥ 1` because `r ≤ N`) and exactly `k` ones.
-/

namespace P2Shape
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

theorem prefix_shape (N r : ℕ) (hr : 0 < r) (hrN : r ≤ N) (k : ℕ) :
    (((List.range k).map (blk N r)).flatten).length = N * k / r ∧
    (((List.range k).map (blk N r)).flatten).count true = k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.flatten_append]
    have hs := step_pos N r k hr hrN
    refine ⟨?_, ?_⟩
    · simp only [List.length_append, ih.1, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil, blk, List.length_cons, List.length_replicate]
      omega
    · simp [List.count_append, ih.2, blk, List.count_replicate]

end P2Shape

theorem knightWord_shape_thm : LaboK.knightWord_shape_enonce := by
  intro N r h1 h2
  have hs := P2Shape.prefix_shape N r h1 h2 r
  have e : LaboK.knightWord N r = ((List.range r).map (P2Shape.blk N r)).flatten := rfl
  rw [e]
  exact ⟨by rw [hs.1, Nat.mul_div_cancel N h1], hs.2⟩
