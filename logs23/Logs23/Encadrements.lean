import Mathlib

/-!
# Logs23 · proofs (1): certified enclosures of `log 2` and `log 3`

`log 2 = 2 artanh(1/3)` and `log (3/2) = 2 artanh(1/5)`, with the partial sums
`∑_{i<n} x^(2i+1)/(2i+1)` and the remainder bounds of Mathlib (`Real.sum_range_le_log_div`,
`Real.log_div_le_sum_range_add`). The partial sums are rational numbers computed by `atanhSum`; the comparisons
between such rationals are checked by the kernel (`decide +kernel`). Widths: below `10^(−211)`.
-/

namespace Logs23

/-- `∑_{i<n} x^(2i+1)/(2i+1)` in `ℚ`, by recursion on `n`. -/
def atanhSum (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => atanhSum x n + x ^ (2 * n + 1) / (2 * n + 1)

theorem atanhSum_cast (x : ℚ) (n : ℕ) :
    ((atanhSum x n : ℚ) : ℝ) = ∑ i ∈ Finset.range n, (x : ℝ) ^ (2 * i + 1) / (2 * i + 1) := by
  induction n with
  | zero => simp [atanhSum]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp only [atanhSum]
    push_cast
    ring

/-- The enclosure of `(1/2) log ((1 + x)/(1 − x))` given by `n` terms, for `0 ≤ x < 1`. -/
theorem half_log_bounds {x : ℚ} (h₀ : 0 ≤ x) (h₁ : x < 1) (n : ℕ) :
    ((atanhSum x n : ℚ) : ℝ) ≤ 1 / 2 * Real.log ((1 + x) / (1 - x)) ∧
      1 / 2 * Real.log ((1 + x) / (1 - x)) ≤
        ((atanhSum x n + x ^ (2 * n + 1) / (1 - x ^ 2) : ℚ) : ℝ) := by
  have h₀' : (0 : ℝ) ≤ x := by exact_mod_cast h₀
  have h₁' : (x : ℝ) < 1 := by exact_mod_cast h₁
  refine ⟨?_, ?_⟩
  · rw [atanhSum_cast]
    exact Real.sum_range_le_log_div h₀' h₁' n
  · push_cast
    rw [atanhSum_cast]
    exact Real.log_div_le_sum_range_add h₀' h₁' n

/-- Lower end for `log 2`. -/
def L2lo : ℚ := 2 * atanhSum (1 / 3) 221
/-- Upper end for `log 2`. -/
def L2hi : ℚ := 2 * (atanhSum (1 / 3) 221 + (1 / 3) ^ (2 * 221 + 1) / (1 - (1 / 3) ^ 2))
/-- Lower end for `log (3/2)`. -/
def L32lo : ℚ := 2 * atanhSum (1 / 5) 155
/-- Upper end for `log (3/2)`. -/
def L32hi : ℚ := 2 * (atanhSum (1 / 5) 155 + (1 / 5) ^ (2 * 155 + 1) / (1 - (1 / 5) ^ 2))

theorem log_two_bounds : (L2lo : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (L2hi : ℝ) := by
  obtain ⟨h1, h2⟩ := half_log_bounds (x := 1 / 3) (by norm_num) (by norm_num) 221
  have e : (1 + ((1 / 3 : ℚ) : ℝ)) / (1 - ((1 / 3 : ℚ) : ℝ)) = 2 := by norm_num
  rw [e] at h1 h2
  unfold L2lo L2hi
  push_cast at h1 h2 ⊢
  constructor <;> linarith

theorem log_three_halves_bounds : (L32lo : ℝ) ≤ Real.log (3 / 2) ∧ Real.log (3 / 2) ≤ (L32hi : ℝ) := by
  obtain ⟨h1, h2⟩ := half_log_bounds (x := 1 / 5) (by norm_num) (by norm_num) 155
  have e : (1 + ((1 / 5 : ℚ) : ℝ)) / (1 - ((1 / 5 : ℚ) : ℝ)) = 3 / 2 := by norm_num
  rw [e] at h1 h2
  unfold L32lo L32hi
  push_cast at h1 h2 ⊢
  constructor <;> linarith

theorem log_three_eq : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
  rw [← Real.log_mul (by norm_num) (by norm_num)]
  norm_num

theorem log_three_bounds :
    ((L2lo + L32lo : ℚ) : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ ((L2hi + L32hi : ℚ) : ℝ) := by
  obtain ⟨a, b⟩ := log_two_bounds
  obtain ⟨c, d⟩ := log_three_halves_bounds
  rw [log_three_eq]
  push_cast
  constructor <;> linarith

/-- The widths, checked by the kernel. -/
theorem widths : L2hi - L2lo < 1 / 10 ^ 211 ∧ L32hi - L32lo < 1 / 10 ^ 211 := by
  decide +kernel

end Logs23
