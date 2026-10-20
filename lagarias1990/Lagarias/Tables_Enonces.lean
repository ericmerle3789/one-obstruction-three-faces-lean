import Mathlib
import Lagarias.L1990_Enonces

/-!
# Lagarias 1990 · FROZEN STATEMENTS for Table 3.1, p. 41 and the count of the proof of Theorem 3.3

Written before any proof. Table 2.2 statements are in `L1990_Enonces.lean`. Proofs: `Lagarias/Tables.lean`
(kernel computation, `decide +kernel`, no `native_decide`).

| paper | Lean | deviation |
|---|---|---|
| Table 3.1 (p. 41): for `k ≤ 149`, `k ≡ ±1 (6)`, the smallest positive `n0` in a primitive cycle of `T_k`, and the length of that cycle | `table3_1`, `table3_1_rows` | 48 rows: the printed `n0` is in a primitive cycle of the printed (minimal) length; the minimality of `n0` is NOT checked (out of scope) |
| row `k = 35`: `(7, 3)` | `table3_1_row35` | `{7, 28, 14}` is a cycle of `T_35` but NOT primitive (`(7,35) = 7`); the correct row is `(13, 8)`, minimality proved |
| row `k = 73`: `(19, 60)` | `table3_1_row73` | `19` is in a primitive cycle of length 60, but `5` is in one of length 12; the correct row is `(5, 12)`, minimality proved |
| p. 41: "for `n = 85, 107, 139` [the minimum of `|2ⁿ − 3^l|`] is at least `⅓·2ⁿ`" | `p41` | true for these `n`, which are the `k`'s; the periods of the cycles are `100, 106, 136`, and there it is false |
| proof of Thm 3.3 (p. 43): "at least `n^{−1} C(2n,n)` distinct primitive cycles" from the words of length `2n` with `n` ones | `thm3_3_count_printed_false` | for `n = 1`: `C(2,1)/1 = 2`, but `10` and `01` lie on one cycle (`{1, 2}`) |
-/

namespace Lagarias

open LaboBP LaboHH

/-- Table 3.1 (p. 41) as printed: `(k, n0, cycle length)`. -/
def table3_1 : List (ℤ × ℤ × ℕ) :=
  [(1, 1, 2), (5, 1, 3), (7, 5, 4), (11, 1, 6), (13, 1, 4), (17, 1, 7), (19, 5, 11), (23, 5, 5),
   (25, 7, 16), (29, 1, 5), (31, 13, 23), (35, 7, 3), (37, 19, 6), (41, 1, 20), (43, 1, 11),
   (47, 5, 18), (49, 25, 38), (53, 103, 29), (55, 1, 12), (59, 1, 28), (61, 1, 6), (65, 19, 24),
   (67, 17, 30), (71, 29, 10), (73, 19, 60),
   (77, 1, 38), (79, 1, 44), (83, 65, 24), (85, 7, 100), (89, 17, 17), (91, 1, 48), (95, 1, 72),
   (97, 1, 18), (101, 7, 14), (103, 5, 21), (107, 1, 106), (109, 19, 52), (113, 1, 29),
   (115, 13, 27), (119, 1, 75), (121, 5, 44), (125, 1, 7), (127, 1, 37), (131, 13, 26),
   (133, 11, 36), (137, 1, 14), (139, 11, 136), (143, 7, 140), (145, 1, 10), (149, 19, 59)]

/-- `n0` lies in a primitive cycle of `T_k` of minimal period `L`. -/
def PrimCycleOfLength (k n0 : ℤ) (L : ℕ) : Prop :=
  Int.gcd n0 k = 1 ∧ 0 < L ∧ (Tk k)^[L] n0 = n0 ∧ ∀ j ∈ Finset.Ico 1 L, (Tk k)^[j] n0 ≠ n0

/-- Table 3.1, 48 rows: the printed `n0` is in a primitive cycle of the printed length. -/
def table3_1_rows : Prop :=
  ∀ r ∈ table3_1, r.1 ≠ 35 → r.1 ≠ 73 → PrimCycleOfLength r.1 r.2.1 r.2.2

/-- Table 3.1, row `k = 35`. -/
def table3_1_row35 : Prop :=
  (Tk 35)^[3] 7 = 7 ∧ Int.gcd 7 35 = 7 ∧ PrimCycleOfLength 35 13 8 ∧
  ∀ n : ℤ, 0 < n → n < 13 → Int.gcd n 35 = 1 → ¬ ∃ p, 0 < p ∧ (Tk 35)^[p] n = n

/-- Table 3.1, row `k = 73`. -/
def table3_1_row73 : Prop :=
  PrimCycleOfLength 73 19 60 ∧ PrimCycleOfLength 73 5 12 ∧
  ∀ n : ℤ, 0 < n → n < 5 → Int.gcd n 73 = 1 → ¬ ∃ p, 0 < p ∧ (Tk 73)^[p] n = n

/-- p. 41. -/
def p41 : Prop :=
  (∀ n ∈ ([85, 107, 139] : List ℕ), ∀ l ≤ n, (2 : ℤ) ^ n ≤ 3 * |2 ^ n - 3 ^ l|) ∧
  PrimCycleOfLength 85 7 100 ∧ PrimCycleOfLength 107 1 106 ∧ PrimCycleOfLength 139 11 136 ∧
  (∀ n ∈ ([100, 106, 136] : List ℕ), ∃ l ≤ n, 3 * |(2 : ℤ) ^ n - 3 ^ l| < 2 ^ n)

/-- Proof of Theorem 3.3, the count `n^{−1} C(2n,n)`, for `n = 1`: the two words of length 2 with one 1
lie on a single cycle, while `C(2,1)/1 = 2`. -/
def thm3_3_count_printed_false : Prop :=
  Nat.choose 2 1 / 1 = 2 ∧ xv [true, false] = 1 ∧ xv [false, true] = 2 ∧
  collatzQ 1 = 2 ∧ collatzQ 2 = 1

end Lagarias
