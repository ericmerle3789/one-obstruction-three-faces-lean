import Mathlib

/-!
# Seifert 1988 · FROZEN STATEMENTS

B. G. Seifert, *On the arithmetic of cycles for the Collatz–Hasse ('Syracuse') conjectures*, Discrete Mathematics 68
(1988), 293–298, DOI 10.1016/0012-365X(88)90121-5.

Written and committed before the proofs. Each statement is a `def … : Prop`; its proof is `…_thm`, and
`Seifert1988/Axiomes.lean` checks `example : X := X_thm` for each of them. This file proves nothing about the
conjecture: Seifert's theorems are arithmetic criteria for cycles.

**Reading of the length vector.** Definition 1.1 of the paper reads the vector forwards along the orbit:
`f^i(n) = 2^(−z(i)) (3 f^(i−1)(n) + ε)`, and the two worked examples of the paper use that reading. The printed
formula (e), and with it (1.2), (1.2'), the difference in the proof of Corollary 1 and Theorem 2, read it backwards. So
`e` below is the formula that fits Definition 1.1 and the examples, `ePrinted` is the printed one, and
`printed_e_reverse` says `ePrinted z = e z.reverse`. The statements marked "repaired" are what is proved with that reading. For `ε = 1`, printed (1.2') and Theorem 1(b),
and Theorem 2 with the numerator of (1.3), are neither proved nor refuted here: the README says why.
-/

namespace Seifert

open Function

/-- `ε = +1` or `ε = −1`. -/
def IsSign (ε : ℤ) : Prop := ε = 1 ∨ ε = -1

/-- The domain of `f_ε`: the positive odd integers. -/
def PosOdd (n : ℤ) : Prop := 0 < n ∧ Odd n

/-- `k` in eq. (1): the exponent of the highest power of 2 dividing `3n + ε`. -/
def val (ε n : ℤ) : ℕ := padicValInt 2 (3 * n + ε)

/-- Eq. (1): `f_ε(n) = 2^(−k) (3n + ε)`. -/
def f (ε n : ℤ) : ℤ := (3 * n + ε) / 2 ^ val ε n

/-- Definition 1.1: `n` is a cyclic point of `f_ε`. -/
def IsCyclic (ε n : ℤ) : Prop := PosOdd n ∧ ∃ r : ℕ, 0 < r ∧ (f ε)^[r] n = n

/-- Definition 1.1: the length vector of `n`. Its length `r` is the number of distinct points of the cycle, which is
the minimal period; its `i`-th coordinate is the exponent of the step from `f^(i−1)(n)` to `f^i(n)`. -/
noncomputable def lengthVector (ε n : ℤ) : List ℕ :=
  (List.range (minimalPeriod (f ε) n)).map fun i => val ε ((f ε)^[i] n)

/-- `z` occurs as the length vector of a cyclic point. -/
def IsLengthVector (ε : ℤ) (z : List ℕ) : Prop := ∃ n, IsCyclic ε n ∧ lengthVector ε n = z

/-- Condition α) of Theorem 1: the cyclic group acts freely on the orbit of `z`. -/
def Free (z : List ℕ) : Prop := ∀ k, 0 < k → k < z.length → z.rotate k ≠ z

/-- (d.ε): `d(ε, r)(z) = ε (2^(z(1)+…+z(r)) − 3^r)`. -/
def d (ε : ℤ) (z : List ℕ) : ℤ := ε * (2 ^ z.sum - 3 ^ z.length)

/-- The numerator that fits Definition 1.1 and the examples:
`∑_{j=0}^{r−1} 3^j 2^(z(1)+…+z(r−1−j))`. -/
def e (z : List ℕ) : ℕ :=
  ∑ j ∈ Finset.range z.length, 3 ^ j * 2 ^ (z.take (z.length - 1 - j)).sum

/-- (e) as printed: `∑_{j=0}^{r−1} 3^j 2^(∑_{i=j+2}^{r} z(i))`; `z.drop (j+1)` is `(z(j+2), …, z(r))`. -/
def ePrinted (z : List ℕ) : ℕ :=
  ∑ j ∈ Finset.range z.length, 3 ^ j * 2 ^ (z.drop (j + 1)).sum

/-- The exponent of Theorem 2, repaired: `z(1)+…+z(r−1) − (r−1)`. -/
def H (z : List ℕ) : ℕ := z.dropLast.sum - (z.length - 1)

/-- Conjecture (S). -/
def S_plus : Prop := ∀ n, PosOdd n → ∃ k : ℕ, (f 1)^[k] n = 1

/-- Conjecture (S'): every orbit reaches one of the cycles (1), (5 7), (17 25 37 55 41 61 91). -/
def S_minus : Prop :=
  ∀ n, PosOdd n → ∃ k : ℕ, (f (-1))^[k] n ∈ ({1, 5, 7, 17, 25, 37, 55, 41, 61, 91} : Set ℤ)

/-! ## The map and the two functions -/

/-- Introduction: `f_ε` maps the positive odd integers to themselves, with a positive exponent. -/
def f_maps : Prop :=
  ∀ ε n, IsSign ε → PosOdd n → PosOdd (f ε n) ∧ 0 < val ε n ∧ 2 ^ val ε n * f ε n = 3 * n + ε

/-- Introduction: `d(−1, r) = −d(1, r)`. -/
def d_neg : Prop := ∀ z, d (-1) z = - d 1 z

/-- Proof of Corollary 1: `d` is invariant under all permutations of the coordinates. -/
def d_perm : Prop := ∀ ε z z', List.Perm z z' → d ε z = d ε z'

/-- (1.2), repaired: `3^r n + ε e(z) = 2^(z(1)+…+z(r)) f^r(n)` along any piece of orbit. -/
def formula_1_2 : Prop :=
  ∀ ε n (r : ℕ), IsSign ε → PosOdd n →
    ∀ z, z = (List.range r).map (fun i => val ε ((f ε)^[i] n)) →
      3 ^ r * n + ε * (e z : ℤ) = 2 ^ z.sum * (f ε)^[r] n

/-- (1.2'), repaired: a cyclic point is `e(z) / d(ε, r)(z)`. -/
def formula_1_2' : Prop :=
  ∀ ε n, IsSign ε → IsCyclic ε n → d ε (lengthVector ε n) * n = e (lengthVector ε n)

/-- A length vector is non-empty with positive coordinates. -/
def lengthVector_pos : Prop :=
  ∀ ε n, IsSign ε → IsCyclic ε n → lengthVector ε n ≠ [] ∧ ∀ a ∈ lengthVector ε n, 0 < a

/-! ## Theorem 1 -/

/-- Theorem 1(a), first part: a cyclic point is determined by its length vector. -/
def thm1a_unique : Prop :=
  ∀ ε n m, IsSign ε → IsCyclic ε n → IsCyclic ε m → lengthVector ε n = lengthVector ε m → n = m

/-- Theorem 1(a), second part: `f^k(n(z)) = n(g^k(z))`. -/
def thm1a_rotate : Prop :=
  ∀ ε n (k : ℕ), IsSign ε → IsCyclic ε n →
    IsCyclic ε ((f ε)^[k] n) ∧ lengthVector ε ((f ε)^[k] n) = (lengthVector ε n).rotate k

/-- Theorem 1(b), repaired (`e` for the printed `e`): `z` is a length vector iff α) `G(r)` acts freely on its orbit,
β) `d > 0`, γ) the ideal `⟨d⟩` contains the ideal generated by the `e(g z)`. -/
def thm1b : Prop :=
  ∀ ε z, IsSign ε → z ≠ [] → (∀ a ∈ z, 0 < a) →
    (IsLengthVector ε z ↔ Free z ∧ 0 < d ε z ∧
      Ideal.span (Set.range fun k : ℕ => (e (z.rotate k) : ℤ)) ≤ Ideal.span {d ε z})

/-- The closing remark on the "explicit computational criterion", repaired: one divisibility suffices.
Freeness must stay, see `free_essential`. -/
def thm1b_single : Prop :=
  ∀ ε z, IsSign ε → z ≠ [] → (∀ a ∈ z, 0 < a) →
    (IsLengthVector ε z ↔ Free z ∧ 0 < d ε z ∧ d ε z ∣ (e z : ℤ))

/-- "The hypothesis that `G(r)` acts freely is essential": for `z = (1, 1)`, `ε = −1`, `e/d` is a positive integer
and `z` is not a length vector. -/
def free_essential : Prop :=
  0 < d (-1) [1, 1] ∧ d (-1) [1, 1] ∣ (e [1, 1] : ℤ) ∧ ¬ IsLengthVector (-1) [1, 1]

/-- The examples of the paper: 5 and 17 for `f_{−1}`, with their `z`, `e`, `d`. Beyond its list: the fixed point 1 of each `f_ε`. -/
def examples : Prop :=
  IsCyclic (-1) 5 ∧ lengthVector (-1) 5 = [1, 2] ∧ e [1, 2] = 5 ∧ d (-1) [1, 2] = 1 ∧
  IsCyclic (-1) 17 ∧ lengthVector (-1) 17 = [1, 1, 1, 2, 1, 1, 4] ∧
    e [1, 1, 1, 2, 1, 1, 4] = 2363 ∧ d (-1) [1, 1, 1, 2, 1, 1, 4] = 139 ∧
  IsCyclic 1 1 ∧ lengthVector 1 1 = [2] ∧ IsCyclic (-1) 1 ∧ lengthVector (-1) 1 = [1]

/-- The remark after Theorem 1 says `e(z)/d(+1, r)(z) = 1` for `z = (1, …, 1)`. In fact that quotient is `−1`, it is `1`
with `d(−1, r)`, and the vector of the sequence `1 1 …` of `f_1` is `(2, …, 2)`. -/
def remark_constant : Prop :=
  ∀ r : ℕ, 0 < r →
    (e (List.replicate r 1) : ℤ) = 3 ^ r - 2 ^ r ∧
    d 1 (List.replicate r 1) = -(3 ^ r - 2 ^ r) ∧
    d (-1) (List.replicate r 1) = 3 ^ r - 2 ^ r ∧
    (e (List.replicate r 2) : ℤ) = d 1 (List.replicate r 2)

/-! ## The printed formula -/

/-- The printed (e) is `e` of the reversed vector. -/
def printed_e_reverse : Prop := ∀ z, ePrinted z = e z.reverse

/-- The printed (e) disagrees with the examples of the paper, which give 5 and 2363; `139 ∤ 13801`. -/
def printed_e_examples : Prop :=
  ePrinted [1, 2] = 7 ∧ ePrinted [1, 1, 1, 2, 1, 1, 4] = 13801 ∧ ¬ (139 : ℤ) ∣ 13801

/-- Theorem 1(b) (i) ⇒ (ii) γ) fails with the printed (e) and Definition 1.1. -/
def thm1b_printed_false : Prop :=
  ¬ ∀ z, IsLengthVector (-1) z → ∀ k : ℕ, d (-1) z ∣ (ePrinted (z.rotate k) : ℤ)

/-- Theorem 1(b) with the printed (e) holds for the vector read backwards. -/
def thm1b_reversed : Prop :=
  ∀ ε z, IsSign ε → z ≠ [] → (∀ a ∈ z, 0 < a) →
    (IsLengthVector ε z.reverse ↔ Free z ∧ 0 < d ε z ∧ ∀ k : ℕ, d ε z ∣ (ePrinted (z.rotate k) : ℤ))

/-! ## Corollary 1 -/

/-- The difference in the proof of Corollary 1, as printed. -/
def cor1_difference_printed : Prop :=
  ∀ a b w, (ePrinted (a :: b :: w) : ℤ) - ePrinted (b :: a :: w) = (2 ^ b - 2 ^ a) * 2 ^ w.sum

/-- The same difference for `e`. -/
def cor1_difference : Prop :=
  ∀ a b w, (e (a :: b :: w) : ℤ) - e (b :: a :: w) = (2 ^ a - 2 ^ b) * 3 ^ w.length

/-- Corollary 1 is false as printed: `(1, 2)` and `(2, 1)` are the length vectors of 5 and 7 for `f_{−1}`. -/
def cor1_printed_false : Prop :=
  ¬ ∀ ε a b w, IsSign ε → IsLengthVector ε (a :: b :: w) → b :: a :: w ≠ a :: b :: w →
    ¬ IsLengthVector ε (b :: a :: w)

/-- What the proof of Corollary 1 does give: `d` divides `2^|z(1)−z(2)| − 1`. -/
def cor1_divides : Prop :=
  ∀ ε a b w, IsSign ε → IsLengthVector ε (a :: b :: w) → IsLengthVector ε (b :: a :: w) →
    d ε (a :: b :: w) ∣ (2 : ℤ) ^ (max a b - min a b) - 1

/-- An arithmetic input not in the paper: `|2^l − 3^r| ≥ 2^(l−r)` for `r ≥ 3`. A finite check by the kernel for `r ≤ 20000`,
`lam_lower` of `../logs23/` above. -/
def near_miss : Prop := ∀ r l : ℕ, 3 ≤ r → (2 : ℤ) ^ l ≤ 2 ^ r * |(2 : ℤ) ^ l - 3 ^ r|

/-- Corollary 1, repaired: the only counterexample is the cycle (5 7) of `f_{−1}`. -/
def cor1_exact : Prop :=
  ∀ ε a b w, IsSign ε → IsLengthVector ε (a :: b :: w) → IsLengthVector ε (b :: a :: w) → a ≠ b →
    ε = -1 ∧ w = [] ∧ ((a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1))

/-- The same at any two adjacent positions. -/
def cor1_exact_anywhere : Prop :=
  ∀ ε u a b v, IsSign ε → IsLengthVector ε (u ++ a :: b :: v) → IsLengthVector ε (u ++ b :: a :: v) → a ≠ b →
    ε = -1 ∧ u = [] ∧ v = [] ∧ ((a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1))

/-! ## Corollary 2 -/

/-- The step of the proof of Corollary 2: a solution of (E.ε) with `r ≥ 2` gives a cycle of length `r`, since `d = 1`.
By `gersonides_plus` and `gersonides_minus` the hypothesis has one solution, `(l, r, ε) = (3, 2, −1)`: this statement has a
single instance, the cycle (5 7). -/
def solution_gives_cycle : Prop :=
  ∀ ε (l r : ℕ), IsSign ε → 2 ≤ r → (2 : ℤ) ^ l - 3 ^ r = ε →
    IsLengthVector ε ((l - r + 1) :: List.replicate (r - 1) 1)

/-- Corollary 2 for (S). -/
def cor2_plus : Prop :=
  S_plus → ∀ l r : ℕ, 0 < l → 0 < r → (2 : ℤ) ^ l - 3 ^ r = 1 → l = 2 ∧ r = 1

/-- Corollary 2 for (S'). -/
def cor2_minus : Prop :=
  S_minus → ∀ l r : ℕ, 0 < l → 0 < r → (2 : ℤ) ^ l - 3 ^ r = -1 → (l = 1 ∧ r = 1) ∨ (l = 3 ∧ r = 2)

/-- The conclusion of Corollary 2 holds without (S): the classical solution of `2^l − 3^r = 1` (Levi ben Gerson). -/
def gersonides_plus : Prop := ∀ l r : ℕ, 0 < r → (2 : ℤ) ^ l - 3 ^ r = 1 → l = 2 ∧ r = 1

/-- The conclusion of Corollary 2 holds without (S'): the classical solution of `2^l − 3^r = −1`. -/
def gersonides_minus : Prop :=
  ∀ l r : ℕ, 0 < l → 0 < r → (2 : ℤ) ^ l - 3 ^ r = -1 → (l = 1 ∧ r = 1) ∨ (l = 3 ∧ r = 2)

/-! ## Theorem 2 -/

/-- Theorem 2, first inequality, repaired: `n ≤ 2^(z(1)+…+z(r−1)−r+1) (3^r − 2^r) / d`. -/
def thm2 : Prop :=
  ∀ ε n z, IsSign ε → IsCyclic ε n → lengthVector ε n = z →
    d ε z * n ≤ 2 ^ H z * (3 ^ z.length - 2 ^ z.length)

/-- Theorem 2, second inequality, repaired (`ε = 1`): `n ≤ 2^(z(1)+…+z(r−1)−r+1) (2^l − 2^r) / d`. -/
def thm2_plus : Prop :=
  ∀ n z, IsCyclic 1 n → lengthVector 1 n = z →
    d 1 z * n ≤ 2 ^ H z * (2 ^ z.sum - 2 ^ z.length)

/-- Theorem 2 fails as printed, with Definition 1.1: `n = 7`, `z = (2, 1)`, `ε = −1`: the printed exponent
`z(2) − 2 + 1` is 0 and the bound is `(3² − 2²) / 1 = 5`. The display of the theorem prints the numerator `3^r − 3^r`, a
misprint (read literally, the bound is 0); the numerator used here is the `3^r − 2^r` of (1.3) in the proof.
This comment was corrected on 2026-11-07 after reading the page images; the statement itself is unchanged. -/
def thm2_printed_false : Prop :=
  IsCyclic (-1) 7 ∧ lengthVector (-1) 7 = [2, 1] ∧
    ¬ (d (-1) [2, 1] * 7 ≤ 2 ^ ((([2, 1] : List ℕ).drop 1).sum - (([2, 1] : List ℕ).length - 1)) * (3 ^ 2 - 2 ^ 2))

/-- The exponent of the repaired Theorem 2 is the printed exponent of the vector read backwards. -/
def thm2_reversed : Prop := ∀ z, H z = (z.reverse.drop 1).sum - (z.length - 1)

end Seifert
