import Mathlib
import Labo.HH1997_Preuves

/-!
# Lagarias 1990 · FROZEN STATEMENTS (phase 2a)

J. C. Lagarias, *The set of rational cycles for the 3x+1 problem*, Acta Arith. 56 (1990) 33–53
(read at source: `LABO-COLLATZ/calculs/bibliothecaire/lag1990_full/aa5614.pdf`, 21 pp.).

This file contains ONLY definitions and `def <X> : Prop` statements, written before any proof.
Proofs: `Lagarias/L2_Preuves.lean`, `L3_Preuves.lean`, `L4_Preuves.lean`, `Tables.lean`.
It reuses, without redefining, from the copied hh1997 files (commit 36d5136): `LaboBP.C` (= `N(v)`, (2.7b)),
`LaboBP.d` (= `D(v)`, (2.7a)), `LaboHH.collatzQ` (= `T` on ℚ, parity of the reduced numerator),
`LaboHH.gStep`/`phiMap` (= `U_0`, `U_1` and the composition (2.2)).
Words are `List Bool` (`true` = 1); the first letter is the parity of the starting point.

**Rule.** When a printed statement is false or its proof has a gap, the REPAIRED statement is formalised, and
the printed one is recorded next to it (often as a `…_printed_false` counterexample).

## Line-by-line comparison with the paper

| paper | Lean | deviation |
|---|---|---|
| (2.1), (1.2): `x(v) = (2ⁿ − 3^{v_0+…+v_{n−1}})^{−1} Σ_j v_j 3^{v_{j+1}+…+v_{n−1}} 2^j` | `xv`, `eq2_1` | none |
| Thm 2.1 (p. 36): `x(v)` is the unique `x ∈ Q_(2)` periodic of period `n` whose parity sequence starts with `v` | `thm2_1` | `v ≠ []`; "period n" = `T^n x = x` (not necessarily minimal), as in the paper |
| (1.3) (p. 34): such rationals are exactly `Σ_{j=0}^k 3^j 2^{a(j)} / (2ⁿ − 3^{k+1})`, `n > a(0) > … > a(k) ≥ 0` | `S3`, `eq1_3` | the exponents are a strictly decreasing list; `x = 0` (`v = 0ⁿ`, empty sum) is NOT of this form: excluded by `true ∈ v` |
| Cor. 2.1a (p. 37): for fixed `k`, the `Σ_{i=0}^k 2^{a_i} 3^i`, `a_0 > … > a_k ≥ 0`, are distinct | `cor2_1a` | none; two proofs (Lagarias's via Thm 2.1, Coppersmith's 2-adic one) |
| (word form, used in Thm 4.1 p. 48) | `cor2_1a_words` | same length, same weight |
| p. 37: `2⁴ + 3 = 2² + 2·3 + 3² = 19` | `ex_p37` | none |
| proof of Cor. 2.1a: `x(v) = (2ⁿ − 3^k)^{−1} Σ …` | — | printed `3^k`, the word has `k+1` ones: `3^{k+1}` (`eq1_3` has the right exponent) |
| p. 39: "T does not change the denominator of any `x ∈ Q_(2)`" | `den_printed_false` | FALSE: `T(1/3) = 1` |
| what is true: `den(T x) ∣ den x`, `=` unless `3 ∣ den x` | `den_step` | — |
| p. 39: all rationals of a cycle have the same denominator `δ(v)` | `den_cycle` | none (the conclusion holds; the printed reason does not) |
| p. 39: `δ(v) = D(v)/(N(v), D(v))` | `delta_eq` | `|D(v)|` (D < 0 for negative cycles) |
| p. 37: any trajectory is eventually periodic or divergent | `dichotomy` | none |
| p. 38: the parity map `x ↦ b(x)` is one-to-one on `Q_(2)` (cited from [10]) | `bseq_inj` | proved here, not cited |
| Cor. 2.1b (p. 38): a divergent trajectory has an aperiodic parity sequence | `cor2_1b` | none |
| Table 2.2 (p. 39), the 23 rows `n ≤ 6` | `table2_2`, `table2_2_values`, `table2_2_complete` | none |
| p. 39: `v = 110000`: `D = 55`, `δ = 11`, the only row with `D ≠ δ` | `table2_2_gcd` | none |
| (3.1): `T_k(n) = (3n+k)/2` (n odd), `n/2` (n even), `k` odd | `Tk` | none |
| p. 40: clearing the denominator `k` | `clear_den` | none |
| p. 40: "`(D(v), 6) = 1`" | `D6_printed_false`, `D6` | false for `v = 0ⁿ`, `n` even (`3 ∣ 2ⁿ − 1`); true when `v` has a 1 |
| p. 40: "`T_k(n) = T_{−k}(−n)`" | `tk_sign_printed_false`, `tk_sign` | sign missing: `T_k(n) = −T_{−k}(−n)` |
| p. 40: `T_k` maps `Z(d,k) = {n : (n,k) = d}` into itself | `tk_Z_printed_false`, `tk_Z` | needs `3 ∤ k` (`T_9(1) = 6`) |
| p. 40: `T_k` on `Z(d,k)` = `T_{k/d}` on `Z(1,k/d)` up to scale | `tk_scale` | none |
| p. 40: primitive cycle of `T_k`: `T_k`-cycle of integers prime to `k` | `InPrimCycle` | `k` odd made explicit |
| p. 40: bijection `𝒞` (rational cycles) ↔ members of primitive cycles of the `T_k`, `k > 0`, `k ≡ ±1 (6)` | `bij3` | none |
| p. 44: the smallest member of a primitive cycle is `≡ ±1 (6)` (used, not proved) | `no3`, `min_pm1` | the cycle `{0}` excluded |
| Thm 3.4 (p. 44) | `thm3_4` | the first claim also covers EVEN `n0`; the printed proof uses `ord_{N(v)}(2)`, undefined for `N(v)` even (repaired with the odd part of `N(v)`) |
| p. 44: `v = 10^m`, `x(v) = 1/(2^m − 3)` | `ex_10m` | `v` of total length `m` (`10^{m−1}`) |
| p. 45: `v = 1²0^m`, `x(v) = 5/(2^m − 9)`, primitive iff `m ≢ 2 (4)` | `ex_5` | `v` of total length `m` (`1²0^{m−2}`) |
| (3.8)–(3.9) (p. 45): `x(v) < 0 ⇒ x(v) ≤ −1`, equality iff `v = 1ⁿ` | `eq3_8` | none |
| Thm 3.5 (p. 45) | `thm3_5` | none |
| (4.4) (p. 47): `Σ_{j<n} 2^j 3^{n−j} = 3ⁿ − 2ⁿ` | `eq4_4_printed_false`, `eq4_4` | exponent `n−1−j` |
| (4.5), (4.8) (p. 48) | `eq4_5`, `eq4_8` | none |
| `F(n,M)` (p. 47): max number of `v ∈ {0,1}ⁿ` with `N(v)` in one class mod `M` | `words`, `cntRes` | stated for every class `r` |
| Thm 4.1 (p. 47): `(M,3) = 1`, `M = 2^{αn}`: `F ≤ n+1` (`α > log₂3`), `F ≤ 2n·2^{(1−φα)n}` (`0 < α ≤ log₂3`) | `thm4_1` | `n ≥ 1`; `2^{(1−φα)n} = 2ⁿ/M^φ`, `φ = log₃2`; `M = 1` allowed |
| proof of Thm 4.1: "at most `m` choices of `w`", `F ≤ m·2^{n−m}` | `thm4_1_core`, `thm4_1_printed_step_false` | `m + 1` choices (weights `0…m`) |
-/

namespace Lagarias

open LaboBP LaboHH

/-! ## Section 2 -/

/-- Parity of a rational, as `collatzQ` reads it: parity of the reduced numerator. -/
def par (x : ℚ) : Bool := decide (x.num % 2 = 1)

/-- The first `n` bits `b_0(x), …, b_{n−1}(x)` of the parity sequence, `b_j(x) ≡ T^{(j)}(x) (mod 2)`. -/
def parWord (x : ℚ) : ℕ → List Bool
  | 0 => []
  | n + 1 => par x :: parWord (collatzQ x) n

/-- The parity sequence `b(x)` (p. 36). -/
def bseq (x : ℚ) (j : ℕ) : Bool := par (collatzQ^[j] x)

/-- `x(v) = N(v)/D(v)`, (2.1)/(1.2), with `N = LaboBP.C`, `D = LaboBP.d`. -/
def xv (v : List Bool) : ℚ := (C v : ℚ) / (d v : ℚ)

/-- (2.1) as printed. -/
def eq2_1 : Prop :=
  ∀ v : List Bool, xv v = ((2 : ℚ) ^ v.length - 3 ^ v.count true)⁻¹ *
    ∑ j ∈ Finset.range v.length,
      (if v.getD j false then (3 : ℚ) ^ ((v.drop (j + 1)).count true) * 2 ^ j else 0)

/-- Theorem 2.1. -/
def thm2_1 : Prop :=
  ∀ v : List Bool, v ≠ [] →
    Odd (xv v).den ∧ collatzQ^[v.length] (xv v) = xv v ∧ parWord (xv v) v.length = v ∧
    ∀ y : ℚ, Odd y.den → collatzQ^[v.length] y = y → parWord y v.length = v → y = xv v

/-- `Σ_j 3^j 2^{a(j)}` for the exponent list `[a(0), a(1), …]` ((1.3), (2.3)). -/
def S3 : List ℕ → ℕ
  | [] => 0
  | a :: L => 2 ^ a + 3 * S3 L

/-- (1.3), both directions, with `x = 0` excluded. -/
def eq1_3 : Prop :=
  (∀ v : List Bool, true ∈ v → ∃ L : List ℕ, L.Pairwise (· > ·) ∧ L.length = v.count true ∧
      (∀ a ∈ L, a < v.length) ∧ xv v = (S3 L : ℚ) / ((2 : ℚ) ^ v.length - 3 ^ L.length)) ∧
  (∀ (n : ℕ) (L : List ℕ), L ≠ [] → L.Pairwise (· > ·) → (∀ a ∈ L, a < n) →
      ∃ v : List Bool, v.length = n ∧ xv v = (S3 L : ℚ) / ((2 : ℚ) ^ n - 3 ^ L.length))

/-- Corollary 2.1a. -/
def cor2_1a : Prop :=
  ∀ L L' : List ℕ, L.length = L'.length → L.Pairwise (· > ·) → L'.Pairwise (· > ·) →
    S3 L = S3 L' → L = L'

/-- Corollary 2.1a, word form (as used in the proof of Theorem 4.1). -/
def cor2_1a_words : Prop :=
  ∀ v w : List Bool, v.length = w.length → v.count true = w.count true → C v = C w → v = w

/-- p. 37: Corollary 2.1a fails across different `k`. -/
def ex_p37 : Prop := S3 [4, 0] = 19 ∧ S3 [2, 1, 0] = 19

/-- p. 39, printed reason: "`T` does not change the denominator" — false. -/
def den_printed_false : Prop := ∃ x : ℚ, Odd x.den ∧ (collatzQ x).den ≠ x.den

/-- What is true: the denominator divides, and is unchanged unless `3 ∣ den`. -/
def den_step : Prop :=
  ∀ x : ℚ, Odd x.den → Odd (collatzQ x).den ∧ (collatzQ x).den ∣ x.den ∧
    (¬ 3 ∣ x.den → (collatzQ x).den = x.den)

/-- p. 39: all rationals of a cycle have the same denominator. -/
def den_cycle : Prop :=
  ∀ x : ℚ, Odd x.den → ∀ p, 0 < p → collatzQ^[p] x = x → ∀ j, (collatzQ^[j] x).den = x.den

/-- p. 39: `δ(v) = |D(v)| / (N(v), D(v))`. -/
def delta_eq : Prop :=
  ∀ v : List Bool, v ≠ [] → ((xv v).den : ℤ) = |d v| / (Int.gcd (C v) (d v) : ℤ)

/-- Divergent trajectory (p. 37): `|T^{(k)}(x)| → ∞`. -/
def Divergent (x : ℚ) : Prop :=
  Filter.Tendsto (fun k : ℕ => |collatzQ^[k] x|) Filter.atTop Filter.atTop

/-- Eventually periodic sequence. -/
def EvPeriodic {α : Type*} (f : ℕ → α) : Prop := ∃ N p, 0 < p ∧ ∀ j, N ≤ j → f (j + p) = f j

/-- p. 37: every trajectory on `Q_(2)` is eventually periodic or divergent. -/
def dichotomy : Prop :=
  ∀ x : ℚ, Odd x.den → EvPeriodic (fun j => collatzQ^[j] x) ∨ Divergent x

/-- p. 38 (cited from [10]): the parity map is one-to-one on `Q_(2)`. -/
def bseq_inj : Prop :=
  ∀ x y : ℚ, Odd x.den → Odd y.den → bseq x = bseq y → x = y

/-- Corollary 2.1b. -/
def cor2_1b : Prop := ∀ x : ℚ, Odd x.den → Divergent x → ¬ EvPeriodic (bseq x)

/-- 0-1 words written with digits. -/
def bw (l : List ℕ) : List Bool := l.map (· == 1)

/-- Table 2.2 (p. 39): `(v, numerator, denominator)` of `x(v)` as printed. -/
def table2_2 : List (List ℕ × ℤ × ℤ) :=
  [([1], -1, 1), ([0], 0, 1), ([1,0], 1, 1), ([1,1,0], -5, 1), ([1,0,0], 1, 5),
   ([1,1,1,0], -19, 11), ([1,1,0,0], 5, 7), ([1,0,0,0], 1, 13),
   ([1,1,1,1,0], -65, 49), ([1,1,1,0,0], 19, 5), ([1,1,0,1,0], 23, 5), ([1,1,0,0,0], 5, 23),
   ([1,0,1,0,0], 7, 23), ([1,0,0,0,0], 1, 29),
   ([1,1,1,1,1,0], -211, 179), ([1,1,1,1,0,0], -65, 17), ([1,1,1,0,1,0], -73, 17),
   ([1,1,1,0,0,0], 19, 37), ([1,1,0,1,0,0], 23, 37), ([1,1,0,0,1,0], 31, 37),
   ([1,1,0,0,0,0], 1, 11), ([1,0,1,0,0,0], 7, 55), ([1,0,0,0,0,0], 1, 61)]

/-- Table 2.2: the printed values are the reduced `x(v)`. -/
def table2_2_values : Prop :=
  ∀ r ∈ table2_2, xv (bw r.1) = (r.2.1 : ℚ) / (r.2.2 : ℚ) ∧ (xv (bw r.1)).den = r.2.2.toNat

/-- All 0-1 words of length `n`. -/
def allWords : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allWords n).map (List.cons true) ++ (allWords n).map (List.cons false)

/-- Lexicographic `≤` on words (`false < true`). -/
def lexLe : List Bool → List Bool → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: v, b :: w => (!a && b) || (a == b && lexLe v w)

/-- `v` is irreducible (its rotations are distinct) and the lexicographically largest of its rotations. -/
def isRep (v : List Bool) : Bool :=
  (List.range v.length).all (fun i => i == 0 || v.rotate i != v) &&
  (List.range v.length).all (fun i => lexLe (v.rotate i) v)

/-- Table 2.2 lists, for each `n ≤ 6`, exactly the representatives of the irreducible cycles. -/
def table2_2_complete : Prop :=
  ∀ n ∈ [1, 2, 3, 4, 5, 6],
    ((allWords n).filter isRep).toFinset = ((table2_2.map (fun r => bw r.1)).filter (·.length == n)).toFinset

/-- p. 39: `v = 110000` has `D(v) = 55`, `δ(v) = 11`; it is the only row of Table 2.2 with `(N(v), D(v)) > 1`. -/
def table2_2_gcd : Prop :=
  d (bw [1,1,0,0,0,0]) = 55 ∧ (xv (bw [1,1,0,0,0,0])).den = 11 ∧
  ∀ r ∈ table2_2, Int.gcd (C (bw r.1)) (d (bw r.1)) = 1 ∨ r.1 = [1,1,0,0,0,0]

/-! ## Section 3 -/

/-- (3.1): the `3x+k` function. -/
def Tk (k n : ℤ) : ℤ := if n % 2 = 0 then n / 2 else (3 * n + k) / 2

/-- `n` lies in a primitive cycle of `T_k` (p. 40). -/
def InPrimCycle (k n : ℤ) : Prop := Odd k ∧ Int.gcd n k = 1 ∧ ∃ p, 0 < p ∧ (Tk k)^[p] n = n

/-- p. 40: clearing the denominator `k`. -/
def clear_den : Prop :=
  ∀ k m : ℤ, 0 < k → Odd k → ∀ j : ℕ, (k : ℚ) * collatzQ^[j] ((m : ℚ) / k) = ((Tk k)^[j] m : ℤ)

/-- p. 40, printed: `(D(v), 6) = 1` — false. -/
def D6_printed_false : Prop := ∃ v : List Bool, v ≠ [] ∧ Int.gcd (d v) 6 ≠ 1

/-- p. 40, repaired. -/
def D6 : Prop := ∀ v : List Bool, true ∈ v → Int.gcd (d v) 6 = 1

/-- p. 40, printed: `T_k(n) = T_{−k}(−n)` — false. -/
def tk_sign_printed_false : Prop := ∃ k n : ℤ, Odd k ∧ Tk k n ≠ Tk (-k) (-n)

/-- p. 40, repaired. -/
def tk_sign : Prop := ∀ k n : ℤ, Odd k → Tk k n = -Tk (-k) (-n)

/-- p. 40, printed: `T_k(Z(d,k)) ⊆ Z(d,k)` for odd `k` — false. -/
def tk_Z_printed_false : Prop := ∃ k n : ℤ, Odd k ∧ Int.gcd (Tk k n) k ≠ Int.gcd n k

/-- p. 40, repaired: needs `3 ∤ k`. -/
def tk_Z : Prop := ∀ k n : ℤ, Odd k → ¬ (3 : ℤ) ∣ k → Int.gcd (Tk k n) k = Int.gcd n k

/-- p. 40: `T_{dk'}(dn') = d·T_{k'}(n')`. -/
def tk_scale : Prop := ∀ e k n : ℤ, Odd e → Odd k → Tk (e * k) (e * n) = e * Tk k n

/-- p. 40: the bijection `x = m/k ↦ (k, m)`. -/
def bij3 : Prop :=
  Set.BijOn (fun x : ℚ => ((x.den : ℤ), x.num))
    {x : ℚ | Odd x.den ∧ x ∈ Function.periodicPts collatzQ}
    {p : ℤ × ℤ | 0 < p.1 ∧ (p.1 % 6 = 1 ∨ p.1 % 6 = 5) ∧ InPrimCycle p.1 p.2}

/-- p. 44 (used): no nonzero member of a cycle of `T_k`, `3 ∤ k`, is divisible by 3. -/
def no3 : Prop :=
  ∀ k n : ℤ, Odd k → ¬ (3 : ℤ) ∣ k → n ≠ 0 → (∃ p, 0 < p ∧ (Tk k)^[p] n = n) → ¬ (3 : ℤ) ∣ n

/-- p. 44 (used): the smallest positive member of a cycle of `T_k`, `3 ∤ k`, is `≡ ±1 (mod 6)`. -/
def min_pm1 : Prop :=
  ∀ k n : ℤ, Odd k → ¬ (3 : ℤ) ∣ k → 0 < n → (∃ p, 0 < p ∧ (Tk k)^[p] n = n) →
    (∀ j, n ≤ (Tk k)^[j] n) → n % 6 = 1 ∨ n % 6 = 5

/-- Theorem 3.4. -/
def thm3_4 : Prop :=
  ∀ n0 : ℤ, 0 < n0 → (∃ k, 0 < k ∧ InPrimCycle k n0) →
    {k : ℤ | 0 < k ∧ InPrimCycle k n0}.Infinite ∧
    (n0 % 6 = 1 ∨ n0 % 6 = 5 → {k : ℤ | 0 < k ∧ InPrimCycle k n0 ∧ ∀ j, n0 ≤ (Tk k)^[j] n0}.Infinite)

/-- p. 44: `v = 10^{m−1}` (length `m`) has `x(v) = 1/(2^m − 3)`, and `1` is in a primitive cycle of `T_{2^m−3}`. -/
def ex_10m : Prop :=
  ∀ m : ℕ, 2 ≤ m → xv (true :: List.replicate (m - 1) false) = 1 / (2 ^ m - 3) ∧
    InPrimCycle (2 ^ m - 3) 1

/-- p. 45: `v = 1²0^{m−2}` (length `m`) has `x(v) = 5/(2^m − 9)`; `5` is in a primitive cycle of `T_{2^m−9}`
iff `m ≢ 2 (mod 4)`. -/
def ex_5 : Prop :=
  ∀ m : ℕ, 4 ≤ m → xv (true :: true :: List.replicate (m - 2) false) = 5 / (2 ^ m - 9) ∧
    (InPrimCycle (2 ^ m - 9) 5 ↔ m % 4 ≠ 2)

/-- (3.8)–(3.9). -/
def eq3_8 : Prop := ∀ v : List Bool, xv v < 0 → xv v ≤ -1 ∧ (xv v = -1 ↔ ∀ b ∈ v, b = true)

/-- Theorem 3.5. -/
def thm3_5 : Prop :=
  (∀ n0 k : ℤ, n0 < 0 → |n0| < k → ¬ InPrimCycle k n0) ∧
  InPrimCycle 1 (-1) ∧ ∀ k : ℤ, 1 < k → ¬ InPrimCycle k (-1)

/-! ## Section 4 -/

/-- (4.4) as printed — false. -/
def eq4_4_printed_false : Prop :=
  ∃ n : ℕ, ∑ j ∈ Finset.range n, (2 : ℤ) ^ j * 3 ^ (n - j) ≠ 3 ^ n - 2 ^ n

/-- (4.4) repaired: the maximum element of `Σ_n`. -/
def eq4_4 : Prop :=
  ∀ n : ℕ, ∑ j ∈ Finset.range n, (2 : ℤ) ^ j * 3 ^ (n - 1 - j) = 3 ^ n - 2 ^ n ∧
    ∀ v : List Bool, v.length = n → (C v : ℤ) ≤ 3 ^ n - 2 ^ n

/-- (4.5). -/
def eq4_5 : Prop :=
  ∀ w w' : List Bool, C (w ++ w') = C w * 3 ^ w'.count true + 2 ^ w.length * C w'

/-- (4.8). -/
def eq4_8 : Prop :=
  ∀ w u w' : List Bool, C (w ++ u ++ w') =
    3 ^ (u.count true + w'.count true) * C w + 2 ^ w.length * 3 ^ w'.count true * C u +
      2 ^ (w.length + u.length) * C w'

/-- `{0,1}ⁿ`. -/
def words : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => (words n).image (List.cons true) ∪ (words n).image (List.cons false)

/-- Number of `v ∈ {0,1}ⁿ` with `N(v) ≡ r (mod M)` (elements of `Σ_n` counted with multiplicity). -/
def cntRes (n M r : ℕ) : ℕ := ((words n).filter (fun v => C v % M = r % M)).card

/-- Theorem 4.1, with `φ = (log₂ 3)^{−1} = log₃ 2` and `2^{(1−φα)n} = 2ⁿ / M^φ` for `M = 2^{αn}`. -/
def thm4_1 : Prop :=
  ∀ n M : ℕ, 0 < n → 0 < M → Nat.Coprime M 3 →
    (3 ^ n < M → ∀ r, cntRes n M r ≤ n + 1) ∧
    (M ≤ 3 ^ n → ∀ r, (cntRes n M r : ℝ) ≤ 2 * n * 2 ^ n / (M : ℝ) ^ Real.logb 3 2)

/-- The integer core of the proof of Theorem 4.1 (repaired count `m + 1`). -/
def thm4_1_core : Prop :=
  ∀ n M m : ℕ, 0 < M → Nat.Coprime M 3 → m ≤ n → 3 ^ m ≤ M → ∀ r, cntRes n M r ≤ (m + 1) * 2 ^ (n - m)

/-- The printed intermediate bound `F(n,M) ≤ m·2^{n−m}`, `m = ⌊log₃ M⌋`, is false. -/
def thm4_1_printed_step_false : Prop :=
  ∃ n M m r : ℕ, Nat.Coprime M 3 ∧ 3 ^ m ≤ M ∧ M < 3 ^ (m + 1) ∧ m ≤ n ∧ m * 2 ^ (n - m) < cntRes n M r

end Lagarias
