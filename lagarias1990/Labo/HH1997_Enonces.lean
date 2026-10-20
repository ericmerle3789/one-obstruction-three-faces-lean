import Mathlib
import Labo.S2_Pont
import OneObstruction.ContentDescent

/-!
# LABO-COLLATZ · HH1997 · formaliste (2026-10-19) — FROZEN STATEMENTS

L. Halbeisen, N. Hungerbühler, *Optimal bounds for the length of rational Collatz cycles*,
Acta Arith. 78 (1997) 227–239 (read at source: `LABO-COLLATZ/calculs/bibliothecaire/s6src/hh1997.txt`).
ccchallenge entry `HalbeisenHungerbuhler1997`: `not_started`, 0 formalisations (API read 2026-10-19).

This file contains ONLY definitions and `def <X> : Prop` statements.  Proofs: `Labo/HH1997_Preuves.lean`.
Reused, not redefined: `LaboBP.C`, `LaboBP.Csum`, `LaboBP.d` (`Labo/Blueprint.lean`; `C_eq_Csum` is proved in
`Labo/S2_Pont.lean`), `ContentDescent.W0`, `msum`, `mssum` (kernel, `OneObstruction/ContentDescent.lean`).

Conventions.  A 0-1 sequence `s = (s₁,…,s_l)` is a `List Bool` (`true` = 1); `l(s) = s.length`,
`n(s) = s.count true`.  Paper indices are 1-based, Lean indices 0-based: paper `s_{j+1}` = Lean `s.getD j false`.

## Line-by-line comparison with the paper (statements frozen BEFORE any proof)

| paper | Lean | deviation |
|---|---|---|
| §1 `g₀(x) = x/2`, `g₁(x) = (3x+1)/2` | `gStep` | over any field of characteristic 0 (paper: ℝ) |
| §2 `φ_s = g_{s_l} ∘ … ∘ g_{s_1}` | `phiMap s = foldl` (applies `g_{s₁}` first) | none |
| (1) Collatz map on ℚ_(2), parity = parity of the reduced numerator | `collatzQ` (`x.num % 2`) | defined on all of ℚ |
| (2) `ϕ({}) = 0, ϕ(s0) = ϕ(s), ϕ(s1) = 3ϕ(s) + 2^{l(s)}` | `phi` (recursion on the reversed word), `eq2` | none |
| (3) `ϕ(s) = Σ_{j=1}^{l} s_j 3^{s_{j+1}+…+s_l} 2^{j−1}` | `eq3` | 0-based `j` |
| (4) `ϕ(s s̄) = 3^{n(s̄)} ϕ(s) + 2^{l(s)} ϕ(s̄)` | `eq4` | none |
| Lemma 2, `φ_s(x) = (3^{n(s)} x + ϕ(s)) / 2^{l(s)}` | `lemma2_affine` | none |
| Lemma 2, unique `x₀ = ϕ(s)/(2^l − 3^n)` | `lemma2_fixed` (`s ≠ []`) | `l(s) ≥ 1` made explicit (for `l = 0`, `φ = id`) |
| Lemma 2, `x₀ ∈ ℚ_(2)` generates a Collatz cycle of length `l(s)` = the pseudo-cycle of `s` | `lemma2_cycle` | the iterates are stated as `collatzQ^[i] x₀ = φ_{s₁…s_i}(x₀)`, `i ≤ l`, with odd denominators |
| σ(s) = `{λ_l^k(s) : k = 1,…,l}`, λ = left shift | `sigma` (`List.rotate k`, `1 ≤ k ≤ l`) | none |
| `S_{l,n}` | `Sln` | none |
| `M_{l,n} = max_{s ∈ S_{l,n}} min_{t ∈ σ(s)} ϕ(t)` | `minRot` (`sInf`), `M` (`sSup`) | junk-free forms `IsLeast` / `IsGreatest` also stated |
| Lemma 4: `s ≠ t ∈ S_{l,n}`, `Σ_{i≤k} s_i ≤ Σ_{i≤k} t_i` (k = 1..l) ⇒ `ϕ(s) > ϕ(t)` | `lemma4` | none |
| Lemma 5: `s̃_i = ⌈in/l⌉ − ⌈(i−1)n/l⌉`, `ϕ(s̃) = min_{σ(s̃)} ϕ = M_{l,n}` | `stilde`, `cl`, `lemma5` | `0 < l` made explicit (σ of the empty word is empty) |
| Corollary 1: `M_{l,n} = Σ_{j=1}^{l} (⌈jn/l⌉ − ⌈(j−1)n/l⌉) 2^{j−1} 3^{n−⌈jn/l⌉}` | `cor1` | `0 < l` |
| ρ_l: `(s₁,…,s_l) ↦ (s_l, s₁, …, s₂)` (sic) | `rotR` = right shift `(s_l, s₁, …, s_{l−1})` | the printed `s₂` is a typo for `s_{l−1}` |
| (13) `ϕ(ρ(s0)) = ϕ(0s) = 2ϕ(s0)`, `ϕ(ρ(s1)) = ϕ(1s) = (2ϕ(s1) + 3^{n(s1)} − 2^{l(s1)})/3` | `eq13` | the second identity in ℚ |
| Lemma 9 (14) under `s ≠ 0…0`, `s̄1 ∈ σ(s)`, `2^l − 3^n > 0` | `lemma9_14` | none; `lemma9_14_gen` drops the hypotheses (stronger) |
| Lemma 9 (15) `gcd(ϕ(t) : t ∈ σ(s)) = gcd(ϕ(s), 2^l − 3^n)` | `lemma9_15` (`Finset.gcd` over `k = 1..l`) | none; `lemma9_15_gen` drops `2^l − 3^n > 0` |

Bridges (not in the paper; they say what the lab had already):
`phi_eq_C` (HH's ϕ = the lab's `LaboBP.C`), `W0_bridge` (the kernel's `W0` = `(2^K − 3^n) + ϕ` on the block word),
`eq4_kernel` ((4) on block words, to be derived from the kernel cocycle `ContentDescent.W0_append`),
`lemma9_core` (the per-rotation gcd invariance, to be derived from the kernel collapse
`CollatzTransport.collapse_of_recurrence`).
-/

namespace LaboHH

open LaboBP

/-! ## (2) The function ϕ, read from the right -/

/-- `phiRev` takes the word reversed (last letter first): it is (2) verbatim. -/
def phiRev : List Bool → ℕ
  | [] => 0
  | false :: r => phiRev r
  | true :: r => 3 * phiRev r + 2 ^ r.length

/-- HH (2): `ϕ({}) = 0`, `ϕ(s0) = ϕ(s)`, `ϕ(s1) = 3ϕ(s) + 2^{l(s)}`. -/
def phi (s : List Bool) : ℕ := phiRev s.reverse

/-- (2) as printed. -/
def eq2 : Prop :=
  phi [] = 0 ∧ ∀ s : List Bool, phi (s ++ [false]) = phi s ∧ phi (s ++ [true]) = 3 * phi s + 2 ^ s.length

/-- (3) closed form, 0-based: `ϕ(s) = Σ_{j<l} s_{j+1} · 3^{#1 in s_{j+2}…s_l} · 2^j`. -/
def eq3 : Prop :=
  ∀ s : List Bool, phi s =
    ∑ j ∈ Finset.range s.length, (s.getD j false).toNat * 3 ^ ((s.drop (j + 1)).count true) * 2 ^ j

/-- (4) decomposition formula. -/
def eq4 : Prop :=
  ∀ s t : List Bool, phi (s ++ t) = 3 ^ (t.count true) * phi s + 2 ^ s.length * phi t

/-- Bridge to the lab: HH's ϕ is the lab's numerator `C` (defined there by the left recursion). -/
def phi_eq_C : Prop := ∀ s : List Bool, phi s = C s

/-- A kernel word `[(m₁,s₁), …]` read as the 0-1 word `1^{m₁} 0^{s₁} 1^{m₂} 0^{s₂} …`. -/
def encode (l : List (ℕ × ℕ)) : List Bool :=
  l.flatMap fun p => List.replicate p.1 true ++ List.replicate p.2 false

/-- Bridge to the kernel: `W0 = (2^K − 3^n) + ϕ` on the block word. -/
def W0_bridge : Prop :=
  ∀ l : List (ℕ × ℕ),
    (encode l).length = ContentDescent.mssum l ∧ (encode l).count true = ContentDescent.msum l ∧
    ContentDescent.W0 l = d (encode l) + (phi (encode l) : ℤ)

/-- (4) on block words, to be obtained from the kernel cocycle `ContentDescent.W0_append`. -/
def eq4_kernel : Prop :=
  ∀ l₁ l₂ : List (ℕ × ℕ),
    phi (encode l₁ ++ encode l₂)
      = 3 ^ ((encode l₂).count true) * phi (encode l₁) + 2 ^ (encode l₁).length * phi (encode l₂)

/-! ## Lemma 2 (Lagarias) -/

/-- `g₀(x) = x/2`, `g₁(x) = (3x+1)/2`. -/
def gStep {K : Type*} [Field K] (b : Bool) (x : K) : K := if b then (3 * x + 1) / 2 else x / 2

/-- `φ_s = g_{s_l} ∘ … ∘ g_{s_1}` (the first letter acts first). -/
def phiMap {K : Type*} [Field K] (s : List Bool) (x : K) : K := s.foldl (fun y b => gStep b y) x

/-- (1) on ℚ: `x/2` if the reduced numerator is even, `(3x+1)/2` otherwise. -/
def collatzQ (x : ℚ) : ℚ := if x.num % 2 = 0 then x / 2 else (3 * x + 1) / 2

/-- Lemma 2, first formula. -/
def lemma2_affine : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (s : List Bool) (x : K),
    phiMap s x = (3 ^ s.count true * x + (phi s : K)) / 2 ^ s.length

/-- Lemma 2, the unique fixed point `x₀ = ϕ(s) / (2^{l(s)} − 3^{n(s)})` (for `l(s) ≥ 1`). -/
def lemma2_fixed : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (s : List Bool), s ≠ [] →
    ((2 : K) ^ s.length - 3 ^ s.count true ≠ 0) ∧
    ∀ x : K, phiMap s x = x ↔ x = (phi s : K) / (2 ^ s.length - 3 ^ s.count true)

/-- Lemma 2, the cycle: `x₀ ∈ ℚ_(2)` and its Collatz sequence (1) is the pseudo-cycle of `s`, of length `l(s)`. -/
def lemma2_cycle : Prop :=
  ∀ s : List Bool, s ≠ [] →
    Odd (d s) ∧ Odd ((phi s : ℚ) / (d s : ℚ)).den ∧
    (∀ i, i ≤ s.length →
      collatzQ^[i] ((phi s : ℚ) / (d s : ℚ)) = phiMap (s.take i) ((phi s : ℚ) / (d s : ℚ)) ∧
      Odd (collatzQ^[i] ((phi s : ℚ) / (d s : ℚ))).den) ∧
    collatzQ^[s.length] ((phi s : ℚ) / (d s : ℚ)) = (phi s : ℚ) / (d s : ℚ)

/-! ## Rotations, `S_{l,n}`, `M_{l,n}` -/

/-- σ(s) = `{λ_l^k(s) : k = 1,…,l}`, λ_l the left shift (`List.rotate 1`). -/
def sigma (s : List Bool) : Set (List Bool) := {t | ∃ k, 1 ≤ k ∧ k ≤ s.length ∧ t = s.rotate k}

/-- `S_{l,n}`. -/
def Sln (l n : ℕ) : Set (List Bool) := {s | s.length = l ∧ s.count true = n}

/-- `min_{t ∈ σ(s)} ϕ(t)`. -/
noncomputable def minRot (s : List Bool) : ℕ := sInf (phi '' sigma s)

/-- `M_{l,n} = max_{s ∈ S_{l,n}} min_{t ∈ σ(s)} ϕ(t)`. -/
noncomputable def M (l n : ℕ) : ℕ := sSup (minRot '' Sln l n)

/-! ## Lemma 4 -/

/-- Lemma 4 (monotonicity under prefix-sum domination). -/
def lemma4 : Prop :=
  ∀ s t : List Bool, s.length = t.length → s.count true = t.count true → s ≠ t →
    (∀ k, 1 ≤ k → k ≤ s.length → (s.take k).count true ≤ (t.take k).count true) →
    phi t < phi s

/-! ## Lemma 5 and Corollary 1 -/

/-- `⌈jn/l⌉`. -/
def cl (l n j : ℕ) : ℕ := ⌈((j * n : ℕ) : ℚ) / l⌉₊

/-- `s̃(l,n)`: position `i` (0-based) carries `⌈(i+1)n/l⌉ − ⌈in/l⌉ ∈ {0,1}`. -/
def stilde (l n : ℕ) : List Bool := (List.range l).map fun i => decide (cl l n i < cl l n (i + 1))

/-- Lemma 5. -/
def lemma5 : Prop :=
  ∀ l n : ℕ, 0 < l → n ≤ l →
    (stilde l n).length = l ∧
    (∀ i, i < l → ((stilde l n).getD i false).toNat = cl l n (i + 1) - cl l n i) ∧
    stilde l n ∈ Sln l n ∧
    IsLeast (phi '' sigma (stilde l n)) (phi (stilde l n)) ∧
    IsGreatest (minRot '' Sln l n) (phi (stilde l n)) ∧
    phi (stilde l n) = minRot (stilde l n) ∧ minRot (stilde l n) = M l n

/-- Corollary 1. -/
def cor1 : Prop :=
  ∀ l n : ℕ, 0 < l → n ≤ l →
    M l n = ∑ j ∈ Finset.Icc 1 l, (cl l n j - cl l n (j - 1)) * 2 ^ (j - 1) * 3 ^ (n - cl l n j)

/-! ## (13) and Lemma 9 -/

/-- ρ_l, the right shift `(s₁,…,s_l) ↦ (s_l, s₁, …, s_{l−1})`. -/
def rotR (s : List Bool) : List Bool := s.rotate (s.length - 1)

/-- (13). -/
def eq13 : Prop :=
  ∀ u : List Bool,
    rotR (u ++ [false]) = false :: u ∧ rotR (u ++ [true]) = true :: u ∧
    phi (false :: u) = 2 * phi (u ++ [false]) ∧
    (phi (true :: u) : ℚ)
      = (2 * phi (u ++ [true]) + 3 ^ (u ++ [true]).count true - 2 ^ (u ++ [true]).length) / 3

/-- Lemma 9 (14), with the paper's hypotheses. -/
def lemma9_14 : Prop :=
  ∀ s u : List Bool, true ∈ s → u ++ [true] ∈ sigma s → 0 < d s →
    Int.gcd (phi (u ++ [true])) (phi (rotR (u ++ [true]))) = Int.gcd (phi (u ++ [true])) (d s)

/-- (14) without the hypotheses (stronger than printed). -/
def lemma9_14_gen : Prop :=
  ∀ u : List Bool,
    Int.gcd (phi (u ++ [true])) (phi (rotR (u ++ [true]))) = Int.gcd (phi (u ++ [true])) (d (u ++ [true]))

/-- Lemma 9 (15), with the paper's hypotheses. -/
def lemma9_15 : Prop :=
  ∀ s : List Bool, true ∈ s → 0 < d s →
    (Finset.range s.length).gcd (fun k => (phi (s.rotate (k + 1)) : ℤ)) = GCDMonoid.gcd (phi s : ℤ) (d s)

/-- (15) without `2^l − 3^n > 0` (stronger than printed). -/
def lemma9_15_gen : Prop :=
  ∀ s : List Bool, true ∈ s →
    (Finset.range s.length).gcd (fun k => (phi (s.rotate (k + 1)) : ℤ)) = GCDMonoid.gcd (phi s : ℤ) (d s)

/-- The core of Lemma 9 (the kernel's L-A1 in HH's coordinates): `gcd(ϕ(λ^k s), 2^l − 3^n)` does not depend on `k`. -/
def lemma9_core : Prop :=
  ∀ s : List Bool, true ∈ s → ∀ k : ℕ, Int.gcd (phi (s.rotate k)) (d s) = Int.gcd (phi s) (d s)

end LaboHH
