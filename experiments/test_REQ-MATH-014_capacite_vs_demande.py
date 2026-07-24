#!/usr/bin/env python3
# test_REQ-MATH-014_capacite_vs_demande.py — ARES (creuser la fissure, suite, 2026-07-24)
#
# REDIRECTION du negatif de REQ-MATH-013 : la rigidite n'est pas dans les CHIFFRES
# (aucune obstruction de congruence propre a la strate). Est-elle dans le NOMBRE ?
# = cadeau B de Ben : "capacite logarithmique contre demande lineaire".
#
# CAPACITE  = q = 2^K - 3^n  (nb de residus mod q ; log2 ≈ K ≈ 1.585 n).
# DEMANDE   = nb de gammes candidates a n threes = nb de profils (m,s), sum(m)=n,
#             sum(s)=S=bit_length(3^n)-n.  Chaque profil "tente" R_0 ≡ 0 (mod q), 1 case sur q.
#   - general : G(n) = Σ_p C(n-1,p-1) C(S-1,p-1) = C(K-2, n-1)  [Vandermonde].
#   - strate  : St(n) = Σ_p C(n-1,p-1) * oddcomp(S,p),  oddcomp(S,p)=C((S-p)/2+p-1,p-1).
# Heuristique (SANS conspiration) : nb attendu de cycles ≈ demande / capacite = 2^(log2 D - K).
# Si (K - log2 D) > 0 ET CROIT avec n  =>  la famille est "trop rare pour conspirer",
# marge croissante : c'est la forme quantitative du cadeau B. On MESURE la marge.
import math
from mpmath import mp, mpf, log
mp.dps = 60
def log2c(a, b):
    if b < 0 or b > a: return float('-inf')
    return sum(math.log2(a-i) - math.log2(i+1) for i in range(b))  # log2 C(a,b), stable

def oddcomp(S, p):
    if (S - p) % 2 or S < p: return 0
    return math.comb((S-p)//2 + p-1, p-1)

def demand_general(n, S):
    return math.comb(n + S - 2, n - 1)          # Vandermonde = Σ_p C(n-1,p-1)C(S-1,p-1)
def demand_stratum(n, S):
    return sum(math.comb(n-1, p-1) * oddcomp(S, p) for p in range(1, S+1))

# ===================== CANARIS =====================
print("=== CANARIS ===")
# C1 : Vandermonde  Σ_p C(n-1,p-1)C(S-1,p-1) == C(n+S-2,n-1)
ok1 = True
for n, S in [(5,3),(8,5),(12,8),(10,6)]:
    lhs = sum(math.comb(n-1,p-1)*math.comb(S-1,p-1) for p in range(1, min(n,S)+1))
    if lhs != math.comb(n+S-2, n-1): ok1 = False
print(f"C1  Vandermonde (demande generale) : {ok1}")
# C2 : compositions de S en parts IMPAIRES (tous p) = Fibonacci F(S)  [F(1)=1,F(2)=1,...]
def fib(k):
    a,b=1,1
    for _ in range(k-1): a,b=b,a+b
    return a
ok2 = all(sum(oddcomp(S,p) for p in range(1,S+1)) == fib(S) for S in range(1,16))
print(f"C2  Σ_p oddcomp(S,p) = Fibonacci(S) : {ok2}")
# C3 : coherence log2c vs comb sur petit cas
ok3 = abs(log2c(20,7) - math.log2(math.comb(20,7))) < 1e-9
print(f"C3  log2c stable : {ok3}")
if not (ok1 and ok2 and ok3):
    print("CANARI FAIL"); raise SystemExit(1)
print("CANARIS: PASS\n")

# ===================== MESURE : marge capacite - demande, strate & general =====================
print("=== CAPACITE (K=log2 q) vs DEMANDE (log2 nb de profils) — la marge croit-elle ? ===")
print(f"{'n':>5} {'K=log2 q':>10} {'log2 St':>10} {'marge St':>9} {'log2 Gen':>10} {'marge Gen':>10} {'K/n':>6} {'margeSt/n':>10}")
rows = []
for n in [10, 20, 40, 80, 160, 320, 640, 1280]:
    K = (3**n).bit_length(); S = K - n
    St = demand_stratum(n, S); G = demand_general(n, S)
    lSt = math.log2(St) if St > 0 else float('-inf')
    lG  = math.log2(G)  if G  > 0 else float('-inf')
    mSt, mG = K - lSt, K - lG
    rows.append((n, K, lSt, mSt))
    print(f"{n:>5} {K:>10} {lSt:>10.1f} {mSt:>9.1f} {lG:>10.1f} {mG:>10.1f} {K/n:>6.3f} {mSt/n:>10.4f}")

# la marge par n tend-elle vers une constante > 0 (croissance lineaire de la marge) ?
slopes = [rows[i][3]/rows[i][0] for i in range(len(rows))]
print(f"\n  marge_strate / n  aux grands n : {slopes[-3]:.4f}, {slopes[-2]:.4f}, {slopes[-1]:.4f}")
print("  => si cette valeur se stabilise > 0, la marge CROIT lineairement : nb attendu de cycles")
print("     ~ 2^(-marge) -> 0 exponentiellement. Forme quantifiee du cadeau B de Ben (capacite > demande).")
print("\n  LIMITE HONNETE : c'est l'heuristique 'sans conspiration'. La rendre RIGOUREUSE (interdire")
print("  la conspiration individuelle) reste le fosse x2x3 — mais la cible est nette : une independance/")
print("  equidistribution des residus R_0 mod q le long de la famille, PAS une obstruction de congruence.")
raise SystemExit(0)
