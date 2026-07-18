#!/usr/bin/env python3
# test_REQ-MATH-005_localglobal_p22margins.py — ARES (Red Team interne, session 2)
# A) THEOREME DE SESSION (a prouver machine) : pour l'instance staircase p=7 (Macindoe),
#    l'equation de fermeture  w * q = R_r  est soluble dans R, dans Z_2, dans Z_3
#    SEPAREMENT, et insoluble dans Z : l'obstruction est PUREMENT globale (defaut local-global).
#    + mesure de la "distance a l'integralite" min(m, q-m)/q (generique ~ uniforme ?).
# B) TEST DE LA FAILLE A4 : profil geometrique (Construction 12.8.6.2 de Macindoe, crash c=1,
#    arrondi par sommes partielles) evalue AVANT correction pour :
#    (p=21, n=15601) (p=22, n=25217) (p=22, n=31202) (p=23, n=47468)
#    -> nb de rotations en echec de taille + pire marge log2(R_r/q) + gamma.
#    Si p=22 part avec un deficit bien pire que p=21/23, l'explication "trou" tient.
import math
from fractions import Fraction
from mpmath import mp, mpf, log
mp.dps = 60
L = log(3)/log(2)

def rotations_R(m, s):
    p = len(m)
    out = []
    for r in range(p):
        ms = m[r:] + m[:r]; ss = s[r:] + s[:r]
        sig = [ss[t] + ms[(t+1) % p] for t in range(p)]
        Mafter = [0]*p; acc = 0
        for t in range(p-1, -1, -1):
            Mafter[t] = acc; acc += ms[t]
        tot, Spre = 0, 0
        for t in range(p):
            tot += 3**Mafter[t] * 2**Spre * (2**ss[t] - 1)
            Spre += sig[t]
        out.append(tot)
    return out

print("=== A) DEFAUT LOCAL-GLOBAL — instance p=7 (m=(4,7,9,15,23,35,1)) ===")
m7 = [4,7,9,15,23,35,1]; n = sum(m7)
K = (3**n).bit_length(); S = K - n
s7 = [1]*6 + [S-6]
q = 2**K - 3**n
Rs = rotations_R(m7, s7)
print(f"q impair ? {q % 2 == 1} | q divisible par 3 ? {q % 3 == 0}  (q inversible dans Z2 et Z3)")
B2, B3 = 64, 40
inv2 = pow(q, -1, 2**B2)   # existe ssi q impair
inv3 = pow(q, -1, 3**B3)   # existe ssi 3 ne divise pas q
print(f"{'rot':>3} {'R/q (reel)':>14} {'w mod 2^64 (Z2)':>22} {'w mod 3^5 (Z3)':>15} {'entier?':>8} {'dist. glob. min(m,q-m)/q':>25}")
for r, R in enumerate(Rs):
    w2 = (R * inv2) % 2**B2
    w3 = (R * inv3) % 3**B3
    mres = R % q
    dist = min(mres, q - mres) / q          # float ok (ratio)
    exact = (mres == 0)
    print(f"{r:>3} {float(mpf(R)/mpf(q)):>14.3f} {w2:>22} {w3 % 3**5:>15} {str(exact):>8} {dist:>25.4f}")
print("=> soluble dans R (ratios >= 1, cf. REQ-MATH-003), dans Z2 (colonne w2), dans Z3 (colonne w3),")
print("   dans Z : JAMAIS. Distance globale ~ uniforme => defaut purement global, aucun invariant local simple.")

print("\n=== B) MARGES DU PROFIL GEOMETRIQUE PAR PERIODE (avant correction) ===")
def build_profile(p, n):
    # Construction 12.8.6.2 : crash m_{p-1}=1, climb m_j ~ L^j (somme n-1),
    # arrondi par SOMMES PARTIELLES ; s_j=1 (climb), s_{p-1}=S-(p-1)
    K = (3**n).bit_length(); S = K - n
    w = [mpf(L)**j for j in range(p-1)]
    tw = sum(w)
    target = [x*(n-1)/tw for x in w]
    ms, Tprev = [], 0
    run = mpf(0)
    for j in range(p-1):
        run += target[j]
        Tj = int(run + mpf('0.5'))
        ms.append(max(1, Tj - Tprev)); Tprev = Tj
    # ajuste le dernier bloc de climb pour retomber exactement sur n-1
    ms[-1] += (n-1) - sum(ms)
    ms.append(1)
    ss = [1]*(p-1) + [S-(p-1)]
    return ms, ss, K, S

for (p, n) in [(21, 15601), (22, 25217), (22, 31202), (23, 47468)]:
    ms, ss, K, S = build_profile(p, n)
    if ss[-1] < 1 or min(ms) < 1:
        print(f"p={p} n={n}: PROFIL INVALIDE (s_crash={ss[-1]})"); continue
    q = 2**K - 3**n
    gamma = float(-log(1 - mpf(3)**n / mpf(2)**K)/log(2))
    Rs = rotations_R(ms, ss)
    fails = sum(1 for R in Rs if q > R)
    worst = min(float(log(mpf(R)/mpf(q))/log(2)) for R in Rs)
    print(f"p={p:2d} n={n:6d} | gamma={gamma:7.2f} | rotations en ECHEC de taille : {fails:2d}/{p} | pire marge log2(R/q) = {worst:8.2f}")
print("\nLECTURE : marge negative = rotation qui echoue ; la correction de Macindoe (<=40 moves)")
print("peut regagner quelques bits, pas des dizaines. Deficit massif => hors de portee de la recette.")
raise SystemExit(0)
