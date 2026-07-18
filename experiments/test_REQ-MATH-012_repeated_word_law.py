#!/usr/bin/env python3
# test_REQ-MATH-012_repeated_word_law.py — ARES (clé Merle sur L-A2)
# LA LOI DES MOTS RÉPÉTÉS (Macindoe, briefs/prime-local-probe-findings.md, seedée L-A2) :
#   pour P = B^j (j >= 2) :  gcd(q_P, R_0(P)) = |q_P| / q_red(B),
#   avec q_red(B) = |q_B| / gcd(q_B, R_0(B)) — force > 1, aveugle au signe ;
#   et P est divisible ssi B l'est (le cycle realise = celui de la base, traverse j fois).
# CLE INDEPENDANTE : conventions re-derivees de MON stack (rotations_R des REQ-MATH-006/010),
# sans lire son experiments/prime_local_probe.py.
# CANARIS (calcules a la main avant d'ecrire ce script) :
#   B=(m=1,s=1) trivial-bloc, j=2 : q_P=7,  R_0=7,   gcd=7  = 7/1   (base q_red=1)
#   B=(m=1,s=3),            j=2 : q_P=247, R_0=133, gcd=19 = 247/13 (base q_red=13)
import math, random

def rotations_R0(m, s):
    p = len(m)
    sig = [s[t] + m[(t+1) % p] for t in range(p)]
    Mafter = [0]*p; acc = 0
    for t in range(p-1, -1, -1):
        Mafter[t] = acc; acc += m[t]
    tot, Spre = 0, 0
    for t in range(p):
        tot += 3**Mafter[t] * 2**Spre * (2**s[t] - 1)
        Spre += sig[t]
    return tot

def qKn(m, s):
    n = sum(m); K = sum(s) + n
    return 2**K - 3**n

def check_law(mB, sB, j):
    qB = qKn(mB, sB); RB = rotations_R0(mB, sB)
    qred = abs(qB) // math.gcd(abs(qB), RB)
    mP, sP = mB*j, sB*j
    qP = qKn(mP, sP); RP = rotations_R0(mP, sP)
    g = math.gcd(abs(qP), RP)
    law = (g == abs(qP) // qred)
    forced = (g > 1)
    div_iff = ((RP % qP == 0) == (RB % qB == 0))
    return law, forced, div_iff, g, qP, qred

print("=== CANARIS (valeurs main) ===")
l1 = check_law([1], [1], 2)
print(f"trivial-bloc j=2 : gcd={l1[3]} (attendu 7),  loi={l1[0]}")
l2 = check_law([1], [3], 2)
print(f"(m=1,s=3)   j=2 : gcd={l2[3]} (attendu 19), q_P={l2[4]} (attendu 247), loi={l2[0]}")
if not (l1[0] and l1[3] == 7 and l2[0] and l2[3] == 19 and l2[4] == 247):
    print("CANARI FAIL"); raise SystemExit(1)
print("CANARIS: PASS")

print("\n=== CAMPAGNE : bases aleatoires x repetitions j=2..5 ===")
random.seed(20260719)
N = 0; fails_law = 0; fails_forced = 0; fails_iff = 0
for _ in range(600):
    p = random.randint(1, 5)
    mB = [random.randint(1, 12) for _ in range(p)]
    sB = [random.randint(1, 9) for _ in range(p)]
    for j in (2, 3, 4, 5):
        if (sum(mB) + sum(sB)) * j > 400: continue   # garde les entiers raisonnables
        law, forced, div_iff, g, qP, qred = check_law(mB, sB, j)
        N += 1
        fails_law += (not law); fails_forced += (not forced); fails_iff += (not div_iff)
print(f"tests : {N} | loi gcd exacte : {N - fails_law}/{N} | force >1 : {N - fails_forced}/{N} | divisible ssi base : {N - fails_iff}/{N}")

ok = (fails_law == 0 and fails_forced == 0 and fails_iff == 0)
print(f"\nEXIT-CRITERION: {'PASS — cle Merle tournee sur L-A2' if ok else 'FAIL'}")
raise SystemExit(0 if ok else 1)
