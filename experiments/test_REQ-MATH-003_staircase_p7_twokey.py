#!/usr/bin/env python3
# test_REQ-MATH-003_staircase_p7_twokey.py — ARES Regle 6 (Two-Key)
#
# RE-VERIFICATION INDEPENDANTE (code frais, conventions re-derivees du paper v1 de
# Macindoe, SANS lire ses scripts) de l'instance staircase p=7 (cycles.md 12.8.3) :
#   m = (4,7,9,15,23,35,1), s = (1,1,1,1,1,1,S-6), n = 94, K = ceil(nL), S = K-n
#   ATTENDUS : K=149, s7=49, gamma = 6.744, q <= R_r pour les 7 rotations,
#              q | R_r ECHOUE partout (donc pas un cycle).
#
# Conventions re-derivees (elimination identity, paper v1 Prop. 4.x) :
#   sigma_t = s_t + m_{t+1 mod p} ;  R_r = sum_t 3^{M_t} 2^{S_t} (2^{s_t}-1)
#   ordre de rotation (r, r+1, ...) : M_t = somme des m APRES t ; S_t = somme des sigma AVANT t.
# CANARI : cycle trivial p blocs (m_t=1, s_t=1) doit donner R_r = q = 4^p - 3^p.
import math
from mpmath import mp, mpf, log
mp.dps = 60

def rotations_R(m, s):
    p = len(m)
    out = []
    for r in range(p):
        ms = m[r:] + m[:r]
        ss = s[r:] + s[:r]
        sig = [ss[t] + ms[(t+1) % p] for t in range(p)]
        Mafter = [0]*p
        acc = 0
        for t in range(p-1, -1, -1):
            Mafter[t] = acc
            acc += ms[t]
        total, Spre = 0, 0
        for t in range(p):
            total += 3**Mafter[t] * 2**Spre * (2**ss[t] - 1)
            Spre += sig[t]
        out.append(total)
    return out

print("=== CANARI : cycle trivial, p = 1..4 ===")
ok = True
for p in range(1, 5):
    m = [1]*p; s = [1]*p
    n = sum(m); K = sum(s) + n
    q = 2**K - 3**n
    Rs = rotations_R(m, s)
    good = all(R == q for R in Rs)
    ok = ok and good
    print(f"p={p}: q=4^p-3^p={q}, R_r tous egaux a q ? {good}")
print(f"CANARI: {'PASS' if ok else 'FAIL'}")
if not ok:
    raise SystemExit(1)

print("\n=== INSTANCE p=7 de Macindoe (re-verification Two-Key) ===")
m = [4, 7, 9, 15, 23, 35, 1]
n = sum(m)
K = (3**n).bit_length()      # ceil(n*log2(3)) EXACT
S = K - n
s = [1, 1, 1, 1, 1, 1, S - 6]
q = 2**K - 3**n
ratio = mpf(3**n) / mpf(2**K)
gamma = -log(1 - ratio)/log(2)
print(f"n={n} (attendu 94) | K={K} (attendu 149) | S={S} (attendu 55) | s7={s[-1]} (attendu 49)")
print(f"gamma = {float(gamma):.4f} (attendu 6.744)")
meta_ok = (n == 94 and K == 149 and S == 55 and s[-1] == 49 and abs(float(gamma) - 6.744) < 0.001)

Rs = rotations_R(m, s)
size_pass = [q <= R for R in Rs]
div_pass = [R % q == 0 for R in Rs]
print(f"tests de TAILLE  q <= R_r : {size_pass}  -> {'TOUS PASSENT' if all(size_pass) else 'ECHEC'}")
print(f"tests de DIVISIBILITE q | R_r : {div_pass}  -> {'AUCUNE NE PASSE (attendu)' if not any(div_pass) else 'INATTENDU'}")

print("\n=== FORENSIC : pourquoi la divisibilite echoue (piste T2) ===")
for r, R in enumerate(Rs):
    g = math.gcd(q, R)
    v2q, v3q = 0, 0
    print(f" rot {r}: R/q ~ {float(mpf(R)/mpf(q)):9.3f} | gcd(q,R) a {g.bit_length():3d} bits "
          f"(q en a {q.bit_length()}) | R mod 8={R % 8}, q mod 8={q % 8} | R mod 3={R % 3}, q mod 3={q % 3}")

print("\n=== STRUCTURE 3-ADIQUE (idee fraiche, piste F) ===")
par = ['impair' if x % 2 else 'PAIR' for x in s]
print(f"parites des s_t : {par}")
print(f"tous impairs ? {all(x % 2 == 1 for x in s)}")
print("Rappel (loi d'absorption, paper Macindoe Lemma 3.x): a_+ = 0 ssi s impair.")
print("=> si tous les s_t sont impairs, le cycle hypothetique ne gagne JAMAIS de facteur 3 :")
print("   il vit dans le sous-systeme 'sans absorption 3-adique' (d_t = m_t partout).")

allok = meta_ok and all(size_pass) and not any(div_pass)
print(f"\nEXIT-CRITERION: {'PASS' if allok else 'FAIL'}")
raise SystemExit(0 if allok else 1)
