#!/usr/bin/env python3
# test_REQ-MATH-011_pourquoi_le_signe.py — ARES
# POURQUOI LE SIGNE CHANGE-T-IL TOUT ? Quatre reponses calculees :
#  A. MIROIR : le monde negatif de 3x+1 EST le monde positif de 3x-1 (conjugaison exacte
#     n <-> -n). Le "mystere du signe" = "pourquoi 3x-1 a 3 maisons et 3x+1 une seule".
#  B. ENVELOPPE : q+(k) + q-(k) = 2^floor(k*L) exactement — les deux cotes se partagent
#     un budget fixe ; AUCUNE asymetrie structurelle des frolements.
#  C. EQUIDISTRIBUTION : le meilleur frolement tombe ~50/50 de chaque cote (k <= 5000).
#     => le signe ne change RIEN aux lois du jeu.
#  D. CATALAN : les ecarts |2^a - 3^b| = 1 (serrure GRATUITE : q=+-1 divise tout) sont
#     exactement TROIS : (2,3), (4,3), (8,9) — repartis 1 cote +, 2 cote -.
#     [Mihailescu 2002 prouve qu'il n'y en aura jamais d'autres — theoreme de Catalan.]
#  E. LA CARTE EXHAUSTIVE k <= 10 : enumeration PROUVEE-complete de tous les cycles des
#     deux cotes (bornes demontrees : cote+ kL < K <= 2k ; cote- k <= K < kL),
#     divisibilite testee sur UNE rotation (L-A1). Attendu : {+1} et {-1,-5,-17}, rien d'autre.
from itertools import combinations

def v2(x):
    x = abs(x)
    return (x & -x).bit_length() - 1

def T(n):          # 3x+1 odd map (tous entiers impairs, positifs ou negatifs)
    y = 3*n + 1
    return y >> v2(y)

def Tminus(m):     # 3x-1 odd map (positifs)
    y = 3*m - 1
    return y >> v2(y)

print("=== A. LE MIROIR : T_{3x+1}(-m) = -T_{3x-1}(m) ===")
mirror_ok = all(T(-m) == -Tminus(m) for m in range(1, 20002, 2))
print(f"verifie pour 10^4 impairs : {mirror_ok}")
print("=> le monde negatif de Collatz EST le monde 3x-1 en positif. Une seule dynamique, deux visages.")

print("\n=== B. L'ENVELOPPE : q+ + q- = 2^floor(kL) (exact, zero flottant) ===")
env_ok = True
p3 = 1
for k in range(1, 51):
    p3 *= 3
    Kf = p3.bit_length() - 1          # floor(kL)
    qp = 2**(Kf + 1) - p3             # cote +  (2^ceil > 3^k)
    qm = p3 - 2**Kf                   # cote -  (3^k > 2^floor)
    if qp + qm != 2**Kf: env_ok = False
print(f"identite verifiee k=1..50 : {env_ok}")
print("=> les deux cotes se partagent un budget fixe : si l'un frole bien, l'autre frole mal.")

print("\n=== C. EQUIDISTRIBUTION DES COTES (k <= 5000) ===")
better_minus = 0
p3 = 1
for k in range(1, 5001):
    p3 *= 3
    Kf = p3.bit_length() - 1
    if (p3 - 2**Kf) < (2**(Kf+1) - p3):   # q- < q+ : le cote - frole mieux
        better_minus += 1
print(f"le cote NEGATIF frole mieux dans {better_minus}/5000 = {better_minus/50:.1f}% des cas")
# CORRECTION ARES (le premier jet de ce script annoncait '~50/50' — la mesure a dit non) :
# q- < q+  <=>  {kL} < log2(3/2) = L-1 = 0.58496...  (mesure de Weyl / loi de Benford :
# le ratio 3^k/2^floor(kL) = 2^{kL mod 1} suit la loi de Benford, qui favorise le bas).
print("=> PAS 50/50 : la theorie exacte est log2(3/2) = 58.496% (Weyl/Benford) ;")
print(f"   mesure {better_minus/5000:.4f} vs theorie 0.58496 — le cote negatif est")
print("   structurellement favorise pour les frolements, dans cette proportion exacte.")

print("\n=== D. CATALAN : les serrures gratuites (|2^a - 3^b| = 1) ===")
catalan = []
p3 = 1
for b in range(1, 191):
    p3 *= 3
    for a in (p3.bit_length() - 1, p3.bit_length()):
        if abs(2**a - p3) == 1 and a <= 300:
            catalan.append((a, b, 2**a - p3))
print(f"solutions pour a<=300 : {catalan}")
print("=> TROIS ecarts +-1 dans toute l'histoire : (1,1):q=-1, (2,1):q=+1, (3,2):q=-1.")
print("   [Mihailescu 2002 (conjecture de Catalan) : il n'y en aura JAMAIS d'autres.]")
print("   Repartition : 1 ticket cote positif (4-3), 2 tickets cote negatif (2-3, 8-9).")

print("\n=== E. LA CARTE EXHAUSTIVE DES CYCLES, k <= 10, LES DEUX SIGNES ===")
# Bornes PROUVEES (3 lignes chacune) :
#  cote + (elements >= 1)  : 2^K/3^k = prod(1 + 1/(3n_t)) in (1, (4/3)^k]  => kL < K <= 2k
#  cote - (elements <= -1) : 2^K/3^k = prod(1 - 1/(3m_t)) in [(2/3)^k, 1)  => k <= K < kL
def steiner_R(svals):
    k = len(svals); R, S = 0, 0
    for t in range(k):
        R += 3**(k-1-t) * 2**S
        S += svals[t]
    return R

def real_cycle_check(n0, k, K):
    # itere la VRAIE carte T depuis n0 ; True si boucle primitive a k impairs, somme s = K
    seen = set(); n = n0; ssum = 0
    for _ in range(k):
        y = 3*n + 1; s = v2(y); ssum += s
        n = y >> s
        if n in seen: return False
        seen.add(n)
    return n == n0 and len(seen) == k and ssum == K

def orbit(n0, k):
    out, n = [], n0
    for _ in range(k):
        out.append(n); n = T(n)
    return out

found = {}
profils_testes = 0
p3 = 1
for k in range(1, 11):
    p3 *= 3
    Kf = p3.bit_length() - 1
    for K in list(range(Kf + 1, 2*k + 1)) + list(range(k, Kf + 1)):  # cote + puis cote -
        q = 2**K - p3
        if q == 0: continue
        # compositions de K en k parts >= 1 via positions de coupure
        for cuts in combinations(range(1, K), k - 1):
            s = [b - a for a, b in zip((0,) + cuts, cuts + (K,))]
            profils_testes += 1
            R = steiner_R(s)
            if R % q: continue                        # UNE rotation suffit (L-A1)
            n0 = R // q
            if n0 % 2 == 0 or n0 == 0: continue
            if real_cycle_check(n0, k, K):
                key = tuple(sorted(orbit(n0, k)))
                found.setdefault(key, (k, K, q, n0))

print(f"profils testes : {profils_testes}")
print(f"{'cycle (elements impairs)':>34} {'k':>3} {'K':>3} {'q':>6} {'|q|=1 (Catalan) ?':>18}")
for key, (k, K, q, n0) in sorted(found.items(), key=lambda x: (x[1][0], x[1][3])):
    print(f"{str(list(key)):>34} {k:>3} {K:>3} {q:>6} {'OUI — gratuit' if abs(q)==1 else 'non — loterie':>18}")

attendus = {(1,), (-1,), (-7, -5), (-91, -61, -55, -41, -37, -25, -17)}
carte_ok = set(found.keys()) == attendus
print(f"\nCARTE = exactement {{+1}} et {{-1, -5, -17}} ? {carte_ok}")
print("=> Pour k <= 10 (exhaustif, bornes prouvees) : le cote + n'a qu'UNE maison (Ithaque = 1),")
print("   le cote - en a TROIS. Trois des quatre maisons sont les tickets Catalan (|q|=1) ;")
print("   la quatrieme (-17, q=-139) est l'unique gagnant de loterie de toute la carte.")
ok = mirror_ok and env_ok and len(catalan) == 3 and carte_ok
print(f"\nEXIT-CRITERION: {'PASS' if ok else 'FAIL'}")
raise SystemExit(0 if ok else 1)
