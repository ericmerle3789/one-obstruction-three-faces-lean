#!/usr/bin/env python3
# BRECHE-124 — LA LECTURE (second temoin) : LE MOT BALANCE EST-IL DEJA EXCLU ? KNIGHT 2025 CONTRE L-A11.
#
# CONTEXTE. L-A11 (round 15) : le mot de Sturm g_j = ceil(jL) - ceil((j-1)L), L = log2 3, porte
# R = sum x_min/x_j ~ 0,72 k, donc la borne triviale R <= k du sceau (L-A8) n'est pas ameliorable.
# La lecture a trouve K. Knight, "Collatz high cycles do not exist", Discrete Math. 349(3) (2025)
# 114812 : le "high cycle" (k,x) a pour vecteur de parite le MOT DE CHRISTOFFEL SUPERIEUR
# (des 1 aux positions floor(k i / x)), et AUCUN high cycle n'est entier. Sa preuve : symetrie
# des mots de Christoffel (le renverse est une rotation, lemme de Cohn), SANS minoration de
# 2^k - 3^x (sans Baker). Question : le mot de L-A11 est-il celui de Knight ?
#
# CONVENTIONS. Knight : k = longueur en pas de T, x = nombre d'impairs. Ici : S = longueur, k = impairs.
#
# PREDICTIONS (NASA, ecrites avant execution) :
#  P1  Les deux exemples de Knight (Ex 4.2 : (8,5) -> 11011010 ; Ex 4.3 : (21,13)) se reproduisent.
#  P2  Le mot de Sturm (lineaire, pente irrationnelle L) et le mot de Christoffel (S,k) (circulaire,
#      pente rationnelle) coincident CIRCULAIREMENT pour certains k et PAS pour d'autres. Prediction :
#      egaux pour k = 3,4,5,8,10,13,15 ; differents pour k = 7,11,14 (mesure exploratoire du 12/09).
#  P3  [RETRACTEE A L'EXECUTION, 2026-09-12 — gardee visible] "R/k -> 1/(2 ln 2) aussi sur le mot de
#      Knight". FAUX : sur le mot de Christoffel la pente est RATIONNELLE S/k, la marche u_i =
#      {S i/k} - i eps/k (eps = S - kL) vit dans une bande de hauteur 1 + eps, pas 1 ; R/k depend de eps
#      (0,597 a k = 156 ou eps = 0,75 ; 0,717 a k = 1000 ou eps = 0,037). Ce que L-A11 a besoin est
#      seulement R LINEAIRE en k. Prediction corrigee : R >= k/4 exactement (termes >= 2^-(1+eps) > 1/4),
#      et R >= k/2 mesure pour tout k <= 300 ; R/k s'approche de 0,7213 quand eps est petit.
#  P4  Si g = gcd(S,k) > 1, le mot de Christoffel (S,k) est la puissance g-ieme du mot de
#      Christoffel (S/g, k/g), et S/g = ceil((k/g) L). Donc L-A2 (mot repete <=> base) ramene le
#      cas non premier au cas premier, ou Knight s'applique : LE CYCLE BALANCE EST EXCLU A TOUT k.
#  P5  *** RE-VERIFICATION BRUTE DE KNIGHT *** Pour tout (S,k) premiers entre eux, S > kL, k <= 60 :
#      le membre f(v_h) du cycle rationnel de mot v_h N'EST PAS ENTIER (sauf (2,1) : le cycle 1-2).
#  P6  CONTROLE : le cycle trivial (S,k) = (2,1), v_h = "10", donne f = 1, entier.
#  P7  Le mecanisme du preprint Buchi (Dhiman-Pandey, arXiv 2601.12772 v2) : sur la classe toute-
#      montante x = 2^k m - 1, T^k(x) = 3^k m - 1 — c'est le residu u_3 = 2^k - 1 de L-A10.
from fractions import Fraction
from math import gcd
from mpmath import mp, mpf, log, ceil as mceil
mp.dps = 60
L = log(3)/log(2)
FAILS = []
def check(nom, ok, detail=""):
    print(f"  [{'PASS' if ok else 'FAIL'}] {nom}" + (f"   {detail}" if detail else ""))
    if not ok: FAILS.append(nom)
def T(x): return x//2 if x % 2 == 0 else (3*x+1)//2
def knight_pv(S, k):                   # Def 4.1 : des 1 aux positions floor(S i / k), i = 0..k-1
    v = [0]*S
    for i in range(k): v[(S*i)//k] = 1
    return v
def sturm_pv(k):                       # L-A11 : des 1 aux positions ceil(jL), j = 0..k-1, longueur S = ceil(kL)
    S = int(mceil(k*L)); v = [0]*S
    for j in range(k): v[int(mceil(j*L))] = 1
    return v
def rot_equal(a, b):
    return len(a) == len(b) and any(a == b[r:]+b[:r] for r in range(len(b)))
def cycle_member(v):                   # l'unique rationnel m avec T^|v|(m) = m le long de v : composer n -> a n + b
    a, b = Fraction(1), Fraction(0)
    for bit in v:
        if bit: a, b = a*Fraction(3,2), b*Fraction(3,2) + Fraction(1,2)
        else:   a, b = a/2, b/2
    return b/(1-a)                     # m = a m + b
def R_of(v):                           # R = sum_j x_min/x_j sur les impairs, limite grand x : x_j/x_0 = 3^j / 2^(G_j)
    ones = [i for i, bit in enumerate(v) if bit]
    u = [j*L - ones[j] for j in range(len(ones))]           # log2(x_j/x_0) = j L - (position du j-ieme 1)
    umin = min(u)
    return sum(mpf(2)**(umin-uj) for uj in u)

print("=" * 94); print("CANARIS"); print("=" * 94)
check("C1  T(7)=11, T(4)=2", T(7) == 11 and T(4) == 2)
check("C2  cycle_member('10') = 1 (cycle trivial)", cycle_member([1,0]) == 1)
check("C3  cycle_member('11111000') = 211/13 (Knight Ex 2.1)", cycle_member([1,1,1,1,1,0,0,0]) == Fraction(211,13))
# C4, premiere version : "1100 n'est pas une rotation de 1001" — FAUX (rotations de 1001 : 1001, 0011, 0110, 1100).
# Le canari a saute sur le TEST, pas sur le code ; corrige le 2026-09-12, le code n'a pas bouge.
check("C4  rot_equal reconnait une rotation et rejette une non-rotation", rot_equal([1,0,0,1], [0,1,1,0]) and not rot_equal([1,0,1,0], [1,1,0,0]))
assert not FAILS

print(); print("=" * 94); print("P1 — LES EXEMPLES DE KNIGHT"); print("=" * 94)
check("Ex 4.2 (8,5) = 11011010", ''.join(map(str, knight_pv(8,5))) == "11011010")
check("Ex 4.3 (21,13) = 110110101101101011010", ''.join(map(str, knight_pv(21,13))) == "110110101101101011010")

print(); print("=" * 94); print("P2/P3 — STURM (L-A11) CONTRE CHRISTOFFEL (KNIGHT) : MEME MOT CIRCULAIRE ? ET R SUR LES DEUX"); print("=" * 94)
print(f"  {'k':>5} {'S':>5} {'gcd':>4} {'Sturm≡Knight':>13} {'R/k Sturm':>10} {'R/k Knight':>11}")
egaux, differents = [], []
for k in list(range(2, 41)) + [100, 156, 200, 1000]:
    S = int(mceil(k*L)); g = gcd(S, k)
    a, b = sturm_pv(k), knight_pv(S, k)
    same = rot_equal(a, b)
    (egaux if same else differents).append(k)
    Ra, Rb = R_of(a), R_of(b)
    if k <= 16 or k in (40, 100, 156, 200, 1000):
        print(f"  {k:>5} {S:>5} {g:>4} {str(same):>13} {float(Ra)/k:>10.4f} {float(Rb)/k:>11.4f}")
    if k >= 1000:
        eps = float(S - k*L)
        check(f"k={k}: eps = S - kL = {eps:.3f} petit => R/k de Knight proche de 0.7213", abs(float(Rb)/k - 0.72135) < 0.01, f"R/k = {float(Rb)/k:.4f}")
rk_min = min((float(R_of(knight_pv(int(mceil(k*L)), k)))/k, k) for k in range(2, 301))
check(f"R >= k/2 sur le mot de Knight pour tout k <= 300 (minimum R/k = {rk_min[0]:.4f} a k = {rk_min[1]})", rk_min[0] >= 0.5)
check("R >= k/4 exactement sur le mot de Knight (bande de hauteur <= 1 + eps < 2), k <= 300",
      all(R_of(knight_pv(int(mceil(k*L)), k)) >= mpf(k)/4 for k in range(2, 301)))
check("P2 : egaux pour k = 3,4,5,8,10,13,15", all(k in egaux for k in (3,4,5,8,10,13,15)))
check("P2 : differents pour k = 7,11,14", all(k in differents for k in (7,11,14)))
print(f"  egaux (k<=40)      : {[k for k in egaux if k<=40]}")
print(f"  differents (k<=40) : {[k for k in differents if k<=40]}")
print("  -> deux mots quasi balances distincts en general ; le mot de Knight est LE mot circulairement balance")
print("     (unique a rotation pres quand gcd(S,k)=1) ; le mot de Sturm lineaire casse la balance a la couture.")

print(); print("=" * 94); print("P4 — gcd(S,k) = g > 1 : CHRISTOFFEL(S,k) = CHRISTOFFEL(S/g,k/g)^g, ET S/g = ceil((k/g) L)"); print("=" * 94)
bad = []
for k in range(2, 301):
    S = int(mceil(k*L)); g = gcd(S, k)
    if g == 1: continue
    base = knight_pv(S//g, k//g)
    if knight_pv(S, k) != base*g or S//g != int(mceil((k//g)*L)): bad.append(k)
check("pour tout k <= 300 avec gcd > 1 : puissance g-ieme du mot premier, et S/g = ceil((k/g) L)", not bad, f"echecs : {bad[:5] if bad else 'aucun'}")
print("  -> L-A2 (repete <=> base) + Knight (base) : le cycle balance est exclu a TOUTE longueur.")

print(); print("=" * 94); print("P5/P6 — RE-VERIFICATION BRUTE : f(v_h) N'EST JAMAIS ENTIER (k <= 60, (S,k) premiers, S > kL)"); print("=" * 94)
n_pairs, entiers = 0, []
for k in range(1, 61):
    for S in range(k+1, 2*k+2):
        if gcd(S, k) != 1 or not (S > k*L): continue
        m = cycle_member(knight_pv(S, k)); n_pairs += 1
        if m.denominator == 1: entiers.append((S, k, m))
check(f"{n_pairs} paires (S,k) testees : le seul membre entier est le cycle trivial (2,1) -> 1",
      entiers == [(2, 1, Fraction(1))], f"entiers trouves : {entiers}")
print("  -> le theoreme de Knight se re-verifie a la main jusqu'a k = 60 (au-dela de tout doute pour ces tailles).")

print(); print("=" * 94); print("P7 — LE MECANISME BUCHI : LA CLASSE TOUTE-MONTANTE EST LE RESIDU DE L-A10"); print("=" * 94)
ok = True
for k in range(1, 40):
    for m in (1, 2, 3, 7, 1000):
        x = (1 << k)*m - 1; y = x
        for _ in range(k):
            ok &= (y % 2 == 1); y = T(y)
        ok &= (y == 3**k*m - 1)
check("T^k(2^k m - 1) = 3^k m - 1, tous les pas impairs, k = 1..39", ok)
print("  -> la relation a k pas, k porte par 2^k, epingle (2^k - 1, 3^k - 1) : base 2 d'un cote, base 3 de l'autre.")
print("     Cobham-Semenov interdit qu'un tel ensemble soit definissable dans les deux bases : c'est l'obstruction ×2×3, en logique.")

print(); print("=" * 94); print(f"TOTAL : {'TOUS LES CONTROLES PASSENT' if not FAILS else 'ECHECS : ' + str(FAILS)}"); print("=" * 94)
