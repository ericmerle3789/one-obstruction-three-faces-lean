#!/usr/bin/env python3
# BRECHE-123 — AUDIT DES §169, §178, §179 AVANT ENVOI A MACINDOE (round 15) : TROIS CHIFFRES ET UNE
# IDENTIFICATION CORRIGES, LA CONSTRUCTION DE STURM REFAITE EN EXACT.
#
# POURQUOI CE RUN. Les §167, §169, §178, §179 sont les quatre resultats que la session
# "Recherche Pilier" recommandait d'envoyer a Macindoe. Regle ARES : rien ne part sans avoir ete
# refait de zero. Refaits de zero, trois d'entre eux ont des chiffres faux (le §167 se reproduit
# exactement, run_120 relance). Les conclusions qualitatives tiennent toutes ; les chiffres, non.
#
# CE QUI EST CORRIGE ICI :
#  C-169  Les comptes de mots imprimitifs a k=20 et k=24 etaient "<=51" et "<=67" (bornes issues
#         d'un echantillon). Le compte EXACT (formule de Mobius sur les diviseurs communs de k et S)
#         est 5 005 et 792. Fractions : 3,5e-5 et 5,1e-8, au lieu de 3,6e-7 et 4,3e-9.
#         k=6,12,16 et les neuf k a zero etaient justes.
#  C-178  "Les mots extremaux sont precisement ce que la litterature appelle des circuits" : FAUX,
#         et a l'envers. Un m-circuit (Steiner 1977, Simons-de Weger 2005) a m blocs de montees ;
#         le mot de Sturm en a ~0,585 k. Il est le PLUS fragmente, pas le moins. Il vit donc
#         hors de portee de tout theoreme de circuits (Hercher 2023 : m <= 91).
#  C-179  Temps d'arret maximaux sur F2[x] a d=14 et d=16 : 43 et 51 (enumeration exhaustive des
#         2^d polynomes), pas 37 et 39 (echantillon). d=4..12 etaient justes.
#
# PREDICTIONS (NASA, ecrites avant execution) :
#  P1  Mot de Sturm g_j = ceil(jL) - ceil((j-1)L), L = log2(3) : gaps dans {1,2}, somme S = ceil(kL),
#      R = sum_j 2^(u_min - u_j) verifie R/k -> 1/(2 ln 2) = 0,7213 (equirepartition de u_j sur (-1,0]).
#      Prediction : |R/k - 0,7213| < 0,002 des k = 1000, et R >= k/2 a tout k.
#  P2  Nombre de blocs de montees du mot de Sturm = nombre de gaps egaux a 2 = ceil(kL) - k
#      ~ 0,585 k. Prediction : exact, et > 91 des k >= 156.
#  P3  Comptes imprimitifs exacts : 6, 126, 792, 5005, 792 a k = 6, 12, 16, 20, 24 ; zero pour
#      k = 3,4,5,7,8,11,13,14,17. Prediction : exact.
#  P4  F2[x], carte T(f) = f/x si x|f, ((x+1)f+1)/x sinon (Hicks-Mullen-Yucas-Zavislak 2008) :
#      temps d'arret maximal 9,15,21,29,35,43,51 a d = 4..16 pairs, tous <= d^2+2d, et le degre
#      ne depasse jamais d le long de l'orbite (apres chaque pas complet). Prediction : exact.
#  P5  CONTROLE NEGATIF : un mot NON balance (tout 1 puis tout 2, un seul bloc) donne R/k -> 0,
#      i.e. R borne — la borne triviale R <= k n'est serree QUE pour les mots balances.
from math import comb, gcd
from mpmath import mp, mpf, log, ceil as mceil
mp.dps = 60
L = log(3)/log(2)
FAILS = []
def check(nom, ok, detail=""):
    print(f"  [{'PASS' if ok else 'FAIL'}] {nom}" + (f"   {detail}" if detail else ""))
    if not ok: FAILS.append(nom)

print("=" * 94); print("CANARIS (a la main avant le code)"); print("=" * 94)
check("C1  ceil(1*L)=2, ceil(2*L)=4, ceil(3*L)=5 -> gaps 2,2,1", [int(mceil(j*L)) for j in (1,2,3)] == [2,4,5])
check("C2  C(S-1,k-1) at k=6,S=10 is 126", comb(9,5) == 126)
check("C3  F2[x] : T(x^2+1) = ((x+1)(x^2+1)+1)/x = x^2+x+1 ; T(x^2)=x", True)  # computed below, asserted here
check("C4  1/(2 ln 2) = 0.72135", abs(float(1/(2*log(2))) - 0.72135) < 1e-5)
assert not FAILS

print(); print("=" * 94); print("P1/P2 — LE MOT DE STURM : R/k, R >= k/2, ET SON NOMBRE DE BLOCS"); print("=" * 94)
print(f"  {'k':>7} {'gaps⊂{1,2}':>10} {'S':>8} {'blocs':>7} {'blocs/k':>8} {'R':>11} {'R/k':>8} {'R>=k/2':>7}")
for k in (10, 100, 1000, 10000, 100000):
    G = [int(mceil(j*L)) for j in range(k+1)]
    gaps = [G[j]-G[j-1] for j in range(1, k+1)]
    u = [j*L - G[j] for j in range(k)]
    umin = min(u)
    R = sum(mpf(2)**(umin-uj) for uj in u)
    blocs = gaps.count(2)
    print(f"  {k:>7} {str(set(gaps)<={1,2}):>10} {G[k]:>8} {blocs:>7} {blocs/k:>8.4f} {float(R):>11.1f} {float(R)/k:>8.4f} {str(R>=mpf(k)/2):>7}")
    if k >= 1000: check(f"k={k}: |R/k - 0.7213| < 0.002 and R >= k/2", abs(float(R)/k - 0.72135) < 0.002 and R >= mpf(k)/2)
    check(f"k={k}: blocs = ceil(kL) - k", blocs == G[k] - k)
check("blocs > 91 from k = 156 on (Hercher's m <= 91 does not reach the Sturm word)", int(mceil(156*L)) - 156 > 91, f"blocs(156) = {int(mceil(156*L)) - 156}")

print(); print("=" * 94); print("P3 — PORTEE DU THEOREME DES MOTS REPETES : COMPTES EXACTS (Mobius)"); print("=" * 94)
def mobius(n):
    r, m, p = 1, n, 2
    while p*p <= m:
        if m % p == 0:
            m //= p
            if m % p == 0: return 0
            r = -r
        p += 1
    return -r if m > 1 else r
attendu = {6:6, 12:126, 16:792, 20:5005, 24:792, 3:0,4:0,5:0,7:0,8:0,11:0,13:0,14:0,17:0}
print(f"  {'k':>3} {'S':>3} {'gcd(k,S)':>8} {'mots':>16} {'imprimitifs':>12} {'fraction':>10}   journal §169")
journal = {20:'<=51 (faux)', 24:'<=67 (faux)'}
for k in sorted(attendu):
    S = int(mceil(k*L)); g = gcd(k, S)
    total = comb(S-1, k-1)
    prim = sum(mobius(j)*comb(S//j-1, k//j-1) for j in range(1, g+1) if g % j == 0)
    imp = total - prim
    print(f"  {k:>3} {S:>3} {g:>8} {total:>16,} {imp:>12,} {imp/total:>10.2e}   {journal.get(k, attendu[k])}")
    check(f"k={k}: imprimitifs = {attendu[k]}", imp == attendu[k])

print(); print("=" * 94); print("P4 — COLLATZ SUR F2[x] : TEMPS D'ARRET EXHAUSTIFS ET BORNE DU DEGRE"); print("=" * 94)
def T2(f):
    if f & 1 == 0: return f >> 1
    g = ((f << 1) ^ f) ^ 1
    assert g & 1 == 0
    return g >> 1
check("C3 (computed) T(x^2+1) = x^2+x+1 and T(x^2) = x", T2(0b101) == 0b111 and T2(0b100) == 0b10)
attendu4 = {4:9, 6:15, 8:21, 10:29, 12:35, 14:43, 16:51}
print(f"  {'d':>3} {'polys':>6} {'max arret':>10} {'d^2+2d':>7} {'deg max':>8}   journal §179")
journal4 = {14:'37 (faux)', 16:'39 (faux)'}
for d in range(4, 17, 2):
    best = 0; degmax = 0
    for f in range(1 << d, 1 << (d+1)):
        x = f; n = 0
        while x != 1:
            x = T2(x); n += 1; degmax = max(degmax, x.bit_length()-1)
            assert n < 10**6
        best = max(best, n)
    print(f"  {d:>3} {1<<d:>6} {best:>10} {d*d+2*d:>7} {degmax:>8}   {journal4.get(d, attendu4[d])}")
    check(f"d={d}: max stopping time = {attendu4[d]}, <= d^2+2d, degree never exceeds d", best == attendu4[d] and best <= d*d+2*d and degmax <= d)

print(); print("=" * 94); print("P5 — CONTROLE NEGATIF : UN MOT A UN SEUL BLOC A R BORNE"); print("=" * 94)
for k in (100, 1000, 10000):
    S = int(mceil(k*L)); n2 = S - k                   # n2 gaps of 2, k-n2 gaps of 1, all 1s first then all 2s
    gaps = [1]*(k-n2) + [2]*n2
    G = [0]
    for g in gaps: G.append(G[-1]+g)
    u = [j*L - G[j] for j in range(k)]
    umin = min(u)
    R = sum(mpf(2)**(umin-uj) for uj in u)
    print(f"  k={k:>6}: one-block word, R = {float(R):.3f}, R/k = {float(R)/k:.5f}")
check("one-block word: R stays below 10 while k grows 100x", float(R) < 10)
print("  -> R bounded for the most UNbalanced word, ~0.72 k for the most balanced one: the trivial bound")
print("     R <= k is tight exactly on the words the circuit theorems do NOT cover.")

print(); print("=" * 94); print(f"TOTAL : {'TOUS LES CONTROLES PASSENT' if not FAILS else 'ECHECS : ' + str(FAILS)}"); print("=" * 94)
