#!/usr/bin/env python3
# BRECHE-125 — AUDIT DU ROUND 15 (revue Macindoe du 2026-09-22) : DEUX CHOSES A ETABLIR DE MA MAIN.
#
#  A. Le corrsum du §167 (run_120.py) n'est PAS le numerateur du cycle. Pour un mot de gaps
#     g = (g_0..g_{k-1}), n_{j+1} = (3 n_j + 1)/2^{g_j}, on a par recurrence
#        n_k * 2^S = 3^k n_0 + N(g),   N(g) = sum_j 3^{k-1-j} 2^{g_0+...+g_{j-1}}   (sommes PREFIXES),
#     donc sur un cycle n_0 * (2^S - 3^k) = N(g). run_120 calcule sum_j 3^{k-1-j} 2^{g_{j+1}+...+g_{k-1}}
#     (sommes SUFFIXES). Trouve par le vérificateur "corrsum" du workflow du 22/09 ; refait ici.
#  B. La fenetre "retiree" de L-A8 (4.955e10 = 49 547 666 543 a X = 2^71) est exactement la fenetre de
#     Legendre de la route DIRECTE : eps = K - n log2 3 = sum log2(1 + 1/(3 x_i)) <= n/(3 X ln 2),
#     n < sqrt(3 X ln2 / 2). La chaine seam_bound de L-A8 perd un facteur 2 (lemme (m+1)^p < 2 m^p),
#     d'ou 3.5035e10. Meme 22 convergents, meme decharge, marge doublee. Trouve par la note de
#     sourçage de Macindoe (round 15) + le vérificateur "window" + trois referes ; refait ici.
#
# PREDICTIONS (NASA, ecrites avant execution) :
#  P1  Sur les cycles entiers de x0 = 1, -1, -5, -7, -17, -25, -41 : x0*d = N_prefix(g) TOUJOURS ;
#      N_suffix(g) echoue sur -5, -17, -25, -41 (mots non palindromes).
#  P2  Tables de residus a k = 12, 14, 15 (exhaustif) : avec N_prefix, compte au residu 0 = 0 pour
#      3 <= k <= 15 ; ecarts a Poisson(C/d) de -19 % a m = 3 et ~ -32 % a m = 4 (k = 15) —
#      PAS "0,1 %". Avec N_suffix on retrouve les chiffres de run_120 (1735122 / 582630 / ...).
#  P3  N_suffix ≡ 0 (mod d) a des solutions a k = 3, 4, 5, 8, 11 (faux positifs) ; N_prefix n'en a
#      aucune pour 3 <= k <= 15.
#  P4  Fenetre directe floor(sqrt(3*2^71*ln2/2)) = 49547666543, encadrement exact W^2 < 3X ln2/2 < (W+1)^2 ;
#      fenetre chaine floor(sqrt(3*2^71*ln2/4)) = 35035491004 ; rapport sqrt 2 a 20 decimales.
#  P5  Les convergents de log2 3 de denominateur <= 49547666543 sont exactement les 22 de L-A8
#      (dernier 6586818670 ; suivant 65470613321 hors des deux fenetres).
#  P6  Decharge directe : min_j theta_j/(q_j delta_direct) = 10.8865 (chaine : 5.4433, moitie exacte) ;
#      q_22 donne 0.499 (< 1 : la fenetre est limitee par Legendre, pas par la decharge) ;
#      forme entiere 1000 q (q+q') <= 2079 * 2^71 vraie pour les 22, fausse pour q_22.
#  P7  Annulation de t : pour n = t q_j, K = t p_j, le rapport eps/(n delta) ne depend pas de t.
#  P8  CONTROLE NEGATIF : a X = 2^71 la route directe ne depasse PAS q_22 = 65470613321, meme avec le
#      meilleur R possible (R = 0.72135 n, mot de Sturm) : la fenetre serait 58337919180 < q_22.
from itertools import combinations
from math import comb, ceil, log2, exp, factorial, isqrt
from collections import Counter
from mpmath import mp, mpf, log, sqrt, floor
FAILS = []
def check(nom, ok, detail=""):
    print(f"  [{'PASS' if ok else 'FAIL'}] {nom}" + (f"   {detail}" if detail else ""))
    if not ok: FAILS.append(nom)

def odd_cycle_word(x0):
    x = x0; g = []
    while True:
        y = 3*x + 1; v = 0
        while y % 2 == 0: y //= 2; v += 1
        g.append(v); x = y
        if x == x0: return tuple(g)
def N_prefix(g):
    k = len(g); s = 0; pre = 0
    for j in range(k): s += 3**(k-1-j) * 2**pre; pre += g[j]
    return s
def N_suffix(g):
    k = len(g); s = 0; suf = 0
    for j in range(k-1, -1, -1): s += 3**(k-1-j) * 2**suf; suf += g[j]
    return s
def comps(S, k):
    for cut in combinations(range(1, S), k-1):
        b = (0,) + cut + (S,); yield tuple(b[i+1]-b[i] for i in range(k))

print("=" * 94); print("CANARIS (a la main avant le code)"); print("=" * 94)
check("C1  cycle trivial : mot (2,), d = 2^2 - 3 = 1, N_prefix = N_suffix = 1", N_prefix((2,)) == 1 == N_suffix((2,)))
check("C2  mot (2,2) (cycle trivial double) : N_prefix = 3 + 4 = 7 = 1*(16-9)", N_prefix((2,2)) == 7)
check("C3  mot (3,1) : N_prefix = 3 + 8 = 11, N_suffix = 6 + 1 = 7 (le 'canari' de run_120 n'est pas un cycle)", N_prefix((3,1)) == 11 and N_suffix((3,1)) == 7)
check("C4  isqrt(2079*2^71 // 4000) = 35031771147 (fenetre entiere de L-A8)", isqrt(2079 * 2**71 // 4000) == 35031771147)
assert not FAILS, FAILS

print(); print("=" * 94); print("P1 — QUELLE SOMME EST LE NUMERATEUR DU CYCLE ? Test sur les cycles entiers reels"); print("=" * 94)
print(f"  {'x0':>4} {'mot g':>24} {'d':>6} {'x0*d':>6} {'N_prefix':>9} {'N_suffix':>9}")
pref_ok = True; suf_fail = []
for x0 in (1, -1, -5, -7, -17, -25, -41):
    g = odd_cycle_word(x0); k = len(g); S = sum(g); d = 2**S - 3**k
    print(f"  {x0:>4} {str(g):>24} {d:>6} {x0*d:>6} {N_prefix(g):>9} {N_suffix(g):>9}")
    pref_ok &= (x0*d == N_prefix(g))
    if x0*d != N_suffix(g): suf_fail.append(x0)
check("x0*d = N_prefix(g) sur les 7 cycles", pref_ok)
check("N_suffix echoue exactement sur -5, -17, -25, -41", suf_fail == [-5, -17, -25, -41], str(suf_fail))

print(); print("=" * 94); print("P2/P3 — TABLES DE RESIDUS EXHAUSTIVES : numerateur vrai (prefixe) contre run_120 (suffixe)"); print("=" * 94)
run120 = {12: [445863, 67100, 4037, 132, 3, 0], 14: [3141930, 431550, 30678, 1412, 67, 2], 15: [1735122, 582630, 98147, 11440, 905, 64]}
zero_pref, zero_suf = {}, {}
for k in range(3, 16):
    S = ceil(k*log2(3)); d = (1 << S) - 3**k; C = comb(S-1, k-1); lam = C/d
    hP = Counter(); hS = Counter()
    for g in comps(S, k): hP[N_prefix(g) % d] += 1; hS[N_suffix(g) % d] += 1
    zero_pref[k] = hP.get(0, 0); zero_suf[k] = hS.get(0, 0)
    if k in (12, 14, 15):
        cP = Counter(hP.values()); cP[0] = d - len(hP); cS = Counter(hS.values()); cS[0] = d - len(hS)
        print(f"  k={k}  S={S}  d={d}  C={C}  lambda={lam:.4f}")
        print(f"    {'m':>2} {'N vrai (prefixe)':>17} {'ecart Poisson':>14} {'run_120 (suffixe)':>18} {'ecart':>7}")
        devs = []
        for m in range(6):
            pred = d*exp(-lam)*lam**m/factorial(m)
            dP = 100*(cP.get(m, 0)-pred)/pred if pred > 0.5 else 0.0; dS = 100*(cS.get(m, 0)-pred)/pred if pred > 0.5 else 0.0
            devs.append(dP)
            print(f"    {m:>2} {cP.get(m,0):>17} {dP:>+13.1f}% {cS.get(m,0):>18} {dS:>+6.1f}%")
        check(f"k={k}: la table suffixe reproduit run_120", [cS.get(m, 0) for m in range(6)] == run120[k])
        if k == 15:
            check("k=15: numerateur vrai sous-disperse, ecart a m=3 < -15 % et a m=4 < -25 %", devs[3] < -15 and devs[4] < -25, f"{devs[3]:+.1f} %, {devs[4]:+.1f} %")
check("residu 0 : compte 0 pour N_prefix a tout k de 3 a 15", all(v == 0 for v in zero_pref.values()), str(zero_pref))
fp = sorted(k for k, v in zero_suf.items() if v > 0)
check("residu 0 : N_suffix a des solutions (faux positifs) exactement a k = 3, 4, 5, 8, 11", fp == [3, 4, 5, 8, 11], str(fp))
print("  -> le 'Poisson a 0,1 %' du §167 est une propriete de la somme suffixe, pas du numerateur du cycle.")

print(); print("=" * 94); print("P4/P5 — LA FENETRE DE LA ROUTE DIRECTE, EN EXACT"); print("=" * 94)
res = {}
for dps in (60, 120):
    mp.dps = dps
    X = mpf(2)**71; ln2 = log(2); L = log(3)/ln2
    Wd = int(floor(sqrt(3*X*ln2/2))); Wc = int(floor(sqrt(3*X*ln2/4)))
    bd = mpf(Wd)**2 < 3*X*ln2/2 < mpf(Wd+1)**2; bc = mpf(Wc)**2 < 3*X*ln2/4 < mpf(Wc+1)**2
    def convergents(x, n):
        a = []; p0, q0, p1, q1 = 1, 0, int(floor(x)), 1; x = x - floor(x); a.append((p1, q1))
        for _ in range(n):
            x = 1/x; ai = int(floor(x)); x -= ai; p0, q0, p1, q1 = p1, q1, ai*p1+p0, ai*q1+q0; a.append((p1, q1))
        return a
    cv = convergents(L, 30)
    res[dps] = (Wd, bd, Wc, bc, [q for p, q in cv[:26]], sqrt(3*X*ln2/2)/sqrt(3*X*ln2/4))
check("fenetre directe = 49547666543 aux deux precisions, encadrement exact", all(res[d][0] == 49547666543 and res[d][1] for d in res))
check("fenetre chaine  = 35035491004 aux deux precisions, encadrement exact", all(res[d][2] == 35035491004 and res[d][3] for d in res))
check("rapport des fenetres = sqrt 2 (20 decimales)", abs(res[120][5] - sqrt(mpf(2))) < mpf(10)**-20, str(res[120][5])[:24])
check("denominateurs des convergents identiques aux deux precisions", res[60][4] == res[120][4])
qs = res[120][4]
inW = [q for q in qs if q <= 49547666543]
check("22 convergents <= fenetre directe, dernier 6586818670, suivant 65470613321", len(inW) == 22 and inW[-1] == 6586818670 and [q for q in qs if q > 49547666543][0] == 65470613321)
check("fenetres entieres : 2000n^2 <= 2079X -> 49542405870 ; 4000n^2 <= 2079X -> 35031771147", isqrt(2079*2**71//2000) == 49542405870 and isqrt(2079*2**71//4000) == 35031771147)

print(); print("=" * 94); print("P6/P7 — LA DECHARGE DIRECTE : MEMES 22 VERIFICATIONS, MARGE DOUBLEE, t S'ANNULE"); print("=" * 94)
mp.dps = 80
X = mpf(2)**71; ln2 = log(2); L = log(3)/ln2; dd = 1/(3*X*ln2); dc = 2/(3*X*ln2)
cv = convergents(L, 30)
ratios_d = [abs(q*L-p)/(q*dd) for p, q in cv[:22]]; ratios_c = [abs(q*L-p)/(q*dc) for p, q in cv[:22]]
check("min theta_j/(q_j delta_direct) sur les 22 = 10.8865 (a j = 21)", abs(min(ratios_d) - mpf('10.8865394915')) < 1e-9 and ratios_d.index(min(ratios_d)) == 21, str(min(ratios_d))[:12])
check("chaine : exactement la moitie, 5.4433 (le chiffre de L-A8)", abs(min(ratios_c)*2 - min(ratios_d)) < mpf(10)**-60 and abs(min(ratios_c) - mpf('5.4432697458')) < 1e-9)
p22, q22 = cv[22]; r22 = abs(q22*L-p22)/(q22*dd)
check("q_22 : rapport 0.4990 < 1 -> non-vacuite, la fenetre est limitee par Legendre", abs(r22 - mpf('0.4990177409')) < 1e-9 and r22 < 1, str(r22)[:12])
check("forme entiere 1000 q (q+q') <= 2079*2^71 : vraie pour les 22, fausse pour q_22",
      all(1000*cv[j][1]*(cv[j][1]+cv[j+1][1]) <= 2079*2**71 for j in range(22)) and not (1000*q22*(q22+cv[23][1]) <= 2079*2**71))
p21, q21 = cv[21]
check("annulation de t : n = t q_21, K = t p_21 -> meme rapport pour t = 1, 2, 7", len({str(abs(t*q21*L-t*p21)/(t*q21*dd))[:40] for t in (1, 2, 7)}) == 1)
extra = sum(49547666543//q - 35035491004//q for p, q in cv[:22])
print(f"  multiples t*q_j admis par la fenetre large et pas par l'ancienne : {extra:,} — tous couverts par les 22 memes verifications (t s'annule).")

print(); print("=" * 94); print("P8 — CONTROLE NEGATIF : la route directe ne rejoint pas q_22 = 65470613321 a X = 2^71"); print("=" * 94)
Wbest = int(floor(sqrt(3*X*ln2/(2*mpf('0.72134752044')))))
print(f"  fenetre avec R = n         : 49547666543")
print(f"  fenetre avec R = 0.7213 n  : {Wbest}   (meilleur R possible sur les mots admissibles, mot de Sturm)")
print(f"  q_22                       : 65470613321")
check("meme au meilleur R, la fenetre reste < q_22 : rejoindre Hercher demanderait R/n <= 0.5727", Wbest < 65470613321 and abs(Wbest - 58337919180) < 5)
print(f"  R/n necessaire pour atteindre q_22 : {float(3*X*ln2/(2*mpf(65470613321)**2)):.4f}")

print(); print("=" * 94); print(f"TOTAL : {'TOUS LES CONTROLES PASSENT' if not FAILS else 'ECHECS : ' + str(FAILS)}"); print("=" * 94)
