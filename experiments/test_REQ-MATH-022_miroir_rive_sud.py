#!/usr/bin/env python3
# test_REQ-MATH-022_miroir_rive_sud.py — ARES (methode du miroir, pas 1 : la rive sud comme groupe de controle)
#
# PREDICTIONS ECRITES AVANT MESURE (NASA) :
#  P1  Seuls mots C=1 (|q|>1, alphabet canonique s>=1, n<=14) : l'orbite du mot du cycle -17 a
#      (n,K)=(7,11), ses puissances a (14,22), les puissances du trivial a (j,2j), les puissances
#      de ([2],[1]) (le mot de -5) a (2j,3j). AUCUN autre. (La famille -1 = pur-climb s=0, hors
#      alphabet canonique — notee a part : x=-1 pour tout (m,0), |q|=beta_m.)
#  P2  (12,19), q=-7153 : 0 hit malgre une esperance de comptage >~1 (a chiffrer, Poisson P(0)).
#  P3  Budget de Poisson des deux rives : les cycles sud = a peu pres le budget sud ; le nord
#      petit-echelle = son budget (a chiffrer). Lien avec l'asymetrie Benford 58.5% : le sud
#      recolte des |q| plus petits a echelle egale.
#  P4  Accord des cadres : q | B  <=>  q | R0 sur tous les hits.
#
# CANARIS (calcules a la MAIN avant le code) :
#  trivial ([1],[1]) : q=1, B=1, x=1 ;  -5 = ([2],[1]) : q=-1, B=beta_2=5, x=-5 ;
#  -17 = ([4,3],[1,3]) : q=-139, B=27*65+32*19=2363=17*139, x=-17, R0=139 ;
#  beta_2=5, beta_3=19, beta_4=65. (sigma-seq de -17 : 1,1,1,2,1,1,4 -> lettres (4,1),(3,3).)
import math, itertools
from math import gcd, comb

def beta(m): return 3**m - 2**m
def B_of(ms, ss):
    """Numerateur classique : compose x -> (3^m x + beta_m)/2^{m+s}. Point fixe x0 = B/q."""
    p = len(ms); n = sum(ms)
    B = 0; Kpre = 0; Mafter = n
    for t in range(p):
        Mafter -= ms[t]
        B += 3**Mafter * 2**Kpre * beta(ms[t])
        Kpre += ms[t] + ss[t]
    return B
def R0(ms, ss):
    p = len(ms); sig = [ss[t] + ms[(t+1) % p] for t in range(p)]
    Ma = [0]*p; acc = 0
    for t in range(p-1, -1, -1): Ma[t] = acc; acc += ms[t]
    tot, Sp = 0, 0
    for t in range(p): tot += 3**Ma[t] * 2**Sp * (2**ss[t] - 1); Sp += sig[t]
    return tot
def comps(total, parts):
    if parts == 1:
        yield (total,); return
    for cuts in itertools.combinations(range(1, total), parts-1):
        pts = (0,) + cuts + (total,)
        yield tuple(pts[i+1]-pts[i] for i in range(parts))
def is_primitive(ms, ss):
    p = len(ms); w = list(zip(ms, ss))
    return not any(w == w[:t]*(p//t) for t in range(1, p) if p % t == 0)

# ===================== CANARIS =====================
print("=== CANARIS (main d'abord) ===")
c = []
c.append(("trivial q", 2**2 - 3**1 == 1 and B_of((1,),(1,)) == 1))
c.append(("-5 : ([2],[1]) B=5 q=-1 x=-5", 2**3-3**2 == -1 and B_of((2,),(1,)) == 5))
q17 = 2**11 - 3**7
c.append(("-17 : q=-139", q17 == -139))
B17 = B_of((4,3),(1,3))
c.append(("-17 : B=2363=17*139, x=-17", B17 == 2363 and B17 % 139 == 0 and B17//q17 == -17))
c.append(("-17 : R0=139 (cadre reduit, C=1 aussi)", R0((4,3),(1,3)) == 139))
c.append(("beta 2/3/4 = 5/19/65", beta(2)==5 and beta(3)==19 and beta(4)==65))
c.append(("puissance de -5 : ([2,2],[1,1]) x=-5", B_of((2,2),(1,1)) == 85 and (2**6-3**4) == -17 and 85 % 17 == 0))
for name, ok in c: print(f"  [{'OK' if ok else 'FAIL'}] {name}")
if not all(ok for _, ok in c): print("CANARI FAIL"); raise SystemExit(1)
print("CANARIS: PASS\n")

# ===================== BALAYAGE EXHAUSTIF n<=14 =====================
NMAX = 14; SMAX = 9
hits = []            # (n,K,q,word,x,primitive,R0agree)
cells = {}           # (n,K) -> [nwords, a, nhits]
spent = []           # |q|=1
for n in range(2, NMAX+1):
    for S in range(1, min(SMAX, 2*n)+1):
        K = n + S; q = 2**K - 3**n; a = abs(q)
        cnt = 0; h = 0
        for p in range(1, min(n, S)+1):
            for ms in comps(n, p):
                for ss in comps(S, p):
                    cnt += 1
                    B = B_of(ms, ss)
                    if a == 1:
                        spent.append((n, K, q, ms, ss, B//q)); continue
                    if B % a == 0:
                        x = B // q
                        r0 = R0(ms, ss)
                        hits.append((n, K, q, ms, ss, x, is_primitive(ms, ss), r0 % a == 0))
                        h += 1
        cells[(n, K)] = [cnt, a, h]

print("=== HITS C=1 (|q|>1) — la carte complete ===")
print(f"{'n':>3} {'K':>3} {'q':>9} {'mot':>26} {'x':>5} {'primitif':>8} {'R0 ok':>6}")
for (n, K, q, ms, ss, x, prim, r0ok) in hits:
    print(f"{n:>3} {K:>3} {q:>9} {str(ms)+'|'+str(ss):>26} {x:>5} {str(prim):>8} {str(r0ok):>6}")
print(f"\n  mots |q|=1 (stock Gersonides, C indefini) : {len(spent)} — realisations x : {sorted(set(w[5] for w in spent))}")

# ===================== CELLULES D'INTERET : (5,8), (7,11), (12,19) =====================
print("\n=== CELLULES D'INTERET : esperance de comptage vs realite ===")
print(f"{'(n,K)':>8} {'q':>7} {'#mots':>7} {'esper.=#/|q|':>12} {'hits':>5} {'P(0) Poisson':>12}")
for (n, K) in [(5,8), (7,11), (12,19)]:
    cnt, a, h = cells[(n, K)]
    lam = cnt / a
    print(f"{'('+str(n)+','+str(K)+')':>8} {2**K-3**n:>7} {cnt:>7} {lam:>12.3f} {h:>5} {math.exp(-lam):>12.3f}")

# ===================== BUDGET DE POISSON DES DEUX RIVES =====================
print("\n=== BUDGET DES DEUX RIVES (n<=14, |q|>1) : somme des esperances vs hits reels ===")
bud_s = sum(cnt/a for (n,K),(cnt,a,h) in cells.items() if 2**K-3**n < 0 and a > 1)
bud_n = sum(cnt/a for (n,K),(cnt,a,h) in cells.items() if 2**K-3**n > 0 and a > 1)
hit_s = sum(h for (n,K),(cnt,a,h) in cells.items() if 2**K-3**n < 0 and a > 1)
hit_n = sum(h for (n,K),(cnt,a,h) in cells.items() if 2**K-3**n > 0 and a > 1)
hp_s = sum(1 for hh in hits if hh[2] < 0 and hh[6])
hp_n = sum(1 for hh in hits if hh[2] > 0 and hh[6])
print(f"  RIVE SUD  (q<0) : budget = {bud_s:6.2f} | hits = {hit_s} (dont primitifs {hp_s})")
print(f"  RIVE NORD (q>0) : budget = {bud_n:6.2f} | hits = {hit_n} (dont primitifs {hp_n})")

# ===================== LE LIEN BENFORD : qui a la meilleure brique a echelle n ? ===================
print("\n=== A echelle n, quel bord a le plus petit |q| (la meilleure brique-serrure) ? ===")
south_wins = 0; tot = 0
for n in range(2, NMAX+1):
    qs = [abs(2**(n+S) - 3**n) for S in range(1, min(SMAX,2*n)+1) if 2**(n+S) < 3**n]
    qn = [abs(2**(n+S) - 3**n) for S in range(1, min(SMAX,2*n)+1) if 2**(n+S) > 3**n]
    if qs and qn:
        tot += 1; south_wins += (min(qs) < min(qn))
        print(f"  n={n:2d} : min|q| sud = {min(qs):>8} | nord = {min(qn):>8}  -> {'SUD' if min(qs)<min(qn) else 'nord'}")
print(f"  le sud gagne {south_wins}/{tot} (asymptotique attendu ~ log2(3/2) = 58.5% cote sud, Weyl/Benford)")

print("\n=== LECTURE ===")
print("P1: comparer la table des hits a la prediction (que des heritages + l'orbite -17).")
print("P2: (12,19) — si 0 hit avec esperance >1, le 'pourquoi' est statistique (Poisson) ou structurel : voir P(0).")
print("P3: si hits ~ budgets sur les 2 rives, les cycles reels sont le BUDGET DE CHANCE de leur rive ;")
print("    la question du mur devient : le nord est-il pauvre par MANQUE DE BUDGET (rarete diophantienne")
print("    de ses bonnes briques) ou par censure au-dela du budget ? — la reponse chiffree est ci-dessus.")
raise SystemExit(0)
