#!/usr/bin/env python3
# test_REQ-MATH-023_loterie_calibree.py — ARES (miroir, pas 2 : la loterie en COLLIERS + le budget restant)
#
# CORRECTIONS de REQ-022 (auto-RED TEAM) :
#  (a) les hits C=1 arrivent par ORBITES de rotation (gcd invariant par rotation, L-A1) : le bon
#      compteur de tirages est le COLLIER (mot a rotation pres), pas le mot.
#  (b) le verdict "censure ou pas" exige le budget TOTAL restant (n>14) : serie Σ colliers/|q|,
#      qui doit decroitre comme ~2^{-c_gen·n} (c_gen=0.0793, constante de Ben) — a MESURER.
# PREDICTIONS AVANT MESURE :
#  P1 budgets colliers ~ budgets mots / p_moyen (facteur ~2-4).
#  P2 nord n<=14 : P(0 primitif) pas alarmant (>5%) une fois en colliers.
#  P3 la queue n>14 CONVERGE (ratio ~2^-0.08 par n, pics aux convergents 41/26, 84/53...) ;
#     la valeur totale restante dit si le mur petit-echelle est "budget" ou "censure".
import math, itertools
from math import gcd

def beta(m): return 3**m - 2**m
def B_of(ms, ss):
    p=len(ms); n=sum(ms); B=0; Kpre=0; Maf=n
    for t in range(p):
        Maf -= ms[t]; B += 3**Maf * 2**Kpre * beta(ms[t]); Kpre += ms[t]+ss[t]
    return B
def comps(total, parts):
    if parts==1: yield (total,); return
    for cuts in itertools.combinations(range(1,total), parts-1):
        pts=(0,)+cuts+(total,)
        yield tuple(pts[i+1]-pts[i] for i in range(parts))
def canon(ms, ss):
    w=list(zip(ms,ss)); p=len(w)
    return min(tuple(w[r:]+w[:r]) for r in range(p))
def log2_big(a):
    e=a.bit_length()-53
    return (e + math.log2(a >> e)) if e>0 else math.log2(a)
def log2C(a,b):
    if b<0 or b>a: return float('-inf')
    return (math.lgamma(a+1)-math.lgamma(b+1)-math.lgamma(a-b+1))/math.log(2)

# ===================== CANARI colliers =====================
print("=== CANARI : colliers de la cellule (7,11) — 84 mots, l'orbite -17 = 1 collier de 2 ===")
seen={}; hits_neck=set()
n,S=7,4; K=n+S; q=2**K-3**n; a=abs(q)
cnt=0
for p in range(1,min(n,S)+1):
    for ms in comps(n,p):
        for ss in comps(S,p):
            cnt+=1; c=canon(ms,ss); seen[c]=seen.get(c,0)+1
            if B_of(ms,ss)%a==0: hits_neck.add(c)
necks=len(seen)
print(f"  mots={cnt} (att.84) | colliers={necks} | colliers-hit={len(hits_neck)} (att.1)")
if not (cnt==84 and len(hits_neck)==1): print("CANARI FAIL"); raise SystemExit(1)
print("CANARIS: PASS\n")

# ===================== BUDGETS EXACTS EN COLLIERS, n<=14 =====================
print("=== budgets exacts en COLLIERS (n<=14, |q|>1) ===")
NMAX=14; SMAX=9
bud={'sud':0.0,'nord':0.0}; hitp={'sud':0,'nord':0}; hith={'sud':0,'nord':0}
for n in range(2,NMAX+1):
    for S in range(1,min(SMAX,2*n)+1):
        K=n+S; q=2**K-3**n; a=abs(q)
        if a==1: continue
        shore='sud' if q<0 else 'nord'
        cs={}; hs=set(); prim=set()
        for p in range(1,min(n,S)+1):
            for ms in comps(n,p):
                for ss in comps(S,p):
                    c=canon(ms,ss); cs[c]=1
                    if B_of(ms,ss)%a==0:
                        hs.add(c)
                        w=list(zip(ms,ss)); pp=len(w)
                        if not any(w==w[:t]*(pp//t) for t in range(1,pp) if pp%t==0): prim.add(c)
        bud[shore]+=len(cs)/a; hith[shore]+=len(hs); hitp[shore]+=len(prim)
for sh in ('sud','nord'):
    lam=bud[sh]
    print(f"  {sh.upper():>4} : budget colliers = {lam:5.2f} | colliers-hit = {hith[sh]} (dont PRIMITIFS {hitp[sh]}) | P(0 primitif | Poisson) = {math.exp(-lam):.3f}")

# ===================== LA QUEUE : budget restant n=15..200 (approx colliers = mots/p) =====================
print("\n=== budget RESTANT par tranches (approx colliers = Σ_p mots_p/p / |q|) ===")
def lam_cell(n,S):
    K=n+S; q=2**K-3**n; a=abs(q)
    if a==1: return 0.0,q
    la=0.0; l2a=log2_big(a)
    for p in range(1,min(n,S)+1):
        t=log2C(n-1,p-1)+log2C(S-1,p-1)-math.log2(p)-l2a
        if t>-60: la+=2.0**t
    return la,q
tranches=[(15,30),(31,60),(61,120),(121,200)]
tot={'sud':0.0,'nord':0.0}; best=[]
for lo,hi in tranches:
    tr={'sud':0.0,'nord':0.0}
    for n in range(lo,hi+1):
        Smax=int(0.5849625*n)+3
        for S in range(1,Smax+1):
            la,q=lam_cell(n,S)
            sh='sud' if q<0 else 'nord'
            tr[sh]+=la; tot[sh]+=la
            if la>0.02: best.append((la,n,n+S,q<0))
    print(f"  n=[{lo:3d},{hi:3d}] : sud += {tr['sud']:8.4f} | nord += {tr['nord']:8.4f}")
print(f"  TOTAL restant n=15..200 : SUD = {tot['sud']:.4f} | NORD = {tot['nord']:.4f}")
print("  cellules dominantes (lambda>0.02) :")
for la,n,K,south in sorted(best,reverse=True)[:8]:
    print(f"    n={n:3d} K={K:3d} {'SUD' if south else 'NORD'} lambda={la:.3f}  (K/n={K/n:.4f})")
print("\n=== LECTURE ===")
print("Budget vie entiere de chaque rive = budget n<=14 + queue. Si la queue est petite et que le")
print("sud a paye ~son budget (1 collier primitif, -17) tandis que le nord n'a rien paye : l'ecart")
print("nord se mesure en P(0). La conclusion honnete est chiffree ci-dessus, pas proclamee.")
raise SystemExit(0)
