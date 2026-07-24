#!/usr/bin/env python3
# test_REQ-MATH-034_sommes_exponentielles.py — ARES (programme analytique : la traduction exacte du mur)
# IDENTITE EXACTE : [a | R0] = (1/a) * sum_{j mod a} e(j*R0/a)
# => Nb de mots-cycles d'une cellule = (1/a)[ W + sum_{j != 0} S(j) ],  S(j) = sum_mots e(j*R0/a)
#    terme principal W/a = NOTRE LOTERIE ; tout le mystere est dans les S(j).
# PREDICTIONS AVANT MESURE :
#  P1 [CANARI] la formule redonne EXACTEMENT le compte de cycles par enumeration directe.
#  P2 |S(j)| ~ sqrt(W) pour j typique (annulation racine carree).
#  P3 il existe des j RESONANTS avec |S(j)| >> sqrt(W) (raies spectrales = structure arithmetique).
import math, cmath, itertools
def R0(ms,ss):
    p=len(ms); sig=[ss[t]+ms[(t+1)%p] for t in range(p)]
    Ma=[0]*p; acc=0
    for t in range(p-1,-1,-1): Ma[t]=acc; acc+=ms[t]
    tot,Sp=0,0
    for t in range(p): tot+=3**Ma[t]*2**Sp*(2**ss[t]-1); Sp+=sig[t]
    return tot
def comps(total,parts):
    if parts==1: yield (total,); return
    for cuts in itertools.combinations(range(1,total),parts-1):
        pts=(0,)+cuts+(total,); yield tuple(pts[i+1]-pts[i] for i in range(parts))
def cell_residues(n,S):
    a=abs(2**(n+S)-3**n); res=[]
    for p in range(1,min(n,S)+1):
        for ms in comps(n,p):
            for ss in comps(S,p): res.append(R0(ms,ss)%a)
    return res,a
print("=== ANALYSE PAR CELLULE : sommes exponentielles S(j) ===")
print(f"{'(n,S)':>9} {'a=|q|':>8} {'W':>7} {'W/a':>8} {'cycles dir.':>11} {'formule':>9} {'max|S|':>9} {'moy|S|':>8} {'sqrt(W)':>8} {'max/sqrtW':>10}")
cells=[(3,3),(4,2),(5,3),(6,3),(7,4),(5,4),(6,5),(4,4),(8,5)]
for (n,S) in cells:
    res,a=cell_residues(n,S)
    W=len(res)
    if a<2 or W<2 or a>200000: continue
    direct=sum(1 for r in res if r==0)
    # S(j) pour tous j (a modeste) sinon echantillon
    js=range(a) if a<=4000 else range(0,a,max(1,a//4000))
    mods=[]; tot=0j
    for j in js:
        s=sum(cmath.exp(2j*math.pi*j*r/a) for r in res)
        tot+=s
        if j!=0: mods.append(abs(s))
    formule = (tot.real/a) if a<=4000 else float('nan')
    mx=max(mods) if mods else 0; mean=sum(mods)/len(mods) if mods else 0
    print(f"{'('+str(n)+','+str(S)+')':>9} {a:>8} {W:>7} {W/a:>8.4f} {direct:>11} {formule:>9.3f} {mx:>9.2f} {mean:>8.2f} {math.sqrt(W):>8.2f} {mx/math.sqrt(W):>10.2f}")
print("\n=== P1 CANARI : 'formule' doit egaler 'cycles dir.' (entier) ===")
print("=== P2/P3 : comparer moy|S| a sqrt(W) (annulation racine) et max|S| (resonances) ===")
print("\n=== ZOOM : le spectre des |S(j)| sur la cellule du -17 (7,4) ===")
res,a=cell_residues(7,4)
W=len(res); spec=[]
for j in range(1,a):
    spec.append((abs(sum(cmath.exp(2j*math.pi*j*r/a) for r in res)),j))
spec.sort(reverse=True)
print(f"  a={a}, W={W}, sqrt(W)={math.sqrt(W):.2f}")
print(f"  top 8 resonances (|S(j)|, j) : {[(round(m,1),j) for m,j in spec[:8]]}")
print(f"  |S| median = {sorted(m for m,_ in spec)[len(spec)//2]:.2f}")
print("\n=== LECTURE ===")
print("Le mur, en langage analytique : il faudrait |sum_{j!=0} S(j)| < a - W pour conclure 0 cycle.")
print("Avec annulation racine (|S|~sqrt(W)) la somme des a-1 termes vaut ~a*sqrt(W) >> a : INSUFFISANT.")
print("Il faudrait une annulation ENTRE les j (structure), pas seulement dans chaque S(j).")
