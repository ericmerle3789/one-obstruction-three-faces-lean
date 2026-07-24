#!/usr/bin/env python3
# test_REQ-MATH-027_exactitude_sud.py — ARES (levier #2 : le budget sud est-il RIGIDE ?)
# PREDICTIONS AVANT MESURE :
#  P1 (rigidite cellule) : FAUX. Il existe des cellules sud a tres petit |q| (frolement serre,
#     grosse esperance) SANS cycle, et le -17 gagne dans une cellule d'esperance modeste.
#     => l'exactitude n'est PAS "serrure serree => cycle" ; le gain est stochastique.
#  P2 (rigidite du STOCK) : le total des GRATUITS |q|=1 est EXACTEMENT 3 (Gersonides, deterministe,
#     prouve), reparti 1 nord / 2 sud. C'EST la seule exactitude rigide -> c'est la que le miroir mord.
#  P3 (le vrai etalon) : parmi les serrures PAYANTES (|q|>1), le sud n'en gagne qu'UNE (-17) sur
#     un budget ~1.1 ; test du modele : le rang de |q| du -17 dans sa cellule, et si un frolement
#     PLUS serre que 139 existe cote sud sans cycle (=> le gain n'est pas "le plus serre gagne").
import math, itertools
def beta(m): return 3**m-2**m
def B_of(ms,ss):
    p=len(ms); n=sum(ms); B=0; Kp=0; Ma=n
    for t in range(p):
        Ma-=ms[t]; B+=3**Ma*2**Kp*beta(ms[t]); Kp+=ms[t]+ss[t]
    return B
def comps(total,parts):
    if parts==1: yield (total,); return
    for cuts in itertools.combinations(range(1,total),parts-1):
        pts=(0,)+cuts+(total,); yield tuple(pts[i+1]-pts[i] for i in range(parts))
# CANARI
assert B_of((4,3),(1,3))==2363 and (2**11-3**7)==-139 and 2363%139==0
print("CANARI: -17 (q=-139, B=2363) OK\n")

NMAX=20; SMAX=13
gratuits={'nord':0,'sud':0}
# par cellule sud : |q|, budget (colliers/|q|), a-t-elle un cycle payant ?
sud_cells=[]; payantes=[]
for n in range(2,NMAX+1):
    for S in range(1,min(SMAX,2*n)+1):
        K=n+S; q=2**K-3**n; a=abs(q)
        if a==1:
            gratuits['nord' if q>0 else 'sud']+=1; continue
        if q>0: continue
        # cellule SUD payante
        cyc=0; nmots=0
        for p in range(1,min(n,S)+1):
            for ms in comps(n,p):
                for ss in comps(S,p):
                    nmots+=1
                    if B_of(ms,ss)%a==0: cyc+=1
        sud_cells.append((a, n, K, cyc, nmots))
        if cyc>0: payantes.append((a,n,K,cyc))

print("=== P1 : 'serrure la plus serree => cycle' ? (cellules sud, triees par |q| croissant) ===")
print(f"{'|q|':>9} {'(n,K)':>8} {'cycles':>7} {'#mots':>6}")
for a,n,K,cyc,nm in sorted(sud_cells)[:12]:
    flag = "  <-- GAGNE" if cyc>0 else ""
    print(f"{a:>9} {'('+str(n)+','+str(K)+')':>8} {cyc:>7} {nm:>6}{flag}")
serre_sans=[x for x in sorted(sud_cells) if x[3]==0 and x[0]<139]
print(f"  frolements sud PLUS serres que 139 SANS cycle : {len(serre_sans)}  ex: {[x[0] for x in serre_sans[:5]]}")
print(f"  => P1 {'CONFIRMEE (rigidite cellule FAUSSE : serrure serree n exige pas cycle)' if serre_sans else 'refutee'}")

print("\n=== P2 : le STOCK GRATUIT |q|=1 est-il rigide/exact ? ===")
print(f"  gratuits |q|=1 : nord={gratuits['nord']}, sud={gratuits['sud']}, total={gratuits['nord']+gratuits['sud']}")
print(f"  (Gersonides : exactement 3 paires harmoniques a distance 1 -> 2^K-3^n=+-1 ; DETERMINISTE)")

print("\n=== P3 : les serrures PAYANTES gagnantes (|q|>1) sur les 2 rives ===")
print(f"  cellules payantes SUD avec cycle : {[(a,n,K,c) for a,n,K,c in payantes]}")
print(f"  -> le sud ne gagne au payant que la cellule |q|=139 (le -17), rang {sorted([x[0] for x in sud_cells]).index(139)+1} par petitesse de |q|")

print("\n=== VERDICT (strategie) ===")
print("Si P1 confirmee + P2 exact : l'exactitude RIGIDE n'est PAS au niveau des serrures payantes")
print("(stochastiques) mais au niveau du STOCK GRATUIT (Gersonides, prouve, 3 exact). Donc le miroir")
print("ne se casse pas en rendant le payant rigide -- il se casse en prouvant que le nord n'a droit")
print("qu'a 1 gratuit (le +1) et que son unique budget payant reste sous 1. Le levier reel = coupler")
print("l'exactitude PROUVEE du stock (Gersonides+Catalan) a la petitesse PROUVEE du budget payant nord.")
raise SystemExit(0)
