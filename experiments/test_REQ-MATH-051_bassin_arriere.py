#!/usr/bin/env python3
# REQ-LOC-004 — ARES (LOCAL) : LE BASSIN DE 4->2->1, ETUDIE PAR L'ARRIERE.
# Question retournee (Eric) : au lieu de chercher ce qui est INTERDIT (les cycles), etudier ce qui
# ATTIRE — l'arbre des ancetres de 1. Collatz <=> cet arbre contient TOUS les entiers.
# Carte de Syracuse (impairs) : x -> (3x+1)/2^v.  Ancetres de x : y=(2^v x -1)/3 quand entier.
# FAIT CLE a verifier : x ≡ 0 mod 3 n'a AUCUN ancetre (feuille) — c'est la non-surjectivite.
# PREDICTIONS : P1 couverture substantielle ; P2 exposant de croissance (ref. Krasikov-Lagarias 0.84) ;
#   P3 les NON-atteints a profondeur d sont-ils structures ?
import math
from collections import deque
def preds(x, vmax=40):
    out=[]
    for v in range(1,vmax):
        num=(1<<v)*x-1
        if num%3==0:
            y=num//3
            if y%2==1 and y>1: out.append(y)
    return out
print("=== CANARIS ===")
p1=sorted(preds(1))[:5]
print(f"  ancetres de 1 : {p1}  (attendu 5, 21, 85, 341, 1365)")
c1 = p1[:5]==[5,21,85,341,1365]
c2 = all(len(preds(x))==0 for x in (3,9,15,21*3,27))
print(f"  multiples de 3 sans ancetre : {c2}")
if not(c1 and c2): print("CANARI FAIL"); raise SystemExit(1)
print("CANARIS: PASS\n")
print("=== COUVERTURE de l'arbre des ancetres de 1, par profondeur ===")
N=200001
odds=(N-1)//2
seen={1}; frontier=[1]; depth=0
print(f"  {'profondeur':>11} {'nouveaux':>10} {'total <= N':>11} {'couverture':>11}")
while frontier and depth<40:
    depth+=1
    nf=[]
    for x in frontier:
        for y in preds(x):
            if y<N and y not in seen:
                seen.add(y); nf.append(y)
    frontier=nf
    cov=len(seen)/odds
    if depth<=12 or depth%5==0:
        print(f"  {depth:>11} {len(nf):>10} {len(seen):>11} {100*cov:>10.2f}%")
    if not nf: break
cov=len(seen)/odds
print(f"\n  couverture finale (impairs < {N}) : {len(seen)}/{odds} = {100*cov:.2f}%")
print(f"  exposant apparent : |arbre| ~ N^a avec a = {math.log(len(seen))/math.log(N):.4f}  (K-L : 0.84)")
print("\n=== P3 : les NON-ATTEINTS sont-ils structures ? ===")
miss=[x for x in range(3,N,2) if x not in seen]
print(f"  non atteints : {len(miss)} ({100*len(miss)/odds:.2f}%)  premiers : {miss[:12]}")
from collections import Counter
print(f"  repartition mod 3 : {dict(Counter(x%3 for x in miss))}")
print(f"  (reference, tous impairs mod 3) : {dict(Counter(x%3 for x in range(3,N,2)))}")
print(f"  repartition mod 8 : {dict(sorted(Counter(x%8 for x in miss).items()))}")
print("\n  -> tous ces non-atteints atteignent-ils 1 en AVANT ? (test direct)")
def reaches1(x,lim=100000):
    for _ in range(lim):
        if x==1: return True
        x=3*x+1
        while x%2==0: x//=2
    return False
bad=[x for x in miss[:400] if not reaches1(x)]
print(f"  sur 400 non-atteints testes : {len(bad)} n'atteignent PAS 1  -> {'tous atteignent 1' if not bad else bad[:5]}")
print("\n=== LECTURE ===")
print("Si les non-atteints atteignent tous 1 en avant, l'arbre est incomplet seulement par")
print("PROFONDEUR (on n'a pas assez remonte), pas par nature. Le bassin serait alors 'tout',")
print("et la question devient : pourquoi la remontee ne rate-t-elle jamais personne ?")
