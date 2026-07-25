#!/usr/bin/env python3
# REQ-LOC-005 — ARES (LOCAL) : POURQUOI 3 ? La famille (y*x+1)/2^v comme tenaille.
# IMAGE (Eric) : la bille dans le lavabo — c'est la FORME du bassin qui ramene au trou.
# La "forme" = la pente moyenne de log2 x par pas impair = log2(y) - E[v] = log2(y) - 2.
# PREDICTIONS : P1 pente = log2 y - 2, negative ssi y<4 ; P2 y=5,7 -> cycles multiples/divergence ;
#   P3 y=3 est le SEUL impair strictement entre 1 et 4 -> unique cas marginal.
import math, random
random.seed(20260725)
def step(y,x):
    z=y*x+1; v=0
    while z%2==0: z//=2; v+=1
    return z,v
def orbit_class(y,x,lim=3000,cap=10**40):
    seen={}; t=0
    while t<lim:
        if x==1: return "->1",t
        if x in seen: return "CYCLE",t
        if x>cap: return "DIVERGE?",t
        seen[x]=t; x,_=step(y,x); t+=1
    return "long",t
print("=== CANARIS ===")
c1 = step(3,3)==(5,1) and step(3,1)==(1,2)
c2 = step(5,13)[0]==33   # 5*13+1=66 -> 33
print(f"  Collatz : step(3,3)=(5,1), step(3,1)=(1,2) : {c1} | 5x+1 : 13->33 : {c2}")
if not(c1 and c2): print("CANARI FAIL"); raise SystemExit(1)
print("CANARIS: PASS\n")
print("=== P1 : la PENTE du lavabo (derive de log2 x par pas impair) ===")
print(f"  {'y':>4} {'log2(y)-2 (theorie)':>21} {'mesure':>10} {'forme':>16}")
for y in (1,3,5,7,9,11):
    th=math.log2(y)-2
    d=[]
    for _ in range(30000):
        x=random.randrange(1<<20,1<<40)|1
        z,v=step(y,x); d.append(math.log2(z)-math.log2(x))
    m=sum(d)/len(d)
    forme = "LAVABO (rentre)" if th<0 else ("CRITIQUE" if abs(th)<1e-9 else "COLLINE (fuit)")
    print(f"  {y:>4} {th:>21.4f} {m:>10.4f} {forme:>16}")
print("\n  -> le basculement est a y = 4 (log2 4 = 2). Les impairs sous 4 : 1 et 3 SEULEMENT.")
print("\n=== P2 : que devient l'orbite selon y ? (300 graines) ===")
print(f"  {'y':>4} {'-> 1':>7} {'autre cycle':>12} {'diverge?':>10} {'pente':>8}")
for y in (1,3,5,7,9):
    from collections import Counter
    c=Counter()
    for _ in range(300):
        x=random.randrange(3,10**6)|1
        r,_t=orbit_class(y,x); c[r]+=1
    print(f"  {y:>4} {c.get('->1',0):>7} {c.get('CYCLE',0):>12} {c.get('DIVERGE?',0)+c.get('long',0):>10} {math.log2(y)-2:>8.3f}")
print("\n=== P3 : LE POINT — 3 est-il le seul cas marginal ? ===")
print(f"  y=1 : pente {math.log2(1)-2:+.3f} — descente FORCEE ((x+1)/2^v <= x), trivial")
print(f"  y=3 : pente {math.log2(3)-2:+.3f} — a peine negative : le bruit (sigma=1.414) l'ecrase")
print(f"        rapport signal/bruit = {abs(math.log2(3)-2)/math.sqrt(2):.4f}  <-- notre mu/sigma !")
print(f"  y=5 : pente {math.log2(5)-2:+.3f} — POSITIVE : la bille s'echappe")
print("\n  => 3 est le SEUL impair y avec 1 < y < 4. Le lavabo de Collatz est le")
print("     dernier lavabo avant la colline — et sa pente est 3 fois plus faible que sa rugosite.")
