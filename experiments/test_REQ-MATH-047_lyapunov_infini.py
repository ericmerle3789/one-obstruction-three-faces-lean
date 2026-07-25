#!/usr/bin/env python3
# REQ-MATH-047 — ARES : cote INFINI (divergence). Une Lyapunov corrigee y garde-t-elle son gain,
# et ses echecs sont-ils STRUCTURES ?
# Contexte honnete : Terras/Everett/Korec/Tao ont deja "presque toutes les orbites descendent".
# Ce qui manque = l'ensemble exceptionnel. Une Lyapunov TOUJOURS decroissante le fermerait.
# V_c(x) = log2 x + c*v2(x+1)   [v2(x+1) gouverne les runs v=1, ou log2 x MONTE de 0.585]
# PREDICTIONS : P1 aucun c ne rend dV<0 toujours ; P2 un c* minimise le taux d'echec ;
#   P3 pas de telescopage cote infini -> le gain de variance est REEL.
import math, random
random.seed(20260725)
L=math.log2(3.0)
def T(x):
    y=3*x+1; v=(y&-y).bit_length()-1
    return y>>v, v
def v2(m): return (m&-m).bit_length()-1 if m else 0
print("=== CANARIS ===")
c1 = T(3)==(5,1) and v2(3+1)==2 and v2(5+1)==1
# structure des runs : x = 2^k - 1 doit donner v=1 et v2(x+1) = k -> k-1
x=2**8-1; y,v=T(x)
c2 = (v==1 and v2(x+1)==8 and v2(y+1)==7)
print(f"  T(3)=(5,1), v2 ok : {c1} | run : x=255 -> v=1, v2(x+1): 8 -> 7 : {c2}")
if not(c1 and c2): print("CANARI FAIL"); raise SystemExit(1)
print("CANARIS: PASS\n")
N=200000
samples=[]
for _ in range(N):
    x=random.randrange(1<<30,1<<60)|1
    y,v=T(x)
    samples.append((math.log2(y)-math.log2(x), v2(y+1)-v2(x+1), v))
print("=== P1/P2 : taux d'echec (dV >= 0) et mu/sigma selon c ===")
print(f"  {'c':>7} {'P(dV>=0)':>10} {'mu':>9} {'sigma':>9} {'mu/sigma':>10} {'gain vs log2':>13}")
base=None; best=None
for c in [0.0,0.3,0.5,0.585,0.7,0.9,1.2,1.585]:
    d=[a+c*b for (a,b,v) in samples]
    fail=sum(1 for z in d if z>=0)/N
    mu=-sum(d)/N; s=(sum((z+mu)**2 for z in d)/N)**.5
    r=mu/s
    if c==0.0: base=r
    if best is None or r>best[0]: best=(r,c,fail)
    print(f"  {c:>7.3f} {fail:>10.4f} {mu:>9.4f} {s:>9.4f} {r:>10.4f} {100*r/base:>12.0f}%")
print(f"\n  meilleur : c={best[1]} -> mu/sigma={best[0]:.4f}, taux d'echec={best[2]:.4f}")
print(f"  P1 : {'CONFIRMEE — aucun c ne supprime les echecs' if best[2]>0 else 'REFUTEE'}")
print("\n=== P3 : les echecs sont-ils STRUCTURES ? (a quoi ressemblent-ils ?) ===")
c=best[1]
fails=[(a,b,v) for (a,b,v) in samples if a+c*b>=0]
print(f"  nb echecs : {len(fails)}/{N} ({100*len(fails)/N:.1f}%)")
from collections import Counter
cv=Counter(v for (a,b,v) in fails); cb=Counter(b for (a,b,v) in fails)
print(f"  repartition par v      : {dict(sorted(cv.items())[:6])}")
print(f"  repartition par dv2    : {dict(sorted(cb.items())[:6])}")
allv=Counter(v for (a,b,v) in samples)
print(f"  (reference, tous v)    : {dict(sorted(allv.items())[:6])}")
print("\n=== P3bis : amplitude des echecs (bornee ou non ?) ===")
amp=sorted(a+c*b for (a,b,v) in fails)
print(f"  dV en echec : median={amp[len(amp)//2]:.3f}, max={amp[-1]:.3f}, 99e pct={amp[int(0.99*len(amp))]:.3f}")
print("\n=== LECTURE ===")
print("Si les echecs sont concentres sur v=1 (runs) ET d'amplitude bornee, une correction")
print("supplementaire pourrait les absorber. S'ils sont diffus et d'amplitude non bornee,")
print("aucune correction locale ne fermera l'ensemble exceptionnel.")
