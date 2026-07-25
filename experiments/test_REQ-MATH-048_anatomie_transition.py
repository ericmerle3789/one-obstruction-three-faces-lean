#!/usr/bin/env python3
# REQ-MATH-048 — ARES : anatomie de la transition de phase a c = log2(3/2), cote INFINI
# V_c(x) = log2 x + c*v2(x+1). A c > log2(3/2) = 0.5849625, TOUS les pas v=1 decroissent.
# Que reste-t-il ? Ou echoue-t-on ? Une correction supplementaire peut-elle absorber ?
import math, random
random.seed(20260725)
L=math.log2(3.0); C0=L-1   # = log2(3/2) = 0.5849625
def T(x):
    y=3*x+1; v=(y&-y).bit_length()-1
    return y>>v, v
def v2(m): return (m&-m).bit_length()-1 if m else 0
print("=== CANARI : a c > log2(3/2), tout pas v=1 decroit-il ? ===")
c=C0+1e-6; bad=0; tot=0
for _ in range(50000):
    x=random.randrange(1<<30,1<<60)|1
    y,v=T(x)
    if v==1:
        tot+=1
        dV=(math.log2(y)-math.log2(x))+c*(v2(y+1)-v2(x+1))
        if dV>=0: bad+=1
print(f"  pas v=1 testes : {tot} | echecs : {bad}  -> {'CONFIRME' if bad==0 else 'ECHEC'}")
if bad: raise SystemExit(1)
print("CANARIS: PASS\n")
N=200000; S=[]
for _ in range(N):
    x=random.randrange(1<<30,1<<60)|1
    y,v=T(x); S.append((math.log2(y)-math.log2(x), v2(x+1), v2(y+1), v))
print("=== ANATOMIE des echecs restants (c = log2(3/2) + eps) ===")
f=[(a,b1,b2,v) for (a,b1,b2,v) in S if a+c*(b2-b1)>=0]
print(f"  taux d'echec : {100*len(f)/N:.2f}%")
from collections import Counter
print(f"  par v          : {dict(sorted(Counter(v for _,_,_,v in f).items())[:6])}")
print(f"  par saut v2    : {dict(sorted(Counter(b2-b1 for _,b1,b2,_ in f).items())[:6])}")
print(f"  -> les echecs sont les ENTREES de run (saut de v2 vers le haut)")
amp=sorted(a+c*(b2-b1) for (a,b1,b2,v) in f)
print(f"  amplitude : mediane={amp[len(amp)//2]:.3f}, 99e={amp[int(.99*len(amp))]:.3f}, max={amp[-1]:.3f}")
print("\n=== LE TEST DECISIF : le bilan sur un RUN COMPLET (entree + traversee) ===")
# un run = entrer sur x avec v2(x+1)=k, puis k-1 pas v=1 jusqu'a v2=1
print(f"  {'k':>3} {'entree dV':>10} {'traversee':>10} {'BILAN':>9} {'net<0 ?':>8}")
for k in range(2,9):
    # x = 2^k - 1 (mod 2^(k+1)) : v2(x+1)=k, run de longueur k-1
    x=(1<<k)-1
    dv_entry=c*(k-1)          # cout d'entree (v2 passe de 1 a k) approx
    dv_run=0.0; xx=x
    for _ in range(k-1):
        y,v=T(xx)
        dv_run+=(math.log2(y)-math.log2(xx))+c*(v2(y+1)-v2(xx+1))
        xx=y
    tot=dv_entry+dv_run
    print(f"  {k:>3} {dv_entry:>10.3f} {dv_run:>10.3f} {tot:>9.3f} {str(tot<0):>8}")
print("\n=== LECTURE ===")
print("Si le BILAN d'un run complet est POSITIF et croit avec k : la correction v2(x+1) deplace")
print("le probleme (elle paie la traversee mais surfacture l'entree) -> pas de Lyapunov par la.")
print("Si le bilan est negatif : la piste est vivante et merite une correction affinee.")
