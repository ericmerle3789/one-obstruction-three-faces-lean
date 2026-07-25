#!/usr/bin/env python3
# REQ-MATH-039 — ARES : rendre le lemme de deficit FORMALISABLE (x rationnel au lieu de l'entropie)
# IDEE : C(m,k)*x^k <= (1+x)^m  pour tout x>0 (un seul terme du binome) — inegalite ENTIERE si x=p/q.
#   => log2 C <= m*log2(1+x) - k*log2 x  => margin(n) = K - log2 C >= K - m*log2(1+x) + k*log2 x
#   avec K = ceil(n*log2 3) = bit_length(3^n), m = K-2, k = n-1.
# BUT : trouver x = p/q RATIONNEL tel que margin_bound(n) >= c*n pour un c RATIONNEL, pour TOUT n.
# PREDICTIONS : P1 x* reel ~ 1.709 ; P2 x=12/7 donne c >= 1/13 ; P3 tient pour n>=n0 petit.
from mpmath import mp, mpf, log, binomial
mp.dps=40
L=log(3)/log(2)
def l2(x): return log(x)/log(2)
def K_of(n): return (3**n).bit_length()          # = ceil(n*log2 3), exact
print("=== CANARIS ===")
c1 = all(K_of(n)==int(mp.ceil(n*L)) for n in [1,2,3,5,7,12,53,100])
c2 = (K_of(5)==8 and 2**8-3**5==13)              # ancre connue
print(f"  K(n)=bit_length(3^n)=ceil(n log2 3) : {c1} | ancre n=5 -> K=8, q=13 : {c2}")
# canari binome : C(m,k) x^k <= (1+x)^m
from fractions import Fraction as F
import math as _m
c3=all(F(_m.comb(m,k))*F(12,7)**k <= F(19,7)**m for (m,k) in [(10,4),(20,8),(30,12)])
print(f"  borne binome C(m,k)x^k <= (1+x)^m (x=12/7) : {c3}")
if not(c1 and c2 and c3): print("CANARI FAIL"); raise SystemExit(1)
print("CANARIS: PASS\n")
c_gen = L - L*l2(L) + (L-1)*l2(L-1)
print(f"c_gen (cible ideale) = {mp.nstr(c_gen,10)}\n")
print("=== P1 : optimum reel de x pour k/m = 1/log2(3) ===")
r=1/L                     # k/m asymptotique
xopt=r/(1-r)
print(f"  k/m -> 1/log2 3 = {mp.nstr(r,8)} ; x* = r/(1-r) = {mp.nstr(xopt,8)}")
print("\n=== P2 : quelle constante c donne chaque x rationnel ? (asymptotique) ===")
print(f"  {'x = p/q':>10} {'c asympt.':>12} {'>= 1/13 ?':>10} {'perte vs c_gen':>15}")
best=None
for (p,q) in [(12,7),(17,10),(41,24),(70,41),(111,65),(5,3),(7,4),(19,11),(26,15),(1709,1000)]:
    x=mpf(p)/q
    # margin/n -> L - L*log2(1+x) + log2(x)   (m~K~nL, k~n)
    c = L - L*l2(1+x) + l2(x)
    if best is None or c>best[0]: best=(c,p,q)
    print(f"  {str(p)+'/'+str(q):>10} {mp.nstr(c,8):>12} {str(c>=mpf(1)/13):>10} {mp.nstr(c_gen-c,4):>15}")
print(f"\n  meilleur teste : x = {best[1]}/{best[2]} -> c = {mp.nstr(best[0],10)}")
print("\n=== P3 : l'inegalite margin_bound(n) >= c*n tient-elle pour TOUT n ? (x=12/7, c=1/13) ===")
x=mpf(12)/7; C=mpf(1)/13
worst=mpf('1e9'); nworst=0; fails=[]
for n in range(1,3001):
    K=K_of(n); m=K-2; k=n-1
    if m<1 or k<0: continue
    mb = K - m*l2(1+x) + k*l2(x)      # borne inferieure PROUVABLE de margin
    s = mb - C*n
    if s<worst: worst=s; nworst=n
    if s<0: fails.append(n)
print(f"  n=1..3000 : slack minimum = {mp.nstr(worst,8)} a n={nworst} | echecs : {len(fails)} {fails[:12]}")
print("\n=== P3bis : et avec le meilleur x rationnel teste ? ===")
x2=mpf(best[1])/best[2]
for Cc,lab in [(mpf(1)/13,"1/13"),(mpf(2)/25,"2/25"),(mpf(79)/1000,"79/1000")]:
    w=mpf('1e9'); nw=0; f=[]
    for n in range(1,3001):
        K=K_of(n); m=K-2; k=n-1
        if m<1 or k<0: continue
        s=(K - m*l2(1+x2) + k*l2(x2)) - Cc*n
        if s<w: w=s; nw=n
        if s<0: f.append(n)
    print(f"  c={lab:>8} : slack min = {mp.nstr(w,8):>12} a n={nw:>4} | echecs : {len(f)} {f[:8]}")
