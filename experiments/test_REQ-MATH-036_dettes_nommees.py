#!/usr/bin/env python3
# test_REQ-MATH-036_dettes_nommees.py — ARES (les 2 dettes de L-A7 : plancher sud + inegalite de marge)
# DETTE 1 (notre) : le pas "meilleure cellule -> masse des DEUX rives" exige un plancher sud eps'_n.
#   CLAIM A VERIFIER : eps_n + eps'_n = 1 exactement (nord = ceil, sud = floor) => max >= 1/2 GRATUIT,
#   min couvert par la borne diophantienne (Rhin). Donc AUCUN ingredient nouveau requis.
# DETTE 2 (Ben l'ecrit) : margin(n) >= c_gen*n pour TOUT n. On (a) verifie exactement, (b) DE-RISQUE
#   sa preuve en testant si la borne d'ENTROPIE suffit : margin >= (n+S) - (n+S-2)*H((n-1)/(n+S-2)).
# PREDICTIONS : P1 eps+eps'=1 (exact) ; P2 min slack 2.84 a n=2 ; P3 la route entropie SUFFIT.
from mpmath import mp, mpf, floor, ceil, log, binomial
mp.dps=60
L=log(3)/log(2)
C_GEN=mpf('0.0793186')
import math
def H(x):
    if x<=0 or x>=1: return mpf(0)
    return -x*log(x)/log(2)-(1-x)*log(1-x)/log(2)
print("=== CANARIS ===")
# ancres connues
K5=int(ceil(5*L)); K7=int(ceil(7*L))
q5=2**K5-3**5; q7=2**K7-3**7
c1=(q5==13 and K5==8)
# margin a n=2 : K=4, S=2, demande=C(2,1)=2 -> margin=4-1=3
K2=int(ceil(2*L)); S2=K2-2; d2=binomial(2+S2-2,1); m2=K2-log(d2)/log(2)
c2=(K2==4 and abs(m2-3)<1e-9)
print(f"  ancre n=5 -> q={q5} (13), K=8 : {c1}")
print(f"  margin(2) = {float(m2):.4f} (attendu 3) : {c2}")
if not(c1 and c2): print("CANARI FAIL"); raise SystemExit(1)
print("CANARIS: PASS\n")

print("=== DETTE 1 : plancher SUD — eps + eps' = 1 ? ===")
worst=mpf(1); nworst=0; bad=0
print(f"  {'n':>6} {'eps (nord)':>12} {'eps prime (sud)':>16} {'somme':>8} {'max>=1/2':>9}")
for n in list(range(2,12))+[100,1000,10000,15601,190537]:
    x=n*L; eN=ceil(x)-x; eS=x-floor(x)
    s=eN+eS
    ok = abs(s-1)<mpf('1e-40') and max(eN,eS)>=mpf('0.5')
    if not ok: bad+=1
    mn=min(eN,eS)
    if mn<worst: worst=mn; nworst=n
    if n<12 or n in (15601,190537):
        print(f"  {n:>6} {float(eN):>12.6f} {float(eS):>16.6f} {float(s):>8.4f} {str(max(eN,eS)>=0.5):>9}")
print(f"  violations (somme != 1 ou max < 1/2) : {bad}")
print(f"  plus petit min(eps,eps') rencontre : {float(worst):.3e} a n={nworst}")
print("  => si 0 violation : le plancher SUD ne demande AUCUN ingredient neuf —")
print("     une rive est >= 1/2 gratuitement, l'autre est couverte par la meme borne diophantienne.")

print("\n=== DETTE 2a : margin(n) - c_gen*n >= 0 (exact, mpmath) ===")
mins=mpf('1e9'); nmin=0; neg=0
for n in range(2,3001):
    K=int(ceil(n*L)); S=K-n
    if S<1: continue
    d=binomial(n+S-2,n-1)
    margin=K-log(d)/log(2)
    slack=margin-C_GEN*n
    if slack<mins: mins=slack; nmin=n
    if slack<0: neg+=1
print(f"  n=2..3000 : slack minimum = {float(mins):.4f} a n={nmin} | violations (slack<0) : {neg}")

print("\n=== DETTE 2b : la route ENTROPIE suffit-elle ? (de-risque la preuve de Ben) ===")
print(f"  {'n':>6} {'margin exact':>13} {'borne entropie':>15} {'c_gen*n':>10} {'entropie suffit':>15}")
ok_all=True; worst_gap=mpf('1e9'); nw=0
for n in list(range(2,15))+[50,200,1000,3000]:
    K=int(ceil(n*L)); S=K-n
    if S<1: continue
    m=n+S-2; k=n-1
    margin=K-log(binomial(m,k))/log(2)
    ent = (n+S) - m*H(mpf(k)/m)          # borne inferieure de margin via C(m,k)<=2^{m H(k/m)}
    suff = ent >= C_GEN*n
    ok_all &= bool(suff)
    g=ent-C_GEN*n
    if g<worst_gap: worst_gap=g; nw=n
    if n<15 or n in (50,200,1000,3000):
        print(f"  {n:>6} {float(margin):>13.4f} {float(ent):>15.4f} {float(C_GEN*n):>10.4f} {str(bool(suff)):>15}")
# balayage complet
allok=True; wg=mpf('1e9'); nwg=0
for n in range(2,3001):
    K=int(ceil(n*L)); S=K-n
    if S<1: continue
    m=n+S-2; k=n-1
    ent=(n+S)-m*H(mpf(k)/m)
    g=ent-C_GEN*n
    if g<wg: wg=g; nwg=n
    if g<0: allok=False
print(f"\n  balayage n=2..3000 : la borne entropie domine c_gen*n partout ? {allok}")
print(f"  marge minimale de la route entropie : {float(wg):.4f} a n={nwg}")
print("\n=== LECTURE ===")
print("Si DETTE1 = 0 violation et DETTE2b = True partout : les deux dettes sont solubles,")
print("la 1re sans ingredient neuf, la 2e par un argument d entropie elementaire (route validee).")
