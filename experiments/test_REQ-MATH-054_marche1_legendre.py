#!/usr/bin/env python3
# REQ-MATH-054 — ARES : MARCHE 1 — fermer T1 dans la fenetre de Legendre.
# CHAINE : seam_bound (PROUVE)  q*3X < 2n*3^n   avec n = p+1
#   q = 2^K - 3^n = 3^n(2^eps - 1) >= 3^n * eps * ln2      [eps = K - n*log2 3 in (0,1)]
#   => eps < 2n/(3X ln2) = n*delta   avec delta = 2/(3X ln2)
#   LEGENDRE : |L - K/n| = eps/n < 1/(2n^2)  <=>  eps < 1/(2n)   => K/n EST un convergent
#   applicable si n*delta <= 1/(2n)  <=>  n <= sqrt(1/(2 delta))
#   PUIS : verification finie sur la liste (courte) des denominateurs de convergents.
import math
from mpmath import mp, mpf, log, floor
mp.dps=60
L=log(3)/log(2)
print("=== CANARIS ===")
# 2^e - 1 >= e ln2 pour e in (0,1)
c1=all(2**mpf(e)-1 >= mpf(e)*log(2) for e in [0.01,0.1,0.3,0.5,0.7,0.9,0.99])
# cycle trivial : n=1, K=2, eps = 2 - log2 3
eps_t=2-L
c2 = (0 < eps_t < 1)
print(f"  2^e-1 >= e*ln2 sur (0,1) : {c1} | trivial : eps = {float(eps_t):.4f} in (0,1) : {c2}")
if not(c1 and c2): print("CANARI FAIL"); raise SystemExit(1)
print("CANARIS: PASS\n")
X=mpf(2)**71
delta=2/(3*X*log(2))
print("=== P1/P2 : la constante et la fenetre ===")
print(f"  delta = 2/(3*2^71*ln2) = {mp.nstr(delta,6)}")
print(f"  (REQ-053 utilisait 1/(3 X ln2) = {mp.nstr(1/(3*X*log(2)),6)} — facteur 2 manquant, CORRIGE)")
W=mp.sqrt(1/(2*delta))
print(f"  fenetre de Legendre : n <= sqrt(1/(2 delta)) = {mp.nstr(W,8)}")
# convergents
y=L; a=[]
for _ in range(45):
    ai=int(floor(y)); a.append(ai); y=1/(y-ai)
p0,q0,p1,q1=1,0,a[0],1; conv=[(1,a[0])]
for ai in a[1:]:
    p0,q0,p1,q1=p1,q1,ai*p1+p0,ai*q1+q0
    conv.append((q1,p1))
print("\n=== P3 : verification finie sur TOUS les convergents de la fenetre ===")
print(f"  {'j':>3} {'q_j':>14} {'theta_j=|q_j L-p_j|':>21} {'q_j*delta':>14} {'theta>=q*delta ?':>17} {'-> pas de cycle':>16}")
allfail=True; nb=0
for j,(qj,pj) in enumerate(conv):
    if qj>W: break
    th=abs(qj*L-pj)
    bound=qj*delta
    fail = th>=bound     # contrainte VIOLEE => aucun cycle a cette echelle
    allfail &= bool(fail); nb+=1
    if j>=12 or j<3:
        print(f"  {j:>3} {qj:>14} {mp.nstr(th,6):>21} {mp.nstr(bound,6):>14} {str(bool(fail)):>17} {str(bool(fail)):>16}")
print(f"\n  convergents dans la fenetre : {nb} | TOUS echouent la contrainte : {allfail}")
print(f"\n=== CONCLUSION DE LA MARCHE 1 ===")
if allfail:
    print(f"  Pour X >= 2^71 : aucun cycle positif de longueur n <= {mp.nstr(W,6)}")
    print(f"  (dans la fenetre, Legendre force n = q_j ; les {nb} q_j possibles echouent tous)")
print(f"\n  a comparer : Hercher (papier) n > 1.375e11 ; le notre serait VERIFIE PAR MACHINE.")
print(f"  ratio : {float(mpf('1.375e11')/W):.2f}x")
