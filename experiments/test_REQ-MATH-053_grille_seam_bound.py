#!/usr/bin/env python3
# REQ-MATH-053 — ARES : T1 moitie GRILLE — le coeur quantitatif (seam bound) + meilleure approximation.
# Chaine : survivor_bound (PROUVE) + difference de puissances + two-bound (PROUVE)
#   => 2^K*3X < 3^(p+1)*(3X + 2(p+1))   i.e.  q*3X < 2(p+1)*3^(p+1)   [SEAM BOUND]
#   + meilleure approximation (n < q_{j+1} => ||nL|| >= theta_j)  => n force sur la grille.
# PREDICTIONS : P1 chaine sur trivial ; P2 best-approx exhaustive ; P3 borne ~6.5e10 vs Hercher 1.375e11.
import math
from mpmath import mp, mpf, log, floor
mp.dps=80
L=log(3)/log(2)
print("=== P1 : chaine entiere sur le cycle trivial (p+1=1 et double traversee p+1=2) ===")
# p+1=1 : X=1,K=2 : seam : 2^2*3 < 3^1*(3+2*1)=15 ? 12<15 ✓ ; q*3X=1*3 <= 2*1*3=6 ✓
c1 = (2**2*3 < 3**1*(3+2*1)) and ((2**2-3**1)*3 < 2*1*3**1)
# p+1=2 (double traversee, X=1, K=4, 2p<3X : 2<3 ✓) : 2^4*3 < 3^2*(3+4)=63 ? 48<63 ✓
c2 = (2**4*3 < 3**2*(3+2*2))
print(f"  p+1=1 : {c1} | p+1=2 : {c2}")
# difference de puissances : (b+1)^(n+1) <= b^(n+1) + (n+1)(b+1)^n  (aleatoire)
import random
random.seed(1)
c3=all((b+1)**(n+1) <= b**(n+1)+(n+1)*(b+1)**n for b in (1,3,10,100) for n in range(0,20))
print(f"  (b+1)^(n+1) <= b^(n+1)+(n+1)(b+1)^n : {c3}")
if not(c1 and c2 and c3): print("CANARI FAIL"); raise SystemExit(1)
print("CANARIS: PASS\n")
print("=== P2 : MEILLEURE APPROXIMATION, exhaustive jusqu'a n < q_13 = 190537 ===")
# convergents
y=L; a=[]
for _ in range(40):
    ai=int(floor(y)); a.append(ai); y=1/(y-ai)
p0,q0,p1,q1=1,0,a[0],1; qs=[1]; thetas=[abs(1*L-1)]
for ai in a[1:]:
    p0,q0,p1,q1=p1,q1,ai*p1+p0,ai*q1+q0
    qs.append(q1); thetas.append(abs(q1*L-p1))
def frac_dist(n):
    z=n*L; return float(min(z-floor(z), floor(z)+1-z))
# verifier : pour chaque j, min_{0<n<q_{j+1}} ||nL|| = theta_j atteint a q_j
ok=True
for j in range(2,14):
    qj,qj1=qs[j],qs[j+1]
    if qj1>200000: break
    m=min((frac_dist(n),n) for n in range(1,qj1))
    good = (m[1]==qj and abs(m[0]-float(thetas[j]))<1e-12)
    ok &= good
    print(f"  j={j} : min ||nL|| sur n<{qj1} = {m[0]:.3e} atteint a n={m[1]} (q_j={qj}) : {good}")
print(f"  BEST-APPROX : {'CONFIRMEE EXHAUSTIVEMENT' if ok else 'ECHEC'}")
print("\n=== P3 : LA BORNE DE LONGUEUR issue de NOTRE chaine (X0 = 2^71) ===")
X0=2**71
delta=2/(3*math.log(2)*X0)     # REQ-MATH-054 : facteur 2 (l'ancienne valeur 1/(3 X ln2)
                               # etait deux fois trop petite -> 1re echelle admissible surestimee)
print(f"  delta = {delta:.4e} ; condition d'existence d'une echelle n : ||nL|| <= n*delta")
print(f"  pour n < q_(j+1) : ||nL|| >= theta_j -> il faut theta_j <= n*delta, donc n >= theta_j/delta")
print(f"  {'j':>3} {'q_j':>16} {'theta_j':>13} {'theta_j/delta':>15} {'q_j admissible ?':>17}")
first=None
for j in range(6,26):
    if j>=len(qs): break
    qj=qs[j]; th=float(thetas[j])
    need=th/delta
    adm = qj>=need
    if adm and first is None: first=qj
    if qs[j]>10**13: break
    print(f"  {j:>3} {qj:>16} {th:>13.3e} {need:>15.3e} {str(adm):>17}")
if first is None:
    print("\n  => AUCUNE echelle admissible dans la plage balayee (etendre range(6,26))")
else:
    jj = qs.index(first)
    print(f"\n  => PREMIERE echelle admissible : n = q_{jj} = {first} ({first:.3e})")
    print(f"  Hercher (dedie, publie)       : n > 1.375e11 = q_23 (seuil sous-jacent)")
    print(f"  rapport : {1.375e11/first:.2f}x — notre chaine independante retrouve l'ordre de")
    print(f"  grandeur, une reduite en dessous. NOTE (Macindoe r10) : l'indexation ici est")
    print(f"  q_0 = q_1 = 1, tous deux comptes ; c'est celle des OUT-054/056.")
print("\n=== LECTURE ===")
print("Le seam bound (noyau) + best-approx (exhaustif ici, standard en theorie des nombres)")
print("forcent : (i) n sur la grille d'Ostrowski ; (ii) n > ~6.5e10 pour tout cycle avec")
print("x_min >= 2^71. La moitie grille de T1 est LANCEE : coeur quantitatif prouvable au noyau,")
print("marche best-approx a formaliser (standard mais non triviale en Lean).")
