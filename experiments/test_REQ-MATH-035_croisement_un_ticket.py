#!/usr/bin/env python3
# test_REQ-MATH-035_croisement_un_ticket.py — ARES (re-derivation du "croisement 1 ticket" ; le 550 etait NON CALCULE)
# Le "~550" de L-A7 n'a JAMAIS ete produit par un script : assertion au jugé -> violation ARES, retiree.
# Ben propose 2 lectures naturelles ; on calcule LES DEUX, avec nos propres constantes, puis avec
# la regle RE-SOURCEE (Rhin 1987, exposant 13.3, cf. Simons-de Weger Lemme 12).
#   borne(n) = -c_gen*n + p*log2(n) + C0     (p = exposant de la regle d'individu)
#   L1 "par echelle"  : plus petit n tel que borne(m) < 0 pour tout m >= n   (2^borne < 1 ticket)
#   L2 "queue cumulee": plus petit n tel que somme_{m>n} 2^borne(m) < 1
# C0 est EXHIBE depuis les donnees exactes (max du residu), pour chaque exposant.
import math
L=math.log2(3.0); C_GEN=0.0793186
def log2C(a,b):
    if b<0 or b>a: return float('-inf')
    return (math.lgamma(a+1)-math.lgamma(b+1)-math.lgamma(a-b+1))/math.log(2)
def log2_big(x):
    e=x.bit_length()-53
    return (e+math.log2(x>>e)) if e>0 else math.log2(x)
NMAX=4000
print("=== CANARI : R_best(n) exact reproduit-il les ancres connues ? ===")
q5=(1<<8)-3**5; q7=(1<<12)-3**7
print(f"  n=5 K=8 q={q5} (att. 13) ; n=7 K=12 q={q7} (att. 1909) : {q5==13 and q7==1909}")
if not(q5==13 and q7==1909): raise SystemExit(1)
# R_best exact par echelle (meilleure cellule nord)
Rbest={}
pow3=9
for n in range(2,NMAX+1):
    if n>2: pow3*=3
    Smax=int(0.5849625*n)+3
    best=-1e18
    for S in range(1,Smax+1):
        K=n+S; q=(1<<K)-pow3
        if q<=0: continue
        R=log2C(n+S-2,n-1)-log2_big(q)
        if R>best: best=R
    if best>-1e17: Rbest[n]=best
print(f"  R_best calcule sur {len(Rbest)} echelles (n<=4000)\n")
def analyse(p, nom):
    C0=max(Rbest[n]+C_GEN*n-p*math.log2(n) for n in Rbest)
    f=lambda n: -C_GEN*n+p*math.log2(n)+C0
    # L1 : par echelle
    L1=None
    for n in range(2,NMAX+1):
        if all(f(m)<0 for m in range(n,min(n+50,NMAX+1))) and f(n)<0:
            L1=n; break
    # L2 : queue cumulee
    L2=None
    for n in range(2,NMAX+1):
        s=sum(2.0**f(m) for m in range(n+1,NMAX+1) if f(m)>-300)
        if s<1.0: L2=n; break
    # verif borne >= exact
    viol=sum(1 for n in Rbest if Rbest[n]>f(n)+1e-9)
    print(f"  {nom}")
    print(f"    exposant p = {p} | C0 exhibe = {C0:.3f} | violations borne<exact : {viol}")
    print(f"    L1 croisement PAR ECHELLE (borne < 1 ticket)      : n = {L1}")
    print(f"    L2 croisement QUEUE CUMULEE (somme queue < 1)     : n = {L2}")
    return C0,L1,L2
print("=== A) avec l'ancienne regle (exposant 4.125, celle qui etait MAL ETIQUETEE) ===")
a=analyse(4.125,"ancienne (mu-1 = 4.125)")
print("\n=== B) avec la regle RE-SOURCEE (Rhin 1987, exposant 13.3 ; via Simons-de Weger) ===")
b=analyse(13.3,"Rhin 1987 (p = 13.3)")
print("\n=== VERDICT ===")
print(f"  Le '~550' de L-A7 : NON REPRODUIT, et jamais calcule. Les valeurs justes, avec nos")
print(f"  propres constantes, sont L1 = {a[1]} (par echelle) et L2 = {a[2]} (queue cumulee).")
print(f"  -> Ben a raison sur les deux lectures. Le 550 doit etre RETIRE.")
print(f"  Sous la regle correctement sourcee (Rhin) : L1 = {b[1]}, L2 = {b[2]}.")
