#!/usr/bin/env python3
# test_REQ-MATH-055_fenetre_entiere.py — ARES
# ECRIT LE 2026-07-26, retroactivement : OUT_REQ-MATH-055.txt etait depose SANS son script
# (releve par Macindoe, audit round 10). Reproduit la sortie deposee.
#
# OBJET : rendre la fenetre de Legendre ENTIERE, pour que Lean n'ait jamais a manipuler un
# logarithme. Fenetre exacte : n < sqrt(3*2^71*ln2/4). Fenetre entiere : 4000 n^2 <= 2079*2^71,
# ou 2079/4000 est un minorant rationnel PRUDENT de 3*ln2/4 (donc la fenetre entiere est
# strictement INTERIEURE a l'exacte : perte du bon cote).
#
# PREDICTIONS AVANT MESURE (= sortie deposee) :
#  P1 ln2 > 693/1000 (le minorant utilise par log_two_gt en Lean).
#  P2 fenetre exacte = 3.5035491e+10 ; fenetre entiere = 3.503177115e+10 ; perte 0.01062 %.
#  P3 la condition entiere bascule entre n = 35e9 (vrai) et n = 36e9 (faux).
#  P4 au seuil rond retenu 34_900_000_000 : 4000n^2 = 4872040000000000000000000,
#     2079*2^71 = 4908899958942996199636992, marge 1.0075656x.
#  P5 les 22 denominateurs de reduites sous ce seuil echouent tous au critere de couture.
from mpmath import mp, mpf, log, sqrt, floor
mp.dps = 50
X = mpf(2)**71
print("=== CANARI : ln2 > 693/1000 ? ===")
ln2 = log(2)
p1 = ln2 > mpf(693)/1000
print(f"  ln2 = {mp.nstr(ln2,10)} > 0.693 : {bool(p1)}")
if not p1: raise SystemExit(1)
print("CANARIS: PASS\n")

fen_exacte = sqrt(3*X*ln2/4)
Xi = 2**71
n_ent = 0
lo, hi = 0, 10**12
while lo <= hi:
    mid = (lo+hi)//2
    if 4000*mid*mid <= 2079*Xi: n_ent = mid; lo = mid+1
    else: hi = mid-1
perte = (1 - mpf(n_ent)/fen_exacte)*100
print(f"=== fenetre EXACTE : n < sqrt(3*2^71*ln2/4) = {mp.nstr(fen_exacte,8)}")
print(f"=== fenetre ENTIERE (4000 n^2 <= 2079*2^71) : n <= {mp.nstr(mpf(n_ent),10)}")
print(f"    perte vs exacte : {mp.nstr(perte,4)} %\n")

print("=== verification de la condition entiere a des seuils ronds ===")
for n in (10**10, 3*10**10, 34*10**9, 349*10**8, 35*10**9, 36*10**9):
    print(f"  n = {n:>14} : 4000n^2 <= 2079*2^71 ? {4000*n*n <= 2079*Xi}")

SEUIL = 34_900_000_000
print(f"\n=== SEUIL RETENU pour Lean : n <= {SEUIL:_} ===")
lhs = 4000*SEUIL*SEUIL; rhs = 2079*Xi
print(f"  4000*n^2      = {lhs}")
print(f"  2079*2^71     = {rhs}")
print(f"  condition OK  : {lhs <= rhs}  (marge {mp.nstr(mpf(rhs)/lhs,8)}x)")

# reduites de log2(3)
L = log(3)/log(2); y = L; a = []
for _ in range(40):
    ai = int(floor(y)); a.append(ai); y = 1/(y-ai)
p0,q0,p1_,q1 = 1,0,a[0],1; conv=[1]
for ai in a[1:]:
    p0,q0,p1_,q1 = p1_,q1,ai*p1_+p0,ai*q1+q0; conv.append(q1)
dans = [q for q in conv if q <= SEUIL]
tous_echouent = all(2000*q*(q + conv[conv.index(q)+1]) <= 2079*Xi for q in dans)
print(f"\n=== les 22 convergents restent-ils tous dans ce seuil et echouent-ils ? ===")
print(f"  convergents avec q_j <= {SEUIL} : {len(dans)} | tous echouent : {tous_echouent}")

ok = (len(dans)==22 and tous_echouent and lhs<=rhs and n_ent==35031771147)
print(f"\nVERDICT reproduction : {'CONFORME A LA SORTIE DEPOSEE' if ok else 'ECART'}")
raise SystemExit(0 if ok else 1)
