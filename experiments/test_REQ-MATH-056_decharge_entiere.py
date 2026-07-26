#!/usr/bin/env python3
# test_REQ-MATH-056_decharge_entiere.py — ARES
# ECRIT LE 2026-07-26, retroactivement : OUT_REQ-MATH-056.txt etait depose SANS son script
# (releve par Macindoe, audit round 10). Reproduit la sortie deposee.
#
# OBJET : rendre la DECHARGE des 22 reduites entierement ENTIERE, pour que Lean la tranche
# par calcul du noyau (decide) sans jamais evaluer un logarithme.
# Idee : au lieu de calculer theta_j = ||q_j * log2 3|| a vingt chiffres, utiliser la borne
# CLASSIQUE  theta_j > 1/(q_j + q_{j+1}).  La contrainte de couture "theta_j >= q_j * delta"
# avec delta = 2/(3*2^71*ln2) devient alors UNE INEGALITE ENTIERE :
#        2000 * q_j * (q_j + q_{j+1})  <=  2079 * 2^71
# (2079/4000 minorant rationnel prudent de 3*ln2/4). Si elle tient, la reduite ECHOUE.
#
# PREDICTIONS AVANT MESURE (= sortie deposee) :
#  P1 CANARI : 1/(q_j+q_{j+1}) < theta_j < 1/q_{j+1} pour j=1..14.
#  P2 22 reduites dans la fenetre entiere n <= 35031771147 ; TOUTES echouent.
#  P3 marge la plus serree 5.17x au convergent j=21 (q=6586818670).
#  P4 le critere ENTIER est CONSERVATIF : le test exact echoue de 5.443x, l'entier de 5.17x.
from mpmath import mp, mpf, log, floor
mp.dps = 60
Xi = 2**71
L = log(3)/log(2)

y = L; a = []
for _ in range(45):
    ai = int(floor(y)); a.append(ai); y = 1/(y-ai)
p0,q0,p1,q1 = 1,0,a[0],1; conv=[1]
for ai in a[1:]:
    p0,q0,p1,q1 = p1,q1,ai*p1+p0,ai*q1+q0; conv.append(q1)
def theta(q):
    t = mpf(q)*L
    return abs(t - mp.nint(t))

print("=== CANARI : borne classique 1/(q_j+q_{j+1}) < theta_j < 1/q_{j+1} ===")
canari = all(mpf(1)/(conv[j]+conv[j+1]) < theta(conv[j]) < mpf(1)/conv[j+1] for j in range(1,15))
print(f"  borne classique verifiee j=1..14 : {bool(canari)}")
if not canari: raise SystemExit(1)
print("CANARIS: PASS\n")

n_ent = 0; lo, hi = 0, 10**12
while lo <= hi:
    mid = (lo+hi)//2
    if 4000*mid*mid <= 2079*Xi: n_ent = mid; lo = mid+1
    else: hi = mid-1
print(f"=== fenetre entiere : n <= {n_ent} ===\n")

rhs = 2079*Xi
print(f"  {'j':>2} {'q_j':>14} {'q_(j+1)':>16} {'2000*q_j*(q_j+q_j1)':>24} {'2079*X':>26}  ECHOUE ?    marge")
dans = []; tightest = None
for j in range(len(conv)-1):
    q, qn = conv[j], conv[j+1]
    if q > n_ent: break
    lhs = 2000*q*(q+qn); ech = lhs <= rhs
    marge = mpf(rhs)/lhs
    dans.append((j,q,qn,ech,marge))
    if tightest is None or marge < tightest[1]: tightest = (j, marge, q)
    if j < 2 or j >= 15:
        print(f"  {j:>2} {q:>14} {qn:>16} {lhs:>24} {rhs:>26} {str(ech):>9} {mp.nstr(marge,6):>8}x")
tous = all(e for _,_,_,e,_ in dans)
print(f"\n  convergents dans la fenetre : {len(dans)} | TOUS echouent (critere entier) : {tous}")
print(f"  marge la plus serree : {mp.nstr(tightest[1],3)}x au convergent j={tightest[0]} (q={tightest[2]})")

print("\n=== P3 : le critere entier est-il conservatif (plus faible que l'exact) ? ===")
j = tightest[0]; q, qn = conv[j], conv[j+1]
delta = 2/(3*mpf(Xi)*log(2))
te = theta(q); bi = mpf(1)/(q+qn); besoin = q*delta
print(f"  j={j} : theta_exact={mp.nstr(te,6)} vs borne_inf=1/(q+q')={mp.nstr(bi,6)}")
print(f"        besoin q_j*delta={mp.nstr(besoin,6)} -> exact echoue de {mp.nstr(te/besoin,4)}x, "
      f"borne entiere de {mp.nstr(bi/besoin,3)}x")

print("\n=== CONCLUSION : T1 fermee dans la fenetre ===")
print("  Legendre (PROUVE) : n dans la fenetre => n = q_j (ou un MULTIPLE — cf. Macindoe r10 :")
print("                      si n = t*q_m alors |K-nL| = t*theta_m et n*delta = t*q_m*delta,")
print("                      le t se simplifie, donc les memes 22 tests tuent tous les multiples)")
print("  decharge (ce test) : les 22 q_j echouent tous, critere ENTIER, verifiable par decide")
print(f"  => aucun cycle positif avec x_min >= 2^71 et n <= {n_ent}")

ok = (len(dans)==22 and tous and tightest[0]==21 and abs(float(tightest[1])-5.17)<0.02)
print(f"\nVERDICT reproduction : {'CONFORME A LA SORTIE DEPOSEE' if ok else 'ECART'}")
raise SystemExit(0 if ok else 1)
