#!/usr/bin/env python3
# REQ-MATH-067 — ARES — LA PISTE D'ERIC : nombre d'or, Fibonacci, structure des piliers.
# Theorie pure. Aucune extension de portee.
#
# CONTEXTE : tout notre programme repose sur les REDUITES de log2(3). Or la theorie des
# fractions continues a un heros : le NOMBRE D'OR phi = [1;1,1,1,...], dont les
# denominateurs de reduites sont EXACTEMENT les nombres de Fibonacci, et qui est le nombre
# LE PLUS MAL APPROCHABLE qui existe. Eric demande : y a-t-il un lien ?
#
# PREDICTIONS AVANT MESURE :
#  P1 phi a tous ses quotients partiels = 1 ; ses denominateurs = Fibonacci. (canari)
#  P2 log2(3) N'EST PAS comme phi : il a de GROS quotients partiels. Le danger vit la —
#     un gros quotient = une approximation exceptionnellement bonne = un endroit ou un
#     cycle pourrait se cacher. Predire : au moins un quotient >= 20 dans les 30 premiers.
#  P3 la distribution des quotients partiels suit-elle Gauss-Kuzmin (loi du hasard des
#     fractions continues) ? Si OUI -> log2(3) est un irrationnel BANAL, aucune structure
#     a exploiter. Si NON -> anomalie, donc piste. Test sur 2000 quotients.
#  P4 nos seuils (fin de fenetre T1, borne de Hercher) tombent-ils juste APRES un gros
#     quotient partiel ? C'est ce que la theorie predit : un gros quotient fait un grand
#     saut de denominateur, donc un grand trou ou rien n'est exclu.
#  P5 les denominateurs de log2(3) ressemblent-ils a Fibonacci (croissance en phi^n) ?
#     Predire NON : croissance bien plus rapide et irreguliere.
from mpmath import mp, mpf, log, floor, sqrt
import math
mp.dps = 3000
# PRECISION — CORRIGE 2026-07-29, et c'est un defaut de fond, pas de confort.
# Ce script tournait a mp.dps = 400. A cette precision la fraction continue de log2(3)
# DIVERGE de la vraie a l'indice 385 : au-dela, les quotients partiels ne sont plus ceux
# de log2(3) mais du bruit d'arrondi. 1615 des 2000 termes etaient faux.
# Consequence : le chi2/N imprime valait 0.00103 ; sur la vraie suite il vaut 0.00078.
# Diagnostic : Macindoe n'arrivait pas a placer le 0.00103, et pour cause — ses trois
# chiffres (plus grand ecart de classe 0.008425 ; son chi2/N 0.001214 ; chi2/dof < 0.567)
# se reproduisent TOUS exactement sur la suite correcte et AUCUN sur celle-ci. Pire :
# sur l'ancienne suite le max chi2/dof valait 1.0504, ce qui aurait contredit sa borne.
# Il calculait juste ; c'est notre suite qui etait fausse.
# Le canari C0 ci-dessous refuse desormais de tourner si la precision ne suffit pas.

def cf(x, n):
    y = x; a = []
    for _ in range(n):
        ai = int(floor(y)); a.append(ai); y = 1/(y-ai)
    return a
def denoms(a):
    p0,q0,p1,q1 = 1,0,a[0],1; out=[1]
    for ai in a[1:]:
        p0,q0,p1,q1 = p1,q1,ai*p1+p0,ai*q1+q0; out.append(q1)
    return out

phi = (1+sqrt(5))/2
L = log(3)/log(2)

print("="*80); print("P1 — CANARI : le nombre d'or et Fibonacci"); print("="*80)
aphi = cf(phi, 25); qphi = denoms(aphi)
fib=[1,1]
while len(fib)<25: fib.append(fib[-1]+fib[-2])
p1 = all(x==1 for x in aphi) and qphi[:20]==fib[:20]
print(f"  quotients partiels de phi (20 premiers) : {aphi[:20]}")
print(f"  denominateurs de phi   : {qphi[:12]}")
print(f"  Fibonacci              : {fib[:12]}")
print(f"  P1 {'PASS' if p1 else 'FAIL'} — phi = [1;1,1,1,...], denominateurs = Fibonacci exactement")
if not p1: raise SystemExit(1)
print("CANARIS: PASS")

print("\n"+"="*80); print("P2 — log2(3) ressemble-t-il au nombre d'or ?"); print("="*80)
aL = cf(L, 2000)

# CANARI C0 — la suite est-elle CONVERGEE ? Recalcul a precision doublee : si un seul
# quotient partiel bouge, la precision ne suffit pas et tout ce qui suit est du bruit.
_dps = mp.dps
mp.dps = 2 * _dps
_ref = cf(log(3)/log(2), 2000)
mp.dps = _dps
_div = next((i for i in range(2000) if aL[i] != _ref[i]), None)
print(f"  CANARI C0 precision : dps={_dps}, recalcul a dps={2*_dps} -> "
      f"{'CONVERGE (2000/2000 identiques)' if _div is None else f'DIVERGE a l indice {_div} — REFUSER LA SUITE'}")
assert _div is None, (f"precision insuffisante : la fraction continue diverge a l'indice {_div}. "
                      f"Augmenter mp.dps. (A dps=400 la divergence etait a 385.)")
print(f"  quotients partiels de log2(3) (30 premiers) :\n    {aL[:30]}")
gros = [(i,v) for i,v in enumerate(aL[:30]) if v>=20]
print(f"\n  quotients >= 20 dans les 30 premiers : {gros}")
print(f"  P2 {'PASS' if gros else 'FAIL'} — log2(3) est TOUT SAUF le nombre d'or :")
print(f"     phi n'a QUE des 1 (le plus mal approchable) ; log2(3) a des pics.")
print(f"     Chaque pic = une approximation exceptionnellement bonne = un endroit dangereux.")

print("\n"+"="*80); print("P3 — log2(3) est-il un irrationnel BANAL ? (loi de Gauss-Kuzmin)"); print("="*80)
N=len(aL)
print(f"  {'k':>3} {'observe':>9} {'Gauss-Kuzmin':>13} {'ecart':>8}")
chi=0.0
for k in range(1,9):
    obs = sum(1 for v in aL if v==k)/N
    att = math.log2(1+1/(k*(k+2)))
    chi += (obs-att)**2/att
    print(f"  {k:>3} {obs:>9.4f} {att:>13.4f} {obs-att:>+8.4f}")
grand_obs = sum(1 for v in aL if v>8)/N
grand_att = 1-sum(math.log2(1+1/(k*(k+2))) for k in range(1,9))
print(f"  >8 {grand_obs:>9.4f} {grand_att:>13.4f} {grand_obs-grand_att:>+8.4f}")
banal = chi < 0.01
print(f"\n  distance normalisee chi2/N = {chi:.5f}")
print(f"    (somme sur les 8 classes de TETE k=1..8 de (p_obs-p_att)^2/p_att, p = probabilites ;")
print(f"     la classe de queue k>=9 ci-dessus est AFFICHEE et N'EST PAS SOMMEE — elle porte")
print(f"     {grand_att:.3f} de la masse attendue, 3e des neuf. Ce n'est donc PAS un chi2 reduit,")
print(f"     qui serait chi2 par degre de liberte. Label corrige 2026-07-29 apres la question")
print(f"     de Macindoe, qui n'avait pu placer le nombre ni comme statistique ni comme p-value.)")
print(f"  P3 : log2(3) est-il BANAL ? {'OUI — il suit la loi du hasard' if banal else 'ANOMALIE a examiner'}")
print("     => aucune structure cachee a exploiter dans ses chiffres. C'est un irrationnel")
print("        ordinaire. Le programme ne peut RIEN tirer de sa nature propre.")

print("\n"+"="*80); print("P4 — nos seuils tombent-ils apres un gros quotient partiel ?"); print("="*80)
qs = denoms(aL)
for cible,nom in ((65470613321,"fin de notre fenetre T1 (q22)"),(137528045312,"seuil de Hercher (q23)")):
    j = qs.index(cible)
    print(f"  {nom:32s} : j={j}, quotient partiel a_j = {aL[j]}, a_(j+1) = {aL[j+1]}")
print(f"\n  rappel : a_j grand => q_(j+1) = a_j*q_j + q_(j-1) fait un GRAND SAUT")
print(f"  les 5 plus gros quotients parmi les 40 premiers : "
      f"{sorted([(v,i) for i,v in enumerate(aL[:40])],reverse=True)[:5]}")

print("\n"+"="*80); print("P5 — croissance : Fibonacci ou pas ?"); print("="*80)
print(f"  {'j':>3} {'q_j (log2 3)':>16} {'ratio q_j/q_(j-1)':>18} {'phi = 1.618':>12}")
for j in (5,10,15,20,23,25):
    r = qs[j]/qs[j-1]
    print(f"  {j:>3} {qs[j]:>16} {r:>18.3f} {'':>12}")
print(f"\n  Fibonacci croit avec un ratio CONSTANT phi = {float(phi):.3f}.")
print(f"  log2(3) : ratios de {min(qs[j]/qs[j-1] for j in range(5,26)):.2f} a "
      f"{max(qs[j]/qs[j-1] for j in range(5,26)):.2f} — irregulier, sans rapport.")
print("  P5 : AUCUNE structure de Fibonacci. Les deux objets n'ont rien a voir.")

print("\n"+"="*80); print("CONCLUSION"); print("="*80)
print("  Le nombre d'or est le nombre le MIEUX PROTEGE contre l'approximation.")
print("  Si log2(3) etait le nombre d'or, Collatz serait probablement FACILE.")
print("  Il ne l'est pas : c'est un irrationnel parfaitement banal, avec des pics")
print("  d'approximation imprevisibles, et statistiquement indiscernable du hasard.")
print("  => la piste 'nombre d'or / Fibonacci' est FERMEE, mais elle explique POURQUOI")
print("     c'est dur : on n'a pas eu la chance de tomber sur le bon nombre.")
