# run_120.py -- LE MUR DANS LE NOIR : le zero est-il special ?
# provenance : demande d'Eric "creuse ce mur derriere, dans le noir"
#
# ---------------------------------------------------------------------------
# LA QUESTION, JAMAIS POSEE DANS LE CORPUS
# ---------------------------------------------------------------------------
# Tout le corpus veut prouver N0(d) = 0 : corrsum n'atteint jamais le residu 0.
# Personne n'a verifie la chose elementaire : *** 0 est-il different des autres ? ***
# Si le compte a 0 est dans le lot commun, il n'y a pas de mur : il y a de la chance.
#
# ET UNE SECONDE QUESTION : corrsum vit dans un INTERVALLE [A,B], pas dans Z/dZ.
# Le nombre de multiples de d reellement ATTEIGNABLES est (B-A)/d. S'il est
# minuscule, la contrainte n'est pas de nature "residu" mais de nature "portee".
#
# PREDICTIONS ECRITES AVANT MESURE
#  P1 le compte a 0 est indiscernable des autres residus (pas de mur).
#  P2 la loi des comptes suit Poisson(C/d).
#  P3 le nombre de multiples atteignables est GRAND (donc la portee ne contraint pas).
# ---------------------------------------------------------------------------
from math import comb, ceil, log2, exp, factorial
from itertools import combinations
from collections import Counter
def comps(S,k):
    for cut in combinations(range(1,S),k-1):
        b=(0,)+cut+(S,); yield tuple(b[i+1]-b[i] for i in range(k))
def corrsum(g):
    k=len(g); s=0; suf=0
    for j in range(k-1,-1,-1):
        s += 3**(k-1-j) * 2**suf; suf += g[j]
    return s
assert corrsum((2,))==1                      # canari : cycle trivial
assert corrsum((3,1))==7                     # main : 3^1*2^1 + 3^0*2^0 = 6+1 = 7
print("canaris OK : corrsum((2,))=1, corrsum((3,1))=7\n")

print("="*80)
print("P1 -- LE ZERO EST-IL SPECIAL ? comparaison du residu 0 aux autres")
print("="*80)
print(f"{'k':>3} {'d':>9} {'C':>8} {'C/d':>7} {'N0':>4} {'max sur':>8} {'residus':>8} "
      f"{'rang de 0':>22}")
for k in range(4,17):
    S=ceil(k*log2(3)); d=(1<<S)-3**k; C=comb(S-1,k-1)
    if C>3_000_000 or d<=0: continue
    h=Counter(corrsum(g)%d for g in comps(S,k))
    n0=h.get(0,0); mx=max(h.values())
    # combien de residus font STRICTEMENT mieux que 0 ?
    mieux=sum(1 for v in h.values() if v>n0)
    # et combien de residus ont exactement le compte de 0 ?
    egaux=sum(1 for v in h.values() if v==n0) + (d-len(h) if n0==0 else 0)
    print(f"{k:>3} {d:>9} {C:>8} {C/d:>7.3f} {n0:>4} {mx:>8} {len(h):>8} "
          f"{f'{mieux} font mieux, {egaux} a egalite':>22}")

print()
print("="*80)
print("P2 -- LA LOI DES COMPTES EST-ELLE CELLE DU HASARD ? (Poisson)")
print("="*80)
for k in (12,14,15):
    S=ceil(k*log2(3)); d=(1<<S)-3**k; C=comb(S-1,k-1); lam=C/d
    h=Counter(corrsum(g)%d for g in comps(S,k))
    cnt=Counter(h.values()); cnt[0]=d-len(h)
    print(f"\n  k={k}  d={d}  C={C}  lambda=C/d={lam:.4f}")
    print(f"    {'compte':>7} {'residus observes':>18} {'Poisson predit':>16} {'ecart':>9}")
    for m in range(0,6):
        obs=cnt.get(m,0); pred=d*exp(-lam)*lam**m/factorial(m)
        print(f"    {m:>7} {obs:>18} {pred:>16.1f} {100*(obs-pred)/pred if pred>0.5 else 0:>8.1f}%")

print()
print("="*80)
print("P3 -- LA PORTEE : combien de multiples de d sont ATTEIGNABLES ?")
print("="*80)
print("  corrsum vit dans [A,B], pas dans Z/dZ tout entier.")
print(f"\n{'k':>3} {'A = min':>12} {'B = max':>16} {'d':>10} {'multiples de d dans [A,B]':>26}")
for k in range(4,17):
    S=ceil(k*log2(3)); d=(1<<S)-3**k; C=comb(S-1,k-1)
    if C>3_000_000 or d<=0: continue
    vals=[corrsum(g) for g in comps(S,k)]
    A,B=min(vals),max(vals)
    m=B//d - (A-1)//d
    print(f"{k:>3} {A:>12} {B:>16} {d:>10} {m:>26}")
