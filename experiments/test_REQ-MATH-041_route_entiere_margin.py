#!/usr/bin/env python3
# REQ-MATH-041 — ARES : la route ENTIERE vers MarginTarget tient-elle ? (avant tout Lean)
# Chaine visee (tout en entiers) :
#  (1) deficit : C(m,k)*12^k*7^(m-k) <= 19^m           [PROUVE en Lean deja]
#  (2) => suffit : 19^(13K)*2^n*7^(13n)*12^13*7^13 <= 14^(13K)*12^(13n)*19^26
#  (3) eleve a la puissance s, avec (A) 19^(13s) <= 14^(13s)*2^t  et  2^K < 2*3^n :
#      suffit : (a) 3^t*2^s*7^(13s) <= 12^(13s)     [facteur par n]
#               (b) 2^t*84^(13s)   <= 19^(26s)      [constante]
# FENETRE THEORIQUE : 13*log2(19/14) <= t/s <= 13*log2(12/7) - 1
import math
from fractions import Fraction as F
l2=lambda x: math.log2(x)
lo=13*l2(19/14); hi=(13*l2(12/7)-1)/l2(3)   # CORRIGE : diviser par log2(3)
print("=== FENETRE pour t/s ===")
print(f"  borne basse (borne 19/14) = {lo:.6f}")
print(f"  borne haute (facteur n)   = {hi:.6f}")
print(f"  fenetre non vide ? {lo<hi}  (largeur {hi-lo:.6f})")
if lo>=hi: print("ROUTE MORTE"); raise SystemExit(1)
print("\n=== recherche du plus petit s admissible ===")
found=None
for s in range(1,400):
    tmin=math.ceil(lo*s-1e-12); tmax=math.floor(hi*s+1e-12)
    if tmin<=tmax:
        found=(s,tmin); print(f"  s={s:>3} : t dans [{tmin},{tmax}] -> t={tmin} (t/s={tmin/s:.6f})")
        break
s,t=found
print(f"\n  RETENU : s={s}, t={t}")
print("\n=== VERIFICATION EXACTE des 3 inegalites (grands entiers) ===")
A = 19**(13*s) <= 14**(13*s) * 2**t
a = 3**t * 2**s * 7**(13*s) <= 12**(13*s)
b = 2**t * 84**(13*s) <= 19**(26*s)
for nom,val,g,d in [("(A) 19^(13s) <= 14^(13s)*2^t", A, 19**(13*s), 14**(13*s)*2**t),
                    ("(a) 3^t*2^s*7^(13s) <= 12^(13s)", a, 3**t*2**s*7**(13*s), 12**(13*s)),
                    ("(b) 2^t*84^(13s) <= 19^(26s)", b, 2**t*84**(13*s), 19**(26*s))]:
    marge = d/g
    print(f"  {nom:>34} : {val}   (ratio droite/gauche = {marge:.6f}, {math.log2(marge):.3f} bits)")
if not(A and a and b): print("\nUNE INEGALITE ECHOUE -> route a revoir"); raise SystemExit(1)
print("\n=== RED TEAM : la chaine complete redonne-t-elle MarginTarget ? (test direct) ===")
def K_of(n): return (3**n).bit_length()
bad=[]
for n in range(1,401):
    K=K_of(n); m=K-2; k=n-1
    if m<0 or k<0 or k>m: continue
    # cible
    C=math.comb(m,k)
    if not (C**13 * 2**n <= 2**(13*K)): bad.append(('cible',n))
    # etape (2) : la borne intermediaire implique-t-elle la cible ?
    if not (19**(13*K) * 2**n * 7**(13*n) * 12**13 * 7**13 <= 14**(13*K) * 12**(13*n) * 19**26):
        bad.append(('etape2',n))
print(f"  n=1..400 : echecs = {len(bad)} {bad[:8]}")
print("\n=== VERDICT ===")
print(f"Route VALIDE avec s={s}, t={t} : 3 controles grands-entiers + 2^K<2*3^n suffisent." if not bad
      else "ROUTE INCOMPLETE — voir echecs.")
