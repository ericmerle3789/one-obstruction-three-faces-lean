#!/usr/bin/env python3
# REQ-MATH-042 — ARES : verification EXACTE de la chaine d'assemblage atomes -> MarginTarget
# DERIVATION (a valider ici avant tout Lean) :
#  m=K-2, k=n-1, m-k=K-n-1 ; hyp : 3^n <= 2^K < 2*3^n, n>=1  => K>=n+1
#  (1) deficit^13 : C^13 * 12^(13k) * 7^(13(m-k)) <= 19^(13m)
#  (2) suffit : 19^(13m)*2^n <= 2^(13K)*12^(13k)*7^(13(m-k))
#  (3) ^15 + atom_A (19^195 <= 14^195*2^86, 14=2*7) => reste :
#      2^(86K)*2^(15n)*7^(195n)*12^195 <= 2^562*12^(195n)*7^195
#  (4) 2^K <= 2*3^n => 2^(86K) <= 2^86*3^(86n) ; regroupe en n :
#      (3^86*2^15*7^195)^n * 2^86*12^195 <= 2^562*7^195*(12^195)^n
#  (5) atom_a : (3^86*2^15*7^195) <= 12^195   =>  suffit : 2^86*12^195 <= 2^562*7^195  [atome C]
import math
print("=== ATOMES ===")
A = 19**195 <= 14**195 * 2**86
a = 3**86 * 2**15 * 7**195 <= 12**195
C = 2**86 * 12**195 <= 2**562 * 7**195
for nom,v,g,d in [("A: 19^195 <= 14^195*2^86",A,19**195,14**195*2**86),
                  ("a: 3^86*2^15*7^195 <= 12^195",a,3**86*2**15*7**195,12**195),
                  ("C: 2^86*12^195 <= 2^562*7^195",C,2**86*12**195,2**562*7**195)]:
    print(f"  {nom:>34} : {v}  (marge {math.log2(d/g):.3f} bits)")
if not(A and a and C): print("ATOME FAUX"); raise SystemExit(1)
print("\n=== CHAINE COMPLETE, etape par etape, sur n=1..300 ===")
def K_of(n): return (3**n).bit_length()
bad={}
for n in range(1,301):
    K=K_of(n); m=K-2; k=n-1
    if not (1<=n): continue
    if not (3**n <= 2**K < 2*3**n): bad.setdefault('hyp',[]).append(n); continue
    if K < n+1: bad.setdefault('K>=n+1',[]).append(n); continue
    if m<0 or k<0 or k>m: bad.setdefault('indices',[]).append(n); continue
    Cb=math.comb(m,k)
    # (1)
    if not (Cb**13 * 12**(13*k) * 7**(13*(m-k)) <= 19**(13*m)): bad.setdefault('etape1',[]).append(n)
    # (2)
    e2 = 19**(13*m)*2**n <= 2**(13*K)*12**(13*k)*7**(13*(m-k))
    if not e2: bad.setdefault('etape2',[]).append(n)
    # (3) forme reduite apres ^15 et atom_A
    e3 = 2**(86*K)*2**(15*n)*7**(195*n)*12**195 <= 2**562*12**(195*n)*7**195
    if not e3: bad.setdefault('etape3',[]).append(n)
    # (4)(5) implication finale
    e45 = (3**86*2**15*7**195)**n * 2**86*12**195 <= 2**562*7**195*(12**195)**n
    if not e45: bad.setdefault('etape45',[]).append(n)
    # CIBLE
    if not (Cb**13 * 2**n <= 2**(13*K)): bad.setdefault('CIBLE',[]).append(n)
print(f"  echecs par etape : { {k:(len(v),v[:5]) for k,v in bad.items()} if bad else 'AUCUN — chaine complete valide'}")
print("\n=== RED TEAM : (3) implique-t-il bien (2) ? test de l'implication elle-meme ===")
viol=0
for n in range(1,201):
    K=K_of(n); m=K-2; k=n-1
    if m<0 or k<0 or k>m: continue
    e3 = 2**(86*K)*2**(15*n)*7**(195*n)*12**195 <= 2**562*12**(195*n)*7**195
    e2 = 19**(13*m)*2**n <= 2**(13*K)*12**(13*k)*7**(13*(m-k))
    if e3 and not e2: viol+=1
print(f"  cas ou (3) vrai mais (2) faux : {viol}  (doit etre 0)")
