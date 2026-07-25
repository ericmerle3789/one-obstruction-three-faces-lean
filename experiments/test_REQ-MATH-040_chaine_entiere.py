#!/usr/bin/env python3
# REQ-MATH-040 — ARES/RED TEAM : la chaine PUREMENT ENTIERE ferme-t-elle ?
# Cible (equivalent entier de "margin(n) >= n/13") :   C(K-2,n-1)^13 * 2^n <= 2^(13K)
# Route Lean proposee (sans analyse reelle) :
#   (i)  binome  : C(m,k) * 12^k * 7^m <= 19^m * 7^k          [un terme du developpement]
#   (ii) donc    : C(m,k) <= 19^m * 7^k / (7^m * 12^k)
#   (iii) suffit : (19^m * 7^k)^13 * 2^n <= 2^(13K) * (7^m * 12^k)^13
# Si (iii) tient pour tout n, la preuve Lean = binome + une inegalite exponentielle entiere.
import math
def K_of(n): return (3**n).bit_length()
print("=== CANARIS ===")
c1=(K_of(5)==8 and 2**8-3**5==13)
c2=all(math.comb(m,k)*12**k*7**m <= 19**m*7**k for (m,k) in [(10,4),(25,10),(40,16),(7,3)])
print(f"  ancre n=5 : {c1} | (i) borne binome x=12/7 sur echantillon : {c2}")
if not(c1 and c2): print("CANARI FAIL"); raise SystemExit(1)
print("CANARIS: PASS\n")
print("=== (A) la CIBLE tient-elle ?  C^13 * 2^n <= 2^(13K) ===")
badA=[]; minmargA=None
for n in range(1,1201):
    K=K_of(n); m=K-2; k=n-1
    if m<0 or k<0 or k>m: continue
    C=math.comb(m,k)
    lhs=C**13 * 2**n; rhs=2**(13*K)
    if lhs>rhs: badA.append(n)
    r=(rhs.bit_length()-lhs.bit_length())
    if minmargA is None or r<minmargA[0]: minmargA=(r,n)
print(f"  n=1..1200 : echecs = {len(badA)} {badA[:10]} | marge min (bits) = {minmargA}")
print("\n=== (B) la ROUTE BINOME suffit-elle a l'etablir ? (iii) ===")
badB=[]; minmargB=None
for n in range(1,1201):
    K=K_of(n); m=K-2; k=n-1
    if m<0 or k<0 or k>m: continue
    lhs=(19**m * 7**k)**13 * 2**n
    rhs=2**(13*K) * (7**m * 12**k)**13
    if lhs>rhs: badB.append(n)
    r=(rhs.bit_length()-lhs.bit_length())
    if minmargB is None or r<minmargB[0]: minmargB=(r,n)
print(f"  n=1..1200 : echecs = {len(badB)} {badB[:10]} | marge min (bits) = {minmargB}")
print("\n=== (C) RED TEAM : petits n un par un (la ou ca casse d'habitude) ===")
print(f"  {'n':>3} {'K':>4} {'C=C(K-2,n-1)':>14} {'cible OK':>9} {'route OK':>9}")
for n in range(1,16):
    K=K_of(n); m=K-2; k=n-1
    if m<0 or k<0 or k>m:
        print(f"  {n:>3} {K:>4} {'(vide)':>14} {'-':>9} {'-':>9}"); continue
    C=math.comb(m,k)
    a = C**13*2**n <= 2**(13*K)
    b = (19**m*7**k)**13*2**n <= 2**(13*K)*(7**m*12**k)**13
    print(f"  {n:>3} {K:>4} {C:>14} {str(a):>9} {str(b):>9}")
print("\n=== VERDICT ===")
print("Si (A) et (B) sans echec : le lemme de deficit devient une inegalite ENTIERE,")
print("prouvable en Lean par (binome) + (inegalite exponentielle), SANS entropie ni Stirling.")
