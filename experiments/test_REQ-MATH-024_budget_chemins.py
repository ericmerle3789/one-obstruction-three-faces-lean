#!/usr/bin/env python3
# test_REQ-MATH-024_budget_chemins.py — ARES (point 1 d'Eric : le "budget de contenu" le long des chemins)
# QUESTION : la somme des micro-coutures peut-elle PORTER C vers 1 le long d'un chemin de transferts ?
# PREDICTIONS : (a) AUCUNE accumulation — C reste au fond puis SAUTE a l'arrivee sur un pic ;
#   au dernier pas avant le pic -17, C est borne par la mini-couture locale (<= log2(7)/log2(139)=0.394) ;
# (b) le pic -17 (primitif, C=1, rive sud) PROUVE qu'aucun plafond aveugle-au-signe n'existe :
#   la route "iterer T1/T2 seuls => C<1 primitif" est FERMEE ; la vraie route doit utiliser q>0.
import math, random
random.seed(20260724)
def R0(ms, ss):
    p=len(ms); sig=[ss[t]+ms[(t+1)%p] for t in range(p)]
    Ma=[0]*p; acc=0
    for t in range(p-1,-1,-1): Ma[t]=acc; acc+=ms[t]
    tot,Sp=0,0
    for t in range(p): tot+=3**Ma[t]*2**Sp*(2**ss[t]-1); Sp+=sig[t]
    return tot
def C_of(ms, ss, a):
    g=math.gcd(a, R0(ms,ss)%a)
    return math.log2(g)/math.log2(a)
def neighbors(ms, ss):
    out=[]
    p=len(ms)
    for i in range(p-1):
        if ss[i+1]>=2: s2=list(ss); s2[i]+=1; s2[i+1]-=1; out.append((list(ms),s2))
        if ss[i]>=2:   s2=list(ss); s2[i]-=1; s2[i+1]+=1; out.append((list(ms),s2))
        if ms[i+1]>=2: m2=list(ms); m2[i]+=1; m2[i+1]-=1; out.append((m2,list(ss)))
        if ms[i]>=2:   m2=list(ms); m2[i]-=1; m2[i+1]+=1; out.append((m2,list(ss)))
    return out
# CANARIS
w17=([4,3],[1,3]); a=139
assert C_of(*w17, a)==1.0
vs=neighbors(*w17)
c1=max(C_of(m,s,a) for m,s in vs)
print(f"CANARI : C(-17)=1 ; voisins immediats : max C = {c1:.4f} (borne couture attendue <= {math.log2(7)/math.log2(139):.4f})")
print(f"  nb voisins interieurs = {len(vs)} ; contenu PARTAGE avec le pic (lemme) : "
      f"{max(math.gcd(139, math.gcd(R0(*w17), R0(m,s))) for m,s in vs)} (attendu 1 : isolation totale)")
# MARCHES ALEATOIRES DEPUIS LE PIC : C par distance
print("\n=== C par distance au pic -17 (2000 marches aleatoires, pas 0..8) ===")
maxC=[0.0]*9; sumC=[0.0]*9; cnt=[0]*9
for _ in range(2000):
    cur=([4,3],[1,3])
    for d in range(9):
        c=C_of(cur[0],cur[1],a)
        maxC[d]=max(maxC[d],c); sumC[d]+=c; cnt[d]+=1
        nb=neighbors(*cur)
        if not nb: break
        cur=random.choice(nb)
print(f"{'dist':>5} {'C max':>8} {'C moyen':>8}")
for d in range(9):
    print(f"{d:>5} {maxC[d]:>8.4f} {sumC[d]/cnt[d]:>8.4f}")
print("\nLECTURE : si C max chute a ~0.39 des le pas 1 puis reste au fond (pas de remontee")
print("progressive), le contenu NE S'ACCUMULE PAS le long des chemins : arrivee = SAUT arithmetique.")
print("Combine au contre-exemple -17 (primitif C=1, rive sud) : la borne globale par iteration")
print("de T1/T2 seuls N'EXISTE PAS ; tout plafond vrai doit invoquer le signe/la taille (q>0).")
raise SystemExit(0)
