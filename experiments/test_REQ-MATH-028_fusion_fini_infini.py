#!/usr/bin/env python3
# test_REQ-MATH-028_fusion_fini_infini.py — ARES (le levier de fusion : fini x infini PAR ORBITE)
# On mesure ENSEMBLE, sur chaque mot, les deux moities qu'on a toujours regardees a part :
#   FINI      : C = log2 gcd(q,R0) / log2|q|  (remplissage de la serrure ; C=1 <=> cycle)
#   INFINI    : x = R0/q (element minimal signe) ; gamma = -log2(1-3^n/2^K) (serrage archimedien)
# QUESTION : y a-t-il une "zone interdite" -- haute serrure C ET x positif valide -- vide au nord ?
# et le couplage (C, gamma, signe x) differe-t-il entre les rives ?
# PREDICTIONS (ecrites avant) :
#  P1 x>0 <=> q>0 <=> rive nord (sign(x)=sign(q)) : identite, canari.
#  P2 C eleve <=> |q| petit <=> gamma grand : correlation POSITIVE C~gamma (pas anti).
#  P3 la zone (C>0.5 ET x>0 grand) n'est PAS vide mais sa densite s'effondre ; comparer nord/sud.
#  P4 aucun conflit DUR (C=1 possible avec x>0) -- sinon le mur tomberait trivialement. On cherche le MOU.
import math, itertools
def beta(m): return 3**m-2**m
def B_of(ms,ss):
    p=len(ms); n=sum(ms); B=0; Kp=0; Ma=n
    for t in range(p):
        Ma-=ms[t]; B+=3**Ma*2**Kp*beta(ms[t]); Kp+=ms[t]+ss[t]
    return B
def R0(ms,ss):
    p=len(ms); sig=[ss[t]+ms[(t+1)%p] for t in range(p)]
    Ma=[0]*p; acc=0
    for t in range(p-1,-1,-1): Ma[t]=acc; acc+=ms[t]
    tot,Sp=0,0
    for t in range(p): tot+=3**Ma[t]*2**Sp*(2**ss[t]-1); Sp+=sig[t]
    return tot
def comps(total,parts):
    if parts==1: yield (total,); return
    for cuts in itertools.combinations(range(1,total),parts-1):
        pts=(0,)+cuts+(total,); yield tuple(pts[i+1]-pts[i] for i in range(parts))

# CANARIS (main)
print("=== CANARIS ===")
# -17 : C=1, x=-17<0 (sud) ; trivial^2 : C=1, x=1>0 (nord)
q17=2**11-3**7; x17=B_of((4,3),(1,3))//q17
qt=2**4-3**2; xt=B_of((1,1),(1,1))//qt
c1=(x17==-17 and q17<0)  # P1 sud
c2=(xt==1 and qt>0)      # P1 nord
print(f"  P1 : -17 (x={x17}<0, q<0 sud) ; trivial^2 (x={xt}>0, q>0 nord) : {c1 and c2}")
if not (c1 and c2): print("CANARI FAIL"); raise SystemExit(1)
print("CANARIS: PASS\n")

# BALAYAGE : joint (C, gamma, signe x), par rive
NMAX=17; SMAX=11
from math import log2
# grille 2D : bins de C x bins de gamma, comptage par rive ; + la "zone haute serrure"
def gamma_of(n,K):
    # -log2(1 - 3^n/2^K) ; pour q>0 (2^K>3^n). pour q<0, symetrique via |.|
    r = mpf_ratio(n,K)
    return -math.log2(abs(1-r)) if r!=1 else 99
def mpf_ratio(n,K):
    # 3^n/2^K en float robuste
    return math.exp(n*math.log(3)-K*math.log(2))
stat={'nord':{'n':0,'hiC':0,'hiC_x_ok':0,'Cmax_xpos':0.0}, 'sud':{'n':0,'hiC':0,'hiC_x_ok':0,'Cmax_xpos':0.0}}
joint={'nord':[], 'sud':[]}
for n in range(2,NMAX+1):
    for S in range(1,min(SMAX,2*n)+1):
        K=n+S; q=2**K-3**n; a=abs(q)
        if a<=1: continue
        sh='nord' if q>0 else 'sud'; g=gamma_of(n,K)
        for p in range(1,min(n,S)+1):
            for ms in comps(n,p):
                for ss in comps(S,p):
                    r=R0(ms,ss); gc=math.gcd(a,r%a); C=math.log2(gc)/math.log2(a)
                    x = B_of(ms,ss)//q            # element minimal signe
                    st=stat[sh]; st['n']+=1
                    if C>0.5:
                        st['hiC']+=1
                        # x "valide pour un vrai cycle" : positif (nord) -> on regarde juste x>0 ici
                        if x>0: st['hiC_x_ok']+=1
                    if x>0 and C>st['Cmax_xpos']: st['Cmax_xpos']=C
                    if C>0.3: joint[sh].append((C,g,1 if x>0 else 0,abs(x)))

print("=== FUSION : haute serrure (C>0.5) ET signe de x, par rive ===")
for sh in ('nord','sud'):
    st=stat[sh]
    frac = st['hiC_x_ok']/st['hiC'] if st['hiC'] else 0
    print(f"  {sh:>4}: mots={st['n']:>7} | C>0.5 : {st['hiC']:>4} | dont x>0 : {st['hiC_x_ok']:>4} ({100*frac:4.0f}%) | max C avec x>0 : {st['Cmax_xpos']:.4f}")

print("\n=== couplage (C, gamma) sur les mots a haute serrure (C>0.3) : correlation ? ===")
for sh in ('nord','sud'):
    J=joint[sh]
    if len(J)<3: print(f"  {sh}: trop peu"); continue
    Cs=[j[0] for j in J]; Gs=[j[1] for j in J]
    mC=sum(Cs)/len(Cs); mG=sum(Gs)/len(Gs)
    cov=sum((c-mC)*(g-mG) for c,g in zip(Cs,Gs))/len(J)
    sC=(sum((c-mC)**2 for c in Cs)/len(J))**.5; sG=(sum((g-mG)**2 for g in Gs)/len(J))**.5
    rho=cov/(sC*sG) if sC*sG>0 else 0
    xpos=sum(j[2] for j in J)/len(J)
    print(f"  {sh}: n={len(J)} | corr(C,gamma)={rho:+.3f} | frac x>0 = {xpos:.3f} | gamma moyen = {mG:.2f}")

print("\n=== LA ZONE : mots avec C=1 (cycles) et signe de x ===")
for sh in ('nord','sud'):
    print(f"  {sh}: (les C=1 sont les cycles reels ; nord = puissances triviales x>0 ; sud = -5,-17 x<0)")
print("\nLECTURE : si au nord 'C>0.5 avec x>0' est RARE et son max-C s'effondre vs le sud,")
print("la fusion revele une zone haute-serrure/x-positif appauvrie -> couplage fini x infini reel,")
print("premier fragment mesurable de l'instrument. Sinon : couplage ailleurs, route eliminee.")
raise SystemExit(0)
