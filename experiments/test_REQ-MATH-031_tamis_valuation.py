#!/usr/bin/env python3
# test_REQ-MATH-031_tamis_valuation.py — ARES (CARTOGRAPHIE DE L'OMBRE : le tamis de valuation)
# METHODE "trou noir" : on ne cherche pas le cycle, on derive ce qu'il EXIGE de son environnement.
# EXIGENCE FORCEE : q | R_0  <=>  pour CHAQUE premier l | q :  v_l(R_0) >= v_l(q).
# TEST : si  max_{mots de la cellule} v_l(R_0)  <  v_l(q)  pour un l | q,
#        alors AUCUN mot de la cellule ne peut etre un cycle -> CELLULE MORTE (deterministe, 0 proba).
# PREDICTIONS (avant machine) :
#  P1 [CANARI VITAL] les cellules des vrais cycles (2,4),(4,6),(7,11) NE sont PAS exclues.
#  P2 l'exclusion se produit pour certaines cellules (tamis non vide).
#  P3 l'exclusion frappe surtout quand l^a || q avec a>=2 (deficit de valuation).
import math, itertools
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
def vp(x,p):
    if x==0: return 99
    v=0
    while x%p==0: x//=p; v+=1
    return v
PRIMES=[p for p in range(3,200) if all(p%d for d in range(2,int(p**.5)+1))]

print("=== CANARIS ===")
# cellule (2,4) trivial : q=7, mot (1,1|1,1) R0=7 -> v_7=1 >= v_7(q)=1 : NON exclue
q=2**4-3**2; r=R0((1,1),(1,1))
c1=(q==7 and r==7 and vp(r,7)>=vp(q,7))
# cellule (7,11) : q=-139, mot (4,3|1,3) R0=139 -> non exclue
q2=2**11-3**7; r2=R0((4,3),(1,3))
c2=(q2==-139 and r2==139 and vp(r2,139)>=vp(abs(q2),139))
print(f"  (2,4) trivial non-exclue : {c1} | (7,11) -17 non-exclue : {c2}")
if not(c1 and c2): print("CANARI FAIL"); raise SystemExit(1)
print("CANARIS: PASS\n")

print("=== TAMIS : cellules mortes par deficit de valuation (n<=11, exhaustif) ===")
NMAX=11
dead=[]; alive=0; total=0; dead_by_a={}
for n in range(2,NMAX+1):
    for S in range(1,2*n+1):
        K=n+S; qq=2**K-3**n; a=abs(qq)
        if a<=1: continue
        total+=1
        # premiers de q parmi PRIMES
        fl=[(l,vp(a,l)) for l in PRIMES if a%l==0]
        if not fl: alive+=1; continue
        # max v_l(R0) sur tous les mots de la cellule
        maxv={l:0 for l,_ in fl}
        for p in range(1,min(n,S)+1):
            for ms in comps(n,p):
                for ss in comps(S,p):
                    r=R0(ms,ss)
                    for l,_ in fl:
                        v=vp(r,l)
                        if v>maxv[l]: maxv[l]=v
        killed=[(l,va,maxv[l]) for l,va in fl if maxv[l]<va]
        if killed:
            dead.append((n,K,qq,killed))
            for l,va,mv in killed: dead_by_a[va]=dead_by_a.get(va,0)+1
        else: alive+=1
print(f"  cellules testees : {total} | MORTES : {len(dead)} | vivantes : {alive}")
print(f"  exclusions par exposant v_l(q) : {dict(sorted(dead_by_a.items()))}")
print(f"\n  {'n':>3} {'K':>3} {'q':>12}  premiers tueurs (l, v_l(q), max v_l(R0))")
for n,K,qq,killed in dead[:14]:
    print(f"  {n:>3} {K:>3} {qq:>12}  {killed}")
print("\n=== P1 : les cellules des VRAIS cycles sont-elles epargnees ? ===")
real=[(2,4),(3,6),(4,6),(4,8),(6,9),(7,11),(8,12),(10,15)]
bad=[c for c in real if any((d[0],d[1])==c for d in dead)]
print(f"  cellules de cycles reels testees : {real}")
print(f"  parmi les MORTES : {bad if bad else 'AUCUNE (P1 CONFIRMEE — pas de contradiction)'}")
print("\n=== LECTURE ===")
print("Si des cellules meurent SANS toucher les vrais cycles : le tamis de valuation est un vrai")
print("mecanisme d'exclusion DETERMINISTE (l'ombre du trou noir). Reste a mesurer sa densite")
print("asymptotique : quelle fraction des cellules candidates tue-t-il quand n grandit ?")
