#!/usr/bin/env python3
# test_REQ-MATH-032_ombre_reelle_ou_hasard.py — ARES (RED TEAM du tamis : structurel ou loterie ?)
# Une cellule "morte" (aucun mot avec v_l(R0)>=v_l(q)) est-elle une OMBRE STRUCTURELLE
# ou juste une petite cellule sans assez de tickets ?
# TEST : pour chaque (cellule, premier l|q, a=v_l(q)) : W mots, esperance de mots valides = W/l^a.
#   P(aucun | hasard) = exp(-W/l^a). Une mort avec esperance ELEVEE (>=5 mots attendus) et 0 observe
#   est une ANOMALIE STRUCTURELLE (proba < 1%) -> vraie ombre.
# PREDICTIONS : P1 la plupart des morts = petites cellules (hasard). P2 il EXISTE des anomalies
#   structurelles (esperance>=5, observe 0). P3 ces anomalies ont une cause d'ordre (ord_l(2)).
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
def ordm(a,l):
    x=a%l; k=1
    while x!=1:
        x=(x*a)%l; k+=1
        if k>l: return -1
    return k
PRIMES=[p for p in range(3,300) if all(p%d for d in range(2,int(p**.5)+1))]
print("=== CANARI : la cellule (6,14) q=15655 — 792 mots, 101|q, 7.8 attendus, 0 observe ? ===")
n,S=6,8; K=n+S; q=2**K-3**n
cnt=0; hits101=0
for p in range(1,min(n,S)+1):
    for ms in comps(n,p):
        for ss in comps(S,p):
            cnt+=1
            if R0(ms,ss)%101==0: hits101+=1
print(f"  q={q}, mots={cnt}, mots avec 101|R0 = {hits101} (attendu ~{cnt/101:.1f})")
print(f"  CANARI: {'ANOMALIE CONFIRMEE' if hits101==0 else 'pas anomalie'}")
print("\n=== BALAYAGE : morts par HASARD vs morts STRUCTURELLES (n<=11) ===")
NMAX=11
chance_sum=0.0; obs_dead=0; anomalies=[]
for n in range(2,NMAX+1):
    for S in range(1,2*n+1):
        K=n+S; qq=2**K-3**n; a=abs(qq)
        if a<=1: continue
        fl=[(l,vp(a,l)) for l in PRIMES if a%l==0]
        if not fl: continue
        W=math.comb(n+S-2,n-1)
        maxv={l:0 for l,_ in fl}; hits={l:0 for l,_ in fl}
        for p in range(1,min(n,S)+1):
            for ms in comps(n,p):
                for ss in comps(S,p):
                    r=R0(ms,ss)
                    for l,va in fl:
                        v=vp(r,l)
                        if v>maxv[l]: maxv[l]=v
                        if v>=va: hits[l]+=1
        died=False
        for l,va in fl:
            exp_hits=W/(l**va)
            if hits[l]==0:
                died=True
                if exp_hits>=5.0:
                    anomalies.append((n,K,qq,l,va,W,exp_hits,ordm(2,l),ordm(3,l)))
        pdie=1.0
        for l,va in fl: pdie*= (1-math.exp(-W/(l**va)))
        chance_sum += (1-pdie)
        obs_dead += died
print(f"  morts OBSERVEES : {obs_dead}")
print(f"  morts ATTENDUES par pur hasard : {chance_sum:.1f}")
print(f"  -> {'PAS d exces global (loterie)' if obs_dead<=chance_sum*1.3 else 'EXCES = structure'}")
print(f"\n=== ANOMALIES STRUCTURELLES (esperance>=5 mots, 0 observe) : {len(anomalies)} ===")
print(f"  {'n':>3} {'K':>3} {'q':>10} {'l':>5} {'v_l(q)':>6} {'W':>6} {'attendus':>9} {'ord_l(2)':>8} {'ord_l(3)':>8}")
for (n,K,qq,l,va,W,e,o2,o3) in anomalies[:20]:
    print(f"  {n:>3} {K:>3} {qq:>10} {l:>5} {va:>6} {W:>6} {e:>9.1f} {o2:>8} {o3:>8}")
if anomalies:
    print("\n  -> une ANOMALIE = un premier qui ne divise JAMAIS R0 dans sa cellule alors qu'il")
    print("     'devrait' : c'est une OMBRE STRUCTURELLE, un vrai mecanisme d'exclusion locale.")
else:
    print("  -> aucune anomalie : le tamis est de la pure loterie, pas d'ombre structurelle.")
