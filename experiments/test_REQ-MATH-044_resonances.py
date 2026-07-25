#!/usr/bin/env python3
# REQ-MATH-044 — ARES : caracterisation des RESONANCES des sommes exponentielles
# Contexte (REQ-034) : Nb cycles = (1/q)[W + sum_{j!=0} S(j)], S(j)=sum_mots e(j*R0/q).
#   |S(j)| se comporte comme du hasard EN MOYENNE (0.856 vs 0.886 gaussien) MAIS il existe
#   des RESONANCES (max/sqrt(W) jusqu'a 5.3), par paires conjuguees, a des j structures.
# HYPOTHESE : la structure vient de la multiplicativite — le paquet {R0 mod q} serait
#   (partiellement) invariant sous multiplication par des unites 3^a*2^-b, d'ou S(j)=S(j*u).
# PREDICTIONS : P1 |S(j)| ~ invariant sous j->2j ; P2 resonances = orbites d'un groupe ;
#   P3 canari : cellule -17 (n=7,S=4,q=139) resonances a j=2,4,12,53, |S|~13.7, mediane 8.14.
import math, cmath, itertools
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
def cell(n,S):
    a=abs(2**(n+S)-3**n); res=[]
    for p in range(1,min(n,S)+1):
        for ms in comps(n,p):
            for ss in comps(S,p): res.append(R0(ms,ss)%a)
    return res,a
def spectre(res,a):
    return [abs(sum(cmath.exp(2j*math.pi*j*r/a) for r in res)) for j in range(a)]

print("=== CANARI : cellule du -17 (n=7,S=4) ===")
res,a=cell(7,4); W=len(res); Sp=spectre(res,a)
med=sorted(Sp[1:])[len(Sp[1:])//2]
top=sorted([(Sp[j],j) for j in range(1,a)],reverse=True)[:8]
print(f"  a={a} (139), W={W} (84), mediane |S|={med:.2f} (8.14), max={top[0][0]:.1f} (13.7)")
print(f"  top j : {[j for _,j in top]}")
ok = a==139 and W==84 and abs(med-8.14)<0.3
print(f"  CANARI: {'PASS' if ok else 'FAIL'}")
if not ok: raise SystemExit(1)

print("\n=== P1 : |S(j)| est-il invariant sous j -> u*j pour u = 2, 3, 3/2 ? ===")
def corr(x,y):
    n=len(x); mx=sum(x)/n; my=sum(y)/n
    cov=sum((a1-mx)*(b1-my) for a1,b1 in zip(x,y))/n
    sx=(sum((a1-mx)**2 for a1 in x)/n)**.5; sy=(sum((b1-my)**2 for b1 in y)/n)**.5
    return cov/(sx*sy) if sx*sy>0 else 0
for (n,S) in [(7,4),(6,5),(8,5),(5,4)]:
    res,a=cell(n,S)
    if a<8 or a>4000: continue
    Sp=spectre(res,a)
    idx=[j for j in range(1,a)]
    out=[]
    for u,lab in [(2,"j->2j"),(3,"j->3j"),(pow(2,-1,a) if a%2 else 1,"j->j/2")]:
        try:
            c=corr([Sp[j] for j in idx],[Sp[(u*j)%a] for j in idx])
            # invariance exacte ?
            exact=all(abs(Sp[j]-Sp[(u*j)%a])<1e-6 for j in idx)
            out.append(f"{lab}: r={c:+.3f}{' EXACT' if exact else ''}")
        except Exception: pass
    # controle : permutation aleatoire
    import random; random.seed(1); perm=idx[:]; random.shuffle(perm)
    cr=corr([Sp[j] for j in idx],[Sp[p_] for p_ in perm])
    print(f"  (n={n},S={S}) a={a:>6} : " + " | ".join(out) + f" | ALEATOIRE r={cr:+.3f}")

print("\n=== P2 : les resonances forment-elles des orbites multiplicatives ? ===")
res,a=cell(7,4); Sp=spectre(res,a)
seuil=1.4*sorted(Sp[1:])[len(Sp[1:])//2]
reson=sorted([j for j in range(1,a) if Sp[j]>seuil])
print(f"  seuil = 1.4 x mediane = {seuil:.2f} | resonances : {reson}")
for u in (2,3,4,12):
    img=sorted({(u*j)%a for j in reson})
    inter=len(set(img)&set(reson))
    print(f"    stable sous j->{u}j ? {inter}/{len(reson)} restent resonants")
print("\n=== LECTURE ===")
print("Si une invariance EXACTE apparait (r=1.000 EXACT) : le paquet de residus a une")
print("symetrie multiplicative -> les S(j) se regroupent en orbites, et la somme sur j se")
print("decompose en (peu d'orbites structurees) + (reste generique). C'est la decomposition")
print("classique terme principal / terme d'erreur, et elle serait ACQUISE, pas supposee.")
