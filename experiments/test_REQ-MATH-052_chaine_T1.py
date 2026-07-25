#!/usr/bin/env python3
# REQ-MATH-052 — ARES : LA CHAINE T1 (structure des survivants), verification machine AVANT Lean.
# (a) IDENTITE PRODUIT : autour d'un cycle, Prod(3x_i+1) = 2^K * Prod(x_i)   [algebre pure]
# (b) BORNE ENTIERE   : si tous x_i >= X : 2^K*(3X)^p <= 3^p*(3X+1)^p       [par facteur]
# (c) CEILING (no-hair, moitie 1) : si de plus 2p < 3X : 3^p < 2^K < 2*3^p  [K force = ceil(p log2 3)]
# (d) GRILLE (no-hair, moitie 2) : eps_n < n/(3 ln2 X0) => n sur la grille d'Ostrowski (script-level)
import math
L=math.log2(3.0)
def cycle_of(x0):
    xs=[x0]; vs=[]
    x=x0
    for _ in range(100):
        y=3*x+1; v=0
        while y%2==0: y//=2; v+=1
        vs.append(v)
        if y==x0: return xs,vs
        xs.append(y); x=y
    return None,None
print("=== (a) IDENTITE PRODUIT sur les 4 cycles reels ===")
ok=True
for x0 in (1,-1,-5,-17):
    xs,vs=cycle_of(x0)
    P1=1; P2=1
    for x in xs: P1*=(3*x+1); P2*=x
    K=sum(vs)
    ident = (P1 == 2**K * P2)
    ok &= ident
    print(f"  cycle {x0:>4} : p={len(xs)}, K={K} | Prod(3x+1)={P1}, 2^K*Prod(x)={2**K*P2} : {ident}")
if not ok: print("CANARI FAIL"); raise SystemExit(1)
print("CANARIS (a): PASS\n")
print("=== (b)(c) BORNE + CEILING sur le cycle trivial (seul cycle positif) ===")
xs,vs=cycle_of(1); p=len(xs); K=sum(vs); X=min(xs)
b = 2**K*(3*X)**p <= 3**p*(3*X+1)**p
c = (3**p < 2**K < 2*3**p) and (2*p < 3*X)
print(f"  trivial : borne {b} | 2p<3X : {2*p<3*X} | ceiling 3<4<6 : {3**p<2**K<2*3**p}")
print("=== (c-bis) sanity : les cycles NEGATIFS violent la condition q>0 (hors-champ, attendu) ===")
for x0 in (-1,-5,-17):
    xs,vs=cycle_of(x0); p=len(xs); K=sum(vs)
    print(f"  cycle {x0:>4} : 3^p={3**p} vs 2^K={2**K} -> q>0 ? {2**K>3**p}  (attendu False)")
print("\n=== (b)(c) sur des PSEUDO-cycles (mots du recensement, x=B/q rationnel) : ceiling force ? ===")
# tout mot ACCORDE (q>0) avec x_min>2p/3 doit avoir K = ceil(n log2 3) : verification par cellules
def K0(n): return (3**n).bit_length()
viol=0; tot=0
for n in range(2,40):
    for K in range(n+1, int(n*L)+4):
        q=2**K-3**n
        if q<=0: continue
        tot+=1
        # la chaine predit : un cycle a cette cellule avec X >= (2n+1)/3 exige K=K0(n)
        if K!=K0(n):
            # alors X < (2n+1)/3 force : la borne (b) doit etre VIOLEE pour X=n (test)
            X=n
            if 2**K*(3*X)**n <= 3**n*(3*X+1)**n: viol+=1
print(f"  cellules q>0 testees : {tot} | cas ou K != K0 mais la borne accepterait X=n : {viol}  (attendu 0)")
print("\n=== (d) LA GRILLE : fenetre de Legendre et structure d'Ostrowski ===")
X0=2**71
delta=1/(3*math.log(2)*X0)
W=math.sqrt(1/(2*delta))
print(f"  delta = 1/(3 ln2 X0) = {delta:.3e} | fenetre Legendre n < sqrt(1/(2 delta)) = {W:.3e}")
print(f"  (P4 : ~5e10 ; Hercher exige n > 1.375e11 -> au-dela, regime Ostrowski)")
# denominateurs des convergents
def convergents(NN):
    from mpmath import mp, mpf, floor, log
    mp.dps=80
    y=log(3)/log(2); a=[]
    for _ in range(40):
        ai=int(floor(y)); a.append(ai); y=1/(y-ai)
    p0,q0,p1,q1=1,0,a[0],1; ds=[1]
    for ai in a[1:]:
        p0,q0,p1,q1=p1,q1,ai*p1+p0,ai*q1+q0; ds.append(q1)
        if q1>NN: break
    return ds
ds=convergents(10**13)
print(f"  denominateurs : {ds}")
# les n a tres petit eps sont-ils des COMBINAISONS des grands q_j ? (test sur petite echelle)
seuil=1e-4
hits=[n for n in range(1,200000) if (math.ceil(n*L)-n*L)<seuil]
def near_grid(n,ds):
    for d in ds:
        if d>=10 and abs(n - round(n/d)*d)<=2 and round(n/d)>0: return d
    return None
gr=[(n,near_grid(n,ds)) for n in hits[:12]]
print(f"  n avec eps<{seuil} (12 premiers) et leur ancre de grille : {gr}")
print(f"  tous ancres sur la grille ? {all(g for _,g in gr)}")
