#!/usr/bin/env python3
# test_REQ-MATH-020_pont_lean.py — ARES : pont deux-clefs entre l'objet Lean W0 et le R0 Python
# (1) W0(l) == 2^{m0} * R0(l)  (300 mots aleatoires, exact)
# (2) T1/T2 Lean (coordonnees W0, listes pre/suf arbitraires) re-verifies en Python (exact)
# (3) T2 en position 0 : REGULIER en W0 (le cas de bord est restaure), et la conclusion
#     de separation en termes de R0 suit (q impair => d|W0 <=> d|R0 pour chaque mot).
import math, random
random.seed(20260724)
def R0(m, s):
    p=len(m); sig=[s[t]+m[(t+1)%p] for t in range(p)]
    Ma=[0]*p; acc=0
    for t in range(p-1,-1,-1): Ma[t]=acc; acc+=m[t]
    tot,Sp=0,0
    for t in range(p): tot+=3**Ma[t]*2**Sp*(2**s[t]-1); Sp+=sig[t]
    return tot
def W0(l):
    if not l: return 0
    (m,s),rest=l[0],l[1:]
    return 3**sum(x[0] for x in rest)*2**m*(2**s-1)+2**(m+s)*W0(rest)
def rw(pmax=6):
    p=random.randint(1,pmax); return [(random.randint(1,9),random.randint(1,9)) for _ in range(p)]
# (1) pont
ok=all(W0(l)==2**l[0][0]*R0([x[0] for x in l],[x[1] for x in l]) for l in (rw() for _ in range(300)))
print(f"(1) W0 == 2^m0 * R0 : {ok} (300 mots)")
# (2) T1/T2 formes Lean
okT1=okT2=okT2z=True
for _ in range(300):
    pre,suf=rw(4),rw(4)
    m1,s1,m2,c,s2=(random.randint(1,9) for _ in range(5))
    d1=W0(pre+[(m1,s1+1),(m2,c)]+suf)-W0(pre+[(m1,s1),(m2,c+1)]+suf)
    okT1 &= (d1==2**sum(x[0]+x[1] for x in pre)*3**sum(x[0] for x in suf)*2**(m1+s1)*(3**m2-2**m2))
    d2=W0(pre+[(m1+1,s1),(m2,s2)]+suf)-W0(pre+[(m1,s1),(m2+1,s2)]+suf)
    okT2 &= (d2==-(2**sum(x[0]+x[1] for x in pre)*3**(m2+sum(x[0] for x in suf))*2**m1*(2**s1-1)))
    # position 0 (pre=[]) : regulier en W0
    d3=W0([(m1+1,s1),(m2,s2)]+suf)-W0([(m1,s1),(m2+1,s2)]+suf)
    okT2z &= (d3==-(3**(m2+sum(x[0] for x in suf))*2**m1*(2**s1-1)))
print(f"(2) T1 Lean exact : {okT1} | T2 Lean exact : {okT2} | (3) T2 position 0 regulier : {okT2z} (300 chacun)")
raise SystemExit(0 if (ok and okT1 and okT2 and okT2z) else 1)
