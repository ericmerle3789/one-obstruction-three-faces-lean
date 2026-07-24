#!/usr/bin/env python3
# test_REQ-MATH-021_biais_structurel_vs_bruit.py — ARES (point Gemini/Ben : mod 7 STRUCTUREL vs detectabilite)
# Un biais REEL : chi2 ∝ N donc chi2/df CROIT ~lineairement avec N. Bruit : chi2/df ~ 1 stable.
# On distingue donc l'unicite STRUCTURELLE du 7 (2^3-1, effondrement maximal sur l'orbite a 3)
# de la simple "solitude" a N fixe (ou mod 5 peut franchir un seuil par fluctuation).
import math, random
random.seed(20260724)
def R0(m, s):
    p=len(m); sig=[s[t]+m[(t+1)%p] for t in range(p)]
    Ma=[0]*p; acc=0
    for t in range(p-1,-1,-1): Ma[t]=acc; acc+=m[t]
    tot,Sp=0,0
    for t in range(p): tot+=3**Ma[t]*2**Sp*(2**s[t]-1); Sp+=sig[t]
    return tot
def rand_word(n=63):
    K=(3**n).bit_length(); S=K-n
    p=random.randint(2,6)
    def comp(tot,pp):
        cuts=sorted(random.sample(range(1,tot),pp-1)); pts=[0]+cuts+[tot]
        return [pts[i+1]-pts[i] for i in range(pp)]
    return comp(n,p),comp(S,p)
def chi2df(residues,l):
    cnt=[0]*l
    for r in residues: cnt[r%l]+=1
    tot=len(residues); exp=tot/l
    return sum((c-exp)**2/exp for c in cnt)/(l-1)

print("=== CANARI : synthetique — uniforme stable, biaise croissant ===")
uni=[random.randrange(9973) for _ in range(50000)]
bia=[random.randrange(9973)*7 for _ in range(50000)]   # multiples de 7 -> biais mod 7
cu=[chi2df(uni[:N],7) for N in (10000,50000)]
cb=[chi2df(bia[:N],7) for N in (10000,50000)]
print(f"  uniforme mod7 chi2/df @10k,50k : {cu[0]:.2f},{cu[1]:.2f} (stable ~1) ; biaise : {cb[0]:.0f},{cb[1]:.0f} (croit)")
ok = cu[1]<3 and cb[1]>cb[0]*2
print(f"  CANARI: {'PASS' if ok else 'FAIL'}")
if not ok: raise SystemExit(1)

print("\n=== chi2/df de R_0 mod l par N croissant (n=63) — biais STRUCTUREL = croissance ===")
Ns=[30000,120000,480000]
maxN=max(Ns); samples=[R0(*rand_word()) for _ in range(maxN)]
print(f"{'l':>4} {'ord_l(2)':>9} " + " ".join(f'N={N//1000}k'.rjust(9) for N in Ns) + "   verdict")
for l in [5,7,11,13,31,127]:
    def ordm(a,l):
        x=a%l;k=1
        while x!=1: x=(x*a)%l;k+=1
        return k
    vals=[chi2df(samples[:N],l) for N in Ns]
    growth = vals[-1] > 2.5*vals[0] and vals[-1] > 5
    flat = vals[-1] < 3
    verdict = "STRUCTUREL (croit)" if growth else ("uniforme (plat)" if flat else "ambigu")
    print(f"{l:>4} {ordm(2,l):>9} " + " ".join(f'{v:9.2f}' for v in vals) + f"   {verdict}")
print("\n  lecture : seul l ou chi2/df CROIT avec N a un biais reel ; les 'plats ~1' sont du bruit")
print("  (mod 5 a N=30k pouvait franchir un seuil sans etre structurel). L'unicite du 7 se lit")
print("  sur le MECANISME (2^3-1, terme (2^s-1)=0 mod 7 des que s=3 mod 6), pas sur la detectabilite.")
raise SystemExit(0)
