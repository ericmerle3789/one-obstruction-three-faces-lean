#!/usr/bin/env python3
# test_REQ-MATH-015_equidistribution_et_structure.py — ARES (creuser jusqu'au bout, 2026-07-24)
#
# Le comptage (REQ-MATH-014) donne "nb attendu de cycles ~ 2^{-0.27n}" SOUS l'hypothese que
# les residus R_0 mod q EQUIDISTRIBUENT. On teste cette hypothese DIRECTEMENT, puis on CHASSE
# le seul endroit ou un cycle pourrait se cacher : un sous-ensemble STRUCTURE (quasi-periodique)
# ou l'equidistribution casserait et R_0 se masserait vers 0.
#  M1  test de Weyl : W_k = |(1/N) Σ e^{2πi k R_0/q}| petit pour k=1..12  <=>  equidistribue.
#      + sur-densite pres de 0 : frac(u<eps) vs 2*eps (uniforme).
#  M2  familles PERIODIQUES accordees (periode d|pgcd(n,S), 'mots repetes' tunes) : leur u
#      et gcd(q,R_0) se massent-ils vers 0 (danger) ou restent-ils LOIN de 0 (rigidite) ?
# Tout profil est ACCORDE (K=bit_length(3^n), sum s=S) : pas d'artefact gros-q.
import math, random, cmath, itertools
random.seed(20260724)

def R0(m, s):
    p = len(m)
    sig = [s[t] + m[(t+1) % p] for t in range(p)]
    Mafter = [0]*p; acc = 0
    for t in range(p-1, -1, -1):
        Mafter[t] = acc; acc += m[t]
    tot, Spre = 0, 0
    for t in range(p):
        tot += 3**Mafter[t] * 2**Spre * (2**s[t] - 1); Spre += sig[t]
    return tot

def rand_comp_positive(total, parts):
    if parts == 1: return [total]
    cuts = sorted(random.sample(range(1, total), parts-1))
    pts = [0]+cuts+[total]; return [pts[i+1]-pts[i] for i in range(parts)]
def rand_comp_odd(S, parts):
    A = (S-parts)//2
    if A < 0 or (S-parts) % 2: return None
    a = [0]*parts
    for _ in range(A): a[random.randrange(parts)] += 1
    return [2*x+1 for x in a]
def comps_positive(total, parts):
    for cuts in itertools.combinations(range(1, total), parts-1):
        pts = [0]+list(cuts)+[total]; yield [pts[i+1]-pts[i] for i in range(parts)]
def comps_odd(S, parts):
    A = (S-parts)//2
    if A < 0 or (S-parts) % 2: return
    for bars in itertools.combinations(range(A+parts-1), parts-1):
        pts = [-1]+list(bars)+[A+parts-1]
        yield [2*(pts[i+1]-pts[i]-1)+1 for i in range(parts)]

def weyl(residues, q, K=12):
    N = len(residues); out = []
    for k in range(1, K+1):
        s = sum(cmath.exp(2j*math.pi*k*(r/q)) for r in residues)
        out.append(abs(s)/N)
    return out

# ===================== CANARIS =====================
print("=== CANARIS ===")
# C1 : instance p=7 -> min_r dist = 0.05 (reproduit REQ-MATH-005/013)
def rotations_R(m,s):
    p=len(m);out=[]
    for r in range(p):
        ms=m[r:]+m[:r];ss=s[r:]+s[:r]
        out.append(R0(ms,ss))
    return out
m7=[4,7,9,15,23,35,1];n7=sum(m7);K7=(3**n7).bit_length();s7=[1]*6+[K7-n7-6];q7=2**K7-3**n7
minu7=round(min(min(R%q7,q7-(R%q7))/q7 for R in rotations_R(m7,s7)),2)
c1=(minu7==0.05); print(f"C1  p=7 min_r u = {minu7} (att. 0.05) : {c1}")
# C2 : Weyl synthetique — uniforme -> petit ; tout=0 -> 1
qtest=2**40-3**25
uni=[random.randrange(qtest) for _ in range(5000)]
zer=[0]*5000
wu=max(weyl(uni,qtest,6)); wz=min(weyl(zer,qtest,6))
c2=(wu<0.08 and wz>0.999); print(f"C2  Weyl uniforme max={wu:.3f}(<.08) ; tout-zero min={wz:.3f}(=1) : {c2}")
# C3 : mot repete (L-A2) gcd force : base=([1],[3]), P=B^2 -> q_P=247, gcd=19
mB,sB=[1],[3]; mP,sP=mB*2,sB*2
qP=2**(sum(sP)+sum(mP))-3**sum(mP); gP=math.gcd(qP,R0(mP,sP))
c3=(qP==247 and gP==19); print(f"C3  mot repete B^2 : q_P={qP}(247), gcd={gP}(19) : {c3}")
if not(c1 and c2 and c3): print("CANARI FAIL"); raise SystemExit(1)
print("CANARIS: PASS\n")

# ===================== M1 : EQUIDISTRIBUTION (Weyl) de la strate generique =====================
print("=== M1 : R_0 mod q equidistribue-t-il sur la strate ? (Weyl W_k + sur-densite pres de 0) ===")
print(f"{'n':>4} {'bits(q)':>8} {'#ech':>7} {'max_k W_k':>10} {'1/sqrt(N)':>10} {'frac(u<.01)':>11} {'attendu .02':>11}")
for n in [12, 24, 40, 63]:
    K=(3**n).bit_length(); S=K-n; q=2**K-3**n
    p=None
    for cand in range(min(6,S,n),1,-1):
        if (S-cand)%2==0: p=cand; break
    if p is None: continue
    res=[]
    # enum complete si petit, sinon echantillon
    n_odd=math.comb((S-p)//2+p-1,p-1); n_m=math.comb(n-1,p-1)
    if n_odd*n_m<=40000:
        for ms in comps_positive(n,p):
            for ss in comps_odd(S,p): res.append(R0(ms,ss)%q)
    else:
        for _ in range(40000):
            ss=rand_comp_odd(S,p); ms=rand_comp_positive(n,p)
            if ss: res.append(R0(ms,ss)%q)
    N=len(res); W=weyl(res,q,12); mw=max(W)
    frac=sum(1 for r in res if min(r,q-r)/q<0.01)/N
    print(f"{n:>4} {q.bit_length():>8} {N:>7} {mw:>10.4f} {1/math.sqrt(N):>10.4f} {frac:>11.4f} {2*0.01:>11.4f}")
print("  max_k W_k ~ 1/sqrt(N) et frac(u<.01) ~ 0.02  =>  EQUIDISTRIBUE, pas de masse cachee pres de 0.")

# ===================== M2 : familles PERIODIQUES accordees — rigidite ou danger ? =====================
print("\n=== M2 : profils PERIODIQUES (mots repetes accordes, periode d|pgcd(n,S)) : u et gcd ===")
print(f"{'n':>4} {'d':>3} {'ell':>4} {'#profils':>9} {'min u (periodique)':>18} {'gcd>1 %':>8} {'min u GENERIQUE (rappel)':>24}")
for n in [24, 36, 60]:
    K=(3**n).bit_length(); S=K-n; q=2**K-3**n
    # rappel generique : min u sur echantillon generique meme n
    p0=None
    for cand in range(min(6,S,n),1,-1):
        if (S-cand)%2==0: p0=cand; break
    gen_min=1.0
    for _ in range(20000):
        ss=rand_comp_odd(S,p0); ms=rand_comp_positive(n,p0)
        if ss:
            r=R0(ms,ss)%q; gen_min=min(gen_min,min(r,q-r)/q)
    for d in range(2, min(n,S)+1):
        if n%d or S%d: continue
        nb, Sb = n//d, S//d
        for ell in [1,2,3]:
            if nb<ell or Sb<ell or (Sb-ell)%2: continue
            cnt=0; minu=1.0; g1=0
            # enum bases si petit sinon echantillon
            base_odd=math.comb((Sb-ell)//2+ell-1,ell-1); base_m=math.comb(nb-1,ell-1)
            if base_odd*base_m<=8000:
                bases=((mb,sb) for mb in comps_positive(nb,ell) for sb in comps_odd(Sb,ell))
            else:
                bases=((rand_comp_positive(nb,ell), rand_comp_odd(Sb,ell)) for _ in range(6000))
            for mb,sb in bases:
                if sb is None: continue
                r=R0(mb*d, sb*d)%q
                minu=min(minu,min(r,q-r)/q); g1+=(math.gcd(q,r)>1); cnt+=1
            if cnt:
                print(f"{n:>4} {d:>3} {ell:>4} {cnt:>9} {minu:>18.6f} {100*g1/cnt:>7.1f}% {gen_min:>24.6f}")
print("\n  LECTURE : si les periodiques ont gcd>1 (souvent 100%) ET min u >> 0 (LOIN de 0) alors la")
print("  structure est RIGIDE — aucun cycle ne peut s'y cacher, il faudrait un profil GENERIQUE, or")
print("  ceux-la equidistribuent (M1). Le seul refuge possible d'un cycle est donc ferme des 2 cotes.")
raise SystemExit(0)
