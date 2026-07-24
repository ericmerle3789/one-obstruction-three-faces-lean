#!/usr/bin/env python3
# test_REQ-MATH-017_mod7_obstruction_locale.py — ARES (micro-lead mod 7, 2026-07-24)
#
# Le biais R_0 mod 7 (REQ-MATH-016) tient a 7=2^3-1. On pousse :
#  (1) L'instance p=7 : 7|q_7 (car 2^149 == 3^94 == 4 mod 7). REQ-MATH-005 avait dit "defaut
#      PUREMENT global" mais n'a teste QUE Z_2 et Z_3. Si 7 divise q ET pas R_0, l'equation
#      omega*q=R_0 est INSOLUBLE dans Z_7 : obstruction LOCALE, correction du "pur global".
#  (2) General : combien de profils sont exclus par une obstruction LOCALE (un p|q avec
#      v_p(R_0)<v_p(q)) plutot que globale ? => raffine "pur local-global".
#  (3) Le biais mod l est-il gouverne par l'ordre de 2 mod l (petit ordre => biais) ?
#  (4) "Seuls des decimaux resolvent" : omega=R_0/q toujours non-entier (hors trivial) ;
#      soluble dans R et Z_p (p inversible), MAIS parfois insoluble dans Z_p pour p|q.
import math, random, itertools
random.seed(20260724)

def R0(m, s):
    p = len(m); sig = [s[t] + m[(t+1) % p] for t in range(p)]
    Mafter = [0]*p; acc = 0
    for t in range(p-1, -1, -1): Mafter[t] = acc; acc += m[t]
    tot, Spre = 0, 0
    for t in range(p):
        tot += 3**Mafter[t] * 2**Spre * (2**s[t] - 1); Spre += sig[t]
    return tot
def rotations_R(m, s):
    p=len(m); return [R0(m[r:]+m[:r], s[r:]+s[:r]) for r in range(p)]
def q_of(m, s):
    n=sum(m); K=sum(s)+n; return 2**K-3**n
def vp(x, p):
    if x == 0: return math.inf
    v = 0
    while x % p == 0: x //= p; v += 1
    return v
def rand_comp_positive(total, parts):
    if parts == 1: return [total]
    cuts = sorted(random.sample(range(1, total), parts-1)); pts=[0]+cuts+[total]
    return [pts[i+1]-pts[i] for i in range(parts)]
def rand_comp_odd(S, parts):
    A=(S-parts)//2
    if A<0 or (S-parts)%2: return None
    a=[0]*parts
    for _ in range(A): a[random.randrange(parts)]+=1
    return [2*x+1 for x in a]

# ===================== CANARIS =====================
print("=== CANARIS ===")
def ordm(a, l):
    x=a%l; k=1
    while x!=1: x=(x*a)%l; k+=1
    return k
c1 = (ordm(2,7)==3 and ordm(3,7)==6)
print(f"C1  ord_7(2)=3, ord_7(3)=6 : {c1}")
c2 = (vp(48,7)==0 and vp(343,7)==3 and (2**149-3**94)%7==0 and vp(2**149-3**94,7)==3)
print(f"C2  vp ok, 7|q_7, v_7(q_7)=3 : {c2}")
m7=[4,7,9,15,23,35,1]; s7=[1]*6+[(3**94).bit_length()-94-6]
c3 = (q_of(m7,s7)==2**149-3**94)
print(f"C3  instance p=7 reconstruite (q=2^149-3^94) : {c3}")
if not(c1 and c2 and c3): print("CANARI FAIL"); raise SystemExit(1)
print("CANARIS: PASS\n")

# ===================== (1) L'INSTANCE p=7 EST-ELLE OBSTRUEE LOCALEMENT AU 7 ? =====================
print("=== (1) instance p=7 : le defaut est-il LOCAL au 7 (et non 'pur global') ? ===")
q7=q_of(m7,s7); v7q=vp(q7,7)
print(f"  v_7(q_7) = {v7q}")
print(f"  {'rot':>3} {'v_7(R_r)':>9} {'v_7(R)>=v_7(q) ? (Z_7 soluble)':>32} {'gcd(q,R)':>10}")
loc_ok_all=True
for r,R in enumerate(rotations_R(m7,s7)):
    v7R=vp(R,7); solvable7 = (v7R>=v7q); loc_ok_all &= solvable7
    print(f"  {r:>3} {v7R:>9} {str(solvable7):>32} {math.gcd(q7,R):>10}")
print(f"  => Z_7 soluble a TOUTES les rotations ? {loc_ok_all}")
print(f"  VERDICT : {'defaut PUREMENT global (REQ-005 confirme)' if loc_ok_all else 'OBSTRUCTION LOCALE au 7 -> REQ-005 a rate un test local, correction !'}")

# ===================== (2) part LOCALE vs GLOBALE de l'exclusion (general) =====================
print("\n=== (2) fraction exclue LOCALEMENT (un p|q avec v_p(R_0)<v_p(q)) vs residuel ===")
small_primes=[5,7,11,13,17,19,23,29,31,37,41,43,47]
print(f"{'n':>4} {'#ech':>7} {'gcd(q,R0)=1 %':>13} {'excl. LOCAL p<=47 %':>20} {'passe tous locaux %':>20}")
for n in [24,40,63,90]:
    K=(3**n).bit_length(); S=K-n; q=2**K-3**n
    p=None
    for cand in range(min(6,S,n),1,-1):
        if (S-cand)%2==0: p=cand; break
    N=20000; coprime=0; loc_excl=0; pass_all=0
    qfac=[pp for pp in small_primes if q%pp==0]
    for _ in range(N):
        ss=rand_comp_odd(S,p); ms=rand_comp_positive(n,p)
        if not ss: continue
        R=R0(ms,ss)
        if math.gcd(q,R)==1: coprime+=1
        excl = any(vp(R,pp)<vp(q,pp) for pp in qfac)   # obstruction locale a un p|q, p<=47
        loc_excl += excl
        if not excl: pass_all+=1
    print(f"{n:>4} {N:>7} {100*coprime/N:>12.1f}% {100*loc_excl/N:>19.1f}% {100*pass_all/N:>19.1f}%  (q divisible par {qfac})")
print("  'excl LOCAL' = tue par un petit premier p|q (v_p(R0)<v_p(q)) : c'est du LOCAL, pas du global.")

# ===================== (3) biais mod l gouverne par ord_l(2) ? =====================
print("\n=== (3) biais R_0 mod l vs ordre de 2 mod l (petit ordre => biais fort ?) ===")
print(f"{'l':>4} {'ord_l(2)':>9} {'ord_l(3)':>9} {'chi2/df':>9} {'verdict':>10}")
n=63; K=(3**n).bit_length(); S=K-n
p=None
for cand in range(min(6,S,n),1,-1):
    if (S-cand)%2==0: p=cand; break
samples=[]
for _ in range(30000):
    ss=rand_comp_odd(S,p); ms=rand_comp_positive(n,p)
    if ss: samples.append(R0(ms,ss))
for l in [5,7,11,13,17,23,31,127]:
    cnt=[0]*l
    for R in samples: cnt[R%l]+=1
    exp=len(samples)/l
    chi2=sum((c-exp)**2/exp for c in cnt)/(l-1)
    print(f"{l:>4} {ordm(2,l):>9} {ordm(3,l):>9} {chi2:>9.2f} {'BIAIS' if chi2>2 else 'uniforme':>10}")
print("  hypothese : ord_l(2) petit (ex. 7:3, 31:5, 127:7) => biais ; ordre grand => uniforme.")

# ===================== (4) SEULS DES DECIMAUX ? omega=R_0/q jamais entier (hors trivial) =====================
print("\n=== (4) 'seuls des decimaux resolvent' : omega=R_0/q entier ? (0 attendu hors trivial) ===")
tot=0; integer_sol=0
for n in [24,40,63]:
    K=(3**n).bit_length(); S=K-n; q=2**K-3**n
    p=None
    for cand in range(min(6,S,n),1,-1):
        if (S-cand)%2==0: p=cand; break
    for _ in range(20000):
        ss=rand_comp_odd(S,p); ms=rand_comp_positive(n,p)
        if not ss: continue
        tot+=1; integer_sol += (R0(ms,ss)%q==0)
print(f"  profils testes : {tot} | omega ENTIER (=cycle) : {integer_sol}")
print("  omega=R_0/q existe toujours comme REEL (R,>0) et comme p-adique pour p inversible ;")
print("  il n'est JAMAIS un entier (hors trivial) => 'seuls des decimaux resolvent' = la conjecture,")
print("  et (1)-(2) montrent que parfois il n'est meme pas un entier LOCAL (Z_p, p|q) : obstruction locale.")
raise SystemExit(0)
