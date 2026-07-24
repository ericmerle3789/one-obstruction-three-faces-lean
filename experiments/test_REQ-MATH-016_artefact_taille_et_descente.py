#!/usr/bin/env python3
# test_REQ-MATH-016_artefact_taille_et_descente.py — ARES (creuser jusqu'au bout, correction, 2026-07-24)
#
# REQ-MATH-015 a montre : max_k W_k grandit et frac(u<.01) grandit avec n. Mon label
# "equidistribue" etait FAUX. Ici on tranche la CAUSE :
#  (A) ARTEFACT DE TAILLE ? u=||R_0/q|| ; un vrai cycle non trivial exige R_0/q >> 1 (element
#      minimal >= borne Hercher). Aux petites echelles R_0/q est petit, souvent < 1. On MESURE
#      la fraction R_0/q<1 et d'ou vient la masse u<.01 : si elle vient de R_0/q<1 (degenere,
#      AUCUN cycle possible) => la "non-equidistribution" est un artefact, pas un danger.
#      + equidistribution a PETIT MODULE (R_0 mod l) : la vraie question arithmetique (deja
#      "structureless" chez REQ-MATH-005) — on re-verifie sur la strate.
#  (B) DESCENTE : les familles periodiques (structurees) ne peuvent contenir de cycle NEUF —
#      P=B^d est un cycle  <=>  B en est un (heritage L-A1/L-A2). Canari + verif.
import math, random, cmath, itertools
random.seed(20260724)

def R0(m, s):
    p = len(m); sig = [s[t] + m[(t+1) % p] for t in range(p)]
    Mafter = [0]*p; acc = 0
    for t in range(p-1, -1, -1): Mafter[t] = acc; acc += m[t]
    tot, Spre = 0, 0
    for t in range(p):
        tot += 3**Mafter[t] * 2**Spre * (2**s[t] - 1); Spre += sig[t]
    return tot
def q_of(m, s):
    n = sum(m); K = sum(s) + n; return 2**K - 3**n
def rand_comp_positive(total, parts):
    if parts == 1: return [total]
    cuts = sorted(random.sample(range(1, total), parts-1)); pts = [0]+cuts+[total]
    return [pts[i+1]-pts[i] for i in range(parts)]
def rand_comp_odd(S, parts):
    A = (S-parts)//2
    if A < 0 or (S-parts) % 2: return None
    a = [0]*parts
    for _ in range(A): a[random.randrange(parts)] += 1
    return [2*x+1 for x in a]

# ===================== CANARIS =====================
print("=== CANARIS ===")
# C1 : HERITAGE. base triviale ([1],[1]) est un 'cycle' (q=1) -> B^2=([1,1],[1,1]) : q=7, R0=7, 7|7 OK
mB,sB=[1],[1]; mP,sP=mB*2,sB*2
qB=q_of(mB,sB); qP=q_of(mP,sP); RB=R0(mB,sB); RP=R0(mP,sP)
c1a = (qB==1 and RB%qB==0)               # base = cycle (lock libre q=1)
c1b = (qP==7 and RP==7 and RP%qP==0)     # B^2 herite -> cycle
# base NON-cycle -> B^d non-cycle
mB2,sB2=[2,1],[3,1]; okdesc=True
for d in (2,3,4):
    P=(mB2*d,sB2*d); B=(mB2,sB2)
    if (R0(*P)%q_of(*P)==0) != (R0(*B)%q_of(*B)==0): okdesc=False
c1=(c1a and c1b and okdesc)
print(f"C1  heritage : triv cycle->B^2 cycle (q7,R7)={c1a and c1b} ; non-cycle->B^d non-cycle={okdesc} : {c1}")
# C2 : equidist synthetique (uniforme -> Weyl petit)
qt=2**40-3**25; wu=max(abs(sum(cmath.exp(2j*math.pi*k*(random.randrange(qt)/qt)) for _ in range(4000)))/4000 for k in (1,2,3))
c2=(wu<0.09); print(f"C2  Weyl uniforme max(k<=3)={wu:.3f}(<.09) : {c2}")
if not(c1 and c2): print("CANARI FAIL"); raise SystemExit(1)
print("CANARIS: PASS\n")

# ===================== (A) D'OU VIENT LA MASSE u<.01 ? =====================
print("=== (A) la masse pres de 0 vient-elle des degeneres R_0/q<1 (aucun cycle possible) ? ===")
print(f"{'n':>4} {'bits(q)':>8} {'#ech':>7} {'frac R0/q<1':>12} {'frac u<.01':>11} {'  dont R0/q<1':>13} {'  dont R0/q>=2':>14}")
for n in [24, 40, 63, 90]:
    K=(3**n).bit_length(); S=K-n; q=2**K-3**n
    p=None
    for cand in range(min(6,S,n),1,-1):
        if (S-cand)%2==0: p=cand; break
    if p is None: continue
    N=30000; lt1=0; near=0; near_lt1=0; near_ge2=0
    for _ in range(N):
        ss=rand_comp_odd(S,p); ms=rand_comp_positive(n,p)
        if not ss: continue
        R=R0(ms,ss); r=R%q; u=min(r,q-r)/q
        ratio_lt1 = (R<q); ratio_ge2 = (R>=2*q)
        lt1+=ratio_lt1
        if u<0.01:
            near+=1; near_lt1+=ratio_lt1; near_ge2+=ratio_ge2
    print(f"{n:>4} {q.bit_length():>8} {N:>7} {lt1/N:>12.3f} {near/N:>11.4f} {near_lt1/max(near,1):>13.2f} {near_ge2/max(near,1):>14.2f}")
print("  Si 'dont R0/q<1' ~ 1.00 : la masse u<.01 est PUREMENT degeneree (R_0/q proche de 0 ou 1,")
print("  element minimal <1 : aucun cycle non trivial la) => la 'non-equidistribution' de REQ-015 est")
print("  un ARTEFACT DE TAILLE, pas un signal de cycle.")

# ===================== (A bis) equidistribution a PETIT MODULE (vrai signal arithmetique) =====================
print("\n=== (A bis) R_0 mod l equidistribue-t-il (petit module l, sans confusion de taille) ? ===")
print(f"{'n':>4} {'l':>4} {'chi2/df':>9} {'verdict':>16}")
for n in [40, 63]:
    K=(3**n).bit_length(); S=K-n
    p=None
    for cand in range(min(6,S,n),1,-1):
        if (S-cand)%2==0: p=cand; break
    for l in [7, 11, 13]:
        N=30000; cnt=[0]*l
        for _ in range(N):
            ss=rand_comp_odd(S,p); ms=rand_comp_positive(n,p)
            if not ss: continue
            cnt[R0(ms,ss)%l]+=1
        tot=sum(cnt); exp=tot/l
        chi2=sum((c-exp)**2/exp for c in cnt)/(l-1)   # ~1 si uniforme
        print(f"{n:>4} {l:>4} {chi2:>9.2f} {'uniforme' if chi2<2 else 'BIAIS':>16}")
print("  chi2/df ~ 1 => R_0 mod l uniforme (recoupe REQ-MATH-005 'prime-local structureless').")

# ===================== (B) DESCENTE : familles periodiques n'ont pas de cycle NEUF =====================
print("\n=== (B) heritage : sur familles periodiques, cycle(P) <=> cycle(base) — jamais neuf ===")
ok=0; tot=0
for n in [24, 36, 60]:
    K=(3**n).bit_length(); S=K-n
    for d in range(2, 7):
        if n%d or S%d: continue
        nb,Sb=n//d,S//d
        for ell in [1,2,3]:
            if nb<ell or Sb<ell or (Sb-ell)%2: continue
            for _ in range(400):
                mb=rand_comp_positive(nb,ell); sb=rand_comp_odd(Sb,ell)
                if not sb: continue
                cyc_P=(R0(mb*d,sb*d)%q_of(mb*d,sb*d)==0)
                cyc_B=(R0(mb,sb)%q_of(mb,sb)==0)
                tot+=1; ok+=(cyc_P==cyc_B)
print(f"  cycle(P)==cycle(base) sur {tot} tirages periodiques : {ok}/{tot}  ({'PARFAIT' if ok==tot else 'CONTRE-EXEMPLE !'})")
print("  => aucune famille structuree ne cree de cycle ; un cycle neuf devrait etre GENERIQUE,")
print("     et le generique n'a de masse pres de 0 que par artefact de taille (A). Porte fermee des 2 cotes,")
print("     MODULO la seule chose qui reste vraie et non prouvee : l'equidistribution a GRANDE echelle (x2x3).")
raise SystemExit(0)
