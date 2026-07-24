#!/usr/bin/env python3
# test_REQ-MATH-018_contenu_adelique.py — ARES (dimension adelique : le temoin "contenu", 2026-07-24)
#
# INVARIANT NOUVEAU (vue formule-du-produit / adeles) :
#   C(profil) = log2 gcd(q, R_0) / log2 q  in [0,1]   (invariant par rotation, L-A1)
#   = la part de la serrure q deja "remplie" aux places finies = la jauge decimal->entier
#   (fraction R_0/q reduite : son denominateur = q / gcd ; C=1 <=> denominateur 1 <=> CYCLE).
# CANDIDAT (dichotomie du contenu) : seul le mot repete (L-A2) fait monter C ; l'aperiodique
# reste au niveau hasard. Avec la descente (L-A4), C<1 aperiodique fermerait tout.
#  (A) loi de C sur profils aleatoires (aperiodiques) par echelle — exces structurel ?
#  (B) mots repetes B^j : C predit par L-A2 (gcd = |q_P|/q_red(B)) -> C monte vers 1 ?
#  (C) LA FALAISE : perturbation d'UNE lettre a q FIXE -> le contenu s'effondre-t-il ?
import math, random
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
def content(m, s):
    q = q_of(m, s); g = math.gcd(q, R0(m, s))
    return math.log2(g)/math.log2(q), g, q
def rand_comp(total, parts):
    if parts == 1: return [total]
    cuts = sorted(random.sample(range(1, total), parts-1)); pts=[0]+cuts+[total]
    return [pts[i+1]-pts[i] for i in range(parts)]
def is_periodic(m, s):
    p = len(m); w = list(zip(m, s))
    return any(w == w[:t]*(p//t) for t in range(1, p) if p % t == 0)

# ===================== CANARIS =====================
print("=== CANARIS ===")
C1, g1, q1 = content([1,1],[1,1])                       # trivial^2 : q=7, R0=7 -> C=1
print(f"C1  trivial^2 : q={q1}(7) gcd={g1}(7) C={C1:.3f}(1.000) : {q1==7 and g1==7 and abs(C1-1)<1e-12}")
C2, g2, q2 = content([1,1],[3,3])                       # L-A2 : q=247, gcd=19
print(f"C2  (1,3)^2 : q={q2}(247) gcd={g2}(19) C={C2:.4f}(0.5344) : {q2==247 and g2==19}")
m7=[4,7,9,15,23,35,1]; s7=[1]*6+[(3**94).bit_length()-94-6]
C3, g3, q3 = content(m7, s7)                            # staircase p=7 : gcd=7 (REQ-017)
print(f"C3  staircase p=7 : gcd={g3}(7), C={C3:.4f} (petit) : {g3==7}")
mr=rand_comp(17,4); sr=rand_comp(10,4)                  # invariance par rotation du gcd
gs={math.gcd(q_of(mr[r:]+mr[:r], sr[r:]+sr[:r]), R0(mr[r:]+mr[:r], sr[r:]+sr[:r])) for r in range(4)}
print(f"C4  gcd invariant par rotation (profil aleatoire) : {len(gs)==1}")
if not (q1==7 and g1==7 and q2==247 and g2==19 and g3==7 and len(gs)==1):
    print("CANARI FAIL"); raise SystemExit(1)
print("CANARIS: PASS\n")

# ===================== (A) loi de C sur l'aperiodique =====================
print("=== (A) profils aleatoires par echelle : C montre-t-il un exces structurel ? ===")
print(f"{'n':>4} {'bits(q)':>8} {'#ech':>7} {'max C aper.':>11} {'#C>0.20':>8} {'#C>0.35':>8} {'#period.':>9}")
for n in [17, 25, 40, 63]:
    K=(3**n).bit_length(); S=K-n
    N=20000; mx=0.0; c20=0; c35=0; nper=0; top=None
    for _ in range(N):
        p=random.randint(2, min(8, S, n))
        ms=rand_comp(n,p); ss=rand_comp(S,p)
        C,g,q = content(ms,ss)
        if is_periodic(ms,ss): nper+=1; continue
        c20+=(C>0.20); c35+=(C>0.35)
        if C>mx: mx=C; top=(p,g)
    print(f"{n:>4} {q_of([n],[S]).bit_length():>8} {N:>7} {mx:>11.4f} {c20:>8} {c35:>8} {nper:>9}   (top: p={top[0]}, gcd={top[1]})")
print("  lecture : max C aperiodique reste bas et DEPEND de la factorisation (sauvage) de q ;")
print("  aucune montee structurelle — compatible pur hasard a la profondeur d'echantillonnage.")

# ===================== (B) mots repetes : C monte vers 1 (loi L-A2) =====================
print("\n=== (B) mots repetes B^j : le contenu fabrique par la repetition (formule L-A2 re-verifiee) ===")
for mB,sB,name in [([1],[3],"B=(1|3), q_B=13"), ([1,2],[3,1],"B=(1,2|3,1), q_B=101")]:
    qB=q_of(mB,sB); qred=abs(qB)//math.gcd(abs(qB),R0(mB,sB))
    print(f"  base {name}, q_red={qred} :")
    print(f"    {'j':>3} {'bits(q_P)':>9} {'gcd':>12} {'formule |q_P|/q_red ?':>21} {'C':>8}")
    for j in [2,3,4,6,8]:
        mP,sP=mB*j,sB*j
        C,g,qP=content(mP,sP)
        ok = (g == abs(qP)//qred)
        print(f"    {j:>3} {qP.bit_length():>9} {g:>12} {str(ok):>21} {C:>8.4f}")

# ===================== (C) LA FALAISE : une lettre change, q fixe =====================
print("\n=== (C) falaise du contenu : B^j vs perturbation d'UNE lettre (q identique) ===")
print(f"{'base^j':>16} {'C(B^j)':>8} {'#pert':>6} {'max C pert':>11} {'moy C pert':>11} {'pert. period.':>13}")
for mB,sB,j in [([1,2],[3,1],3), ([1,2],[3,1],4), ([1],[3],6)]:
    mP,sP=mB*j,sB*j; C0,g0,q0=content(mP,sP)
    mxp=0.0; sm=0.0; cnt=0; nper=0
    while cnt<300:
        m2,s2=mP[:],sP[:]
        if random.random()<0.5:
            i,k=random.sample(range(len(m2)),2)
            if m2[k]<2: continue
            m2[i]+=1; m2[k]-=1
        else:
            i,k=random.sample(range(len(s2)),2)
            if s2[k]<2: continue
            s2[i]+=1; s2[k]-=1
        assert q_of(m2,s2)==q0                      # meme serrure, seul le mot change
        Cp,gp,_=content(m2,s2)
        nper+=is_periodic(m2,s2)
        mxp=max(mxp,Cp); sm+=Cp; cnt+=1
    print(f"{'('+str(mB)+'|'+str(sB)+')^'+str(j):>16} {C0:>8.4f} {cnt:>6} {mxp:>11.4f} {sm/cnt:>11.4f} {nper:>13}")
print("  lecture : si C s'effondre au niveau hasard des UNE lettre changee, le contenu est")
print("  FRAGILE : seule la repetition EXACTE le fabrique — et la repetition est sterile (L-A4).")
raise SystemExit(0)
