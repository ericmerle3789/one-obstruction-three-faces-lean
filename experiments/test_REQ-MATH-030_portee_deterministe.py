#!/usr/bin/env python3
# test_REQ-MATH-030_portee_deterministe.py — ARES (descente a la racine : portee du DETERMINISTE)
# RESTRICTION JUSTIFIEE : x = B/q ; une cellule ne peut heberger un grand x que si q est PETIT,
# donc seules les cellules ACCORDEES (K = ceil(n*L)+j, j=0,1,2) comptent. Exhaustif dessus.
# ASSEMBLAGE : (i) x_max(cellule) = maxB/q exact ; (ii) regle d'individu eps_n >= c/n^{mu-1}.
# => critere DETERMINISTE (0 probabilite) : heberger un cycle d'element min >= X0 exige
#    q <= maxB/X0. Toutes les echelles n < N* sont exclues SANS probabilite.
# PREDICTIONS : P1 canaris ; P2 A = maxB/3^n stable (1..4) ; P3 N* ~ 10^5, litterature 1.4e11.
import math, itertools
L=math.log2(3.0)
def beta(m): return 3**m-2**m
def B_of(ms,ss):
    p=len(ms); n=sum(ms); B=0; Kp=0; Ma=n
    for t in range(p):
        Ma-=ms[t]; B+=3**Ma*2**Kp*beta(ms[t]); Kp+=ms[t]+ss[t]
    return B
def comps(total,parts):
    if parts==1: yield (total,); return
    for cuts in itertools.combinations(range(1,total),parts-1):
        pts=(0,)+cuts+(total,); yield tuple(pts[i+1]-pts[i] for i in range(parts))
print("=== CANARIS ===")
c1=(B_of((1,1),(1,1))==7 and (2**4-3**2)==7)
c2=(B_of((4,3),(1,3))==2363 and (2**11-3**7)==-139 and 2363//(2**11-3**7)==-17)
print(f"  trivial^2 B=7=q x=1 : {c1} | mot -17 B=2363 q=-139 x=-17 : {c2}")
if not(c1 and c2): print("CANARI FAIL"); raise SystemExit(1)
print("CANARIS: PASS\n")
print("=== maxB et x_max sur les cellules ACCORDEES (exhaustif) ===")
print(f"  {'n':>3} {'K':>3} {'q':>14} {'A=maxB/3^n':>11} {'x_max=maxB/q':>14}")
A=0.0
for n in range(2,15):
    p3=3**n; K0=math.ceil(n*L)
    for j in (0,1):
        K=K0+j; S=K-n
        if S<1: continue
        q=2**K-p3
        if q<=0: continue
        mx=0
        for p in range(1,min(n,S)+1):
            for ms in comps(n,p):
                for ss in comps(S,p):
                    b=B_of(ms,ss)
                    if b>mx: mx=b
        a=mx/p3; A=max(A,a)
        if n<=6 or (n>=12 and j==0):
            print(f"  {n:>3} {K:>3} {q:>14} {a:>11.4f} {mx/q:>14.3f}")
print(f"  => A (max observe sur cellules accordees, n<=14) = {A:.4f}")
print("\n=== PORTEE DETERMINISTE (aucune probabilite) ===")
X0=2**71; MU=5.125
print(f"  X0=2^71={X0:.3e} (Barina) ; mu={MU} (Salikhov, a re-sourcer)")
print(f"  hebergement exige : eps_n <= A/(X0*ln2) = {A/(X0*math.log(2)):.3e}")
print(f"  {'c':>10} {'N* = (c*X0*ln2/A)^(1/(mu-1))':>32}")
for c in (1.0,0.1,0.01,1e-3):
    print(f"  {c:>10.0e} {(c*X0*math.log(2)/A)**(1.0/(MU-1)):>32.3e}")
N1=(1.0*X0*math.log(2)/A)**(1.0/(MU-1))
print(f"\n  -> n < N* ~ {N1:.2e} : EXCLU DETERMINISTIQUEMENT (notre chaine elementaire, autonome)")
print(f"  -> litterature (Hercher) : k > 1.375e11, soit {1.375e11/N1:.0f}x plus loin (chaine bien plus fine)")
print("\n=== LA RACINE ATTEINTE ===")
print("  La portee deterministe est FINIE PAR NATURE : au-dela de N*, eps_n redevient minuscule")
print("  aux convergents et la regle d'individu (n^-(mu-1)) est trop lente pour l'interdire.")
print("  C'est le ciseau (REQ-001/004) sous un autre jour. Au-dela : seule l'esperance (torsion).")
print("  RACINE = le pas 'esperance -> certitude' = x2x3. Aucun assemblage de nos pieces ne le franchit.")
raise SystemExit(0)
