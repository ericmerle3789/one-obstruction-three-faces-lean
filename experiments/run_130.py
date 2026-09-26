# run_130 — the cause of the committed run_048.py's x = -6 (round 17). Recorded in the lab as D031 (labtrace id=89,
# 2026-09-26). The committed accumulator omits the factor p on an ascent; a missing parity check cannot produce
# an integer off every cycle. Exact arithmetic, every word to length 12. Body below unchanged.
"""D031 — why run_048.py (committed) emitted x = -6: the accumulator omits the factor p on an ascent. Exact arithmetic."""
from fractions import Fraction
from itertools import product
def rationnel_commite(bits, p, rev=True):                 # verbatim logic of experiments/run_048.py l.102-113
    num = Fraction(0); coef = Fraction(1)
    for b in (reversed(bits) if rev else bits):
        if b: num = (num + 1) / 2; coef = coef * p / 2
        else: num = num / 2; coef = coef / 2
    if coef == 1: return None
    return num / (1 - coef)
def rationnel_correct(bits, p):                           # D010 (recovered corrected run of 2026-08-05)
    a = Fraction(1); c = Fraction(0)
    for b in bits:
        if b: a, c = a * p / 2, (c * p + 1) / 2
        else: a, c = a / 2, c / 2
    if a == 1: return None
    return c / (1 - a)
def T(x, p): return x // 2 if x % 2 == 0 else (p * x + 1) // 2
def follows(x, bits, p):
    for b in bits:
        if (x % 2) != b: return False
        x = T(x, p)
    return True
def on_cycle(x, p, cap=500):
    y = x
    for _ in range(cap):
        y = T(y, p)
        if y == x: return True
    return False
print("Q1 mot 110, p=3 : commite sans reversed ->", rationnel_commite([1,1,0], 3, rev=False), "; correct ->", rationnel_correct([1,1,0], 3))
q1 = rationnel_commite([1,1,0], 3, rev=False) == -3 and rationnel_correct([1,1,0], 3) == -5
bad_fixed, good = set(), set()
for L in range(1, 13):
    for bits in product((0, 1), repeat=L):
        for fn, bag in ((lambda b: rationnel_commite(list(b), 3, rev=False), bad_fixed), (lambda b: rationnel_correct(list(b), 3), good)):
            x = fn(bits)
            if x is not None and x.denominator == 1: bag.add((int(x), bits))
ints_fixed = sorted({x for x, _ in bad_fixed}); ints_good = sorted({x for x, _ in good})
off_cycle_fixed = sorted({x for x in ints_fixed if not on_cycle(x, 3)})
print("Q2 entiers produits (sans reversed, L<=12) :", ints_fixed[:30], "... hors cycle :", off_cycle_fixed[:30])
print("Q2 entiers produits (correct, L<=12)       :", ints_good)
print("   chaque entier correct suit son mot :", all(follows(x, b, 3) for x, b in good))
print("   chaque entier correct est sur un cycle :", all(on_cycle(x, 3) for x in ints_good))
q2 = (-6 in off_cycle_fixed) and all(follows(x, b, 3) for x, b in good) and all(on_cycle(x, 3) for x in ints_good)
w6 = sorted(b for x, b in bad_fixed if x == -6)[:3]
print("   mots qui donnent -6 (sans reversed) :", ["".join(map(str, b)) for b in w6], "; valeur correcte sur ces mots :", [str(rationnel_correct(list(b), 3)) for b in w6])
q3 = all(rationnel_correct(list(b), 3) != -6 for b in w6)
print("Q1", "TENUE" if q1 else "TOMBEE"); print("Q2", "TENUE" if q2 else "TOMBEE"); print("Q3", "TENUE" if q3 else "TOMBEE")
