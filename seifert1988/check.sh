#!/usr/bin/env bash
# Re-check the seifert1988 formalisation, file by file, on Lean 4.34.0 + Mathlib v4.34.0 (needs python3).
# Prerequisite, once: in ../steiner1978, `lake exe cache get` (prebuilt Mathlib; nothing of Mathlib is recompiled).
# This folder has no Lake package of its own: env.sh takes LEAN_PATH from ../logs23. `lake build` is not used.
# 1. The sources are checked against SHA256SUMS.
# 2. ../logs23/check.sh is run: it re-checks Steiner 1978 and logs23, and builds the modules imported here
#    (`near_miss` uses `lam_lower` of logs23).
# 3. Each file of Seifert1988/ is compiled with `lean -o`, in dependency order; the check fails on any error and on any
#    warning "declaration uses `sorry`".
# 4. The `#print axioms` output of Seifert1988/Axiomes.lean is read: the check fails unless the reports are exactly
#    those of the 33 frozen statements (NAMES below), or if one of them depends on an axiom other than propext,
#    Classical.choice, Quot.sound (this also rules out sorryAx and the auxiliary axiom that native_decide adds on
#    Lean 4.34).
set -euo pipefail
cd "$(dirname "$0")"
EXPECTED=33
if command -v sha256sum > /dev/null 2>&1; then sha256sum --quiet -c SHA256SUMS; else shasum -a 256 --quiet -c SHA256SUMS; fi
echo "SHA256SUMS: all sources match"
echo "== ../logs23/check.sh"
../logs23/check.sh
echo "== seifert1988"
source ./env.sh
OUT=.lake/build/lib/lean
mkdir -p "$OUT/Seifert1988" logs
ORDER="Seifert1988.Seifert_Enonces Seifert1988.Algebre Seifert1988.Dynamique Seifert1988.Corollaires Seifert1988.Voisins
Seifert1988.Axiomes"
for m in $ORDER; do
  p="${m//.//}"
  printf '%-30s ' "$m"
  start=$SECONDS
  if lean -o "$OUT/$p.olean" "$p.lean" > "logs/$m.log" 2>&1; then
    echo "ok ($((SECONDS - start)) s)"
  else
    echo "FAILED"; cat "logs/$m.log"; exit 1
  fi
  if grep -Eq "declaration uses .sorry." "logs/$m.log"; then
    echo "CHECK FAILED: sorry in $m"; cat "logs/$m.log"; exit 1
  fi
done
python3 - logs/Seifert1988.Axiomes.log "$EXPECTED" <<'PY'
import re, sys
ok = {"propext", "Classical.choice", "Quot.sound"}
NAMES = ["Seifert." + s + "_thm" for s in """f_maps d_neg d_perm formula_1_2 formula_1_2' lengthVector_pos thm1a_unique
thm1a_rotate thm1b thm1b_single free_essential examples remark_constant printed_e_reverse printed_e_examples
thm1b_printed_false thm1b_reversed cor1_difference_printed cor1_difference cor1_printed_false cor1_divides near_miss
cor1_exact cor1_exact_anywhere solution_gives_cycle cor2_plus cor2_minus gersonides_plus gersonides_minus thm2 thm2_plus
thm2_printed_false thm2_reversed""".split()]
bad, names = [], []
expected = int(sys.argv[2])
if len(set(NAMES)) != expected:
    bad.append(f"NAMES lists {len(set(NAMES))} theorems, EXPECTED is {expected}")
for f in sys.argv[1:2]:
    text = open(f).read()
    if re.search(r"(?m)^\S+:\d+:\d+: error", text):
        bad.append(f + ": error")
    for name, axs in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
        names.append(name)
        extra = {a.strip() for a in axs.split(",")} - ok
        if extra:
            bad.append(f"{name}: {sorted(extra)}")
    names += re.findall(r"'([^']+)' does not depend on any axioms", text)
n = len(names)
print(f"{n} axiom reports read")
if n != expected:
    bad.append(f"expected {expected} axiom reports, read {n}")
if sorted(names) != sorted(NAMES):
    bad.append(f"missing: {sorted(set(NAMES) - set(names))}; unexpected or repeated: "
               f"{sorted(set(n_ for n_ in names if names.count(n_) > 1 or n_ not in NAMES))}")
if bad:
    print("CHECK FAILED:", *bad, sep="\n  ")
    sys.exit(1)
print("all axiom reports within [propext, Classical.choice, Quot.sound]")
PY
