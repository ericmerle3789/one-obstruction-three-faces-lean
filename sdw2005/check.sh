#!/usr/bin/env bash
# Re-check the sdw2005 formalisation, file by file, on Lean 4.34.0 + Mathlib v4.34.0 (needs python3).
# Prerequisite, once: in ../steiner1978, `lake exe cache get` (prebuilt Mathlib; nothing of Mathlib is recompiled).
# This folder has no Lake package of its own: env.sh takes LEAN_PATH from ../steiner1978. `lake build` is not used.
# 1. The sources are checked against SHA256SUMS.
# 2. ../logs23/check.sh is run: it re-checks ../steiner1978 and ../logs23 and builds the modules imported here.
# 3. Each file of Sdw2005/ is compiled with `lean -o`, in dependency order; the check fails on any error and on any
#    warning "declaration uses `sorry`". (Warnings "exponent ... exceeds the threshold 256" and deprecation warnings
#    are expected.)
# 4. The `#print axioms` output of Sdw2005/Axiomes.lean is read: the check fails unless the reports are exactly those
#    of the EXPECTED theorems listed in NAMES below (the 9 frozen statements), or if one of them depends
#    on an axiom other than propext, Classical.choice, Quot.sound (this also rules out sorryAx and the auxiliary
#    axiom that native_decide adds on Lean 4.34).
set -euo pipefail
cd "$(dirname "$0")"
EXPECTED=9
if command -v sha256sum > /dev/null 2>&1; then sha256sum --quiet -c SHA256SUMS; else shasum -a 256 --quiet -c SHA256SUMS; fi
echo "SHA256SUMS: all sources match"
echo "== ../logs23/check.sh"
../logs23/check.sh
echo "== sdw2005"
source ./env.sh
OUT=.lake/build/lib/lean
mkdir -p "$OUT/Sdw2005" logs
ORDER="Sdw2005.Sdw_Enonces Sdw2005.Chaine Sdw2005.Bornes Sdw2005.Cycles Sdw2005.Sdw91_Enonces Sdw2005.Borne91 Sdw2005.Axiomes"
for m in $ORDER; do
  p="${m//.//}"
  printf '%-24s ' "$m"
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
python3 - logs/Sdw2005.Axiomes.log "$EXPECTED" <<'PY'
import re, sys
ok = {"propext", "Classical.choice", "Quot.sound"}
NAMES = ["Sdw2005." + s for s in """lemma4_thm lemma6_thm lemma7_min_thm lemma7_thm chain_K_lt_thm cycle_chain_thm
cycle_K_lt_thm chain_K_lt_91_thm cycle_K_lt_91_thm""".split()]
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
