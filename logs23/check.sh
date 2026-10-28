#!/usr/bin/env bash
# Re-check the logs23 formalisation, file by file, on Lean 4.34.0 + Mathlib v4.34.0 (needs python3).
# Prerequisite, once: in ../steiner1978, `lake exe cache get` (prebuilt Mathlib; nothing of Mathlib is recompiled).
# This folder has no Lake package of its own: env.sh takes LEAN_PATH from ../steiner1978. `lake build` is not used.
# 1. The sources are checked against SHA256SUMS.
# 2. ../steiner1978/check.sh is run: it re-checks Steiner 1978 and builds the modules imported here.
# 3. Each file of Logs23/ is compiled with `lean -o`, in dependency order; the check fails on any error and on any
#    warning "declaration uses `sorry`". (Warnings "exponent ... exceeds the threshold 256" and deprecation warnings
#    are expected.)
# 4. The `#print axioms` output of Logs23/Axiomes.lean is read: the check fails unless the reports are exactly those
#    of the EXPECTED theorems listed in NAMES below (the 14 frozen statements and `widths`), or if one of them depends
#    on an axiom other than propext, Classical.choice, Quot.sound (this also rules out sorryAx and the auxiliary
#    axiom that native_decide adds on Lean 4.34).
set -euo pipefail
cd "$(dirname "$0")"
EXPECTED=15
if command -v sha256sum > /dev/null 2>&1; then sha256sum --quiet -c SHA256SUMS; else shasum -a 256 --quiet -c SHA256SUMS; fi
echo "SHA256SUMS: all sources match"
echo "== ../steiner1978/check.sh"
../steiner1978/check.sh
echo "== logs23"
source ./env.sh
OUT=.lake/build/lib/lean
mkdir -p "$OUT/Logs23" logs
ORDER="Logs23.Logs23_Enonces Logs23.TwoLog_Enonces Logs23.Encadrements Logs23.Pont Logs23.Principal
Logs23.CauchyBinet Logs23.GenVandermonde Logs23.ExpKernel Logs23.Confluence Logs23.Interpolation Logs23.Proposition
Logs23.Constantes Logs23.TwoLog Logs23.Axiomes"
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
python3 - logs/Logs23.Axiomes.log "$EXPECTED" <<'PY'
import re, sys
ok = {"propext", "Classical.choice", "Quot.sound"}
NAMES = ["Logs23." + s for s in """bridge_gap_thm bridge_value_thm lam_lower_bridge_thm steiner_bridge_thm
steiner_cycle_bridge_thm reduction_thm two_log_lower_thm lam_lower_large_thm lam_lower_thm steiner_nh_thm
steiner_int_nh_thm steiner_cycle_nh_thm steiner_cycle_int_nh_thm tstar_circuit_nh_thm widths""".split()]
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
