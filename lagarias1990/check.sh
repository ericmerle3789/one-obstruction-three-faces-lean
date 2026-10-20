#!/usr/bin/env bash
# Re-check the Lagarias 1990 formalisation, file by file, on Lean 4.34.0 + Mathlib v4.34.0.
# Prerequisite, once:  lake exe cache get   (downloads the prebuilt Mathlib; nothing of Mathlib is recompiled).
# Each file is compiled with `lake env lean -o`, in dependency order; then the `#print axioms` output of
# Lagarias/Axiomes.lean is read: the check fails if any theorem depends on an axiom other than
# propext, Classical.choice, Quot.sound (this also rules out sorryAx and Lean.ofReduceBool, i.e. native_decide),
# or if the number of axiom reports is not EXPECTED. The sources are first checked against SHA256SUMS.
set -euo pipefail
cd "$(dirname "$0")"
EXPECTED=61
if command -v sha256sum > /dev/null 2>&1; then sha256sum --quiet -c SHA256SUMS; else shasum -a 256 --quiet -c SHA256SUMS; fi
echo "SHA256SUMS: all sources match"
OUT=.lake/build/lib/lean
mkdir -p "$OUT/Labo" "$OUT/OneObstruction" "$OUT/Lagarias" logs
ORDER="Labo.Blueprint Labo.S2_Pont OneObstruction.ContentDescent Labo.HH1997_Enonces OneObstruction.TransportRecurrence
Labo.HH1997_Preuves Lagarias.L1990_Enonces Lagarias.L2_Preuves Lagarias.L3_Preuves Lagarias.L4_Preuves
Lagarias.Tables_Enonces Lagarias.Tables Lagarias.L1990b_Enonces Lagarias.L3b_Preuves Lagarias.L4b_Preuves
Lagarias.Addenda_Enonces Lagarias.Addenda Lagarias.Mots Lagarias.L2b_Preuves Lagarias.L4c_Preuves
Lagarias.Addenda2_Enonces Lagarias.Addenda2 Lagarias.Addenda3_Enonces Lagarias.Addenda3 Lagarias.Axiomes"
for m in $ORDER; do
  p="${m//.//}"
  printf '%-34s ' "$m"
  start=$SECONDS
  if lake env lean -o "$OUT/$p.olean" "$p.lean" > "logs/$m.log" 2>&1; then
    echo "ok ($((SECONDS - start)) s)"
  else
    echo "FAILED"; cat "logs/$m.log"; exit 1
  fi
done
python3 - logs/Lagarias.Axiomes.log "$EXPECTED" <<'PY'
import re, sys
ok = {"propext", "Classical.choice", "Quot.sound"}
n, bad = 0, []
expected = int(sys.argv[2])
for f in sys.argv[1:2]:
    text = open(f).read()
    if re.search(r"(?m)^\S+:\d+:\d+: error", text):
        bad.append(f + ": error")
    for name, axs in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
        n += 1
        extra = {a.strip() for a in axs.split(",")} - ok
        if extra:
            bad.append(f"{name}: {sorted(extra)}")
    n += len(re.findall(r"' does not depend on any axioms", text))
print(f"{n} axiom reports read")
if n != expected:
    bad.append(f"expected {expected} axiom reports, read {n}")
if bad:
    print("CHECK FAILED:", *bad, sep="\n  ")
    sys.exit(1)
print("all axiom reports within [propext, Classical.choice, Quot.sound]")
PY
