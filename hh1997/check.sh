#!/usr/bin/env bash
# Re-check the Halbeisen–Hungerbühler 1997 formalisation, file by file, on Lean 4.34.0 + Mathlib v4.34.0.
# Prerequisite, once:  lake exe cache get   (downloads the prebuilt Mathlib; nothing of Mathlib is recompiled).
# Each file is compiled with `lake env lean -o`, in dependency order; then the `#print axioms` output of the
# nine *_Axiomes files is read: the check fails if any theorem depends on an axiom other than
# propext, Classical.choice, Quot.sound (this also rules out sorryAx and Lean.ofReduceBool, i.e. native_decide).
set -euo pipefail
cd "$(dirname "$0")"
OUT=.lake/build/lib/lean
mkdir -p "$OUT/Labo" "$OUT/OneObstruction" logs
ORDER="Labo.Blueprint Labo.S2_Pont OneObstruction.ContentDescent Labo.HH1997_Enonces OneObstruction.TransportRecurrence
Labo.HH1997_Preuves Labo.HH1997_Axiomes Labo.HH1997b_Enonces Labo.HH1997b_Preuves Labo.HH1997b_Axiomes
Labo.HH1997c_Enonces Labo.HH1997c_Preuves Labo.HH1997c_Axiomes Labo.HH1997d_Enonces Labo.HH1997d_Preuves
Labo.HH1997d_Axiomes Labo.HH1997d_Pont_Enonces Labo.HH1997d_Pont_Preuves Labo.HH1997d_CF_Preuves
Labo.HH1997d_Fin_Preuves Labo.HH1997d_Fort_Enonces Labo.HH1997d_Fort_Preuves Labo.HH1997d_Fin_Axiomes
Labo.HH1997d_Fort_Axiomes Labo.HH1997d_Pont_Axiomes Labo.HH1997e_Enonces Labo.HH1997e_Preuves
Labo.HH1997e_Axiomes Labo.HH1997f_Enonces Labo.HH1997f_Mots Labo.HH1997f_Calcul Labo.HH1997f_Preuves
Labo.HH1997f_Axiomes"
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
python3 - logs/Labo.*_Axiomes.log <<'PY'
import re, sys
ok = {"propext", "Classical.choice", "Quot.sound"}
n, bad = 0, []
for f in sys.argv[1:]:
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
if bad:
    print("NON-STANDARD AXIOMS OR ERRORS:", *bad, sep="\n  ")
    sys.exit(1)
print("all axiom reports within [propext, Classical.choice, Quot.sound]")
PY
