#!/usr/bin/env bash
# Source this file (from bash, or from any shell after `cd sdw2005`): sets LEAN_PATH to this folder's build directory,
# then ../logs23's build directory, then the LEAN_PATH of ../steiner1978 (Mathlib v4.34.0 and the Steiner 1978 modules).
# This folder uses no Lake package of its own; ../logs23/check.sh builds the modules of ../logs23 imported here.
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
steiner_path="$(cd "$here/../steiner1978" && lake env printenv LEAN_PATH)" || { echo "env.sh: lake env failed in ../steiner1978" >&2; return 1 2>/dev/null || exit 1; }
export LEAN_PATH="$here/.lake/build/lib/lean:$here/../logs23/.lake/build/lib/lean:$steiner_path"
