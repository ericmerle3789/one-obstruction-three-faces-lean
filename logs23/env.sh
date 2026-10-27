#!/usr/bin/env bash
# Source this file (from bash, or from any shell after `cd logs23`): sets LEAN_PATH to this folder's build directory,
# followed by the LEAN_PATH of ../steiner1978 (Mathlib v4.34.0 and the Steiner 1978 modules, built by
# ../steiner1978/check.sh). Only ../steiner1978 needs Mathlib's prebuilt cache (`lake exe cache get` there); this
# folder uses no Lake package of its own.
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
steiner_path="$(cd "$here/../steiner1978" && lake env printenv LEAN_PATH)" || { echo "env.sh: lake env failed in ../steiner1978" >&2; return 1 2>/dev/null || exit 1; }
export LEAN_PATH="$here/.lake/build/lib/lean:$steiner_path"
