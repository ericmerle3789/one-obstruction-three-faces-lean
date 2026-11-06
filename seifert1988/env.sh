#!/usr/bin/env bash
# Source this file (from bash, or from any shell after `cd seifert1988`): sets LEAN_PATH to this folder's build directory,
# followed by the LEAN_PATH of ../logs23 (Mathlib v4.34.0, Steiner 1978 and logs23, built by ../logs23/check.sh).
# Only ../steiner1978 needs Mathlib's prebuilt cache (`lake exe cache get` there); this folder has no Lake package of its own.
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
logs23_path="$(cd "$here/../logs23" && source ./env.sh && printf '%s' "$LEAN_PATH")" || { echo "env.sh: ../logs23/env.sh failed" >&2; return 1; }
export LEAN_PATH="$here/.lake/build/lib/lean:$logs23_path"
