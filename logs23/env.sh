#!/usr/bin/env bash
# Source this file: sets LEAN_PATH to the one of ../steiner1978 (Mathlib v4.34.0 and the Steiner 1978 modules,
# built by ../steiner1978/check.sh), followed by this folder's build directory. Only ../steiner1978 needs
# Mathlib's prebuilt cache (`lake exe cache get` there); this folder uses no Lake package of its own.
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
export LEAN_PATH="$(cd "$here/../steiner1978" && lake env printenv LEAN_PATH):$here/.lake/build/lib/lean"
