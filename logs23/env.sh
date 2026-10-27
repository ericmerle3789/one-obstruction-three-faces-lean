#!/usr/bin/env bash
# Source this file: sets LEAN_PATH to Mathlib v4.34.0 (shared packages), this folder's build, and the
# already-built Steiner 1978 modules of ../steiner1978 (run ../steiner1978/check.sh first on a fresh clone).
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
export LEAN_PATH="$(cd "$here" && lake env printenv LEAN_PATH):$here/../steiner1978/.lake/build/lib/lean"
