#!/usr/bin/env bash
# Standard Lean/PATH honors lean-toolchain. Dependencies are local unless an
# explicit read-only cache root is selected for this invocation.
PLANARHOM_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
export LEAN_NUM_THREADS=1
export MATHLIB_CACHE_DIR="$PLANARHOM_ROOT/.cache/mathlib"
export PLGH_DEPENDENCY_ROOT="${PLGH_DEPENDENCY_ROOT:-$PLANARHOM_ROOT/.lake/packages}"
export LEAN_PATH="${PLGH_BUILD_ROOT:-$PLANARHOM_ROOT/.build}"
for dependency in "$PLGH_DEPENDENCY_ROOT"/*/.lake/build/lib/lean; do
  [ -d "$dependency" ] || continue
  LEAN_PATH="$LEAN_PATH:$dependency"
done
export LEAN_PATH
