#!/bin/bash
# Usage: bash check-portable.sh LEAN_BINARY ACCEPTED_SOURCE_OBJECT_DIR MATHLIB_PACKAGES_DIR MODULE
# Reuses already-qualified dependencies; does not install or rebuild them.
set -euo pipefail
LEAN_BINARY=$1
SOURCE_OBJECTS=$2
PACKAGES=$3
MODULE=$4
HERE=$(cd -- "$(dirname -- "$0")" && pwd)
export LEAN_PATH="$HERE:$SOURCE_OBJECTS"
for d in "$PACKAGES"/*/.lake/build/lib/lean; do LEAN_PATH="$LEAN_PATH:$d"; done
cd "$HERE"
exec "$LEAN_BINARY" -o "${MODULE%.lean}.olean" "$MODULE"
