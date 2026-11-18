#!/bin/sh
# Verify the exact locally commissioned challenge and Lean toolchain.
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
exec python3 "$here/scripts/check-sources.py" --challenge-only
