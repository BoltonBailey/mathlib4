#!/usr/bin/env bash
# Scan Mathlib module by module for functions whose (uncurried) input and output types are
# countable, appending results to a TSV file as each module finishes. See
# `scripts/CountableIO.lean`.
#
# Usage: scripts/countable_io_scan.sh OUT.tsv [MODULE_PREFIX]
#
# MODULE_PREFIX defaults to `Mathlib`. The scan is resumable: modules already listed in
# OUT.tsv.done are skipped, so rerunning after an interruption continues where it stopped.
# Delete OUT.tsv and OUT.tsv.done to start over.
set -euo pipefail

if [[ $# -lt 1 ]]; then
  echo "usage: $0 OUT.tsv [MODULE_PREFIX]" >&2
  exit 1
fi

out_dir=$(cd "$(dirname "$1")" && pwd)
out="$out_dir/$(basename "$1")"
prefix=${2:-Mathlib}
root=$(cd "$(dirname "$0")/.." && pwd)

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
{
  cat "$root/scripts/CountableIO.lean"
  printf '\n#countable_io_scan_modules "%s" %s\n' "$out" "$prefix"
} > "$tmp/CountableIOScan.lean"

cd "$root"
lake env lean "$tmp/CountableIOScan.lean"
