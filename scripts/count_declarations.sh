#!/usr/bin/env bash
# Count every declaration line across the corpus and print the total.
# A declaration is a top-level line opening with one of the keywords below.
set -euo pipefail
cd -- "$(dirname -- "$0")/.."
grep -hE '^(theorem|lemma|def|abbrev|instance|structure|class|inductive) ' lean/*.lean | wc -l | tr -d ' '
