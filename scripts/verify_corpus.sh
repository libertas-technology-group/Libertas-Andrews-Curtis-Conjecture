#!/usr/bin/env bash
# Verify the Andrews-Curtis corpus.
#
# Four checks, in order, then the build. Exit non-zero on any failure.
# Usage: ./scripts/verify_corpus.sh [--no-build]
set -u
cd "$(dirname "$0")/.." || exit 2
fail=0

printf '\n== 1. open obligations =========================================\n'
holes=$(grep -rn '^[[:space:]]*sorry[[:space:]]*$' lean/*.lean 2>/dev/null | wc -l | tr -d ' ')
admits=$(grep -rn '^[[:space:]]*admit[[:space:]]*$' lean/*.lean 2>/dev/null | wc -l | tr -d ' ')
axioms=$(grep -rn '^[[:space:]]*axiom[[:space:]]' lean/*.lean 2>/dev/null | wc -l | tr -d ' ')
printf '   sorry %s   admit %s   user axiom %s\n' "$holes" "$admits" "$axioms"
if [ "$holes" != "0" ] || [ "$admits" != "0" ] || [ "$axioms" != "0" ]; then
  printf '   FAIL: open obligations present\n'; fail=1
else
  printf '   PASS: no open obligations\n'
fi

printf '\n== 2. build set against disk ===================================\n'
python3 - <<'PY'
import os, re, sys
src = open('lean/lakefile.toml').read()
m = re.search(r'globs\s*=\s*\[(.*?)\]', src, re.S)
globs = [g.strip().strip('"') for g in m.group(1).split(',') if g.strip()]
files = sorted(f[:-5] for f in os.listdir('lean') if f.endswith('.lean'))
missing = [g for g in globs if g not in files]
extra = [f for f in files if f not in globs]
print(f'   globs {len(globs)}   files on disk {len(files)}   unbuilt {len(extra)}')
if missing:
    print('   FAIL: globs without a file:', missing); sys.exit(1)
if extra:
    print('   FAIL: files outside the build set:', extra); sys.exit(1)
print('   PASS: every glob resolves and every module is built')
PY
[ $? -ne 0 ] && fail=1

printf '\n== 3. module count and naming ==================================\n'
modules=$(ls -1 lean/*.lean | wc -l | tr -d ' ')
printf '   modules: %s\n' "$modules"
bad=$(ls -1 lean/*.lean | grep -Ev '/(AC|Ac[A-Za-z0-9]*|Ak3[A-Za-z0-9]*|Branch[BCD][0-9]*|Nielsen[A-Za-z0-9]*)\.lean$' | wc -l | tr -d ' ')
if [ "$bad" != "0" ]; then printf '   FAIL: %s module names outside the family prefixes\n' "$bad"; fail=1
else printf '   PASS: every module name carries a family prefix\n'; fi

printf '\n== 4. documentation ============================================\n'
for p in README.md AGENTS.md docs/standards.rst docs/naming.rst docs/families/index.rst; do
  if [ -f "$p" ]; then printf '   present: %s\n' "$p"; else printf '   MISSING: %s\n' "$p"; fail=1; fi
done

printf '\n== 5. registry entry ===========================================\n'
if python3 -B scripts/check_registry.py; then
  printf '   PASS: challenge and solution agree\n'
else
  printf '   FAIL: registry entry\n'; fail=1
fi

printf '\n== 6. documented numbers =======================================\n'
if python3 -B scripts/check_docs_claims.py; then
  printf '   PASS: every documented number matches the tree\n'
else
  printf '   FAIL: a documented number has drifted\n'; fail=1
fi

if [ "${1:-}" != "--no-build" ]; then
  printf '\n== 7. build =====================================================\n'
  ( cd lean && lake build ) || fail=1
fi

printf '\n'
if [ "$fail" -eq 0 ]; then printf 'CORPUS VERIFIED\n'; else printf 'CORPUS FAILED\n'; fi
exit "$fail"
