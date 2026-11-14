# Contributing

## Before a pull request

1. `lake build` succeeds at the pinned toolchain.
2. `scripts/verify_corpus.sh` exits 0.
3. No `sorry` and no new `axiom`. Axioms stay within
   `{propext, Classical.choice, Quot.sound}`.
4. The pull request template carries a falsifier: the observation that would
   defeat the claim being added.

## Review rule

The author of a change does not sign it. A verifier reads the change and the
check independently and records PROCEED or LOOP_BACK.

## Prose

Every numeric claim carries the command that reproduces it. A number that exists
only in prose is removed or replaced with the command output.

## Licence

Contributions are accepted under the repository licence. Vendored material keeps
its own notice in the file header.
