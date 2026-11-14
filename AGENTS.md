# AGENTS.md — the Andrews–Curtis corpus

This repository is a contribution to the SAIR Andrews–Curtis challenge, Proof
Track only. It contains a Lean 4 corpus that reduces the ordinary conjecture to a
small set of named open statements and proves the carrying chain at rank two. It
contains no search code, no campaign notes, and no claim that the conjecture is
settled.

## The challenge

Andrews and Curtis asked in 1965 whether every balanced presentation of the
trivial group can be transformed into the standard presentation by invert,
multiply and conjugate. The Proof Track accepts a proof or a disproof of the
ordinary conjecture or of the stable conjecture.

## What this corpus establishes

| statement | file | status |
|---|---|---|
| the conjecture is equivalent to A8 over every rank | `lean/AcFinal.lean:54` | proved |
| A8 at rank two follows from the tail-minimal statement | `lean/AcA8TailMinimal.lean:587` | proved |
| the tail-minimal statement follows from the uniform pivot statement | `lean/AcA8Assembly.lean:116` | proved |
| the low measure case follows from the measure-twelve slice | `lean/NielsenLowMeasureFinal.lean:47` | proved, conditional on the slice |
| the measure-twelve base, `measure12_ordered_classification` | `lean/NielsenMeasure12Cover.lean:200` | open, a definition |
| the high-measure descent | `lean/NielsenSliceBridge.lean:69` | open, a definition |
| the rank lift from two to every rank | `lean/AcRankReduction.lean:314` | interface stated, not composed |

The exact statement of the reduction, with the two primitive open inputs named, is in
the README. Two derived definitions, `measure12_covers_witness` and
`bothLong_measure12_uniform`, follow from the base. Nothing in this repository is presented as a proof of the conjecture.

## How to read the corpus

1. `README.md`, the chain and the open inputs.
2. `docs/standards.rst`, the five rules the build set follows.
3. `docs/naming.rst`, the module and declaration naming rules.
4. `docs/families/`, one page per family with its entry theorem.
5. `docs/proof_track.rst`, the proof-track argument and the eliminated routes.

## How to verify

```bash
./scripts/verify_corpus.sh
```

The command checks for `sorry`, `admit` and user axioms, checks that the build set
matches disk, checks module naming, checks the documentation files, and then runs
`lake build`. It exits non-zero on any failure.

## Standards

Every built module states its subject in the docstring and carries no open
obligation. Declaration names follow the convention recorded in
`docs/naming.rst`: `lowerCamelCase`, with underscores where a long name needs
segmentation. Several modules record their axiom record in the docstring and with
`#print axioms`; the axiom record is not yet uniform across the build set, and
`docs/standards.rst` records that gap. The family labels describe subject matter.
The module import graph is acyclic, and `docs/standards.rst` states the direction
of the dependencies rather than a strict layering.

## Review and feedback

Review is invited from mathematicians and from machine agents. A useful report
names the file and line, states the claim that fails, and says whether the
failure is in a statement, a name, or a proof. Reports about the open inputs
are the most valuable, and reports about an overstatement in the documentation are
equally welcome.

Findings can be raised through the repository's issue tracker. This repository is
private and is shared for review; please do not redistribute it.

## What this repository does not contain

The search instruments and the retired exploration branches live in the
research workspace and are excluded here
by design. This repository carries the proof and the documentation of the proof.
