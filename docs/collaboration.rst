.. raw:: html

   Libertas Andrews–Curtis — Documentation

Collaboration and review
========================

*Status: Active reference · Co-authored with Libertas Superintelligence © · © 2026 Libertas Technology Group Limited.*

The corpus follows one ownership rule and one verification rule. One writer owns each file, and the writer is not the verifier.

Ownership
---------

A file has one writer at a time. Two writers do not hold one file. The Lean modules, the documentation sources, and the build files are separate ownership units, so a change to a statement and a change to its documentation are reviewed as two artifacts.

Review
------

A fresh reader checks the artifact and its assertion before the work is reported as done. For a Lean declaration the reader checks four items:

1. the statement, read against the official statement in ``lean/AC.lean``;
2. the artifact hash;
3. the move-relation hash;
4. the axiom list, which must be a subset of ``propext``, ``Classical.choice``,
   and ``Quot.sound``.

For a documentation change the reader checks the rendered page, the toctree, the warnings-as-errors build, and the legal notice on the page. A green build is not a substitute for reading the output.

The boundary
------------

The campaign record stays outside this repository. The public proof mirror is created only after a full result and operator approval. The submission is not filed in this private corpus, and the sharing agreement is not checked here.

The documentation tree is self-contained. It names no external repository and links to none. A reader who needs a claim checks the declaration in this tree.

Reporting a defect
------------------

A defect report names the file, the line, the observed output, and the command that produced it. A report without a reachable command or a ``file:line`` reference is a question, not a defect. The fix changes the artifact the report names; a check is not removed or emptied to make a run pass.
