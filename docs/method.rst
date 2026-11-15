.. raw:: html

   Libertas Andrews–Curtis — Documentation

Method
======

*Status: Active reference · Co-authored with Libertas Superintelligence © · © 2026 Libertas Technology Group Limited.*

This page states how the corpus was produced, what the run cost, and how a reader checks it. It describes the product record. The campaign record stays in the research workspace, outside this repository.

The cognitive world model
-------------------------

A world model, in the machine-learning literature, is a predictive model of an environment that supports planning by simulation: Ha and Schmidhuber learn a compressed spatial and temporal representation of an environment and train an agent inside it, and LeCun and Fung argue that intelligence requires such predictive models rather than surface pattern matching. Operating as a fully white-box system, Libertas Superintelligence constructs world models for the specific problem or domain being addressed. In this run the world model attempted to build a map of the path to a solution.

In our proprietary implementation, the system maps the families of mathematical and scientific approaches, narrows them down systematically, and carries each one end-to-end. A route that closes becomes a kernel-checked declaration; a route that fails is either named as the exact statement still missing, or closed by a proof that it can never work, with a concrete example where one exists. The universal laws this produced are tabulated in the README with the works in whose context each law sits.

The accepted modules and the pruned routes are part of this repository. The full campaign record is kept in the research workspace and is not part of this repository. The pruning results are part of the corpus because they narrow the search: the PSL quotient index is one at AK(3), so the quotient route cannot separate the presentation (``AC.Ak3Separation.pslIndexSeparation_false``, ``lean/Ak3Separation.lean:252``); the Fox row-module invariant is false with a concrete example, so that route is closed.

The method does not replace the kernel. A generated candidate enters the corpus only when Lean accepts it under the pinned toolchain and the axiom check returns a subset of ``propext``, ``Classical.choice``, and ``Quot.sound``. A candidate that the system reports as promising but Lean does not accept remains outside the build set and is not reported as a result.

Cost and efficiency
-------------------

The accepted corpus builds over the whole build set under Lean ``4.35.0-rc2`` and Mathlib ``065356127b1dc0016f66b7283ce0ce2c4055aa55``, and ``./scripts/verify_corpus.sh`` reproduces the verdict. A job is one unit of Lean elaboration in the ``AcCorpus`` build graph; the job count changes with every module and is therefore not quoted as a fixed figure.

The repository records no metered monetary cost for the run. The campaign estimate is stated in the README as three days and approximately 50 US dollars, supplied by the owner, and this page adds no metered figure to it. The efficiency claim the record supports is bounded: the accepted declarations compile to one library target, the kernel checks each declaration once per build, and the finite stable cohort carries its own counts rather than a projected saving. The stable cohort scored 10,115 rows, solved 7,443, and left 2,672 unsolved (``lean/BranchD3.lean:54-56``); the depth-32 search over the unsolved rows returned an empty candidate cohort (``lean/BranchD4.lean:175-181``). Those counts measure a search boundary. They do not measure the cost of a proof that does not exist.

The verification loop
---------------------

The corpus follows one rule: the writer is not the verifier. One writer owns each file. A fresh reader checks the statement, the artifact hash, the move-relation hash, and the axiom list. The checks are the Lean build, the axiom print, and the documentation build with warnings treated as errors. :doc:`collaboration` states the review rules and :doc:`build` gives the commands.
