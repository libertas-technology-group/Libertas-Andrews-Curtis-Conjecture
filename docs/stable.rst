.. raw:: html

   Libertas Andrews–Curtis — Documentation

The stable track
================

*Status: Active reference · Co-authored with Libertas Superintelligence © · © 2026 Libertas Technology Group Limited.*

Stable Andrews–Curtis is a separate track. It shares the ordinary move relation and adds two rank-changing moves: insert an isolated generator–relator pair, and remove such a pair. The rank may change along the path and there is no bound on the intermediate rank. The exact statement is on :doc:`statements` and in ``lean/AC.lean:114-112``.

What the stable track proves
----------------------------

The stable track proves the move grammar, the rank accounting, and the equivalence of the two terminal states. The stable move grammar ``AC.BranchD.StableAcMove`` generates exactly the official ``AC.StableStep`` relation; ``stableStep_iff`` is the two-direction proof (``lean/BranchD.lean:81``). Every stable step preserves the rank or changes it by one (``rankOf_stableStep``, ``lean/BranchD.lean:106``).

The standard tuple and the empty presentation are stable-reachable from each other at every rank (``standard_stableReachable_empty`` and ``empty_stableReachable_standard``, ``lean/BranchD.lean:164`` and ``:174``). Consequently the stable target may be stated against either endpoint, and ``stableConjecture_iff_empty_terminal`` records the equivalence (``lean/BranchD.lean:207``).

Stable solvability is invariant under adding or removing one generator–relator pair (``stableReachable_empty_stabilize_iff``, ``lean/BranchD.lean:220``). Every presentation that is ordinarily reachable to the standard tuple is stably trivial (``stableReachable_empty_of_reachable_standard``, ``lean/BranchD.lean:239``). The signed-permutation class is therefore covered on the stable track, because the ordinary track reaches it by ``AC.ProofAttempt.signedPermutation_reachable_standard``.

The relation to ordinary AC
---------------------------

The implication runs from ordinary AC to stable AC: ``AC.Conjecture.stable`` proves ``AC.Conjecture → AC.StableConjecture`` (``lean/AC.lean:145``). The converse is the projection principle ``AC.BranchD.StableImpliesOrdinary``, which states that stable solvability at the rank of a trivial presentation implies ordinary solvability at that rank (``lean/BranchD.lean:259``).

``AC.BranchD.conjecture_iff_stable_and_projection`` proves

.. code-block:: text

   AC.Conjecture ↔ AC.StableConjecture ∧ AC.BranchD.StableImpliesOrdinary

at ``lean/BranchD.lean:286``. The projection principle is the residual obligation. The stable route does not prove it: a stable path may leave the rank and return, and the ordinary move relation is typed at one rank, so a rank excursion has no ordinary reading.

What remains open
-----------------

1. ``AC.StableConjecture`` is not proved.
2. ``AC.BranchD.StableImpliesOrdinary`` is not proved.
3. A stable counterexample is not exhibited. ``AC.StableCounterexample`` is
   defined at ``lean/AC.lean:124``, and
   ``not_stable_conjecture_iff_counterexample`` relates it to the negation of the
   stable statement (``lean/AC.lean:127``).

The relation to A8
------------------

A8 is equivalent to the ordinary conjecture: ``AC.Final.conjecture_iff_A8`` proves ``A8 ↔ AC.Conjecture`` (``lean/AcFinal.lean:58``). A8 is not equivalent to the stable conjecture. If A8 were closed and the ordinary conjecture followed, ``AC.Conjecture.stable`` would give the stable conjecture as a corollary. That chain is conditional at every step and is not a proof in this repository.

The cohort record
-----------------

``lean/BranchD3.lean`` records 10,115 scored rows, 7,443 solved and 2,672 unsolved (``lean/BranchD3.lean:54-56``). ``lean/BranchD4.lean`` records the depth-32, width-1,000 search over the unsolved rows and an empty measured candidate cohort (``lean/BranchD4.lean:175-181``). The record is finite evidence for the projection question. It is not a proof of the universal statement and it does not establish a counterexample.
