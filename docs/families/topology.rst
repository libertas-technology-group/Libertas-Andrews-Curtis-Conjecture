.. raw:: html

   Libertas Andrews–Curtis — Documentation

Topology
========

*Status: Active reference · Co-authored with Libertas Superintelligence © · © 2026 Libertas Technology Group Limited.*

The topology family carries the low-dimensional side: the Akbulut–Kirby presentations and the Stallings orbit machinery.

Entry theorems
--------------

``AC.Ak3Separation.pslIndexSeparation_false`` at ``lean/Ak3Separation.lean:248`` proves that the AK(3) normal-closure index is one, so the PSL quotient route cannot separate the presentation. ``AC.Ak3.ak3_presentsTrivial`` at ``lean/Ak3.lean:37`` proves that AK(3) presents the trivial group.

Files
-----

``Ak3.lean`` states the presentation and its triviality. ``Ak3Invariant.lean`` and ``Ak3OrbitSeparation.lean`` hold the invariants. ``Ak3Separation.lean`` holds the separation results. ``AcStallings.lean``, ``AcStallingsInverse.lean``, ``AcStallingsTailArea.lean``, ``AcStallingsWordMeasure.lean``, ``AcStallingsExponentMeasure.lean`` and the two counterexample modules, ``AcStallingsExponentCounterexample.lean`` and ``AcStallingsTailAreaCounterexample.lean``, hold the Stallings orbit argument.

What the family establishes
---------------------------

The AK(3) separation statement itself is open. The family removes the quotient and index routes by theorem, and it supplies the Stallings machinery the later families use when they prune an orbit-based route.

Edge to the next family
-----------------------

The homological family supplies the Fox and Britton–Schupp invariants that close the remaining algebraic routes.
