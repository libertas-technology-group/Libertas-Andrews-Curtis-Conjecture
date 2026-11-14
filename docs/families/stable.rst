.. raw:: html

   Libertas Andrews–Curtis — Documentation

Stable
======

*Status: Active reference · Co-authored with Libertas Superintelligence © · © 2026 Libertas Technology Group Limited.*

The stable family studies the conjecture with one extra move: a generator and its own relator may be inserted and later deleted.

Entry theorem
-------------

``AC.BranchD.conjecture_iff_stable_and_projection`` at ``lean/BranchD.lean:282`` proves that the ordinary conjecture is equivalent to the stable conjecture together with the projection principle ``StableImpliesOrdinary``. The projection says that a stable path between presentations of the same rank yields an ordinary path.

Files
-----

``AcStableInvariant.lean`` and ``AcStableInvariant2.lean`` hold the stable invariants. ``AcStableProjection.lean`` and ``AcStableTrivial.lean`` hold the projection results, including the rank-one case and the reduction of the rank-two case to the A8 input. ``AcStableCounterexample.lean`` and ``AcStableProjectionCounterexample.lean`` hold the failure cases. ``AcStableMountain.lean``, ``AcStableMountainRankOne.lean`` and ``AcStableMountainCounterexample.lean`` hold the mountain statements. ``AcStableWitness.lean`` holds the witness forms. ``BranchD.lean``, ``BranchD2.lean``, ``BranchD3.lean`` and ``BranchD4.lean`` hold the stable route and its tests.

What the family establishes
---------------------------

The stable problem is easier at the front and harder at the back. The stable conjecture is not proved, and the projection is open. What is proved is the equivalence, so a proof of the stable conjecture together with a proof of the projection would give the ordinary conjecture outright.

Edge to the next family
-----------------------

The topology family supplies the low-dimensional invariants that the later families use to prune routes.
