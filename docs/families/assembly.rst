.. raw:: html

   Libertas Andrews–Curtis — Documentation

Assembly
========

*Status: Active reference · Co-authored with Libertas Superintelligence © · © 2026 Libertas Technology Group Limited.*

The assembly family walks the nielsen result up to the conjecture.

Entry theorem
-------------

``AC.A8TailMinimal.a8_rank_two_of_tailMinimalStatement`` at ``lean/AcA8TailMinimal.lean:587`` proves that the tail-minimal statement gives A8 at rank two. ``AC.A8Assembly.tailMinimalStatement_of_uniformPivot`` at ``lean/AcA8Assembly.lean:116`` proves that the uniform pivot statement gives the tail-minimal statement.

Files
-----

``AcA8Reachability.lean`` holds the reachability lemmas. ``AcA8PivotReduction.lean`` holds the pivot reduction. ``AcA8TailMinimal.lean`` holds the tail-minimal statement and the rank-two theorem. ``AcA8CyclicBridge.lean`` holds the cyclic bridge. ``AcA8Assembly.lean`` composes the chain.

What the family establishes
---------------------------

Three implications, each kernel-checked:

1. the uniform pivot statement implies the tail-minimal statement,
2. the tail-minimal statement implies A8 at rank two,
3. A8 at rank two is the conjecture through ``conjecture_iff_A8``.

The composition is the chain the README draws. It is complete up to one hypothesis.

The open input
--------------

``HighMeasureDescent`` is the only unproved target-level statement. It is stated at ``lean/NielsenSliceBridge.lean:69`` and is not proved in this corpus. A proof of it, or a proof that it is false with a witness, would settle the chain at this level. Two further inputs are open above it: `measure12_ordered_classification` at `lean/NielsenMeasure12Cover.lean:200`, and the rank lift at `lean/AcRankReduction.lean:314`, which is proved but not composed into an all-rank theorem.
