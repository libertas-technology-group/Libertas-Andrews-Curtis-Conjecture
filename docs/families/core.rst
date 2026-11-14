.. raw:: html

   Libertas Andrews–Curtis — Documentation

Core reduction
==============

*Status: Active reference · Co-authored with Libertas Superintelligence © · © 2026 Libertas Technology Group Limited.*

The core family states the conjecture, defines the move relation, and reduces the conjecture to A8.

Entry theorem
-------------

``AC.Final.conjecture_iff_A8`` at ``lean/AcFinal.lean:54`` proves ``AC.Conjecture ↔ A8``. A8 is the statement that every balanced presentation of the trivial group that is already as straight as the move relation allows reaches the standard pair. The reduction turns a statement over all presentations into a statement over straightened ones.

Files
-----

``AC.lean`` states the conjecture and the three moves. ``AcMove.lean`` holds the move lemmas. ``AcInvariant.lean`` and ``AcQuotient.lean`` hold the invariant results, including ``psl_index_separates``. ``AcCounterexample.lean`` and ``AcMagnusCounterexample.lean`` hold the counterexample side. ``AcBase.lean``, ``AcEuclid.lean`` and ``AcEuclidGeneral.lean`` hold the base cases. ``AcRankReduction.lean`` and ``AcInduction.lean`` hold the rank reduction. ``AcTail.lean``, ``AcTailDefs.lean``, ``AcTailClass.lean``, ``AcTailExpVec.lean`` and ``AcTailGeneral.lean`` hold the tail machinery. ``BranchB.lean``, ``BranchC.lean``, ``BranchC3.lean``, ``BranchC4.lean``, ``BranchD.lean``, ``BranchD2.lean``, ``BranchD3.lean`` and ``BranchD4.lean`` hold the strategy branches that survived elimination.

Edge to the next family
-----------------------

The stable family takes ``Reachable`` and adds one move, the insertion and deletion of an isolated generator–relator pair. It asks whether the same conclusion holds with that move allowed.
