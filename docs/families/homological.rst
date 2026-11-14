.. raw:: html

   Libertas Andrews–Curtis — Documentation

Homological
===========

*Status: Active reference · Co-authored with Libertas Superintelligence © · © 2026 Libertas Technology Group Limited.*

The homological family carries the Fox derivative and Britton–Schupp results.

Entry theorems
--------------

``AC.BS23Nonmetabelian.nonmetabelianQuotientSeparation_iff_bs23OrbitSeparation`` reduces the non-metabelian quotient target to the open BS(2,3) orbit separation statement. ``AC.BS23Fox.foxDeterminantUnitClaim_false`` closes the quotient-determinant unit route with a witness. ``AC.BS23Subgroup.subgroupIndexSeparation_false`` closes the subgroup-index route.

Files
-----

``AcBS23BrittonOracle.lean`` holds the Britton lemma oracle. ``AcBS23FoxDeterminant.lean`` holds the Fox determinant results. ``AcBS23NonmetabelianQuotient.lean`` holds the quotient reduction. ``AcBS23SubgroupIndex.lean`` holds the index results. ``AcBS23HNN.lean`` holds the HNN extension. ``AcBS23Conjugacy.lean`` holds the conjugacy results.

What the family establishes
---------------------------

Two routes are closed by theorem rather than by a failed attempt: the Fox determinant unit route and the subgroup-index route. The non-metabelian target is reduced to one open separation statement, which is stated and not proved. The metabelian case is not addressed by a theorem in this family.

Edge to the next family
-----------------------

The nielsen family takes the measure argument. It needs the pruning results from both earlier algebraic families, because it rules out group-invariant separators of every kind before it turns to the measure.
