.. raw:: html

   Libertas Andrews–Curtis — Documentation

Results
=======

*Status: Active reference · Co-authored with Libertas Superintelligence © · © 2026 Libertas Technology Group Limited.*

The corpus carries two result sets, and this page keeps them apart. The ordinary AC table records the declarations accepted for the ordinary conjecture. The Stable AC table records the declarations accepted for the stable track. An entry in either table carries the status of that entry only. No entry in either table is a proof of `AC.Conjecture` or of `AC.StableConjecture`.

The ordinary AC track
---------------------

.. list-table::
   :widths: 26 40 20 14
   :header-rows: 1

   * - Result
     - Declaration
     - Source
     - Status
   * - Official statement
     - ``AC.Conjecture``
     - ``lean/AC.lean:55-57``
     - Verified copy
   * - Move grammar
     - ``AC.Step``, ``AC.Reachable``
     - ``lean/AC.lean:36-50``
     - Exact
   * - G1 exponent span
     - ``AC.Invariant.expSpan_eq_top_of_presents``
     - ``lean/AcInvariant.lean:243``
     - Closed
   * - G3 signed permutations
     - ``AC.ProofAttempt.signedPermutation_reachable_standard``
     - ``lean/AcProof.lean:338``
     - Closed
   * - G4 triviality preservation
     - ``AC.ProofAttempt.presents_of_step``
     - ``lean/AcProof.lean:483``
     - Closed
   * - AC ↔ hterm
     - ``AC.ProofAttempt.conjecture_iff_terminal``
     - ``lean/AcProof.lean:368``
     - Closed
   * - Standard triviality
     - ``AC.Base.presentsTrivialGroup_standard``
     - ``lean/AcBase.lean:30``
     - Accepted
   * - Rank-two A7
     - ``AC.Euclid.abelianTerminal_reachable_of_expSpan_top``
     - ``lean/AcEuclid.lean:338``
     - Accepted
   * - A7-general
     - ``AC.EuclidGeneral.abelianTerminal_reachable_of_expSpan_top_general``
     - ``lean/AcEuclidGeneral.lean:849``
     - Accepted
   * - AK(3) triviality
     - ``AC.Ak3.ak3_presentsTrivial``
     - ``lean/Ak3.lean:37``
     - Accepted
   * - A9 rank reduction
     - ``AC.RankReduction.rankReduction``
     - ``lean/AcRankReduction.lean:314``
     - Accepted
   * - A10 assembly
     - ``AC.Final.conjecture_iff_A8``
     - ``lean/AcFinal.lean:54``
     - Accepted; A8 ↔ AC
   * - AK(3) PSL no-go
     - ``AC.Ak3Separation.pslIndexSeparation_false``
     - ``lean/Ak3Separation.lean:248``
     - Pruned
   * - AK(3) invariant-family no-go
     - ``AC.Ak3Invariant.finiteQuotient_cannot_separate``; ``AC.Ak3Invariant.groupInvariant_ak3_eq_standard``
     - ``lean/Ak3Invariant.lean:302``; ``:331``
     - Pruned
   * - Quotient index
     - ``AC.Quotient.psl_index_separates``
     - ``lean/AcQuotient.lean:124``
     - Accepted
   * - Branch B determinant
     - ``AC.BranchB.expDeterminant_eq_pm_one_of_presents``
     - ``lean/BranchB.lean:195``
     - Closed
   * - Branch C cocommutativity
     - ``AC.BranchC.not_cocommutative_of_presents``
     - ``lean/BranchC.lean:171``
     - Closed
   * - Branch C winding domain
     - ``AC.BranchC.winding_domain_empty_on_trivial``
     - ``lean/BranchC.lean:202``
     - Closed

The open input on this track is A8: every abelian-terminal trivial presentation reaches a signed permutation. ``AC.Final.conjecture_iff_A8`` proves that A8 is equivalent to ``AC.Conjecture``. The equivalence is a reduction of the target; it is not a proof of the target.

The Stable AC track
-------------------

.. list-table::
   :widths: 26 40 20 14
   :header-rows: 1

   * - Result
     - Declaration
     - Source
     - Status
   * - Stable statement
     - ``AC.StableConjecture``
     - ``lean/AC.lean:110-112``
     - Stated; open
   * - Stable move grammar
     - ``AC.BranchD.StableAcMove.stableStep_iff``
     - ``lean/BranchD.lean:77``
     - Closed
   * - Rank accounting
     - ``AC.BranchD.rankOf_stableStep``
     - ``lean/BranchD.lean:102``
     - Closed
   * - Standard to empty
     - ``AC.BranchD.standard_stableReachable_empty``
     - ``lean/BranchD.lean:160``
     - Closed
   * - Empty to standard
     - ``AC.BranchD.empty_stableReachable_standard``
     - ``lean/BranchD.lean:174``
     - Closed
   * - Terminal equivalence
     - ``AC.BranchD.stableReachable_standard_iff_empty``
     - ``lean/BranchD.lean:192``
     - Closed
   * - Empty-terminal form
     - ``AC.BranchD.stableConjecture_iff_empty_terminal``
     - ``lean/BranchD.lean:203``
     - Closed
   * - Stabilization invariance
     - ``AC.BranchD.stableReachable_empty_stabilize_iff``
     - ``lean/BranchD.lean:216``
     - Closed
   * - Covered class
     - ``AC.BranchD.stableReachable_empty_of_reachable_standard``
     - ``lean/BranchD.lean:235``
     - Closed
   * - Stable descent
     - ``AC.BranchD.stableReachable_empty_of_stableReachable_of_reachable``
     - ``lean/BranchD.lean:242``
     - Closed
   * - Ordinary implies stable
     - ``AC.Conjecture.stable``
     - ``lean/AC.lean:141``
     - Closed; conditional on AC
   * - Stable projection
     - ``AC.BranchD.StableImpliesOrdinary``
     - ``lean/BranchD.lean:255``
     - Definition; open obligation
   * - Stable-invariant no-go
     - ``AC.StableCounterexample.ak3_separation_hypothesis_false``
     - ``lean/AcStableCounterexample.lean:287``
     - Pruned
   * - Stable abelianization no-go
     - ``AC.StableInvariant.ak3_separation_hypothesis_false``
     - ``lean/AcStableInvariant.lean:415``
     - Pruned
   * - Stable order/cyclicity no-go
     - ``AC.StableInvariant2.ak3_separation_hypothesis_false``
     - ``lean/AcStableInvariant2.lean:227``
     - Pruned
   * - One-stabilization projection
     - ``AC.StableProjection.one_stabilization_projection_refuted``
     - ``lean/AcStableProjection.lean:214``
     - Refuted for nontrivial presentations; trivial-presentation projection open
   * - Trivial projection reduction
     - ``AC.StableTrivial.trivialProjection_iff_aboveOne``
     - ``lean/AcStableTrivial.lean:307``
     - Accepted; rank one closed; n ≥ 2 open
   * - Stable reduction
     - ``AC.BranchD.conjecture_iff_stable_and_projection``
     - ``lean/BranchD.lean:282``
     - Closed; AC ↔ Stable AC ∧ projection

The last row is the exact relation between the tracks. The ordinary conjecture is equivalent to the stable conjecture together with the projection principle. The projection principle is stated and not proved, so the equivalence moves the open work; it does not remove it.

The stable cohort record
------------------------

``lean/BranchD3.lean`` records the scored cohort: 10,115 rows, 7,443 solved, and 2,672 unsolved (``lean/BranchD3.lean:50-56``). ``lean/BranchD4.lean`` records the search over the unsolved rows at depth 32 and width 1,000; the measured candidate cohort is empty (``lean/BranchD4.lean:171-181``). The cohort is finite evidence about the projection principle. A search boundary is not a counterexample, and an empty candidate cohort is not a proof of the universal statement.
