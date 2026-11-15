The Universal Laws
==================

*Status: the page holds two tables, the kernel-verified laws and the open
hypotheses, and each row states its own. The open hypotheses carry a
proposition of type ``Prop`` and no proof.*

Each row states a law at every rank for every tuple in its stated class. The
module and the declaration are named so a reader can open the source. The two
rows marked open hypothesis state a proposition and carry no proof; every other
row carries a proof.

Kernel-verified universal laws
------------------------------

Each law below is proved, and each declaration is named so a reader can open the source.

.. list-table::
    :header-rows: 1
    :widths: 22 34 26 18

    * - Law
      - Statement
      - Declaration
      - Status
    * - Relation-subgroup collapse
      - a presentation of the trivial group has the whole free group as the normal closure of its relators
      - ``AC.RelationCollapse.relationSubgroup_eq_top`` (``lean/AcRelationModuleCollapse.lean:33``)
      - proved
    * - Exponent span
      - on that class the exponent span of the relators is the whole lattice
      - ``AC.Invariant.expSpan_eq_top_of_presents`` (``lean/AcInvariant.lean:247``)
      - proved
    * - Relation module
      - on that class the relation module is the exponent-vector group
      - ``AC.RelationCollapse.relationModule_equiv_expVec`` (``lean/AcWindingCollapse.lean:96``)
      - proved
    * - Separation
      - no invariant through that module separates an AC-equivalent pair
      - ``AC.RelationCollapse.relationModuleInvariant_cannot_separate`` (``lean/AcRelationModuleCollapse.lean:65``)
      - proved
    * - Signed row law
      - under each move the determinant of the exponent matrix changes by at most a sign
      - ``AC.EuclidGeneral.expMatrix_det_step`` (``lean/AcExpMatrixLaw.lean:51``)
      - proved
    * - Span stability
      - insertion and deletion preserve whether the span is the whole lattice
      - ``AC.StabilityTransport.stableStep_expSpan_top`` (``lean/AcStabilityTransport.lean:223``)
      - proved
    * - Detour impossibility
      - no function of graph distance returns the detour width
      - ``AC.DetourWidth.detourWidth_independent_of_graphDist`` (``lean/AcDetourWidth.lean:266``)
      - proved
    * - Power family
      - ``(x·yⁿ, y)`` reaches the standard pair for every n
      - ``AC.PowFamily.reachable_P`` (``lean/AcPowFamily.lean``)
      - proved
    * - Right family
      - ``(x, y·xⁿ)`` reaches the standard pair for every n
      - ``AC.RightFamily.reachable_Q`` (``lean/AcRightFamily.lean``)
      - proved
    * - Finite-quotient blindness
      - no finite quotient separates
      - ``AC.Ak3Invariant.finiteQuotient_cannot_separate`` (``lean/Ak3Invariant.lean:306``)
      - proved
    * - Energy barrier
      - no positive measure decreases under every single move
      - ``AC.Invariant.no_strictly_decreasing_measure`` (``lean/AcInvariant.lean:216``)
      - proved

Open hypotheses
---------------

The two statements below are propositions of type Prop and carry no proof.

.. list-table::
    :header-rows: 1
    :widths: 22 34 26 18

    * - Law
      - Statement
      - Declaration
      - Status
    * - High-measure descent
      - every tuple above the high-measure threshold descends
      - ``HighMeasureDescent`` (``lean/NielsenSliceBridge.lean:73``)
      - **open hypothesis**
    * - Tail-minimal form
      - every class reaches a tail-minimal normal form
      - ``TailMinimalStatement`` (``lean/AcA8TailMinimal.lean:555``)
      - **open hypothesis**

The registry entry
------------------

``Challenge.lean`` restates eight declarations against Mathlib only, because the
registry caps the challenge module's imports: seven of the laws above plus the
exponent-vector law that the collapse depends on. ``Solution.lean`` proves the
same eight. ``comparator.json`` names them and the three permitted
axioms.
