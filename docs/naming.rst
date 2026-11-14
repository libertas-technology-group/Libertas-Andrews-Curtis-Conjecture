.. raw:: html

   Libertas Andrews–Curtis — Documentation

Naming
======

*Status: Active reference · Co-authored with Libertas Superintelligence © · © 2026 Libertas Technology Group Limited.*

Names in this corpus follow one pattern per object class. The rules exist so a reader can predict a name before opening the file.

Modules
-------

A module file is named by its family prefix and its subject, in CamelCase, with no version numbers and no dates.

.. list-table::
   :widths: 20 26 54
   :header-rows: 1

   * - Family
     - Prefix
     - Examples
   * - Core reduction
     - ``AC``, ``Ac``
     - ``AC.lean``, ``AcMove.lean``, ``AcProof.lean``, ``AcFinal.lean``
   * - Stable
     - ``AcStable``
     - ``AcStableTrivial.lean``, ``AcStableProjection.lean``
   * - Topology
     - ``Ak3``, ``AcStallings``
     - ``Ak3Separation.lean``, ``AcStallingsTailArea.lean``
   * - Homological
     - ``AcBS23``
     - ``AcBS23FoxDeterminant.lean``, ``AcBS23Conjugacy.lean``
   * - Nielsen
     - ``Nielsen``, ``AcNielsen``
     - ``NielsenSliceBridge.lean``, ``AcNielsen.lean``
   * - Assembly
     - ``AcA8``
     - ``AcA8Assembly.lean``, ``AcA8TailMinimal.lean``

Branch files use ``BranchB``, ``BranchC3``, ``BranchD2`` and so on, and name the strategy letter and its position in that strategy. The exploration branches that once used the ``BranchA`` and ``BranchC2`` names are held in the research workspace and are not part of this repository.

Declarations
------------

.. list-table::
   :widths: 24 34 42
   :header-rows: 1

   * - Kind
     - Convention
     - Example
   * - theorem, lemma
     - ``lower_snake_case`` stating the claim
     - ``uniform_of_low_and_high``
   * - definition
     - ``lowerCamelCase`` naming the object
     - ``pivotState``, ``cyclicNielsenLength``
   * - inductive constructor
     - ``lowerCamelCase``
     - ``Step.inv``, ``Step.mulRight``
   * - namespace
     - family name in CamelCase
     - ``AC.Nielsen``, ``AC.BranchD``

A theorem name reads as the sentence it proves. ``conjecture_iff_A8`` reads as "the conjecture if and only if A8". ``a8_rank_two_of_tailMinimalStatement`` reads as "A8 at rank two follows from the tail-minimal statement". A name that needs a comment to explain it is renamed.

Abbreviations are restricted to ``AC``, ``A8``, ``AK3``, ``BS23``, ``MS`` and ``P1`` through ``P6``. Every other abbreviation is spelled out.

Documentation
-------------

Documentation pages are lowercase with hyphens or single words: ``proof_track``, ``standards``, ``naming``, ``families/core``. A page title is a plain sentence or a single noun phrase, in sentence case.

Commits
-------

Commits follow ``<type>(<scope>): <imperative verb> <object>``, with scope drawn from the family list: ``feat(nielsen): add the pivot bridge``.
