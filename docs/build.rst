.. raw:: html

   Libertas Andrews–Curtis — Documentation

Build and verification
======================

*Status: Active reference · Co-authored with Libertas Superintelligence © · © 2026 Libertas Technology Group Limited.*

Build
-----

.. code-block:: sh

   cd lean
   lake build AcCorpus

Expected:

.. code-block:: text

   Build completed successfully (3373 jobs).

The toolchain is Lean ``4.29.1``. The Mathlib revision is ``5e932f97dd25535344f80f9dd8da3aab83df0fe6``. The library target is ``AcCorpus``, declared in ``lean/lakefile.toml``.

Axiom checks
------------

A scratch file outside the repository:

.. code-block:: lean

   import AcBase
   import AcEuclid
   import AcEuclidGeneral
   import Ak3
   import Ak3Separation
   import AcRankReduction
   import AcInduction
   import AcFinal
   import AcQuotient

   #print axioms AC.Base.presentsTrivialGroup_standard
   #print axioms AC.Euclid.abelianTerminal_reachable_of_expSpan_top
   #print axioms AC.EuclidGeneral.abelianTerminal_reachable_of_expSpan_top_general
   #print axioms AC.Ak3.ak3_presentsTrivial
   #print axioms AC.Ak3Separation.pslIndexSeparation_false
   #print axioms AC.RankReduction.rankReduction
   #print axioms AC.Induction.conjecture_of_abelianTerminal
   #print axioms AC.Final.conjecture_iff_A8
   #print axioms AC.Quotient.psl_index_separates

Run it with:

.. code-block:: sh

   lake env lean /path/to/AxiomCheck.lean

Each print must be a subset of ``[propext, Classical.choice, Quot.sound]``. A fresh reader checks the statement, the artifact hash, the move-relation hash, and the axiom list. The writer is not the verifier.

Documentation build
-------------------

The site is built from ``docs/``. The configuration is checked first, then the site is built with warnings treated as errors.

.. code-block:: sh

   python3 -m py_compile docs/conf.py
   uvx --from sphinx sphinx-build -W -b html docs docs/_build/html

The first command exits 0 when ``docs/conf.py`` parses. The second exits 0 when the site builds with no warning, and writes the HTML to ``docs/_build/html``. When ``uvx`` is absent, install Sphinx in an isolated environment and run ``sphinx-build`` with the same flags. The documentation build is separate from the Lean build; neither check substitutes for the other.

Repository map
--------------

.. code-block:: text

   lean/
     AC.lean                  official statement
     AcMove.lean              move grammar
     AcInvariant.lean         G1
     AcProof.lean             G3, G4, AC ↔ hterm
     AcBase.lean              standard triviality
     AcEuclid.lean            rank-two A7
     AcEuclidGeneral.lean     general-rank A7
     Ak3.lean                 AK(3) triviality
     Ak3Separation.lean       PSL index no-go
     AcRankReduction.lean     A9
     AcInduction.lean         A10 conditional assembly
     AcFinal.lean             AC.Conjecture from A8
     AcQuotient.lean          quotient index
     BranchB.lean             determinant classification
     BranchC.lean             invariant pruning
     BranchD.lean             stable reduction
     BranchD2.lean            stable projection cohort
     BranchD3.lean            stable cohort
     BranchD4.lean            unsolved stable cohort

The exploration files ``BranchA`` through ``BranchA7`` and ``BranchC2`` are outside ``AcCorpus`` and carry explicit proof-search gaps. They are not part of the accepted build.
