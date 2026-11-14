Claims and Their Commands
=========================

*Status: every number in this documentation reproduces from the command beside it.*

A number that appears only in prose is removed. Run every command from the
repository root.

Corpus size
-----------

.. list-table::
   :header-rows: 1
   :widths: 34 26 40

   * - Claim
     - Value
     - Command
   * - Lean modules
     - 81
     - ``ls lean/*.lean | wc -l``
   * - Declarations
     - 1,553
     - ``scripts/count_declarations.sh``
   * - Theorems
     - 783
     - ``grep -h '^theorem ' lean/*.lean | wc -l``
   * - Lemmas
     - 189
     - ``grep -h '^lemma ' lean/*.lean | wc -l``
   * - ``sorry`` in the corpus
     - 0
     - ``grep -rn '^[[:space:]]*sorry[[:space:]]*$' lean/*.lean | wc -l``
   * - User axioms in the corpus
     - 0
     - ``grep -rn '^[[:space:]]*axiom[[:space:]]' lean/*.lean | wc -l``

Build
-----

.. list-table::
   :header-rows: 1
   :widths: 34 26 40

   * - Claim
     - Value
     - Command
   * - Corpus build
     - succeeds over every module in the build set
     - ``cd lean && lake exe cache get && lake build``
   * - Root package build
     - succeeds over the corpus plus the two registry modules
     - ``lake build``
   * - Corpus verdict
     - ``CORPUS VERIFIED``
     - ``./scripts/verify_corpus.sh``

Registry entry
--------------

.. list-table::
   :header-rows: 1
   :widths: 34 26 40

   * - Claim
     - Value
     - Command
   * - Challenge module size
     - 163 lines, 7,178 bytes
     - ``wc -lc Challenge.lean``
   * - ``sorry`` in Solution
     - 0
     - ``grep -c '^[[:space:]]*sorry[[:space:]]*$' Solution.lean``
   * - Axioms of each registered theorem
     - within ``propext``, ``Classical.choice``, ``Quot.sound``; the energy barrier uses the first and third
     - append ``#print axioms`` to a copy of ``Solution.lean`` and compile it
   * - Registered theorems
     - 8
     - ``python3 -c "import json;print(len(json.load(open('comparator.json'))['theorem_names']))"``

What is not claimed
-------------------

The conjecture is open in this corpus. Two declarations of type ``Prop`` carry
no proof: ``HighMeasureDescent`` at ``lean/NielsenSliceBridge.lean:69`` and
``measure12_ordered_classification`` at ``lean/NielsenMeasure12Cover.lean:200``.
No command in this file reports either as proved.
