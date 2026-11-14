.. raw:: html

   Libertas Andrews–Curtis — Documentation

Standards
=========

*Status: Active reference · Co-authored with Libertas Superintelligence © · © 2026 Libertas Technology Group Limited.*

Every module in the build set obeys five rules. A change that violates one is a defect and is returned to its author.

The five rules
--------------

**One module, one subject.** The module docstring states, in one paragraph, what the module proves and which family it belongs to. A module that proves two unrelated things is split.

**Names describe the statement.** Theorems and lemmas use ``lower_snake_case`` and spell the statement. Examples from the corpus:

- ``conjecture_iff_A8``
- ``a8_rank_two_of_tailMinimalStatement``
- ``tailMinimalStatement_of_uniformPivot``
- ``uniform_of_low_and_high``

Abbreviations are permitted only for ``AC``, ``A8``, ``AK3``, ``BS23``, ``MS`` and the presentation names ``P1`` through ``P6``. A name that does not read as the statement is renamed.

**Axiom record.** Every built module ends its docstring with the axiom set it uses, naming ``propext``, ``Classical.choice`` and ``Quot.sound``. A module that needs a fourth axiom is not admitted to the build set.

**No open obligations.** No ``sorry``, ``admit``, user ``axiom`` declaration, or ``native_decide`` in a built module. ``native_decide`` is barred because it moves the check outside the kernel.

**Acyclic imports.** The module import graph contains no cycle. The family labels describe subject matter; they are not a strict layering. Where a module in one family uses a result from another, the import is explicit and the dependency appears in :doc:`families/index`.

The families
------------

.. list-table::
   :widths: 22 30 48
   :header-rows: 1

   * - Family
     - Prefix
     - Entry point
   * - Core reduction
     - ``AC``, ``AcMove``, ``AcProof``, ``AcFinal``
     - ``conjecture_iff_A8``
   * - Stable
     - ``AcStable*``
     - ``conjecture_iff_stable_and_projection``
   * - Topology
     - ``Ak3*``, ``AcStallings*``
     - ``pslIndexSeparation_false``, the Stallings orbit results
   * - Homological
     - ``AcBS23*``
     - ``nonmetabelianQuotientSeparation_iff_bs23OrbitSeparation``
   * - Nielsen
     - ``Nielsen*``, ``AcNielsen*``
     - ``cyclicNielsen_uniform_pivot_statement``
   * - Assembly
     - ``AcA8*``
     - ``a8_rank_two_of_tailMinimalStatement``

Documentation rules
-------------------

One page per family carries its entry theorem, the files it covers, and the edge to the next family. Every claim in the README traces to a file and line through the provenance register in :doc:`references`. The site builds without warnings under ``sphinx-build -W``.

Repository rule
---------------

The public repository carries five roots: ``lean/``, ``docs/``, ``scripts/``, ``README.md`` and ``AGENTS.md``, with ``LICENSE``, ``CITATION.cff``, ``VERSION`` and ``.gitignore`` at the root. Anything else is a defect.
