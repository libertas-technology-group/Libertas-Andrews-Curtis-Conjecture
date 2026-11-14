.. raw:: html

   Libertas Andrews–Curtis — Documentation

Families
========

*Status: Active reference · Co-authored with Libertas Superintelligence © · © 2026 Libertas Technology Group Limited.*

The corpus is organised into six families. The order is the reading order and
the dependency order: a family imports from its own family or from an earlier
one, so the graph is acyclic by construction.

.. list-table::
   :widths: 18 26 56
   :header-rows: 1

   * - Family
     - Entry theorem
     - Question it answers
   * - :doc:`core`
     - ``conjecture_iff_A8``
     - what the conjecture is equivalent to
   * - :doc:`stable`
     - ``conjecture_iff_stable_and_projection``
     - how the stable conjecture relates to the ordinary one
   * - :doc:`topology`
     - ``pslIndexSeparation_false``
     - what the low-dimensional invariants can and cannot separate
   * - :doc:`homological`
     - ``nonmetabelianQuotientSeparation_iff_bs23OrbitSeparation``
     - what the Fox and Britton–Schupp invariants reduce to
   * - :doc:`nielsen`
     - ``cyclicNielsen_uniform_pivot_statement``
     - what the measure argument reduces the conjecture to
   * - :doc:`assembly`
     - ``a8_rank_two_of_tailMinimalStatement``
     - how the chain is assembled from the nielsen bridge

.. toctree::
   :maxdepth: 1

   core
   stable
   topology
   homological
   nielsen
   assembly
