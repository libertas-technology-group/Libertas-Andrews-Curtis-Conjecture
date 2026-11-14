.. raw:: html

   Libertas Andrews–Curtis — Documentation

The proof track
===============

*Status: Active reference · Co-authored with Libertas Superintelligence © · © 2026 Libertas Technology Group Limited.*

The proof track is the ordinary Andrews–Curtis target. The corpus reduces that target to one open input, A8, and records the work that closes the inputs around it. Stable AC is a second track with its own residual obligation; :doc:`stable` covers it. The exact statements are on :doc:`statements`, and the declaration tables are on :doc:`results`.

The reduction chain
-------------------

The ordinary target is ``AC.Conjecture`` at ``lean/AC.lean:55-57``. The chain the corpus establishes is:

.. code-block:: text

   AC.Conjecture
     ↔ hterm
     ⇐ A8, with A7-general and A9 discharged by the accepted corpus

``AC.ProofAttempt.conjecture_iff_terminal`` proves the first equivalence (``lean/AcProof.lean:368``). ``AC.Final.conjecture_iff_A8`` proves that A8 is equivalent to ``AC.Conjecture`` once A7-general is available (``lean/AcFinal.lean:54``). The reduction is a statement about the target. It is not a proof of the target.

A8 --

A8 is the statement that every abelian-terminal presentation of the trivial group at positive finite rank reaches a signed permutation by ordinary moves. In the form used by ``AC.Final.conjecture_of_A8``, the hypothesis is

.. code-block:: text

   ∀ (n : ℕ), 0 < n → ∀ S : Relators n, PresentsTrivialGroup S →
     IsAbelianTerminal S →
     ∃ T : Relators n, IsSignedPermutation T ∧ Reachable S T

A8 is open. Two proof attacks are recorded in the session exploration blocks, which stay outside this repository: the Magnus tail descent and the cyclic Nielsen descent. The Nielsen route closes short relators and measures 6, 8, and 10; the remaining Nielsen case is both relators of length at least five above measure 10. The Magnus route repaired the two-stage stress state; the global tail-descent statement is not proved in this tree. The Fox row-module route is pruned by a concrete example. The open inputs are named in the README and in :doc:`families/nielsen`.

A7 and A9
---------

A7 is discharged at rank two by ``AC.Euclid.abelianTerminal_reachable_of_expSpan_top`` (``lean/AcEuclid.lean:338``) and at general rank by ``AC.EuclidGeneral.abelianTerminal_reachable_of_expSpan_top_general`` (``lean/AcEuclidGeneral.lean:849``). A9 is discharged by ``AC.RankReduction.rankReduction`` (``lean/AcRankReduction.lean:314``). The A10 assembly consumes those results and leaves A8 as the only open input.

The counterproof route
--------------------

The counterproof route is a separate way to reach a full result. Its record is:

- ``AC.Ak3.ak3_presentsTrivial`` proves that the AK(3) presentation presents the
  trivial group (``lean/Ak3.lean:37``).
- The separation statement ``¬ Reachable ak3 (standard 2)`` is open
  (``lean/Ak3.lean:124``).
- ``AC.Quotient.psl_index_separates`` proves that a normal-closure index
  different from one refutes reachability to the standard pair
  (``lean/AcQuotient.lean:124``).
- ``AC.Ak3Separation.pslIndexSeparation_false`` proves that the AK(3) PSL index
  is one, so the PSL quotient route is pruned (``lean/Ak3Separation.lean:248``).
- The Fox row-module invariance is refuted by a concrete example held in the
  research workspace record. That route is pruned.

A pruned route is a result about a method. It is not a separation theorem for AK(3), and no counterexample is claimed.

What is not claimed
-------------------

No partial result in this corpus is reported as the endpoint. The corpus does not prove ``AC.Conjecture``, does not prove ``AC.StableConjecture``, and does not exhibit a counterexample to either. The submission is not filed, the sharing agreement is not checked, and the public proof mirror is not created.
