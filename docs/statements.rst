.. raw:: html

   Libertas Andrews–Curtis — Documentation

Statements
==========

*Status: Active reference · Co-authored with Libertas Superintelligence © · © 2026 Libertas Technology Group Limited.*

The corpus fixes two propositions. ``AC.Conjecture`` is the ordinary Andrews–Curtis conjecture at every positive finite rank, with the rank held fixed along the path. ``AC.StableConjecture`` is the stable variant, which permits adding and removing an isolated generator–relator pair. The ordinary statement is the SAIR target. The stable statement is a separate track. The repository proves neither proposition.

Words and presentations
-----------------------

A word on ``n`` generators is an element of the free group ``FreeGroup (Fin n)``. A balanced presentation is an ordered tuple of ``n`` relators on ``n`` generators. The presentation presents the trivial group when the quotient by the normal closure of the relators is a subsingleton.

.. code-block:: lean

   abbrev Word (n : ℕ) := FreeGroup (Fin n)

   abbrev Relators (n : ℕ) := Fin n → Word n

   def standard (n : ℕ) : Relators n := FreeGroup.of

   def PresentsTrivialGroup {n : ℕ} (R : Relators n) : Prop :=
     Subsingleton (PresentedGroup (Set.range R))

Source: ``lean/AC.lean:21-30``.

The ordinary move relation
--------------------------

One ordinary move fixes the rank and changes one relator. The constructors are relator inversion, right multiplication by another relator at a different position, and conjugation by an arbitrary word. The ``i ≠ j`` guard excludes squaring a relator. Left multiplication is derived from right multiplication and conjugation.

.. code-block:: lean

   inductive Step {n : ℕ} : Relators n → Relators n → Prop
     | inv (R : Relators n) (i : Fin n) :
         Step R (Function.update R i (R i)⁻¹)
     | mulRight (R : Relators n) (i j : Fin n) (h : i ≠ j) :
         Step R (Function.update R i (R i * R j))
     | conj (R : Relators n) (i : Fin n) (w : Word n) :
         Step R (Function.update R i (w * R i * w⁻¹))

Reachability is the reflexive-transitive closure of the move relation. The empty sequence is admitted, and no bound is placed on the path length or on the size of intermediate words.

.. code-block:: lean

   def Reachable {n : ℕ} : Relators n → Relators n → Prop :=
     Relation.ReflTransGen Step

Source: ``lean/AC.lean:40-50``.

The ordinary conjecture
-----------------------

.. code-block:: lean

   def Conjecture : Prop :=
     ∀ (n : ℕ), 0 < n → ∀ (R : Relators n),
       PresentsTrivialGroup R → Reachable R (standard n)

Source: ``lean/AC.lean:59-57``.

The rank-zero case is excluded from the quantifier and holds trivially. Relator permutations are reachable, so the ordered standard target adds no restriction.

The stable move relation
------------------------

A stable state carries its rank, so the state type is a dependent pair of a rank and a relator tuple at that rank. Stabilization inserts a fresh generator at position ``g`` and its singleton relator at position ``i``. The injection ``g.succAbove`` relabels the old generators while skipping the new one, so the new generator does not occur in any old relator.

.. code-block:: lean

   abbrev Presentation := (n : ℕ) × Relators n

   def stabilize {n : ℕ} (R : Relators n) (g i : Fin (n + 1)) : Relators (n + 1) :=
     Fin.insertNth i (FreeGroup.of g) (fun j => FreeGroup.map g.succAbove (R j))

   inductive StableStep : Presentation → Presentation → Prop
     | ac {n : ℕ} {R S : Relators n} (h : Step R S) :
         StableStep ⟨n, R⟩ ⟨n, S⟩
     | stabilize {n : ℕ} (R : Relators n) (g i : Fin (n + 1)) :
         StableStep ⟨n, R⟩ ⟨n + 1, AC.stabilize R g i⟩
     | destabilize {n : ℕ} (R : Relators n) (g i : Fin (n + 1)) :
         StableStep ⟨n + 1, AC.stabilize R g i⟩ ⟨n, R⟩

   def StableReachable : Presentation → Presentation → Prop :=
     Relation.ReflTransGen StableStep

Source: ``lean/AC.lean:79-104``. A stable step either preserves the rank or changes it by one; ``AC.BranchD.rankOf_stableStep`` records that accounting (``lean/BranchD.lean:106``).

The stable conjecture
---------------------

The endpoint is the standard tuple at the original rank. The stable path may leave that rank and return to it.

.. code-block:: lean

   def StableConjecture : Prop :=
     ∀ (n : ℕ), 0 < n → ∀ (R : Relators n),
       PresentsTrivialGroup R → StableReachable ⟨n, R⟩ ⟨n, standard n⟩

Source: ``lean/AC.lean:114-112``.

The empty presentation is an equivalent endpoint. ``AC.BranchD.stableConjecture_iff_empty_terminal`` proves that the form above is equivalent to the same statement with the empty presentation as its target (``lean/BranchD.lean:207``).

What the statements do not assert
---------------------------------

- The ordinary statement does not bound the length of a path, the size of an
  intermediate word, or the rank of an intermediate state.
- The stable statement does not assert the ordinary statement. A stable path can
  change the rank, so it has no direct reading as an ordinary path.
- The implication ``AC.Conjecture → AC.StableConjecture`` is proved by
  ``AC.Conjecture.stable`` (``lean/AC.lean:145``). The converse implication is
  the projection principle ``AC.BranchD.StableImpliesOrdinary``, which is stated
  and not proved (``lean/BranchD.lean:259``).
- Neither ``AC.Conjecture`` nor ``AC.StableConjecture`` is proved in this
  repository.
