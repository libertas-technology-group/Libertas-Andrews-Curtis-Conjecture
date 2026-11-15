module

/-
  The abelianisation collapse, normal-closure half.

  Gaur states in prose that any computable invariant factoring through the
  abelianisation of the normal closure collapses to the exponent-sum matrix on
  balanced presentations of the trivial group.  This module compiles the first
  half: when the presented group is trivial the normal closure of the relators
  is the whole free group, so the relation subgroup carries no information
  beyond the rank.

  Source of the claim:
    EXTERNAL_REPOS/COMPETITORS/Andrews-Curtis-Conjecture/research/directions/
    invariant-ideas/idea.md:180-196  (MIT, Copyright 2026 Pragyaan Gaur)

  Nothing below copies code from that repository.  The statement is restated in
  this corpus's own vocabulary and proved from this corpus's own definitions.
-/
public import Ak3Invariant

@[expose] public section

namespace AC.RelationCollapse

open Ak3Invariant

variable {n : ℕ}

/-- When the presented group is trivial, the normal closure of the relators is
the whole free group. The quotient by the normal closure is one-element, so
every word lies in the normal closure. -/
theorem relationSubgroup_eq_top {R : Relators n} (h : PresentsTrivialGroup R) :
    relationSubgroup R = ⊤ := by
  have : (relationSubgroup R).Normal := by
    unfold relationSubgroup
    infer_instance
  rw [eq_top_iff]
  intro w _
  have : Subsingleton (Word n ⧸ relationSubgroup R) := h
  have h1 : (QuotientGroup.mk w : Word n ⧸ relationSubgroup R) = 1 :=
    Subsingleton.elim _ _
  exact (QuotientGroup.eq_one_iff w).mp h1

/-- Two presentations of the trivial group at the same rank have the same
relation subgroup. -/
theorem relationSubgroup_eq_of_presents {R S : Relators n}
    (hR : PresentsTrivialGroup R) (hS : PresentsTrivialGroup S) :
    relationSubgroup R = relationSubgroup S := by
  rw [relationSubgroup_eq_top hR, relationSubgroup_eq_top hS]

/-- Two presentations of the trivial group at the same rank have the same
relation module. This is the collapse at the level of the abelianised normal
closure, before the identification with the exponent-sum matrix. -/
theorem relationModule_eq_of_presents {R S : Relators n}
    (hR : PresentsTrivialGroup R) (hS : PresentsTrivialGroup S) :
    relationModule R = relationModule S := by
  show Abelianization (relationSubgroup R) = Abelianization (relationSubgroup S)
  rw [relationSubgroup_eq_of_presents hR hS]

/-- An invariant that is constant on the class of trivial presentations cannot
separate a member of that class from the standard tuple. This is the separation
form of the collapse, and it is the shape Gaur's Theorem 2 takes when compiled:
the class is not separated, so the invariant has no content there. -/
theorem relationModuleInvariant_cannot_separate {α : Type*} {R : Relators n}
    (P : Relators n → α)
    (h : ∀ R S : Relators n, PresentsTrivialGroup R → PresentsTrivialGroup S →
      P R = P S)
    (hstd : PresentsTrivialGroup (standard n)) (hR : PresentsTrivialGroup R) :
    ¬ (P R ≠ P (standard n)) :=
  ProofAttempt.group_invariant_cannot_separate P h hstd hR

end AC.RelationCollapse
