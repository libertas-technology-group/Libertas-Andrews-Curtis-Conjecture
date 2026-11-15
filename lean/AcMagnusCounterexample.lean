module

public import AcTailDefs

@[expose] public section

/-!
# AcMagnusCounterexample — the negation of the multiplier-core descent statement

This module states the exact negation of the forward proposition recorded in
`AcTail.lean`, and records the obstruction that blocks a proof of the negation.
The abelian-terminal predicate is `AC.Euclid.IsAbelianTerminal`, the single
declaration in the compiled corpus.

The negation is not a statement about the free group alone.  `MultiplierCore`
carries `PresentsTrivialGroup`, and the ordered standard rank-two tuple is
abelian terminal with total tail zero.  Every multiplier core has positive total
tail, so a state that has no reachable abelian-terminal state of smaller
total tail does not reach the standard tuple.
`counterexample_of_not_multiplierCorePlus_descent` records that deduction, and
`not_conjecture_of_not_multiplierCorePlus_descent` records its consequence for
`AC.Conjecture`.
-/

set_option autoImplicit false

namespace AC
namespace Tail

open AC.Invariant

/-- The exact negation of the forward statement `multiplierCorePlus_descent`,
written as the negation of its universal closure. -/
def not_multiplierCorePlus_descent_statement : Prop :=
  ¬ (∀ S : Relators 2, MultiplierCorePlus S →
    ∃ T : Relators 2, Reachable S T ∧ Euclid.IsAbelianTerminal T ∧
      totalTail T < totalTail S)

/-! ## 1. The ordered standard tuple is an abelian terminal state of tail zero -/

/-- The exponent vector of a free generator is the corresponding basis vector. -/
lemma expVec_freeGroup_of (g : Fin 2) : expVec (FreeGroup.of g) = genVec g := by
  simp [expVec, expHom]

/-- The section of a basis vector is the corresponding generator. -/
lemma cosetSection_genVec (g : Fin 2) :
    cosetSection (genVec g 0) (genVec g 1) = FreeGroup.of g := by
  fin_cases g <;> simp [cosetSection, genVec]

/-- A free generator has trivial tail. -/
lemma tail_freeGroup_of (g : Fin 2) : tail (FreeGroup.of g) = 1 := by
  simp [tail, cosetSection_genVec]

/-- The ordered standard rank-two tuple has total tail zero. -/
lemma totalTail_standard : totalTail (standard 2) = 0 := by
  simp [totalTail, tailLength, standard, tail_freeGroup_of]

/-- The ordered standard rank-two tuple is abelian terminal: its exponent matrix
is the identity. -/
lemma isAbelianTerminal_standard : Euclid.IsAbelianTerminal (standard 2) := by
  refine ⟨id, ⟨fun _ _ h => h, fun i => ⟨i, rfl⟩⟩, fun _ => true, ?_⟩
  intro i
  simp [standard]

/-! ## 2. A witness for the negation is a rank-two counterexample -/

/-- A witness for the negation — a state in the multiplier core with no reachable
abelian-terminal state of smaller total tail — is a rank-two counterexample to
the ordinary Andrews–Curtis conjecture: it presents the trivial group and does
not reach the standard tuple, which is abelian terminal with total tail zero. -/
theorem counterexample_of_not_multiplierCorePlus_descent
    (h : not_multiplierCorePlus_descent_statement) : Counterexample := by
  classical
  obtain ⟨S, hS⟩ := not_forall.mp h
  obtain ⟨hcore, hno⟩ := Classical.not_imp.mp hS
  refine ⟨2, by decide, S, ?_⟩
  refine ⟨hcore.1.2.1, ?_⟩
  intro hreach
  exact hno ⟨standard 2, hreach, isAbelianTerminal_standard,
    by simpa [totalTail_standard] using hcore.1.2.2.1⟩

/-- A closed proof of the negation settles `AC.Conjecture` in the negative. -/
theorem not_conjecture_of_not_multiplierCorePlus_descent
    (h : not_multiplierCorePlus_descent_statement) : ¬ Conjecture :=
  AC.Counterexample.not_conjecture
    (counterexample_of_not_multiplierCorePlus_descent h)

end Tail
end AC
