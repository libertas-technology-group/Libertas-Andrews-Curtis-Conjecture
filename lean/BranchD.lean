module

public import AC
public import AcMove

@[expose] public section

/-!
# Branch D — the stable Andrews–Curtis route

This file formalises the stable move set of `AC.StableStep` (`AC.lean:93-99`), the stable
terminal state, and the exact relation between the stable and ordinary conjectures.

## What is proved here

1. `StableAcMove` is the syntactic grammar of the stable moves, and
   `StableAcMove.stableStep_iff` shows that it generates exactly `AC.StableStep`.
   This is the stable analogue of `AcMove.step_iff` in `AcMove.lean:33-43`.
2. `rankOf_stableStep`: every stable step either preserves the rank or moves it by one.
3. `standard_succ_eq_stabilize`: the standard tuple at rank `n + 1` is the stabilization
   of the standard tuple at rank `n` at the last generator and last relator position.
4. `standard_stableReachable_empty` and `empty_stableReachable_standard`: the standard
   tuple and the empty presentation are stable-reachable from each other at every rank.
5. `stableReachable_standard_iff_empty`: the stable terminal state may be taken to be the
   ordered standard tuple or the empty presentation, with no change of content.
6. `stableConjecture_iff_empty_terminal`: `AC.StableConjecture` stated against the empty
   presentation is equivalent to the same statement against the standard tuple.
7. `stableReachable_empty_stabilize_iff`: stable solvability is invariant under adding or
   removing one generator–relator pair. This is what makes the route stable.
8. `stableReachable_empty_of_reachable_standard` and
   `stableReachable_empty_of_stableReachable_of_reachable`: the class of presentations that
   are ordinarily AC-reachable to the standard tuple is stably trivial; in particular the
   whole signed-permutation class at every rank, by `AC.ProofAttempt.signedPermutation_reachable_standard`.
9. `conjecture_iff_stable_and_projection`: `AC.Conjecture` is equivalent to the conjunction
   of `AC.StableConjecture` and the projection principle `StableImpliesOrdinary`. The first
   conjunct is proved from the second input; the projection principle is the residual gap
   and is stated, not proved. This is the precise sense in which Stable AC reduces to
   ordinary AC plus the stabilize/destabilize moves.

## Unfinished proof steps

There are none in this file. Every declaration below is closed. The residual obligation
`StableImpliesOrdinary` is a *definition*, not a theorem with a hole: it names the open
mathematical statement and is used only as a hypothesis.

`set_option autoImplicit false` matches `lean/lakefile.toml:5`. The file is in the
`AcCorpus` globs and compiles in the 3,308-job build.
-/

set_option autoImplicit false

namespace AC
namespace BranchD

/-! ## 1. The stable move grammar -/

/-- The stable moves as syntax: one ordinary `AcMove` at fixed rank, a stabilization, or a
destabilization. The rank-changing constructors are exactly the two directions of
`AC.stabilize` (`AC.lean:86-88`), so the grammar is symmetric by construction. -/
inductive StableAcMove : Presentation → Presentation → Type
  /-- An ordinary Andrews–Curtis move, at fixed rank. -/
  | ac {n : ℕ} {R S : Relators n} (m : AcMove n R S) : StableAcMove ⟨n, R⟩ ⟨n, S⟩
  /-- Add the generator at position `g` with the singleton relator at position `i`. -/
  | stabilize {n : ℕ} (R : Relators n) (g i : Fin (n + 1)) :
      StableAcMove ⟨n, R⟩ ⟨n + 1, AC.stabilize R g i⟩
  /-- Remove the pair inserted by `stabilize R g i`. -/
  | destabilize {n : ℕ} (R : Relators n) (g i : Fin (n + 1)) :
      StableAcMove ⟨n + 1, AC.stabilize R g i⟩ ⟨n, R⟩

namespace StableAcMove

/-- Interpret one grammar move as an official `AC.StableStep`. -/
theorem toStableStep {P Q : Presentation} (m : StableAcMove P Q) : StableStep P Q := by
  cases m with
  | ac h => exact StableStep.ac h.toStep
  | stabilize R g i => exact StableStep.stabilize R g i
  | destabilize R g i => exact StableStep.destabilize R g i

/-- The grammar generates exactly the official stable relation: every official step parses
to a grammar move, and every grammar move interprets to an official step. -/
theorem stableStep_iff {P Q : Presentation} :
    StableStep P Q ↔ Nonempty (StableAcMove P Q) := by
  constructor
  · intro h
    cases h with
    | ac hs =>
        obtain ⟨m⟩ := AcMove.step_iff.mp hs
        exact ⟨StableAcMove.ac m⟩
    | stabilize R g i => exact ⟨StableAcMove.stabilize R g i⟩
    | destabilize R g i => exact ⟨StableAcMove.destabilize R g i⟩
  · intro h
    obtain ⟨m⟩ := h
    exact m.toStableStep

end StableAcMove

/-! ## 2. Rank accounting -/

/-- The rank of a presentation. -/
def rankOf (P : Presentation) : ℕ := P.1

@[simp] theorem rankOf_mk (n : ℕ) (R : Relators n) : rankOf ⟨n, R⟩ = n := rfl

/-- Every stable step either preserves the rank or changes it by exactly one. There is no
step that changes the rank by more than one, so a rank excursion is a walk on `ℕ`. -/
theorem rankOf_stableStep {P Q : Presentation} (h : StableStep P Q) :
    rankOf Q = rankOf P ∨ rankOf Q = rankOf P + 1 ∨ rankOf Q + 1 = rankOf P := by
  cases h with
  | ac _ => exact Or.inl rfl
  | stabilize R g i => exact Or.inr (Or.inl rfl)
  | destabilize R g i => exact Or.inr (Or.inr rfl)

/-! ## 3. The empty presentation -/

/-- The empty presentation: rank zero, no generators, no relators. It is the terminal state
of the Stable AC problem (`stable_core.py:37`). -/
def emptyPresentation : Presentation := ⟨0, Fin.elim0⟩

/-- At rank zero there is exactly one relator tuple, so every rank-zero presentation is the
empty presentation. This is why the empty state is canonical and the standard tuple is not:
`standard n` depends on the generator numbering, `emptyPresentation` has no numbering. -/
theorem rank_zero_eq_empty (R : Relators 0) :
    (⟨0, R⟩ : Presentation) = emptyPresentation := by
  unfold emptyPresentation
  rw [show R = Fin.elim0 from funext fun i => Fin.elim0 i]

/-! ## 4. The standard tuple is a stabilization of the previous standard tuple -/

/-- Inserting the last generator, with its singleton relator at the last position, into
`standard n` gives `standard (n + 1)`. The old generator `j` is relabelled to
`Fin.castSucc j`, which is exactly its position in `Fin (n + 1)`. -/
theorem standard_succ_eq_stabilize (n : ℕ) :
    standard (n + 1) = AC.stabilize (standard n) (Fin.last n) (Fin.last n) := by
  rw [show AC.stabilize (standard n) (Fin.last n) (Fin.last n)
      = Fin.insertNth (α := fun _ => FreeGroup (Fin (n + 1)))
          (Fin.last n) (FreeGroup.of (Fin.last n))
          (fun j => FreeGroup.map (Fin.succAbove (Fin.last n)) (FreeGroup.of j)) from rfl]
  rw [Fin.eq_insertNth_iff]
  constructor
  · rfl
  · funext j
    simp [Fin.removeNth, Fin.succAbove_last, standard]

/-- At the last generator position and the last relator position, `AC.stabilize` is the
append operation: the old relators, relabelled by `Fin.castSucc`, followed by the singleton
relator of the new last generator. This is the state produced by move 14 of `sac-r8-v1`
(`stable_core.py:144-147`), so the frozen benchmark's stabilization is the `last`/`last`
instance of the Lean move set. -/
theorem stabilize_last_last_eq_snoc (n : ℕ) (R : Relators n) :
    AC.stabilize R (Fin.last n) (Fin.last n)
      = Fin.snoc (fun j => FreeGroup.map Fin.castSucc (R j)) (FreeGroup.of (Fin.last n)) := by
  rw [show AC.stabilize R (Fin.last n) (Fin.last n)
      = Fin.insertNth (α := fun _ => FreeGroup (Fin (n + 1)))
          (Fin.last n) (FreeGroup.of (Fin.last n))
          (fun j => FreeGroup.map (Fin.succAbove (Fin.last n)) (R j)) from rfl]
  rw [Fin.insertNth_last']
  simp [Fin.succAbove_last]

/-! ## 5. The standard tuple and the empty presentation are mutually reachable -/

/-- Every standard tuple destabilizes to the empty presentation. The induction removes the
last generator–relator pair at each step; `standard_succ_eq_stabilize` identifies the state
with an official stabilization, so `StableStep.destabilize` applies. -/
theorem standard_stableReachable_empty (n : ℕ) :
    StableReachable ⟨n, standard n⟩ emptyPresentation := by
  induction n with
  | zero =>
      rw [rank_zero_eq_empty (standard 0)]
      exact Relation.ReflTransGen.refl
  | succ n ih =>
      have hstep : StableStep ⟨n + 1, standard (n + 1)⟩ ⟨n, standard n⟩ := by
        rw [standard_succ_eq_stabilize]
        exact StableStep.destabilize (standard n) (Fin.last n) (Fin.last n)
      exact Relation.ReflTransGen.head hstep ih

/-- The empty presentation stabilizes to every standard tuple. This is the reverse
enumeration of `standard_stableReachable_empty`. -/
theorem empty_stableReachable_standard (n : ℕ) :
    StableReachable emptyPresentation ⟨n, standard n⟩ := by
  induction n with
  | zero =>
      rw [rank_zero_eq_empty (standard 0)]
      exact Relation.ReflTransGen.refl
  | succ n ih =>
      have hstep : StableStep ⟨n, standard n⟩ ⟨n + 1, standard (n + 1)⟩ := by
        rw [standard_succ_eq_stabilize]
        exact StableStep.stabilize (standard n) (Fin.last n) (Fin.last n)
      exact Relation.ReflTransGen.tail ih hstep

/-! ## 6. The stable terminal state -/

/-- For any presentation `P`, stable reachability of the ordered standard tuple at the rank
of `P` is equivalent to stable reachability of the empty presentation. The forward
direction appends the destabilization chain of the standard tuple; the reverse direction
appends the stabilization chain of the standard tuple. -/
theorem stableReachable_standard_iff_empty (P : Presentation) :
    StableReachable P ⟨P.1, standard P.1⟩ ↔ StableReachable P emptyPresentation := by
  constructor
  · intro h
    exact Relation.ReflTransGen.trans h (standard_stableReachable_empty P.1)
  · intro h
    exact Relation.ReflTransGen.trans h (empty_stableReachable_standard P.1)

/-- `AC.StableConjecture` with the empty terminal state is equivalent to the official form
with the standard terminal state (`AC.lean:110-112`). The terminal state carries no
mathematical content; either form is the stable target. -/
theorem stableConjecture_iff_empty_terminal :
    StableConjecture ↔ ∀ (n : ℕ), 0 < n → ∀ R : Relators n,
      PresentsTrivialGroup R → StableReachable ⟨n, R⟩ emptyPresentation := by
  constructor
  · intro h n hn R hR
    exact (stableReachable_standard_iff_empty ⟨n, R⟩).mp (h n hn R hR)
  · intro h n hn R hR
    exact (stableReachable_standard_iff_empty ⟨n, R⟩).mpr (h n hn R hR)

/-! ## 7. Stability under adding and removing a trivial pair -/

/-- Stable solvability against the empty state is invariant under one stabilization. The two
directions are the two rank-changing constructors and no other step is used. -/
theorem stableReachable_empty_stabilize_iff {n : ℕ} (R : Relators n) (g i : Fin (n + 1)) :
    StableReachable ⟨n, R⟩ emptyPresentation ↔
      StableReachable ⟨n + 1, AC.stabilize R g i⟩ emptyPresentation := by
  constructor
  · intro h
    exact Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single (StableStep.destabilize R g i)) h
  · intro h
    exact Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single (StableStep.stabilize R g i)) h

/-! ## 8. Covered classes -/

/-- Every presentation that is ordinarily AC-reachable to the standard tuple is stably
trivial. Combined with `AC.ProofAttempt.signedPermutation_reachable_standard`
(`AcProof.lean:336-362`, gap G3 closed), this covers the entire signed-permutation class at
every rank: for every `n` and every signed permutation `T`, `⟨n, T⟩` reaches the empty
presentation. The import of `AcProof` is deliberately avoided here because that file
depends on `AcInvariant`, whose G1 elaboration is blocked in the current tree. -/
theorem stableReachable_empty_of_reachable_standard {n : ℕ} {R : Relators n}
    (h : Reachable R (standard n)) : StableReachable ⟨n, R⟩ emptyPresentation :=
  Relation.ReflTransGen.trans h.stable (standard_stableReachable_empty n)

/-- Stable solvability is inherited backwards along ordinary AC paths: if `S` is stably
trivial and `R` reaches `S` by ordinary moves, then `R` is stably trivial. This is the
descent step the solver uses to reuse a stable certificate from any AC-reachable state. -/
theorem stableReachable_empty_of_stableReachable_of_reachable {n : ℕ} {R S : Relators n}
    (hRS : Reachable R S) (hS : StableReachable ⟨n, S⟩ emptyPresentation) :
    StableReachable ⟨n, R⟩ emptyPresentation :=
  Relation.ReflTransGen.trans hRS.stable hS

/-! ## 9. The reduction of Stable AC to ordinary AC -/

/-- The projection principle: stable solvability at the rank of a trivial presentation
implies ordinary AC solvability at that rank. This is the one statement that the stable
route does not prove. The obstruction is structural: a stable path may leave the rank and
return, `AC.Step` is typed at one rank, so a rank excursion has no ordinary reading, and
`AC.stabilize` is not a morphism for `AC.Step` (section 10 of `BRANCH_D.md` records the
witness). -/
def StableImpliesOrdinary : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ R : Relators n, PresentsTrivialGroup R →
    StableReachable ⟨n, R⟩ ⟨n, standard n⟩ → Reachable R (standard n)

/-- The same projection principle stated against the empty terminal state. -/
def StableEmptyImpliesOrdinary : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ R : Relators n, PresentsTrivialGroup R →
    StableReachable ⟨n, R⟩ emptyPresentation → Reachable R (standard n)

/-- The two forms of the projection principle are equivalent, by the terminal-state
equivalence of section 6. -/
theorem stableImpliesOrdinary_iff_empty :
    StableImpliesOrdinary ↔ StableEmptyImpliesOrdinary := by
  constructor
  · intro h n hn R hR hstable
    exact h n hn R hR ((stableReachable_standard_iff_empty ⟨n, R⟩).mpr hstable)
  · intro h n hn R hR hstable
    exact h n hn R hR ((stableReachable_standard_iff_empty ⟨n, R⟩).mp hstable)

/-- **The reduction.** The ordinary Andrews–Curtis conjecture is equivalent to the stable
conjecture together with the projection principle.

The forward direction is the stable conjecture plus the trivial observation that ordinary
solvability is what the stable hypothesis already provides. The reverse direction composes
`AC.Conjecture.stable` (`AC.lean:141-142`) with the projection principle. Nothing else is
used, so the whole distance between the stable and the ordinary route is the single
statement `StableImpliesOrdinary`. -/
theorem conjecture_iff_stable_and_projection :
    Conjecture ↔ StableConjecture ∧ StableImpliesOrdinary := by
  constructor
  · intro h
    exact ⟨h.stable, fun n hn R hR _ => h n hn R hR⟩
  · rintro ⟨hstable, hproj⟩ n hn R hR
    exact hproj n hn R hR (hstable n hn R hR)

/-- The reduction in the empty-terminal form. -/
theorem conjecture_iff_stableEmpty_and_projection :
    Conjecture ↔ StableConjecture ∧ StableEmptyImpliesOrdinary :=
  conjecture_iff_stable_and_projection.trans
    (and_congr Iff.rfl stableImpliesOrdinary_iff_empty)

/-! ## 10. Axiom record

The fresh reader runs, on the pinned toolchain:

    #print axioms AC.BranchD.standard_succ_eq_stabilize
    #print axioms AC.BranchD.standard_stableReachable_empty
    #print axioms AC.BranchD.empty_stableReachable_standard
    #print axioms AC.BranchD.stableReachable_standard_iff_empty
    #print axioms AC.BranchD.stableConjecture_iff_empty_terminal
    #print axioms AC.BranchD.stableReachable_empty_stabilize_iff
    #print axioms AC.BranchD.conjecture_iff_stable_and_projection

Each must report a set inside `[propext, Classical.choice, Quot.sound]`. A listing that
contains `sorryAx`, or any axiom outside that set, is a defect. `StableImpliesOrdinary` is a
`def`, so `#print axioms` on it reports only the axioms of the definition body, which is
none. -/

end BranchD
end AC
