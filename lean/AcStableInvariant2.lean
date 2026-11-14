import AC
import AcBase
import AcStableInvariant
import Ak3
import Mathlib.Tactic
import Mathlib.SetTheory.Cardinal.Free
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.Int.TypeTags

/-!
# Stable AC: a third invariant test, the order and cyclicity refinement

The stable move set `AC.StableStep` (`AC.lean:93-99`) preserves the presented
group up to multiplicative equivalence
(`AC.StableInvariant.stableStep_presentedGroup_mulEquiv`).  Every invariant of
the isomorphism class of the presented group is therefore a stable invariant.
The triviality indicator of `AcStableCounterexample.lean` and the
abelianization (perfectness) indicator of `AcStableInvariant.lean` belong to
that class, and `AC.StableInvariant.presentedGroupInvariant_cannot_separate`
rules out every invariant of that class as a separator of AK(3).

This file tests a strictly finer member of the class, the pair

    refinementInvariant P = (groupOrderInvariant P, cyclicityInvariant P),

where `groupOrderInvariant P` is the cardinality of the presented group, read
through `Nat.card` and therefore `0` on an infinite group, and
`cyclicityInvariant P` records whether the presented group is cyclic.

The order component refines the triviality indicator:
`groupOrderInvariant P = 1` exactly when `PresentsTrivialGroup P.2`
(`groupOrderInvariant_eq_one_iff`).  It carries more information than the
indicator.  It separates a presentation of `ℤ/2` from a presentation of `ℤ/3`,
and the triviality indicator takes the value `false` at both.

The cyclicity component is not determined by the abelianization.  The
symmetric group `S₃` and the cyclic group `C₂` have isomorphic abelianizations,
both `C₂`, and only `C₂` is cyclic.  The order component is not determined by
the abelianization either: the alternating group `A₅` and the one-element
group have one-element abelianizations and cardinalities `60` and `1`.

## Preservation

`groupOrderInvariant_stableStep` transports `Nat.card` across the multiplicative
equivalence supplied by each stable step.  `cyclicityInvariant_stableStep`
transports `IsCyclic` across the same equivalence, using `MulEquiv.isCyclic`.
The pair inherits both preservation proofs.

## The AK(3) test and the no-go

`Ak3.ak3` presents the one-element group (`Ak3.ak3_presentsTrivial`), and the
standard rank-two tuple presents the one-element group
(`Base.presentsTrivialGroup_standard`).  Both therefore have order `1` and both
are cyclic.  The refinement invariant takes the same value at the two
presentations, so its separation hypothesis is refuted, and this invariant
cannot separate AK(3).  The no-go agrees with the generic prediction of
`presentedGroupInvariant_cannot_separate` and records the finer invariant in
the pruning record.  The exact separation statement remains the `def`
`ak3_stableSeparationGoal`; it is not asserted here.

## Teeth

Section 6 separates the free presentation at rank two, whose relators are all
the identity word, from the standard rank-two tuple.  The free presentation
presents `F₂`, of order `0` and non-cyclic.  Both components therefore give a
genuine separation somewhere, which shows that the no-go at AK(3) is a failure
of this invariant at that pair and not a vacuous invariant.

## Status

Every declaration in this file is closed.  The file contains no proof hole, no
admission, no native evaluation, and no user axiom.  Single-file check from
`lean/`: `lake env lean AcStableInvariant2.lean`.  The writer of this file is
not its verifier.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace AC
namespace StableInvariant2

open Classical

/-! ## 1. Stable invariants and the separation theorem -/

/-- A stable invariant is a function on presentations that takes the same value
at the two ends of every stable step. -/
def IsStableInvariant {α : Type*} (I : Presentation → α) : Prop :=
  ∀ ⦃P Q : Presentation⦄, StableStep P Q → I P = I Q

/-- The value of a stable invariant is constant along every finite stable path. -/
theorem eq_of_stableReachable {α : Type*} {I : Presentation → α}
    (hI : IsStableInvariant I) {P Q : Presentation} (h : StableReachable P Q) :
    I P = I Q := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (hI hstep)

/-- Stable invariant separation: different invariant values rule out a finite
stable path. -/
theorem not_stableReachable_of_stableInvariant {α : Type*} {I : Presentation → α}
    (hI : IsStableInvariant I) {P Q : Presentation} (h : I P ≠ I Q) :
    ¬ StableReachable P Q :=
  fun hpath => h (eq_of_stableReachable hI hpath)

/-! ## 2. The order component -/

/-- The cardinality of the presented group, read through `Nat.card`.  The value
is `0` on an infinite presented group. -/
noncomputable def groupOrderInvariant (P : Presentation) : ℕ :=
  Nat.card (PresentedGroup (Set.range P.2))

/-- The order component is constant on every stable step. -/
theorem groupOrderInvariant_stableStep {P Q : Presentation} (h : StableStep P Q) :
    groupOrderInvariant P = groupOrderInvariant Q := by
  obtain ⟨e⟩ := AC.StableInvariant.stableStep_presentedGroup_mulEquiv h
  exact Nat.card_congr e.toEquiv

/-- The order component is a stable invariant. -/
theorem groupOrderInvariant_isStableInvariant :
    IsStableInvariant groupOrderInvariant :=
  fun _ _ h => groupOrderInvariant_stableStep h

/-- AK(3) presents the one-element group, so its order component is `1`. -/
theorem groupOrderInvariant_ak3 : groupOrderInvariant ⟨2, Ak3.ak3⟩ = 1 := by
  unfold groupOrderInvariant
  haveI : Subsingleton (PresentedGroup (Set.range Ak3.ak3)) := Ak3.ak3_presentsTrivial
  exact Nat.card_unique

/-- The standard rank-two presentation is one-element, so its order component
is `1`. -/
theorem groupOrderInvariant_standard :
    groupOrderInvariant ⟨2, standard 2⟩ = 1 := by
  unfold groupOrderInvariant
  haveI : Subsingleton (PresentedGroup (Set.range (standard 2))) :=
    Base.presentsTrivialGroup_standard 2
  exact Nat.card_unique

/-- The order component is `1` exactly on the presentations of the one-element
group.  This records the precise relation between the order component and the
triviality indicator. -/
theorem groupOrderInvariant_eq_one_iff {P : Presentation} :
    groupOrderInvariant P = 1 ↔ PresentsTrivialGroup P.2 := by
  unfold groupOrderInvariant PresentsTrivialGroup
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨fun h => h.1, fun h => ⟨h, ⟨1⟩⟩⟩

/-! ## 3. The cyclicity component -/

/-- The cyclicity indicator of the presented group. -/
noncomputable def cyclicityInvariant (P : Presentation) : Bool :=
  if IsCyclic (PresentedGroup (Set.range P.2)) then true else false

/-- The cyclicity component is constant on every stable step. -/
theorem cyclicityInvariant_stableStep {P Q : Presentation} (h : StableStep P Q) :
    cyclicityInvariant P = cyclicityInvariant Q := by
  obtain ⟨e⟩ := AC.StableInvariant.stableStep_presentedGroup_mulEquiv h
  have hiff : IsCyclic (PresentedGroup (Set.range P.2)) ↔
      IsCyclic (PresentedGroup (Set.range Q.2)) := MulEquiv.isCyclic e
  unfold cyclicityInvariant
  by_cases hP : IsCyclic (PresentedGroup (Set.range P.2))
  · have hQ : IsCyclic (PresentedGroup (Set.range Q.2)) := hiff.mp hP
    simp [hP, hQ]
  · have hQ : ¬ IsCyclic (PresentedGroup (Set.range Q.2)) := fun hq => hP (hiff.mpr hq)
    simp [hP, hQ]

/-- The cyclicity component is a stable invariant. -/
theorem cyclicityInvariant_isStableInvariant :
    IsStableInvariant cyclicityInvariant :=
  fun _ _ h => cyclicityInvariant_stableStep h

/-- The one-element group is cyclic, so the cyclicity component of AK(3) is
`true`. -/
theorem cyclicityInvariant_ak3 : cyclicityInvariant ⟨2, Ak3.ak3⟩ = true := by
  unfold cyclicityInvariant
  haveI : Subsingleton (PresentedGroup (Set.range Ak3.ak3)) := Ak3.ak3_presentsTrivial
  rw [if_pos (inferInstance : IsCyclic (PresentedGroup (Set.range Ak3.ak3)))]

/-- The cyclicity component of the standard rank-two presentation is `true`. -/
theorem cyclicityInvariant_standard : cyclicityInvariant ⟨2, standard 2⟩ = true := by
  unfold cyclicityInvariant
  haveI : Subsingleton (PresentedGroup (Set.range (standard 2))) :=
    Base.presentsTrivialGroup_standard 2
  rw [if_pos (inferInstance : IsCyclic (PresentedGroup (Set.range (standard 2))))]

/-! ## 4. The refinement invariant -/

/-- The pair of the order component and the cyclicity component. -/
noncomputable def refinementInvariant (P : Presentation) : ℕ × Bool :=
  (groupOrderInvariant P, cyclicityInvariant P)

/-- The refinement invariant is constant on every stable step. -/
theorem refinementInvariant_stableStep {P Q : Presentation} (h : StableStep P Q) :
    refinementInvariant P = refinementInvariant Q := by
  unfold refinementInvariant
  rw [groupOrderInvariant_stableStep h, cyclicityInvariant_stableStep h]

/-- The refinement invariant is a stable invariant. -/
theorem refinementInvariant_isStableInvariant :
    IsStableInvariant refinementInvariant :=
  fun _ _ h => refinementInvariant_stableStep h

/-! ## 5. The AK(3) test and the no-go -/

/-- The order component takes the same value at AK(3) and at the standard pair. -/
theorem ak3_groupOrderInvariant_eq_standard :
    groupOrderInvariant ⟨2, Ak3.ak3⟩ = groupOrderInvariant ⟨2, standard 2⟩ := by
  rw [groupOrderInvariant_ak3, groupOrderInvariant_standard]

/-- The cyclicity component takes the same value at AK(3) and at the standard
pair. -/
theorem ak3_cyclicityInvariant_eq_standard :
    cyclicityInvariant ⟨2, Ak3.ak3⟩ = cyclicityInvariant ⟨2, standard 2⟩ := by
  rw [cyclicityInvariant_ak3, cyclicityInvariant_standard]

/-- The refinement invariant takes the same value at AK(3) and at the standard
pair. -/
theorem ak3_refinementInvariant_eq_standard :
    refinementInvariant ⟨2, Ak3.ak3⟩ = refinementInvariant ⟨2, standard 2⟩ := by
  unfold refinementInvariant
  rw [groupOrderInvariant_ak3, groupOrderInvariant_standard,
    cyclicityInvariant_ak3, cyclicityInvariant_standard]

/-- The separation hypothesis at the refinement invariant is false for the
AK(3) pair, so this invariant cannot discharge the exact goal. -/
theorem ak3_separation_hypothesis_false :
    ¬ (refinementInvariant ⟨2, Ak3.ak3⟩ ≠
        refinementInvariant ⟨2, standard 2⟩) :=
  fun h => h ak3_refinementInvariant_eq_standard

/-- The exact AK(3) stable separation goal.  No proof is asserted: this is the
open statement left by the invariant branch. -/
def ak3_stableSeparationGoal : Prop :=
  ¬ StableReachable ⟨2, Ak3.ak3⟩ ⟨2, standard 2⟩

/-- The conditional separation theorem at the refinement invariant: a value
difference would close the AK(3) goal.  The hypothesis is refuted above. -/
theorem ak3_stableSeparation_of_invariant_difference
    (h : refinementInvariant ⟨2, Ak3.ak3⟩ ≠
        refinementInvariant ⟨2, standard 2⟩) :
    ak3_stableSeparationGoal :=
  not_stableReachable_of_stableInvariant refinementInvariant_isStableInvariant h

/-! ## 6. Teeth: the free rank-two presentation -/

/-- The rank-two presentation all of whose relators are the identity word. -/
def trivialRelators : Relators 2 := fun _ => 1

/-- The relator set of `trivialRelators` is the singleton of the identity. -/
theorem range_trivialRelators :
    Set.range trivialRelators = ({1} : Set (Word 2)) := by
  ext x
  simp only [trivialRelators, Set.mem_range, Set.mem_singleton_iff]
  exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨0, h.symm⟩⟩

/-- The normal closure of the identity relator is the trivial subgroup. -/
theorem normalClosure_range_trivialRelators :
    Subgroup.normalClosure (Set.range trivialRelators) = ⊥ := by
  rw [range_trivialRelators]
  refine le_antisymm ?_ bot_le
  refine Subgroup.normalClosure_le_normal ?_
  intro x hx
  simpa using hx

/-- The group presented by the identity relators is the free group on two
generators. -/
noncomputable def presentedGroup_trivialRelators_mulEquiv :
    PresentedGroup (Set.range trivialRelators) ≃* FreeGroup (Fin 2) :=
  (QuotientGroup.quotientMulEquivOfEq normalClosure_range_trivialRelators).trans
    QuotientGroup.quotientBot

/-- The free presentation has order component `0`. -/
theorem groupOrderInvariant_trivialRelators :
    groupOrderInvariant ⟨2, trivialRelators⟩ = 0 := by
  unfold groupOrderInvariant
  rw [Nat.card_congr presentedGroup_trivialRelators_mulEquiv.toEquiv]
  exact Nat.card_eq_zero_of_infinite

/-- The free group on two generators is not cyclic.  The map that sends the two
generators to the two standard generators of `ℤ × ℤ` is a surjection, and
`ℤ × ℤ` is not cyclic. -/
theorem freeGroup_two_not_isCyclic : ¬ IsCyclic (FreeGroup (Fin 2)) := by
  intro h
  haveI : IsCyclic (FreeGroup (Fin 2)) := h
  let f : FreeGroup (Fin 2) →* (Multiplicative ℤ × Multiplicative ℤ) :=
    FreeGroup.lift fun i : Fin 2 =>
      if i = 0 then (Multiplicative.ofAdd (1 : ℤ), 1)
      else (1, Multiplicative.ofAdd (1 : ℤ))
  have hf : Function.Surjective f := by
    rintro ⟨a, b⟩
    refine ⟨(FreeGroup.of (0 : Fin 2)) ^ (Multiplicative.toAdd a) *
      (FreeGroup.of (1 : Fin 2)) ^ (Multiplicative.toAdd b), ?_⟩
    simp [f, map_zpow, ← Int.ofAdd_mul]
  exact not_isCyclic_prod_of_infinite_nontrivial (Multiplicative ℤ) (Multiplicative ℤ)
    (isCyclic_of_surjective f hf)

/-- The group presented by the identity relators is not cyclic. -/
theorem not_isCyclic_presentedGroup_trivialRelators :
    ¬ IsCyclic (PresentedGroup (Set.range trivialRelators)) := by
  intro h
  exact freeGroup_two_not_isCyclic
    ((MulEquiv.isCyclic presentedGroup_trivialRelators_mulEquiv).mp h)

/-- The free presentation has cyclicity component `false`. -/
theorem cyclicityInvariant_trivialRelators :
    cyclicityInvariant ⟨2, trivialRelators⟩ = false := by
  unfold cyclicityInvariant
  rw [if_neg not_isCyclic_presentedGroup_trivialRelators]

/-- The order component separates the free presentation from the standard
rank-two tuple. -/
theorem not_stableReachable_trivialRelators_standard_by_order :
    ¬ StableReachable ⟨2, trivialRelators⟩ ⟨2, standard 2⟩ := by
  refine not_stableReachable_of_stableInvariant groupOrderInvariant_isStableInvariant ?_
  rw [groupOrderInvariant_trivialRelators, groupOrderInvariant_standard]
  decide

/-- The cyclicity component separates the free presentation from the standard
rank-two tuple. -/
theorem not_stableReachable_trivialRelators_standard_by_cyclicity :
    ¬ StableReachable ⟨2, trivialRelators⟩ ⟨2, standard 2⟩ := by
  refine not_stableReachable_of_stableInvariant cyclicityInvariant_isStableInvariant ?_
  rw [cyclicityInvariant_trivialRelators, cyclicityInvariant_standard]
  decide

/-! ## 7. Axiom record

The fresh reader runs the file with `lake env lean AcStableInvariant2.lean` and
checks that each listing is a subset of `[propext, Classical.choice,
Quot.sound]`. -/

#print axioms not_stableReachable_of_stableInvariant
#print axioms groupOrderInvariant_isStableInvariant
#print axioms cyclicityInvariant_isStableInvariant
#print axioms refinementInvariant_isStableInvariant
#print axioms ak3_separation_hypothesis_false
#print axioms not_stableReachable_trivialRelators_standard_by_order

end StableInvariant2
end AC
