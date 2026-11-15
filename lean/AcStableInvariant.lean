module

public import AC
public import AcBase
public import AcProof
public import Ak3
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.Tactic

@[expose] public section

/-!
# Stable AC: a presented-group invariant and the AK(3) no-go

The stable Andrews–Curtis move set `AC.StableStep` (`AC.lean:93-99`) permits the
ordinary AC moves at fixed rank, insertion of an isolated generator–relator pair,
and removal of such a pair.  A stable invariant is a function on presentations
that is constant on every stable step.

This file tests the *perfectness indicator*:

    abelianizationTrivialInvariant P = true  iff  Abelianization (presented group of P)
                                                  is a one-element group.

It is not the triviality indicator of `AcStableCounterexample.lean`: a nontrivial
perfect group makes the two indicators differ.  The invariant is constant on
`StableStep`, because every stable step preserves the presented group up to a
multiplicative equivalence, and abelianization is a functor on multiplicative
equivalence.

The AK(3) presentation and the standard rank-two presentation both present the
one-element group (`Ak3.ak3_presentsTrivial`,
`Base.presentsTrivialGroup_standard`).  Both abelianizations are therefore
one-element, so the perfectness indicator takes the same value at the two
presentations.  The separation theorem is stated and proved, but its hypothesis
is refuted for this pair: this invariant cannot separate AK(3).  The same no-go
is proved for every invariant of the isomorphism class of the presented group.

The exact separation proposition is left as the `def` `ak3_stableSeparationGoal`;
it is not asserted.  The published stable trivialization of AK(3) (Shehper et
al., arXiv:2408.15332; Lisitsa, arXiv:2501.18601) is consistent with the no-go
and rules out any stable invariant separating this pair.

## Status

Every declaration in this file is closed.  The file contains no proof holes, no
admissions, no native evaluation, and no user axioms.  Single-file check from
`lean/`: `lake env lean AcStableInvariant.lean`.  The writer of this file is not
its verifier.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace AC
namespace StableInvariant

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

/-! ## 2. The presented group is unchanged by an ordinary AC step -/

/-- Every ordinary AC step preserves the normal closure of the relator set. -/
theorem normalClosure_range_step {n : ℕ} {R S : Relators n} (h : Step R S) :
    Subgroup.normalClosure (Set.range S) =
      Subgroup.normalClosure (Set.range R) := by
  cases h with
  | inv i => exact ProofAttempt.normalClosure_range_inv R i
  | mulRight i j hij => exact ProofAttempt.normalClosure_range_mulRight R i j hij
  | conj i w => exact ProofAttempt.normalClosure_range_conj R i w

/-- Every ordinary AC step preserves the presented group literally. -/
theorem presentedGroup_eq_of_step {n : ℕ} {R S : Relators n} (h : Step R S) :
    PresentedGroup (Set.range S) = PresentedGroup (Set.range R) := by
  have hN := normalClosure_range_step h
  show (FreeGroup (Fin n) ⧸ Subgroup.normalClosure (Set.range S)) =
       (FreeGroup (Fin n) ⧸ Subgroup.normalClosure (Set.range R))
  rw [hN]

/-- An ordinary AC step gives a multiplicative equivalence of presented groups. -/
theorem presentedGroup_mulEquiv_of_step {n : ℕ} {R S : Relators n} (h : Step R S) :
    Nonempty (PresentedGroup (Set.range R) ≃* PresentedGroup (Set.range S)) := by
  have hN := normalClosure_range_step h
  refine ⟨QuotientGroup.congr (Subgroup.normalClosure (Set.range R))
    (Subgroup.normalClosure (Set.range S)) (MulEquiv.refl (FreeGroup (Fin n))) ?_⟩
  simpa only [MulEquiv.toMonoidHom_refl, Subgroup.map_id] using hN.symm

/-! ## 3. Stabilization: the new generator is retracted away -/

/-- The inserted relator of `AC.stabilize R g i` is the new generator. -/
theorem stabilize_apply_self {n : ℕ} (R : Relators n) (g i : Fin (n + 1)) :
    AC.stabilize R g i i = FreeGroup.of g := by
  simp [AC.stabilize]

/-- At an old relator position `i.succAbove k`, the stabilized tuple carries the
old relator `R k` with the new generator inserted into the generator type. -/
theorem stabilize_apply_succAbove {n : ℕ} (R : Relators n) (g i : Fin (n + 1))
    (k : Fin n) :
    AC.stabilize R g i (i.succAbove k) = FreeGroup.map g.succAbove (R k) := by
  simp [AC.stabilize]

/-- The retraction that sends the new generator to `1` and every other
generator to the old generator that `Fin.succAbove g` sends to it. -/
noncomputable def retractHom {n : ℕ} (g : Fin (n + 1)) :
    FreeGroup (Fin (n + 1)) →* FreeGroup (Fin n) :=
  FreeGroup.lift fun k =>
    if h : k = g then 1
    else FreeGroup.of (Classical.choose (Fin.exists_succAbove_eq (x := k) (y := g) h))

/-- The retraction kills the new generator. -/
theorem retractHom_of_g {n : ℕ} (g : Fin (n + 1)) :
    retractHom g (FreeGroup.of g) = 1 := by
  rw [retractHom, FreeGroup.lift_apply_of]
  simp

/-- The retraction recovers an old generator from its inserted position. -/
theorem retractHom_of_succAbove {n : ℕ} (g : Fin (n + 1)) (k : Fin n) :
    retractHom g (FreeGroup.of (g.succAbove k)) = FreeGroup.of k := by
  rw [retractHom, FreeGroup.lift_apply_of]
  rw [dite_eq_right (Fin.succAbove_ne g k)]
  congr 1
  exact Fin.succAbove_right_injective
    (Classical.choose_spec
      (Fin.exists_succAbove_eq (x := g.succAbove k) (y := g) (Fin.succAbove_ne g k)))

/-- The retraction is a left inverse to the insertion of the old generators. -/
theorem retractHom_map {n : ℕ} (g : Fin (n + 1)) (w : FreeGroup (Fin n)) :
    retractHom g (FreeGroup.map g.succAbove w) = w := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of k => exact retractHom_of_succAbove g k
  | inv_of k _ => simp [retractHom_of_succAbove]
  | mul x y ihx ihy => rw [map_mul, map_mul, ihx, ihy]

/-- Lifting a function after `FreeGroup.map` is the same as lifting the
composite function. -/
theorem lift_comp_map {n : ℕ} {α : Type*} [Group α]
    (f : Fin (n + 1) → α) (g : Fin (n + 1)) (w : FreeGroup (Fin n)) :
    FreeGroup.lift f (FreeGroup.map g.succAbove w) =
      FreeGroup.lift (fun k => f (g.succAbove k)) w := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of k => simp
  | inv_of k _ => simp
  | mul x y ihx ihy => rw [map_mul, map_mul, ihx, ihy, map_mul]

/-- The forward generator map: the new generator goes to `1`, and an old
generator goes to its preimage under `Fin.succAbove g`. -/
noncomputable def forwardGenerator {n : ℕ} (R : Relators n) (g : Fin (n + 1)) :
    Fin (n + 1) → PresentedGroup (Set.range R) :=
  fun k => PresentedGroup.mk (Set.range R) (retractHom g (FreeGroup.of k))

/-- The forward map sends the new generator to `1`. -/
theorem forwardGenerator_of_g {n : ℕ} (R : Relators n) (g : Fin (n + 1)) :
    forwardGenerator R g g = 1 := by
  simp [forwardGenerator, retractHom_of_g]

/-- The forward map recovers an old generator from its inserted position. -/
theorem forwardGenerator_of_succAbove {n : ℕ} (R : Relators n) (g : Fin (n + 1))
    (k : Fin n) :
    forwardGenerator R g (g.succAbove k) = PresentedGroup.of (rels := Set.range R) k := by
  simp only [forwardGenerator, retractHom_of_succAbove]
  rfl

/-- The backward generator map: an old generator goes to its inserted position. -/
noncomputable def backwardGenerator {n : ℕ} (R : Relators n) (g i : Fin (n + 1)) :
    Fin n → PresentedGroup (Set.range (AC.stabilize R g i)) :=
  fun k => PresentedGroup.of (rels := Set.range (AC.stabilize R g i)) (g.succAbove k)

/-- The map from the stabilized presented group to the old presented group. -/
noncomputable def stabilizeForward {n : ℕ} (R : Relators n) (g i : Fin (n + 1)) :
    PresentedGroup (Set.range (AC.stabilize R g i)) →* PresentedGroup (Set.range R) :=
  PresentedGroup.toGroup (rels := Set.range (AC.stabilize R g i))
    (f := forwardGenerator R g) (by
      intro r hr
      rcases hr with ⟨j, rfl⟩
      rcases Fin.eq_self_or_eq_succAbove i j with h | ⟨k, hk⟩
      · rw [h, stabilize_apply_self]
        rw [FreeGroup.lift_apply_of]
        exact forwardGenerator_of_g R g
      · rw [hk, stabilize_apply_succAbove]
        rw [lift_comp_map]
        have hf : (fun k => forwardGenerator R g (g.succAbove k)) =
            (fun k => PresentedGroup.of (rels := Set.range R) k) := by
          funext k
          exact forwardGenerator_of_succAbove R g k
        rw [hf]
        have hmk : FreeGroup.lift (fun k => PresentedGroup.of (rels := Set.range R) k) =
            PresentedGroup.mk (Set.range R) := by
          ext x
          exact (FreeGroup.lift_unique (PresentedGroup.mk (Set.range R))
            (by intro k; rfl)).symm
        rw [hmk]
        exact PresentedGroup.one_of_mem (Set.mem_range_self k))

/-- The map from the old presented group to the stabilized presented group. -/
noncomputable def stabilizeBackward {n : ℕ} (R : Relators n) (g i : Fin (n + 1)) :
    PresentedGroup (Set.range R) →* PresentedGroup (Set.range (AC.stabilize R g i)) :=
  PresentedGroup.toGroup (rels := Set.range R) (f := backwardGenerator R g i) (by
    intro r hr
    rcases hr with ⟨k, rfl⟩
    have h : FreeGroup.lift (backwardGenerator R g i) =
        (PresentedGroup.mk (Set.range (AC.stabilize R g i))).comp
          (FreeGroup.map g.succAbove) := by
      ext x
      exact (FreeGroup.lift_unique
        ((PresentedGroup.mk (Set.range (AC.stabilize R g i))).comp
          (FreeGroup.map g.succAbove))
        (by intro k
            simp only [backwardGenerator, MonoidHom.comp_apply, FreeGroup.map.of]
            rfl)).symm
    rw [h]
    change PresentedGroup.mk (Set.range (AC.stabilize R g i))
      (FreeGroup.map g.succAbove (R k)) = 1
    rw [← stabilize_apply_succAbove R g i k]
    exact PresentedGroup.one_of_mem ⟨i.succAbove k, rfl⟩)

/-- On a generator of the stabilized presented group, the forward map is the
forward generator map. -/
@[simp] theorem stabilizeForward_of {n : ℕ} (R : Relators n) (g i : Fin (n + 1))
    (k : Fin (n + 1)) :
    stabilizeForward R g i (PresentedGroup.of (rels := Set.range (AC.stabilize R g i)) k) =
      forwardGenerator R g k :=
  PresentedGroup.toGroup.of _

/-- On a generator of the old presented group, the backward map is the backward
generator map. -/
@[simp] theorem stabilizeBackward_of {n : ℕ} (R : Relators n) (g i : Fin (n + 1))
    (k : Fin n) :
    stabilizeBackward R g i (PresentedGroup.of (rels := Set.range R) k) =
      backwardGenerator R g i k :=
  PresentedGroup.toGroup.of _

/-- The forward map is a left inverse to the backward map. -/
theorem stabilizeForward_comp_backward {n : ℕ} (R : Relators n) (g i : Fin (n + 1)) :
    (stabilizeForward R g i).comp (stabilizeBackward R g i) = MonoidHom.id _ := by
  apply PresentedGroup.ext
  intro k
  simp [backwardGenerator, stabilizeForward_of, stabilizeBackward_of,
    forwardGenerator_of_succAbove]

/-- The backward map is a left inverse to the forward map. -/
theorem stabilizeBackward_comp_forward {n : ℕ} (R : Relators n) (g i : Fin (n + 1)) :
    (stabilizeBackward R g i).comp (stabilizeForward R g i) = MonoidHom.id _ := by
  apply PresentedGroup.ext
  intro k
  by_cases hk : k = g
  · rw [hk]
    have hrel : PresentedGroup.of (rels := Set.range (AC.stabilize R g i)) g = 1 := by
      change PresentedGroup.mk (Set.range (AC.stabilize R g i)) (FreeGroup.of g) = 1
      rw [← stabilize_apply_self R g i]
      exact PresentedGroup.one_of_mem ⟨i, rfl⟩
    rw [hrel]
    simp [stabilizeForward_of, stabilizeBackward_of, forwardGenerator_of_g]
  · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (x := k) (y := g) hk
    rw [← hj]
    simp [backwardGenerator, stabilizeForward_of, stabilizeBackward_of,
      forwardGenerator_of_succAbove]

/-- Adding an isolated generator–relator pair preserves the presented group up to
multiplicative equivalence. -/
noncomputable def stabilizeMulEquiv {n : ℕ} (R : Relators n) (g i : Fin (n + 1)) :
    PresentedGroup (Set.range (AC.stabilize R g i)) ≃* PresentedGroup (Set.range R) where
  toFun := stabilizeForward R g i
  invFun := stabilizeBackward R g i
  left_inv := fun x => DFunLike.congr_fun (stabilizeBackward_comp_forward R g i) x
  right_inv := fun x => DFunLike.congr_fun (stabilizeForward_comp_backward R g i) x
  map_mul' := fun x y => map_mul (stabilizeForward R g i) x y

/-! ## 4. Every stable step preserves the presented group up to equivalence -/

/-- Every stable step gives a multiplicative equivalence of presented groups. -/
theorem stableStep_presentedGroup_mulEquiv {P Q : Presentation} (h : StableStep P Q) :
    Nonempty (PresentedGroup (Set.range P.2) ≃* PresentedGroup (Set.range Q.2)) := by
  cases h with
  | ac hstep => exact presentedGroup_mulEquiv_of_step hstep
  | stabilize R g i => exact ⟨(stabilizeMulEquiv R g i).symm⟩
  | destabilize R g i => exact ⟨stabilizeMulEquiv R g i⟩

/-- An invariant of the isomorphism class of the presented group is constant on
every stable step. -/
def IsPresentedGroupInvariant {α : Type*} (I : Presentation → α) : Prop :=
  ∀ ⦃P Q : Presentation⦄,
    Nonempty (PresentedGroup (Set.range P.2) ≃* PresentedGroup (Set.range Q.2)) →
    I P = I Q

/-- Every invariant of the presented group's isomorphism class is a stable
invariant. -/
theorem isPresentedGroupInvariant_isStableInvariant {α : Type*}
    {I : Presentation → α} (hI : IsPresentedGroupInvariant I) :
    IsStableInvariant I := by
  intro P Q hstep
  exact hI (stableStep_presentedGroup_mulEquiv hstep)

/-- A multiplicative equivalence between one-element groups. -/
def subsingletonMulEquiv (G H : Type*) [Group G] [Group H]
    [Subsingleton G] [Subsingleton H] : G ≃* H where
  toFun := fun _ => 1
  invFun := fun _ => 1
  left_inv := fun x => Subsingleton.elim _ _
  right_inv := fun x => Subsingleton.elim _ _
  map_mul' := fun _ _ => by simp

/-- Every invariant of the presented group's isomorphism class has the same value
at AK(3) and at the standard rank-two presentation. -/
theorem presentedGroupInvariant_cannot_separate {α : Type*} {I : Presentation → α}
    (hI : IsPresentedGroupInvariant I) :
    ¬ (I ⟨2, Ak3.ak3⟩ ≠ I ⟨2, standard 2⟩) := by
  intro h
  have : Subsingleton (PresentedGroup (Set.range Ak3.ak3)) := Ak3.ak3_presentsTrivial
  have : Subsingleton (PresentedGroup (Set.range (standard 2))) :=
    Base.presentsTrivialGroup_standard 2
  exact h (hI ⟨subsingletonMulEquiv _ _⟩)

/-! ## 5. The concrete perfectness indicator -/

/-- A one-element group has a one-element abelianization. -/
theorem subsingleton_abelianization {G : Type*} [Group G] [Subsingleton G] :
    Subsingleton (Abelianization G) := by
  refine ⟨fun a b => ?_⟩
  induction a using QuotientGroup.induction_on with
  | _ x =>
    induction b using QuotientGroup.induction_on with
    | _ y =>
      rw [Subsingleton.elim x y]

/-- Multiplicative equivalence transports subsingleton-ness. -/
theorem subsingleton_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Subsingleton G ↔ Subsingleton H := by
  constructor
  · intro hG
    exact ⟨fun a b => e.symm.injective (Subsingleton.elim _ _)⟩
  · intro hH
    exact ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩

/-- The perfectness indicator: `true` exactly when the abelianization of the
presented group is a one-element group. -/
noncomputable def abelianizationTrivialInvariant (P : Presentation) : Bool :=
  if Subsingleton (Abelianization (PresentedGroup (Set.range P.2))) then true else false

/-- The perfectness indicator is an invariant of the presented group's
isomorphism class. -/
theorem abelianizationTrivialInvariant_isPresentedGroupInvariant :
    IsPresentedGroupInvariant abelianizationTrivialInvariant := by
  intro P Q hPQ
  obtain ⟨e⟩ := hPQ
  have hE : Abelianization (PresentedGroup (Set.range P.2)) ≃*
      Abelianization (PresentedGroup (Set.range Q.2)) :=
    MulEquiv.abelianizationCongr e
  have hiff : Subsingleton (Abelianization (PresentedGroup (Set.range P.2))) ↔
      Subsingleton (Abelianization (PresentedGroup (Set.range Q.2))) :=
    subsingleton_of_mulEquiv hE
  unfold abelianizationTrivialInvariant
  by_cases hP : Subsingleton (Abelianization (PresentedGroup (Set.range P.2)))
  · have hQ : Subsingleton (Abelianization (PresentedGroup (Set.range Q.2))) := hiff.mp hP
    simp [hP, hQ]
  · have hQ : ¬ Subsingleton (Abelianization (PresentedGroup (Set.range Q.2))) :=
      fun hq => hP (hiff.mpr hq)
    simp [hP, hQ]

/-- The perfectness indicator is a stable invariant. -/
theorem abelianizationTrivialInvariant_isStableInvariant :
    IsStableInvariant abelianizationTrivialInvariant :=
  isPresentedGroupInvariant_isStableInvariant
    abelianizationTrivialInvariant_isPresentedGroupInvariant

/-! ## 6. The AK(3) test and the no-go -/

/-- The perfectness indicator is `true` at AK(3). -/
theorem abelianizationTrivialInvariant_ak3 :
    abelianizationTrivialInvariant ⟨2, Ak3.ak3⟩ = true := by
  unfold abelianizationTrivialInvariant
  have : Subsingleton (PresentedGroup (Set.range Ak3.ak3)) := Ak3.ak3_presentsTrivial
  have : Subsingleton (Abelianization (PresentedGroup (Set.range Ak3.ak3))) :=
    subsingleton_abelianization
  rw [ite_eq_left (inferInstance :
    Subsingleton (Abelianization (PresentedGroup (Set.range Ak3.ak3))))]

/-- The perfectness indicator is `true` at the standard rank-two presentation. -/
theorem abelianizationTrivialInvariant_standard :
    abelianizationTrivialInvariant ⟨2, standard 2⟩ = true := by
  unfold abelianizationTrivialInvariant
  have : Subsingleton (PresentedGroup (Set.range (standard 2))) :=
    Base.presentsTrivialGroup_standard 2
  have : Subsingleton (Abelianization (PresentedGroup (Set.range (standard 2)))) :=
    subsingleton_abelianization
  rw [ite_eq_left (inferInstance :
    Subsingleton (Abelianization (PresentedGroup (Set.range (standard 2)))))]

/-- The perfectness indicator is constant on the AK(3) pair. -/
theorem ak3_abelianizationTrivialInvariant_eq_standard :
    abelianizationTrivialInvariant ⟨2, Ak3.ak3⟩ =
      abelianizationTrivialInvariant ⟨2, standard 2⟩ := by
  rw [abelianizationTrivialInvariant_ak3, abelianizationTrivialInvariant_standard]

/-- The separation hypothesis at the perfectness indicator is false for the AK(3)
pair, so this invariant cannot discharge the exact goal. -/
theorem ak3_separation_hypothesis_false :
    ¬ (abelianizationTrivialInvariant ⟨2, Ak3.ak3⟩ ≠
        abelianizationTrivialInvariant ⟨2, standard 2⟩) :=
  fun h => h ak3_abelianizationTrivialInvariant_eq_standard

/-- The exact AK(3) stable separation goal.  No proof is asserted: this is the
open statement left by the invariant branch. -/
def ak3_stableSeparationGoal : Prop :=
  ¬ StableReachable ⟨2, Ak3.ak3⟩ ⟨2, standard 2⟩

/-- The conditional separation theorem at the perfectness indicator: a value
difference would close the AK(3) goal.  The hypothesis is refuted above. -/
theorem ak3_stableSeparation_of_invariant_difference
    (h : abelianizationTrivialInvariant ⟨2, Ak3.ak3⟩ ≠
        abelianizationTrivialInvariant ⟨2, standard 2⟩) :
    ak3_stableSeparationGoal :=
  not_stableReachable_of_stableInvariant
    abelianizationTrivialInvariant_isStableInvariant h

/-! ## 7. Axiom record

The fresh reader runs the file with `lake env lean AcStableInvariant.lean` and
checks the following.  Each listing must be a subset of
`[propext, Classical.choice, Quot.sound]`.  A listing that contains the
proof-hole axiom, or any user-declared axiom, is a defect. -/

#print axioms not_stableReachable_of_stableInvariant
#print axioms abelianizationTrivialInvariant_isStableInvariant
#print axioms presentedGroupInvariant_cannot_separate
#print axioms ak3_separation_hypothesis_false

end StableInvariant
end AC
