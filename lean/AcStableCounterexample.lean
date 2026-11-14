import AC
import AcBase
import AcProof
import Ak3
import Mathlib.Tactic

/-!
# Stable AC: invariants, separation, and the AK(3) test

The stable Andrews–Curtis problem permits two moves beyond `AC.Step`: adding an
isolated generator–relator pair and removing one (`AC.lean:93-99`).  This file
states the stable-invariant separation theorem and tests it against the AK(3)
presentation of `Ak3.lean`.

## Main results

1. `IsStableInvariant` is the property of a function on presentations that is
   constant on every `AC.StableStep`.
2. `eq_of_stableReachable` transports an invariant value along a finite stable
   path.
3. `not_stableReachable_of_stableInvariant` is the separation theorem: two
   presentations with different invariant values are not stably reachable.
4. `trivialityInvariant` is the Bool-valued indicator of
   `AC.PresentsTrivialGroup`.  `trivialityInvariant_stableStep` proves that it is
   constant on every stable step.  The stabilization case uses the retraction
   `retractHom`, which kills the inserted generator and recovers the old
   relators.
5. `ak3_stableSeparationGoal` is the exact AK(3) stable separation statement.

## The AK(3) test

`Ak3.ak3_presentsTrivial` and `Base.presentsTrivialGroup_standard` give the same
value of `trivialityInvariant` at AK(3) and at the standard rank-two tuple.
`ak3_trivialityInvariant_eq_standard` records that equality.  The separation
theorem therefore supplies no AK(3) separation from this invariant, and the
invariant branch is pruned.  The exact open goal remains the `def`
`ak3_stableSeparationGoal`.

## Status

No `sorry`, no `admit`, no user `axiom`, no `native_decide`.  Single-file check
from `lean/`: `lake env lean AcStableCounterexample.lean`.  The writer of this
file is not its verifier.
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace AC
namespace StableCounterexample

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

/-- Stable invariant separation: if the invariant values at `P` and `Q` differ,
then no finite stable path joins them. -/
theorem not_stableReachable_of_stableInvariant {α : Type*} {I : Presentation → α}
    (hI : IsStableInvariant I) {P Q : Presentation} (h : I P ≠ I Q) :
    ¬ StableReachable P Q :=
  fun hpath => h (eq_of_stableReachable hI hpath)

/-! ## 2. Stabilization and the retraction of the new generator -/

/-- The inserted relator of `AC.stabilize R g i` is the new generator. -/
theorem stabilize_apply_self {n : ℕ} (R : Relators n) (g i : Fin (n + 1)) :
    AC.stabilize R g i i = FreeGroup.of g := by
  simp [AC.stabilize]

/-- At an old relator position `i.succAbove k`, the stabilized tuple carries the
old relator `R k`, with the new generator inserted into the generator type. -/
theorem stabilize_apply_succAbove {n : ℕ} (R : Relators n) (g i : Fin (n + 1))
    (k : Fin n) :
    AC.stabilize R g i (i.succAbove k) = FreeGroup.map g.succAbove (R k) := by
  simp [AC.stabilize]

/-- The retraction of the new generator: the generator `g` maps to `1`, and any
other generator maps to the old generator that `Fin.succAbove g` sends to it. -/
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
  rw [dif_neg (Fin.succAbove_ne g k)]
  congr 1
  exact Fin.succAbove_right_injective
    (Classical.choose_spec
      (Fin.exists_succAbove_eq (x := g.succAbove k) (y := g) (Fin.succAbove_ne g k)))

/-- The retraction is a left inverse to the insertion of the old generators. -/
theorem retractHom_map {n : ℕ} (g : Fin (n + 1)) (w : FreeGroup (Fin n)) :
    retractHom g (FreeGroup.map g.succAbove w) = w := by
  induction w using FreeGroup.induction_on with
  | C1 => simp
  | of k => exact retractHom_of_succAbove g k
  | inv_of k ih => simp [ih, retractHom_of_succAbove]
  | mul x y ihx ihy => simp [ihx, ihy]

/-! ## 3. The normal closure is unchanged up to triviality -/

/-- The image of a normal closure under a group homomorphism is contained in the
normal closure of the image of the generating set. -/
theorem map_normalClosure_le {G H : Type*} [Group G] [Group H]
    (f : G →* H) (s : Set G) :
    Subgroup.map f (Subgroup.normalClosure s) ≤ Subgroup.normalClosure (f '' s) := by
  rw [Subgroup.map_le_iff_le_comap]
  exact Subgroup.normalClosure_le_normal
    (fun x hx => Subgroup.subset_normalClosure (Set.mem_image_of_mem f hx))

/-- The retraction sends every relator of the stabilized tuple into the normal
closure of the original relators. -/
theorem retractHom_stabilize_mem {n : ℕ} (R : Relators n) (g i : Fin (n + 1))
    (j : Fin (n + 1)) :
    retractHom g (AC.stabilize R g i j) ∈ Subgroup.normalClosure (Set.range R) := by
  rcases Fin.eq_self_or_eq_succAbove i j with h | ⟨k, hk⟩
  · rw [h, stabilize_apply_self, retractHom_of_g]
    exact Subgroup.one_mem _
  · rw [hk, stabilize_apply_succAbove, retractHom_map]
    exact Subgroup.subset_normalClosure ⟨k, rfl⟩

/-- The retraction image of the stabilized relator set lies in the normal closure
of the original relator set. -/
theorem retractHom_image_range_stabilize_subset {n : ℕ} (R : Relators n)
    (g i : Fin (n + 1)) :
    retractHom g '' Set.range (AC.stabilize R g i) ⊆
      Subgroup.normalClosure (Set.range R) := by
  rintro y ⟨x, ⟨j, rfl⟩, rfl⟩
  exact retractHom_stabilize_mem R g i j

/-- Adding an isolated generator–relator pair does not change whether the
normal closure of the relators is the whole free group. -/
theorem normalClosure_stabilize_eq_top_iff {n : ℕ} (R : Relators n)
    (g i : Fin (n + 1)) :
    Subgroup.normalClosure (Set.range (AC.stabilize R g i)) = ⊤ ↔
      Subgroup.normalClosure (Set.range R) = ⊤ := by
  constructor
  · intro h
    rw [eq_top_iff]
    intro x _
    have hx : FreeGroup.map g.succAbove x ∈
        Subgroup.normalClosure (Set.range (AC.stabilize R g i)) := by
      rw [h]
      exact Subgroup.mem_top _
    have hmap : x ∈ Subgroup.map (retractHom g)
        (Subgroup.normalClosure (Set.range (AC.stabilize R g i))) := by
      rw [← retractHom_map g x]
      exact Subgroup.mem_map_of_mem (retractHom g) hx
    have hle : Subgroup.map (retractHom g)
        (Subgroup.normalClosure (Set.range (AC.stabilize R g i))) ≤
        Subgroup.normalClosure (Set.range R) := by
      refine le_trans (map_normalClosure_le (retractHom g)
        (Set.range (AC.stabilize R g i))) ?_
      exact Subgroup.normalClosure_le_normal
        (retractHom_image_range_stabilize_subset R g i)
    exact hle hmap
  · intro h
    have hgen : Set.range (FreeGroup.of : Fin (n + 1) → FreeGroup (Fin (n + 1))) ⊆
        Subgroup.normalClosure (Set.range (AC.stabilize R g i)) := by
      rintro _ ⟨k, rfl⟩
      by_cases hk : k = g
      · rw [hk, ← stabilize_apply_self R g i]
        exact Subgroup.subset_normalClosure ⟨i, rfl⟩
      · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (x := k) (y := g) hk
        rw [← hj, ← FreeGroup.map.of (f := g.succAbove) (x := j)]
        have hjmem : FreeGroup.of j ∈ Subgroup.normalClosure (Set.range R) := by
          rw [h]
          exact Subgroup.mem_top _
        have hmem : FreeGroup.map g.succAbove (FreeGroup.of j) ∈
            Subgroup.map (FreeGroup.map g.succAbove)
              (Subgroup.normalClosure (Set.range R)) :=
          Subgroup.mem_map_of_mem (FreeGroup.map g.succAbove) hjmem
        have hle : Subgroup.map (FreeGroup.map g.succAbove)
            (Subgroup.normalClosure (Set.range R)) ≤
            Subgroup.normalClosure (Set.range (AC.stabilize R g i)) := by
          refine le_trans (map_normalClosure_le (FreeGroup.map g.succAbove)
            (Set.range R)) ?_
          refine Subgroup.normalClosure_le_normal ?_
          rintro y ⟨x, ⟨k', rfl⟩, rfl⟩
          rw [← stabilize_apply_succAbove R g i k']
          exact Subgroup.subset_normalClosure ⟨i.succAbove k', rfl⟩
        exact hle hmem
    have htop : (⊤ : Subgroup (FreeGroup (Fin (n + 1)))) ≤
        Subgroup.normalClosure (Set.range (AC.stabilize R g i)) := by
      rw [← FreeGroup.closure_range_of (Fin (n + 1))]
      exact (Subgroup.closure_le
        (Subgroup.normalClosure (Set.range (AC.stabilize R g i)))).mpr hgen
    exact eq_top_iff.mpr htop

/-- Triviality of the presented group is unchanged by one stabilization. -/
theorem presentsTrivialGroup_stabilize_iff {n : ℕ} (R : Relators n)
    (g i : Fin (n + 1)) :
    PresentsTrivialGroup (AC.stabilize R g i) ↔ PresentsTrivialGroup R := by
  unfold PresentsTrivialGroup PresentedGroup
  rw [QuotientGroup.subsingleton_iff, QuotientGroup.subsingleton_iff]
  exact normalClosure_stabilize_eq_top_iff R g i

/-- Triviality of the presented group is unchanged by every stable step. -/
theorem presentsTrivialGroup_stableStep {P Q : Presentation} (h : StableStep P Q) :
    PresentsTrivialGroup P.2 ↔ PresentsTrivialGroup Q.2 := by
  cases h with
  | ac hstep => exact ProofAttempt.presents_of_step hstep
  | stabilize R g i => exact (presentsTrivialGroup_stabilize_iff R g i).symm
  | destabilize R g i => exact presentsTrivialGroup_stabilize_iff R g i

/-! ## 4. The triviality indicator as a stable invariant -/

/-- The Bool-valued indicator of triviality of the presented group. -/
noncomputable def trivialityInvariant (P : Presentation) : Bool :=
  if PresentsTrivialGroup P.2 then true else false

/-- The indicator is `true` exactly on the trivial presentations. -/
theorem trivialityInvariant_eq_true_iff {P : Presentation} :
    trivialityInvariant P = true ↔ PresentsTrivialGroup P.2 := by
  unfold trivialityInvariant
  by_cases h : PresentsTrivialGroup P.2
  · simp [h]
  · simp [h]

/-- The indicator is constant on every stable step. -/
theorem trivialityInvariant_stableStep {P Q : Presentation} (h : StableStep P Q) :
    trivialityInvariant P = trivialityInvariant Q := by
  have hiff := presentsTrivialGroup_stableStep h
  unfold trivialityInvariant
  by_cases hp : PresentsTrivialGroup P.2
  · have hq : PresentsTrivialGroup Q.2 := hiff.mp hp
    simp [hp, hq]
  · have hq : ¬ PresentsTrivialGroup Q.2 := fun hq => hp (hiff.mpr hq)
    simp [hp, hq]

/-- The triviality indicator is a stable invariant. -/
theorem trivialityInvariant_isStableInvariant :
    IsStableInvariant trivialityInvariant := by
  intro P Q h
  exact trivialityInvariant_stableStep h

/-! ## 5. The AK(3) test -/

/-- The exact AK(3) stable separation goal.  No proof is asserted: this is the
open statement left by the invariant branch. -/
def ak3_stableSeparationGoal : Prop :=
  ¬ StableReachable ⟨2, Ak3.ak3⟩ ⟨2, standard 2⟩

/-- The triviality indicator has value `true` at AK(3). -/
theorem trivialityInvariant_ak3 :
    trivialityInvariant ⟨2, Ak3.ak3⟩ = true :=
  trivialityInvariant_eq_true_iff.mpr Ak3.ak3_presentsTrivial

/-- The triviality indicator has value `true` at the standard rank-two tuple. -/
theorem trivialityInvariant_standard :
    trivialityInvariant ⟨2, standard 2⟩ = true :=
  trivialityInvariant_eq_true_iff.mpr (Base.presentsTrivialGroup_standard 2)

/-- The certified invariant is constant on the AK(3) pair. -/
theorem ak3_trivialityInvariant_eq_standard :
    trivialityInvariant ⟨2, Ak3.ak3⟩ = trivialityInvariant ⟨2, standard 2⟩ := by
  rw [trivialityInvariant_ak3, trivialityInvariant_standard]

/-- The separation hypothesis at the certified invariant is false for the AK(3)
pair, so this invariant cannot discharge the exact goal. -/
theorem ak3_separation_hypothesis_false :
    ¬ (trivialityInvariant ⟨2, Ak3.ak3⟩ ≠ trivialityInvariant ⟨2, standard 2⟩) :=
  fun h => h ak3_trivialityInvariant_eq_standard

/-- The conditional separation theorem at the certified invariant: a value
difference would close the AK(3) goal.  The hypothesis is refuted above. -/
theorem ak3_stableSeparation_of_invariant_difference
    (h : trivialityInvariant ⟨2, Ak3.ak3⟩ ≠ trivialityInvariant ⟨2, standard 2⟩) :
    ak3_stableSeparationGoal :=
  not_stableReachable_of_stableInvariant trivialityInvariant_isStableInvariant h

end StableCounterexample
end AC
