module

/-
# NielsenMeasure12Cover — the covering obligation for the measure-12 slice

`NielsenMeasure12.lean:53` states the universal lengths 5 and 7 slice as the
definition `bothLong_measure12_uniform`. `NielsenRotationNormalForm.lean:428`
transports the seven-stage witness descent across coordinate rotations of the
fixed pair `(r7Shape, s5Shape)`, conditionally on the base-orientation descent
`SevenStageWitnessDescent` (`NielsenRotationNormalForm.lean:418`). The
transport starts at a rotation of the witness. No declaration in this tree
carries an arbitrary measure-12 state to such a rotation: a search of
`lean/*.lean` for `witnessRotate` returns the definition at
`NielsenRotationNormalForm.lean:304`, the lemmas whose source state is
`witnessState` or one of its rotations (`:342`, `:385`, `:428`, `:437`,
`:445`), and the prose at `NielsenMeasure12.lean:34`.

This module states that link as `measure12_covers_witness` and proves
`bothLong_measure12_uniform_of_cover`: the covering statement together with
`SevenStageWitnessDescent` implies `bothLong_measure12_uniform`.

## What is proved here

* `cycLen_mk_of_isCyclicallyReduced`: the cyclic length of a word presented by a
  cyclically reduced list is the list length.
* `cyclicNielsenLength_witnessState`: the witness has cyclic Nielsen length 12.
* `cyclicNielsenLength_eq_twelve`: a state whose two cyclic lengths are 5 and 7
  has cyclic Nielsen length 12.
* `altSevenShape_isCyclicallyReduced` and `altSevenShape_not_rotate`: a second
  cyclically reduced length-seven relator exists, and no rotation of the witness
  relator equals it. The witness is one point of the slice.
* `reachable_swapState`, `abelianTerminal_swapState`, and
  `isSignedPermutation_of_swapState`: the two-relator swap is an official path
  and carries the hypotheses of the covering obligation. A state whose cyclic
  lengths are `5` at coordinate `0` and `7` at coordinate `1` is carried into
  the ordered `(7,5)` case by this path.
* `measure12_covers_witness_of_ordered`: the ordered `(7,5)` classification
  implies the covering obligation.
* `bothLong_measure12_uniform_of_cover`: the covering statement and the base
  witness descent imply the universal slice. Presentation-triviality reaches
  the endpoint by `ProofAttempt.presents_of_reachable` (`AcProof.lean:498`), so
  the separate triviality hypothesis of
  `fiveSeven_rotated_witness_descent_full`
  (`NielsenRotationNormalForm.lean:445`) is not consumed.

## What is not proved here

`measure12_covers_witness` and `measure12_ordered_classification`. The tree
holds no reduction from an arbitrary cyclically reduced measure-12 state to the
witness pair or to a rotation of it: every witness-relative path in the tree
starts at `witnessState` or at one of its rotations
(`NielsenRotationNormalForm.lean:342`, `:385`, `:428`). A rank-two reduction
theorem in the tree, `AC.Euclid.abelianTerminal_reachable_of_expSpan_top`
(`AcEuclid.lean:338`), reaches an abelian-terminal state of unbounded cyclic
Nielsen length by Euclidean row operations; it supplies neither a measure bound
nor a witness orientation. The ordered classification is the exact missing
lemma, and the covering statement stays a definition until it is written.

No `sorry`, `admit`, `axiom`, or `native_decide` occurs in this file. The axiom
record at the end reports the trusted base of the main theorem.
-/

public import AcNielsenDefs
public import AcProof
public import NielsenRotationNormalForm
public import NielsenMeasure12
public import NielsenSevenStage

@[expose] public section

set_option autoImplicit false

namespace AC
namespace Nielsen
namespace Measure12Cover

open RotationNormalForm

/-! ## 1. The cyclic length of a cyclically reduced list -/

/-- The cyclic length of a word presented by a cyclically reduced list is the
length of the list. -/
theorem cycLen_mk_of_isCyclicallyReduced {n : ℕ} {L : List (Fin n × Bool)}
    (h : FreeGroup.IsCyclicallyReduced L) :
    cycLen (FreeGroup.mk L) = L.length := by
  unfold cycLen
  rw [FreeGroup.toWord_mk, FreeGroup.isReduced_iff_reduce_eq.mp h.isReduced,
    reduceCyclically_eq_self h]

/-! ## 2. The measure of the witness -/

/-- The witness has cyclic Nielsen length `7 + 5 = 12`. -/
theorem cyclicNielsenLength_witnessState :
    cyclicNielsenLength witnessState = 12 := by
  rw [cyclicNielsenLength_pair, witnessState_zero, witnessState_one,
    cycLen_mk_of_isCyclicallyReduced r7Shape_isCyclicallyReduced,
    cycLen_mk_of_isCyclicallyReduced s5Shape_isCyclicallyReduced,
    r7Shape_length, s5Shape_length]

/-- A state whose two cyclic lengths are `5` and `7`, in either order, has
cyclic Nielsen length `12`. -/
theorem cyclicNielsenLength_eq_twelve (S : Relators 2)
    (h : (cycLen (S 0) = 5 ∧ cycLen (S 1) = 7) ∨
      (cycLen (S 0) = 7 ∧ cycLen (S 1) = 5)) :
    cyclicNielsenLength S = 12 := by
  rw [cyclicNielsenLength_pair]
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0, h1]

/-! ## 3. The witness is one point of the slice -/

/-- A cyclically reduced length-seven relator that is not a rotation of the
witness relator: `x y X y X Y Y`. -/
def altSevenShape : List (Fin 2 × Bool) :=
  [(0, false), (1, false), (0, true), (1, false), (0, true), (1, true), (1, true)]

theorem altSevenShape_length : altSevenShape.length = 7 := rfl

theorem altSevenShape_isCyclicallyReduced :
    FreeGroup.IsCyclicallyReduced altSevenShape :=
  (isCycRedB_iff altSevenShape).mp (by decide)

/-- No cyclic rotation of the witness relator equals `altSevenShape`. Every
rotation of `r7Shape` carries two occurrences of `x`; `altSevenShape` carries
one. -/
theorem altSevenShape_not_rotate (a : ℕ) : r7Shape.rotate a ≠ altSevenShape := by
  have hmod : r7Shape.rotate (a % 7) = r7Shape.rotate a :=
    List.rotate_mod r7Shape a
  rw [← hmod]
  exact (by decide : ∀ k : Fin 7, r7Shape.rotate (k : ℕ) ≠ altSevenShape)
    ⟨a % 7, Nat.mod_lt a (by decide)⟩

/-! ## 4. The covering obligation -/

/-- **The covering obligation.** Every cyclically reduced measure-12 state that
is abelian terminal, presents the trivial group, is not a signed permutation,
and has cyclic Nielsen lengths `5` and `7` in either order reaches a
coordinate rotation of the seven-stage witness. The antecedent repeats the
hypotheses of `bothLong_measure12_uniform` (`NielsenMeasure12.lean:53`) one for
one; the conclusion supplies the left end that
`fiveSeven_rotated_witness_descent` (`NielsenRotationNormalForm.lean:428`)
consumes. -/
def measure12_covers_witness : Prop :=
  ∀ (S : Relators 2),
    AbelianTerminal S → PresentsTrivialGroup S →
    (∀ i : Fin 2, FreeGroup.IsCyclicallyReduced (S i).toWord) →
    ¬ ProofAttempt.IsSignedPermutation S →
    ((cycLen (S 0) = 5 ∧ cycLen (S 1) = 7) ∨
      (cycLen (S 0) = 7 ∧ cycLen (S 1) = 5)) →
    ∃ a b : ℕ, Reachable S (witnessRotate a b)

/-! ## 5. The coordinate swap and the ordered classification

The covering obligation carries the length pair as a disjunction. The swap below
removes the disjunction: the `(5,7)` order is carried into the `(7,5)` order by
one derived path, and the hypotheses transport along that path. The remaining
input is the ordered classification, stated as a definition because the tree
contains no arbitrary-state classification. -/

/-- Swap the two coordinates of a rank-two state. -/
def swapState (S : Relators 2) : Relators 2 := ![S 1, S 0]

@[simp] theorem swapState_zero (S : Relators 2) : swapState S 0 = S 1 := rfl

@[simp] theorem swapState_one (S : Relators 2) : swapState S 1 = S 0 := rfl

/-- The two-relator swap is one official derived path. -/
theorem reachable_swapState (S : Relators 2) : Reachable S (swapState S) := by
  have h := ProofAttempt.reachable_swap S (i := 0) (j := 1) (by decide)
  have he : Function.update (Function.update S 0 (S 1)) 1 (S 0) = swapState S := by
    funext i
    fin_cases i <;> rfl
  rwa [he] at h

/-- The swap carries the abelian-terminal predicate. -/
theorem abelianTerminal_swapState (S : Relators 2) (h : AbelianTerminal S) :
    AbelianTerminal (swapState S) := by
  obtain ⟨σ, hσ, ε, hε⟩ := h
  refine ⟨fun i => σ (Equiv.swap (0 : Fin 2) 1 i),
    hσ.comp (Equiv.swap (0 : Fin 2) 1).bijective,
    fun i => ε (Equiv.swap (0 : Fin 2) 1 i), ?_⟩
  intro i
  fin_cases i
  · simpa using hε 1
  · simpa using hε 0

/-- The swap reflects the signed-permutation predicate. -/
theorem isSignedPermutation_of_swapState (S : Relators 2)
    (h : ProofAttempt.IsSignedPermutation (swapState S)) :
    ProofAttempt.IsSignedPermutation S := by
  obtain ⟨σ, hσ, ε, hε⟩ := h
  refine ⟨fun i => σ (Equiv.swap (0 : Fin 2) 1 i),
    hσ.comp (Equiv.swap (0 : Fin 2) 1).bijective,
    fun i => ε (Equiv.swap (0 : Fin 2) 1 i), ?_⟩
  intro i
  fin_cases i
  · simpa using hε 1
  · simpa using hε 0

/-- **The ordered classification.** Every cyclically reduced measure-12 state
with cyclic length `7` at coordinate `0` and `5` at coordinate `1`, abelian
terminal, presenting the trivial group, and not a signed permutation reaches a
coordinate rotation of the seven-stage witness. This is the arbitrary-state
classification the tree does not contain. -/
def measure12_ordered_classification : Prop :=
  ∀ (S : Relators 2),
    AbelianTerminal S → PresentsTrivialGroup S →
    (∀ i : Fin 2, FreeGroup.IsCyclicallyReduced (S i).toWord) →
    ¬ ProofAttempt.IsSignedPermutation S →
    cycLen (S 0) = 7 → cycLen (S 1) = 5 →
    ∃ a b : ℕ, Reachable S (witnessRotate a b)

/-- **The ordered classification closes the covering obligation.** A state with
cyclic lengths `5` and `7` in the other order is swapped into the ordered case
by `reachable_swapState`. The swap carries abelian terminality, triviality, and
cyclic reducedness, reflects the signed-permutation exclusion, and exchanges
the two cyclic lengths. -/
theorem measure12_covers_witness_of_ordered
    (h : measure12_ordered_classification) : measure12_covers_witness := by
  intro S hAb hP hCyc hPerm hLen
  rcases hLen with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have hreach : Reachable S (swapState S) := reachable_swapState S
    have hAb' : AbelianTerminal (swapState S) := abelianTerminal_swapState S hAb
    have hP' : PresentsTrivialGroup (swapState S) :=
      (ProofAttempt.presents_of_reachable hreach).mp hP
    have hCyc' : ∀ i : Fin 2,
        FreeGroup.IsCyclicallyReduced ((swapState S) i).toWord := by
      intro i
      fin_cases i
      · simpa using hCyc 1
      · simpa using hCyc 0
    have hPerm' : ¬ ProofAttempt.IsSignedPermutation (swapState S) := by
      intro hs
      exact hPerm (isSignedPermutation_of_swapState S hs)
    have hlen0 : cycLen ((swapState S) 0) = 7 := by simpa using h1
    have hlen1 : cycLen ((swapState S) 1) = 5 := by simpa using h0
    obtain ⟨a, b, hw⟩ := h (swapState S) hAb' hP' hCyc' hPerm' hlen0 hlen1
    exact ⟨a, b, hreach.trans hw⟩
  · exact h S hAb hP hCyc hPerm h0 h1

/-! ## 6. The covering obligation closes the slice -/

/-- **The covering lemma closes the measure-12 slice.** The covering obligation
and the base-orientation witness descent imply `bothLong_measure12_uniform`.
Reachability composes from `S` to the witness rotation and then to the
endpoint; presentation-triviality travels back from `S` along that composite by
`ProofAttempt.presents_of_reachable` (`AcProof.lean:498`); and both `S` and the
witness have cyclic Nielsen length `12`. -/
theorem bothLong_measure12_uniform_of_cover
    (hcover : measure12_covers_witness)
    (hbase : SevenStageWitnessDescent) :
    bothLong_measure12_uniform := by
  intro S hAb hP hCyc hPerm hLen
  obtain ⟨a, b, hreach⟩ := hcover S hAb hP hCyc hPerm hLen
  obtain ⟨T, hT, hAbT, hlt⟩ := fiveSeven_rotated_witness_descent hbase a b
  have hST : Reachable S T := hreach.trans hT
  refine ⟨T, hST, hAbT, (ProofAttempt.presents_of_reachable hST).mp hP, ?_⟩
  rw [cyclicNielsenLength_witnessRotate a b,
    cyclicNielsenLength_witnessState] at hlt
  have hS : cyclicNielsenLength S = 12 := cyclicNielsenLength_eq_twelve S hLen
  omega

/-! ## 6b. The base descent is proved, so the cover loses its parameter -/

/-- **The cover closes the slice with no external hypothesis.** The seven-stage
witness descent is proved at `NielsenSevenStage.lean:430`, so the conditional
form above loses its second parameter. -/
theorem bothLong_measure12_uniform_of_cover_proved
    (hcover : measure12_covers_witness) :
    bothLong_measure12_uniform :=
  bothLong_measure12_uniform_of_cover hcover SevenStage.sevenStageWitnessDescent

/-! ## 7. Axiom record

A fresh reader runs `lake env lean NielsenMeasure12Cover.lean` and checks that
each listing is a subset of `[propext, Classical.choice, Quot.sound]`. A
listing that contains the proof-hole axiom, or any user-declared axiom, is a
defect. -/

#print axioms bothLong_measure12_uniform_of_cover
#print axioms bothLong_measure12_uniform_of_cover_proved
#print axioms measure12_covers_witness_of_ordered
#print axioms cyclicNielsenLength_witnessState
#print axioms altSevenShape_not_rotate

end Measure12Cover
end Nielsen
end AC
