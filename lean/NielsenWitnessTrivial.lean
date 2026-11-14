/-
# NielsenWitnessTrivial — the (5,7) witness presents the trivial group

`NielsenMeasure12Cover.lean` consumes `PresentsTrivialGroup` at the witness in the
full form of the rotated descent (`NielsenRotationNormalForm.lean:445`), and the
covering obligation at `:137` assumes it at every measure-12 state. The tree did
not prove it. This module proves it.

The proof does not use a coset enumeration. It uses the 25-step path already in
the tree, from the witness to the abelian-terminal endpoint
`v13 = (y⁻¹, y⁻¹ x y)` (`NielsenSevenStage.lean:358`), and then three official
steps from `v13` to the standard tuple:

  1. invert the first relator:            `(y, y⁻¹ x y)`
  2. conjugate the second relator by `y`: `(y, x)`
  3. swap the two relators:               `(x, y)`

The standard tuple presents the trivial group (`AcBase.lean:30`), and
`ProofAttempt.presents_of_reachable` (`AcProof.lean:498`) carries triviality back
along the composite path.

No `sorry`, `admit`, `axiom`, or `native_decide` occurs in this file. The axiom
record at the end reports the trusted base.
-/

import AcNielsenDefs
import AcProof
import AcBase
import NielsenRotationNormalForm
import NielsenSevenStage
import Mathlib.Tactic

set_option autoImplicit false

namespace AC
namespace Nielsen
namespace WitnessTrivial

open RotationNormalForm
open SevenStage

/-- Swapping the two relators of an ordered pair is one official derived path. -/
theorem reachable_swap_pair (a b : Word 2) : Reachable ![a, b] ![b, a] := by
  have h := ProofAttempt.reachable_swap (![a, b] : Relators 2) (i := 0) (j := 1)
    (by decide)
  have he : Function.update
      (Function.update (![a, b] : Relators 2) 0 ((![a, b] : Relators 2) 1)) 1
      ((![a, b] : Relators 2) 0) = ![b, a] := by
    funext i
    fin_cases i <;> rfl
  rwa [he] at h

/-- The endpoint `v13 = (y⁻¹, y⁻¹ x y)` reaches the standard tuple `(x, y)`. -/
theorem reachable_v13_standard : Reachable v13 (standard 2) := by
  classical
  set S1 : Relators 2 := Function.update v13 0 (v13 0)⁻¹ with hS1
  have hstep1 : Step v13 S1 := by
    rw [hS1]
    exact Step.inv v13 0
  have hS1_0 : S1 0 = gy := by
    simp [hS1, v13]
  have hS1_1 : S1 1 = gy⁻¹ * gx * gy := by
    simp [hS1, v13]
  set S2 : Relators 2 := Function.update S1 1 (gy * S1 1 * gy⁻¹) with hS2def
  have hstep2 : Step S1 S2 := by
    rw [hS2def]
    exact Step.conj S1 1 gy
  have hS2_0 : S2 0 = gy := by
    simp [hS2def, hS1_0]
  have hS2_1 : S2 1 = gx := by
    rw [hS2def, Function.update_self, hS1_1]
    group
  have hS2 : S2 = ![gy, gx] := by
    funext i
    fin_cases i
    · simpa using hS2_0
    · simpa using hS2_1
  have hswap : Reachable ![gy, gx] (standard 2) := by
    have h := reachable_swap_pair (a := gy) (b := gx)
    have hstd : (![gx, gy] : Relators 2) = standard 2 := by
      funext i
      fin_cases i <;> rfl
    rwa [hstd] at h
  have h3 : Reachable S2 (standard 2) := hS2.symm ▸ hswap
  exact (Relation.ReflTransGen.single hstep1).trans
    ((Relation.ReflTransGen.single hstep2).trans h3)

/-- **The (5,7) witness presents the trivial group.** The path is the proved
25-step descent to `v13`, then inversion, conjugation, and the swap to the
standard tuple. -/
theorem presentsTrivialGroup_witnessState : PresentsTrivialGroup witnessState := by
  have h : Reachable witnessState (standard 2) :=
    SevenStage.reachable_witness_v13.trans reachable_v13_standard
  exact (ProofAttempt.presents_of_reachable h).mpr
    (Base.presentsTrivialGroup_standard 2)

/-- The full rotated descent needs no separate triviality hypothesis once the
witness triviality is proved. -/
theorem fiveSeven_rotated_witness_descent_full_closed
    (hbase : SevenStageWitnessDescent) (a b : ℕ) :
    ∃ T : Relators 2, Reachable (witnessRotate a b) T ∧ AbelianTerminal T ∧
      PresentsTrivialGroup T ∧
      cyclicNielsenLength T < cyclicNielsenLength (witnessRotate a b) :=
  fiveSeven_rotated_witness_descent_full presentsTrivialGroup_witnessState hbase a b

/-! ## Axiom record

A fresh reader runs `lake env lean NielsenWitnessTrivial.lean` and checks that
each listing is a subset of `[propext, Classical.choice, Quot.sound]`. -/

#print axioms presentsTrivialGroup_witnessState
#print axioms reachable_v13_standard
#print axioms fiveSeven_rotated_witness_descent_full_closed

end WitnessTrivial
end Nielsen
end AC
