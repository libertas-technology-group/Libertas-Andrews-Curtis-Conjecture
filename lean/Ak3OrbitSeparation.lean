import Ak3
import Ak3Separation
import Ak3Invariant
import BranchC4

/-!
# Ak3OrbitSeparation — the BS(2,3) image-pair invariant

The candidate in this module is the group Andrews–Curtis orbit of the AK(3)
image pair in the Baumslag–Solitar group

```text
BS(2,3) = ⟨a, t | t a² t⁻¹ = a³⟩.
```

It is a predicate on `Relators 2` read through the fixed quotient map
`F₂ →* BS(2,3)`, not a function of the relation subgroup, the relation module,
the lower central series, a finite quotient, or a multiplicative-equivalence
class. The pruned families are referenced below, not restated.

The named open input is `BS23OrbitSeparation`. The final theorem reduces
`¬ Reachable Ak3.ak3 (standard 2)` to that input. It does not prove the input.
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace AC
namespace Ak3OrbitSeparation

open BranchC3
open BranchC4

/-! ## 0. The pruned declarations, referenced not restated -/

#check Ak3Invariant.relationSubgroup
#check Ak3Invariant.relationInvariant_cannot_separate
#check Ak3Invariant.relationModule
#check Ak3Invariant.relationModule_cannot_separate
#check Ak3Invariant.lowerCentralQuotient
#check Ak3Invariant.lowerCentralQuotient_mulEquiv
#check Ak3Invariant.finiteQuotient_cannot_separate
#check Ak3Invariant.groupInvariant_ak3_eq_standard
#check Ak3Invariant.groupRingInvariant_ak3_eq_standard
#check Ak3Separation.PSLIndexSeparation
#check Ak3Separation.pslIndexSeparation_false
#check Ak3Separation.pairNormalClosure_relators_eq_standard

/-! ## 1. The BS(2,3) presentation -/

/-- The BS(2,3) relator `t a² t⁻¹ a⁻³`. -/
def bs23Relator : Word 2 :=
  FreeGroup.of 1 * (FreeGroup.of 0) ^ (2 : ℕ) * (FreeGroup.of 1)⁻¹ *
    (FreeGroup.of 0) ^ (-3 : ℤ)

/-- The singleton relator set of BS(2,3). -/
def bs23Rels : Set (Word 2) := {bs23Relator}

/-- The presented group `⟨a, t | t a² t⁻¹ a⁻³⟩`, the Baumslag–Solitar group
BS(2,3). -/
abbrev BS23 : Type := PresentedGroup bs23Rels

/-- The quotient map `F₂ →* BS(2,3)`. -/
noncomputable def bs23Map : Word 2 →* BS23 :=
  PresentedGroup.mk bs23Rels

/-- The image pair of a rank-two presentation in BS(2,3). -/
noncomputable def bs23Tuple (P : Relators 2) : BS23 × BS23 :=
  (bs23Map (P 0), bs23Map (P 1))

/-! ## 2. The candidate invariant and the named open input -/

/-- The symmetric group AC component of the image pair in BS(2,3). -/
noncomputable def BS23OrbitInvariant (P : Relators 2) : Prop :=
  GroupACReachable BS23 (bs23Tuple (standard 2)) (bs23Tuple P) ∨
  GroupACReachable BS23 (bs23Tuple P) (bs23Tuple (standard 2))

/-- The open BS(2,3) orbit separation statement. -/
noncomputable def BS23OrbitSeparation : Prop :=
  ¬ BS23OrbitInvariant Ak3.ak3

/-! ## 3. Preservation under the official moves -/

theorem bs23Tuple_update (P : Relators 2) (i : Fin 2) (w : Word 2) :
    bs23Tuple (Function.update P i w) = pairUpdate (bs23Tuple P) i (bs23Map w) := by
  fin_cases i <;> simp [bs23Tuple, pairUpdate, Function.update]

@[simp] theorem pairGet_bs23Tuple (P : Relators 2) (i : Fin 2) :
    pairGet (bs23Tuple P) i = bs23Map (P i) := by
  fin_cases i <;> rfl

theorem step_bs23 {P Q : Relators 2} (h : Step P Q) :
    GroupACReachable BS23 (bs23Tuple P) (bs23Tuple Q) := by
  cases h with
  | inv i =>
      rw [bs23Tuple_update, map_inv]
      simpa only [pairGet_bs23Tuple] using
        (Relation.ReflTransGen.single (GroupACStep.inv (bs23Tuple P) i))
  | mulRight i j hij =>
      rw [bs23Tuple_update, map_mul]
      simpa only [pairGet_bs23Tuple] using
        (Relation.ReflTransGen.single (GroupACStep.mulRight (bs23Tuple P) i j hij))
  | conj i w =>
      rw [bs23Tuple_update]
      simpa only [map_mul, map_inv, pairGet_bs23Tuple] using
        (Relation.ReflTransGen.single (GroupACStep.conj (bs23Tuple P) i (bs23Map w)))

theorem reachable_bs23 {P Q : Relators 2} (h : Reachable P Q) :
    GroupACReachable BS23 (bs23Tuple P) (bs23Tuple Q) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.trans (step_bs23 hstep)

theorem bs23OrbitInvariant_standard : BS23OrbitInvariant (standard 2) :=
  Or.inl Relation.ReflTransGen.refl

theorem bs23OrbitInvariant_of_step {P Q : Relators 2} (h : Step P Q)
    (hP : BS23OrbitInvariant P) : BS23OrbitInvariant Q := by
  rcases hP with hP | hP
  · exact Or.inl (hP.trans (step_bs23 h))
  · exact Or.inr ((groupACReachable_symm (step_bs23 h)).trans hP)

theorem bs23OrbitInvariant_of_reachable {P Q : Relators 2} (h : Reachable P Q)
    (hP : BS23OrbitInvariant P) : BS23OrbitInvariant Q := by
  induction h with
  | refl => exact hP
  | tail _ hstep ih => exact bs23OrbitInvariant_of_step hstep ih

/-! ## 4. The conditional separation theorem -/

theorem bs23OrbitSeparation_implies_not_reachable
    (h : BS23OrbitSeparation) : ¬ Reachable Ak3.ak3 (standard 2) := by
  intro hpath
  exact h (Or.inr (reachable_bs23 hpath))

end Ak3OrbitSeparation
end AC

#print axioms AC.Ak3OrbitSeparation.bs23OrbitSeparation_implies_not_reachable
