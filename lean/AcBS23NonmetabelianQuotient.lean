import Ak3OrbitSeparation
import BranchC3

/-!
# AcBS23NonmetabelianQuotient — the non-metabelian quotient target

Every finite quotient of BS(2,3) is metacyclic. This file states the next test:
an infinite non-metabelian quotient whose image pair is not in the group
Andrews–Curtis orbit of the standard pair. It does not construct the quotient.
-/

set_option autoImplicit false

namespace AC
namespace BS23Nonmetabelian

open Ak3OrbitSeparation
open BranchC3
open BranchC4

/-- A non-metabelian quotient separates the pair when the images are not in the
symmetric group-Andrews–Curtis orbit. -/
def NonmetabelianQuotientSeparation : Prop :=
  ∃ (G : Type) (_ : Group G) (f : BS23 →* G),
    ¬ GroupACReachable G
      (f (bs23Map (FreeGroup.of 0)), f (bs23Map (FreeGroup.of 1)))
      (f (bs23Map (Ak3.ak3 0)), f (bs23Map (Ak3.ak3 1)))


/-- Apply a group homomorphism to both components of a pair. -/
def mapPair {G H : Type*} [Group G] [Group H] (f : G →* H) (p : G × G) : H × H :=
  (f p.1, f p.2)

@[simp] theorem mapPair_pairUpdate {G H : Type*} [Group G] [Group H]
    (f : G →* H) (p : G × G) (i : Fin 2) (x : G) :
    mapPair f (pairUpdate p i x) = pairUpdate (mapPair f p) i (f x) := by
  fin_cases i <;> simp [mapPair, pairUpdate]

@[simp] theorem mapPair_pairGet {G H : Type*} [Group G] [Group H]
    (f : G →* H) (p : G × G) (i : Fin 2) :
    f (pairGet p i) = pairGet (mapPair f p) i := by
  fin_cases i <;> simp [mapPair, pairGet]

/-- One group Andrews–Curtis move maps forward under a group homomorphism. -/
theorem groupACStep_map {G H : Type*} [Group G] [Group H]
    (f : G →* H) {p q : G × G} (h : GroupACStep G p q) :
    GroupACStep H (mapPair f p) (mapPair f q) := by
  cases h with
  | inv i =>
      simpa using GroupACStep.inv (mapPair f p) i
  | mulRight i j hij =>
      simpa using GroupACStep.mulRight (mapPair f p) i j hij
  | conj i w =>
      simpa [map_mul, map_inv] using
        GroupACStep.conj (mapPair f p) i (f w)

/-- A whole group Andrews–Curtis path maps forward under a group homomorphism. -/
theorem groupACReachable_map {G H : Type*} [Group G] [Group H]
    (f : G →* H) {p q : G × G} (h : GroupACReachable G p q) :
    GroupACReachable H (mapPair f p) (mapPair f q) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact ih.trans (Relation.ReflTransGen.single (groupACStep_map f hstep))

/-- The non-metabelian quotient target is equivalent to the open BS(2,3)
separation target. -/
theorem nonmetabelianQuotientSeparation_iff_bs23OrbitSeparation :
    NonmetabelianQuotientSeparation ↔ BS23OrbitSeparation := by
  constructor
  · rintro ⟨G, _, f, hf⟩ hsep
    rcases hsep with hstd | hak
    · exact hf (groupACReachable_map f hstd)
    · exact hf (groupACReachable_map f (groupACReachable_symm hak))
  · intro hsep
    refine ⟨BS23, inferInstance, MonoidHom.id BS23, ?_⟩
    intro hstep
    exact hsep (Or.inl (by simpa [mapPair] using hstep))

end BS23Nonmetabelian
end AC

#check @AC.BS23Nonmetabelian.NonmetabelianQuotientSeparation
#check @AC.BS23Nonmetabelian.nonmetabelianQuotientSeparation_iff_bs23OrbitSeparation
