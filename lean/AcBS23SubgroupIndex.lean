module

public import Ak3OrbitSeparation

@[expose] public section

/-!
# AcBS23SubgroupIndex — the subgroup and index obstruction target

A subgroup that contains the standard pair and excludes the AK(3) image pair
would separate the pair without a normal-form oracle. This file states that
target. It does not construct the subgroup.
-/

set_option autoImplicit false

namespace AC
namespace BS23Subgroup

open Ak3OrbitSeparation

/-- Both elements of a pair lie in the subgroup. -/
def PairInSubgroup (H : Subgroup BS23) (x y : BS23) : Prop :=
  x ∈ H ∧ y ∈ H

/-- A subgroup contains the standard pair and excludes the AK(3) image pair. -/
def SubgroupIndexSeparation : Prop :=
  ∃ H : Subgroup BS23,
    PairInSubgroup H (bs23Map (FreeGroup.of 0)) (bs23Map (FreeGroup.of 1)) ∧
    ¬ PairInSubgroup H (bs23Map (Ak3.ak3 0)) (bs23Map (Ak3.ak3 1))

/-- The standard pair generates the whole Baumslag–Solitar group. -/
theorem standardPair_generates :
    Subgroup.closure
      ({bs23Map (FreeGroup.of 0), bs23Map (FreeGroup.of 1)} : Set BS23) = ⊤ := by
  rw [← PresentedGroup.closure_range_of (rels := bs23Rels) (α := Fin 2)]
  congr 1
  ext x
  constructor
  · intro hx
    have hx' : x = bs23Map (FreeGroup.of 0) ∨
        x = bs23Map (FreeGroup.of 1) := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx
    rcases hx' with hx' | hx'
    · exact ⟨0, by simpa [bs23Map, PresentedGroup.of] using hx'.symm⟩
    · exact ⟨1, by simpa [bs23Map, PresentedGroup.of] using hx'.symm⟩
  · intro hx
    rcases hx with ⟨i, hi⟩
    fin_cases i
    · exact Or.inl (by simpa [bs23Map, PresentedGroup.of] using hi.symm)
    · exact Or.inr (by simpa [bs23Map, PresentedGroup.of] using hi.symm)

/-- The subgroup-index separation target is false: a subgroup that contains the
standard pair is the whole group, so it cannot exclude the AK(3) image pair. -/
theorem subgroupIndexSeparation_false : ¬ SubgroupIndexSeparation := by
  rintro ⟨H, hstd, hnot⟩
  rcases hstd with ⟨h0, h1⟩
  have htop : H = ⊤ := by
    apply eq_top_iff.mpr
    rw [← standardPair_generates]
    exact (Subgroup.closure_le (K := H)).mpr (by
      intro x hx
      have hx' : x = bs23Map (FreeGroup.of 0) ∨
          x = bs23Map (FreeGroup.of 1) := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx
      rcases hx' with hx' | hx'
      · rw [hx']
        exact h0
      · rw [hx']
        exact h1)
  exact hnot ⟨by simp [htop], by simp [htop]⟩

end BS23Subgroup
end AC

#check @AC.BS23Subgroup.PairInSubgroup
#check @AC.BS23Subgroup.SubgroupIndexSeparation
#check @AC.BS23Subgroup.subgroupIndexSeparation_false
