import AC

/-!
# The standard relator tuple presents the trivial group

At rank `n` the standard tuple is the family of free generators. The subgroup
closure of the generator set is the whole free group, and the normal closure of
a set is at least its subgroup closure, so the normal closure of the generator
set is the whole free group. The presented quotient is therefore a one-element
group, which is `PresentsTrivialGroup (standard n)`.
-/

namespace AC
namespace Base

/-- The generators of the free group generate it: the subgroup closure of the
range of `FreeGroup.of` is `⊤`. -/
theorem closure_range_of_eq_top {n : ℕ} :
    Subgroup.closure (Set.range (fun i : Fin n => FreeGroup.of i)) = ⊤ :=
  FreeGroup.closure_range_of (Fin n)

/-- The normal closure of the generator set is the whole free group. -/
theorem normalClosure_range_of_eq_top {n : ℕ} :
    Subgroup.normalClosure (Set.range (fun i : Fin n => FreeGroup.of i)) = ⊤ := by
  refine le_antisymm (Subgroup.normalClosure_le_normal (Set.subset_univ _)) ?_
  rw [← closure_range_of_eq_top (n := n)]
  exact Subgroup.closure_le_normalClosure

/-- The standard tuple presents the trivial group at every rank. -/
theorem presentsTrivialGroup_standard : ∀ n : ℕ, PresentsTrivialGroup (standard n) := by
  intro n
  change Subsingleton
    (FreeGroup (Fin n) ⧸
      Subgroup.normalClosure (Set.range (fun i : Fin n => FreeGroup.of i)))
  exact QuotientGroup.subsingleton_iff.mpr (normalClosure_range_of_eq_top (n := n))

end Base
end AC
