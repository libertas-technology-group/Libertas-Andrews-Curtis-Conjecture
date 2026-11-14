import Ak3
import BranchC3
import AcQuotient

/-!
# AK(3) separation through the PSL quotient index

`Ak3.ak3` is the AK(3) presentation, and `Ak3.ak3_presentsTrivial` proves that it
presents the trivial group.  The counterproof route asks for the negative
reachability statement `¬ Reachable ak3 (standard 2)`.

`AcQuotient.psl_index_separates` reduces that statement to a concrete
normal-closure index in `PSL(2, ℤ) = C₂ * C₃`.  The hypothesis is

    (pairNormalClosure (tuplePSL ak3)).index ≠ 1,

and the theorem turns it into `¬ Reachable ak3 (standard 2)`.  This file states
the hypothesis as `PSLIndexSeparation`, proves the implication, and proves the
hypothesis false.

The image pair in `PSL` is

    tuplePSL ak3 = (a * b⁻¹, a * b * a * b⁻¹ * a * b⁻¹).

In the quotient by the normal closure of the pair, the first component gives
`a = b`, and the second reduces to `b⁻¹`; the quotient is therefore trivial.
The normal closure is the whole group and the index is one.

The failure holds for every quotient.  Since `ak3` presents the trivial group,
its relators normally generate the free group `F₂`.  For every group `H` and
every homomorphism `f : F₂ →* H`, the normal closure of the two relator images
equals the normal closure of the two standard generator images.  A group-valued
normal-closure index therefore cannot separate the AK(3) pair from the standard
pair in any quotient.

## Main results

* `PSLIndexSeparation` : the exact concrete separation hypothesis.
* `pslIndexSeparation_implies_not_reachable` : the conditional theorem.
* `tuplePSL_ak3` : the image pair in `PSL(2, ℤ)`.
* `pairNormalClosure_relators_eq_standard` : the no-separation theorem for every
  group and every homomorphism out of `F₂`.
* `pairNormalClosure_tuplePSL_ak3_eq_top` : the PSL normal closure is the whole
  group.
* `psl_index_eq_one` : the PSL index is one.
* `pslIndexSeparation_false` : the separation hypothesis is refuted.

## Status

No `sorry`, no `admit`, no user `axiom`, no `native_decide`.  Single-file check
from `lean/`: `lake env lean Ak3Separation.lean`.  The unconditional statement
`¬ Reachable ak3 (standard 2)` is not proved here.  The quotient-index branch is
pruned: its hypothesis is false, and the exact open goal remains
`¬ Reachable ak3 (standard 2)`.
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace AC.Ak3Separation

open BranchC3

/-! ## 1. The exact separation hypothesis -/

/-- The concrete PSL(2, ℤ) normal-closure index separation for AK(3).  This is the
hypothesis of `AcQuotient.psl_index_separates` at the AK(3) presentation. -/
def PSLIndexSeparation : Prop :=
  (pairNormalClosure (tuplePSL Ak3.ak3)).index ≠ 1

/-- The conditional theorem: the concrete PSL index separation settles AK(3). -/
theorem pslIndexSeparation_implies_not_reachable (h : PSLIndexSeparation) :
    ¬ Reachable Ak3.ak3 (standard 2) :=
  Quotient.psl_index_separates (P := Ak3.ak3) h

/-! ## 2. The image pair in `PSL(2, ℤ)` -/

/-- The element `a` is an involution. -/
theorem a_inv : a⁻¹ = a := by
  calc a⁻¹ = a⁻¹ * 1 := by simp
    _ = a⁻¹ * a ^ 2 := by rw [a_sq]
    _ = a := by group

/-- The fourth inverse power of `b` is the first inverse power, because `b³ = 1`. -/
theorem b_zpow_neg_four : b ^ (-4 : ℤ) = b⁻¹ := by
  have h4 : b ^ (4 : ℕ) = b := by
    calc b ^ (4 : ℕ) = b ^ (3 : ℕ) * b := by group
      _ = 1 * b := by rw [b_cube]
      _ = b := by simp
  have h : b ^ (-4 : ℤ) = (b ^ (4 : ℕ))⁻¹ := by
    rw [show (-4 : ℤ) = Int.negSucc 3 from rfl, zpow_negSucc]
  rw [h, h4]

/-- The first AK(3) relator maps to `a * b⁻¹`. -/
theorem pslMap_ak3R1 : pslMap Ak3.ak3R1 = a * b⁻¹ := by
  have ha3 : a ^ (3 : ℕ) = a := by
    calc a ^ (3 : ℕ) = a ^ (2 : ℕ) * a := by group
      _ = 1 * a := by rw [a_sq]
      _ = a := by simp
  simp only [Ak3.ak3R1, map_mul, map_pow, map_zpow, pslMap_of_zero, pslMap_of_one]
  rw [ha3, b_zpow_neg_four]

/-- The second AK(3) relator maps to the reduced word `a * b * a * b⁻¹ * a * b⁻¹`. -/
theorem pslMap_ak3R2 :
    pslMap Ak3.ak3R2 = a * b * a * b⁻¹ * a * b⁻¹ := by
  simp [Ak3.ak3R2, map_mul, map_inv, pslMap_of_zero, pslMap_of_one, a_inv]

/-- The image pair of the AK(3) presentation in `PSL(2, ℤ)`. -/
theorem tuplePSL_ak3 :
    tuplePSL Ak3.ak3 = (a * b⁻¹, a * b * a * b⁻¹ * a * b⁻¹) := by
  change (pslMap Ak3.ak3R1, pslMap Ak3.ak3R2) = _
  rw [pslMap_ak3R1, pslMap_ak3R2]

/-! ## 3. The relators normally generate the free group -/

/-- The AK(3) relators normally generate `F₂`.  This is the normal-closure form of
`Ak3.ak3_presentsTrivial`: the presented group is the quotient of `F₂` by this
normal closure, and a subsingleton quotient forces every element into the
normal closure. -/
theorem normalClosure_range_ak3 :
    Subgroup.normalClosure (Set.range Ak3.ak3) = ⊤ := by
  haveI : Subsingleton (PresentedGroup (Set.range Ak3.ak3)) := Ak3.ak3_presentsTrivial
  rw [eq_top_iff]
  intro x _
  rw [← PresentedGroup.mk_eq_one_iff (rels := Set.range Ak3.ak3)]
  exact Subsingleton.elim _ _

/-- The standard generator pair normally generates `F₂`. -/
theorem normalClosure_range_standard :
    Subgroup.normalClosure (Set.range (standard 2)) = ⊤ := by
  have h : Subgroup.closure (Set.range (standard 2)) = ⊤ := by
    rw [show Set.range (standard 2)
        = Set.range (FreeGroup.of : Fin 2 → FreeGroup (Fin 2)) from rfl]
    exact FreeGroup.closure_range_of (Fin 2)
  have hle := Subgroup.closure_le_normalClosure (s := Set.range (standard 2))
  rw [h] at hle
  exact eq_top_iff.mpr hle

/-! ## 4. A homomorphism cannot distinguish the two pairs -/

/-- The image of a normal closure lies in the normal closure of the image.  The
preimage of `normalClosure (f '' s)` is normal and contains `s`, so it contains
`normalClosure s`.  No surjectivity of `f` is required. -/
theorem map_normalClosure_le {G H : Type*} [Group G] [Group H]
    (f : G →* H) (s : Set G) :
    Subgroup.map f (Subgroup.normalClosure s) ≤ Subgroup.normalClosure (f '' s) := by
  rw [Subgroup.map_le_iff_le_comap]
  apply Subgroup.normalClosure_le_normal
  intro x hx
  exact Subgroup.subset_normalClosure (Set.mem_image_of_mem f hx)

/-- If `R` normally generates `G`, the image of `R` normally generates the range
of `f`.  Both directions use monotonicity of the normal closure; the reverse
direction uses `map_normalClosure_le` on the whole group. -/
theorem normalClosure_image_range_eq {G H : Type*} [Group G] [Group H]
    (f : G →* H) (R : Set G) (hR : Subgroup.normalClosure R = ⊤) :
    Subgroup.normalClosure (f '' R) = Subgroup.normalClosure (Set.range f) := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro y ⟨x, _hx, rfl⟩
    exact Subgroup.subset_normalClosure ⟨x, rfl⟩
  · apply Subgroup.normalClosure_le_normal
    rintro y ⟨x, rfl⟩
    have hx : x ∈ Subgroup.normalClosure R := by
      rw [hR]
      exact Subgroup.mem_top x
    exact map_normalClosure_le f R (Subgroup.mem_map_of_mem f hx)

/-- The image of the range of `ak3` is the pair of relator images. -/
theorem image_range_ak3 {H : Type*} [Group H] (f : Word 2 →* H) :
    f '' Set.range Ak3.ak3 = ({f (Ak3.ak3 0), f (Ak3.ak3 1)} : Set H) := by
  ext y
  constructor
  · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨_, ⟨0, rfl⟩, rfl⟩
    · exact ⟨_, ⟨1, rfl⟩, rfl⟩

/-- The image of the range of the standard pair is the pair of generator images. -/
theorem image_range_standard {H : Type*} [Group H] (f : Word 2 →* H) :
    f '' Set.range (standard 2)
      = ({f (FreeGroup.of (0 : Fin 2)), f (FreeGroup.of (1 : Fin 2))} : Set H) := by
  ext y
  constructor
  · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨_, ⟨0, rfl⟩, rfl⟩
    · exact ⟨_, ⟨1, rfl⟩, rfl⟩

/-- For every group and every homomorphism out of `F₂`, the two AK(3) relator
images and the two standard generator images have the same normal closure.  The
AK(3) relators normally generate `F₂`, so both pairs normally generate the range
of the homomorphism. -/
theorem pairNormalClosure_relators_eq_standard {H : Type*} [Group H]
    (f : Word 2 →* H) :
    pairNormalClosure (f (Ak3.ak3 0), f (Ak3.ak3 1))
      = pairNormalClosure (f (FreeGroup.of (0 : Fin 2)), f (FreeGroup.of (1 : Fin 2))) := by
  have h1 := normalClosure_image_range_eq f (Set.range Ak3.ak3) normalClosure_range_ak3
  have h2 := normalClosure_image_range_eq f (Set.range (standard 2)) normalClosure_range_standard
  calc
    pairNormalClosure (f (Ak3.ak3 0), f (Ak3.ak3 1))
        = Subgroup.normalClosure (f '' Set.range Ak3.ak3) := by
          rw [image_range_ak3 f]
          rfl
    _ = Subgroup.normalClosure (Set.range f) := h1
    _ = Subgroup.normalClosure (f '' Set.range (standard 2)) := h2.symm
    _ = pairNormalClosure (f (FreeGroup.of (0 : Fin 2)), f (FreeGroup.of (1 : Fin 2))) := by
          rw [image_range_standard f]
          rfl

/-! ## 5. The PSL index is one -/

/-- The relator-image pair and the standard pair have the same normal closure in
`PSL(2, ℤ)`. -/
theorem pairNormalClosure_tuplePSL_ak3_eq_standard :
    pairNormalClosure (tuplePSL Ak3.ak3) = pairNormalClosure standardPSL := by
  have h := pairNormalClosure_relators_eq_standard (H := PSL) pslMap
  simpa [tuplePSL, standardPSL, pslMap_of_zero, pslMap_of_one] using h

/-- The normal closure of the AK(3) image pair in `PSL(2, ℤ)` is the whole group. -/
theorem pairNormalClosure_tuplePSL_ak3_eq_top :
    pairNormalClosure (tuplePSL Ak3.ak3) = ⊤ := by
  rw [pairNormalClosure_tuplePSL_ak3_eq_standard, Quotient.pairNormalClosure_standardPSL]

/-- The two indices compared by the quotient test are equal. -/
theorem psl_indices_eq :
    (pairNormalClosure (tuplePSL Ak3.ak3)).index
      = (pairNormalClosure standardPSL).index := by
  rw [pairNormalClosure_tuplePSL_ak3_eq_standard]

/-- The PSL index of the AK(3) image pair is one.  The normal closure is the
whole group, and the index of the whole group is one. -/
theorem psl_index_eq_one :
    (pairNormalClosure (tuplePSL Ak3.ak3)).index = 1 := by
  rw [pairNormalClosure_tuplePSL_ak3_eq_top]
  exact Subgroup.index_eq_one.mpr rfl

/-- The exact separation hypothesis of the PSL quotient index is false for AK(3). -/
theorem pslIndexSeparation_false : ¬ PSLIndexSeparation := by
  intro h
  exact h psl_index_eq_one

end AC.Ak3Separation
