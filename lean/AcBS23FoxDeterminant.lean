import Ak3OrbitSeparation
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# AcBS23FoxDeterminant — the Fox determinant in the BS(2,3) group ring

The free-group Fox determinant is a 21-term non-monomial. This file maps that
determinant into the integral group ring of BS(2,3) and states the unit test.
It does not claim that the element is a unit or a non-unit.
-/

set_option autoImplicit false

namespace AC
namespace BS23Fox

open Ak3OrbitSeparation

/-- The group-ring monomial of a free-group word after the map to BS(2,3). -/
noncomputable def q (w : Word 2) : MonoidAlgebra ℤ BS23 :=
  Finsupp.single (bs23Map w) (1 : ℤ)

/-- The 21-term Fox determinant after the quotient map. -/
noncomputable def foxDeterminantQuotient : MonoidAlgebra ℤ BS23 :=
  q (FreeGroup.of 0) +
  q ((FreeGroup.of 0) ^ 2) +
  q ((FreeGroup.of 0) ^ 3) +
  q ((FreeGroup.of 0) ^ 3 * (FreeGroup.of 1) ^ (-4 : ℤ)) +
  q ((FreeGroup.of 0) ^ 3 * (FreeGroup.of 1) ^ (-3 : ℤ)) +
  q ((FreeGroup.of 0) ^ 3 * (FreeGroup.of 1) ^ (-2 : ℤ)) +
  q ((FreeGroup.of 0) ^ 3 * (FreeGroup.of 1) ^ (-1 : ℤ)) -
  q (FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹) -
  q ((FreeGroup.of 0) ^ 2 * FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹) +
  q ((FreeGroup.of 0) ^ 3 * (FreeGroup.of 1) ^ (-4 : ℤ) * FreeGroup.of 0 * FreeGroup.of 1) +
  q ((FreeGroup.of 0) ^ 3 * (FreeGroup.of 1) ^ (-3 : ℤ) * FreeGroup.of 0 * FreeGroup.of 1) +
  q ((FreeGroup.of 0) ^ 3 * (FreeGroup.of 1) ^ (-2 : ℤ) * FreeGroup.of 0 * FreeGroup.of 1) +
  q ((FreeGroup.of 0) ^ 3 * (FreeGroup.of 1) ^ (-1 : ℤ) * FreeGroup.of 0 * FreeGroup.of 1) -
  q ((FreeGroup.of 0) ^ 3 * FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹) -
  q (FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹) -
  q ((FreeGroup.of 0) ^ 2 * FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹) -
  q ((FreeGroup.of 0) ^ 3 * FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹) -
  q ((FreeGroup.of 0) ^ 3 * (FreeGroup.of 1) ^ (-4 : ℤ) * FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹) -
  q ((FreeGroup.of 0) ^ 3 * (FreeGroup.of 1) ^ (-3 : ℤ) * FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹) -
  q ((FreeGroup.of 0) ^ 3 * (FreeGroup.of 1) ^ (-2 : ℤ) * FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹) -
  q ((FreeGroup.of 0) ^ 3 * (FreeGroup.of 1) ^ (-1 : ℤ) * FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹)

/-- The separation test: the quotient determinant is not a unit. -/
def foxDeterminantNonUnitClaim : Prop :=
  ¬ IsUnit foxDeterminantQuotient

/-- The orbit test: the quotient determinant is a unit. -/
def foxDeterminantUnitClaim : Prop :=
  IsUnit foxDeterminantQuotient


/-- The generator assignment `a ↦ 1`, `t ↦ -1` for the sign character. -/
def signGenerators : Fin 2 → ℤˣ :=
  fun i => if i = 0 then 1 else -1

/-- The sign assignment respects the BS(2,3) relator. -/
theorem signGenerators_relator :
    ∀ r ∈ bs23Rels, FreeGroup.lift signGenerators r = 1 := by
  intro r hr
  simp only [bs23Rels, Set.mem_singleton_iff] at hr
  subst r
  simp [signGenerators, bs23Relator, FreeGroup.lift_apply_of]

/-- The sign character `a ↦ 1`, `t ↦ -1` on BS(2,3). -/
noncomputable def signChar : BS23 →* ℤˣ :=
  PresentedGroup.toGroup signGenerators_relator

@[simp] theorem signChar_bs23Map (w : Word 2) :
    signChar (bs23Map w) = FreeGroup.lift signGenerators w := by
  unfold signChar bs23Map PresentedGroup.toGroup PresentedGroup.mk
  change (QuotientGroup.lift (Subgroup.normalClosure bs23Rels)
      (FreeGroup.lift signGenerators) _) (QuotientGroup.mk w) =
    (FreeGroup.lift signGenerators) w
  rw [QuotientGroup.lift_mk]

/-- The ring hom from the group ring to `ℤ` induced by the sign character. -/
noncomputable def signEval : MonoidAlgebra ℤ BS23 →+* ℤ :=
  (MonoidAlgebra.lift ℤ ℤ BS23 ((Units.coeHom ℤ).comp signChar)).toRingHom

@[simp] theorem signEval_q (w : Word 2) :
    signEval (q w) = (signChar (bs23Map w) : ℤ) := by
  simp [signEval, q, MonoidAlgebra.lift_single]

/-- The sign character evaluates the quotient determinant to `3`. -/
theorem foxDeterminant_eval : signEval foxDeterminantQuotient = 3 := by
  simp [foxDeterminantQuotient, signEval_q, signChar_bs23Map, signGenerators,
    FreeGroup.lift_apply_of]
  decide

/-- The unit claim is false because a ring hom sends a unit to a unit, while
the sign evaluation is `3`, which is not a unit in the integers. -/
theorem foxDeterminantUnitClaim_false : ¬ foxDeterminantUnitClaim := by
  intro h
  have hunit : IsUnit (signEval foxDeterminantQuotient) := h.map signEval
  rw [foxDeterminant_eval] at hunit
  rw [Int.isUnit_iff_abs_eq] at hunit
  norm_num at hunit

/-- The quotient determinant is not a unit; the non-unit claim is the route
closure for the Fox determinant route. -/
theorem foxDeterminantNonUnitClaim_true : foxDeterminantNonUnitClaim :=
  foxDeterminantUnitClaim_false

end BS23Fox
end AC

#check @AC.BS23Fox.foxDeterminantQuotient
#check @AC.BS23Fox.foxDeterminantNonUnitClaim
#check @AC.BS23Fox.foxDeterminantUnitClaim
#check @AC.BS23Fox.foxDeterminantUnitClaim_false
#check @AC.BS23Fox.foxDeterminantNonUnitClaim_true
