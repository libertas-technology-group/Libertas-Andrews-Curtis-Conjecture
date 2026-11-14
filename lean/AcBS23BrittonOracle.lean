import Ak3OrbitSeparation

/-!
# AcBS23BrittonOracle — the Britton conjugacy target

The seven-step finite-quotient path requires the conjugacy `t⁻¹ ~ r2` in
BS(2,3). This file states the conjugacy and its negation as the two outcomes the
complete Britton oracle must decide. It does not claim either outcome.
-/

set_option autoImplicit false

namespace AC
namespace BS23Britton

open Ak3OrbitSeparation

/-- The BS(2,3) relator is trivial in the presented group. -/
theorem bs23_relator_eq_one : bs23Map bs23Relator = 1 := by
  exact PresentedGroup.one_of_mem (Set.mem_singleton bs23Relator)

/-- Conjugacy in BS(2,3). -/
def Conjugate (x y : BS23) : Prop :=
  ∃ g : BS23, g * x * g⁻¹ = y

/-- The image of the stable generator. -/
noncomputable def tImage : BS23 :=
  bs23Map (FreeGroup.of 1)

/-- The image of the second AK(3) relator. -/
noncomputable def r2Image : BS23 :=
  bs23Map (Ak3.ak3 1)

/-- The separation outcome: `t⁻¹` is not conjugate to `r2`. -/
def brittonConjugacyClaim : Prop :=
  ¬ Conjugate tImage⁻¹ r2Image

/-- The orbit outcome: `t⁻¹` is conjugate to `r2`. -/
def brittonConjugacyCounterClaim : Prop :=
  Conjugate tImage⁻¹ r2Image

end BS23Britton
end AC

#check @AC.BS23Britton.bs23_relator_eq_one
#check @AC.BS23Britton.Conjugate
#check @AC.BS23Britton.tImage
#check @AC.BS23Britton.r2Image
#check @AC.BS23Britton.brittonConjugacyClaim
#check @AC.BS23Britton.brittonConjugacyCounterClaim
