import AcStallingsTailArea

/-!
# AcStallingsInverse — the inverse ascent statement for the tail area

The Stallings descent asks for a step that lowers `tailArea`. The inverse form
asks for a predecessor that raises it. This file records the inverse statement
as a proposition-valued definition. It does not claim a proof and it does not
assert that the inverse holds.
-/

set_option autoImplicit false

namespace AC
namespace Stallings

/-- The inverse ascent statement: every non-terminal trivial presentation has a
predecessor with strictly larger tail area. -/
def StallingsInverseStatement : Prop :=
  ∀ {n : ℕ} (R : Relators n), PresentsTrivialGroup R →
    ¬ ProofAttempt.IsSignedPermutation R →
    ∃ S : Relators n, Step S R ∧ tailArea R < tailArea S

end Stallings
end AC

#check @AC.Stallings.StallingsInverseStatement
