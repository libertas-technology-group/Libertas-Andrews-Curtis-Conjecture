module

public import AcStallings
public import AcTailDefs
public import AcTailGeneral
public import AcTailClass
public import AcProof

@[expose] public section

/-!
# AcStallingsTailArea — a candidate state-level tail area

This file supplies the object named but not defined in `AcStallings.lean:50-53`:
a state-level measure `tailArea : Relators n → ℕ` and the separation/descent
statements the Stallings route needs. The rank-two refinement reuses the
compiled commutator tail `AC.Tail.totalTail`. The rank-n measure is a structural
candidate; the session body named in `AcStallings.lean:51` is UNKNOWN in this
tree. No descent proof is claimed.
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace AC
namespace Stallings

/-- The number of relator positions whose reduced word is not one letter long. -/
noncomputable def lengthOneDefect {n : ℕ} (R : Relators n) : ℕ :=
  n - (Finset.univ.filter (fun i : Fin n => (R i).toWord.length = 1)).card

/-- The number of generator labels missing from the distinct reduced letter
lists of the relators. -/
noncomputable def generatorImageDefect {n : ℕ} (R : Relators n) : ℕ :=
  n - (Finset.univ.image
    (fun i : Fin n => (R i).toWord.map (fun p : Fin n × Bool => p.1))).card

/-- Candidate rank-`n` tail area. It is zero exactly when every relator is a
one-letter word and the label map is bijective, i.e. exactly on
`ProofAttempt.IsSignedPermutation`. -/
noncomputable def tailArea {n : ℕ} (R : Relators n) : ℕ :=
  lengthOneDefect R + generatorImageDefect R

/-- Rank-two refinement: add the compiled commutator tail. This is the only
place the existing `AC.Tail.totalTail` is reused. -/
noncomputable def tailAreaWithTail (R : Relators 2) : ℕ :=
  AC.Tail.totalTail R + tailArea R

/-- The separation statement: the candidate is zero exactly on the terminal set. -/
def tailArea_separates_signedPermutation_statement : Prop :=
  ∀ {n : ℕ} (R : Relators n),
    tailArea R = 0 ↔ ProofAttempt.IsSignedPermutation R

/-- The descent statement the route needs, with the trivial-presentation
restriction that the unrestricted form at `AcStallings.lean:53` lacks. -/
def tailArea_descent_statement : Prop :=
  ∀ {n : ℕ} (R : Relators n), PresentsTrivialGroup R →
    ¬ ProofAttempt.IsSignedPermutation R →
    ∃ S : Relators n, Step R S ∧ tailArea S < tailArea R

/-- The same descent for the rank-two refinement. -/
def tailAreaWithTail_descent_statement : Prop :=
  ∀ R : Relators 2, PresentsTrivialGroup R →
    ¬ ProofAttempt.IsSignedPermutation R →
    ∃ S : Relators 2, Step R S ∧ tailAreaWithTail S < tailAreaWithTail R

end Stallings
end AC

#check @AC.Stallings.tailArea
#check @AC.Stallings.tailAreaWithTail
#check @AC.Stallings.tailArea_separates_signedPermutation_statement
#check @AC.Stallings.tailArea_descent_statement
#check @AC.Stallings.tailAreaWithTail_descent_statement

example (R : AC.Relators 2) :
    AC.Stallings.tailAreaWithTail R =
      AC.Tail.totalTail R + AC.Stallings.tailArea R := rfl
