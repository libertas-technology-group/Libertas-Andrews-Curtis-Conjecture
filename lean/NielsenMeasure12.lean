import AcNielsenDefs
import AcProof

/-!
# NielsenMeasure12 — the measure-12 both-long uniform slice

This module states the universal lengths-5,7 slice of the cyclic Nielsen route.
The slice is the measure-12 part of the both-long case: two cyclically reduced
relators of cyclic lengths 5 and 7, in either order, on two generators.

The row `bothLong_measure12_uniform` names the measure-12 slice. Its literal
formula is not recorded in this repository, so the statement below encodes the
slice read against `docs/proof_track.rst`: the Nielsen route closes measures 6,
8, and 10, and the remaining case has both relators of length at least five above
measure 10.

## Dependency status

The measure-ten input is proved at `NielsenMeasure10Consumer.lean:340`
(`measure10_input`), and the 5,7 base witness descent is proved at
`NielsenSevenStage.lean:430` (`sevenStageWitnessDescent`). The base proposition
`RotationNormalForm.SevenStageWitnessDescent` at
`NielsenRotationNormalForm.lean:418` is therefore inhabited in this tree.

One dependency keeps this row a statement. The transport is witness-relative: it
concludes a descent for the coordinate rotations `witnessRotate a b` of the fixed
pair `(r7Shape, s5Shape)` (`NielsenRotationNormalForm.lean:304-305`,
`:428-434`). The statement below quantifies over every rank-two state whose two
cyclic lengths are 5 and 7, and no lemma in this tree carries an arbitrary such
state to a rotation of the witness. The row therefore remains a `def` over the
universal class, and its slice form is closed only conditionally from
`measure12_covers_witness` at `NielsenMeasure12Cover.lean:263`.
-/

set_option autoImplicit false

namespace AC
namespace Nielsen

/-- The universal lengths-5,7 slice at measure 12: every rank-two
abelian-terminal presentation of the trivial group whose two relators are
cyclically reduced, are not a signed permutation, and have cyclic Nielsen
lengths 5 and 7 in either order admits a finite AC sequence to an
abelian-terminal presentation of the trivial group whose cyclic Nielsen length
is strictly smaller. -/
def bothLong_measure12_uniform : Prop :=
  ∀ (S : Relators 2),
    AbelianTerminal S → PresentsTrivialGroup S →
    (∀ i : Fin 2, FreeGroup.IsCyclicallyReduced (S i).toWord) →
    ¬ ProofAttempt.IsSignedPermutation S →
    ((cycLen (S 0) = 5 ∧ cycLen (S 1) = 7) ∨
      (cycLen (S 0) = 7 ∧ cycLen (S 1) = 5)) →
    ∃ T : Relators 2, Reachable S T ∧ AbelianTerminal T ∧
      PresentsTrivialGroup T ∧
      cyclicNielsenLength T < cyclicNielsenLength S

end Nielsen
end AC
