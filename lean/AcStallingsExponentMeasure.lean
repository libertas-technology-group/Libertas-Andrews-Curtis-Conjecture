module

public import AcStallingsTailAreaCounterexample
public import AcInvariant
public import BranchD2

@[expose] public section

/-!
# AcStallingsExponentMeasure — a replacement measure for the Stallings route

The structural `tailArea` is refuted at `Ak3.ak3` by
`AC.Stallings.tailAreaDescentCounterexample`. This file records a replacement
for the rank-two Stallings test: the L1 exponent defect

```text
exponentDefect2 R =
  |expVec (R 0) 0| + |expVec (R 0) 1| +
  |expVec (R 1) 0| + |expVec (R 1) 1| - 2.
```

A signed permutation has defect zero. `Ak3.ak3` has defect 7. The two-step path
`ak3 → invert the second relator → multiply the first by the inverse` reaches a
state of defect 5. The file proves the concrete AK(3) decrease and states the
general rank-two descent as an open proposition. It does not claim the general
descent.
-/

set_option autoImplicit false

namespace AC
namespace Stallings

/-- The rank-two L1 exponent defect, normalized so a signed permutation has
defect zero. -/
noncomputable def exponentDefect2 (R : Relators 2) : ℕ :=
  (Invariant.expVec (R 0) 0).natAbs + (Invariant.expVec (R 0) 1).natAbs +
  (Invariant.expVec (R 1) 0).natAbs + (Invariant.expVec (R 1) 1).natAbs - 2

/-- The replacement descent statement: every non-terminal rank-two trivial
presentation reaches a state of strictly smaller exponent defect. -/
def exponentDescentStatement2 : Prop :=
  ∀ R : Relators 2, PresentsTrivialGroup R →
    ¬ ProofAttempt.IsSignedPermutation R →
    ∃ S : Relators 2, Reachable R S ∧ exponentDefect2 S < exponentDefect2 R

lemma expVec_ak3_0 : Invariant.expVec (Ak3.ak3 0) = ![(3 : ℤ), -4] := by decide

lemma expVec_ak3_1 : Invariant.expVec (Ak3.ak3 1) = ![(1 : ℤ), -1] := by decide

lemma exponentDefect2_ak3 : exponentDefect2 Ak3.ak3 = 7 := by
  simp [exponentDefect2, expVec_ak3_0, expVec_ak3_1]

lemma exponentDefect2_standard : exponentDefect2 (standard 2) = 0 := by
  simp [exponentDefect2, standard, Invariant.expVec, Invariant.expHom,
    FreeGroup.lift_apply_of, Invariant.genVec]

/-- Invert the second AK(3) relator. -/
def exponentR1 : Relators 2 :=
  Function.update Ak3.ak3 1 (Ak3.ak3 1)⁻¹

/-- Multiply the first relator by the inverse of the second. -/
def exponentR2 : Relators 2 :=
  Function.update exponentR1 0 (exponentR1 0 * exponentR1 1)

lemma exponentR1_step : Step Ak3.ak3 exponentR1 := by
  simpa [exponentR1] using Step.inv Ak3.ak3 1

lemma exponentR2_step : Step exponentR1 exponentR2 := by
  simpa [exponentR2] using Step.mulRight exponentR1 0 1 (by decide)

lemma exponentR2_reachable : Reachable Ak3.ak3 exponentR2 :=
  (Relation.ReflTransGen.single exponentR1_step).tail exponentR2_step

lemma exponentDefect2_R1 : exponentDefect2 exponentR1 = 7 := by
  simp [exponentDefect2, exponentR1, expVec_ak3_0, expVec_ak3_1,
    Invariant.expVec_inv]

lemma exponentDefect2_R2 : exponentDefect2 exponentR2 = 5 := by
  simp [exponentDefect2, exponentR2, exponentR1, expVec_ak3_0, expVec_ak3_1,
    Invariant.expVec_inv, Invariant.expVec_mul]

/-- The replacement measure strictly decreases on the AK(3) counterexample. -/
theorem ak3_exponentDescent :
    ∃ S : Relators 2, Reachable Ak3.ak3 S ∧
      exponentDefect2 S < exponentDefect2 Ak3.ak3 :=
  ⟨exponentR2, exponentR2_reachable, by
    rw [exponentDefect2_R2, exponentDefect2_ak3]
    decide⟩

/-- Any presentation that reaches the standard tuple satisfies the replacement
descent, because the standard tuple has defect zero. -/
theorem exponentDescent_of_reachable_standard {R : Relators 2}
    (h : Reachable R (standard 2)) (hne : exponentDefect2 R ≠ 0) :
    ∃ S : Relators 2, Reachable R S ∧ exponentDefect2 S < exponentDefect2 R := by
  refine ⟨standard 2, h, ?_⟩
  rw [exponentDefect2_standard]
  exact Nat.pos_of_ne_zero hne

lemma expVec_branchD2_0 :
    Invariant.expVec (BranchD2.candidate 0) = ![(-1 : ℤ), -1] := by decide

lemma expVec_branchD2_1 :
    Invariant.expVec (BranchD2.candidate 1) = ![(-1 : ℤ), 0] := by decide

lemma exponentDefect2_branchD2 : exponentDefect2 BranchD2.candidate = 1 := by
  simp [exponentDefect2, expVec_branchD2_0, expVec_branchD2_1]

/-- The replacement measure strictly decreases on the BranchD2 candidate. -/
theorem branchD2_candidate_exponentDescent :
    ∃ S : Relators 2, Reachable BranchD2.candidate S ∧
      exponentDefect2 S < exponentDefect2 BranchD2.candidate :=
  exponentDescent_of_reachable_standard BranchD2.candidate_ordinary (by
    rw [exponentDefect2_branchD2]
    decide)

end Stallings
end AC

#check @AC.Stallings.exponentDefect2
#check @AC.Stallings.exponentDescentStatement2
#check @AC.Stallings.ak3_exponentDescent
#print axioms AC.Stallings.ak3_exponentDescent
