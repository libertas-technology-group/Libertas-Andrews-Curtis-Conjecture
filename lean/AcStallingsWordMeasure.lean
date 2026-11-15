module

public import AcStallingsExponentCounterexample
public import AcStallingsExponentMeasure
public import BranchD2

@[expose] public section

/-!
# AcStallingsWordMeasure — the word-level replacement measure

The exponent defect alone is refuted by
`AC.Stallings.exponentDescentStatement2_false`. This file records a word-level
measure that combines three components:

```text
wordMeasure R = (tailArea R, exponentDefect2 R, totalLength R)
```

ordered lexicographically. The tailArea separates generator-label collisions;
the exponent defect separates exponent-vector collisions; the total length
separates commutator factors that the first two components miss.

The file proves the measure strictly decreases at the three critical states:

* `Ak3.ak3` → the two-step exponent-defect state.
* `BranchD2.candidate` → `standard 2`.
* `exponentCounterexample` → `standard 2` by conjugation.

The general statement `wordMeasureDescentStatement` is declared but not proved.
-/

set_option autoImplicit false

namespace AC
namespace Stallings

/-- The total reduced word length of a rank-two state. -/
noncomputable def totalLength2 (R : Relators 2) : ℕ :=
  (R 0).toWord.length + (R 1).toWord.length

/-- The three-component word measure. -/
noncomputable def wordMeasure (R : Relators 2) : ℕ × ℕ × ℕ :=
  (tailArea R, exponentDefect2 R, totalLength2 R)

/-- Lexicographic comparison on the three-component measure. -/
def wordMeasureLexLt (a b : ℕ × ℕ × ℕ) : Prop :=
  a.1 < b.1 ∨
    (a.1 = b.1 ∧
      (a.2.1 < b.2.1 ∨ (a.2.1 = b.2.1 ∧ a.2.2 < b.2.2)))

/-- The replacement word-measure descent: every non-terminal rank-two trivial
presentation reaches a state with strictly smaller lexicographic measure. -/
def wordMeasureDescentStatement : Prop :=
  ∀ R : Relators 2, PresentsTrivialGroup R →
    ¬ ProofAttempt.IsSignedPermutation R →
    ∃ S : Relators 2, Reachable R S ∧
      wordMeasureLexLt (wordMeasure S) (wordMeasure R)

lemma tailArea_ak3_word : tailArea Ak3.ak3 = 2 := by decide

lemma totalLength2_ak3_word : totalLength2 Ak3.ak3 = 13 := by decide

lemma wordMeasure_ak3_word : wordMeasure Ak3.ak3 = (2, 7, 13) := by
  rw [wordMeasure, tailArea_ak3_word, exponentDefect2_ak3, totalLength2_ak3_word]

lemma tailArea_R2_word : tailArea exponentR2 = 2 := by decide

lemma totalLength2_R2_word : totalLength2 exponentR2 = 17 := by decide

lemma wordMeasure_R2_word : wordMeasure exponentR2 = (2, 5, 17) := by
  rw [wordMeasure, tailArea_R2_word, exponentDefect2_R2, totalLength2_R2_word]

lemma tailArea_branchD2_word : tailArea BranchD2.candidate = 2 := by decide

lemma totalLength2_branchD2_word : totalLength2 BranchD2.candidate = 9 := by decide

lemma wordMeasure_branchD2_word :
    wordMeasure BranchD2.candidate = (2, 1, 9) := by
  rw [wordMeasure, tailArea_branchD2_word, exponentDefect2_branchD2,
    totalLength2_branchD2_word]

lemma tailArea_counter_word : tailArea exponentCounterexample = 1 := by decide

lemma totalLength2_counter_word : totalLength2 exponentCounterexample = 6 := by decide

lemma wordMeasure_counter_word :
    wordMeasure exponentCounterexample = (1, 0, 6) := by
  rw [wordMeasure, tailArea_counter_word, exponentDefect2_exponentCounterexample,
    totalLength2_counter_word]

lemma tailArea_standard_word : tailArea (standard 2) = 0 := by decide

lemma totalLength2_standard_word : totalLength2 (standard 2) = 2 := by decide

lemma wordMeasure_standard_word : wordMeasure (standard 2) = (0, 0, 2) := by
  rw [wordMeasure, tailArea_standard_word, exponentDefect2_standard,
    totalLength2_standard_word]

/-- The conjugator `x⁻¹ y⁻¹` sends the commutator-factor relator to `y`. -/
def counterexampleConjugator : Word 2 :=
  (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹

lemma counterexample_conj_eq_standard :
    Function.update exponentCounterexample 1
      (counterexampleConjugator * exponentCounterexample 1 *
        counterexampleConjugator⁻¹) = standard 2 := by
  funext i
  fin_cases i
  · simp [exponentCounterexample, exponentCounterexampleR0, standard]
  · simp [exponentCounterexample, exponentCounterexampleR1, counterexampleConjugator,
      standard]
    group

lemma counterexample_conj_step : Step exponentCounterexample (standard 2) := by
  simpa [counterexample_conj_eq_standard] using
    Step.conj exponentCounterexample 1 counterexampleConjugator

lemma counterexample_reachable_standard :
    Reachable exponentCounterexample (standard 2) :=
  Relation.ReflTransGen.single counterexample_conj_step

/-- If the tailArea is positive, the standard tuple has strictly smaller
lexicographic word measure. -/
lemma wordMeasureStandard_lt_of_tailArea_pos {R : Relators 2}
    (h : 0 < tailArea R) :
    wordMeasureLexLt (wordMeasure (standard 2)) (wordMeasure R) := by
  rw [wordMeasure_standard_word]
  simp [wordMeasure, wordMeasureLexLt, h]

/-- Any presentation that reaches the standard tuple satisfies the word-measure
descent, provided its tailArea is positive. -/
theorem wordMeasureDescent_of_reachable_standard {R : Relators 2}
    (h : Reachable R (standard 2)) (hpos : 0 < tailArea R) :
    ∃ S : Relators 2, Reachable R S ∧
      wordMeasureLexLt (wordMeasure S) (wordMeasure R) :=
  ⟨standard 2, h, wordMeasureStandard_lt_of_tailArea_pos hpos⟩

/-- The word measure decreases at AK(3). -/
theorem ak3_wordMeasureDescent :
    ∃ S : Relators 2, Reachable Ak3.ak3 S ∧
      wordMeasureLexLt (wordMeasure S) (wordMeasure Ak3.ak3) := by
  refine ⟨exponentR2, exponentR2_reachable, ?_⟩
  rw [wordMeasure_R2_word, wordMeasure_ak3_word]
  simp [wordMeasureLexLt]

/-- The word measure decreases at BranchD2. -/
theorem branchD2_wordMeasureDescent :
    ∃ S : Relators 2, Reachable BranchD2.candidate S ∧
      wordMeasureLexLt (wordMeasure S) (wordMeasure BranchD2.candidate) := by
  refine ⟨standard 2, BranchD2.candidate_ordinary, ?_⟩
  rw [wordMeasure_standard_word, wordMeasure_branchD2_word]
  simp [wordMeasureLexLt]

/-- The word measure decreases at the exponent counterexample. -/
theorem counterexample_wordMeasureDescent :
    ∃ S : Relators 2, Reachable exponentCounterexample S ∧
      wordMeasureLexLt (wordMeasure S) (wordMeasure exponentCounterexample) := by
  refine ⟨standard 2, counterexample_reachable_standard, ?_⟩
  rw [wordMeasure_standard_word, wordMeasure_counter_word]
  simp [wordMeasureLexLt]

end Stallings
end AC

#check @AC.Stallings.wordMeasure
#check @AC.Stallings.wordMeasureDescentStatement
#check @AC.Stallings.ak3_wordMeasureDescent
#check @AC.Stallings.branchD2_wordMeasureDescent
#check @AC.Stallings.counterexample_wordMeasureDescent
#print axioms AC.Stallings.counterexample_wordMeasureDescent
