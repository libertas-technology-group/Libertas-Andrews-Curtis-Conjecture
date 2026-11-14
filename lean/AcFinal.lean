import AcInduction
import AcEuclidGeneral

/-!
# Final assembly from A8

`AcEuclidGeneral.abelianTerminal_reachable_of_expSpan_top_general` proves the
general A7 input of the A10 assembly. This module composes that theorem with the
remaining A8 input and yields the terminal-reachability statement and
`AC.Conjecture`.

The only open mathematical input after this file is A8: every abelian-terminal
trivial presentation reaches a signed permutation.
-/

namespace AC
namespace Final

open Induction

/-- The terminal-reachability statement from A8 alone. A7 is discharged by
`AcEuclidGeneral`. -/
theorem hterm_of_A8
    (h8 : ∀ (n : ℕ), 0 < n → ∀ S : Relators n, PresentsTrivialGroup S →
      IsAbelianTerminal S →
      ∃ T : Relators n, ProofAttempt.IsSignedPermutation T ∧ Reachable S T) :
    ∀ (n : ℕ), 0 < n → ∀ R : Relators n, PresentsTrivialGroup R →
      ∃ T : Relators n, ProofAttempt.IsSignedPermutation T ∧ Reachable R T := by
  intro n hn R hR
  obtain ⟨S, hS, hRS⟩ :=
    EuclidGeneral.abelianTerminal_reachable_of_expSpan_top_general n hn R
      (Invariant.expSpan_eq_top_of_presents hR)
  have hPS : PresentsTrivialGroup S := (ProofAttempt.presents_of_reachable hRS).mp hR
  obtain ⟨T, hT, hST⟩ := h8 n hn S hPS hS
  exact ⟨T, hT, Relation.ReflTransGen.trans hRS hST⟩

/-- `AC.Conjecture` follows from A8 alone, because A7-general is proved. -/
theorem conjecture_of_A8
    (h8 : ∀ (n : ℕ), 0 < n → ∀ S : Relators n, PresentsTrivialGroup S →
      IsAbelianTerminal S →
      ∃ T : Relators n, ProofAttempt.IsSignedPermutation T ∧ Reachable S T) :
    Conjecture :=
  (ProofAttempt.conjecture_iff_terminal).mpr (hterm_of_A8 h8)

/-- The conjecture implies A8: the standard tuple is a signed permutation. -/
theorem A8_of_conjecture (h : Conjecture) :
    ∀ (n : ℕ), 0 < n → ∀ S : Relators n, PresentsTrivialGroup S →
      IsAbelianTerminal S →
      ∃ T : Relators n, ProofAttempt.IsSignedPermutation T ∧ Reachable S T := by
  intro n hn S hS _
  exact ⟨standard n, ProofAttempt.standard_isSignedPermutation, h n hn S hS⟩

/-- With A7-general proved, A8 is exactly the Andrews–Curtis conjecture. -/
theorem conjecture_iff_A8 :
    Conjecture ↔
      (∀ (n : ℕ), 0 < n → ∀ S : Relators n, PresentsTrivialGroup S →
        IsAbelianTerminal S →
        ∃ T : Relators n, ProofAttempt.IsSignedPermutation T ∧ Reachable S T) :=
  ⟨A8_of_conjecture, conjecture_of_A8⟩

end Final
end AC
