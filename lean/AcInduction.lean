module

public import AC
public import AcInvariant
public import AcProof
public import AcEuclid

@[expose] public section

/-!
# Induction through the abelian terminal set

This module states the induction step that the proof attempt leaves open at
`AcProof.lean:74-76`. The step has two inputs, and both are hypotheses of the
theorems below.

`h7` says that every trivial presentation at positive rank reaches an
abelian-terminal state. `h8` says that every abelian-terminal state which
presents the trivial group reaches a signed permutation. The theorem
`hterm_of_abelianTerminal` composes the two and yields the terminal-reachability
statement `hterm` consumed by `AC.ProofAttempt.conjecture_iff_terminal`
(`AcProof.lean:368-377`).

At rank two `h7` is a theorem, not a hypothesis. Gap G1
(`AC.Invariant.expSpan_eq_top_of_presents`, `AcInvariant.lean:243`) makes the
exponent span the whole lattice, and
`AC.Euclid.abelianTerminal_reachable_of_expSpan_top` (`AcEuclid.lean:338`)
performs the Euclidean reduction. The rank-two theorem
`conjecture_rankTwo_of_abelianTerminal` therefore assumes only the rank-two form
of `h8`.

The terminal predicate below has the same body as `AC.Euclid.IsAbelianTerminal`
(`AcEuclid.lean:44`) at rank two and as `AC.BranchA.IsAbelianTerminal`
(`BranchA.lean:89`) at general rank. `BranchA` is outside the build globs of
`lakefile.toml`, so the predicate is declared here. At rank two the two
definitions are definitionally equal, which `isAbelianTerminal_two_iff` records.

No declaration in this file uses a placeholder, a user axiom, or a compiler
option.
-/

namespace AC
namespace Induction

/-- The abelian terminal set at rank `n`: the relators have signed
standard-basis exponent vectors, and the induced generator map is a bijection.
This is the rank-`n` form of `AC.Euclid.IsAbelianTerminal` (`AcEuclid.lean:44`).
The relators themselves may be arbitrary words with those exponent vectors. -/
def IsAbelianTerminal {n : ℕ} (R : Relators n) : Prop :=
  ∃ σ : Fin n → Fin n, Function.Bijective σ ∧ ∃ ε : Fin n → Bool,
    ∀ i : Fin n,
      Invariant.expVec (R i) = if ε i then Invariant.genVec (σ i) else -Invariant.genVec (σ i)

/-- At rank two the general predicate is the predicate used by `AcEuclid`. -/
theorem isAbelianTerminal_two_iff (R : Relators 2) :
    IsAbelianTerminal R ↔ Euclid.IsAbelianTerminal R :=
  Iff.rfl

/-- Rank-two discharge of `h7`. G1 gives a full exponent span for a trivial
presentation, and the Euclidean reduction of `AcEuclid` reaches an
abelian-terminal state from it. -/
theorem isAbelianTerminal_reachable_of_expSpan_top (R : Relators 2)
    (h : Invariant.expSpan R = ⊤) :
    ∃ S : Relators 2, IsAbelianTerminal S ∧ Reachable R S := by
  obtain ⟨S, hS, hRS⟩ := Euclid.abelianTerminal_reachable_of_expSpan_top R h
  exact ⟨S, (isAbelianTerminal_two_iff S).mpr hS, hRS⟩

/-- The induction step. `h7` supplies an abelian-terminal state reachable from
every trivial presentation, `h8` carries that state to a signed permutation, and
the two paths compose. The statement produced is exactly the `hterm` hypothesis
of `AC.ProofAttempt.conjecture_of_terminal_and_canonical` (`AcProof.lean:74-76`). -/
theorem hterm_of_abelianTerminal
    (h7 : ∀ (n : ℕ), 0 < n → ∀ R : Relators n, PresentsTrivialGroup R →
      ∃ S : Relators n, IsAbelianTerminal S ∧ Reachable R S)
    (h8 : ∀ (n : ℕ), 0 < n → ∀ S : Relators n, PresentsTrivialGroup S →
      IsAbelianTerminal S →
      ∃ T : Relators n, ProofAttempt.IsSignedPermutation T ∧ Reachable S T) :
    ∀ (n : ℕ), 0 < n → ∀ R : Relators n, PresentsTrivialGroup R →
      ∃ T : Relators n, ProofAttempt.IsSignedPermutation T ∧ Reachable R T := by
  intro n hn R hR
  obtain ⟨S, hS, hRS⟩ := h7 n hn R hR
  have hPS : PresentsTrivialGroup S := (ProofAttempt.presents_of_reachable hRS).mp hR
  obtain ⟨T, hT, hST⟩ := h8 n hn S hPS hS
  exact ⟨T, hT, Relation.ReflTransGen.trans hRS hST⟩

/-- `AC.Conjecture` follows from the two induction inputs. The forward direction
of `AC.ProofAttempt.conjecture_iff_terminal` supplies the terminal statement,
and the reverse direction consumes it with gap G3 closed
(`AcProof.lean:337-338`). -/
theorem conjecture_of_abelianTerminal
    (h7 : ∀ (n : ℕ), 0 < n → ∀ R : Relators n, PresentsTrivialGroup R →
      ∃ S : Relators n, IsAbelianTerminal S ∧ Reachable R S)
    (h8 : ∀ (n : ℕ), 0 < n → ∀ S : Relators n, PresentsTrivialGroup S →
      IsAbelianTerminal S →
      ∃ T : Relators n, ProofAttempt.IsSignedPermutation T ∧ Reachable S T) :
    Conjecture :=
  ProofAttempt.conjecture_iff_terminal.mpr (hterm_of_abelianTerminal h7 h8)

/-- Rank-two induction step with `h7` discharged. The only hypothesis is the
rank-two form of `h8`. -/
theorem hterm_rankTwo_of_abelianTerminal
    (h8 : ∀ S : Relators 2, PresentsTrivialGroup S → IsAbelianTerminal S →
      ∃ T : Relators 2, ProofAttempt.IsSignedPermutation T ∧ Reachable S T) :
    ∀ R : Relators 2, PresentsTrivialGroup R →
      ∃ T : Relators 2, ProofAttempt.IsSignedPermutation T ∧ Reachable R T := by
  intro R hR
  have hspan : Invariant.expSpan R = ⊤ := Invariant.expSpan_eq_top_of_presents hR
  obtain ⟨S, hS, hRS⟩ := isAbelianTerminal_reachable_of_expSpan_top R hspan
  have hPS : PresentsTrivialGroup S := (ProofAttempt.presents_of_reachable hRS).mp hR
  obtain ⟨T, hT, hST⟩ := h8 S hPS hS
  exact ⟨T, hT, Relation.ReflTransGen.trans hRS hST⟩

/-- The rank-two instance of `AC.Conjecture`, with `h7` discharged by G1 and the
Euclidean reduction and with gap G3 closing the signed permutation to the
ordered standard tuple. The only hypothesis is the rank-two form of `h8`. -/
theorem conjecture_rankTwo_of_abelianTerminal
    (h8 : ∀ S : Relators 2, PresentsTrivialGroup S → IsAbelianTerminal S →
      ∃ T : Relators 2, ProofAttempt.IsSignedPermutation T ∧ Reachable S T) :
    ∀ R : Relators 2, PresentsTrivialGroup R → Reachable R (standard 2) := by
  intro R hR
  obtain ⟨T, hT, hRT⟩ := hterm_rankTwo_of_abelianTerminal h8 R hR
  exact Relation.ReflTransGen.trans hRT
    (ProofAttempt.signedPermutation_reachable_standard 2 T hT)

end Induction
end AC
