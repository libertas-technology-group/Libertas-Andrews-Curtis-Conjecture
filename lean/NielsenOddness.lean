/-
# NielsenOddness — odd cyclic length at an abelian-terminal state

At an abelian-terminal rank-two state each related exponent vector is a signed
standard basis vector. The parity of the word length is then forced: the sum of
the two exponent components is odd, so the cyclically reduced length is odd.
This discharges the oddness hypotheses of
`AC.Nielsen.SliceBridge.low_of_slice_and_ten`.
-/

import AcNielsenDefs
import AcProof
import AcA8TailMinimal
import NielsenSliceBridge
import Mathlib.Tactic

set_option autoImplicit false

namespace AC
namespace Nielsen

open Invariant

/-- At an abelian-terminal state, every cyclically reduced relator has odd
cyclic length. -/
theorem odd_cycLen_of_abelianTerminal (S : Relators 2) (hAb : AbelianTerminal S)
    (hCyc : ∀ i : Fin 2, FreeGroup.IsCyclicallyReduced (S i).toWord) (i : Fin 2) :
    Odd (cycLen (S i)) := by
  obtain ⟨σ, hσ, ε, hε⟩ := hAb
  have hAb' : A8TailMinimal.IsAbelianTerminal S := ⟨σ, hσ, ε, hε⟩
  have heven : Even (A8TailMinimal.excessLength (S i)) :=
    A8TailMinimal.excessLength_even S hAb' i
  have hex : A8TailMinimal.excessLength (S i) = (S i).toWord.length - 1 :=
    A8TailMinimal.excessLength_eq_length_sub_one_of_signed (S i) (σ i) (ε i) (hε i)
  have hcyc : cycLen (S i) = (S i).toWord.length :=
    SliceBridge.cycLen_eq_toWord_length i (hCyc i)
  have hpos : 1 ≤ (S i).toWord.length := by
    have hparity := A8TailMinimal.expVec_sum_zmod_eq_length (S i)
    rw [hε i] at hparity
    have hleft :
        ((if ε i then genVec (σ i) else -genVec (σ i)) 0 : ZMod 2) +
          ((if ε i then genVec (σ i) else -genVec (σ i)) 1 : ZMod 2) = 1 := by
      simpa using A8TailMinimal.signed_zmod_sum_eq_one (σ i) (ε i)
    rw [hleft] at hparity
    have hodd : Odd (S i).toWord.length :=
      ZMod.natCast_eq_one_iff_odd.mp hparity.symm
    rcases hodd with ⟨j, hj⟩
    omega
  rw [hcyc, Nat.odd_iff]
  rw [hex] at heven
  rcases heven with ⟨k, hk⟩
  omega

#print axioms odd_cycLen_of_abelianTerminal

end Nielsen
end AC
