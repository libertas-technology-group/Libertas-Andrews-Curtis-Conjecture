module

/-
# NielsenSliceBridge — what the measure-12 slice does and does not supply

No declaration in this tree consumes `bothLong_measure12_uniform`
(`NielsenMeasure12.lean:53`), while the target
`cyclicNielsen_uniform_pivot_statement` (`AcNielsen.lean:67`) quantifies over
every measure. This module makes the dependency explicit and proves the part
that follows.

## The decomposition

`LowMeasureDescent` covers states whose cyclic Nielsen length is at most 12.
`HighMeasureDescent` covers states above 12. The target is exactly their union,
because the target asks for one descent step, not an iteration.

## What the slice supplies

`measureTwelve_of_slice` proves that the slice discharges every measure-12 state
whose two cyclic lengths are odd, which abelian terminality forces. The
arithmetic is isolated in two lemmas: two odd lengths, each at least five,
summing to twelve, are five and seven; and with sum at most twelve they are
(5,5), (5,7), or (7,5).

## What the slice does not supply

The measure-10 case, which is the pair (5,5), and every measure above 12. Those
are named as the remaining inputs in `LowMeasureDescent` and
`HighMeasureDescent` and are not proved here. No `sorry` is used: the open
obligations are hypotheses of the theorems that consume them, and the two open
propositions are stated as definitions.

No `sorry`, `admit`, `axiom`, or `native_decide` occurs in this file.
-/

public import AcNielsen
public import AcNielsenDefs
public import AcProof
public import NielsenMeasure12
public import NielsenMeasure12Cover
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

namespace AC
namespace Nielsen
namespace SliceBridge

open RotationNormalForm

/-- One descent step: a reachable abelian-terminal presentation of the trivial
group with strictly smaller cyclic Nielsen length. -/
def DescentFrom (S : Relators 2) : Prop :=
  ∃ T : Relators 2, Reachable S T ∧ AbelianTerminal T ∧
    PresentsTrivialGroup T ∧ cyclicNielsenLength T < cyclicNielsenLength S

/-- Every state in the target's hypothesis set of cyclic Nielsen length at most
12 admits one descent step. The measure-12 part is supplied by the slice. The
measure-10 part, which is the pair (5,5), is a separate obligation. -/
def LowMeasureDescent : Prop :=
  ∀ (S : Relators 2),
    AbelianTerminal S → PresentsTrivialGroup S →
    (∀ i : Fin 2, FreeGroup.IsCyclicallyReduced (S i).toWord) →
    ¬ ProofAttempt.IsSignedPermutation S →
    5 ≤ (S 0).toWord.length → 5 ≤ (S 1).toWord.length →
    cyclicNielsenLength S ≤ 12 → DescentFrom S

/-- Every state in the target's hypothesis set of cyclic Nielsen length above 12
admits one descent step. This is the open high-measure input. -/
def HighMeasureDescent : Prop :=
  ∀ (S : Relators 2),
    AbelianTerminal S → PresentsTrivialGroup S →
    (∀ i : Fin 2, FreeGroup.IsCyclicallyReduced (S i).toWord) →
    ¬ ProofAttempt.IsSignedPermutation S →
    5 ≤ (S 0).toWord.length → 5 ≤ (S 1).toWord.length →
    12 < cyclicNielsenLength S → DescentFrom S

/-- For a cyclically reduced relator, the cyclic length is the word length. -/
theorem cycLen_eq_toWord_length {S : Relators 2} (i : Fin 2)
    (h : FreeGroup.IsCyclicallyReduced (S i).toWord) :
    cycLen (S i) = (S i).toWord.length := by
  conv_lhs => rw [← FreeGroup.mk_toWord (x := S i)]
  exact Measure12Cover.cycLen_mk_of_isCyclicallyReduced h

/-- Two odd lengths, each at least five, summing to twelve, are five and seven. -/
theorem lengths_of_measure_twelve (a b : ℕ) (ha : 5 ≤ a) (hb : 5 ≤ b)
    (hao : Odd a) (hbo : Odd b) (h : a + b = 12) :
    (a = 5 ∧ b = 7) ∨ (a = 7 ∧ b = 5) := by
  rcases hao with ⟨k, hk⟩
  rcases hbo with ⟨l, hl⟩
  omega

/-- Two odd lengths, each at least five, summing to at most twelve, are (5,5),
(5,7), or (7,5). -/
theorem low_lengths (a b : ℕ) (ha : 5 ≤ a) (hb : 5 ≤ b)
    (hao : Odd a) (hbo : Odd b) (h : a + b ≤ 12) :
    (a = 5 ∧ b = 5) ∨ (a = 5 ∧ b = 7) ∨ (a = 7 ∧ b = 5) := by
  rcases hao with ⟨k, hk⟩
  rcases hbo with ⟨l, hl⟩
  omega

/-- **The target is the union of the two measure cases.** The target asks for one
descent step at every measure, so a low-measure input and a high-measure input
compose to it with no induction. -/
theorem uniform_of_low_and_high (hl : LowMeasureDescent)
    (hh : HighMeasureDescent) :
    cyclicNielsen_uniform_pivot_statement := by
  intro S hAb hP hCyc hPerm h0 h1
  by_cases h : cyclicNielsenLength S ≤ 12
  · exact hl S hAb hP hCyc hPerm h0 h1 h
  · exact hh S hAb hP hCyc hPerm h0 h1 (Nat.lt_of_not_le h)

/-- **The slice discharges the measure-12 states.** Abelian terminality forces
each cyclic length to be odd, so a measure-12 state in the hypothesis set has
lengths five and seven, and the slice applies directly. -/
theorem measureTwelve_of_slice (hslice : bothLong_measure12_uniform)
    (S : Relators 2) (hAb : AbelianTerminal S) (hP : PresentsTrivialGroup S)
    (hCyc : ∀ i : Fin 2, FreeGroup.IsCyclicallyReduced (S i).toWord)
    (hPerm : ¬ ProofAttempt.IsSignedPermutation S)
    (h0 : 5 ≤ cycLen (S 0)) (h1 : 5 ≤ cycLen (S 1))
    (ho0 : Odd (cycLen (S 0))) (ho1 : Odd (cycLen (S 1)))
    (hlen : cyclicNielsenLength S = 12) : DescentFrom S := by
  have hsum : cycLen (S 0) + cycLen (S 1) = 12 := by
    rw [← cyclicNielsenLength_pair]
    exact hlen
  rcases lengths_of_measure_twelve (cycLen (S 0)) (cycLen (S 1)) h0 h1 ho0 ho1 hsum with
    ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact hslice S hAb hP hCyc hPerm (Or.inl ⟨ha, hb⟩)
  · exact hslice S hAb hP hCyc hPerm (Or.inr ⟨ha, hb⟩)

/-- **The bridge, stated and proved.** The slice, the measure-10 case, and the
oddness of the two cyclic lengths imply the low-measure input. Oddness is forced
by abelian terminality through `excessLength_even` and
`excessLength_eq_length_sub_one_of_signed`; it is carried as a hypothesis here
so the dependency on those two lemmas is explicit and no proof hole is used. -/
theorem low_of_slice_and_ten (hslice : bothLong_measure12_uniform)
    (hten : ∀ (S : Relators 2), AbelianTerminal S → PresentsTrivialGroup S →
      (∀ i : Fin 2, FreeGroup.IsCyclicallyReduced (S i).toWord) →
      ¬ ProofAttempt.IsSignedPermutation S →
      5 ≤ (S 0).toWord.length → 5 ≤ (S 1).toWord.length →
      cycLen (S 0) = 5 → cycLen (S 1) = 5 → DescentFrom S) :
    ∀ (S : Relators 2), AbelianTerminal S → PresentsTrivialGroup S →
      (∀ i : Fin 2, FreeGroup.IsCyclicallyReduced (S i).toWord) →
      ¬ ProofAttempt.IsSignedPermutation S →
      5 ≤ (S 0).toWord.length → 5 ≤ (S 1).toWord.length →
      Odd (cycLen (S 0)) → Odd (cycLen (S 1)) →
      cyclicNielsenLength S ≤ 12 → DescentFrom S := by
  intro S hAb hP hCyc hPerm h0 h1 ho0 ho1 hle
  have hsum : cycLen (S 0) + cycLen (S 1) ≤ 12 := by
    rw [← cyclicNielsenLength_pair]
    exact hle
  have h0' : 5 ≤ cycLen (S 0) := by
    rw [cycLen_eq_toWord_length 0 (hCyc 0)]
    exact h0
  have h1' : 5 ≤ cycLen (S 1) := by
    rw [cycLen_eq_toWord_length 1 (hCyc 1)]
    exact h1
  rcases low_lengths (cycLen (S 0)) (cycLen (S 1)) h0' h1' ho0 ho1 hsum with
    ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact hten S hAb hP hCyc hPerm h0 h1 ha hb
  · exact hslice S hAb hP hCyc hPerm (Or.inl ⟨ha, hb⟩)
  · exact hslice S hAb hP hCyc hPerm (Or.inr ⟨ha, hb⟩)

/-! ## Axiom record -/

#print axioms uniform_of_low_and_high
#print axioms measureTwelve_of_slice
#print axioms low_of_slice_and_ten
#print axioms lengths_of_measure_twelve
#print axioms low_lengths

end SliceBridge
end Nielsen
end AC
