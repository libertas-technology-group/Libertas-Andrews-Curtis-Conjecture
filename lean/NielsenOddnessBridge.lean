module

/-
# NielsenOddnessBridge — the low-measure input with oddness discharged

`NielsenSliceBridge.low_of_slice_and_ten` concludes the low-measure descent only
under two oddness hypotheses on the cyclic lengths. `NielsenOddness` proves those
hypotheses from abelian terminality. This module joins the two and produces
`LowMeasureDescent` from exactly two inputs: the measure-12 slice and the
measure-10 case.

The join is a separate module because `NielsenOddness` imports
`NielsenSliceBridge`, so importing it back would create a cycle. This module
imports both and is imported by neither.

No `sorry`, `admit`, `axiom`, or `native_decide` occurs in this file.
-/

public import NielsenSliceBridge
public import NielsenOddness
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

namespace AC
namespace Nielsen
namespace OddnessBridge

open SliceBridge

/-- **The low-measure input, with oddness discharged.** The measure-12 slice and
the measure-10 case together imply `LowMeasureDescent`, because abelian
terminality forces both cyclic lengths to be odd and `NielsenOddness` proves it.
-/
theorem low_measure_descent_of_slice_and_ten
    (hslice : bothLong_measure12_uniform)
    (hten : ∀ (S : Relators 2), AbelianTerminal S → PresentsTrivialGroup S →
      (∀ i : Fin 2, FreeGroup.IsCyclicallyReduced (S i).toWord) →
      ¬ ProofAttempt.IsSignedPermutation S →
      5 ≤ (S 0).toWord.length → 5 ≤ (S 1).toWord.length →
      cycLen (S 0) = 5 → cycLen (S 1) = 5 → DescentFrom S) :
    LowMeasureDescent := by
  intro S hAb hP hCyc hPerm h0 h1 hle
  exact low_of_slice_and_ten hslice hten S hAb hP hCyc hPerm h0 h1
    (odd_cycLen_of_abelianTerminal S hAb hCyc 0)
    (odd_cycLen_of_abelianTerminal S hAb hCyc 1) hle

/-- **The target from three named inputs.** The slice, the measure-10 case, and
the high-measure descent imply `cyclicNielsen_uniform_pivot_statement`. -/
theorem uniform_of_slice_ten_high
    (hslice : bothLong_measure12_uniform)
    (hten : ∀ (S : Relators 2), AbelianTerminal S → PresentsTrivialGroup S →
      (∀ i : Fin 2, FreeGroup.IsCyclicallyReduced (S i).toWord) →
      ¬ ProofAttempt.IsSignedPermutation S →
      5 ≤ (S 0).toWord.length → 5 ≤ (S 1).toWord.length →
      cycLen (S 0) = 5 → cycLen (S 1) = 5 → DescentFrom S)
    (hhigh : HighMeasureDescent) :
    cyclicNielsen_uniform_pivot_statement :=
  uniform_of_low_and_high
    (low_measure_descent_of_slice_and_ten hslice hten) hhigh

/-! ## Axiom record -/

#print axioms low_measure_descent_of_slice_and_ten
#print axioms uniform_of_slice_ten_high

end OddnessBridge
end Nielsen
end AC
