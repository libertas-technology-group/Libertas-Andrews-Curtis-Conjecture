/-
# NielsenLowMeasureFinal — the target reduced to two named inputs

Everything below the measure-12 slice is now proved in the kernel:

* the parity gap, in `NielsenOddness`;
* the join, in `NielsenOddnessBridge`;
* the measure-10 case, in `NielsenMeasure10Certificates` and
  `NielsenMeasure10Consumer`.

So `cyclicNielsen_uniform_pivot_statement` follows from exactly two inputs:

1. `bothLong_measure12_uniform`, the measure-12 slice, which the literature
   settles at total length 12 and which this corpus has enumerated at 40 ordered
   states;
2. `HighMeasureDescent`, every state above measure 12.

This module states that reduction as one theorem. It is the narrowest form of
the remaining obligation the corpus has reached.

No `sorry`, `admit`, `axiom`, or `native_decide` occurs in this file.
-/

import NielsenOddnessBridge
import NielsenMeasure10Consumer
import Mathlib.Tactic

set_option autoImplicit false

namespace AC
namespace Nielsen
namespace LowMeasureFinal

open SliceBridge

/-- **The target from two inputs.** The measure-12 slice and the high-measure
descent imply `cyclicNielsen_uniform_pivot_statement`. The parity gap and the
measure-10 case are discharged inside `NielsenOddnessBridge` and
`NielsenMeasure10Consumer`. -/
theorem uniform_of_slice_and_high
    (hslice : bothLong_measure12_uniform)
    (hhigh : HighMeasureDescent) :
    cyclicNielsen_uniform_pivot_statement :=
  OddnessBridge.uniform_of_slice_ten_high hslice Measure10Consumer.measure10_input hhigh

/-- The low-measure input on its own, from the slice alone. -/
theorem low_measure_descent_of_slice
    (hslice : bothLong_measure12_uniform) :
    LowMeasureDescent :=
  OddnessBridge.low_measure_descent_of_slice_and_ten hslice Measure10Consumer.measure10_input

/-! ## Axiom record -/

#print axioms uniform_of_slice_and_high
#print axioms low_measure_descent_of_slice

end LowMeasureFinal
end Nielsen
end AC
