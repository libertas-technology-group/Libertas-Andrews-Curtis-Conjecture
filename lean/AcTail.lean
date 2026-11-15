module

public import AcTailDefs

@[expose] public section

/-!
# AcTail — the Magnus multiplier-core descent statement

This module carries the descent statement of the multiplier core as a
proposition-valued definition. It declares no theorem, because the proposition
is open: the session source records the proof as unfinished.

The proposition is the right-hand side of
`tailDescent_iff_multiplierCorePlus_descent` in the session source
`AcTail.lean:2641-2643`.
-/

set_option autoImplicit false

namespace AC
namespace Tail

open AC.Euclid

/-- A state in the residual multiplier core admits a finite AC sequence to an
abelian terminal state whose total tail is strictly smaller. -/
def multiplierCorePlus_descent_statement : Prop :=
  ∀ S : Relators 2, MultiplierCorePlus S →
    ∃ T : Relators 2, Reachable S T ∧ IsAbelianTerminal T ∧
      totalTail T < totalTail S

end Tail
end AC
