import AcNielsen

/-!
# AcNielsenCounterexample — the Nielsen inverse statement

This module states the exact negation of the cyclic Nielsen uniform-pivot
statement. It declares no theorem, because the negation is open.

The forward statement is `AC.Nielsen.cyclicNielsen_uniform_pivot_statement` in
`AcNielsen.lean`. The inverse is its classical negation.
-/

set_option autoImplicit false

namespace AC
namespace Nielsen

/-- The exact negation of the cyclic Nielsen uniform-pivot statement. It is a
route-level falsification: it denies the universal both-long descent, not the
Andrews–Curtis conjecture itself. -/
def not_cyclicNielsen_uniform_pivot_statement : Prop :=
  ¬ cyclicNielsen_uniform_pivot_statement

end Nielsen
end AC
