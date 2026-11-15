module

public import AC

@[expose] public section

/-!
# The counterexample target for the Andrews–Curtis conjecture

This module is the counterexample entry point of the corpus. It imports `AC`, so the
targets `AC.IsCounterexample`, `AC.Counterexample`, and
`AC.not_conjecture_iff_counterexample` are in scope for a reader of this module.

`AC.IsCounterexample R` asks for a balanced presentation of the trivial group together
with the proposition that no finite sequence of official moves carries `R` to the
standard tuple. `AC.Counterexample` existentially quantifies that pair at positive
finite rank, and `AC.not_conjecture_iff_counterexample` states that it is equivalent to
the negation of `AC.Conjecture` under classical logic.

This module states the target and proves nothing about it. The separation results that
bear on the target live in `AcInvariant` and `AcProof`.
-/

namespace AC
namespace CounterexampleTarget

/-- The counterexample target at a fixed rank, restated for a reader of this module. -/
abbrev Target (n : ℕ) (R : Relators n) : Prop := IsCounterexample R

/-- The existential counterexample target, restated for a reader of this module. -/
abbrev Exists : Prop := Counterexample

end CounterexampleTarget
end AC
