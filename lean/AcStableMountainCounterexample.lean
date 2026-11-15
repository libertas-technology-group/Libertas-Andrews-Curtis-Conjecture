module

public import AcStableMountain

@[expose] public section

/-!
# AcStableMountainCounterexample — the stable mountain normal-form inverse

This module states the exact negation of the stable mountain normal-form
statement. It declares no theorem, because the inverse is open.

The forward statement is
`AC.StableMountain.stableReachable_mountain_normalForm_statement` in
`AcStableMountain.lean:71`. The inverse is its negation. It denies the mountain
normal form for stable paths, not the Andrews–Curtis conjecture itself.
-/

set_option autoImplicit false

/-- The exact negation of the stable mountain normal-form statement: some
stable-reachable pair of presentations has no one-peak stable path between its
endpoints. It denies the mountain normal form, not the Andrews–Curtis
conjecture itself. -/
def stableReachable_mountain_normalForm_counterexample_statement : Prop :=
  ¬ AC.StableMountain.stableReachable_mountain_normalForm_statement
