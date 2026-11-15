module

public import AcStableTrivial

@[expose] public section

/-!
# AcStableProjectionCounterexample — the rank-two stable projection inverse

This module states the exact negation of the rank-two trivial-projection
statement. It declares no theorem, because the inverse is open.

The forward statement is `AC.StableTrivial.trivialProjection_rank_two_statement`
in `AcStableTrivial.lean:309-311`. The inverse is its negation.
-/

set_option autoImplicit false

/-- The exact negation of the rank-two trivial-projection statement: some
rank-two trivial presentation stably reaches the standard tuple at rank two and
does not ordinarily reach it. It denies the rank-two projection, not the
Andrews–Curtis conjecture itself. -/
def trivialProjection_rank_two_counterexample_statement : Prop :=
  ¬ AC.StableTrivial.trivialProjection_rank_two_statement
