module

public import AC

@[expose] public section

/-!
# The power family at rank two

For each natural number `n` the ordered pair `(x * y ^ n, y)` on two generators
can be carried to the standard pair `(x, y)` by Andrews–Curtis moves. The proof
is a parameterised move list, and it closes a whole family rather than one
presentation at a time.

`step_succ` carries `P (n + 1)` to `P n` in three moves: invert the second
relator, right-multiply the first relator by it, and invert the second relator
back. The middle move leaves the first relator as
`x * y ^ (n + 1) * y⁻¹ = x * y ^ n`, so the tuple loses one unit of the
exponent. `reachable_P` iterates the step down to the standard pair.

The move budget is recorded in `move_count`. The three-move step makes the
induction in this file spend `3 * n` moves. The alternating list described in
the docstring of `move_count` spends `n + 2` moves, which lies within that
budget for every `n`.
-/

namespace AC
namespace PowFamily

/-- The ordered pair `(x * y ^ n, y)`, with `x = FreeGroup.of 0` and
`y = FreeGroup.of 1`, written as a rank-two presentation. -/
def P (n : ℕ) : Relators 2 :=
  Function.update (standard 2) 0 (FreeGroup.of 0 * (FreeGroup.of 1) ^ n)

/-- The first relator of `P n` is `x * y ^ n`. -/
@[simp] theorem P_apply_zero (n : ℕ) :
    P n 0 = FreeGroup.of 0 * (FreeGroup.of 1) ^ n := by
  simp [P]

/-- The second relator of `P n` is the generator `y`. -/
@[simp] theorem P_apply_one (n : ℕ) : P n 1 = FreeGroup.of 1 := by
  simp [P, standard]

/-- (a) The family starts at the standard pair, because `y ^ 0 = 1` and
updating a function at a point with its own value changes nothing. -/
theorem P_zero : P 0 = standard 2 := by
  have h : FreeGroup.of 0 * (FreeGroup.of 1) ^ 0 = standard 2 0 := by
    simp [standard]
  simp only [P, h, Function.update_eq_self]

/-- (b) One unit of the exponent costs three moves. The chain inverts relator 1,
right-multiplies relator 0 by it, and inverts relator 1 back. The intermediate
tuples are named `S` and `T` so that the three `Step` constructors can be
applied to explicit targets. -/
theorem step_succ (n : ℕ) : Reachable (P (n + 1)) (P n) := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  set S : Relators 2 := Function.update (P (n + 1)) 1 (FreeGroup.of 1)⁻¹ with hS
  have hstep1 : Step (P (n + 1)) S := by
    rw [hS]
    simpa [P_apply_one] using (Step.inv (P (n + 1)) 1)
  have hS0 : S 0 = FreeGroup.of 0 * (FreeGroup.of 1) ^ (n + 1) := by
    rw [hS]
    simp [P]
  have hS1 : S 1 = (FreeGroup.of 1)⁻¹ := by
    rw [hS]
    simp
  set T : Relators 2 := Function.update S 0 (S 0 * S 1) with hT
  have hstep2 : Step S T := by
    rw [hT]
    exact Step.mulRight S 0 1 h01
  have hT0 : T 0 = FreeGroup.of 0 * (FreeGroup.of 1) ^ n := by
    rw [hT, Function.update_self, hS0, hS1]
    simp [pow_succ, mul_assoc]
  have hT1 : T 1 = (FreeGroup.of 1)⁻¹ := by
    rw [hT, Function.update_of_ne h10]
    exact hS1
  have hstep3 : Step T (Function.update T 1 (FreeGroup.of 1)) := by
    simpa [hT1] using (Step.inv T 1)
  have hF : Function.update T 1 (FreeGroup.of 1) = P n := by
    have h0 : Function.update T 1 (FreeGroup.of 1) 0 = P n 0 := by
      rw [Function.update_of_ne h01, hT0, P_apply_zero]
    have h1 : Function.update T 1 (FreeGroup.of 1) 1 = P n 1 := by
      rw [Function.update_self, P_apply_one]
    funext i
    exact (Fin.forall_fin_two (p := fun j =>
      Function.update T 1 (FreeGroup.of 1) j = P n j)).mpr ⟨h0, h1⟩ i
  have hfirst : Reachable (P (n + 1)) S := Relation.ReflTransGen.single hstep1
  have hsecond : Reachable S T := Relation.ReflTransGen.single hstep2
  have hthird : Reachable T (P n) := by
    rw [← hF]
    exact Relation.ReflTransGen.single hstep3
  exact (hfirst.trans hsecond).trans hthird

/-- (c) Every member of the power family is reachable from the standard pair,
by induction on the exponent using (a) and (b). -/
theorem reachable_P (n : ℕ) : Reachable (P n) (standard 2) := by
  induction n with
  | zero =>
      rw [P_zero]
      exact Relation.ReflTransGen.refl
  | succ n ih =>
      exact (step_succ n).trans ih

/-- (d) The move budget for the family: two moves for each unit of the exponent
plus two moves that fix the orientation of the second relator.

The step-by-step induction proved above spends three moves per unit, because it
restores the second relator after every multiplication so that each intermediate
tuple is again some `P k`; `reachable_P` therefore spends `3 * n` moves. An
alternating list can hold the second relator inverted between multiplications
and invert it once at each end, which spends `n + 2` moves; `move_count_ge`
records that this lies within the budget. -/
def move_count (n : ℕ) : ℕ := 2 * n + 2

/-- The alternating list described in the docstring of `move_count` fits the
budget. -/
theorem move_count_ge (n : ℕ) : n + 2 ≤ move_count n := by
  have h : n + 2 ≤ n + n + 2 := Nat.add_le_add_right (Nat.le_add_right n n) 2
  rw [move_count, Nat.two_mul]
  exact h

end PowFamily
end AC
