import AC
import Mathlib.Tactic.Group

/-!
# The right power family at rank two: `(x, y * x ^ n)`

For every natural `n`, the rank-two tuple `Q n` whose first relator is the
generator `x` and whose second relator is `y * x ^ n` is Andrews–Curtis
reachable to the standard tuple `(x, y)`.

The step `Q (n + 1) -> Q n` is a three-move list: invert relator `0`, so the
first relator becomes `x⁻¹`; right-multiply relator `1` by relator `0`, so the
second relator becomes `(y * x ^ (n + 1)) * x⁻¹ = y * x ^ n`; invert relator `0`
back, restoring `x`. The induction on `n` composes the step, and `Q 0` is the
standard tuple, so the family closes at every exponent.

## Move count

Each application of `step_succ` concatenates three moves, so the route for `Q n`
has `3 * n` moves; `routeLength_eq` records the arithmetic. Holding a single
inversion of relator `0` across all `n` multiplications instead gives the shorter
route of `n + 2` moves, and the two totals differ at the junction inversions,
which cancel pairwise.

The tuple is ordered, and the moves act on relator positions, so the family is a
statement about the ambient free group and not about the presented quotient.
-/

namespace AC
namespace RightFamily

/-- The rank-two tuple with first relator `x` and second relator `y * x ^ n`. -/
def Q (n : ℕ) : Relators 2 :=
  Function.update (standard 2) 1 ((FreeGroup.of 1) * (FreeGroup.of 0) ^ n)

/-- (a) At exponent zero the tuple is the standard tuple. -/
theorem Q_zero : Q 0 = standard 2 := by
  dsimp [Q, standard]
  rw [pow_zero, mul_one]
  exact Function.update_eq_self 1 FreeGroup.of

/-- The first relator of `Q n` is the generator `x`, for every exponent. -/
@[simp] theorem Q_apply_zero (n : ℕ) : Q n 0 = FreeGroup.of 0 := by
  dsimp [Q]
  rw [Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
  rfl

/-- The second relator of `Q n` is `y * x ^ n`, for every exponent. -/
@[simp] theorem Q_apply_one (n : ℕ) : Q n 1 = FreeGroup.of 1 * FreeGroup.of 0 ^ n := by
  dsimp [Q]
  rw [Function.update_self]

/-- (b) One step of the descent: three moves carry `Q (n + 1)` to `Q n`. The
middle move adds `x⁻¹` to the second relator, and `x ^ (n + 1) * x⁻¹ = x ^ n`. -/
theorem step_succ (n : ℕ) : Reachable (Q (n + 1)) (Q n) := by
  classical
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  let S1 : Relators 2 := Function.update (Q (n + 1)) 0 ((Q (n + 1)) 0)⁻¹
  have h1 : Step (Q (n + 1)) S1 := by simpa [S1] using Step.inv (Q (n + 1)) 0
  have hS1_0 : S1 0 = (FreeGroup.of 0)⁻¹ := by
    dsimp [S1]
    rw [Function.update_self, Q_apply_zero]
  have hS1_1 : S1 1 = FreeGroup.of 1 * FreeGroup.of 0 ^ (n + 1) := by
    dsimp [S1]
    rw [Function.update_of_ne h10, Q_apply_one]
  let S2 : Relators 2 := Function.update S1 1 (S1 1 * S1 0)
  have h2 : Step S1 S2 := Step.mulRight S1 1 0 h10
  have hS2_0 : S2 0 = (FreeGroup.of 0)⁻¹ := by
    dsimp [S2]
    rw [Function.update_of_ne h01, hS1_0]
  have hS2_1 : S2 1 = FreeGroup.of 1 * FreeGroup.of 0 ^ n := by
    dsimp [S2]
    rw [Function.update_self, hS1_1, hS1_0, pow_succ]
    group
  let S3 : Relators 2 := Function.update S2 0 (S2 0)⁻¹
  have h3 : Step S2 S3 := by simpa [S3] using Step.inv S2 0
  have hS3 : S3 = Q n := by
    funext k
    by_cases hk : k = 0
    · subst hk
      dsimp [S3]
      rw [Function.update_self, hS2_0, Q_apply_zero]
      simp
    · have hk1 : k = 1 := Fin.eq_one_of_ne_zero k hk
      subst hk1
      dsimp [S3]
      rw [Function.update_of_ne h10, hS2_1, Q_apply_one]
  rw [hS3] at h3
  exact Relation.ReflTransGen.head h1
    (Relation.ReflTransGen.head h2 (Relation.ReflTransGen.head h3 Relation.ReflTransGen.refl))

/-- (c) Every member of the family reaches the standard tuple. -/
theorem reachable_Q (n : ℕ) : Reachable (Q n) (standard 2) := by
  induction n with
  | zero =>
      rw [Q_zero]
      exact Relation.ReflTransGen.refl
  | succ k ih =>
      exact (step_succ k).trans ih

/-- The number of moves that `n` applications of `step_succ` concatenate. -/
def routeLength : ℕ → ℕ
  | 0 => 0
  | k + 1 => routeLength k + 3

/-- (d) The route for `Q n` is three moves per exponent step, so `3 * n` moves. -/
theorem routeLength_eq (n : ℕ) : routeLength n = 3 * n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show routeLength k + 3 = 3 * (k + 1)
      rw [ih, Nat.mul_succ]

end RightFamily
end AC
