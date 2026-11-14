/-
# NielsenPivotP1 — the measure-14 pivot reaches the classical P1 witness

The Andrews–Curtis corpus records `P1` as the pair
`(x⁻¹ y² x y⁻³, y⁻¹ x² y x⁻³)`, the initial presentation of
`cert_sym_equiv_orphan1.json`. This module carries the measure-14 pivot state
`PivotObstruction.pivotState` to that pair by a literal chain of official
moves, so the corpus's open case is kernel-linked to the literature benchmark.

## The chain

`cert_from_pivot.json` is a replay-verified 45-move transcript that carries the
pivot to `P1` with the two relators read in the order `(V, U)`. A relator
permutation is not an elementary `Step`, so the chain opens with a six-step
exchange of the two relators, taken from the standard transvection
decomposition of the swap matrix. The transcript then records move for move.

A multiplication by an inverse relator is three official steps — invert the
multiplier, multiply, invert it back — so the 45 transcript moves become 61
`Step` constructors, and the whole chain has 67.

## The transcription

Every state is a `Relators 2` tuple of `FreeGroup.mk` images of reduced
letter lists. Each move's word equation is discharged by rewriting with
`FreeGroup.mul_mk` and `FreeGroup.inv_mk`, then deciding the resulting
equality of two `FreeGroup.reduce` images. The reduction is computable on
letter lists, so the check is a kernel computation with no tactic that
certifies an unproved goal.

No `sorry`, `admit`, `axiom`, or `native_decide` occurs in this file.
-/

import AcNielsen
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace AC
namespace Nielsen
namespace P1Bridge

open PivotObstruction

/-! ## 1. The target state `P1` -/

/-- `P1`, the initial presentation of `cert_sym_equiv_orphan1.json`: the pair
`(x⁻¹ y² x y⁻³, y⁻¹ x² y x⁻³)`. -/
def p1State : Relators 2 :=
  ![FreeGroup.mk [(0, false), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false)], FreeGroup.mk [(1, false), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false)]]

/-! ## 2. Word equality by kernel reduction

Two `FreeGroup.mk` images are equal when their maximal reductions agree, and
the reduction of a concrete letter list is a computation. -/

theorem mk_eq_mk_of_reduce {L₁ L₂ : List (Fin 2 × Bool)}
    (h : FreeGroup.reduce L₁ = FreeGroup.reduce L₂) :
    FreeGroup.mk L₁ = FreeGroup.mk L₂ :=
  FreeGroup.reduce.exact h

/-! ## 3. One official move, stated for a two-relator tuple -/

theorem step_inv0 {a b a' : Word 2} (h : a' = a⁻¹) : Step ![a, b] ![a', b] := by
  have hs : Step ![a, b] (Function.update ![a, b] 0 (![a, b] 0)⁻¹) :=
    Step.inv ![a, b] 0
  have he : Function.update ![a, b] 0 (![a, b] 0)⁻¹ = ![a', b] := by
    funext i
    fin_cases i <;> simp [h]
  rwa [he] at hs

theorem step_inv1 {a b b' : Word 2} (h : b' = b⁻¹) : Step ![a, b] ![a, b'] := by
  have hs : Step ![a, b] (Function.update ![a, b] 1 (![a, b] 1)⁻¹) :=
    Step.inv ![a, b] 1
  have he : Function.update ![a, b] 1 (![a, b] 1)⁻¹ = ![a, b'] := by
    funext i
    fin_cases i <;> simp [h]
  rwa [he] at hs

theorem step_mul01 {a b a' : Word 2} (h : a' = a * b) : Step ![a, b] ![a', b] := by
  have hs : Step ![a, b] (Function.update ![a, b] 0 (![a, b] 0 * ![a, b] 1)) :=
    Step.mulRight ![a, b] 0 1 (by decide)
  have he : Function.update ![a, b] 0 (![a, b] 0 * ![a, b] 1) = ![a', b] := by
    funext i
    fin_cases i <;> simp [h]
  rwa [he] at hs

theorem step_mul10 {a b b' : Word 2} (h : b' = b * a) : Step ![a, b] ![a, b'] := by
  have hs : Step ![a, b] (Function.update ![a, b] 1 (![a, b] 1 * ![a, b] 0)) :=
    Step.mulRight ![a, b] 1 0 (by decide)
  have he : Function.update ![a, b] 1 (![a, b] 1 * ![a, b] 0) = ![a, b'] := by
    funext i
    fin_cases i <;> simp [h]
  rwa [he] at hs

theorem step_conj0 {a b a' : Word 2} (c : Word 2) (h : a' = c * a * c⁻¹) :
    Step ![a, b] ![a', b] := by
  have hs : Step ![a, b] (Function.update ![a, b] 0 (c * ![a, b] 0 * c⁻¹)) :=
    Step.conj ![a, b] 0 c
  have he : Function.update ![a, b] 0 (c * ![a, b] 0 * c⁻¹) = ![a', b] := by
    funext i
    fin_cases i <;> simp [h]
  rwa [he] at hs

theorem step_conj1 {a b b' : Word 2} (c : Word 2) (h : b' = c * b * c⁻¹) :
    Step ![a, b] ![a, b'] := by
  have hs : Step ![a, b] (Function.update ![a, b] 1 (c * ![a, b] 1 * c⁻¹)) :=
    Step.conj ![a, b] 1 c
  have he : Function.update ![a, b] 1 (c * ![a, b] 1 * c⁻¹) = ![a, b'] := by
    funext i
    fin_cases i <;> simp [h]
  rwa [he] at hs

/-! ## 4. The words, one per distinct relator spelling -/

abbrev u0 : Word 2 := FreeGroup.mk [(0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (1, false)]
abbrev u1 : Word 2 := FreeGroup.mk [(0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false)]
abbrev u2 : Word 2 := FreeGroup.mk [(1, true), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false)]
abbrev u3 : Word 2 := FreeGroup.mk [(0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (0, true), (0, true), (1, false), (0, false), (0, false), (0, false)]
abbrev u4 : Word 2 := FreeGroup.mk [(0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (1, true), (0, true), (1, false), (1, false), (1, false), (0, false)]
abbrev u5 : Word 2 := FreeGroup.mk [(1, true), (1, true), (0, true), (1, false), (1, false), (1, false), (0, false)]
abbrev u6 : Word 2 := FreeGroup.mk [(1, false), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false)]
abbrev u7 : Word 2 := FreeGroup.mk [(0, false), (1, false), (0, true), (0, true), (0, true), (1, true), (0, false)]
abbrev u8 : Word 2 := FreeGroup.mk [(0, true), (1, false), (1, false), (1, false), (0, false), (1, true), (1, true)]
abbrev u9 : Word 2 := FreeGroup.mk [(0, false), (1, false), (0, true), (0, true), (0, true), (1, false), (1, false), (0, false), (1, true), (1, true)]
abbrev u10 : Word 2 := FreeGroup.mk [(0, true), (0, true), (0, true), (1, false), (1, false), (0, false), (1, true), (1, true), (0, false), (1, false)]
abbrev u11 : Word 2 := FreeGroup.mk [(1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false)]
abbrev u12 : Word 2 := FreeGroup.mk [(1, true), (0, true), (1, false), (1, false), (1, false), (0, false), (1, true)]
abbrev u13 : Word 2 := FreeGroup.mk [(0, true), (0, true), (0, true), (1, false), (1, false), (0, false), (1, false), (0, false), (1, true)]
abbrev u14 : Word 2 := FreeGroup.mk [(0, false), (1, false), (0, false), (1, true), (0, true), (0, true), (0, true), (1, false), (1, false)]
abbrev u15 : Word 2 := FreeGroup.mk [(1, true), (0, false), (1, false), (0, false), (1, true), (0, true), (0, true), (0, true), (1, false), (1, false), (1, false)]
abbrev u16 : Word 2 := FreeGroup.mk [(0, true), (1, true), (0, false), (1, false), (0, false), (1, true), (0, true), (0, true), (0, true), (1, false), (1, false), (1, false), (0, false)]
abbrev u17 : Word 2 := FreeGroup.mk [(0, true), (1, true), (0, false), (1, false), (0, false), (1, true), (0, true), (0, true), (1, false), (1, false)]
abbrev u18 : Word 2 := FreeGroup.mk [(1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, true), (0, true), (0, true), (1, false), (1, false), (1, false)]
abbrev u19 : Word 2 := FreeGroup.mk [(0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, true), (0, true), (0, true), (1, false), (1, false), (1, false), (0, false)]
abbrev u20 : Word 2 := FreeGroup.mk [(0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, true), (0, true), (1, false), (1, false)]
abbrev u21 : Word 2 := FreeGroup.mk [(1, true), (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, true), (0, true), (1, false), (1, false), (1, false)]
abbrev u22 : Word 2 := FreeGroup.mk [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, true), (0, true), (1, false), (1, false), (1, false), (0, false)]
abbrev u23 : Word 2 := FreeGroup.mk [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false)]
abbrev u24 : Word 2 := FreeGroup.mk [(0, true), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (0, false)]
abbrev u25 : Word 2 := FreeGroup.mk [(1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (0, false), (1, false)]
abbrev u26 : Word 2 := FreeGroup.mk [(1, true), (0, true), (1, true), (0, true), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false)]
abbrev u27 : Word 2 := FreeGroup.mk [(1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false)]
abbrev u28 : Word 2 := FreeGroup.mk [(0, false), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (0, false), (1, false), (0, false), (1, false)]
abbrev u29 : Word 2 := FreeGroup.mk [(0, false), (1, true), (0, true), (1, false), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false)]
abbrev u30 : Word 2 := FreeGroup.mk [(0, false), (0, false), (1, true), (0, true), (1, false), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false)]
abbrev u31 : Word 2 := FreeGroup.mk [(0, false), (0, false), (1, true), (0, true), (1, false), (1, false), (0, false), (1, false), (0, false)]
abbrev u32 : Word 2 := FreeGroup.mk [(0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, false), (1, false)]
abbrev u33 : Word 2 := FreeGroup.mk [(1, true), (0, false), (0, false), (1, true), (0, true), (1, false), (1, false), (0, false), (1, false), (0, false), (1, false)]
abbrev u34 : Word 2 := FreeGroup.mk [(0, true), (1, true), (0, false), (0, false), (1, true), (0, true), (1, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false)]
abbrev u35 : Word 2 := FreeGroup.mk [(1, false), (0, true), (1, true), (0, false), (0, false), (1, true), (0, true), (1, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, true)]
abbrev u36 : Word 2 := FreeGroup.mk [(0, false), (1, false), (0, true), (1, true), (0, false), (0, false), (1, true), (0, true), (1, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, true)]
abbrev u37 : Word 2 := FreeGroup.mk [(0, false), (1, false), (0, true), (1, true), (0, false), (0, false), (1, true), (0, true), (1, false), (0, false), (1, false)]
abbrev u38 : Word 2 := FreeGroup.mk [(1, true), (0, true), (1, false), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, false), (0, false)]
abbrev u39 : Word 2 := FreeGroup.mk [(0, false), (1, false), (0, true), (0, true), (1, true), (0, false), (0, false)]
abbrev u40 : Word 2 := FreeGroup.mk [(1, false), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, false), (0, false), (1, true), (0, true)]
abbrev u41 : Word 2 := FreeGroup.mk [(1, false), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (1, true), (0, false), (0, false)]
abbrev u42 : Word 2 := FreeGroup.mk [(0, true), (0, true), (1, true), (0, false), (0, false), (0, false), (1, false)]
abbrev u43 : Word 2 := FreeGroup.mk [(0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (1, true), (0, false), (0, false), (1, false)]
abbrev u44 : Word 2 := FreeGroup.mk [(1, true), (0, true), (0, true), (0, true), (1, false), (0, false), (0, false)]
abbrev u45 : Word 2 := FreeGroup.mk [(0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (1, true), (0, true), (1, false), (0, false), (0, false)]
abbrev u46 : Word 2 := FreeGroup.mk [(0, false), (1, false), (0, true), (1, true), (1, true), (0, true), (1, false), (0, false), (0, false), (0, false), (1, false)]
abbrev u47 : Word 2 := FreeGroup.mk [(0, false), (1, false), (0, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, false), (0, false)]
abbrev u48 : Word 2 := FreeGroup.mk [(1, true), (1, true), (0, true), (1, false), (1, false), (0, false), (0, false), (0, false), (1, false), (0, true)]
abbrev u49 : Word 2 := FreeGroup.mk [(0, true), (1, true), (0, false), (0, false), (0, false), (1, false), (0, true)]
abbrev u50 : Word 2 := FreeGroup.mk [(0, false), (1, true), (0, true), (0, true), (0, true), (1, false), (0, false)]
abbrev u51 : Word 2 := FreeGroup.mk [(1, false), (0, true), (0, true), (1, true), (0, false), (0, false), (0, false)]
abbrev u52 : Word 2 := FreeGroup.mk [(0, false), (1, true), (1, true), (0, true), (1, false), (1, false), (1, false)]

/-! ## 5. The states -/

/-- The measure-14 pivot state, in the letter spelling of `pivotU` and `pivotV`. -/
def s0 : Relators 2 :=
  ![FreeGroup.mk [(0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (1, false)], FreeGroup.mk [(0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false)]]

def s1 : Relators 2 := ![u2, u1]
def s2 : Relators 2 := ![u2, u3]
def s3 : Relators 2 := ![u2, u4]
def s4 : Relators 2 := ![u5, u4]
def s5 : Relators 2 := ![u1, u4]
def s6 : Relators 2 := ![u1, u0]
def s7 : Relators 2 := ![u6, u0]
def s8 : Relators 2 := ![u6, u7]
def s9 : Relators 2 := ![u8, u7]
def s10 : Relators 2 := ![u8, u9]
def s11 : Relators 2 := ![u6, u9]
def s12 : Relators 2 := ![u6, u10]
def s13 : Relators 2 := ![u11, u10]
def s14 : Relators 2 := ![u12, u10]
def s15 : Relators 2 := ![u12, u13]
def s16 : Relators 2 := ![u11, u13]
def s17 : Relators 2 := ![u11, u14]
def s18 : Relators 2 := ![u1, u14]
def s19 : Relators 2 := ![u1, u15]
def s20 : Relators 2 := ![u1, u16]
def s21 : Relators 2 := ![u1, u17]
def s22 : Relators 2 := ![u1, u18]
def s23 : Relators 2 := ![u1, u19]
def s24 : Relators 2 := ![u1, u20]
def s25 : Relators 2 := ![u1, u21]
def s26 : Relators 2 := ![u1, u22]
def s27 : Relators 2 := ![u1, u23]
def s28 : Relators 2 := ![u11, u23]
def s29 : Relators 2 := ![u24, u23]
def s30 : Relators 2 := ![u25, u23]
def s31 : Relators 2 := ![u25, u26]
def s32 : Relators 2 := ![u27, u26]
def s33 : Relators 2 := ![u27, u23]
def s34 : Relators 2 := ![u28, u23]
def s35 : Relators 2 := ![u28, u26]
def s36 : Relators 2 := ![u29, u26]
def s37 : Relators 2 := ![u29, u23]
def s38 : Relators 2 := ![u30, u23]
def s39 : Relators 2 := ![u30, u26]
def s40 : Relators 2 := ![u31, u26]
def s41 : Relators 2 := ![u31, u23]
def s42 : Relators 2 := ![u31, u32]
def s43 : Relators 2 := ![u33, u32]
def s44 : Relators 2 := ![u34, u32]
def s45 : Relators 2 := ![u35, u32]
def s46 : Relators 2 := ![u36, u32]
def s47 : Relators 2 := ![u37, u32]
def s48 : Relators 2 := ![u38, u32]
def s49 : Relators 2 := ![u38, u39]
def s50 : Relators 2 := ![u40, u39]
def s51 : Relators 2 := ![u41, u39]
def s52 : Relators 2 := ![u41, u42]
def s53 : Relators 2 := ![u43, u42]
def s54 : Relators 2 := ![u43, u44]
def s55 : Relators 2 := ![u45, u44]
def s56 : Relators 2 := ![u45, u42]
def s57 : Relators 2 := ![u46, u42]
def s58 : Relators 2 := ![u46, u44]
def s59 : Relators 2 := ![u47, u44]
def s60 : Relators 2 := ![u47, u42]
def s61 : Relators 2 := ![u48, u42]
def s62 : Relators 2 := ![u48, u49]
def s63 : Relators 2 := ![u48, u50]
def s64 : Relators 2 := ![u5, u50]
def s65 : Relators 2 := ![u5, u49]
def s66 : Relators 2 := ![u5, u51]
def s67 : Relators 2 := ![u52, u51]

/-! ## 6. The chain -/

theorem reachable_pivot_p1 : Reachable PivotObstruction.pivotState p1State := by
  have hstart : PivotObstruction.pivotState = s0 := rfl
  rw [hstart]
  have h1 : Step s0 s1 :=
    step_inv0 (a := u0) (b := u1) (a' := u2)
      (by rw [FreeGroup.inv_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h2 : Step s1 s2 :=
    step_mul10 (a := u2) (b := u1) (b' := u3)
      (by rw [FreeGroup.mul_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h3 : Step s2 s3 :=
    step_inv1 (a := u2) (b := u3) (b' := u4)
      (by rw [FreeGroup.inv_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h4 : Step s3 s4 :=
    step_mul01 (a := u2) (b := u4) (a' := u5)
      (by rw [FreeGroup.mul_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h5 : Step s4 s5 :=
    step_inv0 (a := u5) (b := u4) (a' := u1)
      (by rw [FreeGroup.inv_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h6 : Step s5 s6 :=
    step_mul10 (a := u1) (b := u4) (b' := u0)
      (by rw [FreeGroup.mul_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h7 : Step s6 s7 :=
    step_conj0 (a := u1) (b := u0) (a' := u6) (FreeGroup.mk [(0, true), (1, false), (1, false), (1, false), (0, false)])
      (by simp only [FreeGroup.mul_mk, FreeGroup.inv_mk];
          exact mk_eq_mk_of_reduce (by decide))
  have h8 : Step s7 s8 :=
    step_conj1 (a := u6) (b := u0) (b' := u7) (FreeGroup.mk [(0, true), (1, false), (0, false), (0, false), (0, false)])
      (by simp only [FreeGroup.mul_mk, FreeGroup.inv_mk];
          exact mk_eq_mk_of_reduce (by decide))
  have h9 : Step s8 s9 :=
    step_inv0 (a := u6) (b := u7) (a' := u8)
      (by rw [FreeGroup.inv_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h10 : Step s9 s10 :=
    step_mul10 (a := u8) (b := u7) (b' := u9)
      (by rw [FreeGroup.mul_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h11 : Step s10 s11 :=
    step_inv0 (a := u8) (b := u9) (a' := u6)
      (by rw [FreeGroup.inv_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h12 : Step s11 s12 :=
    step_conj1 (a := u6) (b := u9) (b' := u10) (FreeGroup.mk [(1, true), (0, true)])
      (by simp only [FreeGroup.mul_mk, FreeGroup.inv_mk];
          exact mk_eq_mk_of_reduce (by decide))
  have h13 : Step s12 s13 :=
    step_conj0 (a := u6) (b := u10) (a' := u11) (FreeGroup.mk [(1, true)])
      (by simp only [FreeGroup.mul_mk, FreeGroup.inv_mk];
          exact mk_eq_mk_of_reduce (by decide))
  have h14 : Step s13 s14 :=
    step_inv0 (a := u11) (b := u10) (a' := u12)
      (by rw [FreeGroup.inv_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h15 : Step s14 s15 :=
    step_mul10 (a := u12) (b := u10) (b' := u13)
      (by rw [FreeGroup.mul_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h16 : Step s15 s16 :=
    step_inv0 (a := u12) (b := u13) (a' := u11)
      (by rw [FreeGroup.inv_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h17 : Step s16 s17 :=
    step_conj1 (a := u11) (b := u13) (b' := u14) (FreeGroup.mk [(1, true), (1, true), (0, false), (0, false), (0, false)])
      (by simp only [FreeGroup.mul_mk, FreeGroup.inv_mk];
          exact mk_eq_mk_of_reduce (by decide))
  have h18 : Step s17 s18 :=
    step_conj0 (a := u11) (b := u14) (a' := u1) (FreeGroup.mk [(1, true)])
      (by simp only [FreeGroup.mul_mk, FreeGroup.inv_mk];
          exact mk_eq_mk_of_reduce (by decide))
  have h19 : Step s18 s19 :=
    step_conj1 (a := u1) (b := u14) (b' := u15) (FreeGroup.mk [(1, true)])
      (by simp only [FreeGroup.mul_mk, FreeGroup.inv_mk];
          exact mk_eq_mk_of_reduce (by decide))
  have h20 : Step s19 s20 :=
    step_conj1 (a := u1) (b := u15) (b' := u16) (FreeGroup.mk [(0, true)])
      (by simp only [FreeGroup.mul_mk, FreeGroup.inv_mk];
          exact mk_eq_mk_of_reduce (by decide))
  have h21 : Step s20 s21 :=
    step_mul10 (a := u1) (b := u16) (b' := u17)
      (by rw [FreeGroup.mul_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h22 : Step s21 s22 :=
    step_conj1 (a := u1) (b := u17) (b' := u18) (FreeGroup.mk [(1, true)])
      (by simp only [FreeGroup.mul_mk, FreeGroup.inv_mk];
          exact mk_eq_mk_of_reduce (by decide))
  have h23 : Step s22 s23 :=
    step_conj1 (a := u1) (b := u18) (b' := u19) (FreeGroup.mk [(0, true)])
      (by simp only [FreeGroup.mul_mk, FreeGroup.inv_mk];
          exact mk_eq_mk_of_reduce (by decide))
  have h24 : Step s23 s24 :=
    step_mul10 (a := u1) (b := u19) (b' := u20)
      (by rw [FreeGroup.mul_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h25 : Step s24 s25 :=
    step_conj1 (a := u1) (b := u20) (b' := u21) (FreeGroup.mk [(1, true)])
      (by simp only [FreeGroup.mul_mk, FreeGroup.inv_mk];
          exact mk_eq_mk_of_reduce (by decide))
  have h26 : Step s25 s26 :=
    step_conj1 (a := u1) (b := u21) (b' := u22) (FreeGroup.mk [(0, true)])
      (by simp only [FreeGroup.mul_mk, FreeGroup.inv_mk];
          exact mk_eq_mk_of_reduce (by decide))
  have h27 : Step s26 s27 :=
    step_mul10 (a := u1) (b := u22) (b' := u23)
      (by rw [FreeGroup.mul_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h28 : Step s27 s28 :=
    step_conj0 (a := u1) (b := u23) (a' := u11) (FreeGroup.mk [(1, false)])
      (by simp only [FreeGroup.mul_mk, FreeGroup.inv_mk];
          exact mk_eq_mk_of_reduce (by decide))
  have h29 : Step s28 s29 :=
    step_conj0 (a := u11) (b := u23) (a' := u24) (FreeGroup.mk [(0, true)])
      (by simp only [FreeGroup.mul_mk, FreeGroup.inv_mk];
          exact mk_eq_mk_of_reduce (by decide))
  have h30 : Step s29 s30 :=
    step_conj0 (a := u24) (b := u23) (a' := u25) (FreeGroup.mk [(1, true)])
      (by simp only [FreeGroup.mul_mk, FreeGroup.inv_mk];
          exact mk_eq_mk_of_reduce (by decide))
  have h31 : Step s30 s31 :=
    step_inv1 (a := u25) (b := u23) (b' := u26)
      (by rw [FreeGroup.inv_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h32 : Step s31 s32 :=
    step_mul01 (a := u25) (b := u26) (a' := u27)
      (by rw [FreeGroup.mul_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h33 : Step s32 s33 :=
    step_inv1 (a := u27) (b := u26) (b' := u23)
      (by rw [FreeGroup.inv_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h34 : Step s33 s34 :=
    step_conj0 (a := u27) (b := u23) (a' := u28) (FreeGroup.mk [(0, false)])
      (by simp only [FreeGroup.mul_mk, FreeGroup.inv_mk];
          exact mk_eq_mk_of_reduce (by decide))
  have h35 : Step s34 s35 :=
    step_inv1 (a := u28) (b := u23) (b' := u26)
      (by rw [FreeGroup.inv_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h36 : Step s35 s36 :=
    step_mul01 (a := u28) (b := u26) (a' := u29)
      (by rw [FreeGroup.mul_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h37 : Step s36 s37 :=
    step_inv1 (a := u29) (b := u26) (b' := u23)
      (by rw [FreeGroup.inv_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h38 : Step s37 s38 :=
    step_conj0 (a := u29) (b := u23) (a' := u30) (FreeGroup.mk [(0, false)])
      (by simp only [FreeGroup.mul_mk, FreeGroup.inv_mk];
          exact mk_eq_mk_of_reduce (by decide))
  have h39 : Step s38 s39 :=
    step_inv1 (a := u30) (b := u23) (b' := u26)
      (by rw [FreeGroup.inv_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h40 : Step s39 s40 :=
    step_mul01 (a := u30) (b := u26) (a' := u31)
      (by rw [FreeGroup.mul_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h41 : Step s40 s41 :=
    step_inv1 (a := u31) (b := u26) (b' := u23)
      (by rw [FreeGroup.inv_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h42 : Step s41 s42 :=
    step_conj1 (a := u31) (b := u23) (b' := u32) (FreeGroup.mk [(1, true), (0, true), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false)])
      (by simp only [FreeGroup.mul_mk, FreeGroup.inv_mk];
          exact mk_eq_mk_of_reduce (by decide))
  have h43 : Step s42 s43 :=
    step_conj0 (a := u31) (b := u32) (a' := u33) (FreeGroup.mk [(1, true)])
      (by simp only [FreeGroup.mul_mk, FreeGroup.inv_mk];
          exact mk_eq_mk_of_reduce (by decide))
  have h44 : Step s43 s44 :=
    step_conj0 (a := u33) (b := u32) (a' := u34) (FreeGroup.mk [(0, true)])
      (by simp only [FreeGroup.mul_mk, FreeGroup.inv_mk];
          exact mk_eq_mk_of_reduce (by decide))
  have h45 : Step s44 s45 :=
    step_conj0 (a := u34) (b := u32) (a' := u35) (FreeGroup.mk [(1, false)])
      (by simp only [FreeGroup.mul_mk, FreeGroup.inv_mk];
          exact mk_eq_mk_of_reduce (by decide))
  have h46 : Step s45 s46 :=
    step_conj0 (a := u35) (b := u32) (a' := u36) (FreeGroup.mk [(0, false)])
      (by simp only [FreeGroup.mul_mk, FreeGroup.inv_mk];
          exact mk_eq_mk_of_reduce (by decide))
  have h47 : Step s46 s47 :=
    step_mul01 (a := u36) (b := u32) (a' := u37)
      (by rw [FreeGroup.mul_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h48 : Step s47 s48 :=
    step_conj0 (a := u37) (b := u32) (a' := u38) (FreeGroup.mk [(0, true), (0, true), (1, false), (0, false), (1, true), (0, true)])
      (by simp only [FreeGroup.mul_mk, FreeGroup.inv_mk];
          exact mk_eq_mk_of_reduce (by decide))
  have h49 : Step s48 s49 :=
    step_mul10 (a := u38) (b := u32) (b' := u39)
      (by rw [FreeGroup.mul_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h50 : Step s49 s50 :=
    step_conj0 (a := u38) (b := u39) (a' := u40) (FreeGroup.mk [(0, false), (1, false)])
      (by simp only [FreeGroup.mul_mk, FreeGroup.inv_mk];
          exact mk_eq_mk_of_reduce (by decide))
  have h51 : Step s50 s51 :=
    step_mul01 (a := u40) (b := u39) (a' := u41)
      (by rw [FreeGroup.mul_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h52 : Step s51 s52 :=
    step_conj1 (a := u41) (b := u39) (b' := u42) (FreeGroup.mk [(1, true), (0, true)])
      (by simp only [FreeGroup.mul_mk, FreeGroup.inv_mk];
          exact mk_eq_mk_of_reduce (by decide))
  have h53 : Step s52 s53 :=
    step_conj0 (a := u41) (b := u42) (a' := u43) (FreeGroup.mk [(1, true)])
      (by simp only [FreeGroup.mul_mk, FreeGroup.inv_mk];
          exact mk_eq_mk_of_reduce (by decide))
  have h54 : Step s53 s54 :=
    step_inv1 (a := u43) (b := u42) (b' := u44)
      (by rw [FreeGroup.inv_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h55 : Step s54 s55 :=
    step_mul01 (a := u43) (b := u44) (a' := u45)
      (by rw [FreeGroup.mul_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h56 : Step s55 s56 :=
    step_inv1 (a := u45) (b := u44) (b' := u42)
      (by rw [FreeGroup.inv_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h57 : Step s56 s57 :=
    step_conj0 (a := u45) (b := u42) (a' := u46) (FreeGroup.mk [(1, true), (0, true)])
      (by simp only [FreeGroup.mul_mk, FreeGroup.inv_mk];
          exact mk_eq_mk_of_reduce (by decide))
  have h58 : Step s57 s58 :=
    step_inv1 (a := u46) (b := u42) (b' := u44)
      (by rw [FreeGroup.inv_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h59 : Step s58 s59 :=
    step_mul01 (a := u46) (b := u44) (a' := u47)
      (by rw [FreeGroup.mul_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h60 : Step s59 s60 :=
    step_inv1 (a := u47) (b := u44) (b' := u42)
      (by rw [FreeGroup.inv_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h61 : Step s60 s61 :=
    step_conj0 (a := u47) (b := u42) (a' := u48) (FreeGroup.mk [(0, false), (1, true), (0, true)])
      (by simp only [FreeGroup.mul_mk, FreeGroup.inv_mk];
          exact mk_eq_mk_of_reduce (by decide))
  have h62 : Step s61 s62 :=
    step_conj1 (a := u48) (b := u42) (b' := u49) (FreeGroup.mk [(0, false)])
      (by simp only [FreeGroup.mul_mk, FreeGroup.inv_mk];
          exact mk_eq_mk_of_reduce (by decide))
  have h63 : Step s62 s63 :=
    step_inv1 (a := u48) (b := u49) (b' := u50)
      (by rw [FreeGroup.inv_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h64 : Step s63 s64 :=
    step_mul01 (a := u48) (b := u50) (a' := u5)
      (by rw [FreeGroup.mul_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h65 : Step s64 s65 :=
    step_inv1 (a := u5) (b := u50) (b' := u49)
      (by rw [FreeGroup.inv_mk]; exact mk_eq_mk_of_reduce (by decide))
  have h66 : Step s65 s66 :=
    step_conj1 (a := u5) (b := u49) (b' := u51) (FreeGroup.mk [(0, true), (0, true), (0, true), (1, false), (0, false)])
      (by simp only [FreeGroup.mul_mk, FreeGroup.inv_mk];
          exact mk_eq_mk_of_reduce (by decide))
  have h67 : Step s66 s67 :=
    step_conj0 (a := u5) (b := u51) (a' := u52) (FreeGroup.mk [(0, false)])
      (by simp only [FreeGroup.mul_mk, FreeGroup.inv_mk];
          exact mk_eq_mk_of_reduce (by decide))
  have t1 : Reachable s0 s1 := Relation.ReflTransGen.single h1
  have t2 : Reachable s0 s2 := t1.trans (Relation.ReflTransGen.single h2)
  have t3 : Reachable s0 s3 := t2.trans (Relation.ReflTransGen.single h3)
  have t4 : Reachable s0 s4 := t3.trans (Relation.ReflTransGen.single h4)
  have t5 : Reachable s0 s5 := t4.trans (Relation.ReflTransGen.single h5)
  have t6 : Reachable s0 s6 := t5.trans (Relation.ReflTransGen.single h6)
  have t7 : Reachable s0 s7 := t6.trans (Relation.ReflTransGen.single h7)
  have t8 : Reachable s0 s8 := t7.trans (Relation.ReflTransGen.single h8)
  have t9 : Reachable s0 s9 := t8.trans (Relation.ReflTransGen.single h9)
  have t10 : Reachable s0 s10 := t9.trans (Relation.ReflTransGen.single h10)
  have t11 : Reachable s0 s11 := t10.trans (Relation.ReflTransGen.single h11)
  have t12 : Reachable s0 s12 := t11.trans (Relation.ReflTransGen.single h12)
  have t13 : Reachable s0 s13 := t12.trans (Relation.ReflTransGen.single h13)
  have t14 : Reachable s0 s14 := t13.trans (Relation.ReflTransGen.single h14)
  have t15 : Reachable s0 s15 := t14.trans (Relation.ReflTransGen.single h15)
  have t16 : Reachable s0 s16 := t15.trans (Relation.ReflTransGen.single h16)
  have t17 : Reachable s0 s17 := t16.trans (Relation.ReflTransGen.single h17)
  have t18 : Reachable s0 s18 := t17.trans (Relation.ReflTransGen.single h18)
  have t19 : Reachable s0 s19 := t18.trans (Relation.ReflTransGen.single h19)
  have t20 : Reachable s0 s20 := t19.trans (Relation.ReflTransGen.single h20)
  have t21 : Reachable s0 s21 := t20.trans (Relation.ReflTransGen.single h21)
  have t22 : Reachable s0 s22 := t21.trans (Relation.ReflTransGen.single h22)
  have t23 : Reachable s0 s23 := t22.trans (Relation.ReflTransGen.single h23)
  have t24 : Reachable s0 s24 := t23.trans (Relation.ReflTransGen.single h24)
  have t25 : Reachable s0 s25 := t24.trans (Relation.ReflTransGen.single h25)
  have t26 : Reachable s0 s26 := t25.trans (Relation.ReflTransGen.single h26)
  have t27 : Reachable s0 s27 := t26.trans (Relation.ReflTransGen.single h27)
  have t28 : Reachable s0 s28 := t27.trans (Relation.ReflTransGen.single h28)
  have t29 : Reachable s0 s29 := t28.trans (Relation.ReflTransGen.single h29)
  have t30 : Reachable s0 s30 := t29.trans (Relation.ReflTransGen.single h30)
  have t31 : Reachable s0 s31 := t30.trans (Relation.ReflTransGen.single h31)
  have t32 : Reachable s0 s32 := t31.trans (Relation.ReflTransGen.single h32)
  have t33 : Reachable s0 s33 := t32.trans (Relation.ReflTransGen.single h33)
  have t34 : Reachable s0 s34 := t33.trans (Relation.ReflTransGen.single h34)
  have t35 : Reachable s0 s35 := t34.trans (Relation.ReflTransGen.single h35)
  have t36 : Reachable s0 s36 := t35.trans (Relation.ReflTransGen.single h36)
  have t37 : Reachable s0 s37 := t36.trans (Relation.ReflTransGen.single h37)
  have t38 : Reachable s0 s38 := t37.trans (Relation.ReflTransGen.single h38)
  have t39 : Reachable s0 s39 := t38.trans (Relation.ReflTransGen.single h39)
  have t40 : Reachable s0 s40 := t39.trans (Relation.ReflTransGen.single h40)
  have t41 : Reachable s0 s41 := t40.trans (Relation.ReflTransGen.single h41)
  have t42 : Reachable s0 s42 := t41.trans (Relation.ReflTransGen.single h42)
  have t43 : Reachable s0 s43 := t42.trans (Relation.ReflTransGen.single h43)
  have t44 : Reachable s0 s44 := t43.trans (Relation.ReflTransGen.single h44)
  have t45 : Reachable s0 s45 := t44.trans (Relation.ReflTransGen.single h45)
  have t46 : Reachable s0 s46 := t45.trans (Relation.ReflTransGen.single h46)
  have t47 : Reachable s0 s47 := t46.trans (Relation.ReflTransGen.single h47)
  have t48 : Reachable s0 s48 := t47.trans (Relation.ReflTransGen.single h48)
  have t49 : Reachable s0 s49 := t48.trans (Relation.ReflTransGen.single h49)
  have t50 : Reachable s0 s50 := t49.trans (Relation.ReflTransGen.single h50)
  have t51 : Reachable s0 s51 := t50.trans (Relation.ReflTransGen.single h51)
  have t52 : Reachable s0 s52 := t51.trans (Relation.ReflTransGen.single h52)
  have t53 : Reachable s0 s53 := t52.trans (Relation.ReflTransGen.single h53)
  have t54 : Reachable s0 s54 := t53.trans (Relation.ReflTransGen.single h54)
  have t55 : Reachable s0 s55 := t54.trans (Relation.ReflTransGen.single h55)
  have t56 : Reachable s0 s56 := t55.trans (Relation.ReflTransGen.single h56)
  have t57 : Reachable s0 s57 := t56.trans (Relation.ReflTransGen.single h57)
  have t58 : Reachable s0 s58 := t57.trans (Relation.ReflTransGen.single h58)
  have t59 : Reachable s0 s59 := t58.trans (Relation.ReflTransGen.single h59)
  have t60 : Reachable s0 s60 := t59.trans (Relation.ReflTransGen.single h60)
  have t61 : Reachable s0 s61 := t60.trans (Relation.ReflTransGen.single h61)
  have t62 : Reachable s0 s62 := t61.trans (Relation.ReflTransGen.single h62)
  have t63 : Reachable s0 s63 := t62.trans (Relation.ReflTransGen.single h63)
  have t64 : Reachable s0 s64 := t63.trans (Relation.ReflTransGen.single h64)
  have t65 : Reachable s0 s65 := t64.trans (Relation.ReflTransGen.single h65)
  have t66 : Reachable s0 s66 := t65.trans (Relation.ReflTransGen.single h66)
  have t67 : Reachable s0 s67 := t66.trans (Relation.ReflTransGen.single h67)
  have hfin : s67 = p1State := rfl
  exact hfin ▸ t67

/-! ## 7. Axiom record -/

#print axioms reachable_pivot_p1

end P1Bridge
end Nielsen
end AC
