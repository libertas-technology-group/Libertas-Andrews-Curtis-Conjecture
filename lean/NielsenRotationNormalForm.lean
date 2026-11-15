module

/-
# NielsenRotationNormalForm — the rotation normal form of the (5,7) witness

The report records the length-five, length-seven slice of the both-long block as
open: "the seven-move collapse stalls on a concrete witness pair, and the
universal statement over that slice remains open"
(`PLANNED_37_NIELSEN_THEORY.md:578`).  The session source states the concrete
witness descent `fiveSeven_witness_descent` and the rotation obstruction
`fiveSeven_rotation_fails`: the fixed seven-stage list reaches the pair of
generators from `(r7Shape, s5Shape)` but does not reach it from the rotation
`(r7Shape.rotate 0, s5Shape.rotate 1)` (`EXPLORATION/AcNielsen.lean:3971-3974`,
stage list at `3933-3936`, witness descent at `4011-4025`).

This module supplies the missing rotation normal form.  A cyclic rotation of one
relator is one official Andrews–Curtis step (`rotate_step`), and at rank two the
cyclic Nielsen length is unchanged by a rotation of a cyclically reduced relator
(`rotation_normal_form`).  Consequently the seven-stage witness transports
across rotations (`fiveSeven_rotated_witness_descent`): to descend from a
rotation, rotate the state back to the base orientation with `rotate_step`, run
the witness, and the measure is the same at the rotated start.  The stage list
failing on the rotated pair is therefore not an obstruction to the descent.

The base-orientation witness descent is the proposition
`SevenStageWitnessDescent` below.  It is proved in this repository at
`NielsenSevenStage.lean:430`, so this module states the transport that lets the
proved witness reach the rotated starts.  The universal `cyclicNielsen_both_long_descent` remains open, as the
report states at `PLANNED_37_NIELSEN_THEORY.md:572-578`.

The dependencies are `AcNielsenDefs` for `cycLen`, `cyclicNielsenLength`, and
`AbelianTerminal`, and `AcProof` for `ProofAttempt.presents_of_reachable`.  No
`sorry`, `admit`, `axiom`, or `native_decide` is used.
-/

public import AcNielsenDefs
public import AcProof
public import Mathlib.Data.List.Rotate

@[expose] public section

set_option autoImplicit false

namespace AC
namespace Nielsen
namespace RotationNormalForm

variable {n : ℕ}

/-! ## 1. Cyclic reduction fixes a cyclically reduced word -/

/-- Cyclic reduction fixes a cyclically reduced list.  This is the analogue of
`EXPLORATION/AcNielsen.lean:213-228`, restated against `FreeGroup.reduceCyclically`. -/
theorem reduceCyclically_eq_self {α : Type*} [DecidableEq α] {L : List (α × Bool)}
    (h : FreeGroup.IsCyclicallyReduced L) : FreeGroup.reduceCyclically L = L := by
  induction L using List.bidirectionalRec with
  | nil => simp
  | singleton a => simp
  | cons_append a l b _ih =>
      rw [FreeGroup.reduceCyclically.cons_append]
      have h' : FreeGroup.IsCyclicallyReduced ((a :: l) ++ [b]) := by
        rw [List.cons_append]
        exact h
      have hcond : ¬ (b.1 = a.1 ∧ (!b.2) = a.2) := by
        rintro ⟨hba, hnb⟩
        have hb2 : b.2 = a.2 :=
          (FreeGroup.isCyclicallyReduced_cons_append_iff.mp h').2 hba
        cases hb : b.2 <;> cases ha : a.2 <;> simp_all
      rw [ite_eq_right hcond, List.cons_append]

/-! ## 2. A cyclic rotation of a cyclically reduced list is cyclically reduced -/

/-- One-step rotation of a cyclically reduced list is cyclically reduced. -/
theorem isCyclicallyReduced_rotate_one {α : Type*} {L : List (α × Bool)}
    (h : FreeGroup.IsCyclicallyReduced L) :
    FreeGroup.IsCyclicallyReduced (L.rotate 1) := by
  cases L with
  | nil => simp
  | cons a L =>
      rw [List.rotate_cons_succ, List.rotate_zero]
      cases L with
      | nil => simp
      | cons b M =>
          have hred : FreeGroup.IsReduced (a :: b :: M) := h.isReduced
          rw [FreeGroup.isReduced_cons_cons] at hred
          constructor
          · refine List.IsChain.append hred.2 (List.isChain_singleton a) ?_
            intro x hx y hy
            simp only [List.head?_singleton, Option.mem_def, Option.some.injEq] at hy
            rw [← hy]
            exact h.2 x (List.mem_getLast?_cons hx) a (by simp)
          · intro x hx y hy
            have hx' : a = x := by
              have hlast : List.getLast? ((b :: M) ++ [a]) = some a := by
                rw [List.getLast?_append_of_ne_nil (b :: M) (l₂ := [a]) (by simp)]
                rfl
              rw [hlast] at hx
              simpa using hx
            have hy' : b = y := by simpa using hy
            rw [← hx', ← hy']
            exact hred.1

/-- Any cyclic rotation of a cyclically reduced list is cyclically reduced. -/
theorem isCyclicallyReduced_rotate {α : Type*} (L : List (α × Bool)) (m : ℕ)
    (h : FreeGroup.IsCyclicallyReduced L) :
    FreeGroup.IsCyclicallyReduced (L.rotate m) := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
      rw [← List.rotate_rotate L m 1]
      exact isCyclicallyReduced_rotate_one ih

/-! ## 3. Rotation is one official Andrews–Curtis step -/

/-- The group-level rotation identity: rotating a list by `m` letters conjugates
its free-group element by the inverse of the prefix of length `m % L.length`.
This is the word-level content of `EXPLORATION/AcNielsen.lean:1840-1856`. -/
theorem mk_rotate_eq_conj {α : Type*} (L : List (α × Bool)) (m : ℕ) :
    FreeGroup.mk (L.rotate m) =
      (FreeGroup.mk (L.take (m % L.length)))⁻¹ * FreeGroup.mk L *
        FreeGroup.mk (L.take (m % L.length)) := by
  let m' : ℕ := m % L.length
  have hrot : L.rotate m = L.drop m' ++ L.take m' :=
    List.rotate_eq_drop_append_take_mod
  have hsplit : L = L.take m' ++ L.drop m' := (List.take_append_drop m' L).symm
  have h1 : FreeGroup.mk L =
      FreeGroup.mk (L.take m') * FreeGroup.mk (L.drop m') := by
    rw [FreeGroup.mul_mk, ← hsplit]
  have h2 : FreeGroup.mk (L.rotate m) =
      FreeGroup.mk (L.drop m') * FreeGroup.mk (L.take m') := by
    rw [hrot, FreeGroup.mul_mk]
  rw [h1, h2]
  simp only [m']
  group

/-- **Rotation normal form, step form.**  A cyclic rotation of one relator of a
rank-`n` state is one official Andrews–Curtis step.  This is the statement of
`rotate_step` at `EXPLORATION/AcNielsen.lean:1833-1859`, stated for every rank. -/
theorem rotate_step (R : Relators n) (i : Fin n) (L : List (Fin n × Bool)) (m : ℕ)
    (hL : R i = FreeGroup.mk L) :
    ∃ R' : Relators n, Step R R' ∧ R' i = FreeGroup.mk (L.rotate m) ∧
      ∀ k : Fin n, k ≠ i → R' k = R k := by
  let m' : ℕ := m % L.length
  let u : Word n := FreeGroup.mk (L.take m')
  have hrot : L.rotate m = L.drop m' ++ L.take m' :=
    List.rotate_eq_drop_append_take_mod
  have hsplit : L = L.take m' ++ L.drop m' := (List.take_append_drop m' L).symm
  refine ⟨Function.update R i (FreeGroup.mk (L.rotate m)), ?_, ?_, ?_⟩
  · have h := Step.conj R i u⁻¹
    have h1 : FreeGroup.mk L =
        FreeGroup.mk (L.take m') * FreeGroup.mk (L.drop m') := by
      rw [FreeGroup.mul_mk, ← hsplit]
    have h2 : FreeGroup.mk (L.rotate m) =
        FreeGroup.mk (L.drop m') * FreeGroup.mk (L.take m') := by
      rw [hrot, FreeGroup.mul_mk]
    have hval : u⁻¹ * R i * (u⁻¹)⁻¹ = FreeGroup.mk (L.rotate m) := by
      rw [hL, h1, h2]
      simp only [u]
      group
    rw [hval] at h
    exact h
  · rw [Function.update_self]
  · intro k hk
    rw [Function.update_of_ne hk]

/-! ## 4. The rank-two measure is rotation invariant -/

/-- The cyclic Nielsen length of a rank-two tuple is the sum of its two cyclic
lengths. -/
theorem cyclicNielsenLength_pair (R : Relators 2) :
    cyclicNielsenLength R = cycLen (R 0) + cycLen (R 1) := by
  unfold cyclicNielsenLength
  rw [Fin.sum_univ_two]

/-- The measure after replacing the zeroth relator. -/
theorem cyclicNielsenLength_update_zero (R : Relators 2) (w : Word 2) :
    cyclicNielsenLength (Function.update R 0 w) = cycLen w + cycLen (R 1) := by
  rw [cyclicNielsenLength_pair, Function.update_self,
    Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]

/-- The measure after replacing the first relator. -/
theorem cyclicNielsenLength_update_one (R : Relators 2) (w : Word 2) :
    cyclicNielsenLength (Function.update R 1 w) = cycLen (R 0) + cycLen w := by
  rw [cyclicNielsenLength_pair, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1),
    Function.update_self]

/-- Rotation preserves the cyclic Nielsen length of a cyclically reduced word. -/
theorem cycLen_mk_rotate {L : List (Fin n × Bool)} {m : ℕ}
    (h : FreeGroup.IsCyclicallyReduced L) :
    cycLen (FreeGroup.mk (L.rotate m)) = cycLen (FreeGroup.mk L) := by
  have h1 : FreeGroup.IsCyclicallyReduced (L.rotate m) :=
    isCyclicallyReduced_rotate L m h
  have hL : (FreeGroup.mk L).toWord = L := by
    rw [FreeGroup.toWord_mk]
    exact FreeGroup.isReduced_iff_reduce_eq.mp h.isReduced
  have hm : (FreeGroup.mk (L.rotate m)).toWord = L.rotate m := by
    rw [FreeGroup.toWord_mk]
    exact FreeGroup.isReduced_iff_reduce_eq.mp h1.isReduced
  unfold cycLen
  rw [hm, hL, reduceCyclically_eq_self h1, reduceCyclically_eq_self h,
    List.length_rotate]

/-- **Rotation normal form at rank two.**  Rotating one relator of a rank-two
state is one official Andrews–Curtis step, and the cyclic Nielsen length is
unchanged when the rotated relator is cyclically reduced. -/
theorem rotation_normal_form (R : Relators 2) (i : Fin 2) (L : List (Fin 2 × Bool))
    (m : ℕ) (hL : R i = FreeGroup.mk L)
    (hcyc : FreeGroup.IsCyclicallyReduced L) :
    Reachable R (Function.update R i (FreeGroup.mk (L.rotate m))) ∧
      cyclicNielsenLength (Function.update R i (FreeGroup.mk (L.rotate m))) =
        cyclicNielsenLength R := by
  constructor
  · obtain ⟨R', hstep, hR'i, hR'rest⟩ := rotate_step R i L m hL
    have hR' : R' = Function.update R i (FreeGroup.mk (L.rotate m)) := by
      funext k
      by_cases hk : k = i
      · subst hk
        rw [hR'i, Function.update_self]
      · rw [hR'rest k hk, Function.update_of_ne hk]
    rw [hR'] at hstep
    exact Relation.ReflTransGen.single hstep
  · fin_cases i
    · change cyclicNielsenLength
          (Function.update R 0 (FreeGroup.mk (L.rotate m))) = cyclicNielsenLength R
      have hL0 : R 0 = FreeGroup.mk L := hL
      rw [cyclicNielsenLength_update_zero, cyclicNielsenLength_pair, hL0,
        cycLen_mk_rotate hcyc]
    · change cyclicNielsenLength
          (Function.update R 1 (FreeGroup.mk (L.rotate m))) = cyclicNielsenLength R
      have hL1 : R 1 = FreeGroup.mk L := hL
      rw [cyclicNielsenLength_update_one, cyclicNielsenLength_pair, hL1,
        cycLen_mk_rotate hcyc]

/-! ## 5. The (5,7) witness and its rotations -/

/-- The length-seven relator of the witness: `x x y X X X Y`.  This is
`r7Shape` at `EXPLORATION/AcNielsen.lean:3304-3306`. -/
def r7Shape : List (Fin 2 × Bool) :=
  [(0, false), (0, false), (1, false), (0, true), (0, true), (0, true), (1, true)]

/-- The length-five relator of the witness: `x y X Y Y`.  This is `s5Shape` at
`EXPLORATION/AcNielsen.lean:3309-3310`. -/
def s5Shape : List (Fin 2 × Bool) :=
  [(0, false), (1, false), (0, true), (1, true), (1, true)]

theorem r7Shape_length : r7Shape.length = 7 := rfl

theorem s5Shape_length : s5Shape.length = 5 := rfl

/-- Two adjacent letters do not cancel. -/
def pairOK (a b : Fin 2 × Bool) : Bool :=
  !(a.1 == b.1 && a.2 == !b.2)

/-- A computable form of `FreeGroup.IsReduced`. -/
def isReducedB : List (Fin 2 × Bool) → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => pairOK a b && isReducedB (b :: t)

/-- A computable form of `FreeGroup.IsCyclicallyReduced`. -/
def isCycRedB (L : List (Fin 2 × Bool)) : Bool :=
  isReducedB L &&
    match L.getLast?, L.head? with
    | some a, some b => pairOK a b
    | _, _ => true

theorem pairOK_eq_true {a b : Fin 2 × Bool} :
    pairOK a b = true ↔ (a.1 = b.1 → a.2 = b.2) := by
  obtain ⟨x, s⟩ := a
  obtain ⟨y, t⟩ := b
  cases s <;> cases t <;> simp [pairOK]

theorem isReducedB_iff (L : List (Fin 2 × Bool)) :
    isReducedB L = true ↔ FreeGroup.IsReduced L := by
  induction L with
  | nil => simp [isReducedB, FreeGroup.IsReduced.nil]
  | cons a t ih =>
      cases t with
      | nil => simp [isReducedB, FreeGroup.IsReduced.singleton]
      | cons b t' =>
          simp only [isReducedB, Bool.and_eq_true, ih, FreeGroup.isReduced_cons_cons]
          exact and_congr pairOK_eq_true Iff.rfl

theorem option_forall_pair {a b : Option (Fin 2 × Bool)}
    {p : Fin 2 × Bool → Fin 2 × Bool → Prop} :
    (∀ x ∈ a, ∀ y ∈ b, p x y) ↔
      (match a, b with | some x, some y => p x y | _, _ => True) := by
  cases a <;> cases b <;> simp [Option.mem_def]

theorem isCycRedB_iff (L : List (Fin 2 × Bool)) :
    isCycRedB L = true ↔ FreeGroup.IsCyclicallyReduced L := by
  unfold isCycRedB
  rw [FreeGroup.isCyclicallyReduced_iff, Bool.and_eq_true, isReducedB_iff]
  cases h : L.getLast? <;> cases h' : L.head? <;>
    simp [pairOK_eq_true]

theorem r7Shape_isCyclicallyReduced : FreeGroup.IsCyclicallyReduced r7Shape :=
  (isCycRedB_iff r7Shape).mp (by decide)

theorem s5Shape_isCyclicallyReduced : FreeGroup.IsCyclicallyReduced s5Shape :=
  (isCycRedB_iff s5Shape).mp (by decide)

/-- The base orientation of the witness, `(r7Shape, s5Shape)`. -/
def witnessState : Relators 2 := ![FreeGroup.mk r7Shape, FreeGroup.mk s5Shape]

/-- A coordinate-wise cyclic rotation of the witness. -/
def witnessRotate (a b : ℕ) : Relators 2 :=
  ![FreeGroup.mk (r7Shape.rotate a), FreeGroup.mk (s5Shape.rotate b)]

@[simp] theorem witnessState_zero : witnessState 0 = FreeGroup.mk r7Shape := rfl

@[simp] theorem witnessState_one : witnessState 1 = FreeGroup.mk s5Shape := rfl

@[simp] theorem witnessRotate_zero (a b : ℕ) :
    witnessRotate a b 0 = FreeGroup.mk (r7Shape.rotate a) := rfl

@[simp] theorem witnessRotate_one (a b : ℕ) :
    witnessRotate a b 1 = FreeGroup.mk (s5Shape.rotate b) := rfl

theorem witnessState_cycRed :
    ∀ i : Fin 2, FreeGroup.IsCyclicallyReduced (witnessState i).toWord := by
  intro i
  fin_cases i
  · change FreeGroup.IsCyclicallyReduced (FreeGroup.mk r7Shape).toWord
    rw [FreeGroup.toWord_mk,
      FreeGroup.isReduced_iff_reduce_eq.mp
        (FreeGroup.IsCyclicallyReduced.isReduced r7Shape_isCyclicallyReduced)]
    exact r7Shape_isCyclicallyReduced
  · change FreeGroup.IsCyclicallyReduced (FreeGroup.mk s5Shape).toWord
    rw [FreeGroup.toWord_mk,
      FreeGroup.isReduced_iff_reduce_eq.mp
        (FreeGroup.IsCyclicallyReduced.isReduced s5Shape_isCyclicallyReduced)]
    exact s5Shape_isCyclicallyReduced

/-- Every rotation of the witness has the same cyclic Nielsen length. -/
theorem cyclicNielsenLength_witnessRotate (a b : ℕ) :
    cyclicNielsenLength (witnessRotate a b) = cyclicNielsenLength witnessState := by
  rw [cyclicNielsenLength_pair, cyclicNielsenLength_pair]
  rw [witnessRotate_zero, witnessRotate_one, witnessState_zero, witnessState_one]
  rw [cycLen_mk_rotate r7Shape_isCyclicallyReduced,
    cycLen_mk_rotate s5Shape_isCyclicallyReduced]

/-- Every coordinate-wise rotation of the witness is reachable from the base
orientation by two official steps. -/
theorem witnessRotate_reachable (a b : ℕ) :
    Reachable witnessState (witnessRotate a b) := by
  obtain ⟨S1, h1, hS1_0, hS1_rest⟩ :=
    rotate_step witnessState 0 r7Shape a (by simp [witnessState])
  have hS1_1 : S1 1 = FreeGroup.mk s5Shape := by
    rw [hS1_rest 1 (by decide), witnessState_one]
  obtain ⟨S2, h2, hS2_1, hS2_rest⟩ :=
    rotate_step S1 1 s5Shape b hS1_1
  have hS2_0 : S2 0 = FreeGroup.mk (r7Shape.rotate a) := by
    rw [hS2_rest 0 (by decide), hS1_0]
  have hS2eq : S2 = witnessRotate a b := by
    funext i
    fin_cases i
    · change S2 0 = witnessRotate a b 0
      rw [hS2_0, witnessRotate_zero]
    · change S2 1 = witnessRotate a b 1
      rw [hS2_1, witnessRotate_one]
  rw [hS2eq] at h2
  exact (Relation.ReflTransGen.single h1).trans (Relation.ReflTransGen.single h2)

/-- Rotating a list by `m` and then by `length - m % length` returns the list. -/
theorem rotate_rotate_length_sub_mod {α : Type*} (L : List α) (m : ℕ) :
    (L.rotate m).rotate (L.length - m % L.length) = L := by
  rcases eq_or_ne L [] with rfl | _hL
  · simp
  · have hpos : 0 < L.length := List.length_pos_of_ne_nil _hL
    rw [List.rotate_rotate]
    have h : m + (L.length - m % L.length) = L.length * (m / L.length + 1) := by
      calc
        m + (L.length - m % L.length)
            = (L.length * (m / L.length) + m % L.length) +
                (L.length - m % L.length) := by rw [Nat.div_add_mod]
        _ = L.length * (m / L.length) +
              (m % L.length + (L.length - m % L.length)) := by rw [Nat.add_assoc]
        _ = L.length * (m / L.length) + L.length := by
              rw [Nat.add_sub_of_le (a := m % L.length) (b := L.length)
                (Nat.le_of_lt (Nat.mod_lt m hpos))]
        _ = L.length * (m / L.length + 1) := by rw [Nat.mul_add, Nat.mul_one]
    rw [h, List.rotate_length_mul]

/-- Every coordinate-wise rotation of the witness reaches the base orientation.
This is the inverse of `witnessRotate_reachable`, built from the same official
rotation step. -/
theorem witnessState_reachable_witnessRotate (a b : ℕ) :
    Reachable (witnessRotate a b) witnessState := by
  obtain ⟨S1, h1, hS1_0, hS1_rest⟩ :=
    rotate_step (witnessRotate a b) 0 (r7Shape.rotate a)
      (r7Shape.length - a % r7Shape.length) (by simp [witnessRotate])
  have hS1_0' : S1 0 = FreeGroup.mk r7Shape := by
    rw [hS1_0, rotate_rotate_length_sub_mod]
  have hS1_1 : S1 1 = FreeGroup.mk (s5Shape.rotate b) := by
    rw [hS1_rest 1 (by decide), witnessRotate_one]
  obtain ⟨S2, h2, hS2_1, hS2_rest⟩ :=
    rotate_step S1 1 (s5Shape.rotate b)
      (s5Shape.length - b % s5Shape.length) hS1_1
  have hS2_0 : S2 0 = FreeGroup.mk r7Shape := by
    rw [hS2_rest 0 (by decide), hS1_0']
  have hS2_1' : S2 1 = FreeGroup.mk s5Shape := by
    rw [hS2_1, rotate_rotate_length_sub_mod]
  have hS2eq : S2 = witnessState := by
    funext i
    fin_cases i
    · change S2 0 = witnessState 0
      rw [hS2_0, witnessState_zero]
    · change S2 1 = witnessState 1
      rw [hS2_1', witnessState_one]
  rw [hS2eq] at h2
  exact (Relation.ReflTransGen.single h1).trans (Relation.ReflTransGen.single h2)

/-! ## 6. Transport of the seven-stage witness across rotations -/

/-- The base-orientation seven-stage witness descent: the conclusion of
`fiveSeven_witness_descent` at `EXPLORATION/AcNielsen.lean:4011-4025`.  The
endpoint is abelian terminal and the cyclic Nielsen length is strictly smaller.
This is the hypothesis the rotation transport consumes; the witness is proved in
this repository at `NielsenSevenStage.lean:430`. -/
def SevenStageWitnessDescent : Prop :=
  ∃ T : Relators 2, Reachable witnessState T ∧ AbelianTerminal T ∧
    cyclicNielsenLength T < cyclicNielsenLength witnessState

/-- **Rotation transport of the seven-stage witness.**  Every coordinate-wise
cyclic rotation of the (5,7) witness descends to the same abelian-terminal
endpoint as the base orientation.  The fixed stage list fails on the rotation
`(r7Shape.rotate 0, s5Shape.rotate 1)` (`fiveSeven_rotation_fails`), but the
rotation is undone by official steps and the measure is unchanged, so the
descent transports. -/
theorem fiveSeven_rotated_witness_descent (hbase : SevenStageWitnessDescent)
    (a b : ℕ) :
    ∃ T : Relators 2, Reachable (witnessRotate a b) T ∧ AbelianTerminal T ∧
      cyclicNielsenLength T < cyclicNielsenLength (witnessRotate a b) := by
  obtain ⟨T, hT, hAb, hlt⟩ := hbase
  exact ⟨T, (witnessState_reachable_witnessRotate a b).trans hT, hAb, by
    rwa [cyclicNielsenLength_witnessRotate]⟩

/-- The concrete rotation named in `fiveSeven_rotation_fails` descends. -/
theorem fiveSeven_rotation_one_descent (hbase : SevenStageWitnessDescent) :
    ∃ T : Relators 2, Reachable (witnessRotate 0 1) T ∧ AbelianTerminal T ∧
      cyclicNielsenLength T < cyclicNielsenLength (witnessRotate 0 1) :=
  fiveSeven_rotated_witness_descent hbase 0 1

/-- The transport with the presentation-triviality conjunct carried through,
matching the full conclusion of `fiveSeven_witness_descent` at
`EXPLORATION/AcNielsen.lean:4011-4025`. -/
theorem fiveSeven_rotated_witness_descent_full
    (hp : PresentsTrivialGroup witnessState)
    (hbase : ∃ T : Relators 2, Reachable witnessState T ∧ AbelianTerminal T ∧
      cyclicNielsenLength T < cyclicNielsenLength witnessState)
    (a b : ℕ) :
    ∃ T : Relators 2, Reachable (witnessRotate a b) T ∧ AbelianTerminal T ∧
      PresentsTrivialGroup T ∧
      cyclicNielsenLength T < cyclicNielsenLength (witnessRotate a b) := by
  obtain ⟨T, hT, hAb, hlt⟩ := hbase
  have hpt : PresentsTrivialGroup T := (ProofAttempt.presents_of_reachable hT).mp hp
  exact ⟨T, (witnessState_reachable_witnessRotate a b).trans hT, hAb, hpt, by
    rwa [cyclicNielsenLength_witnessRotate]⟩

end RotationNormalForm
end Nielsen
end AC
