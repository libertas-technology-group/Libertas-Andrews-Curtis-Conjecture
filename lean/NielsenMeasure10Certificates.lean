module

/-
# NielsenMeasure10Certificates — kernel chains for the eight measure-10 states

`DISCOVERY/measure10_certificates.json` records, for each of the eight ordered
abelian-terminal states of cyclic Nielsen length 10, a replay-verified list of
official moves that carries the state to an abelian-terminal state of cyclic
Nielsen length 6.  This module turns those lists into kernel-checked `Step`
chains and derives `SliceBridge.DescentFrom` at each of the eight states.

## The representation

A state is a `Relators 2` tuple, written as two explicit free-group words in the
generators `gx = FreeGroup.of 0` and `gy = FreeGroup.of 1`.  A letter of the
search script's alphabet maps to a generator as `a ↦ gx`, `A ↦ gx⁻¹`, `b ↦ gy`,
`B ↦ gy⁻¹`, so the `AABab` string is
`gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy`.

## The replay is literal

The search script keeps each relator cyclically reduced, and cyclic reduction
is a conjugation, not an equality: one search step is one official move followed
by a conjugation.  Reading the six move labels literally therefore reaches the
reported endpoint only after those conjugations are inserted.  Every chain
below is the search script's move list with each such conjugation written as an
explicit `Step.conj` by one letter, so the endpoint reached here is the endpoint
the script reports, word for word.

## The proof shape

Each step is one of the three official move forms as a `Step` constructor —
`Step.inv`, `Step.mulRight`, `Step.conj` — with the resulting word equation
discharged by `group`.  Each descent theorem supplies its endpoint, its chain,
abelian terminality at the endpoint, triviality of the presented group, and the
drop from measure 10 to measure 6.

No `sorry`, `admit`, `axiom`, or `native_decide` occurs in this file.  The axiom
record at the end reports the trusted base of the eight descent theorems.
-/

public import AcNielsenDefs
public import AcProof
public import NielsenRotationNormalForm
public import NielsenSevenStage
public import NielsenSliceBridge
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000
-- The move-chain simp sets are written once and reused across the eight
-- certificates; an argument that is idle on one chain is needed on another.
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace AC
namespace Nielsen
namespace Measure10

open SliceBridge
open RotationNormalForm

/-! ## 1. The two generators -/

abbrev gx : Word 2 := FreeGroup.of 0

abbrev gy : Word 2 := FreeGroup.of 1

/-! ## 2. The words of the eight certificates and their endpoints

Each name is the script's letter string with a `w` prefix. -/

abbrev wA : Word 2 := gx⁻¹
abbrev wAABa : Word 2 := gx⁻¹ * gx⁻¹ * gy⁻¹ * gx
abbrev wAABab : Word 2 := gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy
abbrev wAAbaB : Word 2 := gx⁻¹ * gx⁻¹ * gy * gx * gy⁻¹
abbrev wAB : Word 2 := gx⁻¹ * gy⁻¹
abbrev wABAAbaa : Word 2 := gx⁻¹ * gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx * gx
abbrev wABAba : Word 2 := gx⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx
abbrev wABBAbba : Word 2 := gx⁻¹ * gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy * gx
abbrev wABBab : Word 2 := gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy
abbrev wABa : Word 2 := gx⁻¹ * gy⁻¹ * gx
abbrev wABaBAba : Word 2 := gx⁻¹ * gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy * gx
abbrev wABaa : Word 2 := gx⁻¹ * gy⁻¹ * gx * gx
abbrev wABabb : Word 2 := gx⁻¹ * gy⁻¹ * gx * gy * gy
abbrev wABabbaBAba : Word 2 := gx⁻¹ * gy⁻¹ * gx * gy * gy * gx * gy⁻¹ * gx⁻¹ * gy * gx
abbrev wAb : Word 2 := gx⁻¹ * gy
abbrev wAbABa : Word 2 := gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gx
abbrev wAbaabABa : Word 2 := gx⁻¹ * gy * gx * gx * gy * gx⁻¹ * gy⁻¹ * gx
abbrev wB : Word 2 := gy⁻¹
abbrev wBA : Word 2 := gy⁻¹ * gx⁻¹
abbrev wBAABab : Word 2 := gy⁻¹ * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy
abbrev wBAAba : Word 2 := gy⁻¹ * gx⁻¹ * gx⁻¹ * gy * gx
abbrev wBABab : Word 2 := gy⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy
abbrev wBAb : Word 2 := gy⁻¹ * gx⁻¹ * gy
abbrev wBAbABab : Word 2 := gy⁻¹ * gx⁻¹ * gy * gx⁻¹ * gy⁻¹ * gx * gy
abbrev wBAbaa : Word 2 := gy⁻¹ * gx⁻¹ * gy * gx * gx
abbrev wBAbaabABab : Word 2 := gy⁻¹ * gx⁻¹ * gy * gx * gx * gy * gx⁻¹ * gy⁻¹ * gx * gy
abbrev wBAbb : Word 2 := gy⁻¹ * gx⁻¹ * gy * gy
abbrev wBAbba : Word 2 := gy⁻¹ * gx⁻¹ * gy * gy * gx
abbrev wBBAba : Word 2 := gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx
abbrev wBBAbb : Word 2 := gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gy
abbrev wBBabb : Word 2 := gy⁻¹ * gy⁻¹ * gx * gy * gy
abbrev wBa : Word 2 := gy⁻¹ * gx
abbrev wBaBAb : Word 2 := gy⁻¹ * gx * gy⁻¹ * gx⁻¹ * gy
abbrev wBab : Word 2 := gy⁻¹ * gx * gy
abbrev wBabbaBAb : Word 2 := gy⁻¹ * gx * gy * gy * gx * gy⁻¹ * gx⁻¹ * gy
abbrev wa : Word 2 := gx
abbrev waBA : Word 2 := gx * gy⁻¹ * gx⁻¹
abbrev waBAba : Word 2 := gx * gy⁻¹ * gx⁻¹ * gy * gx
abbrev waabA : Word 2 := gx * gx * gy * gx⁻¹
abbrev wab : Word 2 := gx * gy
abbrev wabbaBA : Word 2 := gx * gy * gy * gx * gy⁻¹ * gx⁻¹
abbrev wb : Word 2 := gy
abbrev wbAB : Word 2 := gy * gx⁻¹ * gy⁻¹
abbrev wbABab : Word 2 := gy * gx⁻¹ * gy⁻¹ * gx * gy
abbrev wba : Word 2 := gy * gx
abbrev wbaabAB : Word 2 := gy * gx * gx * gy * gx⁻¹ * gy⁻¹
abbrev wbbaB : Word 2 := gy * gy * gx * gy⁻¹

/-! ## 3. One official move as a `Step` constructor -/

theorem step_inv0 {a b a' : Word 2} (h : a' = a⁻¹) : Step ![a, b] ![a', b] := by
  have hs : Step ![a, b] (Function.update ![a, b] 0 (![a, b] 0)⁻¹) := Step.inv ![a, b] 0
  have he : Function.update ![a, b] 0 (![a, b] 0)⁻¹ = ![a', b] := by
    funext i
    fin_cases i <;> simp [h]
  rwa [he] at hs

theorem step_inv1 {a b b' : Word 2} (h : b' = b⁻¹) : Step ![a, b] ![a, b'] := by
  have hs : Step ![a, b] (Function.update ![a, b] 1 (![a, b] 1)⁻¹) := Step.inv ![a, b] 1
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

theorem step_conj0 {a b c a' : Word 2} (h : a' = c * a * c⁻¹) : Step ![a, b] ![a', b] := by
  have hs : Step ![a, b] (Function.update ![a, b] 0 (c * ![a, b] 0 * c⁻¹)) :=
    Step.conj ![a, b] 0 c
  have he : Function.update ![a, b] 0 (c * ![a, b] 0 * c⁻¹) = ![a', b] := by
    funext i
    fin_cases i <;> simp [h]
  rwa [he] at hs

theorem step_conj1 {a b c b' : Word 2} (h : b' = c * b * c⁻¹) : Step ![a, b] ![a, b'] := by
  have hs : Step ![a, b] (Function.update ![a, b] 1 (c * ![a, b] 1 * c⁻¹)) :=
    Step.conj ![a, b] 1 c
  have he : Function.update ![a, b] 1 (c * ![a, b] 1 * c⁻¹) = ![a, b'] := by
    funext i
    fin_cases i <;> simp [h]
  rwa [he] at hs

/-! ## 4. Cyclic lengths of the start and endpoint words

The cyclic length of a cyclically reduced list is its length
(`NielsenSevenStage.lean:65`).  Each word here is a coordinate of a start state
or of an endpoint, and each is cyclically reduced. -/

theorem cycLen_mk_reduced {L : List (Fin 2 × Bool)} (hL : FreeGroup.IsCyclicallyReduced L) :
    cycLen (FreeGroup.mk L) = L.length :=
  SevenStage.cycLen_mk_of_isCyclicallyReduced hL


theorem cycLen_wA : cycLen wA = 1 := by
  have h : wA = FreeGroup.mk [(0, false)] := rfl
  rw [h]
  exact cycLen_mk_reduced (by simp [FreeGroup.IsCyclicallyReduced, FreeGroup.IsReduced])

theorem cycLen_wAABab : cycLen wAABab = 5 := by
  have h : wAABab = FreeGroup.mk [(0, false), (0, false), (1, false), (0, true), (1, true)] := rfl
  rw [h]
  exact cycLen_mk_reduced (by simp [FreeGroup.IsCyclicallyReduced, FreeGroup.IsReduced])

theorem cycLen_wAAbaB : cycLen wAAbaB = 5 := by
  have h : wAAbaB = FreeGroup.mk [(0, false), (0, false), (1, true), (0, true), (1, false)] := rfl
  rw [h]
  exact cycLen_mk_reduced (by simp [FreeGroup.IsCyclicallyReduced, FreeGroup.IsReduced])

theorem cycLen_wABBab : cycLen wABBab = 5 := by
  have h : wABBab = FreeGroup.mk [(0, false), (1, false), (1, false), (0, true), (1, true)] := rfl
  rw [h]
  exact cycLen_mk_reduced (by simp [FreeGroup.IsCyclicallyReduced, FreeGroup.IsReduced])

theorem cycLen_wABabb : cycLen wABabb = 5 := by
  have h : wABabb = FreeGroup.mk [(0, false), (1, false), (0, true), (1, true), (1, true)] := rfl
  rw [h]
  exact cycLen_mk_reduced (by simp [FreeGroup.IsCyclicallyReduced, FreeGroup.IsReduced])

theorem cycLen_wB : cycLen wB = 1 := by
  have h : wB = FreeGroup.mk [(1, false)] := rfl
  rw [h]
  exact cycLen_mk_reduced (by simp [FreeGroup.IsCyclicallyReduced, FreeGroup.IsReduced])

theorem cycLen_wBAbba : cycLen wBAbba = 5 := by
  have h : wBAbba = FreeGroup.mk [(1, false), (0, false), (1, true), (1, true), (0, true)] := rfl
  rw [h]
  exact cycLen_mk_reduced (by simp [FreeGroup.IsCyclicallyReduced, FreeGroup.IsReduced])

theorem cycLen_wBBAba : cycLen wBBAba = 5 := by
  have h : wBBAba = FreeGroup.mk [(1, false), (1, false), (0, false), (1, true), (0, true)] := rfl
  rw [h]
  exact cycLen_mk_reduced (by simp [FreeGroup.IsCyclicallyReduced, FreeGroup.IsReduced])

theorem cycLen_wa : cycLen wa = 1 := by
  have h : wa = FreeGroup.mk [(0, true)] := rfl
  rw [h]
  exact cycLen_mk_reduced (by simp [FreeGroup.IsCyclicallyReduced, FreeGroup.IsReduced])

theorem cycLen_waBAba : cycLen waBAba = 5 := by
  have h : waBAba = FreeGroup.mk [(0, true), (1, false), (0, false), (1, true), (0, true)] := rfl
  rw [h]
  exact cycLen_mk_reduced (by simp [FreeGroup.IsCyclicallyReduced, FreeGroup.IsReduced])

theorem cycLen_wbABab : cycLen wbABab = 5 := by
  have h : wbABab = FreeGroup.mk [(1, true), (0, false), (1, false), (0, true), (1, true)] := rfl
  rw [h]
  exact cycLen_mk_reduced (by simp [FreeGroup.IsCyclicallyReduced, FreeGroup.IsReduced])


/-! ## 5. Exponent vectors of the endpoint words -/


theorem expVec_wA : Invariant.expVec wA = -Invariant.genVec (0 : Fin 2) := by
  simp [Invariant.expVec, Invariant.expHom, FreeGroup.lift_apply_of]
  all_goals
    ext j
    fin_cases j <;> simp [Invariant.genVec]

theorem expVec_wAABab : Invariant.expVec wAABab = -Invariant.genVec (0 : Fin 2) := by
  simp [Invariant.expVec, Invariant.expHom, FreeGroup.lift_apply_of]
  all_goals
    ext j
    fin_cases j <;> simp [Invariant.genVec]

theorem expVec_wABBab : Invariant.expVec wABBab = -Invariant.genVec (1 : Fin 2) := by
  simp [Invariant.expVec, Invariant.expHom, FreeGroup.lift_apply_of]
  all_goals
    ext j
    fin_cases j <;> simp [Invariant.genVec]

theorem expVec_wABabb : Invariant.expVec wABabb = Invariant.genVec (1 : Fin 2) := by
  simp [Invariant.expVec, Invariant.expHom, FreeGroup.lift_apply_of]
  all_goals
    ext j
    fin_cases j <;> simp [Invariant.genVec]

theorem expVec_wB : Invariant.expVec wB = -Invariant.genVec (1 : Fin 2) := by
  simp [Invariant.expVec, Invariant.expHom, FreeGroup.lift_apply_of]
  all_goals
    ext j
    fin_cases j <;> simp [Invariant.genVec]

theorem expVec_wBAbba : Invariant.expVec wBAbba = Invariant.genVec (1 : Fin 2) := by
  simp [Invariant.expVec, Invariant.expHom, FreeGroup.lift_apply_of]
  all_goals
    ext j
    fin_cases j <;> simp [Invariant.genVec]

theorem expVec_wBBAba : Invariant.expVec wBBAba = -Invariant.genVec (1 : Fin 2) := by
  simp [Invariant.expVec, Invariant.expHom, FreeGroup.lift_apply_of]
  all_goals
    ext j
    fin_cases j <;> simp [Invariant.genVec]

theorem expVec_wa : Invariant.expVec wa = Invariant.genVec (0 : Fin 2) := by
  simp [Invariant.expVec, Invariant.expHom, FreeGroup.lift_apply_of]
  all_goals
    ext j
    fin_cases j <;> simp [Invariant.genVec]

theorem expVec_waBAba : Invariant.expVec waBAba = Invariant.genVec (0 : Fin 2) := by
  simp [Invariant.expVec, Invariant.expHom, FreeGroup.lift_apply_of]
  all_goals
    ext j
    fin_cases j <;> simp [Invariant.genVec]

theorem expVec_wbABab : Invariant.expVec wbABab = Invariant.genVec (1 : Fin 2) := by
  simp [Invariant.expVec, Invariant.expHom, FreeGroup.lift_apply_of]
  all_goals
    ext j
    fin_cases j <;> simp [Invariant.genVec]


/-! ## 6. Triviality of the presented group at a state with a generator relator -/

theorem mk_mul_apply {R : Relators 2} (a b : Word 2) :
    PresentedGroup.mk (Set.range R) (a * b) =
      PresentedGroup.mk (Set.range R) a * PresentedGroup.mk (Set.range R) b :=
  map_mul (PresentedGroup.mk (Set.range R)) a b

theorem mk_inv_apply {R : Relators 2} (a : Word 2) :
    PresentedGroup.mk (Set.range R) a⁻¹ = (PresentedGroup.mk (Set.range R) a)⁻¹ :=
  map_inv (PresentedGroup.mk (Set.range R)) a

theorem presentsTrivialGroup_of_mk_generators {R : Relators 2}
    (h0 : PresentedGroup.mk (Set.range R) (FreeGroup.of 0) = 1)
    (h1 : PresentedGroup.mk (Set.range R) (FreeGroup.of 1) = 1) :
    PresentsTrivialGroup R := by
  have h0' : PresentedGroup.of (rels := Set.range R) (0 : Fin 2) = 1 := h0
  have h1' : PresentedGroup.of (rels := Set.range R) (1 : Fin 2) = 1 := h1
  have htop : Subgroup.closure (Set.range (PresentedGroup.of : Fin 2 → PresentedGroup (Set.range R))) = ⊤ :=
    PresentedGroup.closure_range_of _
  have hle : Subgroup.closure (Set.range (PresentedGroup.of : Fin 2 → PresentedGroup (Set.range R))) ≤ ⊥ := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · simpa using h0'
    · simpa using h1'
  have hbot : (⊤ : Subgroup (PresentedGroup (Set.range R))) = ⊥ := by
    rw [← htop]
    exact le_bot_iff.mp hle
  refine ⟨fun a b => ?_⟩
  have ha : a = 1 := by
    have hm : a ∈ (⊥ : Subgroup (PresentedGroup (Set.range R))) := hbot ▸ Subgroup.mem_top a
    simpa using hm
  have hb : b = 1 := by
    have hm : b ∈ (⊥ : Subgroup (PresentedGroup (Set.range R))) := hbot ▸ Subgroup.mem_top b
    simpa using hm
  rw [ha, hb]


/-! ## Certificate 1: `AABab` / `ABabb` to `A` / `bABab` -/

def state_1 : Relators 2 := ![wAABab, wABabb]
def c1_1 : Relators 2 := ![wBAbaa, wABabb]
def c1_2 : Relators 2 := ![wBAbaa, wbABab]
def c1_3 : Relators 2 := ![wBAbaabABab, wbABab]
def c1_4 : Relators 2 := ![wAbaabABa, wbABab]
def c1_5 : Relators 2 := ![wbaabAB, wbABab]
def c1_6 : Relators 2 := ![waabA, wbABab]
def c1_7 : Relators 2 := ![wab, wbABab]
def c1_8 : Relators 2 := ![wBA, wbABab]
def c1_9 : Relators 2 := ![wBAbABab, wbABab]
def c1_10 : Relators 2 := ![wAbABa, wbABab]
def c1_11 : Relators 2 := ![wbAB, wbABab]
def endpoint_1 : Relators 2 := ![wA, wbABab]

theorem reach_state_1 : Reachable state_1 endpoint_1 := by
  have h1 : Step state_1 c1_1 :=
    step_inv0 (a := wAABab) (b := wABabb) (a' := wBAbaa)
      (by simp only [wAABab, wABabb, wBAbaa, gx, gy, mul_inv_rev, inv_inv, mul_assoc]; first | done | rfl | group | norm_num)
  have h2 : Step c1_1 c1_2 :=
    step_conj1 (a := wBAbaa) (b := wABabb) (c := wb) (b' := wbABab)
      (by simp only [wABabb, wb, wbABab, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h3 : Step c1_2 c1_3 :=
    step_mul01 (a := wBAbaa) (b := wbABab) (a' := wBAbaabABab)
      (by simp only [wBAbaa, wBAbaabABab, wbABab, gx, gy, mul_assoc]; first | done | rfl | group | norm_num)
  have h4 : Step c1_3 c1_4 :=
    step_conj0 (a := wBAbaabABab) (b := wbABab) (c := wb) (a' := wAbaabABa)
      (by simp only [wAbaabABa, wBAbaabABab, wb, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h5 : Step c1_4 c1_5 :=
    step_conj0 (a := wAbaabABa) (b := wbABab) (c := wa) (a' := wbaabAB)
      (by simp only [wAbaabABa, wa, wbaabAB, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h6 : Step c1_5 c1_6 :=
    step_conj0 (a := wbaabAB) (b := wbABab) (c := wB) (a' := waabA)
      (by simp only [wB, waabA, wbaabAB, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h7 : Step c1_6 c1_7 :=
    step_conj0 (a := waabA) (b := wbABab) (c := wA) (a' := wab)
      (by simp only [wA, waabA, wab, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h8 : Step c1_7 c1_8 :=
    step_inv0 (a := wab) (b := wbABab) (a' := wBA)
      (by simp only [wBA, wab, wbABab, gx, gy, mul_inv_rev, inv_inv, mul_assoc]; first | done | rfl | group | norm_num)
  have h9 : Step c1_8 c1_9 :=
    step_mul01 (a := wBA) (b := wbABab) (a' := wBAbABab)
      (by simp only [wBA, wBAbABab, wbABab, gx, gy, mul_assoc]; first | done | rfl | group | norm_num)
  have h10 : Step c1_9 c1_10 :=
    step_conj0 (a := wBAbABab) (b := wbABab) (c := wb) (a' := wAbABa)
      (by simp only [wAbABa, wBAbABab, wb, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h11 : Step c1_10 c1_11 :=
    step_conj0 (a := wAbABa) (b := wbABab) (c := wa) (a' := wbAB)
      (by simp only [wAbABa, wa, wbAB, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h12 : Step c1_11 endpoint_1 :=
    step_conj0 (a := wbAB) (b := wbABab) (c := wB) (a' := wA)
      (by simp only [wA, wB, wbAB, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  exact (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h1)
      (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h2)
            (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h3)
                  (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h4)
                        (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h5)
                              (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h6)
                                    (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h7)
                                          (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h8)
                                                (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h9)
                                                      (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h10)
                                                            (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h11)
                                                                  (Relation.ReflTransGen.single h12))))))))))))

theorem abelianTerminal_1 : AbelianTerminal endpoint_1 := by
  refine ⟨id, Function.bijective_id, ![false, true], ?_⟩
  intro i
  fin_cases i
  · simpa [endpoint_1] using expVec_wA
  · simpa [endpoint_1] using expVec_wbABab

theorem presentsTrivialGroup_1 : PresentsTrivialGroup endpoint_1 := by
  have hgen0 : PresentedGroup.mk (Set.range endpoint_1) (FreeGroup.of 0) = 1 := by
    have h := PresentedGroup.one_of_mem (rels := Set.range endpoint_1) (x := endpoint_1 0)
      (Set.mem_range_self 0)
    have hw : endpoint_1 0 = gx⁻¹ := rfl
    rw [hw] at h
    simp only [gx, gy, mk_mul_apply, mk_inv_apply, mul_one, one_mul, inv_one] at h
    exact inv_eq_one.mp h
  have hgen1 : PresentedGroup.mk (Set.range endpoint_1) (FreeGroup.of 1) = 1 := by
    have h := PresentedGroup.one_of_mem (rels := Set.range endpoint_1) (x := endpoint_1 1)
      (Set.mem_range_self 1)
    have hw : endpoint_1 1 = gy * gx⁻¹ * gy⁻¹ * gx * gy := rfl
    rw [hw] at h
    simp only [gx, gy, mk_mul_apply, mk_inv_apply, mul_one, one_mul, inv_one] at h
    rw [hgen0] at h
    simp only [mul_one, one_mul, inv_one] at h
    have h' : (PresentedGroup.mk (Set.range endpoint_1) (FreeGroup.of 1)) = 1 := by
      rw [← h]
      group
    exact h'
  exact presentsTrivialGroup_of_mk_generators (R := endpoint_1) hgen0 hgen1

theorem length_state_1 : cyclicNielsenLength state_1 = 10 := by
  rw [cyclicNielsenLength_pair]
  change cycLen wAABab + cycLen wABabb = 10
  rw [cycLen_wAABab, cycLen_wABabb]

theorem length_endpoint_1 : cyclicNielsenLength endpoint_1 = 6 := by
  rw [cyclicNielsenLength_pair]
  change cycLen wA + cycLen wbABab = 6
  rw [cycLen_wA, cycLen_wbABab]

theorem descent_state_1 : DescentFrom state_1 := by
  refine ⟨endpoint_1, reach_state_1, abelianTerminal_1, presentsTrivialGroup_1, ?_⟩
  rw [length_endpoint_1, length_state_1]
  norm_num


/-! ## Certificate 2: `AABab` / `ABBab` to `AABab` / `B` -/

def state_2 : Relators 2 := ![wAABab, wABBab]
def c2_1 : Relators 2 := ![wBAbaa, wABBab]
def c2_2 : Relators 2 := ![wBAbaa, wABaa]
def c2_3 : Relators 2 := ![wBAbaa, wBa]
def c2_4 : Relators 2 := ![wAABab, wBa]
def c2_5 : Relators 2 := ![wAABab, wBABab]
def c2_6 : Relators 2 := ![wAABab, wABa]
def endpoint_2 : Relators 2 := ![wAABab, wB]

theorem reach_state_2 : Reachable state_2 endpoint_2 := by
  have h1 : Step state_2 c2_1 :=
    step_inv0 (a := wAABab) (b := wABBab) (a' := wBAbaa)
      (by simp only [wAABab, wABBab, wBAbaa, gx, gy, mul_inv_rev, inv_inv, mul_assoc]; first | done | rfl | group | norm_num)
  have h2 : Step c2_1 c2_2 :=
    step_mul10 (a := wBAbaa) (b := wABBab) (b' := wABaa)
      (by simp only [wABBab, wABaa, wBAbaa, gx, gy, mul_assoc]; first | done | rfl | group | norm_num)
  have h3 : Step c2_2 c2_3 :=
    step_conj1 (a := wBAbaa) (b := wABaa) (c := wa) (b' := wBa)
      (by simp only [wABaa, wBa, wa, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h4 : Step c2_3 c2_4 :=
    step_inv0 (a := wBAbaa) (b := wBa) (a' := wAABab)
      (by simp only [wAABab, wBAbaa, wBa, gx, gy, mul_inv_rev, inv_inv, mul_assoc]; first | done | rfl | group | norm_num)
  have h5 : Step c2_4 c2_5 :=
    step_mul10 (a := wAABab) (b := wBa) (b' := wBABab)
      (by simp only [wAABab, wBABab, wBa, gx, gy, mul_assoc]; first | done | rfl | group | norm_num)
  have h6 : Step c2_5 c2_6 :=
    step_conj1 (a := wAABab) (b := wBABab) (c := wb) (b' := wABa)
      (by simp only [wABa, wBABab, wb, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h7 : Step c2_6 endpoint_2 :=
    step_conj1 (a := wAABab) (b := wABa) (c := wa) (b' := wB)
      (by simp only [wABa, wB, wa, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  exact (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h1)
      (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h2)
            (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h3)
                  (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h4)
                        (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h5)
                              (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h6)
                                    (Relation.ReflTransGen.single h7)))))))

theorem abelianTerminal_2 : AbelianTerminal endpoint_2 := by
  refine ⟨id, Function.bijective_id, ![false, false], ?_⟩
  intro i
  fin_cases i
  · simpa [endpoint_2] using expVec_wAABab
  · simpa [endpoint_2] using expVec_wB

theorem presentsTrivialGroup_2 : PresentsTrivialGroup endpoint_2 := by
  have hgen1 : PresentedGroup.mk (Set.range endpoint_2) (FreeGroup.of 1) = 1 := by
    have h := PresentedGroup.one_of_mem (rels := Set.range endpoint_2) (x := endpoint_2 1)
      (Set.mem_range_self 1)
    have hw : endpoint_2 1 = gy⁻¹ := rfl
    rw [hw] at h
    simp only [gx, gy, mk_mul_apply, mk_inv_apply, mul_one, one_mul, inv_one] at h
    exact inv_eq_one.mp h
  have hgen0 : PresentedGroup.mk (Set.range endpoint_2) (FreeGroup.of 0) = 1 := by
    have h := PresentedGroup.one_of_mem (rels := Set.range endpoint_2) (x := endpoint_2 0)
      (Set.mem_range_self 0)
    have hw : endpoint_2 0 = gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy := rfl
    rw [hw] at h
    simp only [gx, gy, mk_mul_apply, mk_inv_apply, mul_one, one_mul, inv_one] at h
    rw [hgen1] at h
    simp only [mul_one, one_mul, inv_one] at h
    have h' : (PresentedGroup.mk (Set.range endpoint_2) (FreeGroup.of 0))⁻¹ = 1 := by
      rw [← h]
      group
    exact inv_eq_one.mp h'
  exact presentsTrivialGroup_of_mk_generators (R := endpoint_2) hgen0 hgen1

theorem length_state_2 : cyclicNielsenLength state_2 = 10 := by
  rw [cyclicNielsenLength_pair]
  change cycLen wAABab + cycLen wABBab = 10
  rw [cycLen_wAABab, cycLen_wABBab]

theorem length_endpoint_2 : cyclicNielsenLength endpoint_2 = 6 := by
  rw [cyclicNielsenLength_pair]
  change cycLen wAABab + cycLen wB = 6
  rw [cycLen_wAABab, cycLen_wB]

theorem descent_state_2 : DescentFrom state_2 := by
  refine ⟨endpoint_2, reach_state_2, abelianTerminal_2, presentsTrivialGroup_2, ?_⟩
  rw [length_endpoint_2, length_state_2]
  norm_num


/-! ## Certificate 3: `AAbaB` / `ABabb` to `A` / `BBAba` -/

def state_3 : Relators 2 := ![wAAbaB, wABabb]
def c3_1 : Relators 2 := ![wABAAbaa, wABabb]
def c3_2 : Relators 2 := ![wBAAba, wABabb]
def c3_3 : Relators 2 := ![wBAbb, wABabb]
def c3_4 : Relators 2 := ![wAb, wABabb]
def c3_5 : Relators 2 := ![wAb, wBBAba]
def c3_6 : Relators 2 := ![wABAba, wBBAba]
def c3_7 : Relators 2 := ![wBAb, wBBAba]
def endpoint_3 : Relators 2 := ![wA, wBBAba]

theorem reach_state_3 : Reachable state_3 endpoint_3 := by
  have h1 : Step state_3 c3_1 :=
    step_conj0 (a := wAAbaB) (b := wABabb) (c := wAB) (a' := wABAAbaa)
      (by simp only [wAAbaB, wAB, wABAAbaa, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h2 : Step c3_1 c3_2 :=
    step_conj0 (a := wABAAbaa) (b := wABabb) (c := wa) (a' := wBAAba)
      (by simp only [wABAAbaa, wBAAba, wa, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h3 : Step c3_2 c3_3 :=
    step_mul01 (a := wBAAba) (b := wABabb) (a' := wBAbb)
      (by simp only [wABabb, wBAAba, wBAbb, gx, gy, mul_assoc]; first | done | rfl | group | norm_num)
  have h4 : Step c3_3 c3_4 :=
    step_conj0 (a := wBAbb) (b := wABabb) (c := wb) (a' := wAb)
      (by simp only [wAb, wBAbb, wb, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h5 : Step c3_4 c3_5 :=
    step_inv1 (a := wAb) (b := wABabb) (b' := wBBAba)
      (by simp only [wABabb, wAb, wBBAba, gx, gy, mul_inv_rev, inv_inv, mul_assoc]; first | done | rfl | group | norm_num)
  have h6 : Step c3_5 c3_6 :=
    step_mul01 (a := wAb) (b := wBBAba) (a' := wABAba)
      (by simp only [wABAba, wAb, wBBAba, gx, gy, mul_assoc]; first | done | rfl | group | norm_num)
  have h7 : Step c3_6 c3_7 :=
    step_conj0 (a := wABAba) (b := wBBAba) (c := wa) (a' := wBAb)
      (by simp only [wABAba, wBAb, wa, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h8 : Step c3_7 endpoint_3 :=
    step_conj0 (a := wBAb) (b := wBBAba) (c := wb) (a' := wA)
      (by simp only [wA, wBAb, wb, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  exact (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h1)
      (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h2)
            (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h3)
                  (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h4)
                        (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h5)
                              (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h6)
                                    (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h7)
                                          (Relation.ReflTransGen.single h8))))))))

theorem abelianTerminal_3 : AbelianTerminal endpoint_3 := by
  refine ⟨id, Function.bijective_id, ![false, false], ?_⟩
  intro i
  fin_cases i
  · simpa [endpoint_3] using expVec_wA
  · simpa [endpoint_3] using expVec_wBBAba

theorem presentsTrivialGroup_3 : PresentsTrivialGroup endpoint_3 := by
  have hgen0 : PresentedGroup.mk (Set.range endpoint_3) (FreeGroup.of 0) = 1 := by
    have h := PresentedGroup.one_of_mem (rels := Set.range endpoint_3) (x := endpoint_3 0)
      (Set.mem_range_self 0)
    have hw : endpoint_3 0 = gx⁻¹ := rfl
    rw [hw] at h
    simp only [gx, gy, mk_mul_apply, mk_inv_apply, mul_one, one_mul, inv_one] at h
    exact inv_eq_one.mp h
  have hgen1 : PresentedGroup.mk (Set.range endpoint_3) (FreeGroup.of 1) = 1 := by
    have h := PresentedGroup.one_of_mem (rels := Set.range endpoint_3) (x := endpoint_3 1)
      (Set.mem_range_self 1)
    have hw : endpoint_3 1 = gy⁻¹ * gy⁻¹ * gx⁻¹ * gy * gx := rfl
    rw [hw] at h
    simp only [gx, gy, mk_mul_apply, mk_inv_apply, mul_one, one_mul, inv_one] at h
    rw [hgen0] at h
    simp only [mul_one, one_mul, inv_one] at h
    have h' : (PresentedGroup.mk (Set.range endpoint_3) (FreeGroup.of 1))⁻¹ = 1 := by
      rw [← h]
      group
    exact inv_eq_one.mp h'
  exact presentsTrivialGroup_of_mk_generators (R := endpoint_3) hgen0 hgen1

theorem length_state_3 : cyclicNielsenLength state_3 = 10 := by
  rw [cyclicNielsenLength_pair]
  change cycLen wAAbaB + cycLen wABabb = 10
  rw [cycLen_wAAbaB, cycLen_wABabb]

theorem length_endpoint_3 : cyclicNielsenLength endpoint_3 = 6 := by
  rw [cyclicNielsenLength_pair]
  change cycLen wA + cycLen wBBAba = 6
  rw [cycLen_wA, cycLen_wBBAba]

theorem descent_state_3 : DescentFrom state_3 := by
  refine ⟨endpoint_3, reach_state_3, abelianTerminal_3, presentsTrivialGroup_3, ?_⟩
  rw [length_endpoint_3, length_state_3]
  norm_num


/-! ## Certificate 4: `AAbaB` / `ABBab` to `A` / `BAbba` -/

def state_4 : Relators 2 := ![wAAbaB, wABBab]
def c4_1 : Relators 2 := ![wABAAbaa, wABBab]
def c4_2 : Relators 2 := ![wBAAba, wABBab]
def c4_3 : Relators 2 := ![wBAABab, wABBab]
def c4_4 : Relators 2 := ![wAABa, wABBab]
def c4_5 : Relators 2 := ![wAB, wABBab]
def c4_6 : Relators 2 := ![wAB, wBAbba]
def c4_7 : Relators 2 := ![wABBAbba, wBAbba]
def c4_8 : Relators 2 := ![wBBAbb, wBAbba]
def c4_9 : Relators 2 := ![wBAb, wBAbba]
def endpoint_4 : Relators 2 := ![wA, wBAbba]

theorem reach_state_4 : Reachable state_4 endpoint_4 := by
  have h1 : Step state_4 c4_1 :=
    step_conj0 (a := wAAbaB) (b := wABBab) (c := wAB) (a' := wABAAbaa)
      (by simp only [wAAbaB, wAB, wABAAbaa, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h2 : Step c4_1 c4_2 :=
    step_conj0 (a := wABAAbaa) (b := wABBab) (c := wa) (a' := wBAAba)
      (by simp only [wABAAbaa, wBAAba, wa, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h3 : Step c4_2 c4_3 :=
    step_mul01 (a := wBAAba) (b := wABBab) (a' := wBAABab)
      (by simp only [wABBab, wBAABab, wBAAba, gx, gy, mul_assoc]; first | done | rfl | group | norm_num)
  have h4 : Step c4_3 c4_4 :=
    step_conj0 (a := wBAABab) (b := wABBab) (c := wb) (a' := wAABa)
      (by simp only [wAABa, wBAABab, wb, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h5 : Step c4_4 c4_5 :=
    step_conj0 (a := wAABa) (b := wABBab) (c := wa) (a' := wAB)
      (by simp only [wAABa, wAB, wa, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h6 : Step c4_5 c4_6 :=
    step_inv1 (a := wAB) (b := wABBab) (b' := wBAbba)
      (by simp only [wAB, wABBab, wBAbba, gx, gy, mul_inv_rev, inv_inv, mul_assoc]; first | done | rfl | group | norm_num)
  have h7 : Step c4_6 c4_7 :=
    step_mul01 (a := wAB) (b := wBAbba) (a' := wABBAbba)
      (by simp only [wAB, wABBAbba, wBAbba, gx, gy, mul_assoc]; first | done | rfl | group | norm_num)
  have h8 : Step c4_7 c4_8 :=
    step_conj0 (a := wABBAbba) (b := wBAbba) (c := wa) (a' := wBBAbb)
      (by simp only [wABBAbba, wBBAbb, wa, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h9 : Step c4_8 c4_9 :=
    step_conj0 (a := wBBAbb) (b := wBAbba) (c := wb) (a' := wBAb)
      (by simp only [wBAb, wBBAbb, wb, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h10 : Step c4_9 endpoint_4 :=
    step_conj0 (a := wBAb) (b := wBAbba) (c := wb) (a' := wA)
      (by simp only [wA, wBAb, wb, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  exact (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h1)
      (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h2)
            (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h3)
                  (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h4)
                        (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h5)
                              (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h6)
                                    (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h7)
                                          (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h8)
                                                (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h9)
                                                      (Relation.ReflTransGen.single h10))))))))))

theorem abelianTerminal_4 : AbelianTerminal endpoint_4 := by
  refine ⟨id, Function.bijective_id, ![false, true], ?_⟩
  intro i
  fin_cases i
  · simpa [endpoint_4] using expVec_wA
  · simpa [endpoint_4] using expVec_wBAbba

theorem presentsTrivialGroup_4 : PresentsTrivialGroup endpoint_4 := by
  have hgen0 : PresentedGroup.mk (Set.range endpoint_4) (FreeGroup.of 0) = 1 := by
    have h := PresentedGroup.one_of_mem (rels := Set.range endpoint_4) (x := endpoint_4 0)
      (Set.mem_range_self 0)
    have hw : endpoint_4 0 = gx⁻¹ := rfl
    rw [hw] at h
    simp only [gx, gy, mk_mul_apply, mk_inv_apply, mul_one, one_mul, inv_one] at h
    exact inv_eq_one.mp h
  have hgen1 : PresentedGroup.mk (Set.range endpoint_4) (FreeGroup.of 1) = 1 := by
    have h := PresentedGroup.one_of_mem (rels := Set.range endpoint_4) (x := endpoint_4 1)
      (Set.mem_range_self 1)
    have hw : endpoint_4 1 = gy⁻¹ * gx⁻¹ * gy * gy * gx := rfl
    rw [hw] at h
    simp only [gx, gy, mk_mul_apply, mk_inv_apply, mul_one, one_mul, inv_one] at h
    rw [hgen0] at h
    simp only [mul_one, one_mul, inv_one] at h
    have h' : (PresentedGroup.mk (Set.range endpoint_4) (FreeGroup.of 1)) = 1 := by
      rw [← h]
      group
    exact h'
  exact presentsTrivialGroup_of_mk_generators (R := endpoint_4) hgen0 hgen1

theorem length_state_4 : cyclicNielsenLength state_4 = 10 := by
  rw [cyclicNielsenLength_pair]
  change cycLen wAAbaB + cycLen wABBab = 10
  rw [cycLen_wAAbaB, cycLen_wABBab]

theorem length_endpoint_4 : cyclicNielsenLength endpoint_4 = 6 := by
  rw [cyclicNielsenLength_pair]
  change cycLen wA + cycLen wBAbba = 6
  rw [cycLen_wA, cycLen_wBAbba]

theorem descent_state_4 : DescentFrom state_4 := by
  refine ⟨endpoint_4, reach_state_4, abelianTerminal_4, presentsTrivialGroup_4, ?_⟩
  rw [length_endpoint_4, length_state_4]
  norm_num


/-! ## Certificate 5: `ABabb` / `AABab` to `B` / `aBAba` -/

def state_5 : Relators 2 := ![wABabb, wAABab]
def c5_1 : Relators 2 := ![wABabb, wBAbaa]
def c5_2 : Relators 2 := ![wABabb, waBAba]
def c5_3 : Relators 2 := ![wABabbaBAba, waBAba]
def c5_4 : Relators 2 := ![wBabbaBAb, waBAba]
def c5_5 : Relators 2 := ![wabbaBA, waBAba]
def c5_6 : Relators 2 := ![wbbaB, waBAba]
def c5_7 : Relators 2 := ![wba, waBAba]
def c5_8 : Relators 2 := ![wAB, waBAba]
def c5_9 : Relators 2 := ![wABaBAba, waBAba]
def c5_10 : Relators 2 := ![wBaBAb, waBAba]
def c5_11 : Relators 2 := ![waBA, waBAba]
def endpoint_5 : Relators 2 := ![wB, waBAba]

theorem reach_state_5 : Reachable state_5 endpoint_5 := by
  have h1 : Step state_5 c5_1 :=
    step_inv1 (a := wABabb) (b := wAABab) (b' := wBAbaa)
      (by simp only [wAABab, wABabb, wBAbaa, gx, gy, mul_inv_rev, inv_inv, mul_assoc]; first | done | rfl | group | norm_num)
  have h2 : Step c5_1 c5_2 :=
    step_conj1 (a := wABabb) (b := wBAbaa) (c := wa) (b' := waBAba)
      (by simp only [wBAbaa, wa, waBAba, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h3 : Step c5_2 c5_3 :=
    step_mul01 (a := wABabb) (b := waBAba) (a' := wABabbaBAba)
      (by simp only [wABabb, wABabbaBAba, waBAba, gx, gy, mul_assoc]; first | done | rfl | group | norm_num)
  have h4 : Step c5_3 c5_4 :=
    step_conj0 (a := wABabbaBAba) (b := waBAba) (c := wa) (a' := wBabbaBAb)
      (by simp only [wABabbaBAba, wBabbaBAb, wa, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h5 : Step c5_4 c5_5 :=
    step_conj0 (a := wBabbaBAb) (b := waBAba) (c := wb) (a' := wabbaBA)
      (by simp only [wBabbaBAb, wabbaBA, wb, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h6 : Step c5_5 c5_6 :=
    step_conj0 (a := wabbaBA) (b := waBAba) (c := wA) (a' := wbbaB)
      (by simp only [wA, wabbaBA, wbbaB, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h7 : Step c5_6 c5_7 :=
    step_conj0 (a := wbbaB) (b := waBAba) (c := wB) (a' := wba)
      (by simp only [wB, wba, wbbaB, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h8 : Step c5_7 c5_8 :=
    step_inv0 (a := wba) (b := waBAba) (a' := wAB)
      (by simp only [wAB, waBAba, wba, gx, gy, mul_inv_rev, inv_inv, mul_assoc]; first | done | rfl | group | norm_num)
  have h9 : Step c5_8 c5_9 :=
    step_mul01 (a := wAB) (b := waBAba) (a' := wABaBAba)
      (by simp only [wAB, wABaBAba, waBAba, gx, gy, mul_assoc]; first | done | rfl | group | norm_num)
  have h10 : Step c5_9 c5_10 :=
    step_conj0 (a := wABaBAba) (b := waBAba) (c := wa) (a' := wBaBAb)
      (by simp only [wABaBAba, wBaBAb, wa, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h11 : Step c5_10 c5_11 :=
    step_conj0 (a := wBaBAb) (b := waBAba) (c := wb) (a' := waBA)
      (by simp only [wBaBAb, waBA, wb, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h12 : Step c5_11 endpoint_5 :=
    step_conj0 (a := waBA) (b := waBAba) (c := wA) (a' := wB)
      (by simp only [wA, wB, waBA, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  exact (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h1)
      (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h2)
            (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h3)
                  (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h4)
                        (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h5)
                              (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h6)
                                    (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h7)
                                          (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h8)
                                                (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h9)
                                                      (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h10)
                                                            (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h11)
                                                                  (Relation.ReflTransGen.single h12))))))))))))

theorem abelianTerminal_5 : AbelianTerminal endpoint_5 := by
  refine ⟨(Equiv.swap (0 : Fin 2) 1), (Equiv.swap (0 : Fin 2) 1).bijective, ![false, true], ?_⟩
  intro i
  fin_cases i
  · simpa [endpoint_5] using expVec_wB
  · simpa [endpoint_5] using expVec_waBAba

theorem presentsTrivialGroup_5 : PresentsTrivialGroup endpoint_5 := by
  have hgen1 : PresentedGroup.mk (Set.range endpoint_5) (FreeGroup.of 1) = 1 := by
    have h := PresentedGroup.one_of_mem (rels := Set.range endpoint_5) (x := endpoint_5 0)
      (Set.mem_range_self 0)
    have hw : endpoint_5 0 = gy⁻¹ := rfl
    rw [hw] at h
    simp only [gx, gy, mk_mul_apply, mk_inv_apply, mul_one, one_mul, inv_one] at h
    exact inv_eq_one.mp h
  have hgen0 : PresentedGroup.mk (Set.range endpoint_5) (FreeGroup.of 0) = 1 := by
    have h := PresentedGroup.one_of_mem (rels := Set.range endpoint_5) (x := endpoint_5 1)
      (Set.mem_range_self 1)
    have hw : endpoint_5 1 = gx * gy⁻¹ * gx⁻¹ * gy * gx := rfl
    rw [hw] at h
    simp only [gx, gy, mk_mul_apply, mk_inv_apply, mul_one, one_mul, inv_one] at h
    rw [hgen1] at h
    simp only [mul_one, one_mul, inv_one] at h
    have h' : (PresentedGroup.mk (Set.range endpoint_5) (FreeGroup.of 0)) = 1 := by
      rw [← h]
      group
    exact h'
  exact presentsTrivialGroup_of_mk_generators (R := endpoint_5) hgen0 hgen1

theorem length_state_5 : cyclicNielsenLength state_5 = 10 := by
  rw [cyclicNielsenLength_pair]
  change cycLen wABabb + cycLen wAABab = 10
  rw [cycLen_wABabb, cycLen_wAABab]

theorem length_endpoint_5 : cyclicNielsenLength endpoint_5 = 6 := by
  rw [cyclicNielsenLength_pair]
  change cycLen wB + cycLen waBAba = 6
  rw [cycLen_wB, cycLen_waBAba]

theorem descent_state_5 : DescentFrom state_5 := by
  refine ⟨endpoint_5, reach_state_5, abelianTerminal_5, presentsTrivialGroup_5, ?_⟩
  rw [length_endpoint_5, length_state_5]
  norm_num


/-! ## Certificate 6: `ABabb` / `AAbaB` to `ABabb` / `a` -/

def state_6 : Relators 2 := ![wABabb, wAAbaB]
def c6_1 : Relators 2 := ![wABabb, wABAAbaa]
def c6_2 : Relators 2 := ![wABabb, wBAAba]
def c6_3 : Relators 2 := ![wABabb, wBAbb]
def c6_4 : Relators 2 := ![wABabb, wAb]
def c6_5 : Relators 2 := ![wABabb, wBa]
def c6_6 : Relators 2 := ![wABabb, wBBabb]
def c6_7 : Relators 2 := ![wABabb, wBab]
def endpoint_6 : Relators 2 := ![wABabb, wa]

theorem reach_state_6 : Reachable state_6 endpoint_6 := by
  have h1 : Step state_6 c6_1 :=
    step_conj1 (a := wABabb) (b := wAAbaB) (c := wAB) (b' := wABAAbaa)
      (by simp only [wAAbaB, wAB, wABAAbaa, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h2 : Step c6_1 c6_2 :=
    step_conj1 (a := wABabb) (b := wABAAbaa) (c := wa) (b' := wBAAba)
      (by simp only [wABAAbaa, wBAAba, wa, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h3 : Step c6_2 c6_3 :=
    step_mul10 (a := wABabb) (b := wBAAba) (b' := wBAbb)
      (by simp only [wABabb, wBAAba, wBAbb, gx, gy, mul_assoc]; first | done | rfl | group | norm_num)
  have h4 : Step c6_3 c6_4 :=
    step_conj1 (a := wABabb) (b := wBAbb) (c := wb) (b' := wAb)
      (by simp only [wAb, wBAbb, wb, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h5 : Step c6_4 c6_5 :=
    step_inv1 (a := wABabb) (b := wAb) (b' := wBa)
      (by simp only [wABabb, wAb, wBa, gx, gy, mul_inv_rev, inv_inv, mul_assoc]; first | done | rfl | group | norm_num)
  have h6 : Step c6_5 c6_6 :=
    step_mul10 (a := wABabb) (b := wBa) (b' := wBBabb)
      (by simp only [wABabb, wBBabb, wBa, gx, gy, mul_assoc]; first | done | rfl | group | norm_num)
  have h7 : Step c6_6 c6_7 :=
    step_conj1 (a := wABabb) (b := wBBabb) (c := wb) (b' := wBab)
      (by simp only [wBBabb, wBab, wb, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h8 : Step c6_7 endpoint_6 :=
    step_conj1 (a := wABabb) (b := wBab) (c := wb) (b' := wa)
      (by simp only [wBab, wa, wb, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  exact (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h1)
      (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h2)
            (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h3)
                  (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h4)
                        (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h5)
                              (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h6)
                                    (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h7)
                                          (Relation.ReflTransGen.single h8))))))))

theorem abelianTerminal_6 : AbelianTerminal endpoint_6 := by
  refine ⟨(Equiv.swap (0 : Fin 2) 1), (Equiv.swap (0 : Fin 2) 1).bijective, ![true, true], ?_⟩
  intro i
  fin_cases i
  · simpa [endpoint_6] using expVec_wABabb
  · simpa [endpoint_6] using expVec_wa

theorem presentsTrivialGroup_6 : PresentsTrivialGroup endpoint_6 := by
  have hgen0 : PresentedGroup.mk (Set.range endpoint_6) (FreeGroup.of 0) = 1 := by
    have h := PresentedGroup.one_of_mem (rels := Set.range endpoint_6) (x := endpoint_6 1)
      (Set.mem_range_self 1)
    have hw : endpoint_6 1 = gx := rfl
    rw [hw] at h
    simp only [gx, gy, mk_mul_apply, mk_inv_apply, mul_one, one_mul, inv_one] at h
    exact h
  have hgen1 : PresentedGroup.mk (Set.range endpoint_6) (FreeGroup.of 1) = 1 := by
    have h := PresentedGroup.one_of_mem (rels := Set.range endpoint_6) (x := endpoint_6 0)
      (Set.mem_range_self 0)
    have hw : endpoint_6 0 = gx⁻¹ * gy⁻¹ * gx * gy * gy := rfl
    rw [hw] at h
    simp only [gx, gy, mk_mul_apply, mk_inv_apply, mul_one, one_mul, inv_one] at h
    rw [hgen0] at h
    simp only [mul_one, one_mul, inv_one] at h
    have h' : (PresentedGroup.mk (Set.range endpoint_6) (FreeGroup.of 1)) = 1 := by
      rw [← h]
      group
    exact h'
  exact presentsTrivialGroup_of_mk_generators (R := endpoint_6) hgen0 hgen1

theorem length_state_6 : cyclicNielsenLength state_6 = 10 := by
  rw [cyclicNielsenLength_pair]
  change cycLen wABabb + cycLen wAAbaB = 10
  rw [cycLen_wABabb, cycLen_wAAbaB]

theorem length_endpoint_6 : cyclicNielsenLength endpoint_6 = 6 := by
  rw [cyclicNielsenLength_pair]
  change cycLen wABabb + cycLen wa = 6
  rw [cycLen_wABabb, cycLen_wa]

theorem descent_state_6 : DescentFrom state_6 := by
  refine ⟨endpoint_6, reach_state_6, abelianTerminal_6, presentsTrivialGroup_6, ?_⟩
  rw [length_endpoint_6, length_state_6]
  norm_num


/-! ## Certificate 7: `ABBab` / `AABab` to `B` / `AABab` -/

def state_7 : Relators 2 := ![wABBab, wAABab]
def c7_1 : Relators 2 := ![wABBab, wBAbaa]
def c7_2 : Relators 2 := ![wABaa, wBAbaa]
def c7_3 : Relators 2 := ![wBa, wBAbaa]
def c7_4 : Relators 2 := ![wBa, wAABab]
def c7_5 : Relators 2 := ![wBABab, wAABab]
def c7_6 : Relators 2 := ![wABa, wAABab]
def endpoint_7 : Relators 2 := ![wB, wAABab]

theorem reach_state_7 : Reachable state_7 endpoint_7 := by
  have h1 : Step state_7 c7_1 :=
    step_inv1 (a := wABBab) (b := wAABab) (b' := wBAbaa)
      (by simp only [wAABab, wABBab, wBAbaa, gx, gy, mul_inv_rev, inv_inv, mul_assoc]; first | done | rfl | group | norm_num)
  have h2 : Step c7_1 c7_2 :=
    step_mul01 (a := wABBab) (b := wBAbaa) (a' := wABaa)
      (by simp only [wABBab, wABaa, wBAbaa, gx, gy, mul_assoc]; first | done | rfl | group | norm_num)
  have h3 : Step c7_2 c7_3 :=
    step_conj0 (a := wABaa) (b := wBAbaa) (c := wa) (a' := wBa)
      (by simp only [wABaa, wBa, wa, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h4 : Step c7_3 c7_4 :=
    step_inv1 (a := wBa) (b := wBAbaa) (b' := wAABab)
      (by simp only [wAABab, wBAbaa, wBa, gx, gy, mul_inv_rev, inv_inv, mul_assoc]; first | done | rfl | group | norm_num)
  have h5 : Step c7_4 c7_5 :=
    step_mul01 (a := wBa) (b := wAABab) (a' := wBABab)
      (by simp only [wAABab, wBABab, wBa, gx, gy, mul_assoc]; first | done | rfl | group | norm_num)
  have h6 : Step c7_5 c7_6 :=
    step_conj0 (a := wBABab) (b := wAABab) (c := wb) (a' := wABa)
      (by simp only [wABa, wBABab, wb, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h7 : Step c7_6 endpoint_7 :=
    step_conj0 (a := wABa) (b := wAABab) (c := wa) (a' := wB)
      (by simp only [wABa, wB, wa, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  exact (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h1)
      (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h2)
            (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h3)
                  (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h4)
                        (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h5)
                              (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h6)
                                    (Relation.ReflTransGen.single h7)))))))

theorem abelianTerminal_7 : AbelianTerminal endpoint_7 := by
  refine ⟨(Equiv.swap (0 : Fin 2) 1), (Equiv.swap (0 : Fin 2) 1).bijective, ![false, false], ?_⟩
  intro i
  fin_cases i
  · simpa [endpoint_7] using expVec_wB
  · simpa [endpoint_7] using expVec_wAABab

theorem presentsTrivialGroup_7 : PresentsTrivialGroup endpoint_7 := by
  have hgen1 : PresentedGroup.mk (Set.range endpoint_7) (FreeGroup.of 1) = 1 := by
    have h := PresentedGroup.one_of_mem (rels := Set.range endpoint_7) (x := endpoint_7 0)
      (Set.mem_range_self 0)
    have hw : endpoint_7 0 = gy⁻¹ := rfl
    rw [hw] at h
    simp only [gx, gy, mk_mul_apply, mk_inv_apply, mul_one, one_mul, inv_one] at h
    exact inv_eq_one.mp h
  have hgen0 : PresentedGroup.mk (Set.range endpoint_7) (FreeGroup.of 0) = 1 := by
    have h := PresentedGroup.one_of_mem (rels := Set.range endpoint_7) (x := endpoint_7 1)
      (Set.mem_range_self 1)
    have hw : endpoint_7 1 = gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gy := rfl
    rw [hw] at h
    simp only [gx, gy, mk_mul_apply, mk_inv_apply, mul_one, one_mul, inv_one] at h
    rw [hgen1] at h
    simp only [mul_one, one_mul, inv_one] at h
    have h' : (PresentedGroup.mk (Set.range endpoint_7) (FreeGroup.of 0))⁻¹ = 1 := by
      rw [← h]
      group
    exact inv_eq_one.mp h'
  exact presentsTrivialGroup_of_mk_generators (R := endpoint_7) hgen0 hgen1

theorem length_state_7 : cyclicNielsenLength state_7 = 10 := by
  rw [cyclicNielsenLength_pair]
  change cycLen wABBab + cycLen wAABab = 10
  rw [cycLen_wABBab, cycLen_wAABab]

theorem length_endpoint_7 : cyclicNielsenLength endpoint_7 = 6 := by
  rw [cyclicNielsenLength_pair]
  change cycLen wB + cycLen wAABab = 6
  rw [cycLen_wB, cycLen_wAABab]

theorem descent_state_7 : DescentFrom state_7 := by
  refine ⟨endpoint_7, reach_state_7, abelianTerminal_7, presentsTrivialGroup_7, ?_⟩
  rw [length_endpoint_7, length_state_7]
  norm_num


/-! ## Certificate 8: `ABBab` / `AAbaB` to `ABBab` / `a` -/

def state_8 : Relators 2 := ![wABBab, wAAbaB]
def c8_1 : Relators 2 := ![wABBab, wABAAbaa]
def c8_2 : Relators 2 := ![wABBab, wBAAba]
def c8_3 : Relators 2 := ![wABBab, wBAABab]
def c8_4 : Relators 2 := ![wABBab, wAABa]
def c8_5 : Relators 2 := ![wABBab, wAB]
def c8_6 : Relators 2 := ![wABBab, wba]
def c8_7 : Relators 2 := ![wABBab, wBab]
def endpoint_8 : Relators 2 := ![wABBab, wa]

theorem reach_state_8 : Reachable state_8 endpoint_8 := by
  have h1 : Step state_8 c8_1 :=
    step_conj1 (a := wABBab) (b := wAAbaB) (c := wAB) (b' := wABAAbaa)
      (by simp only [wAAbaB, wAB, wABAAbaa, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h2 : Step c8_1 c8_2 :=
    step_conj1 (a := wABBab) (b := wABAAbaa) (c := wa) (b' := wBAAba)
      (by simp only [wABAAbaa, wBAAba, wa, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h3 : Step c8_2 c8_3 :=
    step_mul10 (a := wABBab) (b := wBAAba) (b' := wBAABab)
      (by simp only [wABBab, wBAABab, wBAAba, gx, gy, mul_assoc]; first | done | rfl | group | norm_num)
  have h4 : Step c8_3 c8_4 :=
    step_conj1 (a := wABBab) (b := wBAABab) (c := wb) (b' := wAABa)
      (by simp only [wAABa, wBAABab, wb, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h5 : Step c8_4 c8_5 :=
    step_conj1 (a := wABBab) (b := wAABa) (c := wa) (b' := wAB)
      (by simp only [wAABa, wAB, wa, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  have h6 : Step c8_5 c8_6 :=
    step_inv1 (a := wABBab) (b := wAB) (b' := wba)
      (by simp only [wAB, wABBab, wba, gx, gy, mul_inv_rev, inv_inv, mul_assoc]; first | done | rfl | group | norm_num)
  have h7 : Step c8_6 c8_7 :=
    step_mul10 (a := wABBab) (b := wba) (b' := wBab)
      (by simp only [wABBab, wBab, wba, gx, gy, mul_assoc]; first | done | rfl | group | norm_num)
  have h8 : Step c8_7 endpoint_8 :=
    step_conj1 (a := wABBab) (b := wBab) (c := wb) (b' := wa)
      (by simp only [wBab, wa, wb, gx, gy, mul_inv_rev, inv_inv]; first | done | rfl | group | norm_num)
  exact (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h1)
      (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h2)
            (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h3)
                  (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h4)
                        (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h5)
                              (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h6)
                                    (Relation.ReflTransGen.trans (Relation.ReflTransGen.single h7)
                                          (Relation.ReflTransGen.single h8))))))))

theorem abelianTerminal_8 : AbelianTerminal endpoint_8 := by
  refine ⟨(Equiv.swap (0 : Fin 2) 1), (Equiv.swap (0 : Fin 2) 1).bijective, ![false, true], ?_⟩
  intro i
  fin_cases i
  · simpa [endpoint_8] using expVec_wABBab
  · simpa [endpoint_8] using expVec_wa

theorem presentsTrivialGroup_8 : PresentsTrivialGroup endpoint_8 := by
  have hgen0 : PresentedGroup.mk (Set.range endpoint_8) (FreeGroup.of 0) = 1 := by
    have h := PresentedGroup.one_of_mem (rels := Set.range endpoint_8) (x := endpoint_8 1)
      (Set.mem_range_self 1)
    have hw : endpoint_8 1 = gx := rfl
    rw [hw] at h
    simp only [gx, gy, mk_mul_apply, mk_inv_apply, mul_one, one_mul, inv_one] at h
    exact h
  have hgen1 : PresentedGroup.mk (Set.range endpoint_8) (FreeGroup.of 1) = 1 := by
    have h := PresentedGroup.one_of_mem (rels := Set.range endpoint_8) (x := endpoint_8 0)
      (Set.mem_range_self 0)
    have hw : endpoint_8 0 = gx⁻¹ * gy⁻¹ * gy⁻¹ * gx * gy := rfl
    rw [hw] at h
    simp only [gx, gy, mk_mul_apply, mk_inv_apply, mul_one, one_mul, inv_one] at h
    rw [hgen0] at h
    simp only [mul_one, one_mul, inv_one] at h
    have h' : (PresentedGroup.mk (Set.range endpoint_8) (FreeGroup.of 1))⁻¹ = 1 := by
      rw [← h]
      group
    exact inv_eq_one.mp h'
  exact presentsTrivialGroup_of_mk_generators (R := endpoint_8) hgen0 hgen1

theorem length_state_8 : cyclicNielsenLength state_8 = 10 := by
  rw [cyclicNielsenLength_pair]
  change cycLen wABBab + cycLen wAAbaB = 10
  rw [cycLen_wABBab, cycLen_wAAbaB]

theorem length_endpoint_8 : cyclicNielsenLength endpoint_8 = 6 := by
  rw [cyclicNielsenLength_pair]
  change cycLen wABBab + cycLen wa = 6
  rw [cycLen_wABBab, cycLen_wa]

theorem descent_state_8 : DescentFrom state_8 := by
  refine ⟨endpoint_8, reach_state_8, abelianTerminal_8, presentsTrivialGroup_8, ?_⟩
  rw [length_endpoint_8, length_state_8]
  norm_num

/-! ## 7. Axiom record

Each listing must be a subset of `[propext, Classical.choice, Quot.sound]`. -/

#print axioms step_inv0
#print axioms step_inv1
#print axioms step_mul01
#print axioms step_mul10
#print axioms step_conj0
#print axioms step_conj1
#print axioms cycLen_mk_reduced
#print axioms cycLen_wA
#print axioms cycLen_wAABab
#print axioms cycLen_wAAbaB
#print axioms cycLen_wABBab
#print axioms cycLen_wABabb
#print axioms cycLen_wB
#print axioms cycLen_wBAbba
#print axioms cycLen_wBBAba
#print axioms cycLen_wa
#print axioms cycLen_waBAba
#print axioms cycLen_wbABab
#print axioms expVec_wA
#print axioms expVec_wAABab
#print axioms expVec_wABBab
#print axioms expVec_wABabb
#print axioms expVec_wB
#print axioms expVec_wBAbba
#print axioms expVec_wBBAba
#print axioms expVec_wa
#print axioms expVec_waBAba
#print axioms expVec_wbABab
#print axioms mk_mul_apply
#print axioms mk_inv_apply
#print axioms presentsTrivialGroup_of_mk_generators
#print axioms reach_state_1
#print axioms abelianTerminal_1
#print axioms presentsTrivialGroup_1
#print axioms length_state_1
#print axioms length_endpoint_1
#print axioms descent_state_1
#print axioms reach_state_2
#print axioms abelianTerminal_2
#print axioms presentsTrivialGroup_2
#print axioms length_state_2
#print axioms length_endpoint_2
#print axioms descent_state_2
#print axioms reach_state_3
#print axioms abelianTerminal_3
#print axioms presentsTrivialGroup_3
#print axioms length_state_3
#print axioms length_endpoint_3
#print axioms descent_state_3
#print axioms reach_state_4
#print axioms abelianTerminal_4
#print axioms presentsTrivialGroup_4
#print axioms length_state_4
#print axioms length_endpoint_4
#print axioms descent_state_4
#print axioms reach_state_5
#print axioms abelianTerminal_5
#print axioms presentsTrivialGroup_5
#print axioms length_state_5
#print axioms length_endpoint_5
#print axioms descent_state_5
#print axioms reach_state_6
#print axioms abelianTerminal_6
#print axioms presentsTrivialGroup_6
#print axioms length_state_6
#print axioms length_endpoint_6
#print axioms descent_state_6
#print axioms reach_state_7
#print axioms abelianTerminal_7
#print axioms presentsTrivialGroup_7
#print axioms length_state_7
#print axioms length_endpoint_7
#print axioms descent_state_7
#print axioms reach_state_8
#print axioms abelianTerminal_8
#print axioms presentsTrivialGroup_8
#print axioms length_state_8
#print axioms length_endpoint_8
#print axioms descent_state_8

end Measure10
end Nielsen
end AC
