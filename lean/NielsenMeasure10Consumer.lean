/-
# NielsenMeasure10Consumer — the `hten` input of the oddness bridge

`NielsenOddnessBridge.low_measure_descent_of_slice_and_ten` consumes one
measure-ten hypothesis, `hten`: every abelian-terminal, cyclically reduced,
non-signed-permutation state of cyclic Nielsen length ten (the pair `(5, 5)`)
admits one descent step.  This module supplies that hypothesis as
`measure10_input`.

## The reduction

Abelian terminality pins the exponent vector of each relator to `±genVec σ i`
for a bijection `σ`.  Each relator is cyclically reduced of cyclic length five,
so its word has length five, and its exponent vector is a signed basis vector.
The classification below enumerates the 1024 length-five words over two
generators and shows that every cyclically reduced one with a signed basis
exponent vector is a rotation — or, after inversion, a rotation — of one of
four canonical words:

* `LA` presents `wAABab`, exponent vector `-genVec 0`;
* `LB` presents `wAAbaB`, exponent vector `-genVec 0`;
* `LC` presents `wABabb`, exponent vector `+genVec 1`;
* `LD` presents `wABBab`, exponent vector `-genVec 1`.

A rotation is one official `Step.conj` by a prefix (via `rotate_step`); an
inversion is `Step.inv`.  Normalising the coordinate whose exponent vector is a
signed `genVec 0` to `LA` or `LB`, and the coordinate whose exponent vector is a
signed `genVec 1` to `LC` or `LD`, lands the state on one of the eight canonical
states `state_1` … `state_8` covered by `NielsenMeasure10Certificates`.  The
measure is the same at the start (both cyclic lengths are five) and at the
canonical state (both `length_state_k` are ten), so the certificate descent
transports.

## Trust

The classification is a kernel `decide` over the 1024 length-five words; the
exponent-vector link is proved by induction on the word (`expVec_mk_eq_countVec`).
No `sorry`, `admit`, `axiom`, or `native_decide` occurs in this file.  The axiom
record at the end reports the trusted base of `measure10_input`.
-/

import NielsenMeasure10Certificates
import NielsenSliceBridge
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace AC
namespace Nielsen
namespace Measure10Consumer

open SliceBridge RotationNormalForm
open Measure10

/-! ## 1. Exponent vector as a letter count -/

/-- The exponent vector contribution of one letter: `+genVec g` for the letter
`x`, `-genVec g` for `x⁻¹`. -/
def letterExp (x : Fin 2 × Bool) : Fin 2 → ℤ :=
  fun j => if j = x.1 then (if x.2 then 1 else -1) else 0

/-- The letter-count vector of a list.  This is computable, unlike `expVec`,
which is defined through `FreeGroup.lift`. -/
def countVec (L : List (Fin 2 × Bool)) : Fin 2 → ℤ :=
  (L.map letterExp).sum

theorem expVec_of (g : Fin 2) :
    Invariant.expVec (FreeGroup.of g) = Invariant.genVec g := by
  simp only [Invariant.expVec, Invariant.expHom, FreeGroup.lift_apply_of, Invariant.genVec]
  funext j
  rfl

theorem expVec_letter (g : Fin 2) (s : Bool) :
    Invariant.expVec (FreeGroup.mk [(g, s)]) = letterExp (g, s) := by
  cases s
  · rw [show FreeGroup.mk [(g, false)] = (FreeGroup.of g)⁻¹ by
      rw [show (FreeGroup.of g) = FreeGroup.mk [(g, true)] from rfl, FreeGroup.inv_mk]
      rfl]
    rw [Invariant.expVec_inv, expVec_of]
    funext j
    by_cases hj : j = g <;> simp [Invariant.genVec, letterExp, Pi.single_apply, hj]
  · rw [show FreeGroup.mk [(g, true)] = FreeGroup.of g from rfl, expVec_of]
    funext j
    by_cases hj : j = g <;> simp [Invariant.genVec, letterExp, Pi.single_apply, hj]

/-- The exponent vector of a free-group word is the letter-count vector of any
list that represents it. -/
theorem expVec_mk_eq_countVec (L : List (Fin 2 × Bool)) :
    Invariant.expVec (FreeGroup.mk L) = countVec L := by
  induction L with
  | nil =>
      show Invariant.expVec (1 : Word 2) = 0
      simp
  | cons a t ih =>
      have hsplit : FreeGroup.mk (a :: t) = FreeGroup.mk [a] * FreeGroup.mk t := by
        rw [FreeGroup.mul_mk, List.singleton_append]
      rw [hsplit, Invariant.expVec_mul, ih]
      obtain ⟨g, s⟩ := a
      simp only [countVec, List.map_cons, List.sum_cons]
      rw [expVec_letter g s]

/-! ## 2. The four canonical words and the four signed basis vectors -/

def LA : List (Fin 2 × Bool) := [(0,false),(0,false),(1,false),(0,true),(1,true)]
def LB : List (Fin 2 × Bool) := [(0,false),(0,false),(1,true),(0,true),(1,false)]
def LC : List (Fin 2 × Bool) := [(0,false),(1,false),(0,true),(1,true),(1,true)]
def LD : List (Fin 2 × Bool) := [(0,false),(1,false),(1,false),(0,true),(1,true)]

def posE0 : Fin 2 → ℤ := ![1,0]
def negE0 : Fin 2 → ℤ := ![-1,0]
def posE1 : Fin 2 → ℤ := ![0,1]
def negE1 : Fin 2 → ℤ := ![0,-1]

theorem mkW_LA : FreeGroup.mk LA = wAABab := rfl
theorem mkW_LB : FreeGroup.mk LB = wAAbaB := rfl
theorem mkW_LC : FreeGroup.mk LC = wABabb := rfl
theorem mkW_LD : FreeGroup.mk LD = wABBab := rfl

theorem genVec_zero : Invariant.genVec (0 : Fin 2) = posE0 := by
  funext j; fin_cases j <;> simp [Invariant.genVec, posE0]
theorem negGenVec_zero : -Invariant.genVec (0 : Fin 2) = negE0 := by
  funext j; fin_cases j <;> simp [Invariant.genVec, negE0]
theorem genVec_one : Invariant.genVec (1 : Fin 2) = posE1 := by
  funext j; fin_cases j <;> simp [Invariant.genVec, posE1]
theorem negGenVec_one : -Invariant.genVec (1 : Fin 2) = negE1 := by
  funext j; fin_cases j <;> simp [Invariant.genVec, negE1]

/-! ## 3. A rotation and an inversion are official steps -/

theorem reachable_rotate (S : Relators 2) (i : Fin 2) (L : List (Fin 2 × Bool)) (m : ℕ)
    (hL : S i = FreeGroup.mk L) :
    Reachable S (Function.update S i (FreeGroup.mk (L.rotate m))) := by
  obtain ⟨R', hstep, hR'i, hR'rest⟩ := rotate_step S i L m hL
  have hR' : R' = Function.update S i (FreeGroup.mk (L.rotate m)) := by
    funext k
    by_cases hk : k = i
    · subst hk; rw [hR'i, Function.update_self]
    · rw [hR'rest k hk, Function.update_of_ne hk]
  rw [hR'] at hstep
  exact Relation.ReflTransGen.single hstep

theorem reach_rot (S : Relators 2) (i : Fin 2) (L C : List (Fin 2 × Bool)) (m : ℕ)
    (hL : S i = FreeGroup.mk L) (hm : L.rotate m = C) :
    Reachable S (Function.update S i (FreeGroup.mk C)) := by
  have h := reachable_rotate S i L m hL
  rwa [hm] at h

theorem reach_inv_rot (S : Relators 2) (i : Fin 2) (L C : List (Fin 2 × Bool)) (m : ℕ)
    (hL : S i = FreeGroup.mk L) (hm : (FreeGroup.invRev L).rotate m = C) :
    Reachable S (Function.update S i (FreeGroup.mk C)) := by
  set S' : Relators 2 := Function.update S i ((S i)⁻¹) with hS'def
  have h1 : Reachable S S' := Relation.ReflTransGen.single (Step.inv S i)
  have hS'i : S' i = FreeGroup.mk (FreeGroup.invRev L) := by
    rw [hS'def, Function.update_self, hL, FreeGroup.inv_mk]
  have h2 : Reachable S' (Function.update S' i (FreeGroup.mk ((FreeGroup.invRev L).rotate m))) :=
    reachable_rotate S' i (FreeGroup.invRev L) m hS'i
  rw [hm] at h2
  have he : Function.update S' i (FreeGroup.mk C) = Function.update S i (FreeGroup.mk C) := by
    funext k
    by_cases hk : k = i
    · subst hk; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hk, Function.update_of_ne hk, hS'def, Function.update_of_ne hk]
  rw [he] at h2
  exact h1.trans h2

/-! ## 4. The finite classification -/

theorem exists_fn_of_length {L : List (Fin 2 × Bool)} (h : L.length = 5) :
    ∃ f : Fin 5 → Fin 2 × Bool, L = List.ofFn f :=
  ⟨fun i => L.get (Fin.cast h.symm i),
    (List.ofFn_get (l := L)).symm.trans (List.ofFn_congr h (List.get L))⟩

theorem c_negE0 :
    ∀ f : Fin 5 → Fin 2 × Bool,
      isCycRedB (List.ofFn f) = true → countVec (List.ofFn f) = negE0 →
      (∃ m : Fin 5, (List.ofFn f).rotate m.val = LA) ∨
      (∃ m : Fin 5, (List.ofFn f).rotate m.val = LB) := by decide

theorem c_posE0 :
    ∀ f : Fin 5 → Fin 2 × Bool,
      isCycRedB (List.ofFn f) = true → countVec (List.ofFn f) = posE0 →
      (∃ m : Fin 5, (FreeGroup.invRev (List.ofFn f)).rotate m.val = LA) ∨
      (∃ m : Fin 5, (FreeGroup.invRev (List.ofFn f)).rotate m.val = LB) := by decide

theorem c_posE1 :
    ∀ f : Fin 5 → Fin 2 × Bool,
      isCycRedB (List.ofFn f) = true → countVec (List.ofFn f) = posE1 →
      (∃ m : Fin 5, (List.ofFn f).rotate m.val = LC) ∨
      (∃ m : Fin 5, (FreeGroup.invRev (List.ofFn f)).rotate m.val = LD) := by decide

theorem c_negE1 :
    ∀ f : Fin 5 → Fin 2 × Bool,
      isCycRedB (List.ofFn f) = true → countVec (List.ofFn f) = negE1 →
      (∃ m : Fin 5, (List.ofFn f).rotate m.val = LD) ∨
      (∃ m : Fin 5, (FreeGroup.invRev (List.ofFn f)).rotate m.val = LC) := by decide

theorem cl_negE0 (L : List (Fin 2 × Bool)) (h : L.length = 5)
    (hcyc : FreeGroup.IsCyclicallyReduced L) (hv : countVec L = negE0) :
    (∃ m : Fin 5, L.rotate m.val = LA) ∨ (∃ m : Fin 5, L.rotate m.val = LB) := by
  obtain ⟨f, rfl⟩ := exists_fn_of_length h
  exact c_negE0 f ((isCycRedB_iff _).mpr hcyc) hv

theorem cl_posE0 (L : List (Fin 2 × Bool)) (h : L.length = 5)
    (hcyc : FreeGroup.IsCyclicallyReduced L) (hv : countVec L = posE0) :
    (∃ m : Fin 5, (FreeGroup.invRev L).rotate m.val = LA) ∨
    (∃ m : Fin 5, (FreeGroup.invRev L).rotate m.val = LB) := by
  obtain ⟨f, rfl⟩ := exists_fn_of_length h
  exact c_posE0 f ((isCycRedB_iff _).mpr hcyc) hv

theorem cl_posE1 (L : List (Fin 2 × Bool)) (h : L.length = 5)
    (hcyc : FreeGroup.IsCyclicallyReduced L) (hv : countVec L = posE1) :
    (∃ m : Fin 5, L.rotate m.val = LC) ∨
    (∃ m : Fin 5, (FreeGroup.invRev L).rotate m.val = LD) := by
  obtain ⟨f, rfl⟩ := exists_fn_of_length h
  exact c_posE1 f ((isCycRedB_iff _).mpr hcyc) hv

theorem cl_negE1 (L : List (Fin 2 × Bool)) (h : L.length = 5)
    (hcyc : FreeGroup.IsCyclicallyReduced L) (hv : countVec L = negE1) :
    (∃ m : Fin 5, L.rotate m.val = LD) ∨
    (∃ m : Fin 5, (FreeGroup.invRev L).rotate m.val = LC) := by
  obtain ⟨f, rfl⟩ := exists_fn_of_length h
  exact c_negE1 f ((isCycRedB_iff _).mpr hcyc) hv

/-! ## 5. Coordinate normalisation -/

/-- A coordinate whose exponent vector is a signed `genVec 0` reaches a state
whose coordinate is `wAABab` or `wAAbaB`, everything else unchanged. -/
theorem norm_e0 (R : Relators 2) (i : Fin 2)
    (hcyc : FreeGroup.IsCyclicallyReduced ((R i).toWord))
    (hlen : (R i).toWord.length = 5) (v : Fin 2 → ℤ)
    (hv : countVec ((R i).toWord) = v) (h : v = posE0 ∨ v = negE0) :
    Reachable R (Function.update R i (FreeGroup.mk LA)) ∨
    Reachable R (Function.update R i (FreeGroup.mk LB)) := by
  rcases h with rfl | rfl
  · rcases cl_posE0 ((R i).toWord) hlen hcyc hv with ⟨m, hm⟩ | ⟨m, hm⟩
    · left; exact reach_inv_rot R i _ LA m (FreeGroup.mk_toWord.symm) hm
    · right; exact reach_inv_rot R i _ LB m (FreeGroup.mk_toWord.symm) hm
  · rcases cl_negE0 ((R i).toWord) hlen hcyc hv with ⟨m, hm⟩ | ⟨m, hm⟩
    · left; exact reach_rot R i _ LA m (FreeGroup.mk_toWord.symm) hm
    · right; exact reach_rot R i _ LB m (FreeGroup.mk_toWord.symm) hm

/-- A coordinate whose exponent vector is a signed `genVec 1` reaches a state
whose coordinate is `wABabb` or `wABBab`, everything else unchanged. -/
theorem norm_e1 (R : Relators 2) (i : Fin 2)
    (hcyc : FreeGroup.IsCyclicallyReduced ((R i).toWord))
    (hlen : (R i).toWord.length = 5) (v : Fin 2 → ℤ)
    (hv : countVec ((R i).toWord) = v) (h : v = posE1 ∨ v = negE1) :
    Reachable R (Function.update R i (FreeGroup.mk LC)) ∨
    Reachable R (Function.update R i (FreeGroup.mk LD)) := by
  rcases h with rfl | rfl
  · rcases cl_posE1 ((R i).toWord) hlen hcyc hv with ⟨m, hm⟩ | ⟨m, hm⟩
    · left; exact reach_rot R i _ LC m (FreeGroup.mk_toWord.symm) hm
    · right; exact reach_inv_rot R i _ LD m (FreeGroup.mk_toWord.symm) hm
  · rcases cl_negE1 ((R i).toWord) hlen hcyc hv with ⟨m, hm⟩ | ⟨m, hm⟩
    · right; exact reach_rot R i _ LD m (FreeGroup.mk_toWord.symm) hm
    · left; exact reach_inv_rot R i _ LC m (FreeGroup.mk_toWord.symm) hm

/-! ## 6. From the eight states to a descent -/

theorem update_pair (S : Relators 2) (a b : Word 2) :
    Function.update (Function.update S 0 a) 1 b = ![a, b] := by
  funext k
  fin_cases k <;> simp [Function.update_self, Function.update_of_ne]

theorem descent_via (S R0 : Relators 2) (hR : Reachable S R0) (hD : DescentFrom R0)
    (hS : cyclicNielsenLength S = 10) (h0 : cyclicNielsenLength R0 = 10) :
    DescentFrom S := by
  obtain ⟨U, hU, hAbU, hPU, hlt⟩ := hD
  exact ⟨U, hR.trans hU, hAbU, hPU, by rw [hS, ← h0]; exact hlt⟩

theorem finish1 (S : Relators 2) (hR : Reachable S ![FreeGroup.mk LA, FreeGroup.mk LC])
    (hlen : cyclicNielsenLength S = 10) : DescentFrom S := by
  have h : ![FreeGroup.mk LA, FreeGroup.mk LC] = state_1 := rfl
  rw [h] at hR
  exact descent_via S state_1 hR descent_state_1 hlen length_state_1

theorem finish2 (S : Relators 2) (hR : Reachable S ![FreeGroup.mk LA, FreeGroup.mk LD])
    (hlen : cyclicNielsenLength S = 10) : DescentFrom S := by
  have h : ![FreeGroup.mk LA, FreeGroup.mk LD] = state_2 := rfl
  rw [h] at hR
  exact descent_via S state_2 hR descent_state_2 hlen length_state_2

theorem finish3 (S : Relators 2) (hR : Reachable S ![FreeGroup.mk LB, FreeGroup.mk LC])
    (hlen : cyclicNielsenLength S = 10) : DescentFrom S := by
  have h : ![FreeGroup.mk LB, FreeGroup.mk LC] = state_3 := rfl
  rw [h] at hR
  exact descent_via S state_3 hR descent_state_3 hlen length_state_3

theorem finish4 (S : Relators 2) (hR : Reachable S ![FreeGroup.mk LB, FreeGroup.mk LD])
    (hlen : cyclicNielsenLength S = 10) : DescentFrom S := by
  have h : ![FreeGroup.mk LB, FreeGroup.mk LD] = state_4 := rfl
  rw [h] at hR
  exact descent_via S state_4 hR descent_state_4 hlen length_state_4

theorem finish5 (S : Relators 2) (hR : Reachable S ![FreeGroup.mk LC, FreeGroup.mk LA])
    (hlen : cyclicNielsenLength S = 10) : DescentFrom S := by
  have h : ![FreeGroup.mk LC, FreeGroup.mk LA] = state_5 := rfl
  rw [h] at hR
  exact descent_via S state_5 hR descent_state_5 hlen length_state_5

theorem finish6 (S : Relators 2) (hR : Reachable S ![FreeGroup.mk LC, FreeGroup.mk LB])
    (hlen : cyclicNielsenLength S = 10) : DescentFrom S := by
  have h : ![FreeGroup.mk LC, FreeGroup.mk LB] = state_6 := rfl
  rw [h] at hR
  exact descent_via S state_6 hR descent_state_6 hlen length_state_6

theorem finish7 (S : Relators 2) (hR : Reachable S ![FreeGroup.mk LD, FreeGroup.mk LA])
    (hlen : cyclicNielsenLength S = 10) : DescentFrom S := by
  have h : ![FreeGroup.mk LD, FreeGroup.mk LA] = state_7 := rfl
  rw [h] at hR
  exact descent_via S state_7 hR descent_state_7 hlen length_state_7

theorem finish8 (S : Relators 2) (hR : Reachable S ![FreeGroup.mk LD, FreeGroup.mk LB])
    (hlen : cyclicNielsenLength S = 10) : DescentFrom S := by
  have h : ![FreeGroup.mk LD, FreeGroup.mk LB] = state_8 := rfl
  rw [h] at hR
  exact descent_via S state_8 hR descent_state_8 hlen length_state_8

theorem fin2_eq_one {x : Fin 2} (h : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl h
  · rfl

theorem fin2_eq_zero {x : Fin 2} (h : x ≠ 1) : x = 0 := by
  fin_cases x
  · rfl
  · exact absurd rfl h

/-! ## 7. The `hten` input -/

/-- **The measure-ten input.** Every abelian-terminal, cyclically reduced,
non-signed-permutation state with both cyclic lengths five admits one descent
step. This is exactly the `hten` hypothesis of
`NielsenOddnessBridge.low_measure_descent_of_slice_and_ten`. -/
theorem measure10_input :
    ∀ (S : Relators 2), AbelianTerminal S → PresentsTrivialGroup S →
      (∀ i : Fin 2, FreeGroup.IsCyclicallyReduced (S i).toWord) →
      ¬ ProofAttempt.IsSignedPermutation S →
      5 ≤ (S 0).toWord.length → 5 ≤ (S 1).toWord.length →
      cycLen (S 0) = 5 → cycLen (S 1) = 5 → DescentFrom S := by
  intro S hAb _hP hCyc _hPerm _h0 _h1 hc0 hc1
  obtain ⟨σ, hσ, ε, hε⟩ := hAb
  -- The measure of `S` is ten.
  have hSlen : cyclicNielsenLength S = 10 := by
    rw [cyclicNielsenLength_pair, hc0, hc1]
  -- The word lengths are five.
  have hLlen0 : (S 0).toWord.length = 5 := by
    rw [← cycLen_eq_toWord_length 0 (hCyc 0)]; exact hc0
  have hLlen1 : (S 1).toWord.length = 5 := by
    rw [← cycLen_eq_toWord_length 1 (hCyc 1)]; exact hc1
  -- The letter-count vectors, before reducing the sign.
  have hv0g : countVec ((S 0).toWord) =
      (if ε 0 then Invariant.genVec (σ 0) else -Invariant.genVec (σ 0)) := by
    rw [← expVec_mk_eq_countVec ((S 0).toWord), FreeGroup.mk_toWord]
    exact hε 0
  have hv1g : countVec ((S 1).toWord) =
      (if ε 1 then Invariant.genVec (σ 1) else -Invariant.genVec (σ 1)) := by
    rw [← expVec_mk_eq_countVec ((S 1).toWord), FreeGroup.mk_toWord]
    exact hε 1
  -- `σ 0` is zero or one.
  have hσ0cases : σ 0 = 0 ∨ σ 0 = 1 := by
    have hlt := (σ 0).isLt
    rcases (by omega : (σ 0).val = 0 ∨ (σ 0).val = 1) with h | h
    · left; apply Fin.ext; simpa using h
    · right; apply Fin.ext; simpa using h
  rcases hσ0cases with hσ0 | hσ0
  · -- Case `σ 0 = 0`: the zeroth coordinate carries `genVec 0`, the first `genVec 1`.
    have hσ1 : σ 1 = 1 := by
      have hne : σ 1 ≠ 0 := by
        intro h
        have he : σ 1 = σ 0 := by rw [h, hσ0]
        exact (by decide : (1 : Fin 2) ≠ 0) (hσ.1 he)
      exact fin2_eq_one hne
    have hv0 : countVec ((S 0).toWord) = (if ε 0 then posE0 else negE0) := by
      rw [hv0g, hσ0]
      cases ε 0
      · simp [negGenVec_zero]
      · simp [genVec_zero]
    have hv1 : countVec ((S 1).toWord) = (if ε 1 then posE1 else negE1) := by
      rw [hv1g, hσ1]
      cases ε 1
      · simp [negGenVec_one]
      · simp [genVec_one]
    have hs0 : (if ε 0 then posE0 else negE0) = posE0 ∨
        (if ε 0 then posE0 else negE0) = negE0 := by cases ε 0 <;> simp
    have hs1 : (if ε 1 then posE1 else negE1) = posE1 ∨
        (if ε 1 then posE1 else negE1) = negE1 := by cases ε 1 <;> simp
    rcases norm_e0 S 0 (hCyc 0) hLlen0 _ hv0 hs0 with hA | hA
    · -- zeroth coordinate to `wAABab`
      have hA1 : (Function.update S 0 (FreeGroup.mk LA)) 1 = S 1 := by
        rw [Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
      have hcyc1 : FreeGroup.IsCyclicallyReduced (((Function.update S 0 (FreeGroup.mk LA)) 1).toWord) := by
        rw [hA1]; exact hCyc 1
      have hlen1 : (((Function.update S 0 (FreeGroup.mk LA)) 1).toWord).length = 5 := by
        rw [hA1]; exact hLlen1
      have hv1' : countVec (((Function.update S 0 (FreeGroup.mk LA)) 1).toWord) =
          (if ε 1 then posE1 else negE1) := by rw [hA1]; exact hv1
      rcases norm_e1 (Function.update S 0 (FreeGroup.mk LA)) 1 hcyc1 hlen1 _ hv1' hs1
        with hB | hB
      · exact finish1 S (by
          have hcomb := hA.trans hB
          rw [update_pair] at hcomb
          exact hcomb) hSlen
      · exact finish2 S (by
          have hcomb := hA.trans hB
          rw [update_pair] at hcomb
          exact hcomb) hSlen
    · -- zeroth coordinate to `wAAbaB`
      have hA1 : (Function.update S 0 (FreeGroup.mk LB)) 1 = S 1 := by
        rw [Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
      have hcyc1 : FreeGroup.IsCyclicallyReduced (((Function.update S 0 (FreeGroup.mk LB)) 1).toWord) := by
        rw [hA1]; exact hCyc 1
      have hlen1 : (((Function.update S 0 (FreeGroup.mk LB)) 1).toWord).length = 5 := by
        rw [hA1]; exact hLlen1
      have hv1' : countVec (((Function.update S 0 (FreeGroup.mk LB)) 1).toWord) =
          (if ε 1 then posE1 else negE1) := by rw [hA1]; exact hv1
      rcases norm_e1 (Function.update S 0 (FreeGroup.mk LB)) 1 hcyc1 hlen1 _ hv1' hs1
        with hB | hB
      · exact finish3 S (by
          have hcomb := hA.trans hB
          rw [update_pair] at hcomb
          exact hcomb) hSlen
      · exact finish4 S (by
          have hcomb := hA.trans hB
          rw [update_pair] at hcomb
          exact hcomb) hSlen
  · -- Case `σ 0 = 1`: the zeroth coordinate carries `genVec 1`, the first `genVec 0`.
    have hσ1 : σ 1 = 0 := by
      have hne : σ 1 ≠ 1 := by
        intro h
        have he : σ 1 = σ 0 := by rw [h, hσ0]
        exact (by decide : (1 : Fin 2) ≠ 0) (hσ.1 he)
      exact fin2_eq_zero hne
    have hv0 : countVec ((S 0).toWord) = (if ε 0 then posE1 else negE1) := by
      rw [hv0g, hσ0]
      cases ε 0
      · simp [negGenVec_one]
      · simp [genVec_one]
    have hv1 : countVec ((S 1).toWord) = (if ε 1 then posE0 else negE0) := by
      rw [hv1g, hσ1]
      cases ε 1
      · simp [negGenVec_zero]
      · simp [genVec_zero]
    have hs0 : (if ε 0 then posE1 else negE1) = posE1 ∨
        (if ε 0 then posE1 else negE1) = negE1 := by cases ε 0 <;> simp
    have hs1 : (if ε 1 then posE0 else negE0) = posE0 ∨
        (if ε 1 then posE0 else negE0) = negE0 := by cases ε 1 <;> simp
    rcases norm_e1 S 0 (hCyc 0) hLlen0 _ hv0 hs0 with hA | hA
    · -- zeroth coordinate to `wABabb`
      have hA1 : (Function.update S 0 (FreeGroup.mk LC)) 1 = S 1 := by
        rw [Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
      have hcyc1 : FreeGroup.IsCyclicallyReduced (((Function.update S 0 (FreeGroup.mk LC)) 1).toWord) := by
        rw [hA1]; exact hCyc 1
      have hlen1 : (((Function.update S 0 (FreeGroup.mk LC)) 1).toWord).length = 5 := by
        rw [hA1]; exact hLlen1
      have hv1' : countVec (((Function.update S 0 (FreeGroup.mk LC)) 1).toWord) =
          (if ε 1 then posE0 else negE0) := by rw [hA1]; exact hv1
      rcases norm_e0 (Function.update S 0 (FreeGroup.mk LC)) 1 hcyc1 hlen1 _ hv1' hs1
        with hB | hB
      · exact finish5 S (by
          have hcomb := hA.trans hB
          rw [update_pair] at hcomb
          exact hcomb) hSlen
      · exact finish6 S (by
          have hcomb := hA.trans hB
          rw [update_pair] at hcomb
          exact hcomb) hSlen
    · -- zeroth coordinate to `wABBab`
      have hA1 : (Function.update S 0 (FreeGroup.mk LD)) 1 = S 1 := by
        rw [Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
      have hcyc1 : FreeGroup.IsCyclicallyReduced (((Function.update S 0 (FreeGroup.mk LD)) 1).toWord) := by
        rw [hA1]; exact hCyc 1
      have hlen1 : (((Function.update S 0 (FreeGroup.mk LD)) 1).toWord).length = 5 := by
        rw [hA1]; exact hLlen1
      have hv1' : countVec (((Function.update S 0 (FreeGroup.mk LD)) 1).toWord) =
          (if ε 1 then posE0 else negE0) := by rw [hA1]; exact hv1
      rcases norm_e0 (Function.update S 0 (FreeGroup.mk LD)) 1 hcyc1 hlen1 _ hv1' hs1
        with hB | hB
      · exact finish7 S (by
          have hcomb := hA.trans hB
          rw [update_pair] at hcomb
          exact hcomb) hSlen
      · exact finish8 S (by
          have hcomb := hA.trans hB
          rw [update_pair] at hcomb
          exact hcomb) hSlen

/-! ## 8. Axiom record -/

#print axioms measure10_input

end Measure10Consumer
end Nielsen
end AC
