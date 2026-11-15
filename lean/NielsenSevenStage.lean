module

/-
# NielsenSevenStage — the concrete descent of the (5,7) witness

`NielsenRotationNormalForm.lean:418` states the base-orientation seven-stage
witness descent as the proposition `SevenStageWitnessDescent`:

    ∃ T : Relators 2, Reachable witnessState T ∧ AbelianTerminal T ∧
      cyclicNielsenLength T < cyclicNielsenLength witnessState

and leaves it as a `def`, because the session source that was to supply the
seven-stage list, `EXPLORATION/AcNielsen.lean`, is outside this repository.
The names the session source uses for the stage machinery — `NStage`,
`runStages`, and the concrete seven-stage list — have no declaration in this
tree; a search of `lean/*.lean` for them returns only prose.

This module proves the proposition without that machinery.  It exhibits an
explicit path of 25 official Andrews–Curtis `Step`s from the witness to the
state `(y⁻¹, y⁻¹ x y)`, whose cyclic Nielsen length is 2, and which is abelian
terminal because its exponent vectors are `-genVec 1` and `genVec 0`.  The path
was found by search over the official moves and is checked here move by move;
every intermediate state is written out and every move equality is discharged
by the group normaliser.

The witness lists in `NielsenRotationNormalForm.lean:235-241` read, under the
Mathlib convention that `(a, true)` is the positive letter and `(a, false)` its
inverse (`Mathlib/GroupTheory/FreeGroup/Reduce.lean:210`),

    r7Shape = x⁻¹ x⁻¹ y⁻¹ x x x y,      s5Shape = x⁻¹ y⁻¹ x y y.

The intermediate states below are the images of the states of the search path
under the automorphism `x ↦ x⁻¹`, `y ↦ y⁻¹`.  That automorphism preserves each
of the three official move forms, so it carries the path to the witness as the
lists actually denote it.

No `sorry`, `admit`, `axiom`, or `native_decide` is used.  The axiom record at
the end reports the trusted base of the main theorem.
-/

public import AcNielsenDefs
public import AcProof
public import NielsenRotationNormalForm
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace AC
namespace Nielsen
namespace SevenStage

open RotationNormalForm

/-! ## 1. The two generators of the rank-two free group -/

/-- The first generator. -/
abbrev gx : Word 2 := FreeGroup.of 0

/-- The second generator. -/
abbrev gy : Word 2 := FreeGroup.of 1

/-! ## 2. The cyclic length of the witness -/

/-- The cyclic length of a word presented by a cyclically reduced list is the
length of the list. -/
theorem cycLen_mk_of_isCyclicallyReduced {n : ℕ} {L : List (Fin n × Bool)}
    (h : FreeGroup.IsCyclicallyReduced L) :
    cycLen (FreeGroup.mk L) = L.length := by
  unfold cycLen
  rw [FreeGroup.toWord_mk, FreeGroup.isReduced_iff_reduce_eq.mp h.isReduced,
    reduceCyclically_eq_self h]

/-- The witness has cyclic Nielsen length `7 + 5 = 12`. -/
theorem cyclicNielsenLength_witnessState :
    cyclicNielsenLength witnessState = 12 := by
  rw [cyclicNielsenLength_pair, witnessState_zero, witnessState_one,
    cycLen_mk_of_isCyclicallyReduced r7Shape_isCyclicallyReduced,
    cycLen_mk_of_isCyclicallyReduced s5Shape_isCyclicallyReduced,
    r7Shape_length, s5Shape_length]

/-! ## 3. One-step reachability lemmas -/

/-- Conjugating the zeroth relator is one official move. -/
theorem reach_conj0 {a b c w : Word 2} (h : w * a * w⁻¹ = c) :
    Reachable ![a, b] ![c, b] := by
  have hs : Step ![a, b] (Function.update ![a, b] 0 (w * ![a, b] 0 * w⁻¹)) :=
    Step.conj ![a, b] 0 w
  have he : Function.update ![a, b] 0 (w * ![a, b] 0 * w⁻¹) = ![c, b] := by
    funext i
    fin_cases i <;> simp [h]
  rw [he] at hs
  exact Relation.ReflTransGen.single hs

/-- Conjugating the first relator is one official move. -/
theorem reach_conj1 {a b c w : Word 2} (h : w * b * w⁻¹ = c) :
    Reachable ![a, b] ![a, c] := by
  have hs : Step ![a, b] (Function.update ![a, b] 1 (w * ![a, b] 1 * w⁻¹)) :=
    Step.conj ![a, b] 1 w
  have he : Function.update ![a, b] 1 (w * ![a, b] 1 * w⁻¹) = ![a, c] := by
    funext i
    fin_cases i <;> simp [h]
  rw [he] at hs
  exact Relation.ReflTransGen.single hs

/-- Inverting the zeroth relator is one official move. -/
theorem reach_inv0 {a b : Word 2} : Reachable ![a, b] ![a⁻¹, b] := by
  have hs : Step ![a, b] (Function.update ![a, b] 0 (![a, b] 0)⁻¹) :=
    Step.inv ![a, b] 0
  have he : Function.update ![a, b] 0 (![a, b] 0)⁻¹ = ![a⁻¹, b] := by
    funext i
    fin_cases i <;> simp
  rw [he] at hs
  exact Relation.ReflTransGen.single hs

/-- Inverting the first relator is one official move. -/
theorem reach_inv1 {a b : Word 2} : Reachable ![a, b] ![a, b⁻¹] := by
  have hs : Step ![a, b] (Function.update ![a, b] 1 (![a, b] 1)⁻¹) :=
    Step.inv ![a, b] 1
  have he : Function.update ![a, b] 1 (![a, b] 1)⁻¹ = ![a, b⁻¹] := by
    funext i
    fin_cases i <;> simp
  rw [he] at hs
  exact Relation.ReflTransGen.single hs

/-- Right-multiplying the zeroth relator by the first is one official move. -/
theorem reach_mul01 {a b c : Word 2} (h : a * b = c) :
    Reachable ![a, b] ![c, b] := by
  have hs : Step ![a, b] (Function.update ![a, b] 0 (![a, b] 0 * ![a, b] 1)) :=
    Step.mulRight ![a, b] 0 1 (by decide)
  have he : Function.update ![a, b] 0 (![a, b] 0 * ![a, b] 1) = ![c, b] := by
    funext i
    fin_cases i <;> simp [h]
  rw [he] at hs
  exact Relation.ReflTransGen.single hs

/-- Right-multiplying the first relator by the zeroth is one official move. -/
theorem reach_mul10 {a b c : Word 2} (h : b * a = c) :
    Reachable ![a, b] ![a, c] := by
  have hs : Step ![a, b] (Function.update ![a, b] 1 (![a, b] 1 * ![a, b] 0)) :=
    Step.mulRight ![a, b] 1 0 (by decide)
  have he : Function.update ![a, b] 1 (![a, b] 1 * ![a, b] 0) = ![a, c] := by
    funext i
    fin_cases i <;> simp [h]
  rw [he] at hs
  exact Relation.ReflTransGen.single hs

/-- Right-multiply the zeroth relator by the inverse of the first.  The inverse
is taken in one move, the product in one move, and the first relator is
restored in one move. -/
theorem reach_mul01_inv {a b c : Word 2} (h : a * b⁻¹ = c) :
    Reachable ![a, b] ![c, b] := by
  have h1 : Reachable ![a, b] ![a, b⁻¹] := reach_inv1
  have h2 : Reachable ![a, b⁻¹] ![c, b⁻¹] :=
    reach_mul01 (a := a) (b := b⁻¹) (c := c) (by simpa using h)
  have h3 : Reachable ![c, b⁻¹] ![c, b] := by
    simpa using reach_inv1 (a := c) (b := b⁻¹)
  exact Relation.ReflTransGen.trans h1 (Relation.ReflTransGen.trans h2 h3)

/-- Right-multiply the first relator by the inverse of the zeroth.  Symmetric
to `reach_mul01_inv`. -/
theorem reach_mul10_inv {a b c : Word 2} (h : b * a⁻¹ = c) :
    Reachable ![a, b] ![a, c] := by
  have h1 : Reachable ![a, b] ![a⁻¹, b] := reach_inv0
  have h2 : Reachable ![a⁻¹, b] ![a⁻¹, c] :=
    reach_mul10 (a := a⁻¹) (b := b) (c := c) h
  have h3 : Reachable ![a⁻¹, c] ![a, c] := by
    simpa using reach_inv0 (a := a⁻¹) (b := c)
  exact Relation.ReflTransGen.trans h1 (Relation.ReflTransGen.trans h2 h3)

/-! ## 4. The fourteen states of the explicit descent

The words are read with `(a, true)` positive.  State `v0` is the witness; state
`v13` is `(y⁻¹, y⁻¹ x y)`. -/

/-- The witness orientation. -/
def v0 : Relators 2 :=
  ![gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gx * gx * gy, gx⁻¹ * gy⁻¹ * gx * gy * gy]

/-- After conjugating the zeroth relator by `x x y`. -/
def v1 : Relators 2 :=
  ![gx * gx * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx, gx⁻¹ * gy⁻¹ * gx * gy * gy]

/-- After conjugating the first relator by `y y`. -/
def v2 : Relators 2 :=
  ![gx * gx * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx, gy * gy * gx⁻¹ * gy⁻¹ * gx]

/-- After multiplying the zeroth relator by the inverse of the first. -/
def v3 : Relators 2 :=
  ![gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹, gy * gy * gx⁻¹ * gy⁻¹ * gx]

/-- After conjugating the zeroth relator by `x⁻¹ y⁻¹`. -/
def v4 : Relators 2 :=
  ![gx⁻¹ * gy⁻¹ * gx * gx * gy * gx⁻¹ * gy⁻¹ * gx, gy * gy * gx⁻¹ * gy⁻¹ * gx]

/-- After multiplying the zeroth relator by the inverse of the first. -/
def v5 : Relators 2 :=
  ![gx⁻¹ * gy⁻¹ * gx * gx * gy⁻¹, gy * gy * gx⁻¹ * gy⁻¹ * gx]

/-- After conjugating the zeroth relator by `x y⁻¹`. -/
def v6 : Relators 2 :=
  ![gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx, gy * gy * gx⁻¹ * gy⁻¹ * gx]

/-- After multiplying the zeroth relator by the inverse of the first. -/
def v7 : Relators 2 :=
  ![gx * gy⁻¹ * gy⁻¹ * gy⁻¹, gy * gy * gx⁻¹ * gy⁻¹ * gx]

/-- After conjugating the first relator by `y⁻¹ x`. -/
def v8 : Relators 2 :=
  ![gx * gy⁻¹ * gy⁻¹ * gy⁻¹, gy⁻¹ * gx * gy * gy * gx⁻¹]

/-- After multiplying the first relator by the zeroth. -/
def v9 : Relators 2 :=
  ![gx * gy⁻¹ * gy⁻¹ * gy⁻¹, gy⁻¹ * gx * gy⁻¹]

/-- After conjugating the zeroth relator by `y⁻¹ y⁻¹`. -/
def v10 : Relators 2 :=
  ![gy⁻¹ * gy⁻¹ * gx * gy⁻¹, gy⁻¹ * gx * gy⁻¹]

/-- After multiplying the zeroth relator by the inverse of the first. -/
def v11 : Relators 2 :=
  ![gy⁻¹, gy⁻¹ * gx * gy⁻¹]

/-- After multiplying the first relator by the inverse of the zeroth. -/
def v12 : Relators 2 :=
  ![gy⁻¹, gy⁻¹ * gx]

/-- The abelian-terminal endpoint `(y⁻¹, y⁻¹ x y)`. -/
def v13 : Relators 2 :=
  ![gy⁻¹, gy⁻¹ * gx * gy]

/-- The witness is the initial state of the chain. -/
theorem v0_eq_witnessState : v0 = witnessState := by
  funext i
  fin_cases i <;> rfl

/-! ## 5. The chain of official moves -/

/-- The explicit 25-step path from the witness to `v13`. -/
theorem reachable_v0_v13 : Reachable v0 v13 := by
  have s01 : Reachable v0 v1 := by
    have h : (gx * gx * gy) * (gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gx * gx * gy) *
        (gx * gx * gy)⁻¹ = gx * gx * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx := by
      group
    simpa [v0, v1] using
      reach_conj0 (a := gx⁻¹ * gx⁻¹ * gy⁻¹ * gx * gx * gx * gy)
        (b := gx⁻¹ * gy⁻¹ * gx * gy * gy)
        (c := gx * gx * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx)
        (w := gx * gx * gy) h
  have s12 : Reachable v1 v2 := by
    have h : (gy * gy) * (gx⁻¹ * gy⁻¹ * gx * gy * gy) * (gy * gy)⁻¹ =
        gy * gy * gx⁻¹ * gy⁻¹ * gx := by
      group
    simpa [v1, v2] using
      reach_conj1 (a := gx * gx * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx)
        (b := gx⁻¹ * gy⁻¹ * gx * gy * gy)
        (c := gy * gy * gx⁻¹ * gy⁻¹ * gx)
        (w := gy * gy) h
  have s23 : Reachable v2 v3 := by
    have h : (gx * gx * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx) *
        (gy * gy * gx⁻¹ * gy⁻¹ * gx)⁻¹ = gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹ := by
      group
    simpa [v2, v3] using
      reach_mul01_inv (a := gx * gx * gy * gx⁻¹ * gx⁻¹ * gy⁻¹ * gx)
        (b := gy * gy * gx⁻¹ * gy⁻¹ * gx)
        (c := gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹) h
  have s34 : Reachable v3 v4 := by
    have h : (gx⁻¹ * gy⁻¹) * (gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹) *
        (gx⁻¹ * gy⁻¹)⁻¹ = gx⁻¹ * gy⁻¹ * gx * gx * gy * gx⁻¹ * gy⁻¹ * gx := by
      group
    simpa [v3, v4] using
      reach_conj0 (a := gx * gx * gy * gx⁻¹ * gy⁻¹ * gy⁻¹)
        (b := gy * gy * gx⁻¹ * gy⁻¹ * gx)
        (c := gx⁻¹ * gy⁻¹ * gx * gx * gy * gx⁻¹ * gy⁻¹ * gx)
        (w := gx⁻¹ * gy⁻¹) h
  have s45 : Reachable v4 v5 := by
    have h : (gx⁻¹ * gy⁻¹ * gx * gx * gy * gx⁻¹ * gy⁻¹ * gx) *
        (gy * gy * gx⁻¹ * gy⁻¹ * gx)⁻¹ = gx⁻¹ * gy⁻¹ * gx * gx * gy⁻¹ := by
      group
    simpa [v4, v5] using
      reach_mul01_inv (a := gx⁻¹ * gy⁻¹ * gx * gx * gy * gx⁻¹ * gy⁻¹ * gx)
        (b := gy * gy * gx⁻¹ * gy⁻¹ * gx)
        (c := gx⁻¹ * gy⁻¹ * gx * gx * gy⁻¹) h
  have s56 : Reachable v5 v6 := by
    have h : (gx * gy⁻¹) * (gx⁻¹ * gy⁻¹ * gx * gx * gy⁻¹) * (gx * gy⁻¹)⁻¹ =
        gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx := by
      group
    simpa [v5, v6] using
      reach_conj0 (a := gx⁻¹ * gy⁻¹ * gx * gx * gy⁻¹)
        (b := gy * gy * gx⁻¹ * gy⁻¹ * gx)
        (c := gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx)
        (w := gx * gy⁻¹) h
  have s67 : Reachable v6 v7 := by
    have h : (gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx) *
        (gy * gy * gx⁻¹ * gy⁻¹ * gx)⁻¹ = gx * gy⁻¹ * gy⁻¹ * gy⁻¹ := by
      group
    simpa [v6, v7] using
      reach_mul01_inv (a := gx * gy⁻¹ * gx⁻¹ * gy⁻¹ * gx)
        (b := gy * gy * gx⁻¹ * gy⁻¹ * gx)
        (c := gx * gy⁻¹ * gy⁻¹ * gy⁻¹) h
  have s78 : Reachable v7 v8 := by
    have h : (gy⁻¹ * gx) * (gy * gy * gx⁻¹ * gy⁻¹ * gx) * (gy⁻¹ * gx)⁻¹ =
        gy⁻¹ * gx * gy * gy * gx⁻¹ := by
      group
    simpa [v7, v8] using
      reach_conj1 (a := gx * gy⁻¹ * gy⁻¹ * gy⁻¹)
        (b := gy * gy * gx⁻¹ * gy⁻¹ * gx)
        (c := gy⁻¹ * gx * gy * gy * gx⁻¹)
        (w := gy⁻¹ * gx) h
  have s89 : Reachable v8 v9 := by
    have h : (gy⁻¹ * gx * gy * gy * gx⁻¹) * (gx * gy⁻¹ * gy⁻¹ * gy⁻¹) =
        gy⁻¹ * gx * gy⁻¹ := by
      group
    simpa [v8, v9] using
      reach_mul10 (a := gx * gy⁻¹ * gy⁻¹ * gy⁻¹)
        (b := gy⁻¹ * gx * gy * gy * gx⁻¹)
        (c := gy⁻¹ * gx * gy⁻¹) h
  have s9_10 : Reachable v9 v10 := by
    have h : (gy⁻¹ * gy⁻¹) * (gx * gy⁻¹ * gy⁻¹ * gy⁻¹) * (gy⁻¹ * gy⁻¹)⁻¹ =
        gy⁻¹ * gy⁻¹ * gx * gy⁻¹ := by
      group
    simpa [v9, v10] using
      reach_conj0 (a := gx * gy⁻¹ * gy⁻¹ * gy⁻¹)
        (b := gy⁻¹ * gx * gy⁻¹)
        (c := gy⁻¹ * gy⁻¹ * gx * gy⁻¹)
        (w := gy⁻¹ * gy⁻¹) h
  have s10_11 : Reachable v10 v11 := by
    have h : (gy⁻¹ * gy⁻¹ * gx * gy⁻¹) * (gy⁻¹ * gx * gy⁻¹)⁻¹ = gy⁻¹ := by
      group
    simpa [v10, v11] using
      reach_mul01_inv (a := gy⁻¹ * gy⁻¹ * gx * gy⁻¹)
        (b := gy⁻¹ * gx * gy⁻¹)
        (c := gy⁻¹) h
  have s11_12 : Reachable v11 v12 := by
    have h : (gy⁻¹ * gx * gy⁻¹) * (gy⁻¹)⁻¹ = gy⁻¹ * gx := by
      group
    simpa [v11, v12] using
      reach_mul10_inv (a := gy⁻¹) (b := gy⁻¹ * gx * gy⁻¹)
        (c := gy⁻¹ * gx) h
  have s12_13 : Reachable v12 v13 := by
    have h : (gy⁻¹ * gx) * (gy⁻¹)⁻¹ = gy⁻¹ * gx * gy := by
      group
    simpa [v12, v13] using
      reach_mul10_inv (a := gy⁻¹) (b := gy⁻¹ * gx)
        (c := gy⁻¹ * gx * gy) h
  exact Relation.ReflTransGen.trans s01
    (Relation.ReflTransGen.trans s12
      (Relation.ReflTransGen.trans s23
        (Relation.ReflTransGen.trans s34
          (Relation.ReflTransGen.trans s45
            (Relation.ReflTransGen.trans s56
              (Relation.ReflTransGen.trans s67
                (Relation.ReflTransGen.trans s78
                  (Relation.ReflTransGen.trans s89
                    (Relation.ReflTransGen.trans s9_10
                      (Relation.ReflTransGen.trans s10_11
                        (Relation.ReflTransGen.trans s11_12 s12_13)))))))))))

/-- Reachability from the witness itself. -/
theorem reachable_witness_v13 : Reachable witnessState v13 := by
  rw [← v0_eq_witnessState]
  exact reachable_v0_v13

/-! ## 6. The endpoint is abelian terminal -/

/-- The exponent vector of the first generator. -/
theorem expVec_gx : Invariant.expVec gx = Invariant.genVec (0 : Fin 2) := by
  simp [Invariant.expVec, Invariant.expHom, Invariant.genVec]

/-- The exponent vector of the second generator. -/
theorem expVec_gy : Invariant.expVec gy = Invariant.genVec (1 : Fin 2) := by
  simp [Invariant.expVec, Invariant.expHom, Invariant.genVec]

/-- The exponent vector of the inverse of the second generator. -/
theorem expVec_gy_inv : Invariant.expVec (gy⁻¹) = -Invariant.genVec (1 : Fin 2) := by
  rw [Invariant.expVec_inv, expVec_gy]

/-- The exponent vector of the endpoint's second relator. -/
theorem expVec_gy_gx_gy :
    Invariant.expVec (gy⁻¹ * gx * gy) = Invariant.genVec (0 : Fin 2) := by
  rw [Invariant.expVec_mul, Invariant.expVec_mul, Invariant.expVec_inv,
    expVec_gx, expVec_gy]
  ext j
  fin_cases j <;> simp [Invariant.genVec]

/-- The endpoint `(y⁻¹, y⁻¹ x y)` is abelian terminal. -/
theorem abelianTerminal_v13 : AbelianTerminal v13 := by
  refine ⟨(Equiv.swap (0 : Fin 2) 1 : Fin 2 → Fin 2),
    (Equiv.swap (0 : Fin 2) 1).bijective, fun i => decide (i = 1), ?_⟩
  intro i
  fin_cases i
  · simpa [v13] using expVec_gy_inv
  · simpa [v13] using expVec_gy_gx_gy

/-! ## 7. The endpoint has cyclic Nielsen length two -/

/-- The cyclic length of `y⁻¹` is one. -/
theorem cycLen_gy_inv : cycLen (gy⁻¹) = 1 := by
  have h : gy⁻¹ = FreeGroup.mk [(1, false)] := rfl
  rw [h]
  unfold cycLen
  rw [FreeGroup.toWord_mk]
  simp [FreeGroup.reduceCyclically]

/-- The cyclic length of `y⁻¹ x y` is one: the outer letters cancel cyclically
and leave `x`. -/
theorem cycLen_gy_gx_gy : cycLen (gy⁻¹ * gx * gy) = 1 := by
  have h : gy⁻¹ * gx * gy = FreeGroup.mk [(1, false), (0, true), (1, true)] := rfl
  rw [h]
  unfold cycLen
  rw [FreeGroup.toWord_mk]
  have hred : FreeGroup.reduce ([(1, false), (0, true), (1, true)] : List (Fin 2 × Bool)) =
      [(1, false), (0, true), (1, true)] := rfl
  rw [hred]
  have hlist : ([(1, false), (0, true), (1, true)] : List (Fin 2 × Bool)) =
      (1, false) :: ([(0, true)] ++ [(1, true)]) := rfl
  rw [hlist, FreeGroup.reduceCyclically.cons_append]
  simp

/-- The endpoint has cyclic Nielsen length `1 + 1 = 2`. -/
theorem cyclicNielsenLength_v13 : cyclicNielsenLength v13 = 2 := by
  rw [cyclicNielsenLength_pair]
  change cycLen (gy⁻¹) + cycLen (gy⁻¹ * gx * gy) = 2
  rw [cycLen_gy_inv, cycLen_gy_gx_gy]

/-! ## 8. The witness descent -/

/-- **The seven-stage witness descent.**  The witness reaches the abelian
terminal state `(y⁻¹, y⁻¹ x y)` by 25 official Andrews–Curtis steps, and the
cyclic Nielsen length drops from 12 to 2.  This is the proposition left open as
a `def` at `NielsenRotationNormalForm.lean:418`. -/
theorem sevenStageWitnessDescent : SevenStageWitnessDescent := by
  refine ⟨v13, reachable_witness_v13, abelianTerminal_v13, ?_⟩
  rw [cyclicNielsenLength_v13, cyclicNielsenLength_witnessState]
  norm_num

/-! ## 9. Axiom record -/

#print axioms sevenStageWitnessDescent
#print axioms reachable_witness_v13
#print axioms abelianTerminal_v13

end SevenStage
end Nielsen
end AC
