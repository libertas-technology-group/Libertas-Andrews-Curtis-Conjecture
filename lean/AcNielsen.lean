import AcNielsenDefs
import AcProof
import NielsenRotationNormalForm
import NielsenCycLenConj

/-!
# AcNielsen — the cyclic Nielsen uniform pivot statement

This module states the universal pivot proposition of the cyclic Nielsen route
as a proposition-valued definition, and it proves a replacement statement that
records the failure of the one-stage, two-stage, and three-stage schedules at
the measure-14 pivot state.

## The open proposition

`cyclicNielsen_uniform_pivot_statement` is the both-long descent recorded as
taken from the session source `AcNielsen.lean:3211-3219`
(`cyclicNielsen_both_long_descent`). That session file is outside this
repository, so its text is UNKNOWN in this tree. The definitions the proposition
reads are declared in `AcNielsenDefs`; the terminal set it excludes is
`AC.ProofAttempt.IsSignedPermutation` from `AcProof`.

## The measure-14 obstruction

`PivotObstruction.pivotBlockObstruction` records three finite facts about the
state `pivotState` of cyclic lengths seven and seven. The one-stage block
`NStage.run` returns total cyclic Nielsen length at least seventeen against the
starting measure fourteen (`pivot_oneStage_measure_stalls`); the natural
two-stage completion returns fourteen (`pivot_twoStage_returns`); and the
three-stage unimodular return preserves the measure (`threeStage_measure`). The
three facts are proved in the `PivotObstruction` namespace and combined in
`pivotBlockObstruction_holds`.

The obstruction is local to those schedules. `pivotState` is abelian terminal,
cyclically reduced, not a signed permutation, and has two relators of length
seven (`pivotState_bothLong`); presentation-triviality of `pivotState` is not
proved here. The uniform proposition remains open: no theorem in this tree
carries an arbitrary both-long state to a smaller abelian-terminal state.

## Dependency status

`NielsenCycLenConj` proves conjugacy and inversion invariance of `cycLen`
(`cycLen_conj`, `cycLen_inv`). `NielsenRotationNormalForm` supplies the rotation
step and the computable cyclic-reduction predicate used by the obstruction
record. `NielsenMeasure12` and `NielsenMeasure12Cover` state the measure-12
slice and its covering obligation; the cover is not used by the obstruction
record.

## Check status

Candidate pending the kernel. The obstruction record was checked by
`lake env lean -DwarningAsError=true AcNielsen.lean` with exit zero and no
output; no full package build was run in this session.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace AC
namespace Nielsen

/-- The universal pivot statement of the cyclic Nielsen route: every rank-two
abelian-terminal presentation of the trivial group whose two relators are
cyclically reduced, are not a signed permutation, and have length at least
five has a finite AC sequence to an abelian-terminal presentation of the
trivial group whose cyclic Nielsen length is strictly smaller. -/
def cyclicNielsen_uniform_pivot_statement : Prop :=
  ∀ (S : Relators 2),
    AbelianTerminal S → PresentsTrivialGroup S →
    (∀ i : Fin 2, FreeGroup.IsCyclicallyReduced (S i).toWord) →
    ¬ ProofAttempt.IsSignedPermutation S →
    5 ≤ (S 0).toWord.length → 5 ≤ (S 1).toWord.length →
    ∃ T : Relators 2, Reachable S T ∧ AbelianTerminal T ∧
      PresentsTrivialGroup T ∧
      cyclicNielsenLength T < cyclicNielsenLength S

namespace PivotObstruction

open RotationNormalForm

/-- The inverse letter of one letter. -/
def invPair (x : Fin 2 × Bool) : Fin 2 × Bool := (x.1, !x.2)

/-- A computable cyclic reduction with fuel. -/
def cycRedFuel : ℕ → List (Fin 2 × Bool) → List (Fin 2 × Bool)
  | 0, L => L
  | n + 1, L =>
      match L with
      | [] => []
      | [_] => L
      | x :: xs =>
          match xs.getLast? with
          | some y =>
              if y = invPair x then cycRedFuel n ((x :: xs).dropLast.tail) else L
          | none => L

/-- The computable cyclic reduction at full fuel. -/
def cycRedB (L : List (Fin 2 × Bool)) : List (Fin 2 × Bool) :=
  cycRedFuel L.length L

/-- One two-relator stage, as data. `side` selects the relator that moves
(`false` is relator `0`, `true` is relator `1`), `ma` and `mb` are the rotations
of the relators `0` and `1`, and `inv` selects multiplication by the inverse of
the stationary relator. -/
structure NStage where
  side : Bool
  ma : ℕ
  mb : ℕ
  inv : Bool

/-- The word carried by the moved relator after one stage. -/
def NStage.moveWord (g : NStage) (A B : List (Fin 2 × Bool)) : List (Fin 2 × Bool) :=
  if g.side then
    cycRedB (FreeGroup.reduce (B.rotate g.mb ++
      (if g.inv then FreeGroup.invRev (A.rotate g.ma) else A.rotate g.ma)))
  else
    cycRedB (FreeGroup.reduce (A.rotate g.ma ++
      (if g.inv then FreeGroup.invRev (B.rotate g.mb) else B.rotate g.mb)))

/-- The word carried by the stationary relator after one stage. -/
def NStage.stayWord (g : NStage) (A B : List (Fin 2 × Bool)) : List (Fin 2 × Bool) :=
  if g.side then
    (if g.inv then FreeGroup.invRev (A.rotate g.ma) else A.rotate g.ma)
  else
    (if g.inv then FreeGroup.invRev (B.rotate g.mb) else B.rotate g.mb)

/-- The pair of words after one stage. -/
def NStage.run (g : NStage) (p : List (Fin 2 × Bool) × List (Fin 2 × Bool)) :
    List (Fin 2 × Bool) × List (Fin 2 × Bool) :=
  if g.side then (g.stayWord p.1 p.2, g.moveWord p.1 p.2)
  else (g.moveWord p.1 p.2, g.stayWord p.1 p.2)

/-- The first relator of the first failing state. -/
def pivotU : List (Fin 2 × Bool) :=
  [(0, true), (0, true), (0, true), (1, true), (0, false), (0, false), (1, false)]

/-- The second relator of the first failing state. -/
def pivotV : List (Fin 2 × Bool) :=
  [(0, true), (1, true), (1, true), (1, true), (0, false), (1, false), (1, false)]

/-- The first failing state, at cyclic Nielsen length fourteen. -/
def pivotState : Relators 2 := ![FreeGroup.mk pivotU, FreeGroup.mk pivotV]

/-- The cyclic length of a word presented by a cyclically reduced list is the
length of the list. -/
theorem cycLen_mk_of_isCycRed {L : List (Fin 2 × Bool)}
    (h : FreeGroup.IsCyclicallyReduced L) :
    cycLen (FreeGroup.mk L) = L.length := by
  unfold cycLen
  rw [FreeGroup.toWord_mk, FreeGroup.isReduced_iff_reduce_eq.mp h.isReduced,
    reduceCyclically_eq_self h]

/-- Every one-stage instantiation at the first failing state returns total list
length at least seventeen, above the starting measure fourteen. -/
theorem pivot_stage_stalls :
    ∀ (side : Bool) (ma mb : Fin 7) (iv : Bool),
      17 ≤ (NStage.run ⟨side, ma.val, mb.val, iv⟩ (pivotU, pivotV)).1.length +
        (NStage.run ⟨side, ma.val, mb.val, iv⟩ (pivotU, pivotV)).2.length := by
  decide

/-- Both words of every one-stage instantiation are cyclically reduced. -/
theorem pivot_stage_cycRed :
    ∀ (side : Bool) (ma mb : Fin 7) (iv : Bool),
      isCycRedB (NStage.run ⟨side, ma.val, mb.val, iv⟩ (pivotU, pivotV)).1 = true ∧
      isCycRedB (NStage.run ⟨side, ma.val, mb.val, iv⟩ (pivotU, pivotV)).2 = true := by
  decide

/-- Every one-stage instantiation at the first failing state has cyclic Nielsen
length at least seventeen, above the starting measure fourteen. -/
theorem pivot_oneStage_measure_stalls :
    ∀ (side : Bool) (ma mb : Fin 7) (iv : Bool),
      17 ≤ cycLen (FreeGroup.mk (NStage.run ⟨side, ma.val, mb.val, iv⟩ (pivotU, pivotV)).1) +
        cycLen (FreeGroup.mk (NStage.run ⟨side, ma.val, mb.val, iv⟩ (pivotU, pivotV)).2) := by
  intro side ma mb iv
  have hlen := pivot_stage_stalls side ma mb iv
  have hred := pivot_stage_cycRed side ma mb iv
  have h1 : cycLen (FreeGroup.mk (NStage.run ⟨side, ma.val, mb.val, iv⟩ (pivotU, pivotV)).1) =
      (NStage.run ⟨side, ma.val, mb.val, iv⟩ (pivotU, pivotV)).1.length :=
    cycLen_mk_of_isCycRed ((isCycRedB_iff _).mp hred.1)
  have h2 : cycLen (FreeGroup.mk (NStage.run ⟨side, ma.val, mb.val, iv⟩ (pivotU, pivotV)).2) =
      (NStage.run ⟨side, ma.val, mb.val, iv⟩ (pivotU, pivotV)).2.length :=
    cycLen_mk_of_isCycRed ((isCycRedB_iff _).mp hred.2)
  omega

/-- The exponent sum of a list of letters at generator `i`. -/
def letterSum (L : List (Fin 2 × Bool)) (i : Fin 2) : ℤ :=
  (L.map (fun p => if p.1 = i then (if p.2 then (1 : ℤ) else -1) else 0)).sum

theorem letterSum_cons (a : Fin 2 × Bool) (t : List (Fin 2 × Bool)) (i : Fin 2) :
    letterSum (a :: t) i =
      (if a.1 = i then (if a.2 then (1 : ℤ) else -1) else 0) + letterSum t i := by
  simp [letterSum]

/-- The exponent vector of a generator. -/
theorem expVec_of (x : Fin 2) :
    Invariant.expVec (FreeGroup.of x) = Invariant.genVec x := by
  simp [Invariant.expVec, Invariant.expHom]

/-- The exponent vector of the inverse of a generator. -/
theorem expVec_inv_of (x : Fin 2) :
    Invariant.expVec ((FreeGroup.of x)⁻¹) = -Invariant.genVec x := by
  rw [Invariant.expVec_inv, expVec_of]

/-- A single negative letter is the inverse of a generator. -/
theorem mk_false_eq_inv (x : Fin 2) :
    FreeGroup.mk [(x, false)] = (FreeGroup.of x)⁻¹ := by
  simp [FreeGroup.of, FreeGroup.inv_mk, FreeGroup.invRev]

/-- The exponent vector of a one-letter list. -/
theorem expVec_mk_singleton_apply (a : Fin 2 × Bool) (i : Fin 2) :
    Invariant.expVec (FreeGroup.mk [a]) i =
      if a.1 = i then (if a.2 then (1 : ℤ) else -1) else 0 := by
  obtain ⟨x, b⟩ := a
  cases b
  · rw [mk_false_eq_inv, expVec_inv_of]
    by_cases h : x = i
    · subst h
      simp [Invariant.genVec]
    · simp [Invariant.genVec, h, Ne.symm h]
  · have hof : FreeGroup.mk [(x, true)] = FreeGroup.of x := rfl
    rw [hof, expVec_of]
    by_cases h : x = i
    · subst h
      simp [Invariant.genVec]
    · simp [Invariant.genVec, h, Ne.symm h]

/-- The exponent vector of a list is the exponent vector of its head plus the
exponent vector of its tail. -/
theorem expVec_mk_cons (a : Fin 2 × Bool) (t : List (Fin 2 × Bool)) :
    Invariant.expVec (FreeGroup.mk (a :: t)) =
      Invariant.expVec (FreeGroup.mk [a]) + Invariant.expVec (FreeGroup.mk t) := by
  have h : FreeGroup.mk (a :: t) = FreeGroup.mk [a] * FreeGroup.mk t := by
    rw [FreeGroup.mul_mk]
    rfl
  rw [h, Invariant.expVec_mul]

/-- The exponent vector of a list word is the letter sum. -/
theorem expVec_mk_apply (L : List (Fin 2 × Bool)) (i : Fin 2) :
    Invariant.expVec (FreeGroup.mk L) i = letterSum L i := by
  induction L with
  | nil =>
      have h1 : FreeGroup.mk ([] : List (Fin 2 × Bool)) = 1 := rfl
      rw [h1, Invariant.expVec_one]
      simp [letterSum]
  | cons a t ih =>
      rw [expVec_mk_cons]
      change Invariant.expVec (FreeGroup.mk [a]) i + Invariant.expVec (FreeGroup.mk t) i =
        letterSum (a :: t) i
      rw [expVec_mk_singleton_apply, ih, letterSum_cons]

theorem pivotU_length : pivotU.length = 7 := rfl

theorem pivotV_length : pivotV.length = 7 := rfl

theorem pivotU_isReduced : FreeGroup.IsReduced pivotU :=
  (isReducedB_iff pivotU).mp (by decide)

theorem pivotV_isReduced : FreeGroup.IsReduced pivotV :=
  (isReducedB_iff pivotV).mp (by decide)

theorem pivotU_isCycRed : FreeGroup.IsCyclicallyReduced pivotU :=
  (isCycRedB_iff pivotU).mp (by decide)

theorem pivotV_isCycRed : FreeGroup.IsCyclicallyReduced pivotV :=
  (isCycRedB_iff pivotV).mp (by decide)

theorem pivotU_letterSum : letterSum pivotU 0 = 1 ∧ letterSum pivotU 1 = 0 := by
  decide

theorem pivotV_letterSum : letterSum pivotV 0 = 0 ∧ letterSum pivotV 1 = 1 := by
  decide

/-- The first failing state has cyclic Nielsen length fourteen. -/
theorem pivotState_measure : cyclicNielsenLength pivotState = 14 := by
  rw [cyclicNielsenLength_pair]
  have h0 : pivotState 0 = FreeGroup.mk pivotU := rfl
  have h1 : pivotState 1 = FreeGroup.mk pivotV := rfl
  rw [h0, h1, cycLen_mk_of_isCycRed pivotU_isCycRed,
    cycLen_mk_of_isCycRed pivotV_isCycRed, pivotU_length, pivotV_length]

/-- The first failing state is abelian terminal. -/
theorem pivotState_abelianTerminal : AbelianTerminal pivotState := by
  refine ⟨id, Function.bijective_id, fun _ => true, ?_⟩
  intro i
  fin_cases i
  · change Invariant.expVec (FreeGroup.mk pivotU) = Invariant.genVec (id 0)
    ext t
    rw [expVec_mk_apply]
    fin_cases t <;> simp [pivotU_letterSum, Invariant.genVec, Pi.single]
  · change Invariant.expVec (FreeGroup.mk pivotV) = Invariant.genVec (id 1)
    ext t
    rw [expVec_mk_apply]
    fin_cases t <;> simp [pivotV_letterSum, Invariant.genVec, Pi.single]

/-- Both relators of the first failing state are cyclically reduced. -/
theorem pivotState_cycRed :
    ∀ i : Fin 2, FreeGroup.IsCyclicallyReduced (pivotState i).toWord := by
  intro i
  have hUtw : (FreeGroup.mk pivotU).toWord = pivotU := by
    rw [FreeGroup.toWord_mk]
    exact (FreeGroup.IsReduced.red_iff_eq pivotU_isReduced).mp FreeGroup.reduce.red
  have hVtw : (FreeGroup.mk pivotV).toWord = pivotV := by
    rw [FreeGroup.toWord_mk]
    exact (FreeGroup.IsReduced.red_iff_eq pivotV_isReduced).mp FreeGroup.reduce.red
  fin_cases i
  · change FreeGroup.IsCyclicallyReduced (FreeGroup.mk pivotU).toWord
    rw [hUtw]
    exact pivotU_isCycRed
  · change FreeGroup.IsCyclicallyReduced (FreeGroup.mk pivotV).toWord
    rw [hVtw]
    exact pivotV_isCycRed

/-- The first failing state is not a signed permutation. -/
theorem pivotState_not_signedPermutation :
    ¬ ProofAttempt.IsSignedPermutation pivotState := by
  rintro ⟨σ, _hσ, ε, hε⟩
  have h0 := hε 0
  have hlen : (pivotState 0).toWord.length = 7 := by
    change (FreeGroup.mk pivotU).toWord.length = 7
    rw [FreeGroup.toWord_mk]
    have hred := (FreeGroup.IsReduced.red_iff_eq pivotU_isReduced).mp
      FreeGroup.reduce.red
    rw [hred]
    exact pivotU_length
  have hlen1 : (pivotState 0).toWord.length = 1 := by
    rw [h0]
    cases ε 0 <;> simp [FreeGroup.toWord_of, FreeGroup.toWord_inv]
  omega

/-- The natural two-stage completion returns total list length fourteen. -/
theorem pivot_twoStage_stalls :
    (NStage.run ⟨false, 0, 6, true⟩
      (NStage.run ⟨false, 0, 0, true⟩ (pivotU, pivotV))).1.length +
    (NStage.run ⟨false, 0, 6, true⟩
      (NStage.run ⟨false, 0, 0, true⟩ (pivotU, pivotV))).2.length = 14 := by
  decide

/-- Both words of the natural two-stage completion are cyclically reduced. -/
theorem pivot_twoStage_cycRed :
    isCycRedB (NStage.run ⟨false, 0, 6, true⟩
      (NStage.run ⟨false, 0, 0, true⟩ (pivotU, pivotV))).1 = true ∧
    isCycRedB (NStage.run ⟨false, 0, 6, true⟩
      (NStage.run ⟨false, 0, 0, true⟩ (pivotU, pivotV))).2 = true := by
  decide

/-- The natural two-stage completion returns cyclic Nielsen length fourteen. -/
theorem pivot_twoStage_returns :
    cycLen (FreeGroup.mk (NStage.run ⟨false, 0, 6, true⟩
      (NStage.run ⟨false, 0, 0, true⟩ (pivotU, pivotV))).1) +
    cycLen (FreeGroup.mk (NStage.run ⟨false, 0, 6, true⟩
      (NStage.run ⟨false, 0, 0, true⟩ (pivotU, pivotV))).2) = 14 := by
  have hlen := pivot_twoStage_stalls
  have hred := pivot_twoStage_cycRed
  rw [cycLen_mk_of_isCycRed ((isCycRedB_iff _).mp hred.1),
    cycLen_mk_of_isCycRed ((isCycRedB_iff _).mp hred.2)]
  exact hlen

/-! ## The three-stage unimodular return -/

/-- The negation of a signed basis vector is the signed basis vector with the
complementary sign. -/
theorem neg_pm_genVec (f : Bool) (s : Fin 2) :
    -(if f then Invariant.genVec s else -Invariant.genVec s) =
      (if !f then Invariant.genVec s else -Invariant.genVec s) := by
  cases f <;> simp

/-- **The three-stage unimodular block.** From `(A, B)` five official moves reach
`(A * B * A⁻¹, A⁻¹)`. -/
theorem threeStage_reachable (S : Relators 2) (A B : Word 2)
    (hA : S 0 = A) (hB : S 1 = B) :
    ∃ T : Relators 2, Reachable S T ∧ T 0 = A * B * A⁻¹ ∧ T 1 = A⁻¹ := by
  classical
  let S1 : Relators 2 := Function.update S 0 (S 0 * S 1)
  let S2 : Relators 2 := Function.update S1 0 (S1 0)⁻¹
  let S3 : Relators 2 := Function.update S2 1 (S2 1 * S2 0)
  let S4 : Relators 2 := Function.update S3 0 (S3 0)⁻¹
  let S5 : Relators 2 := Function.update S4 0 (S4 0 * S4 1)
  have hS1_0 : S1 0 = A * B := by
    simp only [S1, Function.update_self, hA, hB]
  have hS1_1 : S1 1 = B := by
    simp only [S1, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0), hB]
  have hS2_0 : S2 0 = (A * B)⁻¹ := by
    simp only [S2, Function.update_self, hS1_0]
  have hS2_1 : S2 1 = B := by
    simp only [S2, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0), hS1_1]
  have hS3_0 : S3 0 = (A * B)⁻¹ := by
    simp only [S3, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1), hS2_0]
  have hS3_1 : S3 1 = B * (A * B)⁻¹ := by
    simp only [S3, Function.update_self, hS2_1, hS2_0]
  have hS4_0 : S4 0 = A * B := by
    simp only [S4, Function.update_self, hS3_0, inv_inv]
  have hS4_1 : S4 1 = B * (A * B)⁻¹ := by
    simp only [S4, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0), hS3_1]
  have hS5_0 : S5 0 = A * B * A⁻¹ := by
    simp only [S5, Function.update_self, hS4_0, hS4_1]
    group
  have hS5_1 : S5 1 = A⁻¹ := by
    simp only [S5, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0), hS4_1]
    group
  have hstep1 : Step S S1 := Step.mulRight S 0 1 (by decide)
  have hstep2 : Step S1 S2 := Step.inv S1 0
  have hstep3 : Step S2 S3 := Step.mulRight S2 1 0 (by decide)
  have hstep4 : Step S3 S4 := Step.inv S3 0
  have hstep5 : Step S4 S5 := Step.mulRight S4 0 1 (by decide)
  have hchain : Reachable S S5 :=
    (Relation.ReflTransGen.single hstep1).trans
      ((Relation.ReflTransGen.single hstep2).trans
        ((Relation.ReflTransGen.single hstep3).trans
          ((Relation.ReflTransGen.single hstep4).trans
            (Relation.ReflTransGen.single hstep5))))
  exact ⟨S5, hchain, hS5_0, hS5_1⟩

/-- The first entry of the three-stage return has the exponent vector of `B`. -/
theorem threeStage_expVec (A B : Word 2) :
    Invariant.expVec (A * B * A⁻¹) = Invariant.expVec B :=
  Invariant.expVec_conj (r := B) (w := A)

/-- The second entry of the three-stage return has the negated exponent vector
of `A`. -/
theorem threeStage_expVec_inv (A : Word 2) :
    Invariant.expVec A⁻¹ = -Invariant.expVec A :=
  Invariant.expVec_inv (w := A)

/-- The three-stage return lands in the abelian-terminal set: the endpoint's
exponent vectors are `expVec B` and `-expVec A`, the signed swap of the start. -/
theorem threeStage_abelianTerminal (S T : Relators 2) (A B : Word 2)
    (hA : S 0 = A) (hB : S 1 = B)
    (hT0 : T 0 = A * B * A⁻¹) (hT1 : T 1 = A⁻¹)
    (hS : AbelianTerminal S) : AbelianTerminal T := by
  obtain ⟨σ, hσ, ε, hε⟩ := hS
  refine ⟨fun i => σ (Equiv.swap 0 1 i), hσ.comp (Equiv.swap 0 1).bijective,
    fun i => if i = 0 then ε 1 else !(ε 0), ?_⟩
  intro i
  fin_cases i
  · show Invariant.expVec (T 0) =
      (if (if (0 : Fin 2) = 0 then ε 1 else !(ε 0)) then
        Invariant.genVec (σ (Equiv.swap 0 1 0)) else
        -Invariant.genVec (σ (Equiv.swap 0 1 0)))
    rw [hT0, threeStage_expVec]
    rw [← hB, hε 1]
    simp
  · show Invariant.expVec (T 1) =
      (if (if (1 : Fin 2) = 0 then ε 1 else !(ε 0)) then
        Invariant.genVec (σ (Equiv.swap 0 1 1)) else
        -Invariant.genVec (σ (Equiv.swap 0 1 1)))
    rw [hT1, threeStage_expVec_inv]
    rw [← hA, hε 0, neg_pm_genVec]
    simp

/-- **The three-stage return preserves the measure.** The endpoint
`(A * B * A⁻¹, A⁻¹)` has the same cyclic Nielsen length as `(A, B)`, using
conjugacy invariance and inversion invariance from `NielsenCycLenConj`. -/
theorem threeStage_measure (S T : Relators 2) (A B : Word 2)
    (hA : S 0 = A) (hB : S 1 = B)
    (hT0 : T 0 = A * B * A⁻¹) (hT1 : T 1 = A⁻¹) :
    cyclicNielsenLength T = cyclicNielsenLength S := by
  rw [cyclicNielsenLength_pair T, cyclicNielsenLength_pair S, hT0, hT1, hA, hB,
    cycLen_conj A B, cycLen_inv A]
  omega

/-- The state produced by one instantiation of the one-stage block. -/
def blockState (side : Bool) (ma mb : Fin 7) (iv : Bool) : Relators 2 :=
  ![FreeGroup.mk (NStage.run ⟨side, ma.val, mb.val, iv⟩ (pivotU, pivotV)).1,
    FreeGroup.mk (NStage.run ⟨side, ma.val, mb.val, iv⟩ (pivotU, pivotV)).2]

/-- The state produced by the natural two-stage completion. -/
def twoStageState : Relators 2 :=
  ![FreeGroup.mk (NStage.run ⟨false, 0, 6, true⟩
      (NStage.run ⟨false, 0, 0, true⟩ (pivotU, pivotV))).1,
    FreeGroup.mk (NStage.run ⟨false, 0, 6, true⟩
      (NStage.run ⟨false, 0, 0, true⟩ (pivotU, pivotV))).2]

/-- **The finite-block obstruction at the measure-14 pivot state.** The
one-stage both-long block raises the measure to at least 17; the natural
two-stage completion returns it to 14; and the three-stage unimodular return
preserves the measure. These three facts block the three schedules recorded for
the pivot state; they do not exhaust the reachable set. -/
def pivotBlockObstruction : Prop :=
  (∀ (side : Bool) (ma mb : Fin 7) (iv : Bool),
    17 ≤ cyclicNielsenLength (blockState side ma mb iv)) ∧
  (cyclicNielsenLength twoStageState = 14) ∧
  (∀ (S T : Relators 2) (A B : Word 2), S 0 = A → S 1 = B →
    T 0 = A * B * A⁻¹ → T 1 = A⁻¹ →
    cyclicNielsenLength T = cyclicNielsenLength S)

/-- **The obstruction holds.** This is the replacement statement for the
measure-14 block. It is not a proof of
`cyclicNielsen_uniform_pivot_statement`; the uniform both-long block remains
open. -/
theorem pivotBlockObstruction_holds : pivotBlockObstruction := by
  refine ⟨?_, ?_, ?_⟩
  · intro side ma mb iv
    exact pivot_oneStage_measure_stalls side ma mb iv
  · exact pivot_twoStage_returns
  · exact threeStage_measure

/-- The measure-14 state satisfies every hypothesis of
`cyclicNielsen_uniform_pivot_statement` except presentation-triviality, which is
not proved here. It is cyclically reduced, abelian terminal, not a signed
permutation, and its two cyclic lengths are seven. -/
theorem pivotState_bothLong :
    AbelianTerminal pivotState ∧
    (∀ i : Fin 2, FreeGroup.IsCyclicallyReduced (pivotState i).toWord) ∧
    ¬ ProofAttempt.IsSignedPermutation pivotState ∧
    cyclicNielsenLength pivotState = 14 ∧
    (pivotState 0).toWord.length = 7 ∧
    (pivotState 1).toWord.length = 7 := by
  refine ⟨pivotState_abelianTerminal, pivotState_cycRed,
    pivotState_not_signedPermutation, pivotState_measure, ?_, ?_⟩
  · change (FreeGroup.mk pivotU).toWord.length = 7
    rw [FreeGroup.toWord_mk]
    have hred := (FreeGroup.IsReduced.red_iff_eq pivotU_isReduced).mp
      FreeGroup.reduce.red
    rw [hred, pivotU_length]
  · change (FreeGroup.mk pivotV).toWord.length = 7
    rw [FreeGroup.toWord_mk]
    have hred := (FreeGroup.IsReduced.red_iff_eq pivotV_isReduced).mp
      FreeGroup.reduce.red
    rw [hred, pivotV_length]

end PivotObstruction

end Nielsen
end AC
