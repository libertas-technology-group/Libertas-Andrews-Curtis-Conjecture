module

public import AC
public import AcMove
public import BranchD
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.Tactic.Group
public import Mathlib.Tactic

@[expose] public section

/-!
# Branch D3 — the full stable projection cohort

This file records the finite cohort measurement of the stable projection test and
the concrete obstruction that a general projection proof must remove.

## What is proved here

1. `cohort_partition`: the scored cohort has 10,115 rows, split into 7,443 solved
   and 2,672 unsolved rows.
2. `cohort_no_refutation`, `cohort_no_unknown`, `cohort_within_budget`: no
   measured candidate in `cohort` has the refuted or unknown status, and every
   exact ordinary minimum is at or below its stable work.  The candidate table is
   the set of stable paths found by the forced and fresh-generator searches;
   `BRANCH_D3.md` records the paths, rank traces, and exact ordinary minima.
3. `cohort_positive_overhead`, `cohort_min_gap`: the stable work is strictly above
   the ordinary minimum in every measured candidate, and the smallest gap is 18.
4. `move_two_standard` and `polluted_no_destabilize`: one ordinary move takes the
   standard rank-two tuple to `((x * y), (y))`, and no destabilization step leaves
   that state.  The inserted generator is absent from the old relators only in a
   stabilization image, so the direct rank return fails.

## Status

No `sorry`, no `admit`, no user `axiom`, no `native_decide`. The file is in the
`AcCorpus` globs and compiles in the 3,308-job build. The open statement is
`AC.BranchD.StableImpliesOrdinary`, a `def` in `BranchD.lean`; the cohort table
is finite evidence for it, not a proof of it.
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace AC
namespace BranchD3

/-! ## 1. The scored cohort -/

/-- The scored cohort size: 10,115 presentations on the stable board. -/
def scoredCount : ℕ := 10115

/-- The solved rows reported by the score record. -/
def solvedCount : ℕ := 7443

/-- The unsolved rows reported by the score record. -/
def unsolvedCount : ℕ := 2672

/-- The score-record partition of the scored cohort. -/
theorem cohort_partition : solvedCount + unsolvedCount = scoredCount := by decide

/-! ## 2. The fixed rule and the measured candidates -/

/-- The outcome of the exact uniform-cost ordinary search at one stable budget. -/
inductive Result where
  /-- An ordinary path was found with the recorded minimum work. -/
  | consistent (work : ℕ)
  /-- The search exhausted every state at or below the stable work without a goal. -/
  | refuted
  /-- The search hit its state or time cap before deciding the budget. -/
  | unknown
  deriving DecidableEq, Repr

/-- One measured stable candidate.  `stableWork` is the official work of the
stable path; `result` is the exact ordinary search at that budget. -/
structure Candidate where
  id : String
  search : String
  solved : Bool
  initialLength : ℕ
  stableWork : ℕ
  result : Result
  deriving DecidableEq, Repr

/-- The fixed rule: a candidate refutes the projection principle only when the
ordinary search exhausted the stable budget.  An unknown result is not a
refutation. -/
def Candidate.refutes (c : Candidate) : Bool :=
  match c.result with
  | Result.refuted => true
  | _ => false

/-- A candidate is within budget when its exact ordinary minimum is at most its
stable work. -/
def Candidate.withinBudget (c : Candidate) : Bool :=
  match c.result with
  | Result.consistent work => work ≤ c.stableWork
  | _ => false

/-- A candidate has an undecided result when the exact search hit its cap. -/
def Candidate.unknown (c : Candidate) : Bool :=
  match c.result with
  | Result.unknown => true
  | _ => false

/-- A candidate has positive stable overhead when its stable work is strictly
above the exact ordinary minimum. -/
def Candidate.positiveOverhead (c : Candidate) : Bool :=
  match c.result with
  | Result.consistent work => c.stableWork > work
  | _ => false

/-- The measured candidate table.  Each row is a stable path found by the forced
or fresh-generator search; the `BRANCH_D3.md` table carries the path and the rank
trace.  A `consistent` result records the exact ordinary minimum work at the
stable budget. -/
def cohort : List Candidate := [
  ⟨"sac-00742-fresh", "fresh", true, 17, 193, Result.consistent 93⟩,
  ⟨"sac-00807-forced", "forced", true, 25, 215, Result.consistent 180⟩,
  ⟨"sac-00894-forced", "forced", true, 27, 229, Result.consistent 184⟩,
  ⟨"sac-01635-forced", "forced", true, 13, 87, Result.consistent 62⟩,
  ⟨"sac-01635-fresh", "fresh", true, 13, 142, Result.consistent 62⟩,
  ⟨"sac-02761-forced", "forced", true, 31, 239, Result.consistent 182⟩,
  ⟨"sac-02761-fresh", "fresh", true, 31, 372, Result.consistent 182⟩,
  ⟨"sac-03448-forced", "forced", true, 30, 288, Result.consistent 221⟩,
  ⟨"sac-03493-forced", "forced", true, 24, 219, Result.consistent 172⟩,
  ⟨"sac-03493-fresh", "fresh", true, 24, 309, Result.consistent 172⟩,
  ⟨"sac-03501-forced", "forced", true, 24, 203, Result.consistent 162⟩,
  ⟨"sac-03501-fresh", "fresh", true, 24, 305, Result.consistent 162⟩,
  ⟨"sac-03756-forced", "forced", true, 31, 271, Result.consistent 214⟩,
  ⟨"sac-03953-fresh", "fresh", true, 28, 387, Result.consistent 228⟩,
  ⟨"sac-04631-forced", "forced", true, 17, 140, Result.consistent 114⟩,
  ⟨"sac-04631-fresh", "fresh", true, 17, 217, Result.consistent 114⟩,
  ⟨"sac-04705-forced", "forced", true, 21, 182, Result.consistent 148⟩,
  ⟨"sac-04705-fresh", "fresh", true, 21, 273, Result.consistent 148⟩,
  ⟨"sac-05532-forced", "forced", true, 31, 250, Result.consistent 182⟩,
  ⟨"sac-05532-fresh", "fresh", true, 31, 350, Result.consistent 182⟩,
  ⟨"sac-05625-forced", "forced", true, 33, 270, Result.consistent 209⟩,
  ⟨"sac-05625-fresh", "fresh", true, 33, 388, Result.consistent 209⟩,
  ⟨"sac-05765-forced", "forced", true, 29, 263, Result.consistent 208⟩,
  ⟨"sac-05765-fresh", "fresh", true, 29, 373, Result.consistent 208⟩,
  ⟨"sac-06154-forced", "forced", true, 25, 240, Result.consistent 200⟩,
  ⟨"sac-06154-fresh", "fresh", true, 25, 347, Result.consistent 200⟩,
  ⟨"sac-06467-forced", "forced", true, 25, 210, Result.consistent 163⟩,
  ⟨"sac-06467-fresh", "fresh", true, 25, 304, Result.consistent 163⟩,
  ⟨"sac-06500-forced", "forced", true, 13, 193, Result.consistent 160⟩,
  ⟨"sac-06500-fresh", "fresh", true, 13, 259, Result.consistent 160⟩,
  ⟨"sac-06507-forced", "forced", true, 29, 244, Result.consistent 199⟩,
  ⟨"sac-06507-fresh", "fresh", true, 29, 366, Result.consistent 199⟩,
  ⟨"sac-06530-forced", "forced", true, 25, 240, Result.consistent 195⟩,
  ⟨"sac-06530-fresh", "fresh", true, 25, 345, Result.consistent 195⟩,
  ⟨"sac-06645-forced", "forced", true, 29, 375, Result.consistent 310⟩,
  ⟨"sac-06821-forced", "forced", true, 30, 270, Result.consistent 215⟩,
  ⟨"sac-06821-fresh", "fresh", true, 30, 382, Result.consistent 215⟩,
  ⟨"sac-07106-forced", "forced", true, 32, 274, Result.consistent 230⟩,
  ⟨"sac-07106-fresh", "fresh", true, 32, 403, Result.consistent 230⟩,
  ⟨"sac-07248-forced", "forced", true, 23, 212, Result.consistent 177⟩,
  ⟨"sac-07248-fresh", "fresh", true, 23, 310, Result.consistent 177⟩,
  ⟨"sac-07280-forced", "forced", true, 26, 212, Result.consistent 163⟩,
  ⟨"sac-07280-fresh", "fresh", true, 26, 308, Result.consistent 163⟩,
  ⟨"sac-07445-forced", "forced", true, 12, 141, Result.consistent 112⟩,
  ⟨"sac-07445-fresh", "fresh", true, 12, 211, Result.consistent 112⟩,
  ⟨"sac-08491-forced", "forced", true, 9, 66, Result.consistent 48⟩,
  ⟨"sac-08491-fresh", "fresh", true, 9, 104, Result.consistent 48⟩,
  ⟨"sac-09292-forced", "forced", true, 31, 276, Result.consistent 233⟩,
  ⟨"sac-09292-fresh", "fresh", true, 31, 402, Result.consistent 233⟩,
  ⟨"sac-09434-forced", "forced", true, 22, 198, Result.consistent 157⟩,
  ⟨"sac-09434-fresh", "fresh", true, 22, 286, Result.consistent 157⟩
]

/-- The distinct scored identifiers in the cohort. -/
def cohortIds : List String := [
  "sac-00742",
  "sac-00807",
  "sac-00894",
  "sac-01635",
  "sac-02761",
  "sac-03448",
  "sac-03493",
  "sac-03501",
  "sac-03756",
  "sac-03953",
  "sac-04631",
  "sac-04705",
  "sac-05532",
  "sac-05625",
  "sac-05765",
  "sac-06154",
  "sac-06467",
  "sac-06500",
  "sac-06507",
  "sac-06530",
  "sac-06645",
  "sac-06821",
  "sac-07106",
  "sac-07248",
  "sac-07280",
  "sac-07445",
  "sac-08491",
  "sac-09292",
  "sac-09434"
]

/-- The number of measured candidate paths. -/
theorem cohort_length : cohort.length = 51 := by decide

/-- The number of distinct identifiers. -/
theorem cohortIds_length : cohortIds.length = 29 := by decide

/-- The identifiers are distinct. -/
theorem cohortIds_nodup : cohortIds.Nodup := by decide

/-- Every measured candidate lies on a solved scored row. -/
theorem cohort_all_solved : cohort.all (fun c => c.solved) = true := by decide

/-- The forced search supplied 27 candidate paths. -/
theorem forced_count :
    (cohort.filter (fun c => c.search == "forced")).length = 27 := by decide

/-- The fresh-generator search supplied 24 candidate paths. -/
theorem fresh_count :
    (cohort.filter (fun c => c.search == "fresh")).length = 24 := by decide

/-- The two search counts partition the candidate table. -/
theorem cohort_search_partition : 27 + 24 = cohort.length := by decide

/-- Every measured candidate has an exact ordinary minimum at or below its stable
work. -/
theorem cohort_within_budget : cohort.all (fun c => c.withinBudget) = true := by decide

/-- No measured candidate has the refuted status. -/
theorem cohort_no_refutation : cohort.filter (fun c => c.refutes) = [] := by decide

/-- No measured candidate has the unknown status. -/
theorem cohort_no_unknown : cohort.filter (fun c => c.unknown) = [] := by decide

/-- The stable work is strictly above the exact ordinary minimum in every
measured candidate. -/
theorem cohort_positive_overhead :
    cohort.all (fun c => c.positiveOverhead) = true := by decide

/-- The smallest stable-work gap in the measured cohort is 18. -/
theorem cohort_min_gap :
    cohort.all (fun c => match c.result with
      | Result.consistent work => 18 ≤ c.stableWork - work
      | _ => false) = true := by decide

/-- The ordinary-to-stable direction that the forced search instantiates: an
ordinary solution gives a stable path to the empty presentation. -/
theorem ordinary_solution_stable {n : ℕ} {R : Relators n}
    (h : Reachable R (standard n)) :
    StableReachable ⟨n, R⟩ BranchD.emptyPresentation :=
  BranchD.stableReachable_empty_of_reachable_standard h

/-! ## 3. The concrete obstruction -/

def x2 : Word 2 := FreeGroup.of 0
def y2 : Word 2 := FreeGroup.of 1

def tup (a b : Word 2) : Relators 2 := fun i => if i = 0 then a else b

/-- The homomorphism that kills `x` and fixes `y`. -/
def killX : FreeGroup (Fin 2) →* FreeGroup (Fin 2) :=
  FreeGroup.lift fun i => if i = (0 : Fin 2) then 1 else FreeGroup.of i

@[simp] theorem killX_x : killX x2 = 1 := by
  simp [killX, x2]

@[simp] theorem killX_y : killX y2 = y2 := by
  simp [killX, y2]

theorem lift_comp {α β γ : Type} [Group γ]
    (f : α → FreeGroup β) (g : FreeGroup β →* γ) (x : FreeGroup α) :
    g (FreeGroup.lift f x) = FreeGroup.lift (g ∘ f) x := by
  let G : FreeGroup α →* γ := g.comp (FreeGroup.lift f)
  have hG : ∀ a, G (FreeGroup.of a) = (g ∘ f) a := by
    intro a
    simp [G]
  exact FreeGroup.lift_unique G hG

theorem lift_const_one {α : Type} (w : FreeGroup α) :
    FreeGroup.lift (fun _ => (1 : FreeGroup (Fin 2))) w = 1 := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of a => simp
  | inv_of a ih => simp [ih]
  | mul x y ihx ihy => simp [ihx, ihy]

/-- The inserted generator is absent from the image of `Fin.succAbove 1`. -/
theorem killX_map_succAbove_one (w : Word 1) :
    killX (FreeGroup.map (Fin.succAbove (1 : Fin 2)) w) = 1 := by
  rw [FreeGroup.map_eq_lift]
  rw [lift_comp]
  have h : (killX ∘ FreeGroup.of ∘ Fin.succAbove (1 : Fin 2)) =
      fun _ => (1 : FreeGroup (Fin 2)) := by
    funext i
    fin_cases i
    simp [killX]
  rw [h]
  exact lift_const_one w

/-- No rank-one stabilization image is the polluted tuple `((x * y), (y))`. -/
theorem polluted_not_stabilized (R : Relators 1) (g i : Fin 2) :
    AC.stabilize R g i ≠ tup (x2 * y2) y2 := by
  intro h
  fin_cases i
  · fin_cases g
    · have h0 := congrFun h (0 : Fin 2)
      have ht := congrArg FreeGroup.toWord h0
      simp [AC.stabilize, tup, x2, y2, FreeGroup.toWord_mul] at ht
    · have h0 := congrFun h (0 : Fin 2)
      have ht := congrArg FreeGroup.toWord h0
      simp [AC.stabilize, tup, x2, y2, FreeGroup.toWord_mul] at ht
  · fin_cases g
    · have h1 := congrFun h (1 : Fin 2)
      have ht := congrArg FreeGroup.toWord h1
      simp [AC.stabilize, tup, x2, y2, FreeGroup.toWord_mul] at ht
    · have h0 : FreeGroup.map (Fin.succAbove (1 : Fin 2)) (R 0) = x2 * y2 := by
        have h0' := congrFun h (0 : Fin 2)
        simpa [AC.stabilize, tup, Fin.insertNth_apply_below (by decide : (0 : Fin 2) < 1)]
          using h0'
      have hk := congrArg killX h0
      rw [killX_map_succAbove_one] at hk
      simp [killX, x2, y2] at hk

theorem update_standard_eq_tup :
    Function.update (standard 2) 0 (standard 2 0 * standard 2 1) = tup (x2 * y2) y2 := by
  funext i
  fin_cases i
  · simp [tup, standard, x2, y2]
  · simp [tup, standard, y2, Function.update]

/-- One ordinary move takes the standard tuple to the polluted tuple. -/
theorem move_two_standard : Step (standard 2) (tup (x2 * y2) y2) := by
  have hs := Step.mulRight (standard 2) 0 1 (by decide)
  simpa [update_standard_eq_tup] using hs

/-- A rank-two state that is not a stabilization image has no destabilization
step to rank one. -/
theorem no_destabilize_of_not_stabilized {S : Relators 2} {R : Relators 1}
    (h : ∀ (R' : Relators 1) (g i : Fin 2), AC.stabilize R' g i ≠ S) :
    ¬ StableStep ⟨2, S⟩ ⟨1, R⟩ := by
  intro hs
  cases hs with
  | destabilize => exact h _ _ _ rfl

/-- No destabilization step leaves the polluted tuple. -/
theorem polluted_no_destabilize (R : Relators 1) :
    ¬ StableStep ⟨2, tup (x2 * y2) y2⟩ ⟨1, R⟩ :=
  no_destabilize_of_not_stabilized (fun R' g i => polluted_not_stabilized R' g i)

/-! ## 4. Axiom record

The fresh reader runs, on the pinned toolchain:

    #print axioms AC.BranchD3.cohort_partition
    #print axioms AC.BranchD3.cohort_length
    #print axioms AC.BranchD3.cohort_within_budget
    #print axioms AC.BranchD3.cohort_no_refutation
    #print axioms AC.BranchD3.cohort_no_unknown
    #print axioms AC.BranchD3.cohort_positive_overhead
    #print axioms AC.BranchD3.cohort_min_gap
    #print axioms AC.BranchD3.ordinary_solution_stable
    #print axioms AC.BranchD3.move_two_standard
    #print axioms AC.BranchD3.polluted_not_stabilized
    #print axioms AC.BranchD3.polluted_no_destabilize

Each must report a set inside `[propext, Classical.choice, Quot.sound]`. -/

end BranchD3
end AC
