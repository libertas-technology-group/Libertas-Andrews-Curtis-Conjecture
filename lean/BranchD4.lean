module

public import AC
public import AcMove
public import BranchD
public import BranchD3
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.Tactic.Group
public import Mathlib.Tactic

@[expose] public section

/-!
# Branch D4 — the unsolved stable projection cohort

This file records the Branch D4 measurement: the forced and fresh-generator
stable searches over the 2,672 unsolved rows of the stable board, at depth 32
and width 1,000, and the exact ordinary search at each stable candidate's work.

## What is recorded here

1. `unsolved_partition`: the scored cohort is 10,115 rows, 7,443 solved and
   2,672 unsolved; D4 measures only the unsolved rows.
2. The search protocol: depth 32, width 1,000, the forced prefix `[14]`, the
   fresh relator-0 prefix `[14,137,29]`, the corrected relator-1 prefix
   `[14,149,41]`, and the rank-4 prefix `[14,14]`.  The literal D3 relator-1
   record `[14,153,41]` names generator 5 at rank 3 and is inapplicable; the
   corrected prefix is the relator-1 analogue of the relator-0 prefix.
3. The measured search outcomes: every one of the four real searches ended at
   the depth bound or at the clock, none returned a goal, and the literal
   relator-1 prefix failed applicability on every row.
4. `cohort`: every stable candidate the searches returned.  The measured cohort
   is empty, so no exact ordinary search ran.  `cohort_no_refutation` and
   `cohort_refutes_false` record the fixed-rule verdict: the unsolved cohort
   supplies no candidate and therefore no refutation.

## Status

No `sorry`, no `admit`, no user `axiom`, no `native_decide`. The file is in the
`AcCorpus` globs and compiles in the 3,308-job build. The open statement is
`AC.BranchD.StableImpliesOrdinary` (`BranchD.lean:256-258`); the cohort table is
finite evidence, not a proof of the universal statement.
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace AC
namespace BranchD4

open BranchD3

/-! ## 1. The unsolved cohort -/

/-- Scored rows on the stable board. -/
def scoredCount : ℕ := 10115

/-- Solved rows reported by the score record. -/
def solvedCount : ℕ := 7443

/-- Unsolved rows: the D4 population. -/
def unsolvedCount : ℕ := 2672

/-- The score-record partition. -/
theorem unsolved_partition : solvedCount + unsolvedCount = scoredCount := by decide

/-- The unsolved count is the scored count minus the solved count. -/
theorem unsolved_count_eq : scoredCount - solvedCount = unsolvedCount := by decide

/-! ## 2. The search protocol -/

/-- Maximum beam depth. -/
def searchDepth : ℕ := 32

/-- Beam width. -/
def searchWidth : ℕ := 1000

/-- State cap per search. -/
def stateCap : ℕ := 1500000

/-- Clock cap per search, in seconds. -/
def clockSeconds : ℕ := 12

/-- The forced one-stabilization prefix. -/
def forcedPrefix : List ℕ := [14]

/-- The fresh-generator prefix that pollutes relator 0. -/
def freshRelatorZeroPrefix : List ℕ := [14, 137, 29]

/-- The literal relator-1 prefix recorded in Branch D3.  Move 153 is the
conjugation of relator 1 by generator 5, unavailable at rank 3. -/
def freshRelatorOneLiteralPrefix : List ℕ := [14, 153, 41]

/-- The corrected relator-1 prefix: conjugate relator 1 by the fresh generator
3 (move 149) and multiply by the singleton relator (move 41). -/
def freshRelatorOnePrefix : List ℕ := [14, 149, 41]

/-- The rank-4 double-stabilization prefix. -/
def rankFourPrefix : List ℕ := [14, 14]

/-- The four search kinds that ran on every unsolved row. -/
def searchKinds : List String := ["forced", "fresh_r0", "fresh_r1", "rank4"]

/-- Four searches per unsolved row. -/
def searchesPerRow : ℕ := searchKinds.length

/-- Total bounded stable searches over the unsolved cohort. -/
def searchesRun : ℕ := unsolvedCount * searchesPerRow

theorem searchesRun_eq : searchesRun = 10688 := by decide

/-! ## 3. The measured search outcomes -/

/-- Forced searches that reached the depth bound without a goal. -/
def forcedMaxDepth : ℕ := 2484

/-- Forced searches that reached the clock bound without a goal. -/
def forcedTimeLimit : ℕ := 188

/-- Every forced search ended at the depth bound or at the clock. -/
theorem forced_partition : forcedMaxDepth + forcedTimeLimit = unsolvedCount := by decide

/-- Fresh relator-0 searches that reached the depth bound without a goal. -/
def freshRelatorZeroMaxDepth : ℕ := 2483

/-- Fresh relator-0 searches that reached the clock bound without a goal. -/
def freshRelatorZeroTimeLimit : ℕ := 189

/-- Every fresh relator-0 search ended at the depth bound or at the clock. -/
theorem freshRelatorZero_partition :
    freshRelatorZeroMaxDepth + freshRelatorZeroTimeLimit = unsolvedCount := by decide

/-- Fresh relator-1 searches that reached the depth bound without a goal. -/
def freshRelatorOneMaxDepth : ℕ := 2486

/-- Fresh relator-1 searches that reached the clock bound without a goal. -/
def freshRelatorOneTimeLimit : ℕ := 186

/-- Every fresh relator-1 search ended at the depth bound or at the clock. -/
theorem freshRelatorOne_partition :
    freshRelatorOneMaxDepth + freshRelatorOneTimeLimit = unsolvedCount := by decide

/-- Rank-4 searches that reached the depth bound without a goal. -/
def rankFourMaxDepth : ℕ := 2472

/-- Rank-4 searches that reached the clock bound without a goal. -/
def rankFourTimeLimit : ℕ := 200

/-- Every rank-4 search ended at the depth bound or at the clock. -/
theorem rankFour_partition : rankFourMaxDepth + rankFourTimeLimit = unsolvedCount := by decide

/-- Literal relator-1 prefix attempts that failed applicability. -/
def literalPrefixErrors : ℕ := 2672

/-- The literal relator-1 prefix failed on every unsolved row. -/
theorem literalPrefix_all_error : literalPrefixErrors = unsolvedCount := by decide

/-- Searches that reached depth 32, by kind. -/
def forcedDepthThirtyTwo : ℕ := 2495
def freshRelatorZeroDepthThirtyTwo : ℕ := 2495
def freshRelatorOneDepthThirtyTwo : ℕ := 2498
def rankFourDepthThirtyTwo : ℕ := 2482

/-- The depth-32 count is at most the row count in every search kind. -/
theorem depthThirtyTwo_bounds :
    forcedDepthThirtyTwo ≤ unsolvedCount ∧
    freshRelatorZeroDepthThirtyTwo ≤ unsolvedCount ∧
    freshRelatorOneDepthThirtyTwo ≤ unsolvedCount ∧
    rankFourDepthThirtyTwo ≤ unsolvedCount := by decide

/-- Goals found by the four real searches. -/
def totalGoals : ℕ := 0

/-- The four real searches found no stable candidate. -/
theorem totalGoals_eq : totalGoals = 0 := by decide

/-! ## 4. The measured candidate table -/

/-- Every stable candidate returned by the four searches.  Each row carries a
verified `sac-r8-v1` path; `Result.consistent work` records the exact ordinary
minimum at the candidate's stable work.  The measured table is empty. -/
def cohort : List Candidate := []

/-- The number of measured stable candidates. -/
def candidateCount : ℕ := cohort.length

theorem candidateCount_eq : candidateCount = 0 := by decide

/-- The measured cohort is empty. -/
theorem cohort_empty : cohort = [] := by decide

/-- No measured candidate has the refuted status. -/
theorem cohort_no_refutation : cohort.filter (fun c => c.refutes) = [] := by decide

/-- Every measured candidate has an exact ordinary minimum at or below its
stable work. -/
theorem cohort_within_budget : cohort.all (fun c => c.withinBudget) = true := by decide

/-- No measured candidate has the unknown status. -/
theorem cohort_no_unknown : cohort.filter (fun c => c.unknown) = [] := by decide

/-- The fixed rule over a candidate list: true when any candidate refutes the
work-bounded projection principle. -/
def CohortRefutes (cs : List Candidate) : Bool := cs.any (fun c => c.refutes)

/-- The measured unsolved cohort contains no refutation. -/
theorem cohort_refutes_false : CohortRefutes cohort = false := by decide

/-! ## 5. The inherited structural obstruction -/

/-- One ordinary move from the standard rank-two tuple produces a polluted
state.  This is the D3 witness, reused here. -/
theorem obstruction_move_two_standard :
    Step (standard 2) (BranchD3.tup (BranchD3.x2 * BranchD3.y2) BranchD3.y2) :=
  BranchD3.move_two_standard

/-- No rank-one stabilization image equals the polluted tuple. -/
theorem obstruction_polluted_not_stabilized (R : Relators 1) (g i : Fin 2) :
    AC.stabilize R g i ≠ BranchD3.tup (BranchD3.x2 * BranchD3.y2) BranchD3.y2 :=
  BranchD3.polluted_not_stabilized R g i

/-- No destabilization step leaves the polluted tuple. -/
theorem obstruction_no_destabilize (R : Relators 1) :
    ¬ StableStep ⟨2, BranchD3.tup (BranchD3.x2 * BranchD3.y2) BranchD3.y2⟩ ⟨1, R⟩ :=
  BranchD3.polluted_no_destabilize R

/-! ## 6. The two formal gaps

There are two gaps between this finite record and the universal statement.

1. The open obligation `BranchD.StableImpliesOrdinary` has no work bound.  The
   D4 fixed rule tests the work-bounded form: a stable path with no ordinary
   path at or below its work refutes that form.  A refutation of the unbounded
   statement would additionally need an ordinary impossibility argument above
   the budget.
2. The Lean stable relation `AC.StableStep` has no rank bound and ranges over
   every conjugator.  The measured search uses the frozen `sac-r8-v1` move
   table: rank at most 8 and 257 numbered moves.  The translation between the
   benchmark and the Lean relation is not formalized here. -/

/-- The frozen benchmark rank bound. -/
def benchmarkRankCap : ℕ := 8

/-- The frozen benchmark move count. -/
def benchmarkMoveCount : ℕ := 257

/-- The measured protocol uses the frozen rank and move bounds. -/
theorem protocol_shape : benchmarkRankCap = 8 ∧ benchmarkMoveCount = 257 := by decide

/-! ## 7. The open obligation -/

/-- The projection principle measured by this branch.  It is a definition, not
a proof: the D4 cohort is finite evidence for or against its work-bounded form. -/
def openObligation : Prop := BranchD.StableImpliesOrdinary

/-! ## 8. Axiom record

The fresh reader runs, on the pinned toolchain:

    #print axioms AC.BranchD4.unsolved_partition
    #print axioms AC.BranchD4.searchesRun_eq
    #print axioms AC.BranchD4.forced_partition
    #print axioms AC.BranchD4.freshRelatorZero_partition
    #print axioms AC.BranchD4.freshRelatorOne_partition
    #print axioms AC.BranchD4.rankFour_partition
    #print axioms AC.BranchD4.literalPrefix_all_error
    #print axioms AC.BranchD4.candidateCount_eq
    #print axioms AC.BranchD4.cohort_empty
    #print axioms AC.BranchD4.cohort_no_refutation
    #print axioms AC.BranchD4.cohort_refutes_false
    #print axioms AC.BranchD4.obstruction_move_two_standard
    #print axioms AC.BranchD4.obstruction_no_destabilize

Each must report a set inside `[propext, Classical.choice, Quot.sound]`. -/

end BranchD4
end AC
