import BranchC3

/-!
# Branch C4: the targeted bidirectional PSL(2,ℤ) orbit test at length 20

This file continues Branch C3.  C3 ran a full breadth-first enumeration of the
bounded group AC orbit of `(a,b)` in `G = C₂ * C₃` and left six sample rows
unknown because their cyclic cores have a component longer than the bound.
C4 replaces the full enumeration with a targeted bidirectional search:

* a forward side from the standard pair, using the official group AC moves;
* a backward side from the row's core pair, using the reverse of each move;
* a meeting point `m` yields a forward path `standard → m → target`, and the
  backward half is a forward path because every backward move is the converse
  of a forward move.

The soundness theorem `meeting_sound` is proved here.  The computational run is
an external exact enumeration recorded in `BRANCH_C4.md`; the records below are
data, not kernel-checked theorems.  The file also proves that the unbounded
group AC relation is symmetric, so an inside verdict in the forward direction
is the same relation that an Andrews–Curtis path would produce in the reverse
direction.

## Status

No `sorry`, no `admit`, no user `axiom`, no `native_decide`. The file is in the
`AcCorpus` globs and compiles in the 3,308-job build under
`leanprover/lean4:v4.29.1` with Mathlib `5e932f97…`.
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace AC
namespace BranchC4

open BranchC3

/-! ## 1. The backward move set -/

/-- The reverse of a group AC move.  A backward step from `g` to `h` means that
`h` is a predecessor of `g` under one official forward move: `h → g` is a
single `GroupACStep`. -/
inductive GroupACBackStep (G : Type*) [Group G] : G × G → G × G → Prop
  | inv (g : G × G) (i : Fin 2) :
      GroupACBackStep G g (pairUpdate g i (pairGet g i)⁻¹)
  | mulRightInv (g : G × G) (i j : Fin 2) (hij : i ≠ j) :
      GroupACBackStep G g (pairUpdate g i (pairGet g i * (pairGet g j)⁻¹))
  | conj (g : G × G) (i : Fin 2) (w : G) :
      GroupACBackStep G g (pairUpdate g i (w * pairGet g i * w⁻¹))

section BackStep

variable {G : Type*} [Group G]

/-- A forward inversion is its own reverse. -/
theorem backStep_inv (p : G × G) (i : Fin 2) :
    GroupACBackStep G (pairUpdate p i (pairGet p i)⁻¹) p := by
  have hh : pairUpdate (pairUpdate p i (pairGet p i)⁻¹) i
      (pairGet (pairUpdate p i (pairGet p i)⁻¹) i)⁻¹ = p := by
    fin_cases i <;> simp [pairUpdate, pairGet]
  have h := GroupACBackStep.inv (G := G) (pairUpdate p i (pairGet p i)⁻¹) i
  rwa [hh] at h

/-- A forward right multiplication is reversed by inverting the other
component, multiplying, and inverting back. -/
theorem backStep_mulRight (p : G × G) (i j : Fin 2) (hij : i ≠ j) :
    GroupACBackStep G (pairUpdate p i (pairGet p i * pairGet p j)) p := by
  have hh : pairUpdate (pairUpdate p i (pairGet p i * pairGet p j)) i
      (pairGet (pairUpdate p i (pairGet p i * pairGet p j)) i *
       (pairGet (pairUpdate p i (pairGet p i * pairGet p j)) j)⁻¹) = p := by
    fin_cases i <;> fin_cases j <;> simp_all [pairUpdate, pairGet, mul_assoc]
  have h := GroupACBackStep.mulRightInv (G := G)
    (pairUpdate p i (pairGet p i * pairGet p j)) i j hij
  rwa [hh] at h

/-- A forward conjugation is reversed by conjugating by the inverse. -/
theorem backStep_conj (p : G × G) (i : Fin 2) (w : G) :
    GroupACBackStep G (pairUpdate p i (w * pairGet p i * w⁻¹)) p := by
  have hh : pairUpdate (pairUpdate p i (w * pairGet p i * w⁻¹)) i
      (w⁻¹ * pairGet (pairUpdate p i (w * pairGet p i * w⁻¹)) i * (w⁻¹)⁻¹) = p := by
    fin_cases i <;> simp [pairUpdate, pairGet, mul_assoc]
  have h := GroupACBackStep.conj (G := G)
    (pairUpdate p i (w * pairGet p i * w⁻¹)) i w⁻¹
  rwa [hh] at h

/-- Every forward move is a backward move in the reverse direction. -/
theorem backStep_of_step {g h : G × G} (hs : GroupACStep G g h) :
    GroupACBackStep G h g := by
  cases hs with
  | inv i => exact backStep_inv g i
  | mulRight i j hij => exact backStep_mulRight g i j hij
  | conj i w => exact backStep_conj g i w

/-- Every backward move is one forward move in the reverse direction. -/
theorem step_of_backStep {g h : G × G} (hs : GroupACBackStep G g h) :
    GroupACStep G h g := by
  cases hs with
  | inv i =>
      have hh : pairUpdate (pairUpdate g i (pairGet g i)⁻¹) i
          (pairGet (pairUpdate g i (pairGet g i)⁻¹) i)⁻¹ = g := by
        fin_cases i <;> simp [pairUpdate, pairGet]
      have hs : GroupACStep G (pairUpdate g i (pairGet g i)⁻¹)
          (pairUpdate (pairUpdate g i (pairGet g i)⁻¹) i
            (pairGet (pairUpdate g i (pairGet g i)⁻¹) i)⁻¹) :=
        GroupACStep.inv (G := G) (pairUpdate g i (pairGet g i)⁻¹) i
      simpa [hh] using hs
  | mulRightInv i j hij =>
      have hh : pairUpdate (pairUpdate g i (pairGet g i * (pairGet g j)⁻¹)) i
          (pairGet (pairUpdate g i (pairGet g i * (pairGet g j)⁻¹)) i *
           pairGet (pairUpdate g i (pairGet g i * (pairGet g j)⁻¹)) j) = g := by
        fin_cases i <;> fin_cases j <;> simp_all [pairUpdate, pairGet, mul_assoc]
      have hs : GroupACStep G (pairUpdate g i (pairGet g i * (pairGet g j)⁻¹))
          (pairUpdate (pairUpdate g i (pairGet g i * (pairGet g j)⁻¹)) i
            (pairGet (pairUpdate g i (pairGet g i * (pairGet g j)⁻¹)) i *
             pairGet (pairUpdate g i (pairGet g i * (pairGet g j)⁻¹)) j)) :=
        GroupACStep.mulRight (G := G) (pairUpdate g i (pairGet g i * (pairGet g j)⁻¹)) i j hij
      simpa [hh] using hs
  | conj i w =>
      have hh : pairUpdate (pairUpdate g i (w * pairGet g i * w⁻¹)) i
          (w⁻¹ * pairGet (pairUpdate g i (w * pairGet g i * w⁻¹)) i * w) = g := by
        fin_cases i <;> simp [pairUpdate, pairGet, mul_assoc]
      have hs : GroupACStep G (pairUpdate g i (w * pairGet g i * w⁻¹))
          (pairUpdate (pairUpdate g i (w * pairGet g i * w⁻¹)) i
            (w⁻¹ * pairGet (pairUpdate g i (w * pairGet g i * w⁻¹)) i * w)) := by
        simpa only [inv_inv] using
          (GroupACStep.conj (G := G) (pairUpdate g i (w * pairGet g i * w⁻¹)) i w⁻¹)
      simpa [hh] using hs

end BackStep

/-! ## 2. Symmetry of the unbounded group AC relation -/

section Symmetry

variable {G : Type*} [Group G]

/-- One forward move is reversible by at most three forward moves. -/
theorem step_reachable_symm {g h : G × G} (hs : GroupACStep G g h) :
    GroupACReachable G h g := by
  cases hs with
  | inv i =>
      let h0 := pairUpdate g i (pairGet g i)⁻¹
      have hh : pairUpdate h0 i (pairGet h0 i)⁻¹ = g := by
        dsimp [h0, pairUpdate, pairGet]
        fin_cases i <;> simp [pairUpdate, pairGet]
      have s1 : GroupACStep G h0 g := by
        simpa [hh] using GroupACStep.inv (G := G) h0 i
      exact Relation.ReflTransGen.single s1
  | mulRight i j hij =>
      let h0 := pairUpdate g i (pairGet g i * pairGet g j)
      let h1 := pairUpdate h0 j (pairGet h0 j)⁻¹
      let h2 := pairUpdate h1 i (pairGet h1 i * pairGet h1 j)
      have s1 : GroupACStep G h0 h1 := GroupACStep.inv h0 j
      have s2 : GroupACStep G h1 h2 := GroupACStep.mulRight h1 i j hij
      have hh : pairUpdate h2 j (pairGet h2 j)⁻¹ = g := by
        dsimp [h0, h1, h2, pairUpdate, pairGet]
        fin_cases i <;> fin_cases j <;> simp_all [pairUpdate, pairGet, mul_assoc]
      have s3 : GroupACStep G h2 g := by
        simpa [hh] using GroupACStep.inv (G := G) h2 j
      exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail (Relation.ReflTransGen.single s1) s2) s3
  | conj i w =>
      let h0 := pairUpdate g i (w * pairGet g i * w⁻¹)
      have hh : pairUpdate h0 i (w⁻¹ * pairGet h0 i * w) = g := by
        dsimp [h0, pairUpdate, pairGet]
        fin_cases i <;> simp [pairUpdate, pairGet, mul_assoc]
      have s1 : GroupACStep G h0 g := by
        simpa only [inv_inv, hh] using GroupACStep.conj (G := G) h0 i w⁻¹
      exact Relation.ReflTransGen.single s1

/-- The unbounded group AC relation is symmetric. -/
theorem groupACReachable_symm {g h : G × G} (hpath : GroupACReachable G g h) :
    GroupACReachable G h g := by
  induction hpath with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact (step_reachable_symm hstep).trans ih

end Symmetry

/-! ## 3. Bounded backward reachability and the meet theorem -/

/-- A bounded backward step is the converse of a bounded forward step. -/
noncomputable def BoundedBackStep (L : ℕ) (g h : PSL × PSL) : Prop :=
  BoundedStep L h g

/-- Reachability by bounded backward steps. -/
noncomputable def BoundedBackReachable (L : ℕ) : PSL × PSL → PSL × PSL → Prop :=
  Relation.ReflTransGen (BoundedBackStep L)

/-- A bounded backward path is the reverse of a bounded forward path. -/
theorem boundedBackReachable_iff {L : ℕ} {g h : PSL × PSL} :
    BoundedBackReachable L g h ↔ BoundedReachable L h g :=
  Relation.reflTransGen_swap

/-- A meeting between a forward path from `s` and a backward path from `t`
produces a forward path from `s` to `t`. -/
theorem meeting_sound {L : ℕ} {s m t : PSL × PSL}
    (hf : BoundedReachable L s m) (hb : BoundedBackReachable L t m) :
    BoundedReachable L s t :=
  hf.trans (boundedBackReachable_iff.mp hb)

/-- A meeting produces an unbounded group AC path in the forward direction. -/
theorem meeting_groupACReachable {L : ℕ} {s m t : PSL × PSL}
    (hf : BoundedReachable L s m) (hb : BoundedBackReachable L t m) :
    GroupACReachable PSL s t :=
  boundedReachable_imp_groupACReachable (meeting_sound hf hb)

/-- A meeting produces the reverse unbounded group AC path as well, by symmetry.
This is the direction an Andrews–Curtis path would use. -/
theorem meeting_groupACReachable_reverse {L : ℕ} {s m t : PSL × PSL}
    (hf : BoundedReachable L s m) (hb : BoundedBackReachable L t m) :
    GroupACReachable PSL t s :=
  groupACReachable_symm (meeting_groupACReachable hf hb)

/-! ## 4. The recorded length-20 run -/

/-- The three-way verdict used by the C4 run. -/
inductive C4Verdict
  | inside
  | outside
  | unknown
deriving Repr, DecidableEq

/-- One row of the six-row table.  `distance` is the forward BFS distance from
the standard pair; it is zero for a row whose core does not fit the ball. -/
structure RowRecord where
  id : String
  verdict : C4Verdict
  distance : ℕ
  coreFirst : ℕ
  coreSecond : ℕ
deriving Repr, DecidableEq

/-- The six rows left unknown by Branch C3, tested at word length 20.  The
verdicts are the output of the external exact enumeration recorded in
`BRANCH_C4.md` §3; this is a record, not a kernel-checked theorem. -/
def c4Rows : List RowRecord :=
  [ ⟨"ac-00057", .inside, 6, 6, 20⟩
  , ⟨"ac-00063", .unknown, 0, 1, 26⟩
  , ⟨"ac-00074", .unknown, 0, 2, 22⟩
  , ⟨"ac-00087", .unknown, 0, 1, 22⟩
  , ⟨"ac-00126", .unknown, 0, 4, 22⟩
  , ⟨"ac-00184", .inside, 8, 6, 20⟩
  ]

/-- The recorded count triple at `L = 20`: 2 inside, 0 outside, 4 unknown. -/
def c4Counts : OrbitCounts :=
  { inside := 2, outside := 0, unknown := 4 }

/-- The ball at `L = 20` has 7,162 elements. -/
def ballSize20 : ℕ := 7162

/-- The pair state space at `L = 20` is `7162² = 51,294,244`. -/
def pairSpace20 : ℕ := 51294244

/-- The forward orbit at `L = 20` has 30,630,300 pairs. -/
def orbitSize20 : ℕ := 30630300

/-- The recorded count triple of the escalation at `L = 22`:
5 inside, 0 outside, 1 unknown. -/
def c4EscalationCounts : OrbitCounts :=
  { inside := 5, outside := 0, unknown := 1 }

/-- The outside count is zero, so no row of the six is a separating candidate
at the assigned bound. -/
theorem c4_no_separation : c4Counts.outside = 0 := rfl

/-- Every inside row carries a positive recorded distance. -/
theorem c4_inside_positives :
    (c4Rows.filter (fun r => r.verdict == C4Verdict.inside)).map RowRecord.distance
      = [6, 8] := rfl

/-! ## 5. The BS(2,3) fallback record -/

/-- One row of the BS(2,3) fallback.  The lengths are the letter lengths of the
normal forms of the two images.  The verdict is `unknown` because the image lies
outside every ball small enough to enumerate completely. -/
structure BSRowRecord where
  id : String
  firstLength : ℕ
  secondLength : ℕ
  verdict : C4Verdict
deriving Repr, DecidableEq

/-- The six BS(2,3) images and their fallback verdicts.  The normal form is
Britton normal form; its verification record is in `BRANCH_C4.md` §5. -/
def bsRows : List BSRowRecord :=
  [ ⟨"ac-00057", 15, 42, .unknown⟩
  , ⟨"ac-00063", 9, 29, .unknown⟩
  , ⟨"ac-00074", 9, 69, .unknown⟩
  , ⟨"ac-00087", 9, 36, .unknown⟩
  , ⟨"ac-00126", 42, 111, .unknown⟩
  , ⟨"ac-00184", 26, 68, .unknown⟩
  ]

/-- The fallback count triple: no row is decided at the tractable BS(2,3)
bound. -/
def bsCounts : OrbitCounts :=
  { inside := 0, outside := 0, unknown := 6 }

/-- The BS(2,3) ball at letter length 6 has 440 elements. -/
def bsBallSize6 : ℕ := 440

/-- The BS(2,3) orbit of `(a,t)` at letter length 6 has 119,743 pairs. -/
def bsOrbitSize6 : ℕ := 119743

/-- No BS(2,3) fallback verdict is outside at the tested bound. -/
theorem bs_no_separation : bsCounts.outside = 0 := rfl

end BranchC4
end AC
