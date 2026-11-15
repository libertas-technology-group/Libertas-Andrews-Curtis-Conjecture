module

public import AC
public import AcMove
public import BranchD
public import Mathlib.Tactic.Group

@[expose] public section

/-!
# Branch D2 — the stable projection test

This file records one concrete test of `AC.BranchD.StableImpliesOrdinary` and the
general lemma that constructs the test.

## What is proved here

1. `stabilize_update`: updating a stabilized tuple at the image of one old relator
   position is the stabilization of the updated tuple.
2. `Step.stabilize` and `Reachable.stabilize`: every ordinary path lifts through one
   stabilization, so an ordinary solution at rank `n` becomes an ordinary path at
   rank `n + 1` between the two stabilized tuples.
3. `reachable_standard_stable_through_succ`: every ordinarily solvable presentation
   has a stable path to the standard tuple that passes through rank `n + 1`.
4. The candidate `candidate` (the scored presentation `ac-08491`) has an explicit
   twelve-step ordinary path to `standard 2`, and a stable path to the empty
   presentation that passes through rank 3.

The projection principle itself is not proved in general. The file proves the
instantiated implication at the candidate, because the ordinary path is explicit.

## Evidence

The candidate, the stable path, the rank trace, and the ordinary search bound are
recorded in `BRANCH_D2.md`. The file is in the `AcCorpus` globs and compiles in the
3,308-job build.
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace AC
namespace BranchD2

/-! ## 1. Lifting an ordinary path through one stabilization -/

theorem freeGroup_map_inv {α β : Type} (f : α → β) (x : FreeGroup α) :
    FreeGroup.map f x⁻¹ = (FreeGroup.map f x)⁻¹ := by
  change f <$> x⁻¹ = (f <$> x)⁻¹
  rw [FreeGroup.map_inv]

theorem freeGroup_map_mul {α β : Type} (f : α → β) (x y : FreeGroup α) :
    FreeGroup.map f (x * y) = FreeGroup.map f x * FreeGroup.map f y := by
  change f <$> (x * y) = f <$> x * f <$> y
  rw [FreeGroup.map_mul]

theorem stabilize_apply_succAbove {n : ℕ} (R : Relators n) (g i : Fin (n + 1))
    (k : Fin n) :
    AC.stabilize R g i (i.succAbove k) = FreeGroup.map g.succAbove (R k) := by
  simp [AC.stabilize]

theorem stabilize_apply_self {n : ℕ} (R : Relators n) (g i : Fin (n + 1)) :
    AC.stabilize R g i i = FreeGroup.of g := by
  simp [AC.stabilize]

theorem stabilize_update {n : ℕ} (R : Relators n) (g i : Fin (n + 1))
    (k : Fin n) (w : Word n) :
    Function.update (AC.stabilize R g i) (i.succAbove k) (FreeGroup.map g.succAbove w)
      = AC.stabilize (Function.update R k w) g i := by
  funext j
  rcases Fin.eq_self_or_eq_succAbove i j with h | ⟨k', hk'⟩
  · rw [h]
    rw [Function.update_of_ne (Fin.succAbove_ne i k).symm
      (FreeGroup.map g.succAbove w) (AC.stabilize R g i)]
    rw [stabilize_apply_self, stabilize_apply_self]
  · rw [hk']
    by_cases h : k' = k
    · subst h
      rw [Function.update_self, stabilize_apply_succAbove, Function.update_self]
    · rw [Function.update_of_ne (fun hh => h (Fin.succAbove_right_injective (p := i) hh))
        (FreeGroup.map g.succAbove w) (AC.stabilize R g i)]
      rw [stabilize_apply_succAbove, stabilize_apply_succAbove, Function.update_of_ne h]

theorem Step.stabilize {n : ℕ} {R S : Relators n} (h : Step R S) (g i : Fin (n + 1)) :
    Step (AC.stabilize R g i) (AC.stabilize S g i) := by
  cases h with
  | inv k =>
      have hs := Step.inv (AC.stabilize R g i) (i.succAbove k)
      rw [stabilize_apply_succAbove] at hs
      rw [← freeGroup_map_inv] at hs
      rw [stabilize_update] at hs
      exact hs
  | mulRight k l hkl =>
      have hs := Step.mulRight (AC.stabilize R g i) (i.succAbove k) (i.succAbove l)
        (fun hh => hkl (Fin.succAbove_right_injective (p := i) hh))
      rw [stabilize_apply_succAbove, stabilize_apply_succAbove] at hs
      rw [← freeGroup_map_mul] at hs
      rw [stabilize_update] at hs
      exact hs
  | conj k w =>
      have hs := Step.conj (AC.stabilize R g i) (i.succAbove k)
        (FreeGroup.map g.succAbove w)
      rw [stabilize_apply_succAbove] at hs
      rw [← freeGroup_map_inv, ← freeGroup_map_mul, ← freeGroup_map_mul] at hs
      rw [stabilize_update] at hs
      exact hs

theorem Reachable.stabilize {n : ℕ} {R S : Relators n} (h : Reachable R S)
    (g i : Fin (n + 1)) :
    Reachable (AC.stabilize R g i) (AC.stabilize S g i) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (Step.stabilize hstep g i)

/-! ## 2. From an ordinary path to a stable path through the next rank -/

/-- An ordinary solution at rank `n` yields a stable path from `R` to the stabilized
standard tuple at rank `n + 1`: stabilize, run the lifted ordinary path, and keep the
inserted pair in place. The last step of the stable path is not taken here; this is
the excursion through rank `n + 1`. -/
theorem reachable_standard_stable_through_succ {n : ℕ} (R : Relators n)
    (h : Reachable R (standard n)) (g i : Fin (n + 1)) :
    StableReachable ⟨n, R⟩ ⟨n + 1, AC.stabilize (standard n) g i⟩ := by
  have hstep : StableStep ⟨n, R⟩ ⟨n + 1, AC.stabilize R g i⟩ :=
    StableStep.stabilize R g i
  have hlift : Reachable (AC.stabilize R g i) (AC.stabilize (standard n) g i) :=
    Reachable.stabilize h g i
  exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single hstep) hlift.stable

/-! ## 3. The candidate of the scored sample -/

/-! The candidate is `ac-08491`: the rank-2 presentation
`<x, y | y⁻¹x⁻¹ = 1; y⁻²x⁻²y²x = 1>`. The ordinary path is the twelve official
`Step`s `[7,4,12,1,6,4,2,4,1,2,0,4]` of `BRANCH_D2.md`. -/

def x2 : Word 2 := FreeGroup.of 0
def y2 : Word 2 := FreeGroup.of 1

def tup (a b : Word 2) : Relators 2 := fun i => if i = 0 then a else b

@[simp] lemma tup_zero (a b : Word 2) : tup a b 0 = a := by simp [tup]
@[simp] lemma tup_one (a b : Word 2) : tup a b 1 = b := by simp [tup]

lemma update_tup_zero (a b x : Word 2) :
    Function.update (tup a b) 0 x = tup x b := by
  funext i
  by_cases h : i = 0
  · subst h; simp [Function.update, tup]
  · simp [Function.update, tup, h]

lemma update_tup_one (a b x : Word 2) :
    Function.update (tup a b) 1 x = tup a x := by
  funext i
  by_cases h : i = 0
  · subst h; simp [Function.update, tup]
  · have h1 : i = 1 := Fin.eq_one_of_ne_zero i h
    subst h1
    simp [Function.update, tup]

lemma tup_congr {a a' b b' : Word 2} (ha : a = a') (hb : b = b') :
    tup a b = tup a' b' := by
  subst ha; subst hb; rfl

lemma step_conj_zero (a b w : Word 2) :
    Step (tup a b) (tup (w * a * w⁻¹) b) := by
  have hs := Step.conj (tup a b) 0 w
  simpa only [update_tup_zero, tup_zero] using hs

lemma step_conj_one (a b w : Word 2) :
    Step (tup a b) (tup a (w * b * w⁻¹)) := by
  have hs := Step.conj (tup a b) 1 w
  simpa only [update_tup_one, tup_one] using hs

lemma step_mul_one_zero (a b : Word 2) :
    Step (tup a b) (tup a (b * a)) := by
  have hs := Step.mulRight (tup a b) 1 0 (by decide)
  simpa only [update_tup_one, tup_one, tup_zero] using hs

lemma step_mul_zero_one (a b : Word 2) :
    Step (tup a b) (tup (a * b) b) := by
  have hs := Step.mulRight (tup a b) 0 1 (by decide)
  simpa only [update_tup_zero, tup_zero, tup_one] using hs

lemma step_inv_zero (a b : Word 2) : Step (tup a b) (tup a⁻¹ b) := by
  have hs := Step.inv (tup a b) 0
  simpa only [update_tup_zero, tup_zero] using hs

lemma step_inv_one (a b : Word 2) : Step (tup a b) (tup a b⁻¹) := by
  have hs := Step.inv (tup a b) 1
  simpa only [update_tup_one, tup_one] using hs

def A : Word 2 := y2⁻¹ * x2⁻¹
def B : Word 2 := y2⁻¹ * y2⁻¹ * x2⁻¹ * x2⁻¹ * y2 * y2 * x2

def candidate : Relators 2 := tup A B

abbrev s0 : Relators 2 := candidate
abbrev s1 : Relators 2 := tup (x2⁻¹ * y2⁻¹) B
abbrev s2 : Relators 2 := tup (x2⁻¹ * y2⁻¹) (y2⁻¹ * y2⁻¹ * x2⁻¹ * x2⁻¹ * y2)
abbrev s3 : Relators 2 := tup (x2⁻¹ * y2⁻¹) (y2⁻¹ * x2⁻¹ * x2⁻¹)
abbrev s4 : Relators 2 := tup (x2⁻¹ * y2⁻¹) (x2 * x2 * y2)
abbrev s5 : Relators 2 := tup (y2⁻¹ * x2⁻¹) (x2 * x2 * y2)
abbrev s6 : Relators 2 := tup (y2⁻¹ * x2⁻¹) x2
abbrev s7 : Relators 2 := tup (y2⁻¹) x2
abbrev s8 : Relators 2 := tup (y2⁻¹) (x2 * y2⁻¹)
abbrev s9 : Relators 2 := tup (y2⁻¹) (y2 * x2⁻¹)
abbrev s10 : Relators 2 := tup (x2⁻¹) (y2 * x2⁻¹)
abbrev s11 : Relators 2 := tup x2 (y2 * x2⁻¹)
abbrev s12 : Relators 2 := tup x2 y2

theorem candidate_ordinary_chain : Reachable s0 s12 := by
  have h1 : Step s0 s1 := by
    have hs := step_conj_zero A B (x2⁻¹)
    convert hs using 2 <;> (first | rfl | (simp [A]; group) | (simp [A, pow_two]; group) | (simp [A]; norm_num; group) | simp_all)
  have h2 : Step s1 s2 := by
    have hs := step_mul_one_zero (x2⁻¹ * y2⁻¹) B
    have hB : B * (x2⁻¹ * y2⁻¹) = y2⁻¹ * y2⁻¹ * x2⁻¹ * x2⁻¹ * y2 := by
      show (y2⁻¹ * y2⁻¹ * x2⁻¹ * x2⁻¹ * y2 * y2 * x2) * (x2⁻¹ * y2⁻¹)
        = y2⁻¹ * y2⁻¹ * x2⁻¹ * x2⁻¹ * y2
      group
    rw [hB] at hs
    exact hs
  have h3 : Step s2 s3 := by
    have hs := step_conj_one (x2⁻¹ * y2⁻¹) (y2⁻¹ * y2⁻¹ * x2⁻¹ * x2⁻¹ * y2) y2
    convert hs using 2 <;> (first | rfl | group | (rw [pow_two]; group) | (simp [pow_two]; group) | norm_num | simp_all)
  have h4 : Step s3 s4 := by
    have hs := step_inv_one (x2⁻¹ * y2⁻¹) (y2⁻¹ * x2⁻¹ * x2⁻¹)
    convert hs using 2 <;> (first | rfl | group | (rw [pow_two]; group) | (simp [pow_two]; group) | norm_num | simp_all)
  have h5 : Step s4 s5 := by
    have hs := step_conj_zero (x2⁻¹ * y2⁻¹) (x2 * x2 * y2) x2
    convert hs using 2 <;> (first | rfl | group | (rw [pow_two]; group) | (simp [pow_two]; group) | norm_num | simp_all)
  have h6 : Step s5 s6 := by
    have hs := step_mul_one_zero (y2⁻¹ * x2⁻¹) (x2 * x2 * y2)
    convert hs using 2 <;> (first | rfl | group | (rw [pow_two]; group) | (simp [pow_two]; group) | norm_num | simp_all)
  have h7 : Step s6 s7 := by
    have hs := step_mul_zero_one (y2⁻¹ * x2⁻¹) x2
    convert hs using 2 <;> (first | rfl | group | (rw [pow_two]; group) | (simp [pow_two]; group) | norm_num | simp_all)
  have h8 : Step s7 s8 := by
    have hs := step_mul_one_zero (y2⁻¹) x2
    convert hs using 2 <;> (first | rfl | group | (rw [pow_two]; group) | (simp [pow_two]; group) | norm_num | simp_all)
  have h9 : Step s8 s9 := by
    have hs := step_inv_one (y2⁻¹) (x2 * y2⁻¹)
    convert hs using 2 <;> (first | rfl | group | (rw [pow_two]; group) | (simp [pow_two]; group) | norm_num | simp_all)
  have h10 : Step s9 s10 := by
    have hs := step_mul_zero_one (y2⁻¹) (y2 * x2⁻¹)
    convert hs using 2 <;> (first | rfl | group | (rw [pow_two]; group) | (simp [pow_two]; group) | norm_num | simp_all)
  have h11 : Step s10 s11 := by
    have hs := step_inv_zero (x2⁻¹) (y2 * x2⁻¹)
    convert hs using 2 <;> (first | rfl | group | (rw [pow_two]; group) | (simp [pow_two]; group) | norm_num | simp_all)
  have h12 : Step s11 s12 := by
    have hs := step_mul_one_zero x2 (y2 * x2⁻¹)
    convert hs using 2 <;> (first | rfl | group | (rw [pow_two]; group) | (simp [pow_two]; group) | norm_num | simp_all)
  exact Relation.ReflTransGen.tail
    (Relation.ReflTransGen.tail
      (Relation.ReflTransGen.tail
        (Relation.ReflTransGen.tail
          (Relation.ReflTransGen.tail
            (Relation.ReflTransGen.tail
              (Relation.ReflTransGen.tail
                (Relation.ReflTransGen.tail
                  (Relation.ReflTransGen.tail
                    (Relation.ReflTransGen.tail
                      (Relation.ReflTransGen.tail
                        (Relation.ReflTransGen.single h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12

theorem s12_eq_standard : s12 = standard 2 := by
  funext i
  by_cases h : i = 0
  · subst h; rfl
  · have h1 : i = 1 := Fin.eq_one_of_ne_zero i h
    subst h1; rfl

/-- The twelve-step ordinary solution of the candidate. -/
theorem candidate_ordinary : Reachable candidate (standard 2) := by
  have h := candidate_ordinary_chain
  simpa [s12_eq_standard] using h

/-! ## 4. The stable path through rank 3 and the projection instance -/

/-- The stable path reached from the ordinary path by one stabilization: the
ordinary moves act at rank 3 on the first two relators, then the inserted pair is
removed. This is `reachable_standard_stable_through_succ` at the candidate. -/
theorem candidate_stable_through_three :
    StableReachable ⟨2, candidate⟩
      ⟨3, AC.stabilize (standard 2) (Fin.last 2) (Fin.last 2)⟩ :=
  reachable_standard_stable_through_succ candidate candidate_ordinary
    (Fin.last 2) (Fin.last 2)

/-- The candidate reaches the empty presentation stably, and the path passes through
rank 3. The last steps are the two destabilizations of the standard tuple. -/
theorem candidate_stable_empty :
    StableReachable ⟨2, candidate⟩ BranchD.emptyPresentation := by
  have h1 := candidate_stable_through_three
  have h2 : StableStep ⟨3, AC.stabilize (standard 2) (Fin.last 2) (Fin.last 2)⟩
      ⟨2, standard 2⟩ :=
    StableStep.destabilize (standard 2) (Fin.last 2) (Fin.last 2)
  have h3 : StableReachable ⟨2, standard 2⟩ BranchD.emptyPresentation :=
    BranchD.standard_stableReachable_empty 2
  exact Relation.ReflTransGen.trans
    (Relation.ReflTransGen.trans h1 (Relation.ReflTransGen.single h2)) h3

/-- The projection principle holds at the candidate: the ordinary path is explicit,
so the stable hypothesis implies ordinary reachability trivially. This is the
instantiated form of `AC.BranchD.StableImpliesOrdinary`. -/
theorem candidate_projection
    (_h : StableReachable ⟨2, candidate⟩ ⟨2, standard 2⟩) :
    Reachable candidate (standard 2) :=
  candidate_ordinary

/-- The rank witness: a stable path from the candidate to the empty presentation
whose intermediate state has rank 3. -/
theorem candidate_rank_three_witness :
    ∃ P : Presentation, StableReachable ⟨2, candidate⟩ P ∧ P.1 = 3 ∧
      StableReachable P BranchD.emptyPresentation :=
  ⟨_, candidate_stable_through_three, rfl, by
    have h2 : StableStep ⟨3, AC.stabilize (standard 2) (Fin.last 2) (Fin.last 2)⟩
        ⟨2, standard 2⟩ :=
      StableStep.destabilize (standard 2) (Fin.last 2) (Fin.last 2)
    exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single h2)
      (BranchD.standard_stableReachable_empty 2)⟩

/-! ## 5. Axiom record

The fresh reader runs, on the pinned toolchain:

    #print axioms AC.BranchD2.stabilize_update
    #print axioms AC.BranchD2.Step.stabilize
    #print axioms AC.BranchD2.Reachable.stabilize
    #print axioms AC.BranchD2.reachable_standard_stable_through_succ
    #print axioms AC.BranchD2.candidate_ordinary
    #print axioms AC.BranchD2.candidate_stable_through_three
    #print axioms AC.BranchD2.candidate_stable_empty
    #print axioms AC.BranchD2.candidate_projection

Each must report a set inside `[propext, Classical.choice, Quot.sound]`. -/

end BranchD2
end AC
