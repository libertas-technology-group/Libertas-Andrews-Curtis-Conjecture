import AC
import AcInvariant
import Mathlib.Data.Finset.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Group

/-!
# The proof attempt against `AC.Conjecture` and `¬ AC.Conjecture`

Two routes are written here.

The proof route reduces `AC.Conjecture` to two inputs: every trivial presentation reaches
the finite set of signed permutations (`hterm`), and every signed permutation reaches the
ordered standard tuple (`hcanon`). `conjecture_of_terminal_and_canonical` composes the two
and is complete. The first input is the search problem. The second is closed here as
gap G3: `reachable_swap` derives a transposition of two relators from the three official
moves, `permutation_reachable_standard` assembles an arbitrary permutation from those
transpositions, and `reachable_flip` removes the signs.

The disproof route separates a presentation from the standard tuple by the span invariant
of `AcInvariant`. `counterexample_of_span_separation` turns a span difference into a
counterexample and is complete. `span_route_exhausted` records that the required
span difference is inconsistent with gap G1, so this route produces no counterexample.

`presents_of_step` (gap G4, closed) records the obstruction that closes the class of
group-theoretic invariants: every official step preserves the presented group. It rests on
three helper lemmas showing that inverting, right-multiplying, and conjugating one relator
leave the normal closure of the relator set unchanged. A quantity that is a function of the
presented group takes one value on the class of trivial presentations, and it cannot
separate a member of that class from the standard tuple. `group_invariant_cannot_separate`
is the logical step that consumes that constant value.

The decreasing-measure branch is closed in `AcInvariant.no_strictly_decreasing_measure`,
and it is not restated here.

The fresh-reader commands for the trusted base are recorded in `PROOF_STRATEGY.md`
section 7. Each must report a trusted base inside `[propext, Classical.choice, Quot.sound]`.
A listing that contains the placeholder constant, or any assumption outside that set, is a
defect.

This file contains no unfinished proof step, no placeholder tactic, and no user-declared
assumption. The proof was written against the mathlib sources at the revision pinned in
`lake-manifest.json`.

The pinned toolchain `leanprover/lean4:v4.29.1` is installed on this machine, and
`lake build AcCorpus` ran against mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6`
with exit code 0. A fresh reader re-runs the build and the `#print axioms` commands;
this note is not a signature.
-/

namespace AC
namespace ProofAttempt

variable {n : ℕ}

/-! ## 1. The terminal set -/

/-- A signed permutation: every relator is a signed generator, and the generator map is a
bijection. This is the eight-element terminal set at rank two, and its rank-`n` analogue. -/
def IsSignedPermutation (R : Relators n) : Prop :=
  ∃ σ : Fin n → Fin n, Function.Bijective σ ∧
    ∃ ε : Fin n → Bool,
      ∀ i, R i = if ε i then FreeGroup.of (σ i) else (FreeGroup.of (σ i))⁻¹

theorem standard_isSignedPermutation : IsSignedPermutation (standard n) := by
  refine ⟨id, Function.bijective_id, fun _ => true, ?_⟩
  intro i
  simp [standard]

/-! ## 2. The proof route -/

/-- The reduction: terminal reachability plus canonicalisation gives `AC.Conjecture`. -/
theorem conjecture_of_terminal_and_canonical
    (hterm : ∀ (n : ℕ), 0 < n → ∀ R : Relators n, PresentsTrivialGroup R →
      ∃ T : Relators n, IsSignedPermutation T ∧ Reachable R T)
    (hcanon : ∀ (n : ℕ), 0 < n → ∀ T : Relators n,
      IsSignedPermutation T → Reachable T (standard n)) :
    Conjecture := by
  intro n hn R hR
  obtain ⟨T, hT, hRT⟩ := hterm n hn R hR
  exact Relation.ReflTransGen.trans hRT (hcanon n hn T hT)

/-! ## 3. Tuple helpers for the relator transposition

`pairTuple R i j x y` overwrites positions `i` and `j` of `R` with `x` and `y`. The two
update lemmas below move a fresh update at `i` or at `j` into that representation, and the
two projection lemmas read the stored values back. `reachable_swap` is then a chain of
`pairTuple` states. -/

/-- The tuple obtained by overwriting positions `i` and `j` with `x` and `y`. -/
def pairTuple (R : Relators n) (i j : Fin n) (x y : Word n) : Relators n :=
  Function.update (Function.update R i x) j y

/-- The tuple of generators induced by a function on positions. -/
def tupleOf (f : Fin n → Fin n) : Relators n :=
  fun i => FreeGroup.of (f i)

lemma pairTuple_fst (R : Relators n) (i j : Fin n) (hij : i ≠ j) (x y : Word n) :
    pairTuple R i j x y i = x := by
  simp only [pairTuple]
  rw [Function.update_of_ne hij y (Function.update R i x)]
  rw [Function.update_self]

lemma pairTuple_snd (R : Relators n) (i j : Fin n) (x y : Word n) :
    pairTuple R i j x y j = y := by
  simp only [pairTuple]
  rw [Function.update_self]

lemma pairTuple_update_fst (R : Relators n) (i j : Fin n) (hij : i ≠ j)
    (x y z : Word n) :
    Function.update (pairTuple R i j x y) i z = pairTuple R i j z y := by
  simp only [pairTuple]
  rw [Function.update_comm (a := j) (b := i) (Ne.symm hij) y z
    (Function.update R i x)]
  rw [Function.update_idem]

lemma pairTuple_update_snd (R : Relators n) (i j : Fin n) (x y z : Word n) :
    Function.update (pairTuple R i j x y) j z = pairTuple R i j x z := by
  simp only [pairTuple]
  rw [Function.update_idem]

lemma pairTuple_self (R : Relators n) (i j : Fin n) :
    pairTuple R i j (R i) (R j) = R := by
  simp [pairTuple]

/-! ## 4. The transposition `reachable_swap`

For distinct positions `i j` the six macros

    (a,b) → (ab,b) → (ab,b⁻¹) → (ab,a) → (ab,a⁻¹) → (b,a⁻¹) → (b,a)

carry `(a,b)` to `(b,a)`. The third and fifth macros are left multiplications, each
expanded into a right multiplication followed by a conjugation with the partner relator.
The chain below is eight official `Step`s. -/

/-- G3, closed: two relators at distinct positions can be swapped by official moves. -/
theorem reachable_swap (R : Relators n) {i j : Fin n} (hij : i ≠ j) :
    Reachable R (Function.update (Function.update R i (R j)) j (R i)) := by
  classical
  have h01 : Reachable (pairTuple R i j (R i) (R j))
      (pairTuple R i j (R i * R j) (R j)) := by
    refine Relation.ReflTransGen.single ?_
    have hs := Step.mulRight (pairTuple R i j (R i) (R j)) i j hij
    have hi : pairTuple R i j (R i) (R j) i = R i :=
      pairTuple_fst R i j hij (R i) (R j)
    have hj : pairTuple R i j (R i) (R j) j = R j :=
      pairTuple_snd R i j (R i) (R j)
    rw [hi, hj] at hs
    rw [pairTuple_update_fst R i j hij (R i) (R j) (R i * R j)] at hs
    exact hs
  have h12 : Reachable (pairTuple R i j (R i * R j) (R j))
      (pairTuple R i j (R i * R j) ((R j)⁻¹)) := by
    refine Relation.ReflTransGen.single ?_
    have hs := Step.inv (pairTuple R i j (R i * R j) (R j)) j
    have hj : pairTuple R i j (R i * R j) (R j) j = R j :=
      pairTuple_snd R i j (R i * R j) (R j)
    rw [hj] at hs
    rw [pairTuple_update_snd R i j (R i * R j) (R j) ((R j)⁻¹)] at hs
    exact hs
  have h2a : Reachable (pairTuple R i j (R i * R j) ((R j)⁻¹))
      (pairTuple R i j (R i * R j) ((R j)⁻¹ * (R i * R j))) := by
    refine Relation.ReflTransGen.single ?_
    have hs := Step.mulRight (pairTuple R i j (R i * R j) ((R j)⁻¹)) j i
      (Ne.symm hij)
    have hi : pairTuple R i j (R i * R j) ((R j)⁻¹) i = R i * R j :=
      pairTuple_fst R i j hij (R i * R j) ((R j)⁻¹)
    have hj : pairTuple R i j (R i * R j) ((R j)⁻¹) j = (R j)⁻¹ :=
      pairTuple_snd R i j (R i * R j) ((R j)⁻¹)
    rw [hi, hj] at hs
    rw [pairTuple_update_snd R i j (R i * R j) ((R j)⁻¹)
      ((R j)⁻¹ * (R i * R j))] at hs
    exact hs
  have ha3 : Reachable (pairTuple R i j (R i * R j) ((R j)⁻¹ * (R i * R j)))
      (pairTuple R i j (R i * R j) (R i)) := by
    refine Relation.ReflTransGen.single ?_
    have hs := Step.conj (pairTuple R i j (R i * R j) ((R j)⁻¹ * (R i * R j))) j
      (R i * R j)
    have hj : pairTuple R i j (R i * R j) ((R j)⁻¹ * (R i * R j)) j =
        (R j)⁻¹ * (R i * R j) :=
      pairTuple_snd R i j (R i * R j) ((R j)⁻¹ * (R i * R j))
    rw [hj] at hs
    rw [pairTuple_update_snd R i j (R i * R j) ((R j)⁻¹ * (R i * R j))
      ((R i * R j) * ((R j)⁻¹ * (R i * R j)) * (R i * R j)⁻¹)] at hs
    have hgrp : (R i * R j) * ((R j)⁻¹ * (R i * R j)) * (R i * R j)⁻¹ = R i := by
      group
    rw [hgrp] at hs
    exact hs
  have h34 : Reachable (pairTuple R i j (R i * R j) (R i))
      (pairTuple R i j (R i * R j) ((R i)⁻¹)) := by
    refine Relation.ReflTransGen.single ?_
    have hs := Step.inv (pairTuple R i j (R i * R j) (R i)) j
    have hj : pairTuple R i j (R i * R j) (R i) j = R i :=
      pairTuple_snd R i j (R i * R j) (R i)
    rw [hj] at hs
    rw [pairTuple_update_snd R i j (R i * R j) (R i) ((R i)⁻¹)] at hs
    exact hs
  have h4a : Reachable (pairTuple R i j (R i * R j) ((R i)⁻¹))
      (pairTuple R i j ((R i * R j) * (R i)⁻¹) ((R i)⁻¹)) := by
    refine Relation.ReflTransGen.single ?_
    have hs := Step.mulRight (pairTuple R i j (R i * R j) ((R i)⁻¹)) i j hij
    have hi : pairTuple R i j (R i * R j) ((R i)⁻¹) i = R i * R j :=
      pairTuple_fst R i j hij (R i * R j) ((R i)⁻¹)
    have hj : pairTuple R i j (R i * R j) ((R i)⁻¹) j = (R i)⁻¹ :=
      pairTuple_snd R i j (R i * R j) ((R i)⁻¹)
    rw [hi, hj] at hs
    rw [pairTuple_update_fst R i j hij (R i * R j) ((R i)⁻¹)
      ((R i * R j) * (R i)⁻¹)] at hs
    exact hs
  have ha5 : Reachable (pairTuple R i j ((R i * R j) * (R i)⁻¹) ((R i)⁻¹))
      (pairTuple R i j (R j) ((R i)⁻¹)) := by
    refine Relation.ReflTransGen.single ?_
    have hs := Step.conj (pairTuple R i j ((R i * R j) * (R i)⁻¹) ((R i)⁻¹)) i
      ((R i)⁻¹)
    have hi : pairTuple R i j ((R i * R j) * (R i)⁻¹) ((R i)⁻¹) i =
        (R i * R j) * (R i)⁻¹ :=
      pairTuple_fst R i j hij ((R i * R j) * (R i)⁻¹) ((R i)⁻¹)
    rw [hi] at hs
    rw [pairTuple_update_fst R i j hij ((R i * R j) * (R i)⁻¹) ((R i)⁻¹)
      ((R i)⁻¹ * ((R i * R j) * (R i)⁻¹) * ((R i)⁻¹)⁻¹)] at hs
    have hgrp : (R i)⁻¹ * ((R i * R j) * (R i)⁻¹) * ((R i)⁻¹)⁻¹ = R j := by
      group
    rw [hgrp] at hs
    exact hs
  have h56 : Reachable (pairTuple R i j (R j) ((R i)⁻¹))
      (pairTuple R i j (R j) (R i)) := by
    refine Relation.ReflTransGen.single ?_
    have hs := Step.inv (pairTuple R i j (R j) ((R i)⁻¹)) j
    have hj : pairTuple R i j (R j) ((R i)⁻¹) j = (R i)⁻¹ :=
      pairTuple_snd R i j (R j) ((R i)⁻¹)
    rw [hj] at hs
    rw [pairTuple_update_snd R i j (R j) ((R i)⁻¹) (((R i)⁻¹)⁻¹)] at hs
    rw [inv_inv] at hs
    exact hs
  have hchain : Reachable (pairTuple R i j (R i) (R j))
      (pairTuple R i j (R j) (R i)) :=
    Relation.ReflTransGen.trans h01
      (Relation.ReflTransGen.trans h12
        (Relation.ReflTransGen.trans (Relation.ReflTransGen.trans h2a ha3)
          (Relation.ReflTransGen.trans h34
            (Relation.ReflTransGen.trans (Relation.ReflTransGen.trans h4a ha5)
              h56))))
  have hstart : pairTuple R i j (R i) (R j) = R := pairTuple_self R i j
  rw [hstart] at hchain
  simpa [pairTuple] using hchain

/-- The same transposition stated for a permutation tuple: swapping the entries of `f` at
the two positions `p` and `q` applies `f` after the swap. -/
lemma reachable_swap_perm (f : Equiv.Perm (Fin n)) {p q : Fin n} (hpq : p ≠ q) :
    Reachable (tupleOf f) (tupleOf (fun i => f (Equiv.swap p q i))) := by
  classical
  have hsw := reachable_swap (R := tupleOf f) hpq
  have heq : Function.update (Function.update (tupleOf f) p ((tupleOf f) q)) q
        ((tupleOf f) p) = tupleOf (fun i => f (Equiv.swap p q i)) := by
    funext i
    by_cases hip : i = p
    · rw [hip]
      rw [Function.update_of_ne hpq ((tupleOf f) p)
        (Function.update (tupleOf f) p ((tupleOf f) q))]
      rw [Function.update_self]
      simp [tupleOf, Equiv.swap_apply_left]
    · by_cases hiq : i = q
      · rw [hiq]
        rw [Function.update_self]
        simp [tupleOf, Equiv.swap_apply_right]
      · rw [Function.update_of_ne hiq ((tupleOf f) p)
          (Function.update (tupleOf f) p ((tupleOf f) q))]
        rw [Function.update_of_ne hip ((tupleOf f) q) (tupleOf f)]
        simp [tupleOf, Equiv.swap_apply_of_ne_of_ne hip hiq]
  rw [heq] at hsw
  exact hsw

/-! ## 5. The permutation assembly

`Equiv.Perm.swap_induction_on'` inducts over a list of transpositions in the
right-multiplication form. The step applies `reachable_swap_perm` at the permutation
`g * Equiv.swap x y`; `Equiv.swap_apply_self` and `Equiv.Perm.mul_apply` identify the
resulting tuple with `tupleOf g`. -/

/-- The permutation assembly: every permuted generator tuple reaches the standard tuple. -/
theorem permutation_reachable_standard (f : Equiv.Perm (Fin n)) :
    Reachable (tupleOf f) (standard n) := by
  classical
  refine Equiv.Perm.swap_induction_on'
    (motive := fun f => Reachable (tupleOf f) (standard n)) f ?base ?step
  · show Reachable (tupleOf (1 : Equiv.Perm (Fin n))) (standard n)
    have h1 : tupleOf (1 : Equiv.Perm (Fin n)) = standard n := by
      funext i
      simp [tupleOf, standard]
    rw [h1]
    exact Relation.ReflTransGen.refl
  · intro g x y hxy ih
    have hswap := reachable_swap_perm (g * Equiv.swap x y) (p := x) (q := y) hxy
    have htarget : tupleOf (fun i => (g * Equiv.swap x y) (Equiv.swap x y i)) =
        tupleOf g := by
      funext i
      simp [tupleOf, Equiv.Perm.mul_apply, Equiv.swap_apply_self]
    rw [htarget] at hswap
    exact Relation.ReflTransGen.trans hswap ih

/-! ## 6. Sign removal

`reachable_flip` toggles the sign of one entry at a time. Applied to the set of positions
whose sign is negative, it carries a signed permutation to its underlying generator
permutation. -/

/-- Toggling the signs at the positions in a finite set is reachable. -/
lemma reachable_flip (R : Relators n) (s : Finset (Fin n)) :
    Reachable R (fun i => if i ∈ s then (R i)⁻¹ else R i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h : (fun i => if i ∈ (∅ : Finset (Fin n)) then (R i)⁻¹ else R i) = R := by
        funext i
        simp
      rw [h]
      exact Relation.ReflTransGen.refl
  | insert a s ha ih =>
      have hstep : Step (fun i => if i ∈ s then (R i)⁻¹ else R i)
          (Function.update (fun i => if i ∈ s then (R i)⁻¹ else R i) a
            ((fun i => if i ∈ s then (R i)⁻¹ else R i) a)⁻¹) :=
        Step.inv (fun i => if i ∈ s then (R i)⁻¹ else R i) a
      have heq :
          Function.update (fun i => if i ∈ s then (R i)⁻¹ else R i) a
              ((fun i => if i ∈ s then (R i)⁻¹ else R i) a)⁻¹
            = (fun i => if i ∈ insert a s then (R i)⁻¹ else R i) := by
        funext i
        by_cases hia : i = a
        · rw [hia]
          rw [Function.update_self]
          simp [ha, Finset.mem_insert]
        · rw [Function.update_of_ne hia]
          simp [Finset.mem_insert, hia]
      rw [heq] at hstep
      exact Relation.ReflTransGen.trans ih (Relation.ReflTransGen.single hstep)

/-- G3, closed: every signed permutation reaches the ordered standard tuple. -/
theorem signedPermutation_reachable_standard (n : ℕ) (T : Relators n)
    (hT : IsSignedPermutation T) : Reachable T (standard n) := by
  classical
  obtain ⟨σ, hσ, ε, hε⟩ := hT
  set f : Equiv.Perm (Fin n) := Equiv.ofBijective σ hσ with hf_def
  have hf : ∀ i, f i = σ i := by
    intro i
    simp [hf_def, Equiv.ofBijective_apply]
  set s : Finset (Fin n) := Finset.univ.filter (fun i => ε i = false) with hs_def
  have hflip : Reachable T (fun i => if i ∈ s then (T i)⁻¹ else T i) :=
    reachable_flip T s
  have htuple : (fun i => if i ∈ s then (T i)⁻¹ else T i) = tupleOf f := by
    funext i
    cases hεi : ε i
    · have hmem : i ∈ s := by simp [hs_def, hεi]
      rw [if_pos hmem]
      have hTi : T i = (FreeGroup.of (σ i))⁻¹ := by
        simpa [hεi] using hε i
      simp [hTi, tupleOf, hf i]
    · have hmem : i ∉ s := by simp [hs_def, hεi]
      rw [if_neg hmem]
      have hTi : T i = FreeGroup.of (σ i) := by
        simpa [hεi] using hε i
      simp [hTi, tupleOf, hf i]
  rw [htuple] at hflip
  exact Relation.ReflTransGen.trans hflip
    (permutation_reachable_standard (n := n) f)

/-- `AC.Conjecture` is equivalent to reaching the terminal set from every trivial
presentation. The forward direction is immediate; the reverse direction uses gap G3. -/
theorem conjecture_iff_terminal :
    Conjecture ↔ ∀ (n : ℕ), 0 < n → ∀ R : Relators n, PresentsTrivialGroup R →
      ∃ T : Relators n, IsSignedPermutation T ∧ Reachable R T := by
  constructor
  · intro h n hn R hR
    exact Exists.intro (standard n)
      (And.intro (standard_isSignedPermutation (n := n)) (h n hn R hR))
  · intro h
    exact conjecture_of_terminal_and_canonical h
      fun n _ T hT => signedPermutation_reachable_standard n T hT

/-! ## 7. The disproof route -/

/-- A span difference between a trivial presentation and the standard tuple yields an
`AC.Counterexample`, hence `¬ AC.Conjecture`. This theorem is complete. -/
theorem counterexample_of_span_separation {R : Relators n}
    (hR : PresentsTrivialGroup R)
    (h : Invariant.expSpan R ≠ Invariant.expSpan (standard n)) : IsCounterexample R :=
  Invariant.counterexample_of_expSpan_ne hR h

/-- The disproof route is exhausted: under gap G1 the span of a trivial presentation
equals the span of the standard tuple, so the separation hypothesis is unsatisfiable. -/
theorem span_route_exhausted {R : Relators n}
    (hspan : ∀ T : Relators n, PresentsTrivialGroup T → Invariant.expSpan T = ⊤)
    (hstd : PresentsTrivialGroup (standard n)) (hR : PresentsTrivialGroup R) :
    ¬ (Invariant.expSpan R ≠ Invariant.expSpan (standard n)) :=
  Invariant.no_span_separation hspan hstd hR

/-! ## 8. The obstruction for group-theoretic invariants -/

/-- The normal closure of the relator set is unchanged when one relator is inverted. -/
theorem normalClosure_range_inv (R : Relators n) (i : Fin n) :
    Subgroup.normalClosure (Set.range (Function.update R i (R i)⁻¹)) =
      Subgroup.normalClosure (Set.range R) := by
  refine le_antisymm ?_ ?_
  · refine Subgroup.normalClosure_le_normal ?_
    rintro x ⟨j, rfl⟩
    by_cases hj : j = i
    · rw [hj, Function.update_self]
      exact Subgroup.inv_mem _ (Subgroup.subset_normalClosure ⟨i, rfl⟩)
    · rw [Function.update_of_ne hj]
      exact Subgroup.subset_normalClosure ⟨j, rfl⟩
  · refine Subgroup.normalClosure_le_normal ?_
    rintro x ⟨j, rfl⟩
    by_cases hj : j = i
    · rw [hj]
      have hmem : (R i)⁻¹ ∈
          Subgroup.normalClosure (Set.range (Function.update R i (R i)⁻¹)) :=
        Subgroup.subset_normalClosure ⟨i, by rw [Function.update_self]⟩
      simpa using Subgroup.inv_mem _ hmem
    · exact Subgroup.subset_normalClosure ⟨j, Function.update_of_ne hj ((R i)⁻¹) R⟩

/-- The normal closure is unchanged when one relator is right-multiplied by another.
The index guard `i ≠ j` keeps the partner relator intact at its own position. -/
theorem normalClosure_range_mulRight (R : Relators n) (i j : Fin n) (hij : i ≠ j) :
    Subgroup.normalClosure (Set.range (Function.update R i (R i * R j))) =
      Subgroup.normalClosure (Set.range R) := by
  refine le_antisymm ?_ ?_
  · refine Subgroup.normalClosure_le_normal ?_
    rintro x ⟨k, rfl⟩
    by_cases hk : k = i
    · rw [hk, Function.update_self]
      exact Subgroup.mul_mem _ (Subgroup.subset_normalClosure ⟨i, rfl⟩)
        (Subgroup.subset_normalClosure ⟨j, rfl⟩)
    · rw [Function.update_of_ne hk]
      exact Subgroup.subset_normalClosure ⟨k, rfl⟩
  · refine Subgroup.normalClosure_le_normal ?_
    rintro x ⟨k, rfl⟩
    by_cases hk : k = i
    · rw [hk]
      have h1 : R i * R j ∈
          Subgroup.normalClosure (Set.range (Function.update R i (R i * R j))) :=
        Subgroup.subset_normalClosure ⟨i, by rw [Function.update_self]⟩
      have h2 : R j ∈
          Subgroup.normalClosure (Set.range (Function.update R i (R i * R j))) :=
        Subgroup.subset_normalClosure ⟨j, by rw [Function.update_of_ne (Ne.symm hij)]⟩
      have h3 := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
      have h4 : (R i * R j) * (R j)⁻¹ = R i := by group
      rwa [h4] at h3
    · exact Subgroup.subset_normalClosure ⟨k, Function.update_of_ne hk (R i * R j) R⟩

/-- The normal closure is unchanged when one relator is conjugated by any word. -/
theorem normalClosure_range_conj (R : Relators n) (i : Fin n) (w : Word n) :
    Subgroup.normalClosure (Set.range (Function.update R i (w * R i * w⁻¹))) =
      Subgroup.normalClosure (Set.range R) := by
  refine le_antisymm ?_ ?_
  · refine Subgroup.normalClosure_le_normal ?_
    rintro x ⟨k, rfl⟩
    by_cases hk : k = i
    · rw [hk, Function.update_self]
      exact (Subgroup.normalClosure_normal (s := Set.range R)).conj_mem (R i)
        (Subgroup.subset_normalClosure ⟨i, rfl⟩) w
    · rw [Function.update_of_ne hk]
      exact Subgroup.subset_normalClosure ⟨k, rfl⟩
  · refine Subgroup.normalClosure_le_normal ?_
    rintro x ⟨k, rfl⟩
    by_cases hk : k = i
    · rw [hk]
      have hmem : w * R i * w⁻¹ ∈
          Subgroup.normalClosure (Set.range (Function.update R i (w * R i * w⁻¹))) :=
        Subgroup.subset_normalClosure ⟨i, by rw [Function.update_self]⟩
      have hconj := (Subgroup.normalClosure_normal
        (s := Set.range (Function.update R i (w * R i * w⁻¹)))).conj_mem'
        (w * R i * w⁻¹) hmem w
      have h4 : w⁻¹ * (w * R i * w⁻¹) * w = R i := by group
      rwa [h4] at hconj
    · exact Subgroup.subset_normalClosure
        ⟨k, Function.update_of_ne hk (w * R i * w⁻¹) R⟩

/-- G4, closed.

An official step preserves the presented group. Each move replaces one relator by
`r⁻¹`, by `r s`, or by `w r w⁻¹`, and the three helper lemmas show that the normal closure
of the relator set is unchanged in each case. The presented groups are the same quotient,
so triviality is preserved in both directions. -/
theorem presents_of_step {R S : Relators n} (h : Step R S) :
    (PresentsTrivialGroup R ↔ PresentsTrivialGroup S) := by
  have hN : Subgroup.normalClosure (Set.range S) =
      Subgroup.normalClosure (Set.range R) := by
    cases h with
    | inv i => exact normalClosure_range_inv R i
    | mulRight i j hij => exact normalClosure_range_mulRight R i j hij
    | conj i w => exact normalClosure_range_conj R i w
  have hPG : PresentedGroup (Set.range S) = PresentedGroup (Set.range R) := by
    show (FreeGroup (Fin n) ⧸ (Subgroup.normalClosure (Set.range S))) =
      (FreeGroup (Fin n) ⧸ (Subgroup.normalClosure (Set.range R)))
    rw [hN]
  simp only [PresentsTrivialGroup, hPG]

/-- Triviality is preserved along every finite sequence of official steps. -/
theorem presents_of_reachable {R S : Relators n} (h : Reachable R S) :
    (PresentsTrivialGroup R ↔ PresentsTrivialGroup S) := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ hstep ih => exact ih.trans (presents_of_step hstep)

/-- If a quantity is constant on the class of trivial presentations, then it cannot
separate a member of that class from the standard tuple. Gap G4 supplies the constancy
hypothesis for any quantity that is a function of the presented group. -/
theorem group_invariant_cannot_separate {α : Type*} {R : Relators n}
    (P : Relators n → α)
    (h : ∀ R S : Relators n, PresentsTrivialGroup R → PresentsTrivialGroup S →
      P R = P S)
    (hstd : PresentsTrivialGroup (standard n)) (hR : PresentsTrivialGroup R) :
    ¬ (P R ≠ P (standard n)) := by
  intro hne
  exact hne (h R (standard n) hR hstd)

end ProofAttempt
end AC
