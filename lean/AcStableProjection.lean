import AC
import AcInvariant
import AcMove
import AcProof
import BranchD
import BranchD2
import Mathlib.Tactic
import Mathlib.Tactic.Group

/-!
# The stable projection: one stabilization is refutable

`AC.StableConjecture` (`AC.lean:106-112`) allows a stable path to insert and
delete isolated generator–relator pairs, so the rank can leave `n` and return
to `n`. `AC.BranchD.StableImpliesOrdinary` (`BranchD.lean:255-257`) states that
a stable solution at rank `n` yields an ordinary solution at rank `n`. This
file isolates the one-excursion core of that statement.

## Result

The one-stabilization projection is false at rank two. Let

    A = (x, y^2)    and    B = (y, x^2)

in the free group on two generators. The exponent span of `A` is
`Z e0 + 2 Z e1`, and the exponent span of `B` is `2 Z e0 + Z e1`. Every
`AC.Step` preserves the exponent span (`AC.Invariant.step_expSpan`,
`AcInvariant.lean:177`), so `¬ Reachable A B`. At rank three, however,

    stabilize A 2 2 = (x, y^2, z)    and    stabilize B 0 0 = (x, z, y^2).

The two tuples differ by a permutation of the last two relators, and
`ProofAttempt.reachable_swap` (`AcProof.lean:138`) constructs an ordinary AC path
between tuples that differ by such a permutation. Therefore

    Reachable (stabilize A 2 2) (stabilize B 0 0)

holds while `Reachable A B` fails. The failure is the different generator
embedding: the two stabilizations place the exponent-two relator in different
coordinates of `Z^3`, and the relator permutation aligns them after the rank
increase.

The same pair gives a concrete stable-only witness at rank two. The tuple
`U = (x^2)` at rank one satisfies `stabilize U 0 0 = A` and
`stabilize U 1 0 = B`, so

    StableReachable ⟨2, A⟩ ⟨2, B⟩

by one destabilization followed by one stabilization, while `¬ Reachable A B`.
This witness concerns a presentation of `Z/2`, not a trivial presentation. It
refutes the general one-stabilization projection and the excursion-erasure
route. It does not refute `AC.BranchD.StableImpliesOrdinary` for trivial
presentations, which remains a separate open question.

## Contents

1. The refutation of `OneStabilizationProjection`.
2. The soundness direction: a single stabilization, an ordinary path at the
   raised rank, and the matching destabilization form a stable path.
3. `reachable_map` pushes an ordinary path forward along an endomorphism of the
   ambient free group.
4. `stabilize_injective` shows that a stabilization determines its base tuple
   at fixed insertion data.
5. `kill_stabilize` records the image of a stabilized tuple under the
   retraction that kills the inserted generator. The killed tuple has `n + 1`
   relators, one of them trivial, and `AC.Step` has no move that deletes a
   relator or a generator.
6. The stable-only witness and the consistency checks.

## Status

The file contains no proof hole, no admission tactic, no evaluation shortcut, and
no user axiom. The one-stabilization projection is not an open goal: it is false, and
`one_stabilization_projection_refuted` is its kernel-checked refutation.
-/

set_option autoImplicit false

namespace AC
namespace StableProjection

/-! ## 1. The refutation of the one-stabilization projection -/

/-- The one-stabilization projection. If two single stabilizations of rank-`n`
tuples are ordinarily AC-equivalent at rank `n + 1`, then the base tuples are
ordinarily AC-equivalent at rank `n`. The insertion positions and the inserted
generators may differ on the two sides. This proposition is refuted below. -/
def OneStabilizationProjection : Prop :=
  ∀ {n : ℕ} (R S : Relators n) (g i g' i' : Fin (n + 1)),
    Reachable (AC.stabilize R g i) (AC.stabilize S g' i') → Reachable R S

/-- The first counterexample tuple `A = (x, y^2)` at rank two. -/
def counterA : Relators 2 := ![FreeGroup.of 0, (FreeGroup.of 1) ^ 2]

/-- The second counterexample tuple `B = (y, x^2)` at rank two. -/
def counterB : Relators 2 := ![FreeGroup.of 1, (FreeGroup.of 0) ^ 2]

/-- The rank-one tuple `U = (x^2)` whose two single stabilizations are
`counterA` and `counterB`. -/
def counterU : Relators 1 := fun _ => (FreeGroup.of 0) ^ 2

/-- The exponent vector of a free generator is the corresponding standard
basis vector. -/
@[simp] theorem expVec_of {n : ℕ} (i : Fin n) :
    Invariant.expVec (FreeGroup.of i) = Invariant.genVec i := by
  simp [Invariant.expVec, Invariant.expHom]

/-- The stabilization of `counterA` at generator position `2` and relator
position `2` is `(x, y^2, z)`. -/
theorem stabilize_counterA :
    AC.stabilize counterA 2 2 = ![FreeGroup.of 0, (FreeGroup.of 1) ^ 2, FreeGroup.of 2] := by
  funext j
  rcases Fin.eq_self_or_eq_succAbove (2 : Fin 3) j with h | ⟨k, hk⟩
  · rw [h, BranchD2.stabilize_apply_self]
    simp
  · rw [hk, BranchD2.stabilize_apply_succAbove]
    have h0 : Fin.succAbove (2 : Fin 3) (0 : Fin 2) = (0 : Fin 3) := by decide
    have h1 : Fin.succAbove (2 : Fin 3) (1 : Fin 2) = (1 : Fin 3) := by decide
    fin_cases k
    · simp [counterA, h0]
    · simp [counterA, h1]

/-- The stabilization of `counterB` at generator position `0` and relator
position `0` is `(x, z, y^2)`. -/
theorem stabilize_counterB :
    AC.stabilize counterB 0 0 = ![FreeGroup.of 0, FreeGroup.of 2, (FreeGroup.of 1) ^ 2] := by
  funext j
  rcases Fin.eq_self_or_eq_succAbove (0 : Fin 3) j with h | ⟨k, hk⟩
  · rw [h, BranchD2.stabilize_apply_self]
    simp
  · rw [hk, BranchD2.stabilize_apply_succAbove]
    have h0 : Fin.succAbove (0 : Fin 3) (0 : Fin 2) = (1 : Fin 3) := by decide
    have h1 : Fin.succAbove (0 : Fin 3) (1 : Fin 2) = (2 : Fin 3) := by decide
    fin_cases k
    · simp [counterB, h0]
    · simp [counterB, h1]

/-- Swapping relator positions `1` and `2` of `stabilize counterA 2 2` yields
`stabilize counterB 0 0`. -/
theorem swap_counter :
    Function.update (Function.update (AC.stabilize counterA 2 2) 1 ((AC.stabilize counterA 2 2) 2)) 2
      ((AC.stabilize counterA 2 2) 1) = AC.stabilize counterB 0 0 := by
  rw [stabilize_counterA, stabilize_counterB]
  funext j
  fin_cases j
  · simp [Function.update]
  · simp [Function.update]
  · simp [Function.update]

/-- An ordinary AC path at rank three joins the two raised-rank tuples. -/
theorem counterexample_raised :
    Reachable (AC.stabilize counterA 2 2) (AC.stabilize counterB 0 0) := by
  have h := ProofAttempt.reachable_swap (AC.stabilize counterA 2 2)
    (i := (1 : Fin 3)) (j := (2 : Fin 3)) (by decide)
  rw [swap_counter] at h
  exact h

/-- The submodule of vectors of `Z^2` whose first coordinate is even. -/
def evenFirst : Submodule ℤ (Fin 2 → ℤ) where
  carrier := {v | Even (v 0)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    intro x y hx hy
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp [Pi.add_apply, ha, hb]; ring⟩
  smul_mem' := by
    intro c x hx
    obtain ⟨a, ha⟩ := hx
    exact ⟨c * a, by simp [Pi.smul_apply, ha]; ring⟩

/-- The exponent span of `counterB` lies in `evenFirst`. -/
theorem expSpan_counterB_le_evenFirst : Invariant.expSpan counterB ≤ evenFirst := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨j, rfl⟩
  change Even (Invariant.expVec (counterB j) 0)
  fin_cases j
  · change Even (Invariant.expVec (counterB 0) 0)
    rw [show counterB 0 = FreeGroup.of 1 from rfl, expVec_of]
    simp [Invariant.genVec, Pi.single]
  · change Even (Invariant.expVec (counterB 1) 0)
    rw [show counterB 1 = (FreeGroup.of 0) ^ 2 from rfl, pow_two, Invariant.expVec_mul,
      expVec_of]
    exact ⟨1, by norm_num [Pi.add_apply, Invariant.genVec, Pi.single]⟩

/-- The first standard basis vector is not in `evenFirst`. -/
theorem genVec_zero_not_mem_evenFirst :
    Invariant.genVec (0 : Fin 2) ∉ evenFirst := by
  intro h
  obtain ⟨a, ha⟩ := h
  have h1 : Invariant.genVec (0 : Fin 2) 0 = 1 := by simp [Invariant.genVec, Pi.single]
  rw [h1] at ha
  omega

/-- The first standard basis vector lies in the exponent span of `counterA`. -/
theorem genVec_zero_mem_expSpan_counterA :
    Invariant.genVec (0 : Fin 2) ∈ Invariant.expSpan counterA := by
  have h := Invariant.expVec_mem_expSpan counterA (0 : Fin 2)
  simpa [counterA, expVec_of] using h

/-- The exponent spans of `counterA` and `counterB` differ. -/
theorem expSpan_counterA_ne_counterB :
    Invariant.expSpan counterA ≠ Invariant.expSpan counterB := by
  intro h
  have hmem : Invariant.genVec (0 : Fin 2) ∈ Invariant.expSpan counterB :=
    h ▸ genVec_zero_mem_expSpan_counterA
  exact genVec_zero_not_mem_evenFirst (expSpan_counterB_le_evenFirst hmem)

/-- The base tuples of the counterexample are not ordinarily AC-equivalent. -/
theorem counterexample_base : ¬ Reachable counterA counterB :=
  Invariant.not_reachable_of_expSpan_ne expSpan_counterA_ne_counterB

/-- The one-stabilization projection is false. -/
theorem one_stabilization_projection_refuted : ¬ OneStabilizationProjection := by
  intro hproj
  exact counterexample_base (hproj counterA counterB 2 2 0 0 counterexample_raised)

/-! ## 2. The soundness direction -/

/-- A single stabilization, an ordinary path at the raised rank, and the
matching destabilization form a stable path. -/
theorem stableReachable_of_one_stabilization {n : ℕ} {R S : Relators n}
    (g i g' i' : Fin (n + 1))
    (h : Reachable (AC.stabilize R g i) (AC.stabilize S g' i')) :
    StableReachable ⟨n, R⟩ ⟨n, S⟩ :=
  Relation.ReflTransGen.trans
    (Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single (StableStep.stabilize R g i))
      h.stable)
    (Relation.ReflTransGen.single (StableStep.destabilize S g' i'))

/-- An ordinary path lifts through a stabilization with fixed insertion data.
This is the forward half of the equivalence that the refuted projection would
have completed. -/
theorem reachable_stabilize_of_reachable {n : ℕ} {R S : Relators n}
    (g i : Fin (n + 1)) (h : Reachable R S) :
    Reachable (AC.stabilize R g i) (AC.stabilize S g i) :=
  BranchD2.Reachable.stabilize h g i

/-- The two-step stable path from `counterA` to `counterB` through the
rank-one tuple `counterU`. This is the stable-only witness at rank two. -/
theorem stabilize_counterU_zero : AC.stabilize counterU 0 0 = counterA := by
  funext j
  rcases Fin.eq_self_or_eq_succAbove (0 : Fin 2) j with h | ⟨k, hk⟩
  · rw [h, BranchD2.stabilize_apply_self]
    simp [counterA]
  · rw [hk, BranchD2.stabilize_apply_succAbove]
    have h0 : Fin.succAbove (0 : Fin 2) (0 : Fin 1) = (1 : Fin 2) := by decide
    fin_cases k
    · simp [counterU, counterA, h0]

/-- The same rank-one tuple stabilizes to `counterB` at generator position one
and relator position zero. -/
theorem stabilize_counterU_one : AC.stabilize counterU 1 0 = counterB := by
  funext j
  rcases Fin.eq_self_or_eq_succAbove (0 : Fin 2) j with h | ⟨k, hk⟩
  · rw [h, BranchD2.stabilize_apply_self]
    simp [counterB]
  · rw [hk, BranchD2.stabilize_apply_succAbove]
    have h0 : Fin.succAbove (0 : Fin 2) (0 : Fin 1) = (1 : Fin 2) := by decide
    fin_cases k
    · simp [counterU, counterB, h0]

/-- The counterexample pair is stable-reachable at rank two. -/
theorem stable_reachable_counter :
    StableReachable ⟨2, counterA⟩ ⟨2, counterB⟩ := by
  have h1 : StableStep ⟨2, counterA⟩ ⟨1, counterU⟩ := by
    have h := StableStep.destabilize counterU 0 0
    rwa [stabilize_counterU_zero] at h
  have h2 : StableStep ⟨1, counterU⟩ ⟨2, counterB⟩ := by
    have h := StableStep.stabilize counterU 1 0
    rwa [stabilize_counterU_one] at h
  exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single h1)
    (Relation.ReflTransGen.single h2)

/-- A concrete stable-only witness: the pair is stable-reachable at rank two
and not ordinarily reachable at rank two. -/
theorem stable_only_witness :
    StableReachable ⟨2, counterA⟩ ⟨2, counterB⟩ ∧ ¬ Reachable counterA counterB :=
  ⟨stable_reachable_counter, counterexample_base⟩

/-! ## 3. Pushforward along an endomorphism -/

/-- Updating one entry commutes with applying an endomorphism entrywise. -/
theorem update_map {n : ℕ} (φ : Word n →* Word n) (R : Relators n)
    (i : Fin n) (w : Word n) :
    Function.update (fun j => φ (R j)) i (φ w)
      = fun j => φ (Function.update R i w j) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [Function.update]
  · simp [Function.update, h]

/-- Every ordinary AC move is preserved by an endomorphism of the ambient free
group. Inversion, right multiplication, and conjugation are each carried to
the same move on the image tuple. -/
theorem step_map {n : ℕ} (φ : Word n →* Word n) {R S : Relators n}
    (h : Step R S) :
    Step (fun i => φ (R i)) (fun i => φ (S i)) := by
  cases h with
  | inv i =>
      have hupd : (fun j => φ (Function.update R i (R i)⁻¹ j))
          = Function.update (fun j => φ (R j)) i ((φ (R i))⁻¹) := by
        rw [← update_map, map_inv]
      rw [hupd]
      exact Step.inv (fun j => φ (R j)) i
  | mulRight i j hij =>
      have hupd : (fun k => φ (Function.update R i (R i * R j) k))
          = Function.update (fun k => φ (R k)) i (φ (R i) * φ (R j)) := by
        rw [← update_map, map_mul]
      rw [hupd]
      exact Step.mulRight (fun k => φ (R k)) i j hij
  | conj i w =>
      have hupd : (fun k => φ (Function.update R i (w * R i * w⁻¹) k))
          = Function.update (fun k => φ (R k)) i (φ w * φ (R i) * (φ w)⁻¹) := by
        rw [← update_map]
        simp [map_mul, map_inv]
      rw [hupd]
      exact Step.conj (fun k => φ (R k)) i (φ w)

/-- An ordinary AC path is carried to an ordinary AC path by an endomorphism of
the ambient free group. -/
theorem reachable_map {n : ℕ} (φ : Word n →* Word n) {R S : Relators n}
    (h : Reachable R S) :
    Reachable (fun i => φ (R i)) (fun i => φ (S i)) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (step_map φ hstep)

/-! ## 4. A stabilization determines its base tuple -/

/-- A stabilization is injective in the base tuple at fixed insertion data.
The relators appear at the positions `i.succAbove j`, and the relabelling
`Fin.succAbove g` is injective on generators. -/
theorem stabilize_injective {n : ℕ} {R S : Relators n} {g i : Fin (n + 1)}
    (h : AC.stabilize R g i = AC.stabilize S g i) : R = S := by
  funext k
  have hk := congrFun h (i.succAbove k)
  rw [BranchD2.stabilize_apply_succAbove, BranchD2.stabilize_apply_succAbove] at hk
  exact FreeGroup.map_injective (Fin.succAbove_right_injective (p := g)) hk

/-! ## 5. The killing retraction and the exact obstruction -/

/-- The retraction of the free group on `Fin (n + 1)` that sends the generator
`g` to `1` and fixes every other generator. -/
def killGen {n : ℕ} (g : Fin (n + 1)) :
    FreeGroup (Fin (n + 1)) →* FreeGroup (Fin (n + 1)) :=
  FreeGroup.lift fun k => if k = g then 1 else FreeGroup.of k

@[simp] theorem killGen_self {n : ℕ} (g : Fin (n + 1)) :
    killGen g (FreeGroup.of g) = 1 := by
  simp [killGen]

theorem killGen_of_ne {n : ℕ} {g k : Fin (n + 1)} (h : k ≠ g) :
    killGen g (FreeGroup.of k) = FreeGroup.of k := by
  simp [killGen, h]

/-- The retraction fixes every word that omits the generator `g`, in particular
every relabelled old relator of a stabilization. -/
theorem killGen_map_succAbove {n : ℕ} (g : Fin (n + 1)) (w : Word n) :
    killGen g (FreeGroup.map g.succAbove w) = FreeGroup.map g.succAbove w := by
  have hgen : ∀ j : Fin n,
      (killGen g).comp (FreeGroup.map g.succAbove) (FreeGroup.of j)
        = FreeGroup.map g.succAbove (FreeGroup.of j) := by
    intro j
    simp [killGen, Fin.succAbove_ne]
  have h := FreeGroup.map.unique (f := g.succAbove)
    ((killGen g).comp (FreeGroup.map g.succAbove)) hgen (x := w)
  simpa using h

/-- The exact image of a stabilized tuple under the retraction that kills the
inserted generator: the inserted relator becomes `1`, and the old relators
appear at the relabelled positions. This is the point where the killed path
stops being a stabilization image. -/
theorem kill_stabilize {n : ℕ} (R : Relators n) (g i : Fin (n + 1)) :
    (fun j => killGen g (AC.stabilize R g i j))
      = Fin.insertNth i 1 (fun j => FreeGroup.map g.succAbove (R j)) := by
  funext j
  rcases Fin.eq_self_or_eq_succAbove i j with h | ⟨k, hk⟩
  · rw [h]
    rw [BranchD2.stabilize_apply_self]
    simp [killGen]
  · rw [hk]
    rw [BranchD2.stabilize_apply_succAbove, killGen_map_succAbove]
    simp

/-! ## 6. Consistency checks -/

/-- The projection at equal endpoints has a reflexive conclusion. -/
theorem one_stabilization_refl {n : ℕ} (R : Relators n) (g i g' i' : Fin (n + 1))
    (_h : Reachable (AC.stabilize R g i) (AC.stabilize R g' i')) :
    Reachable R R :=
  Relation.ReflTransGen.refl

/-- The projection at rank zero holds, because there is exactly one relator
tuple at rank zero. This checks that the refutation is not a rank-zero
artefact. -/
theorem one_stabilization_of_rank_zero (R S : Relators 0) (g i g' i' : Fin 1)
    (_h : Reachable (AC.stabilize R g i) (AC.stabilize S g' i')) :
    Reachable R S := by
  have hRS : R = S := by
    funext j
    exact Fin.elim0 j
  rw [hRS]
  exact Relation.ReflTransGen.refl

/-! ## 7. Axiom record

The fresh reader runs, on the pinned toolchain:

    #print axioms AC.StableProjection.one_stabilization_projection_refuted
    #print axioms AC.StableProjection.counterexample_raised
    #print axioms AC.StableProjection.counterexample_base
    #print axioms AC.StableProjection.stable_only_witness
    #print axioms AC.StableProjection.update_map
    #print axioms AC.StableProjection.step_map
    #print axioms AC.StableProjection.reachable_map
    #print axioms AC.StableProjection.stabilize_injective
    #print axioms AC.StableProjection.killGen_map_succAbove
    #print axioms AC.StableProjection.kill_stabilize
    #print axioms AC.StableProjection.stableReachable_of_one_stabilization
    #print axioms AC.StableProjection.reachable_stabilize_of_reachable
    #print axioms AC.StableProjection.one_stabilization_refl
    #print axioms AC.StableProjection.one_stabilization_of_rank_zero

Each of these reports a set inside `[propext, Classical.choice, Quot.sound]`.
No declaration in this file depends on the proof-hole axiom. -/

end StableProjection
end AC
