import AC
import AcBase
import Mathlib.Data.Fin.SuccPred
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Rank reduction for the pivot-reduced A9 interface

This module closes the reduction step that `BranchA.rank_reduction_interface` states.
A rank `n + 1` relator tuple `S` is pivot-reduced at `i` when relator `i` is the signed
generator `i` and every other relator avoids generator `i`. Deleting the pivot generator
and the pivot relator leaves a rank `n` tuple `T`; `embed` re-inserts them. The module
proves that `embed` fixes the standard tuple, that it carries every rank `n` path to a
rank `n + 1` path, and that the deleted tuple presents the trivial group whenever `S`
does, so the deletion supplies the rank `n` witness.

The embedding is `Fin.insertNth i (FreeGroup.of i) (Fin.succAbove i ∘ ·)` on generator
names. The deletion is `FreeGroup.map` along a retraction of `Fin.succAbove i`.

## A note on `Fin.predAbove`

In this Mathlib revision `Fin.predAbove` is typed `Fin n → Fin (n + 1) → Fin n`: its
pivot is an element of `Fin n`, so it retracts only the embeddings `(castSucc p).succAbove`
whose hole is a cast successor. The A9 interface quantifies over an arbitrary pivot
`i : Fin (n + 1)`, and when `i` is the last index no `predAbove` retraction exists.
`deleteIndex` is the retraction of `Fin.succAbove i` in that generality, obtained from
`Fin.exists_succAbove_eq`; `succAbove_deleteIndex` is the `predAbove_succAbove` identity
for this retraction, and `deleteIndex_castSucc` records that on a cast-successor hole it
agrees with `Fin.predAbove`.
-/

set_option autoImplicit false

namespace AC
namespace RankReduction

variable {n : ℕ}

/-! ## 1. The pivot-reduced predicate -/

/-- A word avoids generator `g` when no letter of its reduced form is `g`.
This is the `BranchA.Avoids` predicate, restated here so the module is self-contained. -/
def Avoids {m : ℕ} (g : Fin m) (w : Word m) : Prop :=
  ∀ p ∈ w.toWord, p.1 ≠ g

/-- The pivot-reduced predicate: relator `i` is the signed generator `g`, and every
other relator avoids `g`. This is the `BranchA.PivotReduced` predicate, restated here. -/
def PivotReduced {m : ℕ} (R : Relators m) (i g : Fin m) : Prop :=
  (R i = FreeGroup.of g ∨ R i = (FreeGroup.of g)⁻¹) ∧
    ∀ j : Fin m, j ≠ i → Avoids g (R j)

/-! ## 2. The embedding -/

/-- Insert the pivot generator at index `i` of a rank `n` tuple: the pivot relator is
`FreeGroup.of i`, and the old relators are relabelled along `Fin.succAbove i`. -/
def embed (i : Fin (n + 1)) (U : Relators n) : Relators (n + 1) :=
  Fin.insertNth i (FreeGroup.of i) (fun t => FreeGroup.map (Fin.succAbove i) (U t))

/-- The embedding fixes the standard tuple. This is the first required interface
property. -/
theorem embed_standard (i : Fin (n + 1)) : embed i (standard n) = standard (n + 1) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [embed, standard]
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    simp [embed, standard]

/-- The embedding commutes with overwriting one relator, at the transported index. -/
private lemma embed_update (i : Fin (n + 1)) (U : Relators n) (k : Fin n) (w : Word n) :
    embed i (Function.update U k w) =
      Function.update (embed i U) (Fin.succAbove i k) (FreeGroup.map (Fin.succAbove i) w) := by
  funext j
  simp only [embed]
  by_cases hj : j = i
  · rw [hj]
    rw [Fin.insertNth_apply_same]
    rw [Function.update_of_ne (Ne.symm (Fin.succAbove_ne i k))]
    rw [Fin.insertNth_apply_same]
  · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hj
    rw [Fin.insertNth_apply_succAbove]
    by_cases hl : l = k
    · rw [hl]
      simp only [Function.update_self]
    · have hne : Fin.succAbove i l ≠ Fin.succAbove i k := by
        intro hh
        exact hl (Fin.succAbove_right_injective hh)
      rw [Function.update_of_ne hne]
      rw [Fin.insertNth_apply_succAbove]
      rw [Function.update_of_ne hl]

/-- The embedding carries one official move to one official move. -/
private lemma step_embed (i : Fin (n + 1)) {U V : Relators n} (h : Step U V) :
    Step (embed i U) (embed i V) := by
  cases h with
  | inv k =>
      rw [embed_update]
      rw [map_inv]
      have hval : embed i U (Fin.succAbove i k) = FreeGroup.map (Fin.succAbove i) (U k) := by
        simp [embed]
      rw [← hval]
      exact Step.inv (embed i U) (Fin.succAbove i k)
  | mulRight k l hkl =>
      rw [embed_update]
      rw [map_mul]
      have hk : embed i U (Fin.succAbove i k) = FreeGroup.map (Fin.succAbove i) (U k) := by
        simp [embed]
      have hl : embed i U (Fin.succAbove i l) = FreeGroup.map (Fin.succAbove i) (U l) := by
        simp [embed]
      rw [← hk, ← hl]
      exact Step.mulRight (embed i U) (Fin.succAbove i k) (Fin.succAbove i l)
        (fun hh => hkl (Fin.succAbove_right_injective hh))
  | conj k w =>
      rw [embed_update]
      rw [map_mul, map_mul, map_inv]
      have hk : embed i U (Fin.succAbove i k) = FreeGroup.map (Fin.succAbove i) (U k) := by
        simp [embed]
      rw [← hk]
      exact Step.conj (embed i U) (Fin.succAbove i k) (FreeGroup.map (Fin.succAbove i) w)

/-- Every rank `n` path lifts through the embedding. This is the second required
interface property. -/
theorem reachable_embed (i : Fin (n + 1)) {U V : Relators n} (h : Reachable U V) :
    Reachable (embed i U) (embed i V) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.trans (Relation.ReflTransGen.single (step_embed i hstep))

/-! ## 3. The deletion

The target rank `n` is required to be nonempty: there is no total function
`Fin (n + 1) → Fin n` when `n = 0`, so the deletion is stated for `[NeZero n]`.
The rank-one case of the interface is closed directly in `rankReduction`. -/

section Delete
variable [NeZero n]

/-- The retraction of `Fin.succAbove i`: a left inverse away from the pivot, and the
general form of `Fin.predAbove` for an arbitrary hole `i : Fin (n + 1)`. -/
noncomputable def deleteIndex (i : Fin (n + 1)) (a : Fin (n + 1)) : Fin n :=
  if h : a = i then 0 else (Fin.exists_succAbove_eq h).choose

/-- The retraction identity: every non-pivot index is the image of its own deletion. -/
lemma succAbove_deleteIndex {i : Fin (n + 1)} {a : Fin (n + 1)} (h : a ≠ i) :
    Fin.succAbove i (deleteIndex i a) = a := by
  unfold deleteIndex
  rw [dif_neg h]
  exact (Fin.exists_succAbove_eq h).choose_spec

/-- On the image of `Fin.succAbove i` the deletion is its inverse. -/
lemma deleteIndex_succAbove (i : Fin (n + 1)) (k : Fin n) :
    deleteIndex i (Fin.succAbove i k) = k :=
  Fin.succAbove_right_injective (succAbove_deleteIndex (Fin.succAbove_ne i k))

/-- On a cast-successor hole the deletion is `Fin.predAbove`. -/
lemma deleteIndex_castSucc {p : Fin n} {a : Fin (n + 1)} (h : a ≠ p.castSucc) :
    deleteIndex p.castSucc a = Fin.predAbove p a := by
  have h1 : Fin.succAbove (p.castSucc) (deleteIndex p.castSucc a) = a :=
    succAbove_deleteIndex h
  have h2 : Fin.succAbove (p.castSucc) (Fin.predAbove p a) = a :=
    Fin.succAbove_predAbove h
  exact Fin.succAbove_right_injective (p := p.castSucc) (h1.trans h2.symm)

/-- Delete the pivot generator from a word. The map is letterwise on the reduced word. -/
noncomputable def deletePivot (i : Fin (n + 1)) (w : Word (n + 1)) : Word n :=
  FreeGroup.map (deleteIndex i) w

/-- The round-trip identity on a raw reduced word list that avoids the pivot. -/
lemma map_succAbove_deletePivot_mk (i : Fin (n + 1)) (L : List (Fin (n + 1) × Bool))
    (hL : ∀ p ∈ L, p.1 ≠ i) :
    FreeGroup.map (Fin.succAbove i) (deletePivot i (FreeGroup.mk L)) = FreeGroup.mk L := by
  rw [deletePivot, FreeGroup.map.mk, FreeGroup.map.mk, List.map_map]
  congr 1
  induction L with
  | nil => rfl
  | cons x t ih =>
      obtain ⟨a, b⟩ := x
      simp only [List.map_cons, Function.comp_apply, List.cons.injEq]
      exact ⟨Prod.ext (succAbove_deleteIndex (hL (a, b) (by simp))) rfl,
        ih (fun p hp => hL p (by simp [hp]))⟩

/-- Deleting the pivot generator and re-inserting it recovers a word that avoids it.
This is the round trip the reachability witness needs. -/
lemma map_succAbove_deletePivot {i : Fin (n + 1)} {w : Word (n + 1)}
    (h : Avoids i w) :
    FreeGroup.map (Fin.succAbove i) (deletePivot i w) = w := by
  have key := map_succAbove_deletePivot_mk i w.toWord h
  rwa [FreeGroup.mk_toWord] at key

/-- The deleted tuple: the non-pivot relators, with the pivot generator removed. -/
noncomputable def reduceTuple (i : Fin (n + 1)) (S : Relators (n + 1)) : Relators n :=
  fun k => deletePivot i (S (Fin.succAbove i k))

/-- Re-inserting the deleted tuple gives `S` with the pivot relator normalised to
`FreeGroup.of i`. -/
lemma embed_reduceTuple {i : Fin (n + 1)} {S : Relators (n + 1)}
    (hred : PivotReduced S i i) :
    embed i (reduceTuple i S) = Function.update S i (FreeGroup.of i) := by
  funext j
  simp only [embed]
  by_cases hj : j = i
  · rw [hj]
    rw [Fin.insertNth_apply_same, Function.update_self]
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    rw [Fin.insertNth_apply_succAbove]
    rw [Function.update_of_ne (Fin.succAbove_ne i k)]
    exact map_succAbove_deletePivot (hred.2 (Fin.succAbove i k) (Fin.succAbove_ne i k))

/-- The pivot-reduced tuple reaches the embedding of its deletion: at most one inversion
of the pivot relator is needed. -/
theorem reachable_reduceTuple {i : Fin (n + 1)} {S : Relators (n + 1)}
    (hred : PivotReduced S i i) :
    Reachable S (embed i (reduceTuple i S)) := by
  rw [embed_reduceTuple hred]
  rcases hred.1 with h | h
  · rw [← h, Function.update_eq_self]
    exact Relation.ReflTransGen.refl
  · have hstep : Step S (Function.update S i (FreeGroup.of i)) := by
      have hs := Step.inv S i
      rw [h, inv_inv] at hs
      exact hs
    exact Relation.ReflTransGen.single hstep

end Delete

/-! ## 4. Triviality transport

The normal closure of the relators is the obstruction to triviality. The retraction
`psi` kills the pivot generator and inverts the deletion on the other generators, so it
maps the normal closure of `S` onto the normal closure of the deleted tuple. Since `psi`
is surjective, the deletion of a trivial presentation is trivial.
-/

section Transport
variable [NeZero n]

/-- The generator relabelling that inserts the pivot index. -/
def phi (i : Fin (n + 1)) : Word n →* Word (n + 1) := FreeGroup.map (Fin.succAbove i)

/-- The retraction that kills the pivot generator and deletes it from every other word. -/
noncomputable def psi (i : Fin (n + 1)) : Word (n + 1) →* Word n :=
  FreeGroup.lift (fun a => if a = i then 1 else FreeGroup.of (deleteIndex i a))

/-- The retraction kills the pivot generator. -/
lemma psi_of_pivot (i : Fin (n + 1)) : psi i (FreeGroup.of i) = 1 := by
  simp [psi]

/-- The retraction is a left inverse of the generator embedding. -/
lemma psi_phi (i : Fin (n + 1)) (x : Word n) : psi i (phi i x) = x := by
  have hgen : ∀ k : Fin n, (psi i).comp (phi i) (FreeGroup.of k) = FreeGroup.of k := by
    intro k
    simp only [MonoidHom.comp_apply, phi, FreeGroup.map.of, psi, FreeGroup.lift_apply_of]
    rw [if_neg (Fin.succAbove_ne i k), deleteIndex_succAbove]
  calc psi i (phi i x) = FreeGroup.lift FreeGroup.of x :=
        FreeGroup.lift_unique (f := FreeGroup.of) ((psi i).comp (phi i)) hgen
    _ = x := FreeGroup.lift_of_apply x

/-- The deleted tuple presents the trivial group whenever `S` does. -/
theorem presentsTrivialGroup_reduceTuple {i : Fin (n + 1)} {S : Relators (n + 1)}
    (hred : PivotReduced S i i) (hp : PresentsTrivialGroup S) :
    PresentsTrivialGroup (reduceTuple i S) := by
  set T : Relators n := reduceTuple i S with hT
  set M : Subgroup (Word (n + 1)) := Subgroup.normalClosure (Set.range S) with hM
  set N : Subgroup (Word n) := Subgroup.normalClosure (Set.range T) with hN
  have hsurj : Function.Surjective (psi i) := fun x => ⟨phi i x, psi_phi i x⟩
  haveI hMnorm : M.Normal := by rw [hM]; infer_instance
  haveI hmapnorm : (Subgroup.map (psi i) M).Normal := hMnorm.map (psi i) hsurj
  have hMtop : M = ⊤ := by
    rw [hM]
    exact QuotientGroup.subsingleton_iff.mp hp
  have hmap1 : Subgroup.map (psi i) M ≤ N := by
    rw [Subgroup.map_le_iff_le_comap, hM]
    refine Subgroup.normalClosure_le_normal ?_
    rintro x ⟨j, rfl⟩
    change psi i (S j) ∈ N
    by_cases hj : j = i
    · rw [hj]
      rcases hred.1 with h | h
      · rw [h, psi_of_pivot]
        exact N.one_mem
      · rw [h, map_inv, psi_of_pivot]
        simpa only [inv_one] using N.one_mem
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
      have hST : phi i (T k) = S (Fin.succAbove i k) :=
        map_succAbove_deletePivot (hred.2 (Fin.succAbove i k) (Fin.succAbove_ne i k))
      rw [← hST, psi_phi]
      exact Subgroup.subset_normalClosure ⟨k, rfl⟩
  have hmap2 : N ≤ Subgroup.map (psi i) M := by
    rw [hN]
    refine Subgroup.normalClosure_le_normal ?_
    rintro x ⟨k, rfl⟩
    change ∃ y ∈ M, psi i y = T k
    refine ⟨phi i (T k), ?_, psi_phi i (T k)⟩
    have hST : phi i (T k) = S (Fin.succAbove i k) :=
      map_succAbove_deletePivot (hred.2 (Fin.succAbove i k) (Fin.succAbove_ne i k))
    rw [hST]
    exact Subgroup.subset_normalClosure ⟨Fin.succAbove i k, rfl⟩
  have hNtop : N = ⊤ := by
    have heq : Subgroup.map (psi i) M = N := le_antisymm hmap1 hmap2
    rw [← heq, hMtop]
    exact Subgroup.map_top_of_surjective (psi i) hsurj
  show Subsingleton (Word n ⧸ Subgroup.normalClosure (Set.range T))
  rw [← hN]
  exact QuotientGroup.subsingleton_iff.mpr hNtop

end Transport

/-! ## 5. The A9 interface -/

/-- Rank reduction at a pivot-reduced trivial presentation. A rank `n + 1` tuple `S`,
pivot-reduced at `i`, yields a rank `n` trivial tuple `T`, an embedding `embed` that
fixes the standard tuple and lifts every rank `n` path, and a path `Reachable S (embed T)`.
The rank-one case `n = 0` is closed directly, since no deletion index exists there. -/
theorem rankReduction (S : Relators (n + 1)) (i : Fin (n + 1))
    (hred : PivotReduced S i i) (hp : PresentsTrivialGroup S) :
    ∃ (T : Relators n) (embed : Relators n → Relators (n + 1)),
      PresentsTrivialGroup T ∧
      embed (standard n) = standard (n + 1) ∧
      (∀ {U V : Relators n}, Reachable U V → Reachable (embed U) (embed V)) ∧
      Reachable S (embed T) := by
  rcases n with _ | m
  · -- rank one: the pivot relator is the only relator
    have hsingle : ∀ j : Fin 1, j = i := by
      intro j
      exact Fin.ext (by have hj := j.isLt; have hi := i.isLt; omega)
    have hstd : standard 1 = Function.update S i (FreeGroup.of i) := by
      funext j
      rw [hsingle j, Function.update_self]
      rfl
    refine ⟨standard 0, fun _ => standard 1, AC.Base.presentsTrivialGroup_standard 0, rfl,
      fun _ => Relation.ReflTransGen.refl, ?_⟩
    rcases hred.1 with h | h
    · have hS : S = standard 1 := by
        rw [hstd, ← h, Function.update_eq_self]
      rw [hS]
      exact Relation.ReflTransGen.refl
    · have hstep : Step S (Function.update S i (FreeGroup.of i)) := by
        have hs := Step.inv S i
        rw [h, inv_inv] at hs
        exact hs
      rw [hstd]
      exact Relation.ReflTransGen.single hstep
  · exact ⟨reduceTuple i S, embed i, presentsTrivialGroup_reduceTuple hred hp,
      embed_standard i, fun h => reachable_embed i h, reachable_reduceTuple hred⟩

end RankReduction
end AC
