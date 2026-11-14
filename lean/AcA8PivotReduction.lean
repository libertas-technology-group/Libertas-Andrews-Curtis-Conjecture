import AcA8Reachability
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Basic

/-!
# AcA8PivotReduction — pivot reduction for the A8 route

This module proves that a relator list can be reduced to one in which every
non-pivot relator avoids a chosen signed generator.  The proof iterates the
delete-letter helper in `AcA8Reachability` and terminates by lowering the total
length of the reduced relation words.
-/

set_option autoImplicit false

namespace AC
namespace A8PivotReduction

open AC
open A8Reachability
open scoped BigOperators

variable {n : ℕ}

/-- A word avoids a generator when no letter of its reduced word carries that generator. -/
def Avoids (g : Fin n) (w : Word n) : Prop :=
  ∀ p ∈ w.toWord, p.1 ≠ g

/-- The pivot relation is a signed generator and every other relation avoids it. -/
def PivotReduced (R : Relators n) (i g : Fin n) : Prop :=
  (R i = FreeGroup.of g ∨ R i = (FreeGroup.of g)⁻¹) ∧
    ∀ j : Fin n, j ≠ i → Avoids g (R j)

/-- The total length of all reduced relation words. -/
noncomputable def totalLength (R : Relators n) : ℕ :=
  ∑ j ∈ (Finset.univ : Finset (Fin n)), (R j).toWord.length

/-- Every occurrence in a list splits the list at that occurrence. -/
lemma exists_append_cons_of_mem {α : Type*} {a : α} {L : List α} (h : a ∈ L) :
    ∃ pre post : List α, L = pre ++ a :: post := by
  induction L with
  | nil => simp at h
  | cons b L ih =>
      by_cases hba : b = a
      · subst hba
        exact ⟨[], L, rfl⟩
      · have h' : a ∈ L := by
          rcases List.mem_cons.mp h with h | h
          · exact False.elim (hba h.symm)
          · exact h
        rcases ih h' with ⟨pre, post, hL⟩
        exact ⟨b :: pre, post, by simp [hL]⟩

/-- Deleting a letter from one relation lowers the total reduced length. -/
lemma totalLength_update_delete_letter_lt (R : Relators n) {i j g : Fin n}
    (hij : i ≠ j) (pre post : List (Fin n × Bool)) (b : Bool)
    (hL : (R j).toWord = pre ++ (g, b) :: post) :
    totalLength (Function.update R j (FreeGroup.mk post * FreeGroup.mk pre)) <
      totalLength R := by
  classical
  change totalLength (Function.update R j (FreeGroup.mk (post ++ pre))) < totalLength R
  let newLen := (FreeGroup.mk (post ++ pre)).toWord.length
  let oldLen := (R j).toWord.length
  let rest := ∑ x ∈ (Finset.univ : Finset (Fin n)) \ {j}, (R x).toWord.length
  have hnew : newLen ≤ post.length + pre.length := by
    dsimp [newLen]
    change FreeGroup.norm (FreeGroup.mk (post ++ pre)) ≤ post.length + pre.length
    calc
      FreeGroup.norm (FreeGroup.mk (post ++ pre)) ≤ (post ++ pre).length :=
        FreeGroup.norm_mk_le
      _ = post.length + pre.length := by simp [List.length_append]
  have hold : oldLen = pre.length + 1 + post.length := by
    dsimp [oldLen]
    rw [hL]
    simp [List.length_append]
    omega
  have hnew1 : newLen + 1 ≤ oldLen := by
    omega
  have hfun : (fun k : Fin n =>
      (Function.update R j (FreeGroup.mk (post ++ pre)) k).toWord.length) =
      Function.update (fun k : Fin n => (R k).toWord.length) j newLen := by
    funext k
    by_cases hk : k = j
    · subst hk
      simp [newLen]
    · simp [Function.update_of_ne hk]
  have hsumS :
      totalLength (Function.update R j (FreeGroup.mk (post ++ pre))) =
        newLen + rest := by
    dsimp [totalLength, rest, newLen]
    rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ j)]
    simp [newLen]
  have hsumR : totalLength R = oldLen + rest := by
    dsimp [totalLength, rest, oldLen]
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_univ j)]
  rw [hsumS, hsumR]
  omega

/-- Every non-pivot-reduced list has a relation other than the pivot carrying a pivot letter. -/
lemma exists_pivot_letter_of_not_pivotReduced (R : Relators n) {i g : Fin n}
    (hu : R i = FreeGroup.of g ∨ R i = (FreeGroup.of g)⁻¹)
    (hred : ¬ PivotReduced R i g) :
    ∃ j : Fin n, j ≠ i ∧ ∃ p ∈ (R j).toWord, p.1 = g := by
  classical
  rw [PivotReduced] at hred
  by_cases hA : R i = FreeGroup.of g ∨ R i = (FreeGroup.of g)⁻¹
  · have hnotB : ¬ ∀ j : Fin n, j ≠ i → Avoids g (R j) := by
      intro hB
      exact hred ⟨hA, hB⟩
    push Not at hnotB
    rcases hnotB with ⟨j, hij, hnot⟩
    rw [Avoids] at hnot
    push Not at hnot
    exact ⟨j, hij, hnot⟩
  · exact False.elim (hA hu)

/-- Pivot reduction: iterate deletion until every non-pivot relation avoids the pivot. -/
theorem pivot_reduction_exists (R : Relators n) (i g : Fin n)
    (hi : R i = FreeGroup.of g ∨ R i = (FreeGroup.of g)⁻¹) :
    ∃ S : Relators n, PivotReduced S i g ∧ Reachable R S := by
  classical
  suffices h : ∀ N : ℕ, ∀ R : Relators n, totalLength R = N →
      (R i = FreeGroup.of g ∨ R i = (FreeGroup.of g)⁻¹) →
      ∃ S : Relators n, PivotReduced S i g ∧ Reachable R S by
    exact h (totalLength R) R rfl hi
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
      intro R hN hiR
      by_cases hred : PivotReduced R i g
      · exact ⟨R, hred, Relation.ReflTransGen.refl⟩
      · rcases exists_pivot_letter_of_not_pivotReduced R hiR hred with
          ⟨j, hij, ⟨⟨g', b⟩, hmem, hg'⟩⟩
        have hg'eq : g' = g := hg'
        subst g'
        rcases exists_append_cons_of_mem hmem with ⟨pre, post, hL⟩
        have hj : R j = FreeGroup.mk (pre ++ (g, b) :: post) := by
          rw [← FreeGroup.mk_toWord (x := R j), hL]
        let S : Relators n :=
          Function.update R j (FreeGroup.mk post * FreeGroup.mk pre)
        have hstep : Reachable R S :=
          reachable_delete_letter R (Ne.symm hij) (R i) rfl hiR pre post b hj
        have hlt : totalLength S < totalLength R :=
          totalLength_update_delete_letter_lt R (Ne.symm hij) pre post b hL
        have hNlt : totalLength S < N := by
          omega
        have hSi : S i = FreeGroup.of g ∨ S i = (FreeGroup.of g)⁻¹ := by
          have hSR : S i = R i := by
            dsimp [S]
            exact Function.update_of_ne (Ne.symm hij)
              (FreeGroup.mk (post ++ pre)) R
          rw [hSR]
          exact hiR
        rcases ih (totalLength S) hNlt S rfl hSi with ⟨T, hT, hST⟩
        exact ⟨T, hT, hstep.trans hST⟩


lemma expVec_of_gen {n : ℕ} (g : Fin n) :
    Invariant.expVec (FreeGroup.of g) = Invariant.genVec g := by
  simp [Invariant.expVec, Invariant.expHom]

lemma expVec_delete_letter_eq (R : Relators n) {j g : Fin n}
    (pre post : List (Fin n × Bool)) (b : Bool) (k : Fin n) (hk : k ≠ g)
    (hR : R j = FreeGroup.mk (pre ++ (g, b) :: post)) :
    Invariant.expVec (FreeGroup.mk post * FreeGroup.mk pre) k =
      Invariant.expVec (R j) k := by
  classical
  have hsplit : R j = FreeGroup.mk pre * signedGen g b * FreeGroup.mk post := by
    rw [hR]
    rw [show pre ++ (g, b) :: post = (pre ++ [(g, b)]) ++ post by simp]
    rw [← wordOfList_singleton, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk]
  have hsingle : Invariant.expVec (signedGen g b) k = 0 := by
    cases b <;>
      simp [signedGen, expVec_of_gen, Invariant.expVec_inv, Invariant.genVec, hk]
  rw [hsplit, Invariant.expVec_mul, Invariant.expVec_mul, Invariant.expVec_mul]
  simp only [Pi.add_apply]
  rw [hsingle]
  abel

/-- Pivot reduction with the exponent invariant: deleting pivot letters changes
only the pivot coordinate of the other relators. -/
theorem pivot_reduction_exists_exp (R : Relators n) (i g : Fin n)
    (hi : R i = FreeGroup.of g ∨ R i = (FreeGroup.of g)⁻¹) :
    ∃ S : Relators n, PivotReduced S i g ∧ Reachable R S ∧
      (∀ j : Fin n, j ≠ i → ∀ k : Fin n, k ≠ g →
        Invariant.expVec (S j) k = Invariant.expVec (R j) k) := by
  classical
  suffices h : ∀ N : ℕ, ∀ R : Relators n, totalLength R = N →
      (R i = FreeGroup.of g ∨ R i = (FreeGroup.of g)⁻¹) →
      ∃ S : Relators n, PivotReduced S i g ∧ Reachable R S ∧
        (∀ j : Fin n, j ≠ i → ∀ k : Fin n, k ≠ g →
          Invariant.expVec (S j) k = Invariant.expVec (R j) k) by
    exact h (totalLength R) R rfl hi
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
      intro R hN hiR
      by_cases hred : PivotReduced R i g
      · exact ⟨R, hred, Relation.ReflTransGen.refl, fun _ _ _ _ => rfl⟩
      · rcases exists_pivot_letter_of_not_pivotReduced R hiR hred with
          ⟨j, hij, ⟨⟨g', b⟩, hmem, hg'⟩⟩
        have hg'eq : g' = g := hg'
        subst g'
        rcases exists_append_cons_of_mem hmem with ⟨pre, post, hL⟩
        have hj : R j = FreeGroup.mk (pre ++ (g, b) :: post) := by
          rw [← FreeGroup.mk_toWord (x := R j), hL]
        let S : Relators n :=
          Function.update R j (FreeGroup.mk post * FreeGroup.mk pre)
        have hstep : Reachable R S :=
          reachable_delete_letter R (Ne.symm hij) (R i) rfl hiR pre post b hj
        have hlt : totalLength S < totalLength R :=
          totalLength_update_delete_letter_lt R (Ne.symm hij) pre post b hL
        have hNlt : totalLength S < N := by omega
        have hSi : S i = FreeGroup.of g ∨ S i = (FreeGroup.of g)⁻¹ := by
          have hSR : S i = R i := by
            dsimp [S]
            exact Function.update_of_ne (Ne.symm hij)
              (FreeGroup.mk (post ++ pre)) R
          rw [hSR]
          exact hiR
        have hInvS : ∀ j' : Fin n, j' ≠ i → ∀ k : Fin n, k ≠ g →
            Invariant.expVec (S j') k = Invariant.expVec (R j') k := by
          intro j' hj' k hk
          by_cases hjj : j' = j
          · subst hjj
            dsimp [S]
            rw [Function.update_self]
            exact expVec_delete_letter_eq R pre post b k hk hj
          · have hSR : S j' = R j' := by
              dsimp [S]
              exact Function.update_of_ne hjj (FreeGroup.mk (post ++ pre)) R
            rw [hSR]
        rcases ih (totalLength S) hNlt S rfl hSi with ⟨T, hT, hST, hInvT⟩
        refine ⟨T, hT, hstep.trans hST, ?_⟩
        intro j' hj' k hk
        rw [hInvT j' hj' k hk, hInvS j' hj' k hk]

end A8PivotReduction
end AC
