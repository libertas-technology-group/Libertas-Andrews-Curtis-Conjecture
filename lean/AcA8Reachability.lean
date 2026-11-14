import AC
import AcProof
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Tactic.Group

/-!
# AcA8Reachability — the buildable delete-letter helper

This module restates the Branch A delete-letter helper in the accepted corpus. The
positive conjugation macro is corrected: it inverts the pivot, applies the negative
macro, and restores the pivot. The resulting sequence reaches `q * p` rather than the
incorrect `q * p * u * u`.
-/

set_option autoImplicit false

namespace AC
namespace A8Reachability

open AC

variable {n : ℕ}

/-- The signed generator `g` or its inverse, as a word. -/
def signedGen (g : Fin n) (ε : Bool) : Word n :=
  if ε then FreeGroup.of g else (FreeGroup.of g)⁻¹

/-- The free-group element represented by a list of letters. -/
abbrev wordOfList (L : List (Fin n × Bool)) : Word n :=
  FreeGroup.mk L

lemma wordOfList_singleton (g : Fin n) (b : Bool) :
    wordOfList [(g, b)] = signedGen g b := by
  cases b with
  | false => simp [wordOfList, signedGen, FreeGroup.of, FreeGroup.invRev]
  | true => simp [wordOfList, signedGen, FreeGroup.of]

lemma reachable_conj_mul_conj_neg (R : Relators n) {i j : Fin n} (hij : i ≠ j)
    (u p q : Word n) (hi : R i = u) (hj : R j = p * u⁻¹ * q) :
    Reachable R (Function.update R j (q * p)) := by
  classical
  let S1 : Relators n := Function.update R j (p⁻¹ * R j * p)
  have h1 : Step R S1 := by simpa [S1] using Step.conj R j p⁻¹
  have hS1j : S1 j = u⁻¹ * q * p := by
    dsimp [S1]
    rw [Function.update_self, hj]
    group
  have hS1i : S1 i = u := by
    dsimp [S1]
    rw [Function.update_of_ne hij, hi]
  let S2 : Relators n := Function.update S1 j (S1 j * S1 i)
  have h2 : Step S1 S2 := Step.mulRight S1 j i (Ne.symm hij)
  have hS2j : S2 j = u⁻¹ * q * p * u := by
    dsimp [S2]
    rw [Function.update_self, hS1j, hS1i]
  let S3 : Relators n := Function.update S2 j (u * S2 j * u⁻¹)
  have h3 : Step S2 S3 := by simpa [S3] using Step.conj S2 j u
  have hS3j : S3 j = q * p := by
    dsimp [S3]
    rw [Function.update_self, hS2j]
    group
  have hS3 : S3 = Function.update R j (q * p) := by
    funext k
    by_cases hk : k = j
    · subst hk
      rw [hS3j, Function.update_self]
    · have hkj : j ≠ k := Ne.symm hk
      dsimp [S3, S2, S1]
      rw [Function.update_of_ne hk, Function.update_of_ne hk,
        Function.update_of_ne hk, Function.update_of_ne hk]
  rw [hS3] at h3
  exact (Relation.ReflTransGen.single h1).trans
    ((Relation.ReflTransGen.single h2).trans (Relation.ReflTransGen.single h3))

lemma reachable_conj_mul_conj_pos (R : Relators n) {i j : Fin n} (hij : i ≠ j)
    (u p q : Word n) (hi : R i = u) (hj : R j = p * u * q) :
    Reachable R (Function.update R j (q * p)) := by
  classical
  let S1 : Relators n := Function.update R i (R i)⁻¹
  have h1 : Step R S1 := by simpa [S1] using Step.inv R i
  have hS1i : S1 i = u⁻¹ := by
    dsimp [S1]
    rw [Function.update_self, hi]
  have hS1j : S1 j = p * (u⁻¹)⁻¹ * q := by
    dsimp [S1]
    rw [Function.update_of_ne (Ne.symm hij), hj]
    group
  have hneg := reachable_conj_mul_conj_neg S1 hij (u⁻¹) p q hS1i hS1j
  let T : Relators n := Function.update S1 j (q * p)
  let S2 : Relators n := Function.update T i (T i)⁻¹
  have hstep : Step T S2 := by simpa [S2] using Step.inv T i
  have hT_i : T i = u⁻¹ := by
    dsimp [T]
    rw [Function.update_of_ne hij, hS1i]
  have hS2eq : S2 = Function.update R j (q * p) := by
    funext k
    by_cases hk : k = j
    · subst hk
      dsimp [S2, T]
      rw [Function.update_of_ne (Ne.symm hij), Function.update_self, Function.update_self]
    · by_cases hki : k = i
      · subst hki
        dsimp [S2, T]
        rw [Function.update_self, Function.update_of_ne hij, hS1i]
        rw [Function.update_of_ne hij, hi]
        group
      · dsimp [S2, T, S1]
        rw [Function.update_of_ne hki, Function.update_of_ne hk,
          Function.update_of_ne hki, Function.update_of_ne hk]
  rw [hS2eq] at hstep
  exact (Relation.ReflTransGen.single h1).trans
    (hneg.trans (Relation.ReflTransGen.single hstep))

lemma reachable_delete_letter (R : Relators n) {i j g : Fin n} (hij : i ≠ j)
    (u : Word n) (hi : R i = u)
    (hu : u = FreeGroup.of g ∨ u = (FreeGroup.of g)⁻¹)
    (pre post : List (Fin n × Bool)) (b : Bool)
    (hj : R j = FreeGroup.mk (pre ++ (g, b) :: post)) :
    Reachable R (Function.update R j (FreeGroup.mk post * FreeGroup.mk pre)) := by
  classical
  have hsplit : R j = FreeGroup.mk pre * signedGen g b * FreeGroup.mk post := by
    rw [hj]
    rw [show pre ++ (g, b) :: post = (pre ++ [(g, b)]) ++ post by simp]
    rw [← wordOfList_singleton, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk]
  cases b
  · cases hu with
    | inl hu =>
        exact reachable_conj_mul_conj_neg R hij (FreeGroup.of g)
          (FreeGroup.mk pre) (FreeGroup.mk post) (by simpa [hu] using hi)
          (by simpa [hu, signedGen] using hsplit)
    | inr hu =>
        exact reachable_conj_mul_conj_pos R hij u
          (FreeGroup.mk pre) (FreeGroup.mk post) hi
          (by simpa [hu, signedGen] using hsplit)
  · cases hu with
    | inl hu =>
        exact reachable_conj_mul_conj_pos R hij (FreeGroup.of g)
          (FreeGroup.mk pre) (FreeGroup.mk post) (by simpa [hu] using hi)
          (by simpa [hu, signedGen] using hsplit)
    | inr hu =>
        exact reachable_conj_mul_conj_neg R hij u
          (FreeGroup.mk pre) (FreeGroup.mk post) hi
          (by simpa [hu, signedGen] using hsplit)

/-- A pure conjugate of a signed generator reaches that signed generator in one move. -/
lemma reachable_conj_signedGen (R : Relators n) {i : Fin n} (u : Word n)
    (g : Fin n) (b : Bool)
    (hi : R i = u * signedGen g b * u⁻¹) :
    Reachable R (Function.update R i (signedGen g b)) := by
  classical
  let S : Relators n := Function.update R i (u⁻¹ * R i * (u⁻¹)⁻¹)
  have h1 : Step R S := by simpa [S] using Step.conj R i (u⁻¹)
  have hS : S = Function.update R i (signedGen g b) := by
    funext j
    by_cases hj : j = i
    · subst hj
      dsimp [S]
      rw [Function.update_self, hi]
      group
      rw [Function.update_self]
    · dsimp [S]
      rw [Function.update_of_ne hj, Function.update_of_ne hj]
  rw [hS] at h1
  exact Relation.ReflTransGen.single h1

end A8Reachability
end AC
