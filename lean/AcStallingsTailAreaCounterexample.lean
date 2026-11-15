module

public import AcStallingsTailArea
public import Ak3
public import AcProof
public import Mathlib.GroupTheory.FreeGroup.Reduce

@[expose] public section

/-!
# AcStallingsTailAreaCounterexample — the AK(3) no-descent theorem

The current structural `tailArea` is
`lengthOneDefect + generatorImageDefect` (`AcStallingsTailArea.lean:34-41`).
On `Ak3.ak3` it has value `2`: both relators have length greater than one, and
both generator labels occur. The one-step products have length 13, and no
conjugate of either relator has length one because the exponent vectors are
`(3, -4)` and `(1, -1)`, not signed basis vectors.

This file proves the counterexample: `Ak3.ak3` is a trivial non-terminal state,
and no single `Step` lowers its `tailArea`. The current one-step descent
statement is therefore false. The Stallings route remains open for a different
measure.
-/

set_option autoImplicit false

namespace AC
namespace Stallings

/-- The AK(3) state is trivial, is not a signed permutation, and no one-step
successor has a strictly smaller `tailArea`. -/
def tailAreaDescentCounterexample_statement : Prop :=
  PresentsTrivialGroup Ak3.ak3 ∧
    ¬ ProofAttempt.IsSignedPermutation Ak3.ak3 ∧
    ∀ S : Relators 2, Step Ak3.ak3 S → tailArea Ak3.ak3 ≤ tailArea S

lemma expVec_of {n : ℕ} (i : Fin n) :
    Invariant.expVec (FreeGroup.of i) = Invariant.genVec i := by
  simp [Invariant.expVec, Invariant.expHom, FreeGroup.lift_apply_of]

lemma mk_singleton_true {n : ℕ} (i : Fin n) :
    FreeGroup.mk ([(i, true)] : List (Fin n × Bool)) = FreeGroup.of i := rfl

lemma mk_singleton_false {n : ℕ} (i : Fin n) :
    FreeGroup.mk ([(i, false)] : List (Fin n × Bool)) = (FreeGroup.of i)⁻¹ := by
  have h : FreeGroup.invRev ([(i, true)] : List (Fin n × Bool)) = [(i, false)] := rfl
  rw [← h, ← FreeGroup.inv_mk]
  rfl

lemma expVec_eq_genVec_or_neg_of_length_one {n : ℕ} {w : Word n}
    (h : w.toWord.length = 1) :
    ∃ i : Fin n, Invariant.expVec w = Invariant.genVec i ∨
      Invariant.expVec w = -Invariant.genVec i := by
  rcases hw : w.toWord with _ | ⟨head, tail⟩
  · simp [hw] at h
  · rcases tail with _ | ⟨head2, tail2⟩
    · rcases head with ⟨i, b⟩
      refine ⟨i, ?_⟩
      have hw' : w = FreeGroup.mk [(i, b)] := by
        rw [← FreeGroup.mk_toWord (x := w), hw]
      cases b
      · right
        rw [hw', mk_singleton_false, Invariant.expVec_inv, expVec_of]
      · left
        rw [hw', mk_singleton_true, expVec_of]
    · rw [hw] at h
      simp at h

lemma expVec_ak3_ne_genVec (i j : Fin 2) :
    Invariant.expVec (Ak3.ak3 i) ≠ Invariant.genVec j ∧
    Invariant.expVec (Ak3.ak3 i) ≠ -Invariant.genVec j := by
  fin_cases i <;> fin_cases j <;> decide

lemma tailArea_ge_two {R : Relators 2}
    (h0 : (R 0).toWord.length ≠ 1) (h1 : (R 1).toWord.length ≠ 1) :
    2 ≤ tailArea R := by
  unfold tailArea lengthOneDefect generatorImageDefect
  have hfilter : (Finset.univ.filter (fun i : Fin 2 => (R i).toWord.length = 1)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _
    fin_cases i
    · exact h0
    · exact h1
  rw [hfilter]
  simp

lemma conj_length_ne_one (i : Fin 2) (w : Word 2) :
    (w * Ak3.ak3 i * w⁻¹).toWord.length ≠ 1 := by
  intro hlen
  obtain ⟨j, hj | hj⟩ := expVec_eq_genVec_or_neg_of_length_one hlen
  · have he : Invariant.expVec (w * Ak3.ak3 i * w⁻¹) = Invariant.expVec (Ak3.ak3 i) :=
      Invariant.expVec_conj
    rw [he] at hj
    exact (expVec_ak3_ne_genVec i j).1 hj
  · have he : Invariant.expVec (w * Ak3.ak3 i * w⁻¹) = Invariant.expVec (Ak3.ak3 i) :=
      Invariant.expVec_conj
    rw [he] at hj
    exact (expVec_ak3_ne_genVec i j).2 hj

lemma ak3_not_signedPermutation : ¬ ProofAttempt.IsSignedPermutation Ak3.ak3 := by
  rintro ⟨σ, hσ, ε, hε⟩
  have h0 := hε 0
  have len0 : (Ak3.ak3 0).toWord.length = 1 := by
    rw [h0]
    split <;> simp
  have h7 : (Ak3.ak3 0).toWord.length = 7 := by decide
  omega

lemma tailArea_ak3 : tailArea Ak3.ak3 = 2 := by decide

theorem ak3_no_descent :
    ∀ S : Relators 2, Step Ak3.ak3 S → tailArea Ak3.ak3 ≤ tailArea S := by
  intro S hS
  rw [tailArea_ak3]
  cases hS with
  | inv i =>
      fin_cases i <;> decide
  | mulRight i j hij =>
      fin_cases i <;> fin_cases j <;> simp_all <;> decide
  | conj i w =>
      fin_cases i
      · apply tailArea_ge_two
        · simpa [Function.update] using conj_length_ne_one 0 w
        · simp [Function.update]; decide
      · apply tailArea_ge_two
        · simp [Function.update]; decide
        · simpa [Function.update] using conj_length_ne_one 1 w

/-- The AK(3) state is a counterexample to the current one-step descent
statement. -/
theorem tailAreaDescentCounterexample :
    tailAreaDescentCounterexample_statement :=
  ⟨Ak3.ak3_presentsTrivial, ak3_not_signedPermutation, ak3_no_descent⟩

end Stallings
end AC

#print axioms AC.Stallings.tailAreaDescentCounterexample
