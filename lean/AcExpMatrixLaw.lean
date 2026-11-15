module

/-
  The exponent-matrix move law, at every rank.

  The corpus already carries the exponent-span law (`step_expSpan`) and three of
  the four row laws for the exponent matrix (`expMatrix_rowAdd`,
  `expMatrix_rowNeg`, `expMatrix_rowSwap`). This module closes the set with the
  conjugation law and derives the determinant law at general rank, which existed
  only at rank two (`BranchB.expDeterminant_step`).

  Together these are the compiled form of the transformation law stated in prose
  at
    EXTERNAL_REPOS/COMPETITORS/Andrews-Curtis-Conjecture/research/directions/
    invariant-ideas/idea.md:180-196  (MIT licence, Copyright 2026 Pragyaan Gaur)
  No code or proof text is copied from that repository.
-/
public import AcEuclidGeneral

@[expose] public section

namespace AC.EuclidGeneral

variable {n : ℕ}

/-- Conjugation by an arbitrary word does not change the exponent matrix. This is
the fourth and last per-move row law. -/
lemma expMatrix_conj (R : Relators n) (i : Fin n) (w : Word n) :
    expMatrix (Function.update R i (w * R i * w⁻¹)) = expMatrix R := by
  rw [expMatrix_update, Invariant.expVec_conj]
  rw [show Invariant.expVec (R i) = (expMatrix R) i from rfl]
  exact Function.update_eq_self i (expMatrix R)

/-- Row addition leaves the determinant fixed, provided the two rows differ. -/
lemma expMatrix_det_rowAdd (R : Relators n) (i j : Fin n) (hij : i ≠ j) (c : ℤ) :
    (expMatrix (Function.update R i (R i * R j ^ c))).det = (expMatrix R).det := by
  rw [expMatrix_rowAdd]
  exact Matrix.det_updateRow_add_smul_self (expMatrix R) hij c

/-- Row negation multiplies the determinant by minus one. -/
lemma expMatrix_det_rowNeg (R : Relators n) (i : Fin n) :
    (expMatrix (Function.update R i (R i)⁻¹)).det = -(expMatrix R).det := by
  rw [expMatrix_rowNeg]
  change (Matrix.updateRow (expMatrix R) i (-(expMatrix R i))).det = -(expMatrix R).det
  rw [show -(expMatrix R i) = (-1 : ℤ) • expMatrix R i from
    (neg_one_smul ℤ (expMatrix R i)).symm]
  rw [Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  simp

/-- One official move changes the determinant by at most a sign, at every rank. -/
theorem expMatrix_det_step {R S : Relators n} (h : Step R S) :
    (expMatrix S).det = (expMatrix R).det ∨
      (expMatrix S).det = -(expMatrix R).det := by
  cases h with
  | inv i => exact Or.inr (expMatrix_det_rowNeg R i)
  | mulRight i j hij => exact Or.inl (by simpa using expMatrix_det_rowAdd R i j hij 1)
  | conj i w => exact Or.inl (by rw [expMatrix_conj])

/-- Along any finite route the determinant changes by at most a sign. -/
theorem expMatrix_det_reachable {R S : Relators n} (h : Reachable R S) :
    (expMatrix S).det = (expMatrix R).det ∨
      (expMatrix S).det = -(expMatrix R).det := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hstep ih =>
      rcases ih with h' | h'
      · rcases expMatrix_det_step hstep with h'' | h''
        · exact Or.inl (by rw [h'', h'])
        · exact Or.inr (by rw [h'', h'])
      · rcases expMatrix_det_step hstep with h'' | h''
        · exact Or.inr (by rw [h'', h'])
        · exact Or.inl (by rw [h'', h', neg_neg])

end AC.EuclidGeneral
