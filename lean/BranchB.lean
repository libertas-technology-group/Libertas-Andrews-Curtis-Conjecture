module

public import AC
public import AcInvariant
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Data.Int.Order.Units
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Branch B: the rank-two structural classification

The classification has four coordinates: the exponent determinant, the first-letter
profile, the total relator length, and the exponent-envelope predicate. The determinant
is a class function up to sign and is normalised by one official move. The other three
are coordinates of the encoding, not invariants of the Andrews–Curtis relation.

`expDeterminant_eq_pm_one_of_presents` uses one supplied theorem from `AcInvariant`,
`expSpan_eq_top_of_presents`. Every other declaration is closed here. A fresh reader
checks the file on the pinned toolchain.
-/

namespace AC
namespace BranchB

open Invariant

variable {n : ℕ}

/-! ## 1. The exponent matrix and its determinant -/

/-- The exponent matrix of a rank-two presentation. Row `i` is the exponent vector of
relator `i`; column `j` is the exponent of generator `j`. -/
noncomputable def expMatrix (R : Relators 2) : Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j => expVec (R i) j

/-- The determinant of the exponent matrix, written out at rank two. -/
noncomputable def expDeterminant (R : Relators 2) : ℤ :=
  expVec (R 0) 0 * expVec (R 1) 1 - expVec (R 0) 1 * expVec (R 1) 0

/-- The explicit determinant is the matrix determinant. -/
theorem expDeterminant_eq_matrix_det (R : Relators 2) :
    expDeterminant R = Matrix.det (expMatrix R) := by
  simp [expDeterminant, expMatrix, Matrix.det_fin_two]

/-- The exponent vector of a free generator is the corresponding standard basis vector. -/
@[simp] theorem expVec_of (i : Fin n) :
    expVec (FreeGroup.of i) = genVec i := by
  simp [expVec, expHom]

/-- The standard rank-two presentation has exponent matrix the identity. -/
theorem expMatrix_standard : expMatrix (standard 2) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [expMatrix, standard, genVec, Pi.single]

/-- The standard rank-two presentation has determinant `+1`. -/
theorem expDeterminant_standard : expDeterminant (standard 2) = 1 := by
  rw [expDeterminant_eq_matrix_det, expMatrix_standard, Matrix.det_one]

/-! ## 2. Each official move preserves the determinant up to sign -/

/-- Inverting relator `0` negates the determinant. -/
theorem expDeterminant_inv_zero (R : Relators 2) :
    expDeterminant (Function.update R 0 (R 0)⁻¹) = -expDeterminant R := by
  simp only [expDeterminant, Function.update_self,
    Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide),
    expVec_inv, Pi.neg_apply]
  ring

/-- Inverting relator `1` negates the determinant. -/
theorem expDeterminant_inv_one (R : Relators 2) :
    expDeterminant (Function.update R 1 (R 1)⁻¹) = -expDeterminant R := by
  simp only [expDeterminant, Function.update_self,
    Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide),
    expVec_inv, Pi.neg_apply]
  ring

/-- Right-multiplying relator `0` by relator `1` preserves the determinant. -/
theorem expDeterminant_mulRight_zero_one (R : Relators 2) :
    expDeterminant (Function.update R 0 (R 0 * R 1)) = expDeterminant R := by
  simp only [expDeterminant, Function.update_self,
    Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide),
    expVec_mul, Pi.add_apply]
  ring

/-- Right-multiplying relator `1` by relator `0` preserves the determinant. -/
theorem expDeterminant_mulRight_one_zero (R : Relators 2) :
    expDeterminant (Function.update R 1 (R 1 * R 0)) = expDeterminant R := by
  simp only [expDeterminant, Function.update_self,
    Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide),
    expVec_mul, Pi.add_apply]
  ring

/-- Conjugating relator `0` by any word preserves the determinant. -/
theorem expDeterminant_conj_zero (R : Relators 2) (w : Word 2) :
    expDeterminant (Function.update R 0 (w * R 0 * w⁻¹)) = expDeterminant R := by
  simp only [expDeterminant, Function.update_self,
    Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide), expVec_conj]

/-- Conjugating relator `1` by any word preserves the determinant. -/
theorem expDeterminant_conj_one (R : Relators 2) (w : Word 2) :
    expDeterminant (Function.update R 1 (w * R 1 * w⁻¹)) = expDeterminant R := by
  simp only [expDeterminant, Function.update_self,
    Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), expVec_conj]

/-- Every official step either preserves or negates the determinant. -/
theorem expDeterminant_step {R S : Relators 2} (h : Step R S) :
    expDeterminant S = expDeterminant R ∨ expDeterminant S = -expDeterminant R := by
  cases h with
  | inv i =>
      right
      fin_cases i
      · exact expDeterminant_inv_zero R
      · exact expDeterminant_inv_one R
  | mulRight i j hij =>
      left
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact expDeterminant_mulRight_zero_one R
      · exact expDeterminant_mulRight_one_zero R
      · exact absurd rfl hij
  | conj i w =>
      left
      fin_cases i
      · exact expDeterminant_conj_zero R w
      · exact expDeterminant_conj_one R w

/-- Along every finite path the determinant is preserved up to sign. -/
theorem expDeterminant_reachable {R S : Relators 2} (h : Reachable R S) :
    expDeterminant S = expDeterminant R ∨ expDeterminant S = -expDeterminant R := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hstep ih =>
      rcases ih with h1 | h1
      · rcases expDeterminant_step hstep with h2 | h2
        · exact Or.inl (h2.trans h1)
        · exact Or.inr (by rw [h2, h1])
      · rcases expDeterminant_step hstep with h2 | h2
        · exact Or.inr (by rw [h2, h1])
        · exact Or.inl (by rw [h2, h1, neg_neg])

/-! ## 3. The unimodularity theorem -/

/-- A rank-two presentation whose exponent span is the whole lattice has determinant `±1`.

Writing each standard basis vector as an integer combination of the two exponent rows
gives a coefficient matrix `C` with `C * expMatrix R = 1`. Taking determinants gives
`det C * det (expMatrix R) = 1`, and the units of `ℤ` are `±1`. This is the algebraic
core; the group-theoretic input is the next theorem. -/
theorem expDeterminant_eq_pm_one_of_span_top {R : Relators 2}
    (htop : expSpan R = ⊤) : expDeterminant R = 1 ∨ expDeterminant R = -1 := by
  classical
  have hmem0 : (Pi.single (0 : Fin 2) (1 : ℤ)) ∈ expSpan R := by
    rw [htop]
    exact Submodule.mem_top
  have hmem1 : (Pi.single (1 : Fin 2) (1 : ℤ)) ∈ expSpan R := by
    rw [htop]
    exact Submodule.mem_top
  have hspan0 : (Pi.single (0 : Fin 2) (1 : ℤ)) ∈
      Submodule.span ℤ (Set.range (fun i : Fin 2 => expVec (R i))) := hmem0
  have hspan1 : (Pi.single (1 : Fin 2) (1 : ℤ)) ∈
      Submodule.span ℤ (Set.range (fun i : Fin 2 => expVec (R i))) := hmem1
  obtain ⟨c0, hc0⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hspan0
  obtain ⟨c1, hc1⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hspan1
  have h00 : c0 0 * expVec (R 0) 0 + c0 1 * expVec (R 1) 0 = 1 := by
    have := congrFun hc0 0
    simpa [Fin.sum_univ_two, Pi.single, Pi.smul_apply, smul_eq_mul] using this
  have h01 : c0 0 * expVec (R 0) 1 + c0 1 * expVec (R 1) 1 = 0 := by
    have := congrFun hc0 1
    simpa [Fin.sum_univ_two, Pi.single, Pi.smul_apply, smul_eq_mul] using this
  have h10 : c1 0 * expVec (R 0) 0 + c1 1 * expVec (R 1) 0 = 0 := by
    have := congrFun hc1 0
    simpa [Fin.sum_univ_two, Pi.single, Pi.smul_apply, smul_eq_mul] using this
  have h11 : c1 0 * expVec (R 0) 1 + c1 1 * expVec (R 1) 1 = 1 := by
    have := congrFun hc1 1
    simpa [Fin.sum_univ_two, Pi.single, Pi.smul_apply, smul_eq_mul] using this
  let C : Matrix (Fin 2) (Fin 2) ℤ := !![c0 0, c0 1; c1 0, c1 1]
  have hCM : C * expMatrix R = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [C, expMatrix, Matrix.mul_apply, Fin.sum_univ_two, h00, h01, h10, h11]
  have hdet : Matrix.det C * Matrix.det (expMatrix R) = 1 := by
    rw [← Matrix.det_mul, hCM, Matrix.det_one]
  have hunit : IsUnit (Matrix.det (expMatrix R)) := by
    rw [isUnit_iff_dvd_one]
    exact ⟨Matrix.det C, by rw [mul_comm, hdet]⟩
  have hpm : Matrix.det (expMatrix R) = 1 ∨ Matrix.det (expMatrix R) = -1 :=
    Int.isUnit_iff.mp hunit
  rw [expDeterminant_eq_matrix_det]
  exact hpm

/-- A balanced rank-two presentation of the trivial group has determinant `±1`. The
exponent span is the whole lattice by `Invariant.expSpan_eq_top_of_presents`. -/
theorem expDeterminant_eq_pm_one_of_presents {R : Relators 2}
    (h : PresentsTrivialGroup R) : expDeterminant R = 1 ∨ expDeterminant R = -1 :=
  expDeterminant_eq_pm_one_of_span_top (expSpan_eq_top_of_presents h)

/-! ## 4. Total relator length -/

/-- The total relator length of a rank-two presentation. -/
noncomputable def totalLength (R : Relators 2) : ℕ :=
  FreeGroup.norm (R 0) + FreeGroup.norm (R 1)

/-- Inverting one relator preserves the total relator length. -/
theorem totalLength_inv (R : Relators 2) (i : Fin 2) :
    totalLength (Function.update R i (R i)⁻¹) = totalLength R := by
  unfold totalLength
  fin_cases i <;> simp [Function.update_self]

/-- The standard rank-two presentation has total relator length two. -/
theorem totalLength_standard : totalLength (standard 2) = 2 := by
  simp [totalLength, standard, FreeGroup.norm, FreeGroup.toWord_of]

/-- One official move changes the total relator length, so length is not an invariant. -/
theorem exists_step_changing_totalLength :
    ∃ R S : Relators 2, Step R S ∧ totalLength S ≠ totalLength R := by
  refine ⟨standard 2, Function.update (standard 2) 0 (standard 2 0 * standard 2 1),
    Step.mulRight (standard 2) 0 1 (by decide), ?_⟩
  simp [totalLength, standard, FreeGroup.norm, FreeGroup.toWord_mul, FreeGroup.toWord_of,
    Function.update_self]

/-! ## 5. The sign-class reachability claim -/

/-- The one-move sign normalisation: an official step, a sign flip, and a length-preserving
map. -/
theorem signNormalisation (R : Relators 2) :
    Step R (Function.update R 0 (R 0)⁻¹) ∧
    expDeterminant (Function.update R 0 (R 0)⁻¹) = -expDeterminant R ∧
    totalLength (Function.update R 0 (R 0)⁻¹) = totalLength R :=
  ⟨Step.inv R 0, expDeterminant_inv_zero R, totalLength_inv R 0⟩

/-- Every negative-determinant state reaches a positive-determinant state in one official
move of the same total relator length. -/
theorem negative_reaches_positive_one_move (R : Relators 2) (h : expDeterminant R = -1) :
    ∃ S : Relators 2, Step R S ∧ expDeterminant S = 1 ∧ totalLength S = totalLength R := by
  refine ⟨Function.update R 0 (R 0)⁻¹, Step.inv R 0, ?_, totalLength_inv R 0⟩
  rw [expDeterminant_inv_zero, h]
  norm_num

/-- Every positive-determinant state reaches a negative-determinant state in one official
move of the same total relator length. -/
theorem positive_reaches_negative_one_move (R : Relators 2) (h : expDeterminant R = 1) :
    ∃ S : Relators 2, Step R S ∧ expDeterminant S = -1 ∧ totalLength S = totalLength R := by
  refine ⟨Function.update R 0 (R 0)⁻¹, Step.inv R 0, ?_, totalLength_inv R 0⟩
  rw [expDeterminant_inv_zero, h]

/-- The closed part of the classification theorem. -/
theorem expDeterminant_classification_closed (R : Relators 2) :
    (∀ S : Relators 2, Step R S →
      expDeterminant S = expDeterminant R ∨ expDeterminant S = -expDeterminant R) ∧
    (expDeterminant R = 1 →
      ∃ S : Relators 2, Step R S ∧ expDeterminant S = -1 ∧
        totalLength S = totalLength R) ∧
    (expDeterminant R = -1 →
      ∃ S : Relators 2, Step R S ∧ expDeterminant S = 1 ∧
        totalLength S = totalLength R) :=
  ⟨fun _ h => expDeterminant_step h,
   fun h => positive_reaches_negative_one_move R h,
   fun h => negative_reaches_positive_one_move R h⟩

/-- The classification theorem: a trivial rank-two presentation lies in exactly one of the
two determinant classes, and each class reaches the other in one official move of the same
total relator length. -/
theorem expDeterminant_dichotomy_of_presents {R : Relators 2}
    (h : PresentsTrivialGroup R) :
    (expDeterminant R = 1 ∧ ∃ S : Relators 2, Step R S ∧ expDeterminant S = -1 ∧
      totalLength S = totalLength R) ∨
    (expDeterminant R = -1 ∧ ∃ S : Relators 2, Step R S ∧ expDeterminant S = 1 ∧
      totalLength S = totalLength R) := by
  rcases expDeterminant_eq_pm_one_of_presents h with h1 | h1
  · obtain ⟨S, hstep, hdet, hlen⟩ := positive_reaches_negative_one_move R h1
    exact Or.inl ⟨h1, S, hstep, hdet, hlen⟩
  · obtain ⟨S, hstep, hdet, hlen⟩ := negative_reaches_positive_one_move R h1
    exact Or.inr ⟨h1, S, hstep, hdet, hlen⟩

/-! ## 6. The exponent-envelope family -/

/-- The exponent envelope: the first relator has exponent vector `(0,-1)` and the second
relator has `x`-exponent `1`. This is the scored subset that shares the training algebraic
signature. -/
def InExponentEnvelope (R : Relators 2) : Prop :=
  expVec (R 0) 0 = 0 ∧ expVec (R 0) 1 = -1 ∧ expVec (R 1) 0 = 1

/-- The exponent envelope is contained in the positive-determinant class. -/
theorem inExponentEnvelope_expDeterminant_eq_one {R : Relators 2}
    (h : InExponentEnvelope R) : expDeterminant R = 1 := by
  obtain ⟨h00, h01, h10⟩ := h
  unfold expDeterminant
  rw [h00, h01, h10]
  ring

/-- The standard presentation is outside the envelope, so the inclusion is strict. -/
theorem standard_not_inExponentEnvelope : ¬ InExponentEnvelope (standard 2) := by
  intro h
  obtain ⟨h00, -, -⟩ := h
  have h1 : expVec (standard 2 0) 0 = 1 := by
    simp [standard, genVec, Pi.single]
  rw [h1] at h00
  norm_num at h00

/-! ## 7. The first-letter profile -/

/-- The first letter of a freely reduced word, or `none` for the empty word. -/
def firstLetter (w : Word 2) : Option (Fin 2 × Bool) :=
  w.toWord.head?

/-- The first-letter profile of a rank-two presentation. -/
def firstLetterProfile (R : Relators 2) :
    Option (Fin 2 × Bool) × Option (Fin 2 × Bool) :=
  (firstLetter (R 0), firstLetter (R 1))

/-- The standard first relator begins with the positive first generator. -/
theorem firstLetter_standard : firstLetter (standard 2 0) = some (0, true) := rfl

/-- Conjugating the first relator by the second generator changes its first letter. -/
theorem firstLetter_conj :
    firstLetter (FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹) =
      some (1, true) := by
  unfold firstLetter
  rw [FreeGroup.toWord_mul, FreeGroup.toWord_mul, FreeGroup.toWord_of,
    FreeGroup.toWord_of, FreeGroup.toWord_inv, FreeGroup.toWord_of]
  decide

/-- The first-letter profile is not an invariant of the Andrews–Curtis relation. -/
theorem firstLetter_not_invariant :
    firstLetter (FreeGroup.of 0) ≠
      firstLetter (FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹) := by
  rw [firstLetter_conj]
  decide

/-- One official move changes the first letter of the first relator. -/
theorem exists_step_changing_firstLetter :
    ∃ R S : Relators 2, Step R S ∧ firstLetter (R 0) ≠ firstLetter (S 0) := by
  refine ⟨standard 2,
    Function.update (standard 2) 0
      (FreeGroup.of 1 * standard 2 0 * (FreeGroup.of 1)⁻¹),
    Step.conj (standard 2) 0 (FreeGroup.of 1), ?_⟩
  have h := firstLetter_not_invariant
  simpa [standard, Function.update_self] using h

end BranchB
end AC
