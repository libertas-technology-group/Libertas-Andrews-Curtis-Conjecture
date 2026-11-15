module

public import AC
public import AcInvariant
public import AcProof
public import BranchB
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Int.Order.Units
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Euclidean row reduction at rank two

This file closes the rank-two abelian reduction. The exponent vectors of a rank-two
relator tuple form a `2 x 2` integer matrix. Row addition is `Step.mulRight`, the row
swap is `ProofAttempt.reachable_swap`, and the terminal set is the set of signed
permutation matrices at exponent level.

The reduction is the Euclidean algorithm on the first column of that matrix. One step
replaces the top entry by its remainder modulo the bottom entry and then swaps the rows,
so the absolute value of the bottom entry strictly decreases. When the bottom entry reaches
zero, the determinant being a unit forces the diagonal entries to be `+-1`, and one further
row addition clears the off-diagonal entry.
-/

namespace AC
namespace Euclid

open Invariant
open BranchB

/-! ## 1. Row addition -/

/-- Row addition at rank two: replacing the first relator by its product with the second
is a single official move. On exponent vectors this is `u + v`. -/
theorem row_add_reachable (R : Relators 2) :
    Reachable R (Function.update R 0 (R 0 * R 1)) :=
  Relation.ReflTransGen.single (Step.mulRight R 0 1 (by decide))

/-! ## 2. The abelian terminal predicate -/

/-- The abelian terminal set at rank two: the exponent matrix is a signed permutation
matrix. The body is the same as `AC.BranchA.IsAbelianTerminal`; the predicate is restated
here so this file imports only modules whose proofs are complete. -/
def IsAbelianTerminal (R : Relators 2) : Prop :=
  ∃ σ : Fin 2 → Fin 2, Function.Bijective σ ∧ ∃ ε : Fin 2 → Bool,
    ∀ i : Fin 2, expVec (R i) = if ε i then genVec (σ i) else -genVec (σ i)

/-! ## 3. Row swap and diagonal matrices -/

/-- Exchange the two rows of a `2 x 2` matrix. -/
def swapRows (M : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j => M (if i = 0 then 1 else 0) j

@[simp] lemma swapRows_zero (M : Matrix (Fin 2) (Fin 2) ℤ) (j : Fin 2) :
    swapRows M 0 j = M 1 j := by simp [swapRows]

@[simp] lemma swapRows_one (M : Matrix (Fin 2) (Fin 2) ℤ) (j : Fin 2) :
    swapRows M 1 j = M 0 j := by simp [swapRows]

/-- A diagonal matrix whose diagonal entries are units of `ℤ`. -/
def IsDiagonalUnimodular (M : Matrix (Fin 2) (Fin 2) ℤ) : Prop :=
  (M 0 0 = 1 ∨ M 0 0 = -1) ∧ M 0 1 = 0 ∧ M 1 0 = 0 ∧ (M 1 1 = 1 ∨ M 1 1 = -1)

/-! ## 4. Entry lemmas -/

@[simp] lemma update0_zero_zero (M : Matrix (Fin 2) (Fin 2) ℤ) (r : Fin 2 → ℤ) :
    (Function.update M 0 r) 0 0 = r 0 := by simp [Function.update]

@[simp] lemma update0_zero_one (M : Matrix (Fin 2) (Fin 2) ℤ) (r : Fin 2 → ℤ) :
    (Function.update M 0 r) 0 1 = r 1 := by simp [Function.update]

@[simp] lemma update0_one_zero (M : Matrix (Fin 2) (Fin 2) ℤ) (r : Fin 2 → ℤ) :
    (Function.update M 0 r) 1 0 = M 1 0 := by simp [Function.update]

@[simp] lemma update0_one_one (M : Matrix (Fin 2) (Fin 2) ℤ) (r : Fin 2 → ℤ) :
    (Function.update M 0 r) 1 1 = M 1 1 := by simp [Function.update]

lemma expMatrix_update0 (R : Relators 2) (x : Word 2) :
    expMatrix (Function.update R 0 x) = Function.update (expMatrix R) 0 (expVec x) := by
  funext i j
  by_cases h : i = 0
  · subst h
    simp [expMatrix, Function.update]
  · simp [expMatrix, Function.update, h]

lemma expMatrix_swap (R : Relators 2) :
    expMatrix (Function.update (Function.update R 0 (R 1)) 1 (R 0)) =
      swapRows (expMatrix R) := by
  funext i j
  fin_cases i
  · show expVec (Function.update (Function.update R 0 (R 1)) 1 (R 0) 0) j = _
    simp [expMatrix]
  · show expVec (Function.update (Function.update R 0 (R 1)) 1 (R 0) 1) j = _
    simp [expMatrix]

lemma expVec_zpow {n : ℕ} (w : Word n) (k : ℤ) : expVec (w ^ k) = k • expVec w := by
  simp [expVec, map_zpow]

@[simp] lemma expMatrix_zero (R : Relators 2) : expMatrix R 0 = expVec (R 0) := rfl

@[simp] lemma expMatrix_one (R : Relators 2) : expMatrix R 1 = expVec (R 1) := rfl

lemma expMatrix_update0_mul_zpow (R : Relators 2) (k : ℤ) :
    expMatrix (Function.update R 0 (R 0 * R 1 ^ k)) =
      Function.update (expMatrix R) 0 (expMatrix R 0 + k • expMatrix R 1) := by
  rw [expMatrix_update0, expVec_mul, expVec_zpow, expMatrix_zero, expMatrix_one]

/-! ## 5. Determinant of each row operation -/

lemma det_update0_add (M : Matrix (Fin 2) (Fin 2) ℤ) (k : ℤ) :
    Matrix.det (Function.update M 0 (M 0 + k • M 1)) = Matrix.det M := by
  rw [Matrix.det_fin_two (A := Function.update M 0 (M 0 + k • M 1)),
    Matrix.det_fin_two (A := M)]
  simp [Function.update, Pi.add_apply]
  ring

lemma det_swapRows (M : Matrix (Fin 2) (Fin 2) ℤ) :
    Matrix.det (swapRows M) = -Matrix.det M := by
  simp [Matrix.det_fin_two, swapRows]
  ring

/-! ## 6. Row addition with an integer multiplier is reachable -/

lemma row_mul_pow_reachable (R : Relators 2) (n : ℕ) :
    Reachable R (Function.update R 0 (R 0 * R 1 ^ n)) := by
  induction n with
  | zero => simpa [Reachable, Function.update] using (Relation.ReflTransGen.refl : Reachable R R)
  | succ n ih =>
      have hstep : Reachable (Function.update R 0 (R 0 * R 1 ^ n))
          (Function.update R 0 (R 0 * R 1 ^ (n + 1))) := by
        refine Relation.ReflTransGen.single ?_
        have hs := Step.mulRight (Function.update R 0 (R 0 * R 1 ^ n)) 0 1 (by decide)
        have e1 : (Function.update R 0 (R 0 * R 1 ^ n)) 0 = R 0 * R 1 ^ n := by simp
        have e2 : (Function.update R 0 (R 0 * R 1 ^ n)) 1 = R 1 := by simp
        rw [e1, e2] at hs
        rw [Function.update_idem] at hs
        have heq : Function.update R 0 ((R 0 * R 1 ^ n) * R 1) =
            Function.update R 0 (R 0 * R 1 ^ (n + 1)) := by
          rw [mul_assoc, ← pow_succ]
        rwa [heq] at hs
      exact ih.trans hstep

lemma row_mul_invpow_reachable (R : Relators 2) (n : ℕ) :
    Reachable R (Function.update R 0 (R 0 * (R 1)⁻¹ ^ n)) := by
  classical
  set S : Relators 2 := Function.update R 1 (R 1)⁻¹ with hS
  have h1 : Reachable R S := Relation.ReflTransGen.single (Step.inv R 1)
  set T : Relators 2 := Function.update S 0 (S 0 * S 1 ^ n) with hT
  have h2 : Reachable S T := row_mul_pow_reachable S n
  have h3 : Reachable T (Function.update T 1 (T 1)⁻¹) :=
    Relation.ReflTransGen.single (Step.inv T 1)
  have hfin : Function.update T 1 (T 1)⁻¹ =
      Function.update R 0 (R 0 * (R 1)⁻¹ ^ n) := by
    funext i
    fin_cases i <;> simp [hT, hS]
  rw [hfin] at h3
  exact (h1.trans h2).trans h3

lemma row_mul_zpow_reachable (R : Relators 2) (k : ℤ) :
    Reachable R (Function.update R 0 (R 0 * R 1 ^ k)) := by
  obtain ⟨n, h | h⟩ := Int.eq_nat_or_neg k
  · subst h
    rw [zpow_natCast]
    exact row_mul_pow_reachable R n
  · subst h
    have hz : R 1 ^ (-(n : ℤ)) = (R 1)⁻¹ ^ n := by
      rw [zpow_neg, ← inv_zpow, zpow_natCast]
    rw [hz]
    exact row_mul_invpow_reachable R n

/-! ## 7. The row swap is reachable -/

lemma row_swap_reachable (R : Relators 2) :
    Reachable R (Function.update (Function.update R 0 (R 1)) 1 (R 0)) :=
  ProofAttempt.reachable_swap R (i := 0) (j := 1) (by decide)

/-! ## 8. Integer arithmetic of one Euclidean step -/

lemma natAbs_emod_lt (a c : ℤ) (hc : c ≠ 0) : Int.natAbs (a % c) < Int.natAbs c := by
  have h1 : a % c < (c.natAbs : ℤ) := by
    have := Int.emod_lt_abs a hc
    rwa [Int.abs_eq_natAbs] at this
  have h2 : 0 ≤ a % c := Int.emod_nonneg a hc
  have h3 : ((a % c).natAbs : ℤ) < (c.natAbs : ℤ) := by
    rw [Int.natAbs_of_nonneg h2]
    exact h1
  exact Int.ofNat_lt.mp h3

lemma emod_eq_add_mul (a c : ℤ) : a % c = a + (-(a / c)) * c := by
  have hkey : a % c + (a / c) * c = a := by
    rw [mul_comm]
    exact Int.emod_add_mul_ediv a c
  linarith

/-! ## 9. The Euclidean reduction -/

lemma isDiagonal_of_clear (M : Matrix (Fin 2) (Fin 2) ℤ) (hc : M 1 0 = 0)
    (ha : M 0 0 = 1 ∨ M 0 0 = -1) (hd : M 1 1 = 1 ∨ M 1 1 = -1) :
    IsDiagonalUnimodular (Function.update M 0 (M 0 + (-(M 0 1 * M 1 1)) • M 1)) := by
  have h00 : (Function.update M 0 (M 0 + (-(M 0 1 * M 1 1)) • M 1)) 0 0 = M 0 0 := by
    simp [Pi.add_apply, hc]
  have h01 : (Function.update M 0 (M 0 + (-(M 0 1 * M 1 1)) • M 1)) 0 1 = 0 := by
    rcases hd with hd | hd <;> simp [Pi.add_apply, hd]
  have h10 : (Function.update M 0 (M 0 + (-(M 0 1 * M 1 1)) • M 1)) 1 0 = 0 := by
    simp [hc]
  have h11 : (Function.update M 0 (M 0 + (-(M 0 1 * M 1 1)) • M 1)) 1 1 = M 1 1 := by
    simp
  exact ⟨by rw [h00]; exact ha, h01, h10, by rw [h11]; exact hd⟩

lemma reduce_base (R : Relators 2) (hc : expMatrix R 1 0 = 0)
    (hdet : Matrix.det (expMatrix R) = 1 ∨ Matrix.det (expMatrix R) = -1) :
    ∃ T : Relators 2, Reachable R T ∧ IsDiagonalUnimodular (expMatrix T) := by
  have hprod : expMatrix R 0 0 * expMatrix R 1 1 = 1 ∨
      expMatrix R 0 0 * expMatrix R 1 1 = -1 := by
    rcases hdet with h | h
    · left
      have hh := h
      rw [Matrix.det_fin_two] at hh
      simpa [hc] using hh
    · right
      have hh := h
      rw [Matrix.det_fin_two] at hh
      simpa [hc] using hh
  have ha : expMatrix R 0 0 = 1 ∨ expMatrix R 0 0 = -1 := by
    have hunit : IsUnit (expMatrix R 0 0) := by
      rcases hprod with h | h
      · exact IsUnit.of_mul_eq_one (expMatrix R 1 1) h
      · refine IsUnit.of_mul_eq_one (-(expMatrix R 1 1)) ?_
        rw [mul_neg, h]
        norm_num
    exact Int.isUnit_iff.mp hunit
  have hd : expMatrix R 1 1 = 1 ∨ expMatrix R 1 1 = -1 := by
    have hunit : IsUnit (expMatrix R 1 1) := by
      rcases hprod with h | h
      · refine IsUnit.of_mul_eq_one (expMatrix R 0 0) ?_
        rw [mul_comm]
        exact h
      · refine IsUnit.of_mul_eq_one (-(expMatrix R 0 0)) ?_
        nlinarith [h]
    exact Int.isUnit_iff.mp hunit
  refine ⟨Function.update R 0 (R 0 * R 1 ^ (-(expMatrix R 0 1 * expMatrix R 1 1))),
    row_mul_zpow_reachable R _, ?_⟩
  rw [expMatrix_update0_mul_zpow]
  exact isDiagonal_of_clear (expMatrix R) hc ha hd

lemma reduce_step (R : Relators 2) (hc : expMatrix R 1 0 ≠ 0)
    (hdet : Matrix.det (expMatrix R) = 1 ∨ Matrix.det (expMatrix R) = -1) :
    ∃ S : Relators 2, Reachable R S ∧
      Int.natAbs (expMatrix S 1 0) < Int.natAbs (expMatrix R 1 0) ∧
      (Matrix.det (expMatrix S) = 1 ∨ Matrix.det (expMatrix S) = -1) := by
  classical
  let q : ℤ := -(expMatrix R 0 0 / expMatrix R 1 0)
  set S1 : Relators 2 := Function.update R 0 (R 0 * R 1 ^ q) with hS1
  set S2 : Relators 2 := Function.update (Function.update S1 0 (S1 1)) 1 (S1 0) with hS2
  have hstep1 : Reachable R S1 := row_mul_zpow_reachable R q
  have hstep2 : Reachable S1 S2 := by
    rw [hS2]
    exact row_swap_reachable S1
  have hM1 : expMatrix S1 =
      Function.update (expMatrix R) 0 (expMatrix R 0 + q • expMatrix R 1) := by
    rw [hS1]
    exact expMatrix_update0_mul_zpow R q
  have hS2mat : expMatrix S2 = swapRows (expMatrix S1) := by
    rw [hS2]
    exact expMatrix_swap S1
  have h10 : expMatrix S2 1 0 = expMatrix R 0 0 % expMatrix R 1 0 := by
    rw [hS2mat, swapRows_one, hM1]
    simp only [update0_zero_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    show expMatrix R 0 0 + q * expMatrix R 1 0 = expMatrix R 0 0 % expMatrix R 1 0
    rw [show q = -(expMatrix R 0 0 / expMatrix R 1 0) from rfl]
    exact (emod_eq_add_mul (expMatrix R 0 0) (expMatrix R 1 0)).symm
  have hmeas : Int.natAbs (expMatrix S2 1 0) < Int.natAbs (expMatrix R 1 0) := by
    rw [h10]
    exact natAbs_emod_lt _ _ hc
  have hdet2 : Matrix.det (expMatrix S2) = 1 ∨ Matrix.det (expMatrix S2) = -1 := by
    rw [hS2mat, det_swapRows, hM1, det_update0_add]
    rcases hdet with h | h <;> rw [h] <;> norm_num
  exact ⟨S2, hstep1.trans hstep2, hmeas, hdet2⟩

theorem reduce_aux (m : ℕ) : ∀ R : Relators 2,
    Int.natAbs (expMatrix R 1 0) ≤ m →
    (Matrix.det (expMatrix R) = 1 ∨ Matrix.det (expMatrix R) = -1) →
    ∃ T : Relators 2, Reachable R T ∧ IsDiagonalUnimodular (expMatrix T) := by
  induction m with
  | zero =>
      intro R hm hdet
      have hc : expMatrix R 1 0 = 0 := by
        have h0 : Int.natAbs (expMatrix R 1 0) = 0 := Nat.le_zero.mp hm
        exact Int.natAbs_eq_zero.mp h0
      exact reduce_base R hc hdet
  | succ m ih =>
      intro R hm hdet
      by_cases hc : expMatrix R 1 0 = 0
      · exact reduce_base R hc hdet
      · obtain ⟨S, hRS, hmeas, hdetS⟩ := reduce_step R hc hdet
        have hle : Int.natAbs (expMatrix S 1 0) ≤ m := by omega
        obtain ⟨T, hST, hdiag⟩ := ih S hle hdetS
        exact ⟨T, hRS.trans hST, hdiag⟩

/-! ## 10. Diagonal entries give the abelian terminal predicate -/

lemma eq_genVec_zero_or_neg {v : Fin 2 → ℤ} (h0 : v 0 = 1 ∨ v 0 = -1) (h1 : v 1 = 0) :
    v = genVec (0 : Fin 2) ∨ v = -genVec (0 : Fin 2) := by
  rcases h0 with h0 | h0
  · left; funext j; fin_cases j <;> simp [genVec, h0, h1]
  · right; funext j; fin_cases j <;> simp [genVec, h0, h1]

lemma eq_genVec_one_or_neg {v : Fin 2 → ℤ} (h0 : v 0 = 0) (h1 : v 1 = 1 ∨ v 1 = -1) :
    v = genVec (1 : Fin 2) ∨ v = -genVec (1 : Fin 2) := by
  rcases h1 with h1 | h1
  · left; funext j; fin_cases j <;> simp [genVec, h0, h1]
  · right; funext j; fin_cases j <;> simp [genVec, h0, h1]

lemma isAbelianTerminal_of_diagonal {T : Relators 2}
    (h : IsDiagonalUnimodular (expMatrix T)) : IsAbelianTerminal T := by
  obtain ⟨h00, h01, h10, h11⟩ := h
  have h0 : expVec (T 0) = genVec (0 : Fin 2) ∨ expVec (T 0) = -genVec (0 : Fin 2) :=
    eq_genVec_zero_or_neg h00 h01
  have h1 : expVec (T 1) = genVec (1 : Fin 2) ∨ expVec (T 1) = -genVec (1 : Fin 2) :=
    eq_genVec_one_or_neg h10 h11
  refine ⟨id, Function.bijective_id,
    fun i => if expVec (T i) = genVec i then true else false, ?_⟩
  intro i
  fin_cases i
  · by_cases hh : expVec (T 0) = genVec (0 : Fin 2)
    · simp [hh]
    · have hh' : expVec (T 0) = -genVec (0 : Fin 2) := h0.resolve_left hh
      simp [hh']
  · by_cases hh : expVec (T 1) = genVec (1 : Fin 2)
    · simp [hh]
    · have hh' : expVec (T 1) = -genVec (1 : Fin 2) := h1.resolve_left hh
      simp [hh']

/-! ## 11. The main theorem -/

/-- Every rank-two relator tuple whose exponent span is the whole lattice reaches an
abelian-terminal state. -/
theorem abelianTerminal_reachable_of_expSpan_top (R : Relators 2)
    (h : expSpan R = ⊤) :
    ∃ S : Relators 2, IsAbelianTerminal S ∧ Reachable R S := by
  have hdet : Matrix.det (expMatrix R) = 1 ∨ Matrix.det (expMatrix R) = -1 := by
    rcases expDeterminant_eq_pm_one_of_span_top (R := R) h with hh | hh
    · left
      rwa [expDeterminant_eq_matrix_det] at hh
    · right
      rwa [expDeterminant_eq_matrix_det] at hh
  obtain ⟨T, hRT, hdiag⟩ := reduce_aux (Int.natAbs (expMatrix R 1 0)) R le_rfl hdet
  exact ⟨T, isAbelianTerminal_of_diagonal hdiag, hRT⟩

end Euclid
end AC
