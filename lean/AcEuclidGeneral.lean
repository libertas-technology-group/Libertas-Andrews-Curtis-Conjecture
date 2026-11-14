import AC
import AcInvariant
import AcProof
import AcInduction
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Int.Order.Units
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# General-rank A7: abelian-terminal reachability from a top exponent span

The rank-two reduction in `AcEuclid` operates on a `2 x 2` integer matrix. This
module carries the same reduction at every positive rank.

The exponent vectors of a rank-`n` relator tuple form an `n x n` integer matrix.
An official `Step.mulRight` adds one row to another at exponent level, `Step.inv`
negates a row, and `ProofAttempt.reachable_swap` exchanges two rows. The row span
of the matrix is the exponent span, and every row operation preserves it.

The main result is `abelianTerminal_reachable_of_expSpan_top_general`: a relator
tuple whose exponent span is the whole lattice reaches a state whose exponent
matrix is a signed permutation matrix. The proof reduces the first column by the
Euclidean algorithm, removes the pivot row and column, applies the induction
hypothesis to the remaining block, and clears the pivot row with the signed
permutation rows that remain.
-/

set_option autoImplicit false

namespace AC
namespace EuclidGeneral

open Invariant

variable {n m k : ℕ}

/-! ## 1. Row operations on integer matrices -/

/-- Row addition: row `i` becomes `row i + c * row j`. -/
def rowAdd (M : Matrix (Fin m) (Fin k) ℤ) (i j : Fin m) (c : ℤ) :
    Matrix (Fin m) (Fin k) ℤ :=
  Function.update M i (M i + c • M j)

/-- Row negation. -/
def rowNeg (M : Matrix (Fin m) (Fin k) ℤ) (i : Fin m) : Matrix (Fin m) (Fin k) ℤ :=
  Function.update M i (-(M i))

/-- Row exchange: rows `i` and `j` trade places. -/
def rowSwap (M : Matrix (Fin m) (Fin k) ℤ) (i j : Fin m) : Matrix (Fin m) (Fin k) ℤ :=
  Function.update (Function.update M i (M j)) j (M i)

@[simp] lemma rowAdd_self (M : Matrix (Fin m) (Fin k) ℤ) (i j : Fin m) (c : ℤ) :
    rowAdd M i j c i = M i + c • M j := by
  simp [rowAdd]

lemma rowAdd_of_ne (M : Matrix (Fin m) (Fin k) ℤ) (i j r : Fin m) (hr : r ≠ i) (c : ℤ) :
    rowAdd M i j c r = M r := by
  simp [rowAdd, hr]

@[simp] lemma rowNeg_self (M : Matrix (Fin m) (Fin k) ℤ) (i : Fin m) :
    rowNeg M i i = -(M i) := by
  simp [rowNeg]

lemma rowNeg_of_ne (M : Matrix (Fin m) (Fin k) ℤ) (i r : Fin m) (hr : r ≠ i) :
    rowNeg M i r = M r := by
  simp [rowNeg, hr]

lemma rowSwap_left (M : Matrix (Fin m) (Fin k) ℤ) (i j : Fin m) (hij : i ≠ j) :
    rowSwap M i j i = M j := by
  simp [rowSwap, hij]

@[simp] lemma rowSwap_right (M : Matrix (Fin m) (Fin k) ℤ) (i j : Fin m) :
    rowSwap M i j j = M i := by
  simp [rowSwap]

lemma rowSwap_of_ne (M : Matrix (Fin m) (Fin k) ℤ) (i j r : Fin m)
    (hri : r ≠ i) (hrj : r ≠ j) :
    rowSwap M i j r = M r := by
  simp [rowSwap, hri, hrj]

/-! ## 2. The row-step relation and the row span -/

/-- One elementary row operation over the integers. -/
inductive RowStep : Matrix (Fin m) (Fin k) ℤ → Matrix (Fin m) (Fin k) ℤ → Prop
  | add (M : Matrix (Fin m) (Fin k) ℤ) (i j : Fin m) (hij : i ≠ j) (c : ℤ) :
      RowStep M (rowAdd M i j c)
  | neg (M : Matrix (Fin m) (Fin k) ℤ) (i : Fin m) : RowStep M (rowNeg M i)
  | swap (M : Matrix (Fin m) (Fin k) ℤ) (i j : Fin m) (hij : i ≠ j) :
      RowStep M (rowSwap M i j)

/-- A finite sequence of elementary row operations. -/
def RowReach : Matrix (Fin m) (Fin k) ℤ → Matrix (Fin m) (Fin k) ℤ → Prop :=
  Relation.ReflTransGen RowStep

/-- The `ℤ`-span of the rows of a matrix. -/
noncomputable def rowSpan (M : Matrix (Fin m) (Fin k) ℤ) : Submodule ℤ (Fin k → ℤ) :=
  Submodule.span ℤ (Set.range M)

lemma mem_rowSpan_row (M : Matrix (Fin m) (Fin k) ℤ) (i : Fin m) :
    M i ∈ rowSpan M :=
  Submodule.subset_span ⟨i, rfl⟩

lemma rowSpan_rowAdd (M : Matrix (Fin m) (Fin k) ℤ) (i j : Fin m) (hij : i ≠ j) (c : ℤ) :
    rowSpan (rowAdd M i j c) = rowSpan M := by
  apply le_antisymm
  · rw [rowSpan, Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    by_cases hr : r = i
    · rw [hr, rowAdd_self]
      exact Submodule.add_mem _ (mem_rowSpan_row M i) (Submodule.smul_mem _ c (mem_rowSpan_row M j))
    · rw [rowAdd_of_ne M i j r hr]
      exact mem_rowSpan_row M r
  · rw [rowSpan, Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    by_cases hr : r = i
    · rw [hr]
      have h1 : rowAdd M i j c i = M i + c • M j := rowAdd_self M i j c
      have h2 : rowAdd M i j c j = M j := rowAdd_of_ne M i j j (Ne.symm hij) c
      have hsplit : M i = rowAdd M i j c i - c • rowAdd M i j c j := by
        rw [h1, h2]
        simp
      rw [hsplit]
      exact Submodule.sub_mem _ (mem_rowSpan_row (rowAdd M i j c) i)
        (Submodule.smul_mem _ c (mem_rowSpan_row (rowAdd M i j c) j))
    · rw [← rowAdd_of_ne M i j r hr]
      exact mem_rowSpan_row (rowAdd M i j c) r

lemma rowSpan_rowNeg (M : Matrix (Fin m) (Fin k) ℤ) (i : Fin m) :
    rowSpan (rowNeg M i) = rowSpan M := by
  apply le_antisymm
  · rw [rowSpan, Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    by_cases hr : r = i
    · rw [hr, rowNeg_self]
      exact Submodule.neg_mem _ (mem_rowSpan_row M i)
    · rw [rowNeg_of_ne M i r hr]
      exact mem_rowSpan_row M r
  · rw [rowSpan, Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    by_cases hr : r = i
    · rw [hr]
      have hsplit : M i = -rowNeg M i i := by
        rw [rowNeg_self]
        simp
      rw [hsplit]
      exact Submodule.neg_mem _ (mem_rowSpan_row (rowNeg M i) i)
    · rw [← rowNeg_of_ne M i r hr]
      exact mem_rowSpan_row (rowNeg M i) r

lemma rowSpan_rowSwap (M : Matrix (Fin m) (Fin k) ℤ) (i j : Fin m) (hij : i ≠ j) :
    rowSpan (rowSwap M i j) = rowSpan M := by
  apply le_antisymm
  · rw [rowSpan, Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    by_cases hri : r = i
    · rw [hri, rowSwap_left M i j hij]
      exact mem_rowSpan_row M j
    · by_cases hrj : r = j
      · rw [hrj, rowSwap_right]
        exact mem_rowSpan_row M i
      · rw [rowSwap_of_ne M i j r hri hrj]
        exact mem_rowSpan_row M r
  · rw [rowSpan, Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    by_cases hri : r = i
    · rw [hri]
      have hsplit : M i = rowSwap M i j j := by rw [rowSwap_right]
      rw [hsplit]
      exact mem_rowSpan_row (rowSwap M i j) j
    · by_cases hrj : r = j
      · rw [hrj]
        have hsplit : M j = rowSwap M i j i := by rw [rowSwap_left M i j hij]
        rw [hsplit]
        exact mem_rowSpan_row (rowSwap M i j) i
      · rw [← rowSwap_of_ne M i j r hri hrj]
        exact mem_rowSpan_row (rowSwap M i j) r

lemma rowSpan_rowStep {M N : Matrix (Fin m) (Fin k) ℤ} (h : RowStep M N) :
    rowSpan N = rowSpan M := by
  cases h with
  | add i j hij c => exact rowSpan_rowAdd M i j hij c
  | neg i => exact rowSpan_rowNeg M i
  | swap i j hij => exact rowSpan_rowSwap M i j hij

lemma rowSpan_rowReach {M N : Matrix (Fin m) (Fin k) ℤ} (h : RowReach M N) :
    rowSpan N = rowSpan M := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact (rowSpan_rowStep hstep).trans ih

/-! ## 3. The exponent matrix of a relator tuple -/

/-- The exponent matrix: row `i` is the exponent vector of relator `i`. -/
noncomputable def expMatrix (R : Relators n) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => expVec (R i) j

/-- The exponent span is the row span of the exponent matrix. -/
lemma expSpan_eq_rowSpan (R : Relators n) : expSpan R = rowSpan (expMatrix R) := rfl

lemma expVec_zpow_general (w : Word n) (z : ℤ) : expVec (w ^ z) = z • expVec w := by
  simp [expVec, map_zpow]

lemma expMatrix_update (R : Relators n) (i : Fin n) (w : Word n) :
    expMatrix (Function.update R i w) = Function.update (expMatrix R) i (expVec w) := by
  funext r s
  by_cases hr : r = i
  · rw [hr]
    simp [expMatrix]
  · simp [expMatrix, hr]

lemma expMatrix_rowAdd (R : Relators n) (i j : Fin n) (c : ℤ) :
    expMatrix (Function.update R i (R i * R j ^ c)) = rowAdd (expMatrix R) i j c := by
  funext r s
  by_cases hr : r = i
  · rw [hr]
    simp [expMatrix, rowAdd, expVec_mul, expVec_zpow_general, Pi.add_apply]
  · simp [expMatrix, rowAdd, hr]

lemma expMatrix_rowNeg (R : Relators n) (i : Fin n) :
    expMatrix (Function.update R i (R i)⁻¹) = rowNeg (expMatrix R) i := by
  funext r s
  by_cases hr : r = i
  · rw [hr]
    simp [expMatrix, rowNeg, expVec_inv]
  · simp [expMatrix, rowNeg, hr]

lemma expMatrix_rowSwap (R : Relators n) (i j : Fin n) :
    expMatrix (Function.update (Function.update R i (R j)) j (R i)) =
      rowSwap (expMatrix R) i j := by
  funext r s
  by_cases hri : r = i
  · rw [hri]
    by_cases hij : i = j
    · rw [hij]
      simp [expMatrix, rowSwap]
    · simp [expMatrix, rowSwap, Function.update_of_ne hij]
  · by_cases hrj : r = j
    · rw [hrj]
      simp [expMatrix, rowSwap]
    · simp [expMatrix, rowSwap, hri, hrj]

/-! ## 4. Row addition with an integer multiplier is reachable -/

lemma row_mul_pow_reachable_general (R : Relators n) (i j : Fin n) (hij : i ≠ j) (p : ℕ) :
    Reachable R (Function.update R i (R i * R j ^ p)) := by
  induction p with
  | zero => simpa using (Relation.ReflTransGen.refl : Reachable R R)
  | succ p ih =>
      have hstep : Reachable (Function.update R i (R i * R j ^ p))
          (Function.update R i (R i * R j ^ (p + 1))) := by
        refine Relation.ReflTransGen.single ?_
        have hs := Step.mulRight (Function.update R i (R i * R j ^ p)) i j hij
        have e1 : (Function.update R i (R i * R j ^ p)) i = R i * R j ^ p := by simp
        have e2 : (Function.update R i (R i * R j ^ p)) j = R j := by
          simp [Function.update_of_ne (Ne.symm hij)]
        rw [e1, e2] at hs
        rw [Function.update_idem] at hs
        have heq : Function.update R i ((R i * R j ^ p) * R j) =
            Function.update R i (R i * R j ^ (p + 1)) := by
          rw [mul_assoc, ← pow_succ]
        rwa [heq] at hs
      exact ih.trans hstep

lemma row_mul_invpow_reachable_general (R : Relators n) (i j : Fin n) (hij : i ≠ j)
    (p : ℕ) :
    Reachable R (Function.update R i (R i * (R j)⁻¹ ^ p)) := by
  classical
  set S : Relators n := Function.update R j (R j)⁻¹ with hS
  have h1 : Reachable R S := Relation.ReflTransGen.single (Step.inv R j)
  set T : Relators n := Function.update S i (S i * S j ^ p) with hT
  have h2 : Reachable S T := row_mul_pow_reachable_general S i j hij p
  have h3 : Reachable T (Function.update T j (T j)⁻¹) :=
    Relation.ReflTransGen.single (Step.inv T j)
  have hfin : Function.update T j (T j)⁻¹ =
      Function.update R i (R i * (R j)⁻¹ ^ p) := by
    funext r
    by_cases hri : r = i
    · rw [hri]
      simp [hT, hS, Function.update_of_ne hij]
    · by_cases hrj : r = j
      · rw [hrj]
        simp [hT, hS, Ne.symm hij]
      · simp [hT, hS, hri, hrj]
  rw [hfin] at h3
  exact (h1.trans h2).trans h3

lemma row_mul_zpow_reachable_general (R : Relators n) (i j : Fin n) (hij : i ≠ j) (z : ℤ) :
    Reachable R (Function.update R i (R i * R j ^ z)) := by
  obtain ⟨p, h | h⟩ := Int.eq_nat_or_neg z
  · subst h
    rw [zpow_natCast]
    exact row_mul_pow_reachable_general R i j hij p
  · subst h
    have hz : R j ^ (-(p : ℤ)) = (R j)⁻¹ ^ p := by
      rw [zpow_neg, ← inv_zpow, zpow_natCast]
    rw [hz]
    exact row_mul_invpow_reachable_general R i j hij p

/-! ## 5. Every row step lifts to relators -/

lemma rowStep_reachable {M N : Matrix (Fin n) (Fin n) ℤ} (h : RowStep M N) :
    ∀ R : Relators n, expMatrix R = M → ∃ S : Relators n, expMatrix S = N ∧ Reachable R S := by
  intro R hR
  cases h with
  | add i j hij c =>
      refine ⟨Function.update R i (R i * R j ^ c), ?_,
        row_mul_zpow_reachable_general R i j hij c⟩
      rw [expMatrix_rowAdd, hR]
  | neg i =>
      refine ⟨Function.update R i (R i)⁻¹, ?_, Relation.ReflTransGen.single (Step.inv R i)⟩
      rw [expMatrix_rowNeg, hR]
  | swap i j hij =>
      refine ⟨Function.update (Function.update R i (R j)) j (R i), ?_,
        ProofAttempt.reachable_swap R hij⟩
      rw [expMatrix_rowSwap, hR]

lemma rowReach_reachable {M N : Matrix (Fin n) (Fin n) ℤ} (h : RowReach M N) :
    ∀ R : Relators n, expMatrix R = M → ∃ S : Relators n, expMatrix S = N ∧ Reachable R S := by
  induction h with
  | refl =>
      intro R hR
      exact ⟨R, hR, Relation.ReflTransGen.refl⟩
  | tail _ hstep ih =>
      intro R hR
      obtain ⟨S, hS, hRS⟩ := ih R hR
      obtain ⟨T, hT, hST⟩ := rowStep_reachable hstep S hS
      exact ⟨T, hT, hRS.trans hST⟩

/-! ## 6. Clearing the first column by the Euclidean algorithm -/

/-- Two distinguished rows can be reduced so that the second entry of the first column
vanishes. The reduction touches only those two rows. -/
theorem pair_aux (m k d : ℕ) :
    ∀ (M : Matrix (Fin m) (Fin (k + 1)) ℤ) (i j : Fin m), i ≠ j →
      Int.natAbs (M j 0) ≤ d →
      ∃ M' : Matrix (Fin m) (Fin (k + 1)) ℤ, RowReach M M' ∧ M' j 0 = 0 ∧
        (∀ r, r ≠ i → r ≠ j → M' r = M r) := by
  induction d with
  | zero =>
      intro M i j hij hle
      have hj0 : M j 0 = 0 := Int.natAbs_eq_zero.mp (Nat.le_zero.mp hle)
      exact ⟨M, Relation.ReflTransGen.refl, hj0, fun r _ _ => rfl⟩
  | succ d ih =>
      intro M i j hij hle
      by_cases hj0 : M j 0 = 0
      · exact ⟨M, Relation.ReflTransGen.refl, hj0, fun r _ _ => rfl⟩
      by_cases hi0 : M i 0 = 0
      · refine ⟨rowSwap M i j, Relation.ReflTransGen.single (RowStep.swap M i j hij), ?_, ?_⟩
        · rw [rowSwap_right, hi0]
        · intro r hri hrj
          exact rowSwap_of_ne M i j r hri hrj
      · let c : ℤ := -(M i 0 / M j 0)
        let M1 : Matrix (Fin m) (Fin (k + 1)) ℤ := rowAdd M i j c
        let M2 : Matrix (Fin m) (Fin (k + 1)) ℤ := rowSwap M1 i j
        have hreach : RowReach M M2 :=
          (Relation.ReflTransGen.single (RowStep.add M i j hij c)).trans
            (Relation.ReflTransGen.single (RowStep.swap M1 i j hij))
        have hjval : M2 j 0 = M i 0 % M j 0 := by
          have h2 : M2 j = M1 i := by simp [M2, rowSwap]
          have h1 : M1 i = M i + c • M j := rowAdd_self M i j c
          rw [h2, h1]
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          show M i 0 + c * M j 0 = M i 0 % M j 0
          rw [show c = -(M i 0 / M j 0) from rfl]
          exact (AC.Euclid.emod_eq_add_mul (M i 0) (M j 0)).symm
        have hlt : Int.natAbs (M2 j 0) < Int.natAbs (M j 0) := by
          rw [hjval]
          exact AC.Euclid.natAbs_emod_lt _ _ hj0
        have hle' : Int.natAbs (M2 j 0) ≤ d := by omega
        obtain ⟨M', hreach', hj', hother'⟩ := ih M2 i j hij hle'
        refine ⟨M', hreach.trans hreach', hj', ?_⟩
        intro r hri hrj
        rw [hother' r hri hrj]
        dsimp only [M2, M1]
        rw [rowSwap_of_ne (rowAdd M i j c) i j r hri hrj, rowAdd_of_ne M i j r hri c]

/-- The number of nonzero entries of the first column outside row `0`. -/
def tailNZ (n k : ℕ) (M : Matrix (Fin (n + 1)) (Fin (k + 1)) ℤ) : ℕ :=
  (Finset.univ.filter (fun i : Fin (n + 1) => i ≠ 0 ∧ M i 0 ≠ 0)).card

lemma tailNZ_erase {n k : ℕ} {M M' : Matrix (Fin (n + 1)) (Fin (k + 1)) ℤ}
    {j : Fin (n + 1)} (hj0 : j ≠ 0) (hjval : M j 0 ≠ 0) (hjzero : M' j 0 = 0)
    (hother : ∀ r, r ≠ 0 → r ≠ j → M' r = M r) :
    tailNZ n k M' = tailNZ n k M - 1 := by
  classical
  have hfilter :
      (Finset.univ.filter (fun i : Fin (n + 1) => i ≠ 0 ∧ M' i 0 ≠ 0)) =
        (Finset.univ.filter (fun i : Fin (n + 1) => i ≠ 0 ∧ M i 0 ≠ 0)).erase j := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · rintro ⟨hi0, hiv⟩
      by_cases hij : i = j
      · rw [hij, hjzero] at hiv
        exact absurd rfl hiv
      · exact ⟨hij, hi0, by rw [← hother i hi0 hij]; exact hiv⟩
    · rintro ⟨hij, hi0, hiv⟩
      exact ⟨hi0, by rw [hother i hi0 hij]; exact hiv⟩
  rw [tailNZ, hfilter, Finset.card_erase_of_mem]
  · rfl
  · simp [hj0, hjval]

/-- Every matrix reaches a matrix whose first column has one nonzero entry. -/
theorem exists_rowReach_colFirst (n k : ℕ) (M : Matrix (Fin (n + 1)) (Fin (k + 1)) ℤ) :
    ∃ (M' : Matrix (Fin (n + 1)) (Fin (k + 1)) ℤ) (d : ℤ),
      RowReach M M' ∧ M' 0 0 = d ∧ ∀ i : Fin (n + 1), i ≠ 0 → M' i 0 = 0 := by
  classical
  let P : ℕ → Prop := fun c => ∀ M : Matrix (Fin (n + 1)) (Fin (k + 1)) ℤ,
      tailNZ n k M = c → ∃ (M' : Matrix (Fin (n + 1)) (Fin (k + 1)) ℤ) (d : ℤ),
        RowReach M M' ∧ M' 0 0 = d ∧ ∀ i, i ≠ 0 → M' i 0 = 0
  have hP : ∀ c, P c := by
    intro c
    induction c using Nat.strong_induction_on with
    | _ c ih =>
      intro M hM
      by_cases hc : c = 0
      · subst hc
        refine ⟨M, M 0 0, Relation.ReflTransGen.refl, rfl, ?_⟩
        intro i hi
        by_contra hne
        have hmem : i ∈ Finset.univ.filter (fun i : Fin (n + 1) => i ≠ 0 ∧ M i 0 ≠ 0) := by
          simp [hi, hne]
        have hpos : 0 < tailNZ n k M := by
          simp only [tailNZ]
          exact Finset.card_pos.mpr ⟨i, hmem⟩
        rw [hM] at hpos
        omega
      · have hcpos : 0 < tailNZ n k M := by
          rw [hM]
          omega
        have hnonempty :
            (Finset.univ.filter (fun i : Fin (n + 1) => i ≠ 0 ∧ M i 0 ≠ 0)).Nonempty := by
          rw [← Finset.card_pos]
          simpa only [tailNZ] using hcpos
        obtain ⟨j, hjmem⟩ := hnonempty
        have hj0 : j ≠ 0 := (Finset.mem_filter.mp hjmem).2.1
        have hjval : M j 0 ≠ 0 := (Finset.mem_filter.mp hjmem).2.2
        by_cases h00 : M 0 0 = 0
        · have hother : ∀ r : Fin (n + 1), r ≠ 0 → r ≠ j → rowSwap M 0 j r = M r :=
            fun r hr0 hrj => rowSwap_of_ne M 0 j r hr0 hrj
          have hjzero : rowSwap M 0 j j 0 = 0 := by
            rw [rowSwap_right, h00]
          have htail : tailNZ n k (rowSwap M 0 j) = c - 1 := by
            rw [tailNZ_erase hj0 hjval hjzero hother, hM]
          obtain ⟨M', d, hreach, hd, hclear⟩ := ih (c - 1) (by omega) (rowSwap M 0 j) htail
          exact ⟨M', d,
            (Relation.ReflTransGen.single (RowStep.swap M 0 j (Ne.symm hj0))).trans hreach,
            hd, hclear⟩
        · obtain ⟨M1, hreach1, hjzero, hother⟩ :=
            pair_aux (n + 1) k (Int.natAbs (M j 0)) M 0 j (Ne.symm hj0) le_rfl
          have htail : tailNZ n k M1 = c - 1 := by
            rw [tailNZ_erase hj0 hjval hjzero hother, hM]
          obtain ⟨M', d, hreach, hd, hclear⟩ := ih (c - 1) (by omega) M1 htail
          exact ⟨M', d, hreach1.trans hreach, hd, hclear⟩
  exact hP (tailNZ n k M) M rfl

/-! ## 7. The cleared pivot is a unit -/

lemma isUnit_of_colFirst {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) (d : ℤ)
    (h00 : M 0 0 = d) (hzero : ∀ i : Fin (n + 1), i ≠ 0 → M i 0 = 0)
    (hspan : rowSpan M = ⊤) : d = 1 ∨ d = -1 := by
  classical
  let proj0 : (Fin (n + 1) → ℤ) →ₗ[ℤ] ℤ := LinearMap.proj (0 : Fin (n + 1))
  have himage : Submodule.span ℤ (proj0 '' Set.range M) =
      Submodule.span ℤ ({d} : Set ℤ) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro x ⟨v, ⟨i, rfl⟩, rfl⟩
      by_cases hi : i = 0
      · rw [hi]
        simp only [proj0, LinearMap.proj_apply]
        rw [h00]
        exact Submodule.subset_span (by simp)
      · simp only [proj0, LinearMap.proj_apply]
        rw [hzero i hi]
        exact Submodule.zero_mem _
    · rw [Submodule.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Submodule.subset_span ⟨M 0, ⟨0, rfl⟩, by
        simp only [proj0, LinearMap.proj_apply]
        exact h00⟩
  have hspan_top : Submodule.span ℤ ({d} : Set ℤ) = ⊤ := by
    rw [← himage]
    have hmap : Submodule.map proj0 (rowSpan M) =
        Submodule.span ℤ (proj0 '' Set.range M) := by
      rw [rowSpan, Submodule.map_span]
    rw [← hmap, hspan, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (LinearMap.proj_surjective 0)
  have hmem : (1 : ℤ) ∈ Submodule.span ℤ ({d} : Set ℤ) := by
    rw [hspan_top]
    exact Submodule.mem_top
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
  have hunit : IsUnit d := IsUnit.of_mul_eq_one a (by
    rw [mul_comm]
    simpa [smul_eq_mul] using ha)
  exact Int.isUnit_iff.mp hunit

/-! ## 8. The remaining block spans the whole lattice -/

lemma rowSpan_submatrix_succ {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) (d : ℤ)
    (h00 : M 0 0 = d) (hzero : ∀ i : Fin (n + 1), i ≠ 0 → M i 0 = 0) (hd : d ≠ 0)
    (hspan : rowSpan M = ⊤) :
    rowSpan (fun (i j : Fin n) => M i.succ j.succ) = ⊤ := by
  classical
  apply eq_top_iff.mpr
  intro w _
  have hmem : (Fin.cons (0 : ℤ) w : Fin (n + 1) → ℤ) ∈ rowSpan M := by
    rw [hspan]
    exact Submodule.mem_top
  rw [rowSpan, Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hcoord0 : c 0 * d = 0 := by
    have h := congrFun hc 0
    simpa [Fin.sum_univ_succ, h00, hzero, Pi.smul_apply, Finset.sum_apply, smul_eq_mul] using h
  have hc0 : c 0 = 0 := by
    rcases mul_eq_zero.mp hcoord0 with h | h
    · exact h
    · exact absurd h hd
  rw [rowSpan]
  refine (Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨fun i : Fin n => c i.succ, ?_⟩
  funext j
  have h := congrFun hc j.succ
  simpa [Fin.sum_univ_succ, hc0, Pi.smul_apply, Finset.sum_apply, smul_eq_mul] using h

/-! ## 9. Lifting a row path on the block to the whole matrix -/

/-- Build a matrix from a first row `r` and a block `N`: the remaining rows carry a zero
in the first column followed by the corresponding row of `N`. -/
def liftMat {n : ℕ} (r : Fin (n + 1) → ℤ) (N : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Fin.cons r (fun i => Fin.cons 0 (N i))

@[simp] lemma liftMat_zero_row (r : Fin (n + 1) → ℤ) (N : Matrix (Fin n) (Fin n) ℤ) :
    liftMat r N 0 = r := by
  simp [liftMat]

@[simp] lemma liftMat_succ_row (r : Fin (n + 1) → ℤ) (N : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    liftMat r N i.succ = Fin.cons 0 (N i) := by
  simp [liftMat]

@[simp] lemma liftMat_succ_zero (r : Fin (n + 1) → ℤ) (N : Matrix (Fin n) (Fin n) ℤ)
    (i : Fin n) : liftMat r N i.succ 0 = 0 := by
  simp [liftMat]

@[simp] lemma liftMat_succ_succ (r : Fin (n + 1) → ℤ) (N : Matrix (Fin n) (Fin n) ℤ)
    (i j : Fin n) : liftMat r N i.succ j.succ = N i j := by
  simp [liftMat]

lemma liftMat_update (r : Fin (n + 1) → ℤ) (N : Matrix (Fin n) (Fin n) ℤ)
    (i : Fin n) (v : Fin n → ℤ) :
    liftMat r (Function.update N i v) =
      Function.update (liftMat r N) i.succ (Fin.cons 0 v) := by
  funext a b
  by_cases ha : a = 0
  · rw [ha]
    simp [liftMat, Function.update_of_ne (Ne.symm (Fin.succ_ne_zero i))]
  · obtain ⟨a', rfl⟩ := Fin.eq_succ_of_ne_zero ha
    by_cases hb : b = 0
    · rw [hb]
      by_cases hai : a' = i
      · rw [hai]
        simp [liftMat]
      · simp [liftMat, hai, Fin.succ_inj]
    · obtain ⟨b', rfl⟩ := Fin.eq_succ_of_ne_zero hb
      by_cases hai : a' = i
      · rw [hai]
        simp [liftMat]
      · simp [liftMat, hai, Fin.succ_inj]

lemma finCons_zero_add_smul {n : ℕ} (u v : Fin n → ℤ) (c : ℤ) :
    (Fin.cons 0 (u + c • v) : Fin (n + 1) → ℤ) =
      (Fin.cons 0 u : Fin (n + 1) → ℤ) + c • (Fin.cons 0 v : Fin (n + 1) → ℤ) := by
  funext b
  by_cases hb : b = 0
  · rw [hb]
    simp
  · obtain ⟨b', rfl⟩ := Fin.eq_succ_of_ne_zero hb
    simp [Pi.add_apply]

lemma finCons_zero_neg {n : ℕ} (u : Fin n → ℤ) :
    (Fin.cons 0 (-u) : Fin (n + 1) → ℤ) = -(Fin.cons 0 u : Fin (n + 1) → ℤ) := by
  funext b
  by_cases hb : b = 0
  · rw [hb]
    simp
  · obtain ⟨b', rfl⟩ := Fin.eq_succ_of_ne_zero hb
    simp [Pi.neg_apply]

lemma liftMat_rowAdd (r : Fin (n + 1) → ℤ) (N : Matrix (Fin n) (Fin n) ℤ)
    (i j : Fin n) (c : ℤ) :
    liftMat r (rowAdd N i j c) = rowAdd (liftMat r N) i.succ j.succ c := by
  rw [rowAdd, rowAdd, liftMat_update]
  congr 1
  rw [liftMat_succ_row, liftMat_succ_row]
  exact finCons_zero_add_smul (N i) (N j) c

lemma liftMat_rowNeg (r : Fin (n + 1) → ℤ) (N : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    liftMat r (rowNeg N i) = rowNeg (liftMat r N) i.succ := by
  rw [rowNeg, rowNeg, liftMat_update]
  congr 1
  rw [liftMat_succ_row]
  exact finCons_zero_neg (N i)

lemma liftMat_rowSwap (r : Fin (n + 1) → ℤ) (N : Matrix (Fin n) (Fin n) ℤ)
    (i j : Fin n) :
    liftMat r (rowSwap N i j) = rowSwap (liftMat r N) i.succ j.succ := by
  rw [rowSwap, rowSwap, liftMat_update, liftMat_update]
  rfl

lemma liftMat_rowStep {N N' : Matrix (Fin n) (Fin n) ℤ} (h : RowStep N N')
    (r : Fin (n + 1) → ℤ) : RowStep (liftMat r N) (liftMat r N') := by
  cases h with
  | add i j hij c =>
      rw [liftMat_rowAdd]
      exact RowStep.add (liftMat r N) i.succ j.succ (fun hh => hij (Fin.succ_inj.mp hh)) c
  | neg i =>
      rw [liftMat_rowNeg]
      exact RowStep.neg (liftMat r N) i.succ
  | swap i j hij =>
      rw [liftMat_rowSwap]
      exact RowStep.swap (liftMat r N) i.succ j.succ (fun hh => hij (Fin.succ_inj.mp hh))

lemma liftMat_rowReach {N N' : Matrix (Fin n) (Fin n) ℤ} (h : RowReach N N')
    (r : Fin (n + 1) → ℤ) : RowReach (liftMat r N) (liftMat r N') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact ih.trans (Relation.ReflTransGen.single (liftMat_rowStep hstep r))

/-! ## 10. Clearing the pivot row with the signed permutation rows -/

lemma finCons_smul_genVec_zero {n : ℕ} (d : ℤ) :
    (Fin.cons d (0 : Fin n → ℤ) : Fin (n + 1) → ℤ) = d • genVec (0 : Fin (n + 1)) := by
  funext j
  by_cases hj : j = 0
  · rw [hj]
    simp [genVec, Pi.single]
  · obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hj
    simp [genVec, Pi.single, Fin.succ_ne_zero]

lemma finCons_smul_genVec_succ {n : ℕ} (s : ℤ) (i : Fin n) :
    (Fin.cons 0 (s • genVec i) : Fin (n + 1) → ℤ) = s • genVec i.succ := by
  funext j
  by_cases hj : j = 0
  · rw [hj]
    simp only [Fin.cons_zero, Pi.smul_apply]
    have h : genVec i.succ (0 : Fin (n + 1)) = 0 := by
      simp [genVec, Pi.single, Ne.symm (Fin.succ_ne_zero i)]
    rw [h]
    simp
  · obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hj
    simp only [Fin.cons_succ, Pi.smul_apply]
    by_cases hki : k = i
    · rw [hki]
      simp [genVec, Pi.single]
    · have h1 : genVec i k = 0 := by
        simp [genVec, Pi.single, hki]
      have h2 : genVec i.succ k.succ = 0 := by
        simp [genVec, Pi.single, Fin.succ_inj, hki]
      rw [h1, h2]

/-- The pivot row can be cleared against the signed permutation rows of the block. -/
theorem exists_rowReach_liftMat_clear {n : ℕ} (q : Fin (n + 1) → ℤ) (d : ℤ) (hq0 : q 0 = d)
    (N : Matrix (Fin n) (Fin n) ℤ) (σ : Fin n → Fin n) (hσ : Function.Bijective σ)
    (sgn : Fin n → ℤ) (hsgn : ∀ i, sgn i = 1 ∨ sgn i = -1)
    (hN : ∀ i j, N i j = if j = σ i then sgn i else 0) :
    RowReach (liftMat q N) (liftMat (Fin.cons d 0) N) := by
  classical
  have hmain : ∀ s : Finset (Fin n), ∀ q : Fin (n + 1) → ℤ,
      ∃ q' : Fin (n + 1) → ℤ,
        RowReach (liftMat q N) (liftMat q' N) ∧ q' 0 = q 0 ∧
        (∀ i ∈ s, q' (σ i).succ = 0) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro q
        exact ⟨q, Relation.ReflTransGen.refl, rfl, by simp⟩
    | insert a s ha ih =>
        intro q
        obtain ⟨q1, hreach1, hq1_0, hq1_s⟩ := ih q
        let c : ℤ := -(q1 (σ a).succ * sgn a)
        let q2 : Fin (n + 1) → ℤ := q1 + c • (Fin.cons 0 (N a))
        have hrow : liftMat q2 N = rowAdd (liftMat q1 N) 0 a.succ c := by
          funext r j
          by_cases hr : r = 0
          · rw [hr]
            simp [liftMat, q2, rowAdd, Pi.add_apply]
          · obtain ⟨r', rfl⟩ := Fin.eq_succ_of_ne_zero hr
            simp [liftMat, q2, rowAdd]
        have hstep : RowStep (liftMat q1 N) (liftMat q2 N) := by
          rw [hrow]
          exact RowStep.add (liftMat q1 N) 0 a.succ (Ne.symm (Fin.succ_ne_zero a)) c
        refine ⟨q2, hreach1.trans (Relation.ReflTransGen.single hstep), ?_, ?_⟩
        · simp [q2]
          exact hq1_0
        · intro i hi
          rcases Finset.mem_insert.mp hi with hia_eq | his
          · rw [hia_eq]
            have hNa : N a (σ a) = sgn a := by simp [hN]
            rcases hsgn a with hs | hs <;> simp [q2, c, hNa, hs]
          · have hia : i ≠ a := fun h => ha (h ▸ his)
            have hne : σ i ≠ σ a := hσ.1.ne hia
            simp [q2, c, hq1_s i his, hN, hne]
  obtain ⟨q', hreach, hq'0, hq'clear⟩ := hmain Finset.univ q
  have hq' : q' = Fin.cons d 0 := by
    funext a
    by_cases ha : a = 0
    · rw [ha]
      simp [hq'0, hq0]
    · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero ha
      have hzero : q' j.succ = 0 := by
        obtain ⟨i, hi⟩ := hσ.2 j
        rw [← hi]
        exact hq'clear i (Finset.mem_univ i)
      simp [hzero]
  simpa [hq'] using hreach

/-! ## 11. Signed permutation matrices -/

/-- A matrix whose rows are signed standard basis vectors, with a bijective index map. -/
def IsSignedPermutationMatrix {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∃ σ : Fin n → Fin n, Function.Bijective σ ∧ ∃ ε : Fin n → Bool,
    ∀ i, M i = if ε i then genVec (σ i) else -genVec (σ i)

lemma isSignedPermutationMatrix_liftMat {n : ℕ} (d : ℤ) (hd : d = 1 ∨ d = -1)
    (N : Matrix (Fin n) (Fin n) ℤ) (σ : Fin n → Fin n) (hσ : Function.Bijective σ)
    (sgn : Fin n → ℤ) (hsgn : ∀ i, sgn i = 1 ∨ sgn i = -1)
    (hN : ∀ i j, N i j = if j = σ i then sgn i else 0) :
    IsSignedPermutationMatrix (liftMat (Fin.cons d 0) N) := by
  classical
  let σ' : Fin (n + 1) → Fin (n + 1) := Fin.cons 0 (fun i => (σ i).succ)
  let ε' : Fin (n + 1) → Bool := Fin.cons (decide (d = 1)) (fun i => decide (sgn i = 1))
  have hσ'inj : Function.Injective σ' := by
    intro a b hab
    by_cases ha : a = 0
    · rw [ha] at hab ⊢
      by_cases hb : b = 0
      · exact hb.symm
      · obtain ⟨b', rfl⟩ := Fin.eq_succ_of_ne_zero hb
        simp [σ'] at hab
        exact absurd hab (Ne.symm (Fin.succ_ne_zero (σ b')))
    · obtain ⟨a', rfl⟩ := Fin.eq_succ_of_ne_zero ha
      by_cases hb : b = 0
      · rw [hb] at hab
        simp [σ'] at hab
      · obtain ⟨b', rfl⟩ := Fin.eq_succ_of_ne_zero hb
        simp only [σ', Fin.cons_succ, Fin.succ_inj] at hab
        exact congrArg Fin.succ (hσ.1 hab)
  have hσ' : Function.Bijective σ' :=
    ⟨hσ'inj, (Finite.injective_iff_surjective (f := σ')).mp hσ'inj⟩
  refine ⟨σ', hσ', ε', ?_⟩
  intro a
  by_cases ha : a = 0
  · rw [ha]
    have hrow : liftMat (Fin.cons d 0) N 0 =
        (Fin.cons d (0 : Fin n → ℤ) : Fin (n + 1) → ℤ) := by
      simp [liftMat]
    rw [hrow, finCons_smul_genVec_zero]
    by_cases hd1 : d = 1
    · simp [σ', ε', hd1, genVec]
    · have hdm1 : d = -1 := by
        rcases hd with h | h
        · exact absurd h hd1
        · exact h
      simp [σ', ε', hdm1, genVec]
  · obtain ⟨a', rfl⟩ := Fin.eq_succ_of_ne_zero ha
    have hrow : liftMat (Fin.cons d 0) N a'.succ = Fin.cons 0 (N a') := by
      simp [liftMat]
    rw [hrow]
    have hNvec : N a' = sgn a' • genVec (σ a') := by
      funext j
      rw [hN a' j]
      by_cases hj : j = σ a'
      · simp [genVec, Pi.single, hj]
      · simp [genVec, Pi.single, hj]
    rw [hNvec, finCons_smul_genVec_succ]
    rcases hsgn a' with hs | hs <;> simp [σ', ε', hs]

/-! ## 12. The matrix induction -/

theorem rowReach_signedPermutation_of_span (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ)
    (hspan : rowSpan M = ⊤) :
    ∃ N : Matrix (Fin n) (Fin n) ℤ, RowReach M N ∧ IsSignedPermutationMatrix N := by
  induction n with
  | zero =>
      refine ⟨M, Relation.ReflTransGen.refl, ?_⟩
      refine ⟨fun i => i, ⟨?_, ?_⟩, fun _ => true, ?_⟩
      · intro a b _
        exact Subsingleton.elim a b
      · intro a
        exact a.elim0
      · intro i
        exact i.elim0
  | succ n ih =>
      obtain ⟨M1, d, hreach1, hd00, hdzero⟩ := exists_rowReach_colFirst n n M
      have hspan1 : rowSpan M1 = ⊤ := (rowSpan_rowReach hreach1).trans hspan
      have hdpm : d = 1 ∨ d = -1 := isUnit_of_colFirst M1 d hd00 hdzero hspan1
      have hdne : d ≠ 0 := by
        rcases hdpm with h | h <;> omega
      have hNspan : rowSpan (fun (i j : Fin n) => M1 i.succ j.succ) = ⊤ :=
        rowSpan_submatrix_succ M1 d hd00 hdzero hdne hspan1
      obtain ⟨N', hreachN, hN'⟩ := ih (fun (i j : Fin n) => M1 i.succ j.succ) hNspan
      have hM1eq : liftMat (M1 0) (fun (i j : Fin n) => M1 i.succ j.succ) = M1 := by
        funext a b
        by_cases ha : a = 0
        · rw [ha]
          simp [liftMat]
        · obtain ⟨a', rfl⟩ := Fin.eq_succ_of_ne_zero ha
          by_cases hb : b = 0
          · rw [hb]
            simp [liftMat, hdzero a'.succ (Fin.succ_ne_zero a')]
          · obtain ⟨b', rfl⟩ := Fin.eq_succ_of_ne_zero hb
            simp [liftMat]
      have hlift : RowReach M1 (liftMat (M1 0) N') := by
        have h := liftMat_rowReach hreachN (M1 0)
        simpa [hM1eq] using h
      obtain ⟨σ, hσ, ε, hε⟩ := hN'
      let sgn : Fin n → ℤ := fun i => if ε i then 1 else -1
      have hsgn : ∀ i, sgn i = 1 ∨ sgn i = -1 := by
        intro i
        by_cases h : ε i <;> simp [sgn, h]
      have hNentry : ∀ i j, N' i j = if j = σ i then sgn i else 0 := by
        intro i j
        rw [hε i]
        by_cases he : ε i
        · by_cases hji : j = σ i
          · rw [hji]
            simp [sgn, he, genVec, Pi.single]
          · simp [sgn, he, hji, genVec, Pi.single]
        · by_cases hji : j = σ i
          · rw [hji]
            simp [sgn, he, genVec, Pi.single]
          · simp [sgn, he, hji, genVec, Pi.single]
      have hclear : RowReach (liftMat (M1 0) N') (liftMat (Fin.cons d 0) N') :=
        exists_rowReach_liftMat_clear (M1 0) d (by simpa using hd00) N' σ hσ sgn hsgn hNentry
      have hfinal : IsSignedPermutationMatrix (liftMat (Fin.cons d 0) N') :=
        isSignedPermutationMatrix_liftMat d hdpm N' σ hσ sgn hsgn hNentry
      exact ⟨liftMat (Fin.cons d 0) N', hreach1.trans (hlift.trans hclear), hfinal⟩

/-! ## 13. The main theorem -/

/-- General-rank A7: every relator tuple of positive rank whose exponent span is the whole
lattice reaches an abelian-terminal state. -/
theorem abelianTerminal_reachable_of_expSpan_top_general (n : ℕ) (_hn : 0 < n)
    (R : Relators n) (h : expSpan R = ⊤) :
    ∃ S : Relators n, Induction.IsAbelianTerminal S ∧ Reachable R S := by
  have hspan : rowSpan (expMatrix R) = ⊤ := by
    rw [← expSpan_eq_rowSpan]
    exact h
  obtain ⟨N, hreach, hN⟩ := rowReach_signedPermutation_of_span n (expMatrix R) hspan
  obtain ⟨S, hS, hRS⟩ := rowReach_reachable hreach R rfl
  refine ⟨S, ?_, hRS⟩
  obtain ⟨σ, hσ, ε, hε⟩ := hN
  refine ⟨σ, hσ, ε, ?_⟩
  intro i
  have hrow := hε i
  rw [← hS] at hrow
  exact hrow
