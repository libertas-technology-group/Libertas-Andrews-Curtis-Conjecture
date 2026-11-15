module

/-
# Detour width is not a function of graph distance

This module restates, in the vocabulary of this corpus, one impossibility result
about the Andrews–Curtis move graph: the detour width of a relator tuple is not
determined by the distance of that tuple from the standard tuple.

Provenance. The statement is due to ph4ge and is published under the MIT licence
(Copyright 2026 ph4ge). Only the statement and the shape of the definitions are
taken from that source; every proof below is re-derived here, and no proof text
is copied.

The two witnesses live at rank two. `R1` inverts one standard relator and `R2`
multiplies it by the other; both are one move from the standard tuple, so both
have graph distance one, while their detour widths are two and three.
-/

public import AcA8PivotReduction
public import AcInvariant

@[expose] public section

set_option autoImplicit false

namespace AC
namespace DetourWidth

open scoped BigOperators

/-! ## Lengths of words and of relator tuples -/

/-- The length of a word, read as the length of its reduced letter list. -/
noncomputable def wordLen {n : ℕ} (w : Word n) : ℕ :=
  w.norm

/-- The total length of a relator tuple, summed over the relators. -/
noncomputable def relLen {n : ℕ} (R : Relators n) : ℕ :=
  ∑ i, wordLen (R i)

/-! ## Finite move paths, kept as data -/

/-- A finite sequence of Andrews–Curtis moves, indexed by its endpoints.  The
sequence is data rather than a proposition so that its length and its largest
intermediate relator length can be read off. -/
inductive MovePath {n : ℕ} : Relators n → Relators n → Type
  | nil (R : Relators n) : MovePath R R
  | cons {R S T : Relators n} (h : Step R S) (p : MovePath S T) : MovePath R T

namespace MovePath

/-- The largest relator-tuple length met along a path, counting both endpoints. -/
noncomputable def maxRelLen {n : ℕ} {R S : Relators n} (p : MovePath R S) : ℕ :=
  match p with
  | .nil _ => relLen R
  | .cons _ q => max (relLen R) q.maxRelLen

/-- The number of moves in a path. -/
def length {n : ℕ} {R S : Relators n} (p : MovePath R S) : ℕ :=
  match p with
  | .nil _ => 0
  | .cons _ q => q.length + 1

/-- A path realises reachability of its endpoints. -/
theorem reachable {n : ℕ} {R S : Relators n} (p : MovePath R S) :
    Reachable R S := by
  induction p with
  | nil R => exact Relation.ReflTransGen.refl
  | cons h q ih => exact Relation.ReflTransGen.head h ih

/-- The endpoint length never exceeds the maximum recorded along the path. -/
theorem relLen_le_maxRelLen {n : ℕ} {R S : Relators n} (p : MovePath R S) :
    relLen S ≤ p.maxRelLen := by
  induction p with
  | nil R => exact le_rfl
  | cons h q ih =>
      simp only [maxRelLen]
      exact le_trans ih (le_max_right _ _)

/-- A path of length zero has equal endpoints. -/
theorem eq_of_length_eq_zero {n : ℕ} {R S : Relators n} (p : MovePath R S)
    (h : p.length = 0) : R = S := by
  cases p with
  | nil R => rfl
  | cons h q => simp [length] at h

end MovePath

/-! ## The two measurements -/

/-- The least bound on the largest relator-tuple length along any move path from
the standard tuple to `R`. -/
noncomputable def detourWidth {n : ℕ} (R : Relators n) : ℕ :=
  sInf { m : ℕ | ∃ p : MovePath (standard n) R, p.maxRelLen ≤ m }

/-- The least number of moves on any move path from the standard tuple to `R`. -/
noncomputable def graphDist {n : ℕ} (R : Relators n) : ℕ :=
  sInf { k : ℕ | ∃ p : MovePath (standard n) R, p.length = k }

/-- A path that stays within `m` bounds the detour width by `m`. -/
theorem detourWidth_le_of_path {n : ℕ} {R : Relators n} {m : ℕ}
    (p : MovePath (standard n) R) (h : p.maxRelLen ≤ m) :
    detourWidth R ≤ m := by
  unfold detourWidth
  exact Nat.sInf_le ⟨p, h⟩

/-- A reachable tuple has relator length at most its detour width. -/
theorem relLen_le_detourWidth {n : ℕ} (R : Relators n)
    (h : ∃ _ : MovePath (standard n) R, True) : relLen R ≤ detourWidth R := by
  obtain ⟨p, _⟩ := h
  unfold detourWidth
  refine le_csInf ⟨p.maxRelLen, p, le_rfl⟩ ?_
  rintro m ⟨q, hq⟩
  exact le_trans (MovePath.relLen_le_maxRelLen q) hq

/-! ## Two witnesses at rank two -/

/-- Invert the first standard relator. -/
def R1 : Relators 2 :=
  Function.update (standard 2) 0 ((FreeGroup.of 0)⁻¹)

/-- Multiply the first standard relator by the second. -/
def R2 : Relators 2 :=
  Function.update (standard 2) 0 (FreeGroup.of 0 * FreeGroup.of 1)

/-- The one-move path reached by inverting the first relator. -/
def pathR1 : MovePath (standard 2) R1 :=
  MovePath.cons (Step.inv (standard 2) 0) (MovePath.nil R1)

/-- The one-move path reached by right-multiplying the first relator. -/
def pathR2 : MovePath (standard 2) R2 :=
  MovePath.cons (Step.mulRight (standard 2) 0 1 (by decide)) (MovePath.nil R2)

/-! ## Lengths of the witnesses -/

theorem relLen_standard_two : relLen (standard 2) = 2 := by
  simp [relLen, wordLen, standard, FreeGroup.norm_of]

theorem relLen_R1 : relLen R1 = 2 := by
  rw [relLen, Fin.sum_univ_two]
  have h0 : wordLen (R1 0) = 1 := by
    unfold wordLen R1
    rw [Function.update_self, FreeGroup.norm_inv_eq, FreeGroup.norm_of]
  have h1 : wordLen (R1 1) = 1 := by
    unfold wordLen R1 standard
    rw [Function.update_of_ne (by decide)]
    exact FreeGroup.norm_of 1
  rw [h0, h1]

theorem norm_of_mul_of_two : (FreeGroup.of (0 : Fin 2) * FreeGroup.of 1).norm = 2 := by
  have hword : (FreeGroup.of (0 : Fin 2) * FreeGroup.of 1).toWord
      = [(0, true), (1, true)] := by
    rw [FreeGroup.toWord_mul, FreeGroup.toWord_of, FreeGroup.toWord_of]
    decide
  show (FreeGroup.of (0 : Fin 2) * FreeGroup.of 1).toWord.length = 2
  rw [hword]
  rfl

theorem relLen_R2 : relLen R2 = 3 := by
  rw [relLen, Fin.sum_univ_two]
  have h0 : wordLen (R2 0) = 2 := by
    unfold wordLen R2
    rw [Function.update_self]
    exact norm_of_mul_of_two
  have h1 : wordLen (R2 1) = 1 := by
    unfold wordLen R2 standard
    rw [Function.update_of_ne (by decide)]
    exact FreeGroup.norm_of 1
  rw [h0, h1]

/-! ## The witnesses differ from the standard tuple -/

theorem R1_ne_standard : R1 ≠ standard 2 := by
  intro h
  have h0 : (FreeGroup.of (0 : Fin 2))⁻¹ = FreeGroup.of 0 := by
    have h' := congrFun h 0
    simp only [R1, standard, Function.update] at h'
    exact h'
  have hword := congrArg FreeGroup.toWord h0
  simp only [FreeGroup.toWord_inv, FreeGroup.toWord_of] at hword
  exact absurd hword (by decide)

theorem R2_ne_standard : R2 ≠ standard 2 := by
  intro h
  have h0 : FreeGroup.of (0 : Fin 2) * FreeGroup.of 1 = FreeGroup.of 0 := by
    have h' := congrFun h 0
    simp only [R2, standard, Function.update] at h'
    exact h'
  have hword := congrArg FreeGroup.toWord h0
  rw [FreeGroup.toWord_mul, FreeGroup.toWord_of, FreeGroup.toWord_of] at hword
  exact absurd hword (by decide)

/-! ## Path measurements for the witnesses -/

theorem maxRelLen_pathR1 : pathR1.maxRelLen = 2 := by
  change max (relLen (standard 2)) (relLen R1) = 2
  rw [relLen_standard_two, relLen_R1]
  rfl

theorem maxRelLen_pathR2 : pathR2.maxRelLen = 3 := by
  change max (relLen (standard 2)) (relLen R2) = 3
  rw [relLen_standard_two, relLen_R2]
  rfl

theorem length_pathR1 : pathR1.length = 1 := rfl

theorem length_pathR2 : pathR2.length = 1 := rfl

/-! ## The two detour widths -/

theorem detourWidth_R1 : detourWidth R1 = 2 := by
  refine le_antisymm ?_ ?_
  · have h : pathR1.maxRelLen ≤ 2 := by rw [maxRelLen_pathR1]
    exact detourWidth_le_of_path pathR1 h
  · have h := relLen_le_detourWidth R1 ⟨pathR1, trivial⟩
    rwa [relLen_R1] at h

theorem detourWidth_R2 : detourWidth R2 = 3 := by
  refine le_antisymm ?_ ?_
  · have h : pathR2.maxRelLen ≤ 3 := by rw [maxRelLen_pathR2]
    exact detourWidth_le_of_path pathR2 h
  · have h := relLen_le_detourWidth R2 ⟨pathR2, trivial⟩
    rwa [relLen_R2] at h

/-! ## The two graph distances -/

theorem graphDist_R1_le : graphDist R1 ≤ 1 := by
  unfold graphDist
  exact Nat.sInf_le ⟨pathR1, length_pathR1⟩

theorem graphDist_R1_ge : 1 ≤ graphDist R1 := by
  unfold graphDist
  refine le_csInf ⟨1, pathR1, length_pathR1⟩ ?_
  rintro k ⟨p, hk⟩
  rw [← hk]
  by_contra hle
  have hlt : p.length < 1 := not_le.mp hle
  have hzero : p.length = 0 := Nat.lt_one_iff.mp hlt
  exact R1_ne_standard (MovePath.eq_of_length_eq_zero p hzero).symm

theorem graphDist_R1 : graphDist R1 = 1 :=
  le_antisymm graphDist_R1_le graphDist_R1_ge

theorem graphDist_R2_le : graphDist R2 ≤ 1 := by
  unfold graphDist
  exact Nat.sInf_le ⟨pathR2, length_pathR2⟩

theorem graphDist_R2_ge : 1 ≤ graphDist R2 := by
  unfold graphDist
  refine le_csInf ⟨1, pathR2, length_pathR2⟩ ?_
  rintro k ⟨p, hk⟩
  rw [← hk]
  by_contra hle
  have hlt : p.length < 1 := not_le.mp hle
  have hzero : p.length = 0 := Nat.lt_one_iff.mp hlt
  exact R2_ne_standard (MovePath.eq_of_length_eq_zero p hzero).symm

theorem graphDist_R2 : graphDist R2 = 1 :=
  le_antisymm graphDist_R2_le graphDist_R2_ge

/-! ## Independence -/

/-- No function of graph distance alone determines the detour width on the set of
tuples reachable from the standard tuple. -/
theorem detourWidth_independent_of_graphDist :
    ¬ ∃ f : ℕ → ℕ, ∀ {n : ℕ} (R : Relators n),
      (∃ _ : MovePath (standard n) R, True) →
      detourWidth R = f (graphDist R) := by
  rintro ⟨f, hf⟩
  have h1 := hf R1 ⟨pathR1, trivial⟩
  have h2 := hf R2 ⟨pathR2, trivial⟩
  rw [detourWidth_R1, graphDist_R1] at h1
  rw [detourWidth_R2, graphDist_R2] at h2
  have hsame : (2 : ℕ) = 3 := by
    rw [h1, h2]
  exact absurd hsame (by decide)

end DetourWidth
end AC
