import AcTailDefs
import Mathlib.Tactic.Group

/-!
# AcTailClass — both tails of a multiplier core are nontrivial

`MultiplierCore S` forces `tail (S 0) ≠ 1` and `tail (S 1) ≠ 1`.  The first
multiplier inequality is read at `u = (tail (S i))⁻¹`.  When `tail (S j) = 1`
the relator `S j` is a signed generator `(of k)^e`, so the conjugate product
`ConjProd (S j)` contains every word of exponent vector zero, in particular
`(tail (S i))⁻¹`.  The inequality then forces `tail (S i)` to have length zero,
hence to be `1`, and `0 < totalTail S` supplies the contradiction.

The auxiliary theorem `exists_conjProd_mul_zpow` writes any word as
`v * (of b)^m` with `v` in the conjugate product of `of a`.  Letters in `of a`
are absorbed into `v`; letters in `of b` are moved past `v` by conjugation, so
a word with zero exponent vector is a conjugate product of `of a`.
-/

set_option autoImplicit false

namespace AC
namespace Tail

open AC.Invariant
open AC.Euclid

/-! ## 1. The exponent vector of a generator and of a section -/

/-- The exponent vector of a free generator is the corresponding basis vector. -/
@[simp] lemma expVec_of (i : Fin 2) : expVec (FreeGroup.of i) = genVec i := by
  simp [expVec, expHom]

/-- The exponent vector of the coset section `x ^ a * y ^ b`. -/
lemma expVec_cosetSection (a b : ℤ) :
    expVec (cosetSection a b) = a • genVec (0 : Fin 2) + b • genVec (1 : Fin 2) := by
  simp [cosetSection, expVec_mul, expVec_zpow]

lemma expVec_cosetSection_zero (a b : ℤ) : expVec (cosetSection a b) 0 = a := by
  rw [expVec_cosetSection]
  simp [genVec]

lemma expVec_cosetSection_one (a b : ℤ) : expVec (cosetSection a b) 1 = b := by
  rw [expVec_cosetSection]
  simp [genVec]

lemma expVec_cosetSection_expVec (w : Word 2) :
    expVec (cosetSection (expVec w 0) (expVec w 1)) = expVec w := by
  ext i
  fin_cases i
  · exact expVec_cosetSection_zero _ _
  · exact expVec_cosetSection_one _ _

/-- A coset section has trivial tail. -/
lemma tail_cosetSection (a b : ℤ) : tail (cosetSection a b) = 1 := by
  unfold tail
  rw [expVec_cosetSection_zero, expVec_cosetSection_one, mul_inv_cancel]

/-- A word with trivial tail is its own coset section. -/
lemma eq_cosetSection_of_tail_eq_one {w : Word 2} (h : tail w = 1) :
    w = cosetSection (expVec w 0) (expVec w 1) := by
  unfold tail at h
  exact eq_of_mul_inv_eq_one h

/-- A word is its tail times the section of its exponent vector. -/
lemma eq_tail_mul_cosetSection (w : Word 2) :
    w = tail w * cosetSection (expVec w 0) (expVec w 1) := by
  unfold tail
  rw [mul_assoc, inv_mul_cancel, mul_one]

/-- The tail has zero exponent vector. -/
lemma expVec_tail (w : Word 2) : expVec (tail w) = 0 := by
  unfold tail
  rw [expVec_mul, expVec_inv, expVec_cosetSection_expVec]
  simp

/-! ## 2. Closure properties of the conjugate product -/

lemma conjProd_inv {B u : Word 2} (h : ConjProd B u) : ConjProd B u⁻¹ := by
  induction h with
  | one => simpa using ConjProd.one (B := B)
  | ofConj w =>
      rw [show (w * B * w⁻¹)⁻¹ = w * B⁻¹ * w⁻¹ by group]
      exact ConjProd.ofConjInv w
  | ofConjInv w =>
      rw [show (w * B⁻¹ * w⁻¹)⁻¹ = w * B * w⁻¹ by group]
      exact ConjProd.ofConj w
  | mul _ _ ih1 ih2 =>
      rw [mul_inv_rev]
      exact ConjProd.mul ih2 ih1

lemma conjProd_conj {B u : Word 2} (h : ConjProd B u) (w : Word 2) :
    ConjProd B (w * u * w⁻¹) := by
  induction h with
  | one => simpa using ConjProd.one (B := B)
  | ofConj v =>
      rw [show w * (v * B * v⁻¹) * w⁻¹ = (w * v) * B * (w * v)⁻¹ by group]
      exact ConjProd.ofConj (w * v)
  | ofConjInv v =>
      rw [show w * (v * B⁻¹ * v⁻¹) * w⁻¹ = (w * v) * B⁻¹ * (w * v)⁻¹ by group]
      exact ConjProd.ofConjInv (w * v)
  | mul _ _ ih1 ih2 =>
      convert ConjProd.mul ih1 ih2 using 1
      group

/-- Replacing the base word by its inverse does not change the conjugate product. -/
lemma conjProd_inv_base {B u : Word 2} (h : ConjProd B u) : ConjProd B⁻¹ u := by
  induction h with
  | one => exact ConjProd.one
  | ofConj w => simpa using ConjProd.ofConjInv (B := B⁻¹) w
  | ofConjInv w => simpa using ConjProd.ofConj (B := B⁻¹) w
  | mul _ _ ih1 ih2 => exact ConjProd.mul ih1 ih2

/-- A conjugate product of `of a` has zero exponent in every other coordinate. -/
lemma conjProd_expVec_other_eq_zero {a b : Fin 2} (hba : b ≠ a) {v : Word 2}
    (hv : ConjProd (FreeGroup.of a) v) : expVec v b = 0 := by
  induction hv with
  | one => simp
  | ofConj w =>
      rw [expVec_conj, expVec_of]
      exact Pi.single_eq_of_ne hba 1
  | ofConjInv w =>
      rw [expVec_conj, expVec_inv, expVec_of]
      simp [genVec, Pi.single_eq_of_ne hba]
  | mul _ _ ih1 ih2 => rw [expVec_mul, Pi.add_apply, ih1, ih2, add_zero]

/-! ## 3. Every zero-exponent word is a conjugate product of a generator -/

/-- The other index of `Fin 2`. -/
private def otherIndex (k : Fin 2) : Fin 2 := if k = 0 then 1 else 0

private lemma otherIndex_ne (k : Fin 2) : otherIndex k ≠ k := by
  fin_cases k <;> simp [otherIndex]

private lemma fin2_eq_or_eq_of_ne {a b i : Fin 2} (hab : a ≠ b) : i = a ∨ i = b := by
  fin_cases i <;> fin_cases a <;> fin_cases b <;> simp_all

private lemma mk_singleton_true (i : Fin 2) :
    FreeGroup.mk ([(i, true)] : List (Fin 2 × Bool)) = FreeGroup.of i := rfl

private lemma mk_singleton_false (i : Fin 2) :
    FreeGroup.mk ([(i, false)] : List (Fin 2 × Bool)) = (FreeGroup.of i)⁻¹ := by
  have h : FreeGroup.invRev ([(i, true)] : List (Fin 2 × Bool)) = [(i, false)] := rfl
  rw [← h, ← FreeGroup.inv_mk]
  rfl

/-- A word is a conjugate product of `of a` times a power of `of b`, for any two
distinct generators. -/
private lemma exists_conjProd_mul_zpow {a b : Fin 2} (hab : a ≠ b)
    (L : List (Fin 2 × Bool)) :
    ∃ (v : Word 2) (m : ℤ), ConjProd (FreeGroup.of a) v ∧
      FreeGroup.mk L = v * (FreeGroup.of b) ^ m := by
  induction L with
  | nil =>
      exact ⟨1, 0, ConjProd.one, by simp [FreeGroup.one_eq_mk]⟩
  | cons head tail ih =>
      obtain ⟨i, bit⟩ := head
      obtain ⟨v, m, hv, hdec⟩ := ih
      rcases fin2_eq_or_eq_of_ne hab (i := i) with hia | hib
      · rw [hia]
        cases bit
        · refine ⟨(FreeGroup.of a)⁻¹ * v, m, ?_, ?_⟩
          · exact ConjProd.mul
              (by simpa using ConjProd.ofConjInv (B := FreeGroup.of a) (1 : Word 2)) hv
          · calc FreeGroup.mk ((a, false) :: tail)
                = FreeGroup.mk [(a, false)] * FreeGroup.mk tail :=
                    (FreeGroup.mul_mk (L₁ := [(a, false)]) (L₂ := tail)).symm
              _ = (FreeGroup.of a)⁻¹ * (v * (FreeGroup.of b) ^ m) := by
                    rw [mk_singleton_false, hdec]
              _ = ((FreeGroup.of a)⁻¹ * v) * (FreeGroup.of b) ^ m := by group
        · refine ⟨FreeGroup.of a * v, m, ?_, ?_⟩
          · exact ConjProd.mul
              (by simpa using ConjProd.ofConj (B := FreeGroup.of a) (1 : Word 2)) hv
          · calc FreeGroup.mk ((a, true) :: tail)
                = FreeGroup.mk [(a, true)] * FreeGroup.mk tail :=
                    (FreeGroup.mul_mk (L₁ := [(a, true)]) (L₂ := tail)).symm
              _ = FreeGroup.of a * (v * (FreeGroup.of b) ^ m) := by
                    rw [mk_singleton_true, hdec]
              _ = (FreeGroup.of a * v) * (FreeGroup.of b) ^ m := by group
      · rw [hib]
        cases bit
        · refine ⟨(FreeGroup.of b)⁻¹ * v * FreeGroup.of b, m - 1, ?_, ?_⟩
          · simpa using conjProd_conj hv (FreeGroup.of b)⁻¹
          · calc FreeGroup.mk ((b, false) :: tail)
                = FreeGroup.mk [(b, false)] * FreeGroup.mk tail :=
                    (FreeGroup.mul_mk (L₁ := [(b, false)]) (L₂ := tail)).symm
              _ = (FreeGroup.of b)⁻¹ * (v * (FreeGroup.of b) ^ m) := by
                    rw [mk_singleton_false, hdec]
              _ = ((FreeGroup.of b)⁻¹ * v * FreeGroup.of b) *
                    (FreeGroup.of b) ^ (m - 1) := by group
        · refine ⟨FreeGroup.of b * v * (FreeGroup.of b)⁻¹, m + 1, ?_, ?_⟩
          · exact conjProd_conj hv (FreeGroup.of b)
          · calc FreeGroup.mk ((b, true) :: tail)
                = FreeGroup.mk [(b, true)] * FreeGroup.mk tail :=
                    (FreeGroup.mul_mk (L₁ := [(b, true)]) (L₂ := tail)).symm
              _ = FreeGroup.of b * (v * (FreeGroup.of b) ^ m) := by
                    rw [mk_singleton_true, hdec]
              _ = (FreeGroup.of b * v * (FreeGroup.of b)⁻¹) *
                    (FreeGroup.of b) ^ (m + 1) := by group

/-- Every word with zero exponent vector is a conjugate product of every
generator. -/
lemma conjProd_of_expVec_zero {a b : Fin 2} (hab : a ≠ b) {u : Word 2}
    (hu : expVec u = 0) : ConjProd (FreeGroup.of a) u := by
  obtain ⟨v, m, hv, hdec⟩ := exists_conjProd_mul_zpow hab u.toWord
  have hu_eq : u = v * (FreeGroup.of b) ^ m := by
    rw [← hdec]
    exact (FreeGroup.mk_toWord).symm
  have hvb : expVec v b = 0 := conjProd_expVec_other_eq_zero (Ne.symm hab) hv
  have hm : m = 0 := by
    have h := congrArg (fun w : Word 2 => expVec w b) hu_eq
    change expVec u b = expVec (v * (FreeGroup.of b) ^ m) b at h
    rw [hu, expVec_mul, Pi.add_apply, hvb, zero_add, expVec_zpow,
      Pi.smul_apply, expVec_of] at h
    simpa [genVec] using h.symm
  rw [hu_eq, hm, zpow_zero, mul_one]
  exact hv

/-- A conjugate product of `of a` is a conjugate product of any signed power of
`of a` with exponent `±1`. -/
lemma conjProd_zpow_of_signed {a : Fin 2} {e : ℤ} (he : e = 1 ∨ e = -1)
    {u : Word 2} (h : ConjProd (FreeGroup.of a) u) :
    ConjProd ((FreeGroup.of a) ^ e) u := by
  rcases he with rfl | rfl
  · simpa using h
  · simpa using conjProd_inv_base h

/-- The section of a signed basis vector is the corresponding signed generator. -/
lemma cosetSection_smul_genVec (k : Fin 2) (e : ℤ) :
    cosetSection ((e • genVec k) 0) ((e • genVec k) 1) = (FreeGroup.of k) ^ e := by
  fin_cases k <;> simp [cosetSection, genVec]

/-! ## 4. The generator-tail kill -/

/-- If one relator of a multiplier core has trivial tail, so does the other.
The first multiplier inequality is applied at the inverse of the other tail. -/
lemma tail_eq_one_of_multiplierCore {S : Relators 2} (h : MultiplierCore S)
    {i j : Fin 2} (hij : i ≠ j) (hj : tail (S j) = 1) : tail (S i) = 1 := by
  have hmul1 := h.2.2.2.1
  obtain ⟨σ, -, ε, hε⟩ := h.1
  set k : Fin 2 := σ j with hk
  set e : ℤ := if ε j then 1 else -1 with he
  have hexpj : expVec (S j) = e • genVec k := by
    have hh := hε j
    rw [hk, he]
    cases hb : ε j
    · simpa [hb] using hh
    · simpa [hb] using hh
  have hSj : S j = (FreeGroup.of k) ^ e := by
    rw [eq_cosetSection_of_tail_eq_one hj, hexpj]
    exact cosetSection_smul_genVec k e
  set T : Word 2 := tail (S i) with hT
  have hSi : S i = T * cosetSection (expVec (S i) 0) (expVec (S i) 1) := by
    rw [hT]
    exact eq_tail_mul_cosetSection (S i)
  have hExpZero : expVec T⁻¹ = 0 := by
    rw [expVec_inv, hT, expVec_tail]
    simp
  have hkey : ConjProd (FreeGroup.of k) T⁻¹ :=
    conjProd_of_expVec_zero (a := k) (b := otherIndex k)
      (Ne.symm (otherIndex_ne k)) hExpZero
  have he_pm : e = 1 ∨ e = -1 := by
    rw [he]
    cases ε j <;> simp
  have hConj : ConjProd (S j) T⁻¹ := by
    rw [hSj]
    exact conjProd_zpow_of_signed he_pm hkey
  have hineq : tailLength (S i) ≤ (tail (T⁻¹ * S i)).toWord.length :=
    hmul1 i j hij T⁻¹ hExpZero hConj
  have hTS : T⁻¹ * S i = cosetSection (expVec (S i) 0) (expVec (S i) 1) := by
    conv_lhs => rw [hSi]
    group
  have htail_one : tail (T⁻¹ * S i) = 1 := by
    rw [hTS, tail_cosetSection]
  have hlen : (tail (S i)).toWord.length = 0 := by
    have h0 : (tail (T⁻¹ * S i)).toWord.length = 0 := by rw [htail_one]; rfl
    have hle := hineq
    simp only [tailLength] at hle
    omega
  have hnil : (tail (S i)).toWord = [] := List.eq_nil_of_length_eq_zero hlen
  calc tail (S i) = FreeGroup.mk ((tail (S i)).toWord) := (FreeGroup.mk_toWord).symm
    _ = FreeGroup.mk ([] : List (Fin 2 × Bool)) := by rw [hnil]
    _ = 1 := FreeGroup.one_eq_mk.symm

/-- In a multiplier core both tails are nontrivial. -/
theorem multiplierCore_both_tails_nontrivial (S : Relators 2) (h : MultiplierCore S) :
    tail (S 0) ≠ 1 ∧ tail (S 1) ≠ 1 := by
  constructor
  · intro h0
    have h1 : tail (S 1) = 1 :=
      tail_eq_one_of_multiplierCore h (i := 1) (j := 0) (by decide) h0
    have hpos : 0 < totalTail S := h.2.2.1
    have htot : totalTail S = 0 := by simp [totalTail, tailLength, h0, h1]
    rw [htot] at hpos
    exact absurd hpos (lt_irrefl (0 : ℕ))
  · intro h1
    have h0 : tail (S 0) = 1 :=
      tail_eq_one_of_multiplierCore h (i := 0) (j := 1) (by decide) h1
    have hpos : 0 < totalTail S := h.2.2.1
    have htot : totalTail S = 0 := by simp [totalTail, tailLength, h0, h1]
    rw [htot] at hpos
    exact absurd hpos (lt_irrefl (0 : ℕ))

/-- `MultiplierCorePlus` inherits both nontrivial tails. -/
theorem multiplierCorePlus_both_tails_nontrivial (S : Relators 2)
    (h : MultiplierCorePlus S) : tail (S 0) ≠ 1 ∧ tail (S 1) ≠ 1 :=
  multiplierCore_both_tails_nontrivial S h.1

end Tail
end AC
