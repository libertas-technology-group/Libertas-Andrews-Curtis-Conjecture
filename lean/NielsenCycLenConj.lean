module

/-
# Conjugacy invariance of the cyclic Nielsen length

This module proves the two word-level identities the three-stage unimodular
block consumes: the cyclic length of a conjugate equals the cyclic length of the
word, and the cyclic length of an inverse equals the cyclic length of the word.
Both are stated against `AC.Nielsen.cycLen` from `AcNielsenDefs`.

The proof does not enumerate rotations. It compares the ordinary free-group
norms of the powers of the two words.
`FreeGroup.reduceCyclically.reduce_flatten_replicate` gives the exact norm of a
power as `2 * |conjugator| + m * cycLen` for every positive exponent `m`. The
powers of a conjugate are conjugate, and the norm of a conjugate differs from
the norm of the word by at most twice the norm of the conjugator, so the affine
coefficient of `m` on each side is the same. The inverse case uses the same
formula at exponents one and two, together with `FreeGroup.norm_inv_eq`.

The development carries no placeholders and no user-declared assumptions.
-/

public import AcNielsenDefs
public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

@[expose] public section

set_option autoImplicit false

namespace AC
namespace Nielsen

variable {n : ℕ}

/-- **The norm of a power.** For a positive exponent `m`, the ordinary norm of
`x ^ m` is `2 * |conjugator| + m * cycLen x`, where the conjugator is the one
produced by `FreeGroup.reduceCyclically`. -/
theorem norm_pow_eq (x : Word n) {m : ℕ} (hm : 1 ≤ m) :
    FreeGroup.norm (x ^ m) =
      2 * (FreeGroup.reduceCyclically.conjugator x.toWord).length + m * cycLen x := by
  rw [FreeGroup.norm, FreeGroup.toWord_pow]
  rw [FreeGroup.reduceCyclically.reduce_flatten_replicate FreeGroup.isReduced_toWord m]
  rw [ite_eq_right (by omega : ¬ m = 0)]
  unfold cycLen
  simp only [List.length_append, List.length_flatten, List.map_replicate,
    List.sum_replicate, FreeGroup.invRev_length]
  ring

/-- **Powers of a conjugate.** `(A * B * A⁻¹) ^ m = A * B ^ m * A⁻¹`. -/
theorem conj_pow (A B : Word n) (m : ℕ) :
    (A * B * A⁻¹) ^ m = A * B ^ m * A⁻¹ := by
  induction m with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, pow_succ, ih]
      group

/-- **Upper bound on the norm of a conjugate's power.** The norm of
`(A * B * A⁻¹) ^ m` exceeds the norm of `B ^ m` by at most `2 * norm A`. -/
theorem norm_conj_pow_le (A B : Word n) (m : ℕ) :
    FreeGroup.norm ((A * B * A⁻¹) ^ m) ≤
      FreeGroup.norm (B ^ m) + 2 * FreeGroup.norm A := by
  rw [conj_pow]
  calc
    FreeGroup.norm (A * B ^ m * A⁻¹) ≤
        FreeGroup.norm (A * B ^ m) + FreeGroup.norm A⁻¹ :=
      FreeGroup.norm_mul_le _ _
    _ ≤ (FreeGroup.norm A + FreeGroup.norm (B ^ m)) + FreeGroup.norm A := by
      rw [FreeGroup.norm_inv_eq]
      have h := FreeGroup.norm_mul_le A (B ^ m)
      omega
    _ = FreeGroup.norm (B ^ m) + 2 * FreeGroup.norm A := by
      ring

/-- **Reverse bound on the norm of a conjugate's power.** The norm of `B ^ m`
exceeds the norm of `(A * B * A⁻¹) ^ m` by at most `2 * norm A`. -/
theorem norm_pow_le_conj (A B : Word n) (m : ℕ) :
    FreeGroup.norm (B ^ m) ≤
      FreeGroup.norm ((A * B * A⁻¹) ^ m) + 2 * FreeGroup.norm A := by
  have h : B ^ m = A⁻¹ * (A * B * A⁻¹) ^ m * A := by
    rw [conj_pow]
    group
  rw [h]
  calc
    FreeGroup.norm (A⁻¹ * (A * B * A⁻¹) ^ m * A) ≤
        FreeGroup.norm (A⁻¹ * (A * B * A⁻¹) ^ m) + FreeGroup.norm A :=
      FreeGroup.norm_mul_le _ _
    _ ≤ (FreeGroup.norm A⁻¹ + FreeGroup.norm ((A * B * A⁻¹) ^ m)) +
        FreeGroup.norm A := by
      have h2 := FreeGroup.norm_mul_le A⁻¹ ((A * B * A⁻¹) ^ m)
      omega
    _ = FreeGroup.norm ((A * B * A⁻¹) ^ m) + 2 * FreeGroup.norm A := by
      simp only [FreeGroup.norm_inv_eq]
      ring

/-- **Equal slopes from bounded affine functions.** If two affine functions of
`m`, `2 * Cx + m * dx` and `2 * Cy + m * dy`, differ by at most `E` at every
positive integer `m`, then their slopes are equal. -/
private theorem eq_of_bounded_affine {dx dy Cx Cy E : ℕ}
    (h₁ : ∀ m : ℕ, 1 ≤ m → 2 * Cx + m * dx ≤ 2 * Cy + m * dy + E)
    (h₂ : ∀ m : ℕ, 1 ≤ m → 2 * Cy + m * dy ≤ 2 * Cx + m * dx + E) :
    dx = dy := by
  rcases le_total dy dx with hle | hle
  · have ht : dy + (dx - dy) = dx := Nat.add_sub_of_le hle
    have h := h₁ (2 * Cy + 2 * E + 1) (by omega)
    rw [← ht, Nat.mul_add] at h
    have hkey : (2 * Cy + 2 * E + 1) * (dx - dy) ≤ 2 * Cy + 2 * E := by omega
    have hzero : dx - dy = 0 := by
      by_contra hne
      have ht1 : 1 ≤ dx - dy := Nat.one_le_iff_ne_zero.mpr hne
      have hmul : 2 * Cy + 2 * E + 1 ≤ (2 * Cy + 2 * E + 1) * (dx - dy) := by
        simpa using Nat.mul_le_mul_left (2 * Cy + 2 * E + 1) ht1
      omega
    omega
  · have ht : dx + (dy - dx) = dy := Nat.add_sub_of_le hle
    have h := h₂ (2 * Cx + 2 * E + 1) (by omega)
    rw [← ht, Nat.mul_add] at h
    have hkey : (2 * Cx + 2 * E + 1) * (dy - dx) ≤ 2 * Cx + 2 * E := by omega
    have hzero : dy - dx = 0 := by
      by_contra hne
      have ht1 : 1 ≤ dy - dx := Nat.one_le_iff_ne_zero.mpr hne
      have hmul : 2 * Cx + 2 * E + 1 ≤ (2 * Cx + 2 * E + 1) * (dy - dx) := by
        simpa using Nat.mul_le_mul_left (2 * Cx + 2 * E + 1) ht1
      omega
    omega

/-- **Conjugacy invariance of the cyclic Nielsen length.**
`cycLen (A * B * A⁻¹) = cycLen B` for every pair of words at every rank. -/
theorem cycLen_conj (A B : Word n) : cycLen (A * B * A⁻¹) = cycLen B := by
  refine eq_of_bounded_affine
    (Cx := (FreeGroup.reduceCyclically.conjugator (A * B * A⁻¹).toWord).length)
    (Cy := (FreeGroup.reduceCyclically.conjugator B.toWord).length)
    (E := 2 * FreeGroup.norm A) ?_ ?_
  · intro m hm
    rw [← norm_pow_eq (A * B * A⁻¹) hm, ← norm_pow_eq B hm]
    exact norm_conj_pow_le A B m
  · intro m hm
    rw [← norm_pow_eq (A * B * A⁻¹) hm, ← norm_pow_eq B hm]
    exact norm_pow_le_conj A B m

/-- **Inversion invariance of the cyclic Nielsen length.**
`cycLen A⁻¹ = cycLen A` for every word at every rank. -/
theorem cycLen_inv (A : Word n) : cycLen A⁻¹ = cycLen A := by
  have h1 := norm_pow_eq (A⁻¹) (m := 1) (by omega)
  have h2 := norm_pow_eq A (m := 1) (by omega)
  have h3 := norm_pow_eq (A⁻¹) (m := 2) (by omega)
  have h4 := norm_pow_eq A (m := 2) (by omega)
  have e1 : FreeGroup.norm ((A⁻¹) ^ 1) = FreeGroup.norm (A ^ 1) := by
    rw [inv_pow, FreeGroup.norm_inv_eq]
  have e2 : FreeGroup.norm ((A⁻¹) ^ 2) = FreeGroup.norm (A ^ 2) := by
    rw [inv_pow, FreeGroup.norm_inv_eq]
  rw [e1] at h1
  rw [e2] at h3
  simp only [pow_one] at h1 h2
  omega

/-- **The proposition recorded as `CycLenConjugacyInvariant`.** The pair of
rank-two identities the three-stage unimodular measure claim consumes, proved
from the rank-general theorems above. -/
theorem cycLenConjugacyInvariant :
    (∀ (A B : Word 2), cycLen (A * B * A⁻¹) = cycLen B) ∧
      (∀ A : Word 2, cycLen A⁻¹ = cycLen A) :=
  ⟨cycLen_conj, cycLen_inv⟩

end Nielsen
end AC
