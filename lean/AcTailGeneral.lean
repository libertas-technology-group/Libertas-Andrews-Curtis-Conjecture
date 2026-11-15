module

public import AcTailDefs
public import Mathlib.Tactic.Group

@[expose] public section

/-!
# AcTailGeneral — the exact tail of a product

The tail removes the coset section `x ^ a * y ^ b` from the right of a word.  The
section of a product is not the product of the sections, because the two
generators do not commute in the free group, so the tail is not multiplicative.
This module states the exact correction for a product of two words on two
generators, and derives the right-multiplication law for a right factor of zero
exponent vector.

Write `c w` for `cosetSection (expVec w 0) (expVec w 1)`.  For words `w` and
`u`,

    tail (w * u) = tail w * (c w * u * (c (w * u))⁻¹).

The tail of the left factor is multiplied by the right word conjugated by the
section of the left factor, and the inverse section of the product is the
correction that the two section factors leave.  When `expVec u = 0`, the section
of the product is the section of `w`, and the formula reads

    tail (w * u) = tail w * (c w * u * (c w)⁻¹),

which is `tail_mul_right`.

Both theorems are closed terms: `tail_mul_general` and `tail_mul_right` carry a
complete proof.
-/

set_option autoImplicit false

namespace AC
namespace Tail

open AC.Invariant

/-- The exact tail of a product.  The right word is conjugated by the section of
the left factor, and the inverse section of the product is the correction left
by the two section factors. -/
theorem tail_mul_general (w u : Word 2) :
    tail (w * u) =
      tail w * (cosetSection (expVec w 0) (expVec w 1) * u *
        (cosetSection (expVec (w * u) 0) (expVec (w * u) 1))⁻¹) := by
  simp only [tail]
  group

/-- Right multiplication by a word of zero exponent vector: the section of the
product is the section of the left factor, so the correction disappears and the
right word is conjugated by that section. -/
theorem tail_mul_right {w u : Word 2} (hu : expVec u = 0) :
    tail (w * u) =
      tail w * (cosetSection (expVec w 0) (expVec w 1) * u *
        (cosetSection (expVec w 0) (expVec w 1))⁻¹) := by
  rw [tail_mul_general]
  rw [expVec_mul, hu]
  have hzero : (expVec w + (0 : Fin 2 → ℤ)) = expVec w := by
    funext i
    exact add_zero (expVec w i)
  rw [hzero]

end Tail
end AC
