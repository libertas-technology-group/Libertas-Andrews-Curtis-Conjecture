import AC
import Mathlib.Tactic

/-!
# The Akbulut–Kirby AK(3) presentation

Akbulut and Kirby introduced the family
`AK(n) = ⟨a, b | a^n b^{-(n+1)}, a b a b^{-1} a^{-1} b^{-1}⟩` for `n ≥ 2`.
The case `n = 3` is the rank-two balanced presentation
`⟨a, b | a^3 b^{-4}, a b a b^{-1} a^{-1} b^{-1}⟩`. The second relator is the braid
relation `a b a = b a b`, and the first is `a^3 = b^4`.

The presentation presents the trivial group. In the quotient write `a` and `b`
for the images of the two generators and set `d = a b a`. The braid relator
gives `d a d^{-1} = b` and `d b d^{-1} = a`. Conjugating `a^3 = b^4` by `d`
gives `b^3 = a^4`, so `a = a^4 a^{-3} = b^3 b^{-4} = b^{-1}`. Substituting this
into the braid relator gives `b^{-1} = b`, hence `b^2 = 1`. The relation
`a^3 = b^4` then gives `b = 1`, and therefore `a = 1`. The normal closure of the
two relators is the whole free group, so the presented group is a subsingleton.
-/

namespace AC.Ak3

/-- The first AK(3) relator `a^3 b^{-4}`. -/
def ak3R1 : Word 2 :=
  (FreeGroup.of 0) ^ 3 * (FreeGroup.of 1) ^ (-4 : ℤ)

/-- The second AK(3) relator `a b a b^{-1} a^{-1} b^{-1}`. -/
def ak3R2 : Word 2 :=
  FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹ *
    (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹

/-- The Akbulut–Kirby AK(3) balanced presentation at rank two. -/
def ak3 : Relators 2 := ![ak3R1, ak3R2]

/-- AK(3) presents the trivial group. -/
theorem ak3_presentsTrivial : PresentsTrivialGroup ak3 := by
  unfold PresentsTrivialGroup
  refine ⟨fun x y => ?_⟩
  let a : PresentedGroup (Set.range ak3) := PresentedGroup.of 0
  let b : PresentedGroup (Set.range ak3) := PresentedGroup.of 1
  have h1 : a ^ 3 * b ^ (-4 : ℤ) = 1 := by
    have hm : PresentedGroup.mk (Set.range ak3) (ak3 0) = 1 :=
      PresentedGroup.one_of_mem (Set.mem_range_self (0 : Fin 2))
    simpa [ak3, ak3R1, a, b, PresentedGroup.of] using hm
  have h2 : a * b * a * b⁻¹ * a⁻¹ * b⁻¹ = 1 := by
    have hm : PresentedGroup.mk (Set.range ak3) (ak3 1) = 1 :=
      PresentedGroup.one_of_mem (Set.mem_range_self (1 : Fin 2))
    simpa [ak3, ak3R2, a, b, PresentedGroup.of] using hm
  have hA : a ^ 3 = b ^ 4 := by
    have h1' : a ^ 3 * (b ^ 4)⁻¹ = 1 := by simpa using h1
    exact eq_of_mul_inv_eq_one h1'
  have hB : a * b * a = b * a * b := by
    calc a * b * a = (a * b * a * b⁻¹ * a⁻¹ * b⁻¹) * (b * a * b) := by group
      _ = 1 * (b * a * b) := by rw [h2]
      _ = b * a * b := by group
  let d : PresentedGroup (Set.range ak3) := a * b * a
  have hda : d * a * d⁻¹ = b := by
    calc d * a * d⁻¹ = a * b * a * b⁻¹ * a⁻¹ := by
          dsimp only [d]
          group
      _ = (b * a * b) * b⁻¹ * a⁻¹ := by rw [hB]
      _ = b := by group
  have hdb : d * b * d⁻¹ = a := by
    calc d * b * d⁻¹ = b * a * b * a⁻¹ * b⁻¹ := by
          rw [show d = b * a * b from hB]
          group
      _ = (a * b * a) * a⁻¹ * b⁻¹ := by rw [hB]
      _ = a := by group
  have hA' : b ^ 3 = a ^ 4 := by
    have hleft : d * a ^ 3 * d⁻¹ = b ^ 3 := by
      calc d * a ^ 3 * d⁻¹ = (d * a * d⁻¹) ^ 3 := by rw [conj_pow]
        _ = b ^ 3 := by rw [hda]
    have hright : d * b ^ 4 * d⁻¹ = a ^ 4 := by
      calc d * b ^ 4 * d⁻¹ = (d * b * d⁻¹) ^ 4 := by rw [conj_pow]
        _ = a ^ 4 := by rw [hdb]
    calc b ^ 3 = d * a ^ 3 * d⁻¹ := hleft.symm
      _ = d * b ^ 4 * d⁻¹ := by rw [hA]
      _ = a ^ 4 := hright
  have hab : a = b⁻¹ := by
    calc a = a ^ 4 * (a ^ 3)⁻¹ := by group
      _ = b ^ 3 * (b ^ 4)⁻¹ := by rw [hA', hA]
      _ = b⁻¹ := by group
  have hb_inv : b⁻¹ = b := by
    have h := hB
    rw [hab] at h
    simpa using h
  have hb2 : b * b = 1 := by
    calc b * b = b⁻¹ * b := by rw [hb_inv]
      _ = 1 := by group
  have hb3 : b ^ 3 = b := by
    calc b ^ 3 = b ^ 2 * b := by group
      _ = 1 * b := by simp [pow_two, hb2]
      _ = b := by group
  have hb4 : b ^ 4 = 1 := by
    calc b ^ 4 = b ^ 2 * b ^ 2 := by group
      _ = 1 * 1 := by simp [pow_two, hb2]
      _ = 1 := by group
  have hbinv3 : (b⁻¹) ^ 3 = b := by
    calc (b⁻¹) ^ 3 = (b ^ 3)⁻¹ := by group
      _ = b⁻¹ := by rw [hb3]
      _ = b := hb_inv
  have hb1 : b = 1 := by
    have h := hA
    rw [hab] at h
    rw [hbinv3, hb4] at h
    exact h
  have ha1 : a = 1 := by
    rw [hab, hb1]
    group
  have hgen : ∀ z : PresentedGroup (Set.range ak3), z = 1 := by
    intro z
    have hmem : z ∈ (⊥ : Subgroup (PresentedGroup (Set.range ak3))) := by
      apply PresentedGroup.generated_by (Set.range ak3) (⊥ : Subgroup _)
      intro j
      fin_cases j
      · exact Subgroup.mem_bot.mpr ha1
      · exact Subgroup.mem_bot.mpr hb1
    exact Subgroup.mem_bot.mp hmem
  exact hgen x ▸ hgen y ▸ rfl

/-- The open Andrews–Curtis question for AK(3), stated as a proposition.
No proof is asserted here: whether AK(3) is Andrews–Curtis trivial is open. -/
def ak3_not_reachable : Prop := ¬ Reachable ak3 (standard 2)

end AC.Ak3
