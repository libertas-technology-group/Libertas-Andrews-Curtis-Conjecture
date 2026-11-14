import AcStallingsExponentMeasure
import AcProof

/-!
# AcStallingsExponentCounterexample — the replacement measure is refuted

`exponentDefect2` is zero on a larger set than the signed permutations. The
state

```text
(x, y * (x * y * x⁻¹ * y⁻¹))
```

presents the trivial group, is not a signed permutation, and has exponent defect
zero. Therefore `exponentDescentStatement2` is false: there is no state of
strictly smaller defect.

The counterexample shows that a word-level defect is required. The exponent
vector alone cannot separate the terminal set from states that carry a
commutator factor.
-/

set_option autoImplicit false

namespace AC
namespace Stallings

/-- The first relator `x`. -/
def exponentCounterexampleR0 : Word 2 := FreeGroup.of 0

/-- The second relator `y * (x * y * x⁻¹ * y⁻¹)`. -/
def exponentCounterexampleR1 : Word 2 :=
  FreeGroup.of 1 *
    (FreeGroup.of 0 * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹)

/-- The rank-two trivial presentation with a commutator factor. -/
def exponentCounterexample : Relators 2 :=
  ![exponentCounterexampleR0, exponentCounterexampleR1]

lemma exponentCounterexampleR1_length :
    (exponentCounterexample 1).toWord.length = 5 := by decide

/-- The counterexample presents the trivial group. -/
theorem exponentCounterexample_presentsTrivial :
    PresentsTrivialGroup exponentCounterexample := by
  unfold PresentsTrivialGroup
  let rels := Set.range exponentCounterexample
  let x : PresentedGroup rels := PresentedGroup.of 0
  let y : PresentedGroup rels := PresentedGroup.of 1
  have hx0 : PresentedGroup.mk rels (exponentCounterexample 0) = 1 :=
    PresentedGroup.one_of_mem (Set.mem_range_self 0)
  have hx : x = 1 := by
    simpa [x, rels, exponentCounterexample, exponentCounterexampleR0,
      PresentedGroup.of] using hx0
  have hy0 : PresentedGroup.mk rels (exponentCounterexample 1) = 1 :=
    PresentedGroup.one_of_mem (Set.mem_range_self 1)
  have hy1 : y * (x * y * x⁻¹ * y⁻¹) = 1 := by
    simpa [y, x, rels, exponentCounterexample, exponentCounterexampleR1,
      PresentedGroup.of] using hy0
  have hy : y = 1 := by
    simpa [hx] using hy1
  have hrange :
      Set.range (fun i : Fin 2 => PresentedGroup.of (rels := rels) i) = {1} := by
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · simpa using hx
      · simpa using hy
    · intro hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact ⟨0, by simpa [x] using hx⟩
  have htop :
      Subgroup.closure (Set.range (fun i : Fin 2 =>
        PresentedGroup.of (rels := rels) i)) = ⊤ :=
    PresentedGroup.closure_range_of rels
  have hbot :
      Subgroup.closure (Set.range (fun i : Fin 2 =>
        PresentedGroup.of (rels := rels) i)) = ⊥ := by
    rw [hrange, Subgroup.closure_singleton_one]
  refine ⟨fun a b => ?_⟩
  have ha : a ∈ Subgroup.closure (Set.range (fun i : Fin 2 =>
      PresentedGroup.of (rels := rels) i)) := by
    rw [htop]
    exact Subgroup.mem_top a
  rw [hbot] at ha
  have hb : b ∈ Subgroup.closure (Set.range (fun i : Fin 2 =>
      PresentedGroup.of (rels := rels) i)) := by
    rw [htop]
    exact Subgroup.mem_top b
  rw [hbot] at hb
  rw [Subgroup.mem_bot] at ha hb
  rw [ha, hb]

lemma expVec_exponentCounterexample_0 :
    Invariant.expVec (exponentCounterexample 0) = ![(1 : ℤ), 0] := by decide

lemma expVec_exponentCounterexample_1 :
    Invariant.expVec (exponentCounterexample 1) = ![(0 : ℤ), 1] := by decide

/-- The exponent defect is zero although the presentation is not terminal. -/
lemma exponentDefect2_exponentCounterexample :
    exponentDefect2 exponentCounterexample = 0 := by
  simp [exponentDefect2, expVec_exponentCounterexample_0,
    expVec_exponentCounterexample_1]

/-- The counterexample is not a signed permutation. -/
lemma exponentCounterexample_not_signedPermutation :
    ¬ ProofAttempt.IsSignedPermutation exponentCounterexample := by
  rintro ⟨σ, hσ, ε, hε⟩
  have h1 := hε 1
  have len1 : (exponentCounterexample 1).toWord.length = 1 := by
    rw [h1]
    split <;> simp
  have h5 : (exponentCounterexample 1).toWord.length = 5 := by decide
  omega

/-- The replacement measure's general descent statement is false. -/
theorem exponentDescentStatement2_false :
    ¬ exponentDescentStatement2 := by
  intro h
  obtain ⟨S, hreach, hlt⟩ :=
    h exponentCounterexample exponentCounterexample_presentsTrivial
      exponentCounterexample_not_signedPermutation
  rw [exponentDefect2_exponentCounterexample] at hlt
  omega

end Stallings
end AC

#print axioms AC.Stallings.exponentDescentStatement2_false
