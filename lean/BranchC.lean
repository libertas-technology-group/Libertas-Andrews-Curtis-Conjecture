module

public import AC
public import AcInvariant
public import Mathlib.RingTheory.Noetherian.Orzech
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Module.Submodule.Lattice

@[expose] public section

/-!
# Branch C: presentation-complex and normal-form invariants

This file is the Lean part of the Branch C invariant search. It records two
pruning results and one surviving candidate, and it states exactly which part of
each result is formalized.

## 1. The presentation complex at chain level

For a balanced presentation `R : Relators n`, the presentation 2-complex has one
0-cell, `n` 1-cells, and `n` 2-cells. Its cellular chain complex is

    0 → ℤⁿ --∂₂--> ℤⁿ --0--> ℤ → 0,

where `∂₂` is `boundary2 R`: the `i`-th basis vector of the relator lattice is
sent to the exponent vector `expVec (R i)`. The first homology is
`h1 R = ℤⁿ ⧸ expSpan R`; the second homology is `h2 R = ker (boundary2 R)`.

`h1_subsingleton_of_presents` and `h2_eq_bot_of_presents` prove that both vanish
for every presentation of the trivial group. The first is the closed gap G1 of
`AcInvariant`; the second is the Hopfian property of the finitely generated
free abelian group `ℤⁿ`, discharged by
`IsNoetherian.injective_of_surjective_endomorphism`.

The chain-level vanishing is what the file proves. The inference from vanishing
reduced homology and trivial `π₁` to contractibility of the 2-complex is
Whitehead's theorem; it is stated in `BRANCH_C.md` and is not formalized here,
because the pinned Mathlib does not carry the required CW-complex API.

## 2. The cocommutative (winding) domain obstruction

The winding invariant of Barmak (arXiv:1806.11493) is defined on a presentation
whose relators all lie in the commutator subgroup of the free group, which at
the level of the exponent map is `Cocommutative R`. `expSpan_eq_bot_of_cocommutative`
computes the span of such a presentation as `⊥`. `not_cocommutative_of_presents`
combines that computation with G1 and proves that no presentation of the trivial
group is cocommutative at positive rank. `not_cocommutative_standard` proves the
same for the standard tuple directly.

The consequence is the exact failure of the winding separation test: the domain
of the invariant and the class of presentations of the trivial group are
disjoint, so the invariant cannot even be evaluated at a candidate presentation
or at `standard n`. The class is pruned by empty domain, not by equality of
values.

## Status

The file is in the `AcCorpus` globs and compiles in the 3,308-job build under
`leanprover/lean4:v4.29.1` with Mathlib `5e932f97…`. No `sorry` body, `axiom`,
or `admit`; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace AC
namespace BranchC

open Invariant

variable {n : ℕ}

/-! ## 1. The second boundary map of the presentation complex -/

/-- The second boundary map of the presentation 2-complex. The relator at
position `i` contributes its exponent vector `expVec (R i)` to the generator
coordinates. -/
noncomputable def boundary2 (R : Relators n) : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ) where
  toFun c := ∑ i, c i • expVec (R i)
  map_add' c d := by
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp [Finset.smul_sum, mul_assoc]

/-- The range of the second boundary map is the exponent span. This is the
chain-level form of the identity "the image of the exponent matrix is the row
space of the relator exponent vectors". -/
theorem range_boundary2 (R : Relators n) :
    LinearMap.range (boundary2 R) = expSpan R := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    show (∑ i, c i • expVec (R i)) ∈ expSpan R
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (expVec_mem_expSpan R i)
  · rw [expSpan, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine ⟨(fun i => if i = j then (1 : ℤ) else 0), ?_⟩
    show (∑ i, (if i = j then (1 : ℤ) else 0) • expVec (R i)) = expVec (R j)
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim

/-- The first homology of the presentation complex, as the cokernel of the second
boundary map. -/
noncomputable def h1 (R : Relators n) : Type :=
  (Fin n → ℤ) ⧸ expSpan R

/-- The second homology of the presentation complex, as the kernel of the second
boundary map. -/
noncomputable def h2 (R : Relators n) : Submodule ℤ (Fin n → ℤ) :=
  LinearMap.ker (boundary2 R)

/-- Triviality of the presented group kills the first homology. -/
theorem h1_subsingleton_of_presents {R : Relators n} (h : PresentsTrivialGroup R) :
    Subsingleton (h1 R) := by
  have htop : expSpan R = ⊤ := expSpan_eq_top_of_presents h
  rw [h1, htop]
  infer_instance

/-- Triviality of the presented group kills the second homology.

The proof is the Hopfian property of `ℤⁿ`: the boundary map is a surjective
endomorphism of a finitely generated free abelian group, and a surjective
endomorphism of a Noetherian module is injective. -/
theorem h2_eq_bot_of_presents {R : Relators n} (h : PresentsTrivialGroup R) :
    h2 R = ⊥ := by
  have htop : expSpan R = ⊤ := expSpan_eq_top_of_presents h
  have hsurj : Function.Surjective (boundary2 R) := by
    rw [← LinearMap.range_eq_top, range_boundary2, htop]
  have : IsNoetherianRing ℤ := PrincipalIdealRing.isNoetherianRing
  have : Module.Finite ℤ (Fin n → ℤ) := inferInstance
  have : IsNoetherian ℤ (Fin n → ℤ) :=
    isNoetherian_of_isNoetherianRing_of_finite ℤ (Fin n → ℤ)
  rw [h2]
  exact LinearMap.ker_eq_bot.mpr
    (IsNoetherian.injective_of_surjective_endomorphism (boundary2 R) hsurj)

/-- The chain-level acyclicity of the presentation complex of a trivial
presentation: first and second homology vanish. -/
theorem chain_acyclic_of_presents {R : Relators n} (h : PresentsTrivialGroup R) :
    Subsingleton (h1 R) ∧ h2 R = ⊥ :=
  ⟨h1_subsingleton_of_presents h, h2_eq_bot_of_presents h⟩

/-- Two presentations of the trivial group carry the same second homology. -/
theorem h2_eq_of_presents {R S : Relators n}
    (hR : PresentsTrivialGroup R) (hS : PresentsTrivialGroup S) : h2 R = h2 S := by
  rw [h2_eq_bot_of_presents hR, h2_eq_bot_of_presents hS]

/-- Two presentations of the trivial group have subsingleton first homology. -/
theorem h1_subsingleton_of_presents_pair {R S : Relators n}
    (hR : PresentsTrivialGroup R) (hS : PresentsTrivialGroup S) :
    Subsingleton (h1 R) ∧ Subsingleton (h1 S) :=
  ⟨h1_subsingleton_of_presents hR, h1_subsingleton_of_presents hS⟩

/-! ## 2. The cocommutative domain obstruction for the winding invariant -/

/-- A presentation is cocommutative when every relator has zero exponent vector.
For a word in a free group this is the condition that the word lies in the
commutator subgroup. It is the domain on which Barmak's winding polynomial is
defined. -/
def Cocommutative (R : Relators n) : Prop :=
  ∀ i, expVec (R i) = 0

/-- A cocommutative presentation has zero exponent span. -/
theorem expSpan_eq_bot_of_cocommutative {R : Relators n} (h : Cocommutative R) :
    expSpan R = ⊥ := by
  rw [expSpan, eq_bot_iff, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  change expVec (R i) ∈ (⊥ : Submodule ℤ (Fin n → ℤ))
  rw [h i]
  exact Submodule.zero_mem _

/-- No presentation of the trivial group is cocommutative at positive rank. -/
theorem not_cocommutative_of_presents {R : Relators n} (hn : 0 < n)
    (h : PresentsTrivialGroup R) : ¬ Cocommutative R := by
  intro hc
  have hbot : expSpan R = ⊥ := expSpan_eq_bot_of_cocommutative hc
  have htop : expSpan R = ⊤ := expSpan_eq_top_of_presents h
  have hEq : (⊥ : Submodule ℤ (Fin n → ℤ)) = ⊤ := by
    rw [← hbot, htop]
  let i : Fin n := ⟨0, hn⟩
  have hmem : genVec i ∈ (⊥ : Submodule ℤ (Fin n → ℤ)) := by
    rw [hEq]
    exact Submodule.mem_top
  have hzero : genVec i = 0 := (Submodule.mem_bot ℤ).mp hmem
  have hval : genVec i i = (1 : ℤ) := by simp [genVec]
  rw [hzero] at hval
  simp at hval

/-- The standard tuple is not cocommutative at positive rank. -/
theorem not_cocommutative_standard (hn : 0 < n) : ¬ Cocommutative (standard n) := by
  intro hc
  let i : Fin n := ⟨0, hn⟩
  have h0 : expVec (standard n i) = 0 := hc i
  have h1 : expVec (standard n i) = genVec i := by
    simp [expVec, expHom, standard, genVec, FreeGroup.lift_apply_of]
  rw [h1] at h0
  have hval : genVec i i = (1 : ℤ) := by simp [genVec]
  rw [h0] at hval
  simp at hval

/-- The winding separation test is empty on the class of trivial presentations:
no member of the class, and not the standard tuple, lies in the domain of the
winding invariant. -/
theorem winding_domain_empty_on_trivial {R : Relators n} (hn : 0 < n)
    (h : PresentsTrivialGroup R) :
    ¬ Cocommutative R ∧ ¬ Cocommutative (standard n) :=
  ⟨not_cocommutative_of_presents hn h, not_cocommutative_standard hn⟩

end BranchC
end AC
