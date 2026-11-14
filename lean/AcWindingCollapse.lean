/-
  The abelianisation collapse, exponent-vector half.

  `AcRelationModuleCollapse` compiles the normal-closure half of Gaur's
  statement: when a balanced presentation presents the one-element group, its
  relation subgroup is the whole free group, so the relation module is the same
  abstract type for every such presentation.  The half left open there is the
  identification of that type with the exponent-vector group `ℤⁿ`.

  This module closes that half.  The abelianisation of the free group on `n`
  generators is the free abelian group on `n` generators, which is the group of
  finitely supported functions `Fin n → ℤ`; under the standard basis this is the
  exponent-vector group.  `abelianizationWordEquiv` is that identification, and
  `abelianizationWordEquiv_of` computes it on a word: the class of `w` maps to
  `expVec w`.  `relationModule_equiv_expVec` transports the identification to
  the relation module of any presentation of the trivial group, so an invariant
  that factors through the abelianised normal closure, on that class, is the
  exponent-sum matrix.

  Source of the claim:
    EXTERNAL_REPOS/COMPETITORS/Andrews-Curtis-Conjecture/research/directions/
    invariant-ideas/idea.md:180-196  (MIT, Copyright 2026 Pragyaan Gaur)

  Nothing below copies code from that repository.  The statement is restated in
  this corpus's own vocabulary and proved from this corpus's own definitions.

  Note on the import.  The single-file check compiles this file with
  `lake env lean <absolute path>`, and that search path is the pinned corpus
  build only: it holds no entry for the sandbox directory, so a sibling sandbox
  module such as `AcRelationModuleCollapse` cannot be imported.  This file
  therefore imports the corpus module `Ak3Invariant`, which supplies every
  definition used below, and reproduces the one lemma it needs from the sibling
  module (`relationSubgroup_eq_top`) inline.  The mathematical content is the
  continuation of that module, and it composes with it unchanged.
-/
import Ak3Invariant
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Map

namespace AC.RelationCollapse

open Ak3Invariant

/-- The abelianisation of the free group on `n` generators is the exponent-vector
group `ℤⁿ`, written multiplicatively.  It is the composite of three additive
equivalences: the abelianisation of a free group is the free abelian group, the
free abelian group is the group of finitely supported integer functions, and a
finitely supported function on a finite type is an arbitrary function. -/
noncomputable def abelianizationWordEquiv (n : ℕ) :
    Abelianization (Word n) ≃* Multiplicative (Fin n → ℤ) :=
  (MulEquiv.multiplicativeAdditive (H := Abelianization (Word n))).symm.trans
    (AddEquiv.toMultiplicative
      ((FreeAbelianGroup.equivFinsupp (Fin n)).trans
        (Finsupp.addEquivFunOnFinite (M := ℤ))))

/-- The identification sends the class of a word to its exponent vector.  Both
sides are monoid homomorphisms out of the free group, so it suffices to check the
generators, where the class of the `i`-th generator maps to the basis vector with
a `1` in position `i`. -/
theorem abelianizationWordEquiv_of (n : ℕ) (w : Word n) :
    abelianizationWordEquiv n (Abelianization.of w) =
      Multiplicative.ofAdd (Invariant.expVec w) := by
  have hhom : (abelianizationWordEquiv n).toMonoidHom.comp Abelianization.of =
      Invariant.expHom n := by
    apply FreeGroup.ext_hom
    intro i
    simp only [MonoidHom.comp_apply, Invariant.expHom, FreeGroup.lift_apply_of]
    have hfinal :
        ((FreeAbelianGroup.equivFinsupp (Fin n)).trans Finsupp.addEquivFunOnFinite)
            (Additive.ofMul (Abelianization.of (FreeGroup.of i))) = Pi.single i 1 := by
      have h1 : Additive.ofMul (Abelianization.of (FreeGroup.of i)) =
          FreeAbelianGroup.of i := rfl
      rw [h1, AddEquiv.trans_apply, FreeAbelianGroup.equivFinsupp_apply,
        FreeAbelianGroup.toFinsupp_of]
      simp only [Finsupp.addEquivFunOnFinite]
      exact Finsupp.equivFunOnFinite_single i 1
    simpa [abelianizationWordEquiv, Invariant.genVec] using
      congrArg Multiplicative.ofAdd hfinal
  have h := DFunLike.congr_fun hhom w
  simpa [Invariant.expVec] using h

/-- The relation module of any presentation of the one-element group is the
exponent-vector group, and the equivalence sends the class of each relator to its
exponent vector.  The relation subgroup is the whole free group, so the relation
module is the abelianisation of the free group, and `abelianizationWordEquiv`
identifies that with `ℤⁿ`. -/
theorem relationModule_equiv_expVec {n : ℕ} {R : Relators n}
    (h : PresentsTrivialGroup R) :
    ∃ e : Abelianization (relationSubgroup R) ≃* Multiplicative (Fin n → ℤ),
      ∀ (i : Fin n) (hi : R i ∈ relationSubgroup R),
        e (Abelianization.of ⟨R i, hi⟩) =
          Multiplicative.ofAdd (Invariant.expVec (R i)) := by
  have htop : relationSubgroup R = ⊤ := by
    haveI : (relationSubgroup R).Normal := by
      unfold relationSubgroup
      infer_instance
    rw [eq_top_iff]
    intro w _
    haveI : Subsingleton (Word n ⧸ relationSubgroup R) := h
    have h1 : (QuotientGroup.mk w : Word n ⧸ relationSubgroup R) = 1 :=
      Subsingleton.elim _ _
    exact (QuotientGroup.eq_one_iff w).mp h1
  refine ⟨?_, ?_⟩
  · exact (MulEquiv.abelianizationCongr
      ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)).trans
      (abelianizationWordEquiv n)
  · intro i hi
    have hx : ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv) ⟨R i, hi⟩ = R i := by
      rw [MulEquiv.trans_apply]
      rfl
    simp only [MulEquiv.trans_apply, abelianizationCongr_of, hx]
    exact abelianizationWordEquiv_of n (R i)

end AC.RelationCollapse
