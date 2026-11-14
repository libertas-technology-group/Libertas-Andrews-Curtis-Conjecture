import Ak3
import Ak3Separation
import AcBase
import AcProof
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-!
# AK(3): the relation module, lower-central classes, finite quotients, and
# isomorphism invariants

`Ak3.ak3` is the rank-two Akbulut–Kirby presentation
`⟨a, b | a^3 b^{-4}, a b a b^{-1} a^{-1} b^{-1}⟩`, and
`Ak3.ak3_presentsTrivial` proves that it presents the one-element group.  The
PSL(2, ℤ) quotient-index route, the metabelian Magnus orbit test, and the Fox
row-module route are pruned elsewhere.  This file tests the next invariant
family: invariants built from the relation subgroup, the relation module, the
lower central series, finite quotients, and isomorphism invariants of the
presented group such as K-theoretic classes attached to its group ring.

## The invariants

For a balanced presentation `R : Relators n` the *relation subgroup* is

    relationSubgroup R = Subgroup.normalClosure (Set.range R),

the normal closure of the relators in the free group `F_n`.  The *relation
module* is its abelianisation

    relationModule R = Abelianization (relationSubgroup R).

When the presented group is one-element the conjugation action of the presented
group on the relation module is the unique trivial action, so the abelian group
`relationModule R` is the entire relation-module invariant.

## Preservation

`relationSubgroup_step` and `relationSubgroup_reachable` prove that every
official move, and every finite sequence of official moves, preserves the
relation subgroup.  Therefore the relation module and every function of the
relation subgroup are preserved.  `presentedGroup_eq_of_step` and
`presentedGroup_eq_of_reachable` prove the stronger statement that the presented
group itself is unchanged by every move.

## The no-go

Both `Ak3.ak3` and the standard pair present the one-element group.  The AK(3)
relators normally generate `F₂` (`Ak3Separation.normalClosure_range_ak3`), while
the standard generators also normally generate `F₂`
(`Ak3Separation.normalClosure_range_standard`).  Hence

    relationSubgroup Ak3.ak3 = ⊤ = relationSubgroup (standard 2)

and the two relation modules are literally the same type:

    relationModule Ak3.ak3 = relationModule (standard 2).

Every lower-central-series quotient of either presented group is a one-element
group.  Every homomorphism from `F₂` to any group that kills the AK(3) relators
is trivial, so a finite-target test, in particular one through a non-soluble
finite group such as `A₅`, sees the trivial pair.  Finally, any function of
groups that is constant on multiplicative equivalence takes the same value on
the two presented groups, because both are one-element groups and therefore
multiplicatively equivalent.

These results are no-go theorems: the tested invariant family cannot separate
`Ak3.ak3` from `standard 2`.  The separation theorem is stated conditionally in
`invariant_separation`.  The unconditional statement
`¬ Reachable Ak3.ak3 (standard 2)` is the exact open goal, restated as
`ak3_separation_goal`; it is not proved here.

## Status

No `sorry`, no `admit`, no user `axiom`, no `native_decide`.  Single-file check
from `lean/`: `lake env lean Ak3Invariant.lean`.  The writer of this file is not
its verifier.
-/

set_option autoImplicit false

namespace AC
namespace Ak3Invariant

/-! ## 0. A utility: one-element groups are multiplicatively equivalent -/

/-- Any two one-element groups are multiplicatively equivalent. -/
def subsingletonMulEquiv (G H : Type*) [Group G] [Group H]
    [Subsingleton G] [Subsingleton H] : G ≃* H where
  toFun := fun _ => 1
  invFun := fun _ => 1
  left_inv := fun x => Subsingleton.elim _ _
  right_inv := fun x => Subsingleton.elim _ _
  map_mul' := fun _ _ => by simp

/-! ## 1. The relation subgroup and the relation module -/

/-- The relation subgroup of a balanced presentation: the normal closure of the
relators in the free group.  This is the subgroup whose abelianisation, with the
conjugation action of the presented group, is the relation module. -/
noncomputable def relationSubgroup {n : ℕ} (R : Relators n) : Subgroup (Word n) :=
  Subgroup.normalClosure (Set.range R)

/-- The relation module of a balanced presentation, taken as the abelianisation
of the relation subgroup.  When the presented group is one-element, the group
ring action is the unique trivial action, so this abelian group is the whole
relation-module invariant. -/
noncomputable abbrev relationModule {n : ℕ} (R : Relators n) : Type :=
  Abelianization (relationSubgroup R)

/-- A monoid homomorphism out of a one-element group is determined by its
codomain: any two such homomorphisms are equal.  Applied to the conjugation
action of the presented group on the relation module, this says the action is
unique when the presented group is one-element. -/
theorem monoidHom_eq_of_subsingleton_domain {G M : Type*} [Group G] [Monoid M]
    [Subsingleton G] (f g : G →* M) : f = g := by
  ext x
  rw [Subsingleton.elim x 1]
  simp

/-! ## 2. Preservation under the official moves -/

/-- Every official move preserves the relation subgroup.  The three cases are the
three moves: inversion, right multiplication by another relator, and conjugation
by an arbitrary word.  The normal closure is unchanged in each case. -/
theorem relationSubgroup_step {n : ℕ} {R S : Relators n} (h : Step R S) :
    relationSubgroup S = relationSubgroup R := by
  cases h with
  | inv i => exact ProofAttempt.normalClosure_range_inv R i
  | mulRight i j hij => exact ProofAttempt.normalClosure_range_mulRight R i j hij
  | conj i w => exact ProofAttempt.normalClosure_range_conj R i w

/-- Every finite sequence of official moves preserves the relation subgroup. -/
theorem relationSubgroup_reachable {n : ℕ} {R S : Relators n} (h : Reachable R S) :
    relationSubgroup S = relationSubgroup R := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact (relationSubgroup_step hstep).trans ih

/-- Every official move preserves the relation module. -/
theorem relationModule_step {n : ℕ} {R S : Relators n} (h : Step R S) :
    relationModule S = relationModule R := by
  show Abelianization (relationSubgroup S) = Abelianization (relationSubgroup R)
  exact congrArg (fun H : Subgroup (Word n) => Abelianization H) (relationSubgroup_step h)

/-- Every finite sequence of official moves preserves the relation module. -/
theorem relationModule_reachable {n : ℕ} {R S : Relators n} (h : Reachable R S) :
    relationModule S = relationModule R := by
  show Abelianization (relationSubgroup S) = Abelianization (relationSubgroup R)
  exact congrArg (fun H : Subgroup (Word n) => Abelianization H) (relationSubgroup_reachable h)

/-! ## 3. The relation subgroup of AK(3) and of the standard pair -/

/-- The AK(3) relators normally generate the free group, because AK(3) presents
the one-element group. -/
theorem relationSubgroup_ak3 : relationSubgroup Ak3.ak3 = ⊤ :=
  Ak3Separation.normalClosure_range_ak3

/-- The standard generator pair normally generates the free group. -/
theorem relationSubgroup_standard : relationSubgroup (standard 2) = ⊤ :=
  Ak3Separation.normalClosure_range_standard

/-- The two relation subgroups are the same subgroup of `F₂`. -/
theorem relationSubgroup_ak3_eq_standard :
    relationSubgroup Ak3.ak3 = relationSubgroup (standard 2) := by
  rw [relationSubgroup_ak3, relationSubgroup_standard]

/-- Consequently the two relation modules are the same type. -/
theorem relationModule_ak3_eq_standard :
    relationModule Ak3.ak3 = relationModule (standard 2) := by
  show Abelianization (relationSubgroup Ak3.ak3)
      = Abelianization (relationSubgroup (standard 2))
  rw [relationSubgroup_ak3, relationSubgroup_standard]

/-- The relation-module invariant cannot separate AK(3) from the standard pair:
its two values are equal. -/
theorem relationModule_cannot_separate :
    ¬ (relationModule Ak3.ak3 ≠ relationModule (standard 2)) := by
  intro h
  exact h relationModule_ak3_eq_standard

/-- Any invariant that is a function of the relation subgroup is constant on
`Ak3.ak3` and `standard 2`.  This covers the relation module, the relation
subgroup itself, and every functorial construction on them. -/
theorem relationInvariant_cannot_separate {α : Type*} (F : Relators 2 → α)
    (hF : ∀ R S : Relators 2, relationSubgroup R = relationSubgroup S → F R = F S) :
    ¬ (F Ak3.ak3 ≠ F (standard 2)) := by
  intro h
  exact h (hF Ak3.ak3 (standard 2) relationSubgroup_ak3_eq_standard)

/-! ## 4. The presented group and the lower central series -/

/-- The group presented by AK(3) is one-element. -/
theorem presentedGroup_ak3_subsingleton :
    Subsingleton (PresentedGroup (Set.range Ak3.ak3)) :=
  Ak3.ak3_presentsTrivial

/-- The group presented by the standard pair is one-element. -/
theorem presentedGroup_standard_subsingleton :
    Subsingleton (PresentedGroup (Set.range (standard 2))) :=
  Base.presentsTrivialGroup_standard 2

/-- Every official move leaves the presented group unchanged. -/
theorem presentedGroup_eq_of_step {n : ℕ} {R S : Relators n} (h : Step R S) :
    PresentedGroup (Set.range S) = PresentedGroup (Set.range R) := by
  have hN : Subgroup.normalClosure (Set.range S) = Subgroup.normalClosure (Set.range R) :=
    relationSubgroup_step h
  show (FreeGroup (Fin n) ⧸ Subgroup.normalClosure (Set.range S)) =
      (FreeGroup (Fin n) ⧸ Subgroup.normalClosure (Set.range R))
  rw [hN]

/-- Every finite sequence of official moves leaves the presented group unchanged. -/
theorem presentedGroup_eq_of_reachable {n : ℕ} {R S : Relators n} (h : Reachable R S) :
    PresentedGroup (Set.range S) = PresentedGroup (Set.range R) := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact (presentedGroup_eq_of_step hstep).trans ih

/-- Triviality of the presented group is preserved along every path out of
AK(3). -/
theorem presentsTrivial_of_reachable_ak3 {R : Relators 2}
    (h : Reachable Ak3.ak3 R) : PresentsTrivialGroup R :=
  (ProofAttempt.presents_of_reachable h).mp Ak3.ak3_presentsTrivial

/-- In a one-element group every subgroup is the whole group, so every term of
the lower central series is the whole group. -/
theorem lowerCentralSeries_eq_top_of_subsingleton {G : Type*} [Group G]
    [Subsingleton G] (k : ℕ) : lowerCentralSeries G k = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [Subsingleton.elim x 1]
  exact Subgroup.one_mem _

/-- The lower central series of the group presented by AK(3) is the whole group
at every stage. -/
theorem lowerCentralSeries_ak3_eq_top (k : ℕ) :
    lowerCentralSeries (PresentedGroup (Set.range Ak3.ak3)) k = ⊤ := by
  haveI : Subsingleton (PresentedGroup (Set.range Ak3.ak3)) := Ak3.ak3_presentsTrivial
  exact lowerCentralSeries_eq_top_of_subsingleton k

/-- The lower central series of the group presented by the standard pair is the
whole group at every stage. -/
theorem lowerCentralSeries_standard_eq_top (k : ℕ) :
    lowerCentralSeries (PresentedGroup (Set.range (standard 2))) k = ⊤ := by
  haveI : Subsingleton (PresentedGroup (Set.range (standard 2))) :=
    Base.presentsTrivialGroup_standard 2
  exact lowerCentralSeries_eq_top_of_subsingleton k

/-- The `k`-th lower central quotient of a balanced presentation. -/
noncomputable abbrev lowerCentralQuotient {n : ℕ} (R : Relators n) (k : ℕ) : Type :=
  PresentedGroup (Set.range R) ⧸
    lowerCentralSeries (PresentedGroup (Set.range R)) k

/-- The `k`-th lower central quotient of AK(3) is a one-element group. -/
theorem lowerCentralQuotient_ak3_subsingleton (k : ℕ) :
    Subsingleton (lowerCentralQuotient Ak3.ak3 k) :=
  QuotientGroup.subsingleton_iff.mpr (lowerCentralSeries_ak3_eq_top k)

/-- The `k`-th lower central quotient of the standard pair is a one-element
group. -/
theorem lowerCentralQuotient_standard_subsingleton (k : ℕ) :
    Subsingleton (lowerCentralQuotient (standard 2) k) :=
  QuotientGroup.subsingleton_iff.mpr (lowerCentralSeries_standard_eq_top k)

/-- The `k`-th lower central quotient remains one-element along every official
path out of AK(3).  This is the preservation statement for the lower-central
class: the class cannot change from the trivial class. -/
theorem lowerCentralQuotient_subsingleton_of_reachable_ak3 {R : Relators 2}
    (h : Reachable Ak3.ak3 R) (k : ℕ) :
    Subsingleton (lowerCentralQuotient R k) := by
  haveI : Subsingleton (PresentedGroup (Set.range R)) := presentsTrivial_of_reachable_ak3 h
  exact QuotientGroup.subsingleton_iff.mpr (lowerCentralSeries_eq_top_of_subsingleton k)

/-- The `k`-th lower central quotients of AK(3) and of the standard pair are
multiplicatively equivalent at every stage. -/
theorem lowerCentralQuotient_mulEquiv (k : ℕ) :
    Nonempty (lowerCentralQuotient Ak3.ak3 k ≃* lowerCentralQuotient (standard 2) k) := by
  haveI : Subsingleton (lowerCentralQuotient Ak3.ak3 k) :=
    lowerCentralQuotient_ak3_subsingleton k
  haveI : Subsingleton (lowerCentralQuotient (standard 2) k) :=
    lowerCentralQuotient_standard_subsingleton k
  exact ⟨subsingletonMulEquiv _ _⟩

/-! ## 5. Finite quotients -/

/-- A homomorphism out of `F₂` that kills every AK(3) relator is trivial.  The
kernel is a normal subgroup containing the relators, hence containing their
normal closure, which is the whole free group. -/
theorem hom_trivial_of_kills_relators {H : Type*} [Group H] (f : Word 2 →* H)
    (hkill : ∀ r ∈ Set.range Ak3.ak3, f r = 1) (x : Word 2) : f x = 1 := by
  have hker : Subgroup.normalClosure (Set.range Ak3.ak3) ≤ MonoidHom.ker f := by
    refine Subgroup.normalClosure_le_normal ?_
    intro r hr
    exact MonoidHom.mem_ker.mpr (hkill r hr)
  rw [Ak3Separation.normalClosure_range_ak3] at hker
  exact MonoidHom.mem_ker.mp (hker (Subgroup.mem_top x))

/-- Every finite quotient of the presented AK(3) group is trivial, so a finite
quotient outside the soluble and PSL classes sees the trivial pair `(1, 1)`.
The statement is quantified over every group `H`; the finite case is the
intended application. -/
theorem finiteQuotient_cannot_separate {H : Type*} [Group H] [Fintype H]
    (f : Word 2 →* H) (hkill : ∀ r ∈ Set.range Ak3.ak3, f r = 1) :
    f (FreeGroup.of (0 : Fin 2)) = 1 ∧ f (FreeGroup.of (1 : Fin 2)) = 1 :=
  ⟨hom_trivial_of_kills_relators f hkill _,
   hom_trivial_of_kills_relators f hkill _⟩

/-! ## 6. Isomorphism invariants of the presented group

A K-theoretic class attached to the presented group, its group cohomology, its
lower central quotients, and its finite quotients are all determined by the
isomorphism class of that group.  The next two results give the generic no-go.
The Fox-matrix class over `ℤ[F₂]` is not a presented-group invariant; it is the
already-pruned Fox route and is not reopened here.
-/

/-- The groups presented by AK(3) and by the standard pair are multiplicatively
equivalent. -/
theorem presentedGroup_ak3_mulEquiv_standard :
    Nonempty (PresentedGroup (Set.range Ak3.ak3) ≃*
      PresentedGroup (Set.range (standard 2))) := by
  haveI : Subsingleton (PresentedGroup (Set.range Ak3.ak3)) := Ak3.ak3_presentsTrivial
  haveI : Subsingleton (PresentedGroup (Set.range (standard 2))) :=
    Base.presentsTrivialGroup_standard 2
  exact ⟨subsingletonMulEquiv _ _⟩

/-- Any group invariant that is constant on multiplicative equivalence takes the
same value on the two presented groups.  This covers K-theoretic classes of the
group ring, group cohomology, and every other isomorphism invariant of the
presented group. -/
theorem groupInvariant_ak3_eq_standard {α : Type*}
    (I : (G : Type) → [Group G] → α)
    (hI : ∀ {G H : Type} [Group G] [Group H], G ≃* H → I G = I H) :
    I (PresentedGroup (Set.range Ak3.ak3))
      = I (PresentedGroup (Set.range (standard 2))) := by
  haveI : Subsingleton (PresentedGroup (Set.range Ak3.ak3)) := Ak3.ak3_presentsTrivial
  haveI : Subsingleton (PresentedGroup (Set.range (standard 2))) :=
    Base.presentsTrivialGroup_standard 2
  exact hI (subsingletonMulEquiv _ _)

/-- A ring invariant of the integral group ring that is constant on ring
isomorphism takes the same value on the group rings of the two presented
groups.  The group rings are `ℤ[G]`, where `K₀`, `K₁`, and the other
K-theoretic invariants live.  This is the concrete K-theoretic no-go. -/
theorem groupRingInvariant_ak3_eq_standard {α : Type*}
    (K : (R : Type) → [Ring R] → α)
    (hK : ∀ {R S : Type} [Ring R] [Ring S], R ≃+* S → K R = K S) :
    K (MonoidAlgebra ℤ (PresentedGroup (Set.range Ak3.ak3)))
      = K (MonoidAlgebra ℤ (PresentedGroup (Set.range (standard 2)))) := by
  haveI : Subsingleton (PresentedGroup (Set.range Ak3.ak3)) := Ak3.ak3_presentsTrivial
  haveI : Subsingleton (PresentedGroup (Set.range (standard 2))) :=
    Base.presentsTrivialGroup_standard 2
  exact hK (MonoidAlgebra.mapDomainRingEquiv (R := ℤ) (subsingletonMulEquiv _ _))

/-! ## 7. The conditional separation theorem and the exact open goal -/

/-- A presentation invariant preserved by every official move is constant along
reachability. -/
theorem invariant_reachable {α : Type*} (I : Relators 2 → α)
    (hstep : ∀ {R S : Relators 2}, Step R S → I S = I R)
    {R S : Relators 2} (h : Reachable R S) : I S = I R := by
  induction h with
  | refl => rfl
  | tail _ hstep' ih => exact (hstep hstep').trans ih

/-- The separation theorem in invariant form: a presentation invariant preserved
by every official move, whose value on AK(3) differs from its value on the
standard pair, refutes reachability. -/
theorem invariant_separation {α : Type*} (I : Relators 2 → α)
    (hstep : ∀ {R S : Relators 2}, Step R S → I S = I R)
    (hne : I Ak3.ak3 ≠ I (standard 2)) :
    ¬ Reachable Ak3.ak3 (standard 2) := by
  intro h
  exact hne (by simpa using (invariant_reachable I hstep h).symm)

/-- The separation theorem instantiated at the relation module.  The
hypothesis is refuted by `relationModule_cannot_separate`. -/
theorem relationModule_separation
    (h : relationModule Ak3.ak3 ≠ relationModule (standard 2)) :
    ¬ Reachable Ak3.ak3 (standard 2) :=
  invariant_separation relationModule relationModule_step h

/-- The exact open goal: AK(3) is not Andrews–Curtis reachable to the standard
pair.  No proof is asserted in this file. -/
def ak3_separation_goal : Prop :=
  ¬ Reachable Ak3.ak3 (standard 2)

end Ak3Invariant
end AC
