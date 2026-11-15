module

public import AC
public import AcStableTrivial
public import AcStableProjection
public import AcBase
public import AcProof
public import Ak3
public import BranchD2
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.Tactic

@[expose] public section

/-!
# AcStableWitness — the rank-two trivial-presentation witness lane

The high-value target is a rank-two trivial presentation `R` with a stable path
to `standard 2` and no ordinary path. It is the negation of
`AC.StableTrivial.trivialProjection_rank_two_statement`
(`AcStableTrivial.lean:324-326`).

The Z/2 pair `counterA`, `counterB` (`AcStableProjection.lean:93,96`) is a
stable-only pair for a non-trivial presentation. It fails `PresentsTrivialGroup`;
this module states that failure and proves it. The rank-two trivial presentation
`BranchD2.candidate` has a stable certificate and an ordinary path. It is a
positive control, not a witness. The only concrete rank-two trivial presentation
in the corpus is `Ak3.ak3`; its ordinary unreachability is the open AK(3)
separation, not a theorem.
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace AC
namespace StableWitness

/-! ## 1. The witness predicate -/

/-- A stable path from `P` to the standard tuple at the same rank. -/
def StableReachToStandard (P : Presentation) : Prop :=
  StableReachable P ⟨P.1, standard P.1⟩

/-- The ordinary unreachability of the underlying presentation. -/
def NotOrdinaryReachable (P : Presentation) : Prop :=
  ¬ Reachable P.2 (standard P.1)

/-- A stable witness: positive rank, trivial presentation, stable path to the
standard tuple, and no ordinary path. -/
def IsStableWitness (P : Presentation) : Prop :=
  0 < P.1 ∧ PresentsTrivialGroup P.2 ∧
    StableReachToStandard P ∧ NotOrdinaryReachable P

/-- A stable certificate: the same data without the ordinary-unreachability
field. -/
def HasStableCertificate (P : Presentation) : Prop :=
  0 < P.1 ∧ PresentsTrivialGroup P.2 ∧ StableReachToStandard P

/-! ## 2. Field projections -/

theorem stableWitness_positive {P : Presentation} (h : IsStableWitness P) : 0 < P.1 :=
  h.1

theorem stableWitness_presents {P : Presentation} (h : IsStableWitness P) :
    PresentsTrivialGroup P.2 :=
  h.2.1

theorem stableWitness_stableReachable {P : Presentation} (h : IsStableWitness P) :
    StableReachToStandard P :=
  h.2.2.1

theorem stableWitness_notReachable {P : Presentation} (h : IsStableWitness P) :
    NotOrdinaryReachable P :=
  h.2.2.2

/-! ## 3. The witness is exactly the stable-certificate counterexample -/

theorem isStableWitness_iff_stableCertificateCounterexample :
    (∃ P : Presentation, IsStableWitness P) ↔
      StableTrivial.StableCertificateCounterexample := by
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨P.1, hP.1, P.2, hP.2.1, hP.2.2.1, hP.2.2.2⟩
  · rintro ⟨n, hn, R, hR, hs, hnot⟩
    exact ⟨⟨n, R⟩, hn, hR, hs, hnot⟩

/-- A stable witness is an ordinary counterexample. -/
theorem stableWitness_counterexample
    (h : ∃ P : Presentation, IsStableWitness P) : Counterexample :=
  StableTrivial.stableCertificateCounterexample_counterexample
    (isStableWitness_iff_stableCertificateCounterexample.mp h)

/-! ## 4. Rank one cannot carry a witness -/

theorem stableWitness_rank_ge_two {P : Presentation} (h : IsStableWitness P) :
    2 ≤ P.1 := by
  rcases P with ⟨n, R⟩
  change 2 ≤ n
  by_contra hlt
  have hn : n = 0 ∨ n = 1 := by omega
  rcases hn with rfl | rfl
  · exact Nat.not_lt_zero 0 h.1
  · exact h.2.2.2 (StableTrivial.reachable_standard_rank_one R h.2.1)

/-! ## 5. The Z/2 pair is not a trivial-presentation witness -/

/-- The element `ofAdd 1` in `Multiplicative (ZMod 2)` has order two. -/
theorem ofAdd_one_sq_zmod_two :
    (Multiplicative.ofAdd (1 : ZMod 2)) ^ 2 = 1 := by
  rw [pow_two, ← ofAdd_add]
  have h2 : (1 : ZMod 2) + 1 = 0 := by decide
  rw [h2, ofAdd_zero]

/-- `counterA = (x, y²)` presents `Z/2`, not the trivial group. -/
theorem counterA_not_presentsTrivialGroup :
    ¬ PresentsTrivialGroup StableProjection.counterA := by
  intro h
  let f : Fin 2 → Multiplicative (ZMod 2) :=
    fun i => if i = 0 then 1 else Multiplicative.ofAdd (1 : ZMod 2)
  have hf : ∀ r ∈ Set.range StableProjection.counterA, FreeGroup.lift f r = 1 := by
    rintro r ⟨i, rfl⟩
    fin_cases i
    · change FreeGroup.lift f (StableProjection.counterA 0) = 1
      simp [StableProjection.counterA, f]
    · change FreeGroup.lift f (StableProjection.counterA 1) = 1
      simp [StableProjection.counterA, f, ofAdd_one_sq_zmod_two]
  let g : PresentedGroup (Set.range StableProjection.counterA) →* Multiplicative (ZMod 2) :=
    PresentedGroup.toGroup (rels := Set.range StableProjection.counterA) (f := f) hf
  have hgen : g (PresentedGroup.of (1 : Fin 2)) = Multiplicative.ofAdd (1 : ZMod 2) := by
    rw [PresentedGroup.toGroup.of]
    simp [f]
  have hone : g (PresentedGroup.of (1 : Fin 2)) = 1 := by
    have : Subsingleton (PresentedGroup (Set.range StableProjection.counterA)) := h
    rw [Subsingleton.elim (PresentedGroup.of (1 : Fin 2)) 1, map_one]
  rw [hgen] at hone
  have hne : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by
    intro h
    have h0 : (1 : ZMod 2) = 0 := ofAdd_eq_one.mp h
    have h1 : (1 : ZMod 2) ≠ 0 := by decide
    exact h1 h0
  exact hne hone

/-- `counterB = (y, x²)` presents `Z/2`, not the trivial group. -/
theorem counterB_not_presentsTrivialGroup :
    ¬ PresentsTrivialGroup StableProjection.counterB := by
  intro h
  let f : Fin 2 → Multiplicative (ZMod 2) :=
    fun i => if i = 0 then Multiplicative.ofAdd (1 : ZMod 2) else 1
  have hf : ∀ r ∈ Set.range StableProjection.counterB, FreeGroup.lift f r = 1 := by
    rintro r ⟨i, rfl⟩
    fin_cases i
    · change FreeGroup.lift f (StableProjection.counterB 0) = 1
      simp [StableProjection.counterB, f]
    · change FreeGroup.lift f (StableProjection.counterB 1) = 1
      simp [StableProjection.counterB, f, ofAdd_one_sq_zmod_two]
  let g : PresentedGroup (Set.range StableProjection.counterB) →* Multiplicative (ZMod 2) :=
    PresentedGroup.toGroup (rels := Set.range StableProjection.counterB) (f := f) hf
  have hgen : g (PresentedGroup.of (0 : Fin 2)) = Multiplicative.ofAdd (1 : ZMod 2) := by
    rw [PresentedGroup.toGroup.of]
    simp [f]
  have hone : g (PresentedGroup.of (0 : Fin 2)) = 1 := by
    have : Subsingleton (PresentedGroup (Set.range StableProjection.counterB)) := h
    rw [Subsingleton.elim (PresentedGroup.of (0 : Fin 2)) 1, map_one]
  rw [hgen] at hone
  have hne : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by
    intro h
    have h0 : (1 : ZMod 2) = 0 := ofAdd_eq_one.mp h
    have h1 : (1 : ZMod 2) ≠ 0 := by decide
    exact h1 h0
  exact hne hone

theorem counterA_not_isStableWitness :
    ¬ IsStableWitness ⟨2, StableProjection.counterA⟩ := by
  intro h
  exact counterA_not_presentsTrivialGroup h.2.1

theorem counterB_not_isStableWitness :
    ¬ IsStableWitness ⟨2, StableProjection.counterB⟩ := by
  intro h
  exact counterB_not_presentsTrivialGroup h.2.1

/-! ## 6. The high-value witness remains a named target -/

/-- The rank-two trivial-presentation stable-only witness. -/
def StableWitnessStatement : Prop :=
  ∃ R : Relators 2, PresentsTrivialGroup R ∧
    StableReachable ⟨2, R⟩ ⟨2, standard 2⟩ ∧ ¬ Reachable R (standard 2)

end StableWitness
end AC

#check @AC.StableWitness.IsStableWitness
#check @AC.StableWitness.StableWitnessStatement
#check @AC.StableWitness.counterA_not_presentsTrivialGroup
#check @AC.StableWitness.counterB_not_presentsTrivialGroup
#print axioms AC.StableWitness.counterA_not_presentsTrivialGroup
#print axioms AC.StableWitness.counterB_not_presentsTrivialGroup
