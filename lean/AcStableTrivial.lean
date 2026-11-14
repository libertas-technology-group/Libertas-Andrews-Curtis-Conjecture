import AC
import AcInduction
import AcInvariant
import AcStableProjection
import BranchD
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic

/-!
# The trivial-presentation stable projection

`AC.StableConjecture` (`AC.lean:106-112`) permits a stable path to insert and
delete isolated generator–relator pairs, so the rank may leave `n` and return.
`AC.BranchD.StableImpliesOrdinary` (`BranchD.lean:255-257`) is the projection
principle: a stable solution at the rank of a trivial presentation yields an
ordinary solution at that rank.

This file names that statement `TrivialProjection` and proves the exact
reductions around it.

## Results

1. `trivialProjection_iff_stableImpliesOrdinary` records that the new name is
   definitionally `AC.BranchD.StableImpliesOrdinary`.
2. `conjecture_implies_trivialProjection` is the easy direction: the ordinary
   conjecture proves the projection.
3. `conjecture_iff_stableConjecture_and_trivialProjection` is the accounting
   `AC.BranchD.conjecture_iff_stable_and_projection` in the new name. Granted
   the separate stable conjecture, the trivial projection is exactly ordinary
   AC.
4. `not_trivialProjection_iff_stableCertificateCounterexample` characterises a
   failure of the projection as a trivial presentation with a stable certificate
   and no ordinary path. `stableCertificateCounterexample_counterexample` turns
   such a failure into `AC.Counterexample`.
5. The rank-one case is closed outright, without using the stable hypothesis:
   `reachable_standard_rank_one`. The proof reads the exponent invariant
   `AC.Invariant.expSpan_eq_top_of_presents`, which forces the single relator to
   have exponent `±1`, and the rank-one free group is infinite cyclic
   (`FreeGroup.equivIntOfUnique`), so the relator is `x` or `x⁻¹`; inversion
   finishes. `trivialProjection_at_one` is the projection instance.
6. `trivialProjection_iff_aboveOne` reduces the open statement to ranks at
   least two. `TrivialProjectionAboveOne` is the exact residual goal.
7. `trivialProjection_rank_two_of_rankTwoA8` reduces the rank-two statement to
   the rank-two A8 input: every rank-two abelian-terminal trivial presentation
   ordinarily reaches a signed permutation. The stable hypothesis is not read,
   so the theorem is a reduction and not a proof of the statement.

## Status

The trivial-presentation projection is open. `TrivialProjection` and
`TrivialProjectionAboveOne` are `def`s, exactly as `StableImpliesOrdinary` is a
`def`; no proof is asserted. The general one-stabilization projection is not
open: `AC.StableProjection.one_stabilization_projection_refuted` refutes it with
the pair `counterA = (x, y²)` and `counterB = (y, x²)`, which presents `ℤ/2`.
That refutation does not touch the trivial-presentation case.

Every declaration in this file is closed. There is no `sorry`, no `admit`, no
`native_decide`, and no user axiom.

A stable-only trivial-group witness would be a trivial `R` with a stable path to
standard and no ordinary path. By `stableCertificateCounterexample_counterexample`
that is an ordinary counterexample, so exhibiting one would disprove the
Andrews–Curtis conjecture. No such witness is available in this corpus.

The rank-two statement is open. `trivialProjection_rank_two_of_rankTwoA8` shows
that the rank-two A8 input closes it, and `AC.Final.conjecture_iff_A8` records
that A8 is the open AC input. The direct erasure route does not close: the
unrestricted one-stabilization projection is refuted at rank two by
`AC.StableProjection.one_stabilization_projection_refuted`, so an erasure lemma
for the trivial case has to use the triviality hypothesis, and no closed lemma
of that form exists in this corpus.

## Axiom record

A fresh reader runs, on the pinned toolchain:

    #print axioms AC.StableTrivial.trivialProjection_iff_stableImpliesOrdinary
    #print axioms AC.StableTrivial.conjecture_implies_trivialProjection
    #print axioms AC.StableTrivial.conjecture_iff_stableConjecture_and_trivialProjection
    #print axioms AC.StableTrivial.not_trivialProjection_iff_stableCertificateCounterexample
    #print axioms AC.StableTrivial.stableCertificateCounterexample_counterexample
    #print axioms AC.StableTrivial.equivIntOfUnique_mul
    #print axioms AC.StableTrivial.equivIntOfUnique_inv
    #print axioms AC.StableTrivial.expVec_zero_eq_equivInt
    #print axioms AC.StableTrivial.expSpan_rank_one_eq
    #print axioms AC.StableTrivial.eq_pm_genVec_of_mem_span
    #print axioms AC.StableTrivial.expVec_rank_one_eq_of_presents
    #print axioms AC.StableTrivial.word_eq_of_expVec
    #print axioms AC.StableTrivial.word_eq_inv_of_expVec
    #print axioms AC.StableTrivial.reachable_standard_rank_one
    #print axioms AC.StableTrivial.trivialProjection_at_one
    #print axioms AC.StableTrivial.trivialProjection_iff_aboveOne
    #print axioms AC.StableTrivial.trivialProjection_rank_two_of_rankTwoA8

Each must report an axiom set inside `[propext, Classical.choice, Quot.sound]`.
The writer of this file is not its verifier.
-/

set_option autoImplicit false

namespace AC
namespace StableTrivial

/-! ## 1. The trivial-presentation projection -/

/-- The trivial-presentation projection: a stable path from a trivial
presentation to the standard tuple at the same positive rank yields an ordinary
`Reachable` path. This is the body of `AC.BranchD.StableImpliesOrdinary`. -/
def TrivialProjection : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ R : Relators n, PresentsTrivialGroup R →
    StableReachable ⟨n, R⟩ ⟨n, standard n⟩ → Reachable R (standard n)

/-- The new name and the corpus name denote the same statement. -/
theorem trivialProjection_iff_stableImpliesOrdinary :
    TrivialProjection ↔ BranchD.StableImpliesOrdinary :=
  Iff.rfl

/-- The ordinary conjecture implies the projection: its conclusion is the
ordinary path the projection asks for. -/
theorem conjecture_implies_trivialProjection (h : Conjecture) : TrivialProjection :=
  fun n hn R hR _ => h n hn R hR

/-- Ordinary AC is equivalent to stable AC together with the trivial
projection. This is `AC.BranchD.conjecture_iff_stable_and_projection` under the
name `TrivialProjection`. -/
theorem conjecture_iff_stableConjecture_and_trivialProjection :
    Conjecture ↔ StableConjecture ∧ TrivialProjection :=
  BranchD.conjecture_iff_stable_and_projection

/-! ## 2. The failure mode -/

/-- A stable-certificate ordinary counterexample: a trivial presentation that
stable-reaches the standard tuple at its own rank, and does not ordinarily reach
it. This is precisely a failure of the trivial projection. -/
def StableCertificateCounterexample : Prop :=
  ∃ (n : ℕ), 0 < n ∧ ∃ R : Relators n,
    PresentsTrivialGroup R ∧ StableReachable ⟨n, R⟩ ⟨n, standard n⟩ ∧
      ¬ Reachable R (standard n)

/-- The trivial projection fails exactly when a stable-certificate ordinary
counterexample exists. -/
theorem not_trivialProjection_iff_stableCertificateCounterexample :
    ¬ TrivialProjection ↔ StableCertificateCounterexample := by
  classical
  constructor
  · intro h
    by_contra hc
    apply h
    intro n hn R hR hs
    by_contra hnot
    exact hc ⟨n, hn, R, hR, hs, hnot⟩
  · rintro ⟨n, hn, R, hR, hs, hnot⟩ hproj
    exact hnot (hproj n hn R hR hs)

/-- A stable-certificate ordinary counterexample is an ordinary counterexample,
so a failure of the projection would refute `AC.Conjecture`. -/
theorem stableCertificateCounterexample_counterexample
    (h : StableCertificateCounterexample) : Counterexample := by
  obtain ⟨n, hn, R, hR, _, hnot⟩ := h
  exact ⟨n, hn, R, hR, hnot⟩

/-! ## 3. Rank one: the exponent sum and the cyclic classification -/

/-- `FreeGroup.equivIntOfUnique` is additive on the rank-one free group. -/
theorem equivIntOfUnique_mul (x y : FreeGroup (Fin 1)) :
    FreeGroup.equivIntOfUnique (x * y) =
      FreeGroup.equivIntOfUnique x + FreeGroup.equivIntOfUnique y := by
  simp [FreeGroup.equivIntOfUnique, FreeGroup.sum.map_mul]

/-- `FreeGroup.equivIntOfUnique` sends an inverse to the negative. -/
theorem equivIntOfUnique_inv (x : FreeGroup (Fin 1)) :
    FreeGroup.equivIntOfUnique x⁻¹ = - FreeGroup.equivIntOfUnique x := by
  have h : FreeGroup.equivIntOfUnique x + FreeGroup.equivIntOfUnique x⁻¹ = 0 := by
    rw [← equivIntOfUnique_mul, mul_inv_cancel]
    simp [FreeGroup.equivIntOfUnique]
  exact eq_neg_of_add_eq_zero_right h

/-- On the rank-one free group the single exponent-sum coordinate is
`FreeGroup.equivIntOfUnique`. -/
theorem expVec_zero_eq_equivInt (w : Word 1) :
    (Invariant.expVec w) 0 = FreeGroup.equivIntOfUnique w := by
  induction w using FreeGroup.induction_on with
  | C1 => simp [Invariant.expVec, Invariant.expHom, FreeGroup.equivIntOfUnique]
  | of i =>
      fin_cases i
      simp [Invariant.expVec, Invariant.expHom, Invariant.genVec, FreeGroup.equivIntOfUnique]
  | inv_of i ih =>
      rw [Invariant.expVec_inv, equivIntOfUnique_inv]
      simp only [Pi.neg_apply]
      rw [ih]
  | mul x y ihx ihy =>
      rw [Invariant.expVec_mul, equivIntOfUnique_mul]
      simp only [Pi.add_apply]
      rw [ihx, ihy]

/-- At rank one the exponent span is the span of the single relator exponent
vector. -/
theorem expSpan_rank_one_eq (R : Relators 1) :
    Invariant.expSpan R =
      Submodule.span ℤ ({Invariant.expVec (R 0)} : Set (Fin 1 → ℤ)) := by
  rw [Invariant.expSpan]
  have hconst : (fun i : Fin 1 => Invariant.expVec (R i)) =
      fun _ => Invariant.expVec (R 0) := by
    funext i
    rw [Subsingleton.elim i 0]
  rw [hconst, Set.range_const]

/-- A single vector whose span contains the first basis vector of `ℤ¹` is that
basis vector or its negative. -/
theorem eq_pm_genVec_of_mem_span {v : Fin 1 → ℤ}
    (h : Invariant.genVec (0 : Fin 1) ∈
      Submodule.span ℤ ({v} : Set (Fin 1 → ℤ))) :
    v = Invariant.genVec 0 ∨ v = - Invariant.genVec 0 := by
  rw [Submodule.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  have h0 := congrFun hc 0
  simp only [Pi.smul_apply, Invariant.genVec, Pi.single_eq_same, smul_eq_mul] at h0
  obtain ⟨hc1, _⟩ | ⟨hc1, _⟩ := Int.eq_one_or_neg_one_of_mul_eq_one' h0
  · left
    rw [← hc, hc1, one_smul]
  · right
    rw [hc1, neg_one_smul] at hc
    have := congrArg Neg.neg hc
    simpa using this

/-- A trivial rank-one presentation has relator exponent vector `±e₀`. -/
theorem expVec_rank_one_eq_of_presents {R : Relators 1}
    (hR : PresentsTrivialGroup R) :
    Invariant.expVec (R 0) = Invariant.genVec 0 ∨
      Invariant.expVec (R 0) = - Invariant.genVec 0 := by
  have htop : Invariant.expSpan R = ⊤ := Invariant.expSpan_eq_top_of_presents hR
  have hmem : Invariant.genVec (0 : Fin 1) ∈ Invariant.expSpan R := by
    rw [htop]
    exact Submodule.mem_top
  rw [expSpan_rank_one_eq] at hmem
  exact eq_pm_genVec_of_mem_span hmem

/-- A rank-one word of exponent vector `e₀` is the generator. -/
theorem word_eq_of_expVec {w : Word 1}
    (h : Invariant.expVec w = Invariant.genVec 0) : w = FreeGroup.of 0 := by
  have h0 : (Invariant.expVec w) 0 = 1 := by
    rw [h]
    simp [Invariant.genVec]
  have he : FreeGroup.equivIntOfUnique w = 1 := by
    rw [← expVec_zero_eq_equivInt]
    exact h0
  have hl : FreeGroup.equivIntOfUnique.symm 1 = w := by
    simpa [he] using FreeGroup.equivIntOfUnique.left_inv w
  rw [← hl]
  simp [FreeGroup.equivIntOfUnique]

/-- A rank-one word of exponent vector `-e₀` is the inverse generator. -/
theorem word_eq_inv_of_expVec {w : Word 1}
    (h : Invariant.expVec w = - Invariant.genVec 0) :
    w = (FreeGroup.of 0)⁻¹ := by
  have h0 : (Invariant.expVec w) 0 = -1 := by
    rw [h]
    simp [Invariant.genVec]
  have he : FreeGroup.equivIntOfUnique w = -1 := by
    rw [← expVec_zero_eq_equivInt]
    exact h0
  have hl : FreeGroup.equivIntOfUnique.symm (-1) = w := by
    simpa [he] using FreeGroup.equivIntOfUnique.left_inv w
  rw [← hl]
  simp [FreeGroup.equivIntOfUnique]

/-- Every trivial rank-one presentation is ordinarily reachable to the standard
tuple. The stable hypothesis is not used. -/
theorem reachable_standard_rank_one (R : Relators 1)
    (hR : PresentsTrivialGroup R) : Reachable R (standard 1) := by
  rcases expVec_rank_one_eq_of_presents hR with h | h
  · have hw : R 0 = FreeGroup.of 0 := word_eq_of_expVec h
    have hstd : R = standard 1 := by
      funext j
      fin_cases j
      simpa [standard] using hw
    rw [hstd]
    exact Relation.ReflTransGen.refl
  · have hw : R 0 = (FreeGroup.of 0)⁻¹ := word_eq_inv_of_expVec h
    have hstep : Step R (standard 1) := by
      have hs := Step.inv R 0
      rw [hw] at hs
      have hupd : Function.update R 0 ((FreeGroup.of 0)⁻¹)⁻¹ = standard 1 := by
        funext j
        fin_cases j
        simp [standard]
      rwa [hupd] at hs
    exact Relation.ReflTransGen.single hstep

/-- The trivial projection holds at rank one. -/
theorem trivialProjection_at_one (R : Relators 1) (hR : PresentsTrivialGroup R)
    (_hstable : StableReachable ⟨1, R⟩ ⟨1, standard 1⟩) :
    Reachable R (standard 1) :=
  reachable_standard_rank_one R hR

/-! ## 4. The exact residual goal -/

/-- The trivial projection at ranks at least two. The rank-one case is
`trivialProjection_at_one`, so this is the exact open statement. -/
def TrivialProjectionAboveOne : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ R : Relators n, PresentsTrivialGroup R →
    StableReachable ⟨n, R⟩ ⟨n, standard n⟩ → Reachable R (standard n)

/-- The trivial projection is equivalent to its open part above rank one,
because rank one is closed. -/
theorem trivialProjection_iff_aboveOne :
    TrivialProjection ↔ TrivialProjectionAboveOne := by
  constructor
  · intro h n hn R hR hs
    exact h n (by omega) R hR hs
  · intro h n hn R hR hs
    rcases n with _ | n
    · omega
    · rcases n with _ | k
      · exact trivialProjection_at_one R hR hs
      · exact h (k + 2) (by omega) R hR hs

/-- The rank-two instance of `TrivialProjectionAboveOne`, written as a `Prop`:
every rank-two trivial presentation that stably reaches the standard tuple at
rank two ordinarily reaches it. This is the exact statement of
`PROBE_STATEMENTS.md`. The definition carries no proof; the theorem below
reduces it to the rank-two A8 input. -/
def trivialProjection_rank_two_statement : Prop :=
  ∀ (R : Relators 2), PresentsTrivialGroup R →
    StableReachable ⟨2, R⟩ ⟨2, standard 2⟩ → Reachable R (standard 2)

/-- The rank-two statement follows from the rank-two A8 input: every
abelian-terminal rank-two trivial presentation ordinarily reaches a signed
permutation. The proof runs the rank-two A7 normalization and the signed
permutation canonicalisation, and it does not read the stable hypothesis. This
is a reduction to the open input, not a proof of the statement. -/
theorem trivialProjection_rank_two_of_rankTwoA8
    (h8 : ∀ S : Relators 2, PresentsTrivialGroup S → Induction.IsAbelianTerminal S →
      ∃ T : Relators 2, ProofAttempt.IsSignedPermutation T ∧ Reachable S T) :
    trivialProjection_rank_two_statement := by
  intro R hR _
  exact Induction.conjecture_rankTwo_of_abelianTerminal h8 R hR

end StableTrivial
end AC
