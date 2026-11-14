import AC
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.Set.Image
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic.Abel

/-!
# Candidate invariants for the Andrews–Curtis relation

This file carries the invariant branch of the proof attempt for `AC.Step`.

`expVec` is the exponent vector of a word and `expSpan` is the `ℤ`-span of the relator
exponent vectors. That span is the image of the exponent matrix, and the abelianisation of
the presented group is `ℤⁿ` modulo it. `step_expSpan` proves that every official step
preserves the span, and `reachable_expSpan` lifts the statement to `AC.Reachable`.

Two further results frame the branch. `not_reachable_of_expSpan_ne` turns a difference of
invariant values into a negative reachability statement, and `counterexample_of_expSpan_ne`
turns it into a counterexample. `no_strictly_decreasing_measure` shows that no `ℕ`-valued
function decreases on every official step, because inversion is a two-cycle; the
decreasing-measure branch is empty.

The elimination of the invariant branch rests on `expSpan_eq_top_of_presents` (gap G1):
the span is the whole space for every presentation of the trivial group. That theorem is
closed here. The argument reads the abelianisation of the presented group: `expHom` is the
projection of the free group onto `ℤⁿ` with kernel the commutator subgroup, so its
composite with the quotient map `ℤⁿ → ℤⁿ ⧸ expSpan R` kills every relator and factors
through the presented group. A subsingleton presented group therefore forces every
generator to die in the quotient, so every `genVec i` lies in `expSpan R`, and `genVec` is
the standard basis `Pi.basisFun`. The conditional forms `span_eq_standard_of_presents` and
`no_span_separation` state the consequence the branch needs.

Declarations that carry no `sorry`: `expVec_one`, `expVec_mul`, `expVec_inv`,
`expVec_conj`, `expVec_mem_expSpan`, `expSpan_le_of_forall`, `expSpan_eq_of_forall`,
`expSpan_inv`, `expSpan_mulRight`, `expSpan_conj`, `step_expSpan`, `reachable_expSpan`,
`not_reachable_of_expSpan_ne`, `not_reachable_standard_of_expSpan_ne`,
`counterexample_of_expSpan_ne`, `expSpan_eq_top_of_presents`, `expSpan_eq_of_presents`,
`no_span_separation`, `span_eq_standard_of_presents`,
`no_strictly_decreasing_measure`.

Axiom check for the fresh reader, on the pinned toolchain:

    #print axioms AC.Invariant.step_expSpan
    #print axioms AC.Invariant.expSpan_eq_top_of_presents
    #print axioms AC.Invariant.expSpan_eq_of_presents
    #print axioms AC.Invariant.no_strictly_decreasing_measure

Each must report an axiom set inside `[propext, Classical.choice, Quot.sound]`. A listing
that contains `sorryAx`, or any axiom outside that set, is a defect.
-/

namespace AC
namespace Invariant

variable {n : ℕ}

/-! ## 1. The exponent vector -/

/-- The vector with value `1` at `i` and value `0` elsewhere. -/
def genVec (i : Fin n) : Fin n → ℤ := Pi.single i 1

/-- The exponent-sum homomorphism from the free group on `n` generators to `ℤⁿ`,
written multiplicatively. -/
noncomputable def expHom (n : ℕ) : Word n →* Multiplicative (Fin n → ℤ) :=
  FreeGroup.lift fun i => Multiplicative.ofAdd (genVec i)

/-- The exponent vector of a word: the vector of its letter counts. -/
noncomputable def expVec (w : Word n) : Fin n → ℤ :=
  Multiplicative.toAdd (expHom n w)

@[simp] theorem expVec_one : expVec (1 : Word n) = 0 := by
  simp [expVec]

theorem expVec_mul {u v : Word n} : expVec (u * v) = expVec u + expVec v := by
  simp [expVec, map_mul]

theorem expVec_inv {w : Word n} : expVec w⁻¹ = -expVec w := by
  have h : expVec w + expVec w⁻¹ = 0 := by
    rw [← expVec_mul, mul_inv_cancel, expVec_one]
  exact eq_neg_of_add_eq_zero_right h

theorem expVec_conj {r w : Word n} : expVec (w * r * w⁻¹) = expVec r := by
  rw [expVec_mul, expVec_mul, expVec_inv]
  abel

/-! ## 2. The span invariant -/

/-- The `ℤ`-span of the relator exponent vectors. -/
noncomputable def expSpan (R : Relators n) : Submodule ℤ (Fin n → ℤ) :=
  Submodule.span ℤ (Set.range fun i => expVec (R i))

theorem expVec_mem_expSpan (R : Relators n) (j : Fin n) : expVec (R j) ∈ expSpan R :=
  Submodule.subset_span ⟨j, rfl⟩

theorem expSpan_le_of_forall {R S : Relators n}
    (h : ∀ j, expVec (S j) ∈ expSpan R) : expSpan S ≤ expSpan R :=
  Submodule.span_le.mpr (Set.range_subset_iff.mpr h)

theorem expSpan_eq_of_forall {R S : Relators n}
    (h1 : ∀ j, expVec (S j) ∈ expSpan R) (h2 : ∀ j, expVec (R j) ∈ expSpan S) :
    expSpan S = expSpan R :=
  le_antisymm (expSpan_le_of_forall h1) (expSpan_le_of_forall h2)

/-! ## 3. The three moves preserve the span -/

theorem expSpan_inv (R : Relators n) (i : Fin n) :
    expSpan (Function.update R i (R i)⁻¹) = expSpan R := by
  apply expSpan_eq_of_forall
  · intro j
    by_cases hj : j = i
    · rw [hj]
      rw [Function.update_self, expVec_inv]
      exact (expSpan R).neg_mem (expVec_mem_expSpan R i)
    · rw [Function.update_of_ne hj]
      exact expVec_mem_expSpan R j
  · intro j
    by_cases hj : j = i
    · rw [hj]
      have h : expVec (R i) = -expVec ((Function.update R i (R i)⁻¹) i) := by
        rw [Function.update_self, expVec_inv, neg_neg]
      rw [h]
      exact (expSpan (Function.update R i (R i)⁻¹)).neg_mem
        (expVec_mem_expSpan (Function.update R i (R i)⁻¹) i)
    · rw [← Function.update_of_ne (f := R) (a := j) (a' := i) hj]
      exact expVec_mem_expSpan (Function.update R i (R i)⁻¹) j

theorem expSpan_mulRight (R : Relators n) (i j : Fin n) (hij : i ≠ j) :
    expSpan (Function.update R i (R i * R j)) = expSpan R := by
  apply expSpan_eq_of_forall
  · intro k
    by_cases hk : k = i
    · rw [hk]
      rw [Function.update_self, expVec_mul]
      exact (expSpan R).add_mem (expVec_mem_expSpan R i) (expVec_mem_expSpan R j)
    · rw [Function.update_of_ne hk]
      exact expVec_mem_expSpan R k
  · intro k
    by_cases hk : k = i
    · rw [hk]
      have hSj : Function.update R i (R i * R j) j = R j :=
        Function.update_of_ne (Ne.symm hij) (R i * R j) R
      have h : expVec (R i) =
          expVec ((Function.update R i (R i * R j)) i) -
            expVec ((Function.update R i (R i * R j)) j) := by
        rw [Function.update_self, hSj, expVec_mul]
        abel
      rw [h]
      exact (expSpan (Function.update R i (R i * R j))).sub_mem
        (expVec_mem_expSpan (Function.update R i (R i * R j)) i)
        (expVec_mem_expSpan (Function.update R i (R i * R j)) j)
    · rw [← Function.update_of_ne (f := R) (a := k) (a' := i) hk]
      exact expVec_mem_expSpan (Function.update R i (R i * R j)) k

theorem expSpan_conj (R : Relators n) (i : Fin n) (w : Word n) :
    expSpan (Function.update R i (w * R i * w⁻¹)) = expSpan R := by
  apply expSpan_eq_of_forall
  · intro k
    by_cases hk : k = i
    · rw [hk]
      rw [Function.update_self, expVec_conj]
      exact expVec_mem_expSpan R i
    · rw [Function.update_of_ne hk]
      exact expVec_mem_expSpan R k
  · intro k
    by_cases hk : k = i
    · rw [hk]
      have h : expVec (R i) = expVec ((Function.update R i (w * R i * w⁻¹)) i) := by
        rw [Function.update_self, expVec_conj]
      rw [h]
      exact expVec_mem_expSpan (Function.update R i (w * R i * w⁻¹)) i
    · rw [← Function.update_of_ne (f := R) (a := k) (a' := i) hk]
      exact expVec_mem_expSpan (Function.update R i (w * R i * w⁻¹)) k

/-- Every official step preserves the span of the relator exponent vectors. -/
theorem step_expSpan {R S : Relators n} (h : Step R S) : expSpan S = expSpan R := by
  cases h with
  | inv i => exact expSpan_inv _ i
  | mulRight i j hij => exact expSpan_mulRight _ i j hij
  | conj i w => exact expSpan_conj _ i w

/-- Every finite sequence of official steps preserves the span. -/
theorem reachable_expSpan {R S : Relators n} (h : Reachable R S) :
    expSpan S = expSpan R := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact (step_expSpan hstep).trans ih

/-! ## 4. Separation: a span difference refutes reachability -/

theorem not_reachable_of_expSpan_ne {R S : Relators n}
    (h : expSpan R ≠ expSpan S) : ¬ Reachable R S := by
  intro hR
  exact h (reachable_expSpan hR).symm

theorem not_reachable_standard_of_expSpan_ne {R : Relators n}
    (h : expSpan R ≠ expSpan (standard n)) : ¬ Reachable R (standard n) :=
  not_reachable_of_expSpan_ne h

theorem counterexample_of_expSpan_ne {R : Relators n} (hR : PresentsTrivialGroup R)
    (h : expSpan R ≠ expSpan (standard n)) : IsCounterexample R :=
  ⟨hR, not_reachable_standard_of_expSpan_ne h⟩

/-! ## 5. The decreasing-measure branch is empty

`Step` contains the two-cycle `R → update R i (R i)⁻¹ → R`. A strict decrease on both
edges of a cycle cannot exist in `ℕ`, so no `ℕ`-valued measure decreases on every step.
-/

/-- No `ℕ`-valued function decreases on every official step at positive rank. -/
theorem no_strictly_decreasing_measure {n : ℕ} (hn : 0 < n) (μ : Relators n → ℕ) :
    ¬ ∀ R S : Relators n, Step R S → μ S < μ R := by
  intro h
  let i : Fin n := ⟨0, hn⟩
  let R : Relators n := standard n
  let S : Relators n := Function.update R i (R i)⁻¹
  have hSR : Function.update S i (S i)⁻¹ = R := by
    funext j
    by_cases hj : j = i
    · rw [hj]
      simp [S]
    · rw [Function.update_of_ne hj]
      exact Function.update_of_ne hj (R i)⁻¹ R
  have h1 : μ S < μ R := h R S (Step.inv R i)
  have h2 : μ R < μ S := h S R (by rw [← hSR]; exact Step.inv S i)
  exact not_lt_of_ge (le_of_lt h1) h2

/-! ## 6. The elimination of the span branch

The span is the abelianisation. For a presentation of the trivial group the abelianisation
is trivial, so the span is the whole space (`expSpan_eq_top_of_presents`, gap G1, closed).
Hence two trivial presentations carry the same span, the separation hypothesis of section 4
is unsatisfiable, and the span carries no counterexample.
-/

/-- G1, closed.

The span is `⊤` for every presentation of the trivial group. The quotient map
`ℤⁿ → ℤⁿ ⧸ expSpan R` kills every relator exponent vector, so it composes with the
exponent homomorphism to a homomorphism out of the presented group. Triviality of that
group forces each generator to die, hence each `genVec i` lies in `expSpan R`. -/
theorem expSpan_eq_top_of_presents {R : Relators n} (h : PresentsTrivialGroup R) :
    expSpan R = ⊤ := by
  classical
  /- The quotient map `ℤⁿ → ℤⁿ ⧸ expSpan R`, bundled as a monoid homomorphism on
  `Multiplicative`. It sends `v` to the class of `v`. -/
  let quoHom : Multiplicative (Fin n → ℤ) →*
      Multiplicative ((Fin n → ℤ) ⧸ expSpan R) :=
    { toFun := fun v => Multiplicative.ofAdd (Submodule.Quotient.mk v.toAdd)
      map_one' := by simp
      map_mul' := by
        intro a b
        simp [toAdd_mul, ofAdd_add] }
  /- The generator map into the quotient. A relator dies because its exponent vector is
  in the span by construction. -/
  let f : Fin n → Multiplicative ((Fin n → ℤ) ⧸ expSpan R) :=
    fun i => Multiplicative.ofAdd (Submodule.Quotient.mk (genVec i))
  have hkill : ∀ r ∈ Set.range R, FreeGroup.lift f r = 1 := by
    rintro r ⟨j, rfl⟩
    have hcomp : (quoHom.comp (expHom n)) (R j) = FreeGroup.lift f (R j) :=
      FreeGroup.lift_unique (f := f) (quoHom.comp (expHom n))
        (fun i => by simp [f, quoHom, expHom])
    rw [← hcomp]
    show Multiplicative.ofAdd (Submodule.Quotient.mk (expVec (R j))) = 1
    have hzero : (Submodule.Quotient.mk (expVec (R j)) : (Fin n → ℤ) ⧸ expSpan R) = 0 := by
      rw [Submodule.Quotient.mk_eq_zero]
      exact expVec_mem_expSpan R j
    rw [hzero]
    simp
  let φ : PresentedGroup (Set.range R) →*
      Multiplicative ((Fin n → ℤ) ⧸ expSpan R) :=
    PresentedGroup.toGroup (f := f) (rels := Set.range R) hkill
  have hgen : ∀ i : Fin n, genVec i ∈ expSpan R := by
    intro i
    haveI : Subsingleton (PresentedGroup (Set.range R)) := h
    have h1 : φ (PresentedGroup.of i) = 1 := by
      rw [show PresentedGroup.of i = (1 : PresentedGroup (Set.range R)) from
        Subsingleton.elim _ _]
      simp
    have h2 : f i = 1 := by
      rw [← PresentedGroup.toGroup.of (f := f) (rels := Set.range R) hkill]
      exact h1
    have h3 : Submodule.Quotient.mk (genVec i) = (0 : (Fin n → ℤ) ⧸ expSpan R) := by
      simpa [f] using h2
    rw [Submodule.Quotient.mk_eq_zero] at h3
    exact h3
  have hbasis : Submodule.span ℤ (Set.range (fun i : Fin n => genVec i)) = ⊤ := by
    have hfun : (fun i : Fin n => genVec i) = ⇑(Pi.basisFun ℤ (Fin n)) := by
      funext i
      simp [genVec, Pi.basisFun_apply]
    rw [hfun]
    exact (Pi.basisFun ℤ (Fin n)).span_eq
  rw [eq_top_iff]
  calc ⊤ = Submodule.span ℤ (Set.range (fun i : Fin n => genVec i)) := hbasis.symm
    _ ≤ expSpan R := Submodule.span_le.mpr (Set.range_subset_iff.mpr hgen)

/-- Two presentations of the trivial group carry the same span. This is the unconditional
form, and it rests on the closed gap G1. -/
theorem expSpan_eq_of_presents {R S : Relators n}
    (hR : PresentsTrivialGroup R) (hS : PresentsTrivialGroup S) :
    expSpan R = expSpan S := by
  rw [expSpan_eq_top_of_presents hR, expSpan_eq_top_of_presents hS]

/-- Conditional elimination, with gap G1 supplied as a hypothesis. The span of a trivial
presentation equals the span of the standard tuple, so the separation of section 4 never
fires. -/
theorem span_eq_standard_of_presents {R : Relators n}
    (hspan : ∀ T : Relators n, PresentsTrivialGroup T → expSpan T = ⊤)
    (hstd : PresentsTrivialGroup (standard n)) (hR : PresentsTrivialGroup R) :
    expSpan R = expSpan (standard n) := by
  rw [hspan R hR, hspan (standard n) hstd]

/-- The separation hypothesis of section 4 is inconsistent with gap G1. -/
theorem no_span_separation {R : Relators n}
    (hspan : ∀ T : Relators n, PresentsTrivialGroup T → expSpan T = ⊤)
    (hstd : PresentsTrivialGroup (standard n)) (hR : PresentsTrivialGroup R) :
    ¬ (expSpan R ≠ expSpan (standard n)) := by
  intro h
  exact h (span_eq_standard_of_presents hspan hstd hR)

end Invariant
end AC
