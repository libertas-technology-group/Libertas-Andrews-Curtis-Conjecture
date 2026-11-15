module


public import AcA8TailMinimal
public import AcA8PivotReduction
public import AcA8CyclicBridge

@[expose] public section

/-!
# AcA8Assembly — conditional assembly of the A8 tail-minimal equation

This module assembles the zero-excess equation from the kernel-checked local
inputs. It takes the cyclic-Nielsen uniform pivot statement as a parameter and
proves `TailMinimalStatement` from it. The two branches are the zero-excess
pivot branch and the both-long branch.
-/

set_option autoImplicit false
namespace AC
namespace A8Assembly

open ProofAttempt Invariant A8TailMinimal

lemma expVec_mk_cons (p : Fin 2 × Bool) (L : List (Fin 2 × Bool)) :
    expVec (FreeGroup.mk (p :: L)) =
      (if p.2 then genVec p.1 else -genVec p.1) + expVec (FreeGroup.mk L) := by
  have h : FreeGroup.mk (p :: L) = FreeGroup.mk [p] * FreeGroup.mk L := by
    rw [show p :: L = [p] ++ L by rfl, FreeGroup.mul_mk]
  rw [h, expVec_mul, expVec_mk_singleton]

lemma expVec_eq_zero_of_avoids (g : Fin 2) (L : List (Fin 2 × Bool))
    (h : ∀ p ∈ L, p.1 ≠ g) : expVec (FreeGroup.mk L) g = 0 := by
  induction L with
  | nil =>
      change expVec (1 : Word 2) g = 0
      simp
  | cons p L ih =>
      rw [expVec_mk_cons]
      have hp : p.1 ≠ g := h p (by simp)
      have hL : ∀ q ∈ L, q.1 ≠ g := by
        intro q hq
        exact h q (by simp [hq])
      cases p with
      | mk pg pb =>
          have hzero : genVec pg g = 0 := by
            simp [genVec, Ne.symm hp]
          cases pb <;> simp [hzero, ih hL]

lemma expVec_word_eq_zero_of_avoids (g : Fin 2) (w : Word 2)
    (h : A8PivotReduction.Avoids g w) : expVec w g = 0 := by
  rw [← FreeGroup.mk_toWord (x := w)]
  exact expVec_eq_zero_of_avoids g w.toWord h

lemma pivot_nonpivot_signed (S T : Relators 2) (i j g : Fin 2)
    (hj : j ≠ i) (σ : Fin 2 → Fin 2) (hσ : Function.Bijective σ)
    (hg : g = σ i)
    (ε : Fin 2 → Bool) (hε : ∀ k, expVec (S k) = if ε k then genVec (σ k) else -genVec (σ k))
    (hExp : ∀ k, k ≠ i → ∀ m, m ≠ g → expVec (T k) m = expVec (S k) m)
    (hav : A8PivotReduction.Avoids g (T j)) :
    T j = FreeGroup.of (σ j) ∨ T j = (FreeGroup.of (σ j))⁻¹ := by
  have hσj : σ j ≠ g := by
    intro h
    apply hj
    apply hσ.injective
    exact h.trans hg
  have hvec : expVec (T j) = genVec (σ j) ∨ expVec (T j) = -genVec (σ j) := by
    have hfull : expVec (T j) = if ε j then genVec (σ j) else -genVec (σ j) := by
      funext m
      by_cases hm : m = g
      · rw [hm]
        have hzero := expVec_word_eq_zero_of_avoids g (T j) hav
        have hcoord : (if ε j then genVec (σ j) else -genVec (σ j)) g = 0 := by
          cases ε j <;> simp [genVec, Ne.symm hσj]
        rw [hzero, hcoord]
      · rw [hExp j hj m hm, hε j]
    cases hεj : ε j
    · right; simpa [hεj] using hfull
    · left; simpa [hεj] using hfull
  exact eq_signedGen_of_avoids_of_signedVec (T j) (σ j) g hσj hav hvec

end A8Assembly
end AC

namespace AC
namespace A8Assembly
open ProofAttempt Invariant A8TailMinimal

lemma pivot_signedPermutation (S T : Relators 2) (i g : Fin 2)
    (σ : Fin 2 → Fin 2) (hσ : Function.Bijective σ)
    (hg : g = σ i)
    (ε : Fin 2 → Bool) (hε : ∀ k, expVec (S k) = if ε k then genVec (σ k) else -genVec (σ k))
    (hT : A8PivotReduction.PivotReduced T i g)
    (hExp : ∀ j, j ≠ i → ∀ k, k ≠ g → expVec (T j) k = expVec (S j) k) :
    IsSignedPermutation T := by
  let ε' : Fin 2 → Bool := fun j => if T j = FreeGroup.of (σ j) then true else false
  refine ⟨σ, hσ, ε', ?_⟩
  intro j
  have hgen : T j = FreeGroup.of (σ j) ∨ T j = (FreeGroup.of (σ j))⁻¹ := by
    by_cases hj : j = i
    · subst hj
      simpa [hg] using hT.1
    · exact pivot_nonpivot_signed S T i j g hj σ hσ hg ε hε hExp (hT.2 j hj)
  by_cases hpos : T j = FreeGroup.of (σ j)
  · simp [ε', hpos]
  · have hneg : T j = (FreeGroup.of (σ j))⁻¹ := by
      rcases hgen with h | h
      · exact False.elim (hpos h)
      · exact h
    simp [ε', hneg]

end A8Assembly
end AC


namespace AC
namespace A8Assembly
open ProofAttempt Invariant A8TailMinimal

theorem tailMinimalStatement_of_uniformPivot
    (h : Nielsen.cyclicNielsen_uniform_pivot_statement) :
    TailMinimalStatement := by
  intro S hS hp hmin
  by_contra hsp
  have hpos : 0 < totalExcess S := by
    by_contra h
    have h0 : totalExcess S = 0 := by omega
    exact hsp (isSignedPermutation_of_totalExcess_zero S hS h0)
  have hcyc : ∀ i : Fin 2, FreeGroup.IsCyclicallyReduced (S i).toWord :=
    A8TailMinimal.cyclicallyReduced_of_minimal S hS hmin
  by_cases hzero : ∃ i : Fin 2, excessLength (S i) = 0
  · obtain ⟨i, hi0⟩ := hzero
    rcases hS with ⟨σ, hσ, ε, hε⟩
    let g : Fin 2 := σ i
    have hsig : S i = A8Reachability.signedGen g (ε i) :=
      eq_signedGen_of_excess_zero (S i) hi0 g (ε i) (hε i)
    have hpiv : S i = FreeGroup.of g ∨ S i = (FreeGroup.of g)⁻¹ := by
      cases hεi : ε i
      · right
        simpa [A8Reachability.signedGen, hεi] using hsig
      · left
        simpa [A8Reachability.signedGen, hεi] using hsig
    obtain ⟨T, hTred, hST, hExp⟩ :=
      A8PivotReduction.pivot_reduction_exists_exp S i g hpiv
    have hTsp : IsSignedPermutation T :=
      pivot_signedPermutation S T i g σ hσ rfl ε hε hTred hExp
    have hTzero : totalExcess T = 0 :=
      totalExcess_eq_zero_of_signedPermutation hTsp
    have hTab : IsAbelianTerminal T := by
      rcases hTsp with ⟨τ, hτ, δ, hδ⟩
      refine ⟨τ, hτ, δ, ?_⟩
      intro j
      cases hδj : δ j <;>
        simp [hδ j, hδj, genVec, expVec_inv, expVec_of_fin]
    have hle := hmin T hST hTab
    omega
  · rcases hS with ⟨σ, hσ, ε, hε⟩
    have hSabel : IsAbelianTerminal S := ⟨σ, hσ, ε, hε⟩
    have hnozero : ∀ i : Fin 2, excessLength (S i) ≠ 0 := by
      intro i hi
      exact hzero ⟨i, hi⟩
    have h5 : ∀ i : Fin 2, 5 ≤ (S i).toWord.length := by
      intro i
      have hposi : 0 < excessLength (S i) := Nat.pos_of_ne_zero (hnozero i)
      have heven : Even (excessLength (S i)) := excessLength_even S hSabel i
      have hge2 : 2 ≤ excessLength (S i) := by
        rcases heven with ⟨k, hk⟩
        omega
      have helen : excessLength (S i) = (S i).toWord.length - 1 :=
        excessLength_eq_length_sub_one_of_signed (S i) (σ i) (ε i) (hε i)
      have hge3 : 3 ≤ (S i).toWord.length := by omega
      have hne3 : (S i).toWord.length ≠ 3 := by
        intro h3
        rcases List.length_eq_three.mp h3 with ⟨a, b, c, hL⟩
        have hw : S i = FreeGroup.mk [a, b, c] := by
          rw [← FreeGroup.mk_toWord (x := S i), hL]
        have hcyc' : FreeGroup.IsCyclicallyReduced [a, b, c] := by
          simpa [hL] using hcyc i
        have hvec' : expVec (FreeGroup.mk [a, b, c]) =
            if ε i then genVec (σ i) else -genVec (σ i) := by
          rw [← hw]
          exact hε i
        exact no_cyc_len3 a b c (σ i) (ε i) hcyc' hvec'
      have hne4 : (S i).toWord.length ≠ 4 := by
        intro h4
        have he3 : excessLength (S i) = 3 := by
          rw [helen, h4]
        rw [he3] at heven
        rcases heven with ⟨k, hk⟩
        omega
      omega
    exact Nielsen.false_of_uniformPivot_and_minimal h S hSabel hp hcyc hsp (h5 0) (h5 1) hmin

end A8Assembly
end AC

#print axioms AC.A8Assembly.tailMinimalStatement_of_uniformPivot
