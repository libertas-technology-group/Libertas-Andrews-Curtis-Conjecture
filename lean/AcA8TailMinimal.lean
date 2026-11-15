module

public import AC
public import AcProof
public import AcInvariant
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.FinCases
public import AcA8Reachability

@[expose] public section

/-!
# AcA8TailMinimal — the rank-two commutator-tail interface

This module restates the rank-two tail metric from `BranchA2` in the buildable
corpus and proves the well-ordering step that supplies a tail-minimal
abelian-terminal state.  It then reduces the rank-two A8 statement to the named
tail-minimal theorem.  The tail-minimal theorem itself remains the open core.
-/

set_option autoImplicit false

namespace FreeGroup

lemma Red.Step.even_length {α : Type*} {L M : List (α × Bool)}
    (h : Red.Step L M) : Even M.length ↔ Even L.length := by
  have hlen : M.length + 2 = L.length := Red.Step.length h
  have h2 : Even (2 : ℕ) := ⟨1, rfl⟩
  rw [← hlen, Nat.even_add]
  simp [h2]

lemma Red.even_length {α : Type*} {L M : List (α × Bool)}
    (h : Red L M) : Even L.length ↔ Even M.length := by
  induction h with
  | refl => rfl
  | tail h1 h2 ih =>
      exact ih.trans (Red.Step.even_length h2).symm

lemma reduce_even_length {α : Type*} [DecidableEq α] (L : List (α × Bool)) :
    Even (reduce L).length ↔ Even L.length :=
  (Red.even_length reduce.red).symm

/-- A reduced list whose letters all carry the same generator has one sign throughout. -/
lemma IsReduced.exists_sign_of_forall_fst_eq {α : Type*} {g : α} {L : List (α × Bool)}
    (hred : IsReduced L) (hgen : ∀ p ∈ L, p.1 = g) :
    ∃ s : Bool, ∀ p ∈ L, p.2 = s := by
  induction L using List.twoStepInduction with
  | nil => exact ⟨true, by simp⟩
  | singleton a =>
      exact ⟨a.2, by intro p hp; rw [List.mem_singleton] at hp; subst hp; rfl⟩
  | cons_cons a b L _ihL ihb =>
      rw [isReduced_cons_cons] at hred
      obtain ⟨hab, hred'⟩ := hred
      have hag : a.1 = g := hgen a (by simp)
      have hbg : b.1 = g := hgen b (by simp)
      have hsab : a.2 = b.2 := hab (hag.trans hbg.symm)
      obtain ⟨s, hs⟩ := ihb b hred' (fun p hp => hgen p (by simp [hp]))
      exact ⟨s, fun p hp => by
        rcases List.mem_cons.mp hp with rfl | hp'
        · rw [hsab, hs b (by simp)]
        · exact hs p hp'⟩

lemma Red.Step.length_zmod {α : Type*} [DecidableEq α] {L M : List (α × Bool)}
    (h : Red.Step L M) : (L.length : ZMod 2) = (M.length : ZMod 2) := by
  have hlen : M.length + 2 = L.length := Red.Step.length h
  rw [← hlen]
  have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
  rw [Nat.cast_add, h2, add_zero]

lemma Red.length_zmod {α : Type*} [DecidableEq α] {L M : List (α × Bool)}
    (h : Red L M) : (L.length : ZMod 2) = (M.length : ZMod 2) := by
  induction h with
  | refl => rfl
  | tail h1 h2 ih => exact ih.trans (Red.Step.length_zmod h2)

lemma reduce_length_zmod {α : Type*} [DecidableEq α] (L : List (α × Bool)) :
    ((reduce L).length : ZMod 2) = (L.length : ZMod 2) :=
  (Red.length_zmod reduce.red).symm


end FreeGroup

namespace AC
namespace A8TailMinimal

open ProofAttempt Invariant

/-- The excess over the abelian minimum at rank two. -/
noncomputable def excessLength (w : Word 2) : ℕ :=
  w.toWord.length - (expVec w 0).natAbs - (expVec w 1).natAbs

/-- The total excess of a rank-two relator list. -/
noncomputable def totalExcess (R : Relators 2) : ℕ :=
  excessLength (R 0) + excessLength (R 1)

/-- The abelian-terminal set at rank two: each exponent vector is a signed basis vector. -/
noncomputable def IsAbelianTerminal (R : Relators 2) : Prop :=
  ∃ σ : Fin 2 → Fin 2, Function.Bijective σ ∧ ∃ ε : Fin 2 → Bool,
    ∀ i : Fin 2, expVec (R i) = if ε i then genVec (σ i) else -genVec (σ i)

/-- Every abelian-terminal state reaches a total-excess minimum. -/
lemma exists_abelianTerminal_tail_minimal (S : Relators 2)
    (hS : IsAbelianTerminal S) :
    ∃ T : Relators 2, Reachable S T ∧ IsAbelianTerminal T ∧
      ∀ U : Relators 2, Reachable T U → IsAbelianTerminal U →
        totalExcess T ≤ totalExcess U := by
  classical
  let p : ℕ → Prop := fun k =>
    ∃ T : Relators 2, Reachable S T ∧ IsAbelianTerminal T ∧ totalExcess T = k
  have hp : ∃ k, p k := ⟨totalExcess S, S, Relation.ReflTransGen.refl, hS, rfl⟩
  obtain ⟨T, hST, hT, hTk⟩ := Nat.find_spec hp
  refine ⟨T, hST, hT, ?_⟩
  intro U hTU hU
  have hUp : p (totalExcess U) :=
    ⟨U, Relation.ReflTransGen.trans hST hTU, hU, rfl⟩
  have hle : Nat.find hp ≤ totalExcess U := Nat.find_min' hp hUp
  rw [hTk]
  exact hle

/-- The exponent vector of a generator is its standard basis vector. -/
@[simp] lemma expVec_of_fin (g : Fin 2) : expVec (FreeGroup.of g) = genVec g := by
  simp [expVec, expHom]

/-- The exponent vector of a singleton word is the signed basis vector. -/
lemma expVec_mk_singleton (g : Fin 2) (b : Bool) :
    expVec (FreeGroup.mk [(g, b)]) =
      if b then genVec g else -genVec g := by
  have h : FreeGroup.mk [(g, b)] = A8Reachability.signedGen g b :=
    A8Reachability.wordOfList_singleton g b
  rw [h]
  cases b <;> simp [A8Reachability.signedGen, expVec_of_fin, expVec_inv]

/-- A zero-excess word with a signed basis exponent vector is a signed generator. -/
lemma eq_signedGen_of_excess_zero (w : Word 2) (hzero : excessLength w = 0)
    (g : Fin 2) (b : Bool)
    (hvec : expVec w = if b then genVec g else -genVec g) :
    w = A8Reachability.signedGen g b := by
  have hsum : (expVec w 0).natAbs + (expVec w 1).natAbs = 1 := by
    rw [hvec]
    fin_cases g <;> cases b <;> simp [genVec]
  have hle : w.toWord.length ≤ (expVec w 0).natAbs + (expVec w 1).natAbs := by
    dsimp [excessLength] at hzero
    omega
  have hpos : 0 < w.toWord.length := by
    rw [List.length_pos_iff_ne_nil]
    intro hnil
    have hw : w = 1 := FreeGroup.toWord_eq_nil_iff.mp hnil
    have hzeroVec : expVec w = 0 := by simp [hw]
    rw [hzeroVec] at hsum
    simp at hsum
  have hlen : w.toWord.length = 1 := by omega
  rcases List.length_eq_one_iff.mp hlen with ⟨p, hp⟩
  obtain ⟨pg, pb⟩ := p
  have hw : w = FreeGroup.mk [(pg, pb)] := by
    rw [← FreeGroup.mk_toWord (x := w), hp]
  have hvec' : expVec (FreeGroup.mk [(pg, pb)]) =
      if b then genVec g else -genVec g := by
    rw [← hw]
    exact hvec
  rw [expVec_mk_singleton] at hvec'
  have hpg : pg = g := by
    fin_cases pg <;> fin_cases g <;> cases pb <;> cases b <;>
      first
      | rfl
      | (have h0 := congrFun hvec' 0
         have h1 := congrFun hvec' 1
         simp [genVec] at h0 h1)
  have hpb : pb = b := by
    fin_cases pg <;> fin_cases g <;> cases pb <;> cases b <;>
      first
      | rfl
      | (have h0 := congrFun hvec' 0
         have h1 := congrFun hvec' 1
         simp [genVec] at h0 h1)
  rw [hw, hpg, hpb]
  exact A8Reachability.wordOfList_singleton g b

/-- A zero-excess abelian-terminal state is already a signed permutation. -/
theorem isSignedPermutation_of_totalExcess_zero (S : Relators 2)
    (hS : IsAbelianTerminal S) (hzero : totalExcess S = 0) :
    IsSignedPermutation S := by
  rcases hS with ⟨σ, hσ, ε, hε⟩
  refine ⟨σ, hσ, ε, ?_⟩
  intro i
  have h0 : excessLength (S i) = 0 := by
    have hle : excessLength (S i) ≤ totalExcess S := by
      fin_cases i <;> simp [totalExcess]
    omega
  exact eq_signedGen_of_excess_zero (S i) h0 (σ i) (ε i) (hε i)

lemma toWord_mul_length_zmod (x y : Word 2) :
    (((x * y).toWord.length : ZMod 2)) =
      (x.toWord.length : ZMod 2) + (y.toWord.length : ZMod 2) := by
  rw [FreeGroup.toWord_mul, FreeGroup.reduce_length_zmod, List.length_append]
  push_cast
  ring

lemma expVec_sum_zmod_eq_length (w : Word 2) :
    (expVec w 0 : ZMod 2) + (expVec w 1 : ZMod 2) =
      (w.toWord.length : ZMod 2) := by
  induction w using FreeGroup.induction_on with
  | one => simp
  | of i =>
      fin_cases i <;> simp [expVec, expHom, genVec]
  | inv_of i ih =>
      rw [expVec_inv]
      fin_cases i <;> simp [genVec]
  | mul x y ihx ihy =>
      rw [expVec_mul]
      simp only [Pi.add_apply]
      rw [Int.cast_add, Int.cast_add]
      rw [toWord_mul_length_zmod]
      calc
        ((expVec x 0 : ZMod 2) + (expVec y 0 : ZMod 2)) +
            ((expVec x 1 : ZMod 2) + (expVec y 1 : ZMod 2)) =
            ((expVec x 0 : ZMod 2) + (expVec x 1 : ZMod 2)) +
              ((expVec y 0 : ZMod 2) + (expVec y 1 : ZMod 2)) := by ring
        _ = (x.toWord.length : ZMod 2) + (y.toWord.length : ZMod 2) := by
          rw [ihx, ihy]

lemma natAbs_sum_eq_one_of_signed (g : Fin 2) (b : Bool) :
    ((if b then genVec g else -genVec g) 0).natAbs +
      ((if b then genVec g else -genVec g) 1).natAbs = 1 := by
  fin_cases g <;> cases b <;> simp [genVec]

lemma signed_zmod_sum_eq_one (g : Fin 2) (b : Bool) :
    ((if b then genVec g else -genVec g) 0 : ZMod 2) +
      ((if b then genVec g else -genVec g) 1 : ZMod 2) = 1 := by
  fin_cases g <;> cases b <;> simp [genVec]

lemma excessLength_eq_length_sub_one_of_signed (w : Word 2) (g : Fin 2) (b : Bool)
    (hvec : expVec w = if b then genVec g else -genVec g) :
    excessLength w = w.toWord.length - 1 := by
  dsimp [excessLength]
  have hsum : (expVec w 0).natAbs + (expVec w 1).natAbs = 1 := by
    rw [hvec]
    exact natAbs_sum_eq_one_of_signed g b
  rw [Nat.sub_sub, hsum]

/-- The excess at an abelian-terminal relator is even. -/
theorem excessLength_even (S : Relators 2) (hS : IsAbelianTerminal S) (i : Fin 2) :
    Even (excessLength (S i)) := by
  rcases hS with ⟨σ, hσ, ε, hε⟩
  have hparity := expVec_sum_zmod_eq_length (S i)
  rw [hε i] at hparity
  have hleft :
      ((if ε i then genVec (σ i) else -genVec (σ i)) 0 : ZMod 2) +
        ((if ε i then genVec (σ i) else -genVec (σ i)) 1 : ZMod 2) = 1 := by
    simpa using signed_zmod_sum_eq_one (σ i) (ε i)
  rw [hleft] at hparity
  have hodd : Odd (S i).toWord.length :=
    ZMod.natCast_eq_one_iff_odd.mp hparity.symm
  rw [excessLength_eq_length_sub_one_of_signed (S i) (σ i) (ε i) (hε i)]
  rw [Nat.even_iff]
  have hmod : (S i).toWord.length % 2 = 1 := Nat.odd_iff.mp hodd
  omega

/-- A reduced word of length one with a signed basis exponent vector is a signed generator. -/
lemma eq_signedGen_of_length_one (w : Word 2) (hlen : w.toWord.length = 1)
    (g : Fin 2) (b : Bool)
    (hvec : expVec w = if b then genVec g else -genVec g) :
    w = A8Reachability.signedGen g b := by
  have hzero : excessLength w = 0 := by
    dsimp [excessLength]
    have hsum : (expVec w 0).natAbs + (expVec w 1).natAbs = 1 := by
      rw [hvec]
      exact natAbs_sum_eq_one_of_signed g b
    rw [Nat.sub_sub, hsum, hlen]
  exact eq_signedGen_of_excess_zero w hzero g b hvec

/-- The exponent vector of a three-letter word is the sum of its three signed letters. -/
lemma expVec_mk_three (a b c : Fin 2 × Bool) :
    expVec (FreeGroup.mk [a, b, c]) =
      (if a.2 then genVec a.1 else -genVec a.1) +
      (if b.2 then genVec b.1 else -genVec b.1) +
      (if c.2 then genVec c.1 else -genVec c.1) := by
  have h : FreeGroup.mk [a, b, c] =
      FreeGroup.mk [a] * FreeGroup.mk [b] * FreeGroup.mk [c] := by
    rw [show [a, b, c] = [a] ++ [b] ++ [c] by simp]
    rw [FreeGroup.mul_mk, FreeGroup.mul_mk]
  rw [h, expVec_mul, expVec_mul, expVec_mk_singleton,
    expVec_mk_singleton, expVec_mk_singleton]

/-- A cyclically reduced three-letter word cannot have a signed basis exponent vector. -/
lemma no_cyc_len3 (a b c : Fin 2 × Bool) (g : Fin 2) (s : Bool)
    (hcyc : FreeGroup.IsCyclicallyReduced [a, b, c])
    (hvec : expVec (FreeGroup.mk [a, b, c]) =
      if s then genVec g else -genVec g) : False := by
  obtain ⟨ag, ab⟩ := a
  obtain ⟨bg, bb⟩ := b
  obtain ⟨cg, cb⟩ := c
  fin_cases ag <;> fin_cases bg <;> fin_cases cg <;>
    cases ab <;> cases bb <;> cases cb <;>
    rw [expVec_mk_three] at hvec <;>
    simp [FreeGroup.IsReduced, FreeGroup.IsCyclicallyReduced, genVec] at hcyc hvec <;>
    (have h0 := congrFun hvec 0
     have h1 := congrFun hvec 1
     fin_cases g <;> cases s <;> simp at h0 h1)

/-- A cyclically reduced three-letter word with a signed basis exponent vector is a
conjugate of a signed generator. The hypotheses are mutually inconsistent, so the
statement is vacuous and the witness is supplied by `False.elim`. -/
theorem eq_conj_signedGen_of_length_three (w : Word 2)
    (hcyc : FreeGroup.IsCyclicallyReduced w.toWord)
    (hlen : w.toWord.length = 3) (g : Fin 2) (s : Bool)
    (hvec : expVec w = if s then genVec g else -genVec g) :
    ∃ u : Word 2, w = u * A8Reachability.signedGen g s * u⁻¹ := by
  rcases List.length_eq_three.mp hlen with ⟨a, b, c, hL⟩
  have hw : w = FreeGroup.mk [a, b, c] := by
    rw [← FreeGroup.mk_toWord (x := w), hL]
  have hcyc' : FreeGroup.IsCyclicallyReduced [a, b, c] := by
    simpa [hL] using hcyc
  have hvec' : expVec (FreeGroup.mk [a, b, c]) =
      if s then genVec g else -genVec g := by
    rw [← hw]
    exact hvec
  exact False.elim (no_cyc_len3 a b c g s hcyc' hvec')

/-- A non-cyclically-reduced word has a shorter conjugate. -/
lemma exists_shorter_conj_of_not_cyclicallyReduced (w : Word 2)
    (h : ¬ FreeGroup.IsCyclicallyReduced w.toWord) :
    ∃ v : Word 2, (v * w * v⁻¹).toWord.length < w.toWord.length := by
  classical
  let L := w.toWord
  let c := FreeGroup.reduceCyclically.conjugator L
  let R := FreeGroup.reduceCyclically L
  have hred : FreeGroup.IsReduced L := FreeGroup.isReduced_toWord
  have hRcyc : FreeGroup.IsCyclicallyReduced R :=
    FreeGroup.reduceCyclically.isCyclicallyReduced hred
  have hRred : FreeGroup.IsReduced R := hRcyc.isReduced
  have hsplit : c ++ R ++ FreeGroup.invRev c = L :=
    FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically L
  have hcne : c ≠ [] := by
    intro hc
    have hRL : R = L := by
      simpa [c, R, hc] using hsplit
    apply h
    rw [hRL] at hRcyc
    simpa [L] using hRcyc
  have hclen : 0 < c.length := List.length_pos_iff_ne_nil.mpr hcne
  have hlen : c.length + R.length + c.length = L.length := by
    have h := congrArg List.length hsplit
    simpa [c, R, List.length_append, Nat.add_assoc] using h
  have hRlen : R.length < L.length := by omega
  have hto : (FreeGroup.mk R).toWord = R := by
    rw [FreeGroup.toWord_mk, hRred.reduce_eq]
  have hw : w = FreeGroup.mk c * FreeGroup.mk R * (FreeGroup.mk c)⁻¹ := by
    calc
      w = FreeGroup.mk w.toWord := (FreeGroup.mk_toWord).symm
      _ = FreeGroup.mk (c ++ R ++ FreeGroup.invRev c) := by rw [hsplit]
      _ = FreeGroup.mk c * FreeGroup.mk R * (FreeGroup.mk c)⁻¹ := by
        rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk]
  refine ⟨(FreeGroup.mk c)⁻¹, ?_⟩
  have hconj : (FreeGroup.mk c)⁻¹ * w * ((FreeGroup.mk c)⁻¹)⁻¹ = FreeGroup.mk R := by
    rw [hw]
    group
  rw [hconj, hto]
  exact hRlen

/-- A length-zero word is cyclically reduced. -/
lemma isCyclicallyReduced_of_length_zero (w : Word 2)
    (h : w.toWord.length = 0) :
    FreeGroup.IsCyclicallyReduced w.toWord := by
  have hnil : w.toWord = [] := List.length_eq_zero_iff.mp h
  rw [hnil]
  simp [FreeGroup.IsCyclicallyReduced, FreeGroup.IsReduced]

/-- A length-one word is cyclically reduced. -/
lemma isCyclicallyReduced_of_length_one (w : Word 2)
    (h : w.toWord.length = 1) :
    FreeGroup.IsCyclicallyReduced w.toWord := by
  rcases List.length_eq_one_iff.mp h with ⟨x, hx⟩
  rw [hx]
  simp [FreeGroup.IsCyclicallyReduced, FreeGroup.IsReduced]

/-- Conjugating one relator strictly lowers the total excess when its word shortens
and the original relator has at least two letters. -/
lemma totalExcess_conj_lt (S : Relators 2) (i : Fin 2) (v : Word 2)
    (hS : IsAbelianTerminal S)
    (hlen : (v * S i * v⁻¹).toWord.length < (S i).toWord.length)
    (hge2 : 2 ≤ (S i).toWord.length) :
    totalExcess (Function.update S i (v * S i * v⁻¹)) < totalExcess S := by
  revert hlen hge2
  fin_cases i
  · intro hlen hge2
    rcases hS with ⟨σ, _hσ, ε, hε⟩
    have hlen0 : (v * S 0 * v⁻¹).toWord.length < (S 0).toWord.length := by
      simpa using hlen
    have hge20 : 2 ≤ (S 0).toWord.length := by
      simpa using hge2
    have hexp_i : expVec (v * S 0 * v⁻¹) = expVec (S 0) := expVec_conj
    have he_i : excessLength (v * S 0 * v⁻¹) =
        (v * S 0 * v⁻¹).toWord.length - 1 :=
      excessLength_eq_length_sub_one_of_signed (v * S 0 * v⁻¹) (σ 0) (ε 0)
        (by rw [hexp_i]; exact hε 0)
    have he_S : excessLength (S 0) = (S 0).toWord.length - 1 :=
      excessLength_eq_length_sub_one_of_signed (S 0) (σ 0) (ε 0) (hε 0)
    have hsub : (v * S 0 * v⁻¹).toWord.length - 1 <
        (S 0).toWord.length - 1 := by
      omega
    change excessLength (v * S 0 * v⁻¹) + excessLength (S 1) <
      excessLength (S 0) + excessLength (S 1)
    rw [he_i, he_S]
    omega
  · intro hlen hge2
    rcases hS with ⟨σ, _hσ, ε, hε⟩
    have hlen1 : (v * S 1 * v⁻¹).toWord.length < (S 1).toWord.length := by
      simpa using hlen
    have hge21 : 2 ≤ (S 1).toWord.length := by
      simpa using hge2
    have hexp_i : expVec (v * S 1 * v⁻¹) = expVec (S 1) := expVec_conj
    have he_i : excessLength (v * S 1 * v⁻¹) =
        (v * S 1 * v⁻¹).toWord.length - 1 :=
      excessLength_eq_length_sub_one_of_signed (v * S 1 * v⁻¹) (σ 1) (ε 1)
        (by rw [hexp_i]; exact hε 1)
    have he_S : excessLength (S 1) = (S 1).toWord.length - 1 :=
      excessLength_eq_length_sub_one_of_signed (S 1) (σ 1) (ε 1) (hε 1)
    have hsub : (v * S 1 * v⁻¹).toWord.length - 1 <
        (S 1).toWord.length - 1 := by
      omega
    change excessLength (S 0) + excessLength (v * S 1 * v⁻¹) <
      excessLength (S 0) + excessLength (S 1)
    rw [he_i, he_S]
    omega

/-- A tail-minimal abelian-terminal state is cyclically reduced in every relator. -/
lemma cyclicallyReduced_of_minimal (S : Relators 2) (hS : IsAbelianTerminal S)
    (hmin : ∀ U : Relators 2, Reachable S U → IsAbelianTerminal U →
      totalExcess S ≤ totalExcess U) :
    ∀ i : Fin 2, FreeGroup.IsCyclicallyReduced (S i).toWord := by
  intro i
  by_contra hnot
  obtain ⟨v, hv⟩ := exists_shorter_conj_of_not_cyclicallyReduced (S i) hnot
  let T : Relators 2 := Function.update S i (v * S i * v⁻¹)
  have hstep : Reachable S T := by
    dsimp [T]
    exact Relation.ReflTransGen.single (Step.conj S i v)
  have hT : IsAbelianTerminal T := by
    rcases hS with ⟨σ, hσ, ε, hε⟩
    refine ⟨σ, hσ, ε, ?_⟩
    intro j
    by_cases hj : j = i
    · subst hj
      dsimp [T]
      rw [Function.update_self, expVec_conj]
      exact hε j
    · dsimp [T]
      rw [Function.update_of_ne hj]
      exact hε j
  have hge2 : 2 ≤ (S i).toWord.length := by
    have hge1 : 1 ≤ (S i).toWord.length := by
      by_contra h
      have h0 : (S i).toWord.length = 0 := by omega
      exact hnot (isCyclicallyReduced_of_length_zero (S i) h0)
    have hne1 : (S i).toWord.length ≠ 1 := by
      intro h1
      exact hnot (isCyclicallyReduced_of_length_one (S i) h1)
    omega
  have hlt : totalExcess T < totalExcess S := by
    dsimp [T]
    exact totalExcess_conj_lt S i v hS hv hge2
  exact absurd (hmin T hstep hT) (not_le.mpr hlt)

/-- The exponent vector of a repeated letter is a scalar multiple of its basis vector. -/
lemma expVec_mk_replicate (g : Fin 2) (s : Bool) (n : ℕ) :
    expVec (FreeGroup.mk (List.replicate n (g, s))) =
      if s then (n : ℤ) • genVec g else -((n : ℤ) • genVec g) := by
  induction n with
  | zero =>
      change expVec (FreeGroup.mk ([] : List (Fin 2 × Bool))) =
        if s then (0 : ℤ) • genVec g else -((0 : ℤ) • genVec g)
      have hmk : FreeGroup.mk ([] : List (Fin 2 × Bool)) = (1 : Word 2) := by
        rw [← FreeGroup.mk_toWord (x := (1 : Word 2))]
        simp
      rw [hmk]
      cases s <;> simp
  | succ n ih =>
      rw [List.replicate_succ]
      have h : FreeGroup.mk ((g, s) :: List.replicate n (g, s)) =
          A8Reachability.signedGen g s *
            FreeGroup.mk (List.replicate n (g, s)) := by
        rw [show (g, s) :: List.replicate n (g, s) =
          [(g, s)] ++ List.replicate n (g, s) by rfl]
        rw [← FreeGroup.mul_mk]
        change A8Reachability.wordOfList [(g, s)] *
          FreeGroup.mk (List.replicate n (g, s)) =
          A8Reachability.signedGen g s *
            FreeGroup.mk (List.replicate n (g, s))
        rw [A8Reachability.wordOfList_singleton]
      have hsingle : expVec (A8Reachability.signedGen g s) =
          if s then genVec g else -genVec g := by
        cases s <;> simp [A8Reachability.signedGen, expVec_of_fin, expVec_inv]
      rw [h, expVec_mul, hsingle, ih]
      cases s <;> simp [add_smul]
      all_goals ring

/-- A word avoiding the pivot generator, with a signed basis exponent vector, is the
other signed generator. This is the corrected single-generator rigidity lemma. -/
lemma eq_signedGen_of_avoids_of_signedVec (u : Word 2) (g h : Fin 2)
    (hgh : g ≠ h)
    (hav : ∀ p ∈ u.toWord, p.1 ≠ h)
    (hvec : expVec u = genVec g ∨ expVec u = -genVec g) :
    u = FreeGroup.of g ∨ u = (FreeGroup.of g)⁻¹ := by
  have hred : FreeGroup.IsReduced u.toWord := FreeGroup.isReduced_toWord
  have hgen : ∀ p ∈ u.toWord, p.1 = g := by
    intro p hp
    obtain ⟨pg, pb⟩ := p
    have hpne : pg ≠ h := hav (pg, pb) (by simpa using hp)
    fin_cases g <;> fin_cases h <;> fin_cases pg <;>
      simp at hpne hgh ⊢
  obtain ⟨s, hs⟩ := hred.exists_sign_of_forall_fst_eq hgen
  let n := u.toWord.length
  have hrep : u.toWord = List.replicate n (g, s) := by
    dsimp [n]
    apply List.eq_replicate_length.mpr
    intro p hp
    obtain ⟨pg, pb⟩ := p
    have hg : pg = g := hgen (pg, pb) (by simpa using hp)
    have hb : pb = s := hs (pg, pb) (by simpa using hp)
    simp [hg, hb]
  have hw : u = FreeGroup.mk (List.replicate n (g, s)) := by
    rw [← FreeGroup.mk_toWord (x := u), hrep]
  have hvec0 := hvec
  have hexp := expVec_mk_replicate g s n
  rw [hw] at hvec
  have hlen : n = 1 := by
    rcases hvec with h | h
    · have hc := congrFun (hexp.symm.trans h) g
      cases s
      · simp [genVec] at hc
        try omega
      · simp [genVec] at hc
        try omega
    · have hc := congrFun (hexp.symm.trans h) g
      cases s
      · simp [genVec] at hc
        try omega
      · simp [genVec] at hc
        try omega
  have hlen' : u.toWord.length = 1 := by simpa [n] using hlen
  rcases hvec0 with h | h
  · left
    have := eq_signedGen_of_length_one u hlen' g true h
    simpa [A8Reachability.signedGen] using this
  · right
    have := eq_signedGen_of_length_one u hlen' g false h
    simpa [A8Reachability.signedGen] using this

/-- The named open core: a tail-minimal abelian-terminal trivial rank-two state is
a signed permutation. -/
def TailMinimalStatement : Prop :=
  ∀ S : Relators 2, IsAbelianTerminal S → PresentsTrivialGroup S →
    (∀ U : Relators 2, Reachable S U → IsAbelianTerminal U →
      totalExcess S ≤ totalExcess U) →
    IsSignedPermutation S

lemma excessLength_signedGen (g : Fin 2) (b : Bool) :
    excessLength (A8Reachability.signedGen g b) = 0 := by
  cases b <;> fin_cases g <;>
    simp [excessLength, A8Reachability.signedGen, expVec_of_fin, expVec_inv, genVec]

/-- A signed permutation has zero total excess. -/
lemma totalExcess_eq_zero_of_signedPermutation {S : Relators 2}
    (h : IsSignedPermutation S) : totalExcess S = 0 := by
  obtain ⟨σ, hσ, ε, hε⟩ := h
  have h0 : S 0 = A8Reachability.signedGen (σ 0) (ε 0) := by
    simpa [A8Reachability.signedGen] using hε 0
  have h1 : S 1 = A8Reachability.signedGen (σ 1) (ε 1) := by
    simpa [A8Reachability.signedGen] using hε 1
  simp [totalExcess, h0, h1, excessLength_signedGen]

/-- The tail-minimal theorem is exactly the assertion that every tail-minimal
abelian-terminal trivial state has zero total excess. -/
theorem tailMinimalStatement_iff_minimalExcessZero :
    TailMinimalStatement ↔
      ∀ S : Relators 2, IsAbelianTerminal S → PresentsTrivialGroup S →
        (∀ U : Relators 2, Reachable S U → IsAbelianTerminal U →
          totalExcess S ≤ totalExcess U) →
        totalExcess S = 0 := by
  constructor
  · intro h S hS hp hmin
    exact totalExcess_eq_zero_of_signedPermutation (h S hS hp hmin)
  · intro h S hS hp hmin
    exact isSignedPermutation_of_totalExcess_zero S hS (h S hS hp hmin)

/-- The tail-minimal theorem implies the rank-two A8 statement. -/
theorem a8_rank_two_of_tailMinimalStatement (h : TailMinimalStatement) :
    ∀ S : Relators 2, IsAbelianTerminal S → PresentsTrivialGroup S →
      ∃ T : Relators 2, IsSignedPermutation T ∧ Reachable S T := by
  intro S hS hp
  obtain ⟨T, hST, hT, hmin⟩ := exists_abelianTerminal_tail_minimal S hS
  have hpT : PresentsTrivialGroup T := (presents_of_reachable hST).mp hp
  exact ⟨T, h T hT hpT hmin, hST⟩

end A8TailMinimal
end AC
