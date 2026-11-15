module

public import AcA8TailMinimal
public import AcNielsen
public import NielsenRotationNormalForm

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace AC
namespace Nielsen

/-! ## 1. Definitional equality of the two abelian-terminal predicates -/

theorem isAbelianTerminal_iff_abelianTerminal (R : Relators 2) :
    AC.A8TailMinimal.IsAbelianTerminal R ↔ AbelianTerminal R :=
  Iff.rfl

/-! ## 2. The exponent bound: |e_0| + |e_1| <= reduced length -/

theorem natAbs_expVec_sum_le_length_mk (L : List (Fin 2 × Bool)) :
    (Invariant.expVec (FreeGroup.mk L) 0).natAbs +
      (Invariant.expVec (FreeGroup.mk L) 1).natAbs ≤ L.length := by
  induction L with
  | nil =>
      rw [← FreeGroup.one_eq_mk]
      simp
  | cons a t ih =>
      obtain ⟨g, b⟩ := a
      have hsplit : FreeGroup.mk ((g, b) :: t) =
          FreeGroup.mk [(g, b)] * FreeGroup.mk t := by
        rw [FreeGroup.mul_mk]
        rfl
      rw [hsplit, Invariant.expVec_mul, List.length_cons]
      have hsingle :
          (Invariant.expVec (FreeGroup.mk [(g, b)]) 0).natAbs +
            (Invariant.expVec (FreeGroup.mk [(g, b)]) 1).natAbs = 1 := by
        rw [AC.A8TailMinimal.expVec_mk_singleton]
        exact AC.A8TailMinimal.natAbs_sum_eq_one_of_signed g b
      have h0 : ((Invariant.expVec (FreeGroup.mk [(g, b)]) +
            Invariant.expVec (FreeGroup.mk t)) 0).natAbs ≤
          (Invariant.expVec (FreeGroup.mk [(g, b)]) 0).natAbs +
            (Invariant.expVec (FreeGroup.mk t) 0).natAbs := by
        simpa using Int.natAbs_add_le
          (Invariant.expVec (FreeGroup.mk [(g, b)]) 0)
          (Invariant.expVec (FreeGroup.mk t) 0)
      have h1 : ((Invariant.expVec (FreeGroup.mk [(g, b)]) +
            Invariant.expVec (FreeGroup.mk t)) 1).natAbs ≤
          (Invariant.expVec (FreeGroup.mk [(g, b)]) 1).natAbs +
            (Invariant.expVec (FreeGroup.mk t) 1).natAbs := by
        simpa using Int.natAbs_add_le
          (Invariant.expVec (FreeGroup.mk [(g, b)]) 1)
          (Invariant.expVec (FreeGroup.mk t) 1)
      omega

theorem natAbs_expVec_sum_le_length (w : Word 2) :
    (Invariant.expVec w 0).natAbs + (Invariant.expVec w 1).natAbs ≤
      w.toWord.length := by
  have h := natAbs_expVec_sum_le_length_mk w.toWord
  rwa [FreeGroup.mk_toWord] at h

/-! ## 3. cycLen at a cyclically reduced word -/

theorem cycLen_eq_toWord_length_of_cycRed (w : Word 2)
    (h : FreeGroup.IsCyclicallyReduced w.toWord) :
    cycLen w = w.toWord.length := by
  unfold cycLen
  rw [RotationNormalForm.reduceCyclically_eq_self h]

/-! ## 4. The bridge -/

theorem totalExcess_add_two_eq_cyclicNielsenLength
    (S : Relators 2) (hS : AC.A8TailMinimal.IsAbelianTerminal S)
    (hcyc : ∀ i : Fin 2, FreeGroup.IsCyclicallyReduced (S i).toWord) :
    AC.A8TailMinimal.totalExcess S + 2 = cyclicNielsenLength S := by
  obtain ⟨σ, _hσ, ε, hε⟩ := hS
  have hexp : ∀ i : Fin 2,
      AC.A8TailMinimal.excessLength (S i) = (S i).toWord.length - 1 :=
    fun i => AC.A8TailMinimal.excessLength_eq_length_sub_one_of_signed
      (S i) (σ i) (ε i) (hε i)
  have hlen : ∀ i : Fin 2, 1 ≤ (S i).toWord.length := by
    intro i
    have h1 : (Invariant.expVec (S i) 0).natAbs +
        (Invariant.expVec (S i) 1).natAbs = 1 := by
      rw [hε i]
      exact AC.A8TailMinimal.natAbs_sum_eq_one_of_signed (σ i) (ε i)
    have h2 := natAbs_expVec_sum_le_length (S i)
    omega
  have hcycLen : ∀ i : Fin 2, cycLen (S i) = (S i).toWord.length :=
    fun i => cycLen_eq_toWord_length_of_cycRed (S i) (hcyc i)
  have e0 := hexp 0
  have e1 := hexp 1
  have l0 := hlen 0
  have l1 := hlen 1
  simp only [AC.A8TailMinimal.totalExcess, RotationNormalForm.cyclicNielsenLength_pair,
    hcycLen 0, hcycLen 1, e0, e1]
  omega

/-! ## 5. The reachability repair -/

theorem step_cyclicReduction (R : Relators 2) (i : Fin 2) :
    ∃ R' : Relators 2, Step R R' ∧
      FreeGroup.IsCyclicallyReduced (R' i).toWord ∧
      cycLen (R' i) = cycLen (R i) ∧
      Invariant.expVec (R' i) = Invariant.expVec (R i) ∧
      ∀ k : Fin 2, k ≠ i → R' k = R k := by
  classical
  let c := FreeGroup.reduceCyclically.conjugator (R i).toWord
  let Q := FreeGroup.reduceCyclically (R i).toWord
  have hred : FreeGroup.IsReduced (R i).toWord := FreeGroup.isReduced_toWord
  have hQcyc : FreeGroup.IsCyclicallyReduced Q :=
    FreeGroup.reduceCyclically.isCyclicallyReduced hred
  have hQred : FreeGroup.IsReduced Q := hQcyc.isReduced
  have hsplit : c ++ Q ++ FreeGroup.invRev c = (R i).toWord :=
    FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically (R i).toWord
  have hto : (FreeGroup.mk Q).toWord = Q := by
    rw [FreeGroup.toWord_mk, hQred.reduce_eq]
  have hw : R i = FreeGroup.mk c * FreeGroup.mk Q * (FreeGroup.mk c)⁻¹ := by
    calc
      R i = FreeGroup.mk (R i).toWord := (FreeGroup.mk_toWord).symm
      _ = FreeGroup.mk (c ++ Q ++ FreeGroup.invRev c) := by rw [hsplit]
      _ = FreeGroup.mk c * FreeGroup.mk Q * (FreeGroup.mk c)⁻¹ := by
        rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk]
  have hconj : (FreeGroup.mk c)⁻¹ * R i * ((FreeGroup.mk c)⁻¹)⁻¹ =
      FreeGroup.mk Q := by
    rw [hw]
    group
  refine ⟨Function.update R i ((FreeGroup.mk c)⁻¹ * R i * ((FreeGroup.mk c)⁻¹)⁻¹),
    Step.conj R i (FreeGroup.mk c)⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [Function.update_self, hconj, hto]
    exact hQcyc
  · rw [Function.update_self]
    exact cycLen_conj (FreeGroup.mk c)⁻¹ (R i)
  · rw [Function.update_self]
    exact Invariant.expVec_conj
  · intro k hk
    rw [Function.update_of_ne hk]

theorem reachable_cyclicReduction (S : Relators 2) :
    ∃ T : Relators 2, Reachable S T ∧
      (∀ i : Fin 2, FreeGroup.IsCyclicallyReduced (T i).toWord) ∧
      (∀ i : Fin 2, cycLen (T i) = cycLen (S i)) ∧
      (∀ i : Fin 2, Invariant.expVec (T i) = Invariant.expVec (S i)) := by
  classical
  obtain ⟨S1, hstep1, hcyc1, hlen1, hexp1, hrest1⟩ := step_cyclicReduction S 0
  have hS1_1 : S1 1 = S 1 := hrest1 1 (by decide)
  obtain ⟨S2, hstep2, hcyc2, hlen2, hexp2, hrest2⟩ := step_cyclicReduction S1 1
  have hS2_0 : S2 0 = S1 0 := hrest2 0 (by decide)
  refine ⟨S2, (Relation.ReflTransGen.single hstep1).trans
    (Relation.ReflTransGen.single hstep2), ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · show FreeGroup.IsCyclicallyReduced (S2 0).toWord
      rw [hS2_0]
      exact hcyc1
    · exact hcyc2
  · intro i
    fin_cases i
    · show cycLen (S2 0) = cycLen (S 0)
      rw [hS2_0, hlen1]
    · show cycLen (S2 1) = cycLen (S 1)
      rw [hlen2, hS1_1]
  · intro i
    fin_cases i
    · show Invariant.expVec (S2 0) = Invariant.expVec (S 0)
      rw [hS2_0, hexp1]
    · show Invariant.expVec (S2 1) = Invariant.expVec (S 1)
      rw [hexp2, hS1_1]

theorem reachable_cyclicReduction_abelianTerminal
    (S : Relators 2) (hS : AbelianTerminal S) :
    ∃ T : Relators 2, Reachable S T ∧ AbelianTerminal T ∧
      (∀ i : Fin 2, FreeGroup.IsCyclicallyReduced (T i).toWord) ∧
      cyclicNielsenLength T = cyclicNielsenLength S := by
  classical
  obtain ⟨T, hreach, hcyc, hlen, hexp⟩ := reachable_cyclicReduction S
  refine ⟨T, hreach, ?_, hcyc, ?_⟩
  · obtain ⟨σ, hσ, ε, hε⟩ := hS
    refine ⟨σ, hσ, ε, ?_⟩
    intro i
    rw [hexp i]
    exact hε i
  · rw [RotationNormalForm.cyclicNielsenLength_pair,
      RotationNormalForm.cyclicNielsenLength_pair, hlen 0, hlen 1]

/-! ## 6. The Case C contradiction -/

theorem false_of_uniformPivot_and_minimal
    (h : cyclicNielsen_uniform_pivot_statement)
    (S : Relators 2)
    (hS : AbelianTerminal S) (hp : PresentsTrivialGroup S)
    (hcycS : ∀ i : Fin 2, FreeGroup.IsCyclicallyReduced (S i).toWord)
    (hnsp : ¬ ProofAttempt.IsSignedPermutation S)
    (h5 : 5 ≤ (S 0).toWord.length) (h7 : 5 ≤ (S 1).toWord.length)
    (hmin : ∀ U : Relators 2, Reachable S U → AbelianTerminal U →
      AC.A8TailMinimal.totalExcess S ≤ AC.A8TailMinimal.totalExcess U) :
    False := by
  classical
  obtain ⟨T, hST, hT, _hpT, hlt⟩ := h S hS hp hcycS hnsp h5 h7
  obtain ⟨U, hTU, hU, hcycU, hlenU⟩ := reachable_cyclicReduction_abelianTerminal T hT
  have bU := totalExcess_add_two_eq_cyclicNielsenLength U hU hcycU
  have bS := totalExcess_add_two_eq_cyclicNielsenLength S hS hcycS
  have hltU : AC.A8TailMinimal.totalExcess U < AC.A8TailMinimal.totalExcess S := by
    omega
  exact absurd (hmin U (hST.trans hTU) hU) (not_le.mpr hltU)

/-! ## 7. The hypothesis is load-bearing: (x y x^-1) has cycLen 1, length 3 -/

theorem concrete_list_isReduced :
    FreeGroup.IsReduced ([(0, true), (1, true), (0, false)] : List (Fin 2 × Bool)) :=
  (RotationNormalForm.isReducedB_iff _).mp (by decide)

theorem concrete_toWord :
    (FreeGroup.mk ([(0, true), (1, true), (0, false)] : List (Fin 2 × Bool))).toWord =
      [(0, true), (1, true), (0, false)] := by
  rw [FreeGroup.toWord_mk, FreeGroup.isReduced_iff_reduce_eq.mp concrete_list_isReduced]

theorem concrete_cycLen :
    cycLen (FreeGroup.mk ([(0, true), (1, true), (0, false)] : List (Fin 2 × Bool))) = 1 := by
  unfold cycLen
  rw [concrete_toWord]
  rw [show ([(0, true), (1, true), (0, false)] : List (Fin 2 × Bool)) =
    (0, true) :: ([(1, true)] ++ [(0, false)]) by rfl]
  rw [FreeGroup.reduceCyclically.cons_append]
  simp

theorem cycLen_ne_length_at_noncycRed :
    cycLen (FreeGroup.mk ([(0, true), (1, true), (0, false)] : List (Fin 2 × Bool))) ≠
      (FreeGroup.mk ([(0, true), (1, true), (0, false)] : List (Fin 2 × Bool))).toWord.length := by
  rw [concrete_cycLen, concrete_toWord]
  decide

theorem concrete_expVec :
    Invariant.expVec (FreeGroup.mk ([(0, true), (1, true), (0, false)] : List (Fin 2 × Bool))) =
      Invariant.genVec (1 : Fin 2) := by
  rw [AC.A8TailMinimal.expVec_mk_three]
  ext j
  fin_cases j <;> simp [Invariant.genVec]

theorem concrete_excessLength :
    AC.A8TailMinimal.excessLength
      (FreeGroup.mk ([(0, true), (1, true), (0, false)] : List (Fin 2 × Bool))) = 2 := by
  have h := AC.A8TailMinimal.excessLength_eq_length_sub_one_of_signed
    (FreeGroup.mk ([(0, true), (1, true), (0, false)] : List (Fin 2 × Bool))) 1 true
    (by simpa using concrete_expVec)
  rw [h, concrete_toWord]
  rfl

end Nielsen
end AC

#print axioms AC.Nielsen.isAbelianTerminal_iff_abelianTerminal
#print axioms AC.Nielsen.natAbs_expVec_sum_le_length
#print axioms AC.Nielsen.totalExcess_add_two_eq_cyclicNielsenLength
#print axioms AC.Nielsen.reachable_cyclicReduction_abelianTerminal
#print axioms AC.Nielsen.false_of_uniformPivot_and_minimal
#print axioms AC.Nielsen.cycLen_ne_length_at_noncycRed
#print axioms AC.Nielsen.concrete_excessLength
