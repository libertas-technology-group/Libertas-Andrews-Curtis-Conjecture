import AC
import Mathlib.GroupTheory.CoprodI
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic

/-!
# Branch C3: the PSL(2,ℤ) orbit test

This file records the image map from the rank-two free group to
`PSL(2,ℤ) ≅ C₂ * C₃`, the action of the official Andrews–Curtis moves on the
image pair, and the bounded length-12 orbit predicate used by the computational
test.

## 1. The group

`PSL` is the free product of `Multiplicative (ZMod 2)` and
`Multiplicative (ZMod 3)`, indexed by `Bool`.  The element `a` is the image of
the order-two factor and `b` the image of the order-three factor.  The map
`pslMap : Word 2 →* PSL` sends `x` to `a` and `y` to `b`.

## 2. The image of an AC move

`step_psl` proves that one official move on a two-relator presentation becomes
one group AC move on the image pair.  `reachable_psl` iterates this over a whole
AC path.  The contrapositive, `not_reachable_of_not_psl_reachable`, is the
certificate direction: a pair outside the unbounded group AC orbit of `(a,b)`
rules out an AC path in the free group.

## 3. The bounded orbit

`pslLength` is the syllable length of the reduced free-product word.
`BoundedStep L` is a group AC move whose target pair has both components of
length at most `L`; `BoundedReachable L` is its reflexive–transitive closure.
`OrbitVerdict` is the pre-registered three-way verdict.

The length-12 enumeration is an external exact computation, recorded in
`BRANCH_C3.md` §5.  This file does not assert the enumeration's output as a
kernel-checked theorem; `pslSampleCounts` is a record of the computed values.

## Status

No `sorry`, no `admit`, no user `axiom`, no `native_decide`. The file is in the
`AcCorpus` globs and compiles in the 3,308-job build under
`leanprover/lean4:v4.29.1` with Mathlib `5e932f97…`.
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace AC
namespace BranchC3

/-! ## 1. The free product `C₂ * C₃` -/

/-- The two factors of `PSL(2,ℤ)`, indexed so that `true` is the order-two
factor and `false` the order-three factor. -/
def pslFactor : Bool → Type
  | true => Multiplicative (ZMod 2)
  | false => Multiplicative (ZMod 3)

instance (i : Bool) : Group (pslFactor i) := by
  cases i <;> dsimp [pslFactor] <;> infer_instance

instance (i : Bool) : Fintype (pslFactor i) := by
  cases i <;> dsimp [pslFactor] <;> infer_instance

instance (i : Bool) : DecidableEq (pslFactor i) := by
  cases i <;> dsimp [pslFactor] <;> infer_instance

/-- `PSL(2,ℤ)` as the free product `C₂ * C₃`. -/
abbrev PSL : Type := Monoid.CoprodI pslFactor

/-- The image of `x`: the generator of the order-two factor. -/
def a : PSL :=
  Monoid.CoprodI.of (M := pslFactor) (i := true) (Multiplicative.ofAdd (1 : ZMod 2))

/-- The image of `y`: the generator of the order-three factor. -/
def b : PSL :=
  Monoid.CoprodI.of (M := pslFactor) (i := false) (Multiplicative.ofAdd (1 : ZMod 3))

/-- `a` has order two. -/
theorem a_sq : a ^ 2 = 1 := by
  unfold a
  rw [← map_pow]
  have h : (Multiplicative.ofAdd (1 : ZMod 2)) ^ 2 = 1 := by
    rw [← ofAdd_nsmul]
    norm_num
    decide
  exact (congrArg (Monoid.CoprodI.of (M := pslFactor) (i := true)) h).trans (map_one _)

/-- `b` has order three. -/
theorem b_cube : b ^ 3 = 1 := by
  unfold b
  rw [← map_pow]
  have h : (Multiplicative.ofAdd (1 : ZMod 3)) ^ 3 = 1 := by
    rw [← ofAdd_nsmul]
    norm_num
    decide
  exact (congrArg (Monoid.CoprodI.of (M := pslFactor) (i := false)) h).trans (map_one _)

/-- The quotient map `F₂ → PSL(2,ℤ)` sending `x` to `a` and `y` to `b`. -/
noncomputable def pslMap : Word 2 →* PSL :=
  FreeGroup.lift (fun i : Fin 2 => if i = 0 then a else b)

@[simp]
theorem pslMap_of_zero : pslMap (FreeGroup.of (0 : Fin 2)) = a := by
  simp [pslMap]

@[simp]
theorem pslMap_of_one : pslMap (FreeGroup.of (1 : Fin 2)) = b := by
  simp [pslMap]

/-- The image pair of a two-relator presentation. -/
noncomputable def tuplePSL (P : Relators 2) : PSL × PSL :=
  (pslMap (P 0), pslMap (P 1))

/-- The image of the standard pair `(x,y)` is `(a,b)`. -/
def standardPSL : PSL × PSL := (a, b)

theorem tuplePSL_standard : tuplePSL (standard 2) = standardPSL := by
  simp [tuplePSL, standard, standardPSL]

/-! ## 2. Reading and updating a pair -/

/-- The two-position update on a pair. -/
def pairUpdate {α : Type*} (p : α × α) (i : Fin 2) (x : α) : α × α :=
  if i = 0 then (x, p.2) else (p.1, x)

/-- Read one position of a pair. -/
def pairGet {α : Type*} (p : α × α) (i : Fin 2) : α :=
  if i = 0 then p.1 else p.2

@[simp]
theorem pairUpdate_zero {α : Type*} (p : α × α) (x : α) :
    pairUpdate p 0 x = (x, p.2) := by
  simp [pairUpdate]

@[simp]
theorem pairUpdate_one {α : Type*} (p : α × α) (x : α) :
    pairUpdate p 1 x = (p.1, x) := by
  simp [pairUpdate]

@[simp]
theorem pairGet_zero {α : Type*} (p : α × α) : pairGet p 0 = p.1 := by
  simp [pairGet]

@[simp]
theorem pairGet_one {α : Type*} (p : α × α) : pairGet p 1 = p.2 := by
  simp [pairGet]

theorem tuplePSL_update (P : Relators 2) (i : Fin 2) (w : Word 2) :
    tuplePSL (Function.update P i w) = pairUpdate (tuplePSL P) i (pslMap w) := by
  fin_cases i <;> simp [tuplePSL, pairUpdate, Function.update]

@[simp]
theorem pairGet_tuplePSL (P : Relators 2) (i : Fin 2) :
    pairGet (tuplePSL P) i = pslMap (P i) := by
  fin_cases i <;> rfl

/-! ## 3. Group AC moves and their normal-closure invariance -/

/-- The three official moves on a pair of elements of a group. -/
inductive GroupACStep (G : Type*) [Group G] : G × G → G × G → Prop
  | inv (g : G × G) (i : Fin 2) :
      GroupACStep G g (pairUpdate g i (pairGet g i)⁻¹)
  | mulRight (g : G × G) (i j : Fin 2) (hij : i ≠ j) :
      GroupACStep G g (pairUpdate g i (pairGet g i * pairGet g j))
  | conj (g : G × G) (i : Fin 2) (w : G) :
      GroupACStep G g (pairUpdate g i (w * pairGet g i * w⁻¹))

/-- Reachability by group AC moves. -/
def GroupACReachable (G : Type*) [Group G] : G × G → G × G → Prop :=
  Relation.ReflTransGen (GroupACStep G)

section NormalClosure

variable {G : Type*} [Group G]

/-- The normal closure of the two components of a pair. -/
def pairNormalClosure (g : G × G) : Subgroup G :=
  Subgroup.normalClosure ({g.1, g.2} : Set G)

theorem normalClosure_swap (u v : G) :
    Subgroup.normalClosure ({v, u} : Set G)
      = Subgroup.normalClosure ({u, v} : Set G) := by
  congr 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem normalClosure_inv_pair (u v : G) :
    Subgroup.normalClosure ({u⁻¹, v} : Set G)
      = Subgroup.normalClosure ({u, v} : Set G) := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h
    · rw [h]
      exact Subgroup.inv_mem _ (Subgroup.subset_normalClosure (by simp))
    · rw [h]
      exact Subgroup.subset_normalClosure (by simp)
  · apply Subgroup.normalClosure_le_normal
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h
    · rw [h]
      have hmem : u⁻¹ ∈ Subgroup.normalClosure ({u⁻¹, v} : Set G) :=
        Subgroup.subset_normalClosure (by simp)
      simpa using Subgroup.inv_mem _ hmem
    · rw [h]
      exact Subgroup.subset_normalClosure (by simp)

theorem normalClosure_mul_pair (u v : G) :
    Subgroup.normalClosure ({u * v, v} : Set G)
      = Subgroup.normalClosure ({u, v} : Set G) := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h
    · rw [h]
      exact Subgroup.mul_mem _ (Subgroup.subset_normalClosure (by simp))
        (Subgroup.subset_normalClosure (by simp))
    · rw [h]
      exact Subgroup.subset_normalClosure (by simp)
  · apply Subgroup.normalClosure_le_normal
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h
    · rw [h]
      have h1 : u * v ∈ Subgroup.normalClosure ({u * v, v} : Set G) :=
        Subgroup.subset_normalClosure (by simp)
      have h2 : v⁻¹ ∈ Subgroup.normalClosure ({u * v, v} : Set G) :=
        Subgroup.inv_mem _ (Subgroup.subset_normalClosure (by simp))
      have h3 : (u * v) * v⁻¹ ∈ Subgroup.normalClosure ({u * v, v} : Set G) :=
        Subgroup.mul_mem _ h1 h2
      simpa using h3
    · rw [h]
      exact Subgroup.subset_normalClosure (by simp)

theorem normalClosure_conj_pair (u v w : G) :
    Subgroup.normalClosure ({w * u * w⁻¹, v} : Set G)
      = Subgroup.normalClosure ({u, v} : Set G) := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h
    · rw [h]
      have hN : (Subgroup.normalClosure ({u, v} : Set G)).Normal :=
        Subgroup.normalClosure_normal
      exact hN.conj_mem u (Subgroup.subset_normalClosure (by simp)) w
    · rw [h]
      exact Subgroup.subset_normalClosure (by simp)
  · apply Subgroup.normalClosure_le_normal
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h
    · rw [h]
      have hmid : w * u * w⁻¹ ∈ Subgroup.normalClosure ({w * u * w⁻¹, v} : Set G) :=
        Subgroup.subset_normalClosure (by simp)
      have hN : (Subgroup.normalClosure ({w * u * w⁻¹, v} : Set G)).Normal :=
        Subgroup.normalClosure_normal
      have hconj := hN.conj_mem (w * u * w⁻¹) hmid w⁻¹
      simpa [mul_assoc] using hconj
    · rw [h]
      exact Subgroup.subset_normalClosure (by simp)

theorem normalClosure_inv_pair_right (u v : G) :
    Subgroup.normalClosure ({u, v⁻¹} : Set G)
      = Subgroup.normalClosure ({u, v} : Set G) := by
  rw [← normalClosure_swap u (v⁻¹), normalClosure_inv_pair v u, normalClosure_swap u v]

theorem normalClosure_mul_pair_right (u v : G) :
    Subgroup.normalClosure ({u, v * u} : Set G)
      = Subgroup.normalClosure ({u, v} : Set G) := by
  rw [← normalClosure_swap u (v * u), normalClosure_mul_pair v u, normalClosure_swap u v]

theorem normalClosure_conj_pair_right (u v w : G) :
    Subgroup.normalClosure ({u, w * v * w⁻¹} : Set G)
      = Subgroup.normalClosure ({u, v} : Set G) := by
  rw [← normalClosure_swap u (w * v * w⁻¹), normalClosure_conj_pair v u w, normalClosure_swap u v]

/-- Every group AC move preserves the normal closure of the pair. -/
theorem GroupACStep.normalClosure_eq {g h : G × G} (hstep : GroupACStep G g h) :
    pairNormalClosure g = pairNormalClosure h := by
  cases hstep with
  | inv i =>
      fin_cases i <;>
        simp [pairNormalClosure, pairUpdate, pairGet,
          normalClosure_inv_pair, normalClosure_inv_pair_right]
  | mulRight i j hij =>
      fin_cases i <;> fin_cases j <;>
        simp_all [pairNormalClosure, pairUpdate, pairGet,
          normalClosure_mul_pair, normalClosure_mul_pair_right]
  | conj i w =>
      fin_cases i <;>
        simp [pairNormalClosure, pairUpdate, pairGet,
          normalClosure_conj_pair, normalClosure_conj_pair_right]

end NormalClosure

/-! ## 4. Lifting an AC path to the quotient -/

/-- One official move on a presentation becomes one group AC move on the image
pair.  This is the functoriality of `pslMap`. -/
theorem step_psl {P Q : Relators 2} (h : Step P Q) :
    GroupACReachable PSL (tuplePSL P) (tuplePSL Q) := by
  cases h with
  | inv i =>
      rw [tuplePSL_update, map_inv]
      simpa only [pairGet_tuplePSL] using
        (Relation.ReflTransGen.single (GroupACStep.inv (tuplePSL P) i))
  | mulRight i j hij =>
      rw [tuplePSL_update, map_mul]
      simpa only [pairGet_tuplePSL] using
        (Relation.ReflTransGen.single (GroupACStep.mulRight (tuplePSL P) i j hij))
  | conj i w =>
      rw [tuplePSL_update]
      simpa only [map_mul, map_inv, pairGet_tuplePSL] using
        (Relation.ReflTransGen.single (GroupACStep.conj (tuplePSL P) i (pslMap w)))

/-- A whole AC path lifts to the quotient. -/
theorem reachable_psl {P Q : Relators 2} (h : Reachable P Q) :
    GroupACReachable PSL (tuplePSL P) (tuplePSL Q) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.trans (step_psl hstep)

/-- The certificate direction: a pair outside the unbounded group AC orbit of
`(a,b)` rules out an AC path in the free group. -/
theorem not_reachable_of_not_psl_reachable {P : Relators 2}
    (h : ¬ GroupACReachable PSL (tuplePSL P) standardPSL) :
    ¬ Reachable P (standard 2) := by
  intro hAC
  apply h
  rw [← tuplePSL_standard]
  exact reachable_psl hAC

/-! ## 5. The bounded length-12 orbit -/

/-- The syllable length of the reduced free-product word. -/
noncomputable def pslLength (g : PSL) : ℕ :=
  (Monoid.CoprodI.Word.equiv (M := pslFactor) g).toList.length

/-- A group AC move whose target pair has both components of length at most `L`. -/
noncomputable def BoundedStep (L : ℕ) (g h : PSL × PSL) : Prop :=
  GroupACStep PSL g h ∧ pslLength h.1 ≤ L ∧ pslLength h.2 ≤ L

/-- Reachability by bounded group AC moves. -/
noncomputable def BoundedReachable (L : ℕ) : PSL × PSL → PSL × PSL → Prop :=
  Relation.ReflTransGen (BoundedStep L)

/-- The pre-registered verdict of the orbit test.  `outside` is a
non-reachability certificate only when the bounded enumeration is complete;
`inside` is consistent with the Andrews–Curtis relation; `unknown` is an
exhausted bound. -/
inductive OrbitVerdict
  | inside
  | outside
  | unknown

/-- The standard pair is in every bounded orbit (the empty path). -/
theorem standard_mem_bounded (L : ℕ) :
    BoundedReachable L standardPSL standardPSL :=
  Relation.ReflTransGen.refl

/-- A bounded path is an unbounded group AC path. -/
theorem boundedReachable_imp_groupACReachable {L : ℕ} {g h : PSL × PSL}
    (hpath : BoundedReachable L g h) : GroupACReachable PSL g h := by
  induction hpath with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih hstep.1

/-- The verdict counts of the fixed 200-row sample at `L = 12`, as returned by
the external exact enumeration recorded in `BRANCH_C3.md` §5.  This is a record
of the computation, not a kernel-checked theorem. -/
structure OrbitCounts where
  inside : ℕ
  outside : ℕ
  unknown : ℕ
deriving Repr, DecidableEq

/-- The recorded count triple: 168 inside, 0 outside, 32 unknown. -/
def pslSampleCounts : OrbitCounts :=
  { inside := 168, outside := 0, unknown := 32 }

end BranchC3
end AC
