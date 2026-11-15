module

/-
# AcBS23Conjugacy — cyclic shifts on the HNN normal form

The file supplies the forward half of the Britton conjugacy lane. A cyclic shift
of the stable-letter list preserves the conjugacy class of the product. For a
normal word with trivial head and a wrap-around chain link, one-step rotation is
again a normal word, rotates the exponent list, and preserves the conjugacy
class. The converse invariant and the target decision are separate steps.
-/
public import Mathlib.GroupTheory.HNNExtension
public import Mathlib.Data.List.Rotate
public import Mathlib.Algebra.Group.Conj

@[expose] public section

set_option autoImplicit false

namespace AC
namespace BS23Cyclic

open HNNExtension

variable {G : Type*} [Group G] {A B : Subgroup G} {φ : A ≃* B}

/-- The product of a list of stable-letter letters `t^u * of g`, as an element of the HNN
extension. This is exactly the tail factor of `ReducedWord.prod`. -/
def letterProd (l : List (ℤˣ × G)) : HNNExtension G A B φ :=
  (l.map (fun x => t ^ (x.1 : ℤ) * of x.2)).prod

@[simp] theorem letterProd_nil : letterProd (φ := φ) ([] : List (ℤˣ × G)) = 1 := rfl

@[simp] theorem letterProd_cons (a : ℤˣ × G) (l : List (ℤˣ × G)) :
    letterProd (φ := φ) (a :: l) = (t ^ (a.1 : ℤ) * of a.2) * letterProd (φ := φ) l := by
  simp [letterProd, List.prod_cons]

theorem letterProd_append (l₁ l₂ : List (ℤˣ × G)) :
    letterProd (φ := φ) (l₁ ++ l₂) = letterProd (φ := φ) l₁ * letterProd (φ := φ) l₂ := by
  simp [letterProd, List.map_append, List.prod_append]

/-- The product of two factors rotates: `a * b` is conjugate to `b * a`. -/
theorem isConj_mul_rotate (a b : HNNExtension G A B φ) :
    IsConj (a * b) (b * a) := by
  rw [isConj_iff]
  exact ⟨a⁻¹, by simp⟩

/-- A cyclic shift of the letter list preserves the conjugacy class of the product. -/
theorem isConj_letterProd_append (l₁ l₂ : List (ℤˣ × G)) :
    IsConj (letterProd (φ := φ) (l₁ ++ l₂)) (letterProd (φ := φ) (l₂ ++ l₁)) := by
  rw [letterProd_append, letterProd_append]
  exact isConj_mul_rotate _ _

/-- Every rotation preserves the conjugacy class of the product. -/
theorem isConj_letterProd_rotate (l : List (ℤˣ × G)) (n : ℕ) :
    IsConj (letterProd (φ := φ) (l.rotate n)) (letterProd (φ := φ) l) := by
  induction n generalizing l with
  | zero => simpa using IsConj.refl (letterProd (φ := φ) l)
  | succ n ih =>
    cases l with
    | nil => simp
    | cons a t =>
      rw [List.rotate_cons_succ]
      refine (ih (t ++ [a])).trans ?_
      have hsplit : letterProd (φ := φ) (a :: t) =
          letterProd (φ := φ) [a] * letterProd (φ := φ) t := by
        rw [← letterProd_append]
        rfl
      rw [letterProd_append, hsplit]
      exact (isConj_mul_rotate _ _).symm

/-- `List.IsRotated` transports to conjugacy of the letter product. -/
theorem isConj_letterProd_of_isRotated {l l' : List (ℤˣ × G)} (h : l ~r l') :
    IsConj (letterProd (φ := φ) l') (letterProd (φ := φ) l) := by
  obtain ⟨n, rfl⟩ := h
  exact isConj_letterProd_rotate l n

variable {d : HNNExtension.NormalWord.TransversalPair G A B}

/-- `NormalWord.prod` is definitionally the head followed by the letter product. -/
theorem prod_eq_head_mul_letterProd (w : HNNExtension.NormalWord d) :
    w.prod φ = of w.head * letterProd (φ := φ) w.toList := rfl

/-- Cycling the head past the whole letter list preserves the conjugacy class. -/
theorem isConj_prod_letterProd_head (w : HNNExtension.NormalWord d) :
    IsConj (w.prod φ) (letterProd (φ := φ) w.toList * of w.head) := by
  rw [prod_eq_head_mul_letterProd]
  exact isConj_mul_rotate _ _

/-- The chain relation carried by `NormalWord`, named. -/
def hnnChainRel : ℤˣ × G → ℤˣ × G → Prop :=
  fun a b => a.2 ∈ HNNExtension.toSubgroup A B a.1 → a.1 = b.1

/-- The wrap-around link: the last letter may not cancel against the first. -/
def CyclicChain (w : HNNExtension.NormalWord d) : Prop :=
  ∀ x ∈ w.toList.getLast?, ∀ y ∈ w.toList.head?, hnnChainRel (A := A) (B := B) x y

/-- A chain plus its wrap-around link survives one-step rotation. -/
theorem isChain_rotate_one {α : Type*} {R : α → α → Prop} {l : List α}
    (h : l.IsChain R) (hcyc : ∀ x ∈ l.getLast?, ∀ y ∈ l.head?, R x y) :
    (l.rotate 1).IsChain R := by
  match l with
  | [] => exact List.isChain_nil
  | [_] => simp
  | a :: b :: t =>
    rw [List.rotate_cons_succ, List.rotate_zero]
    refine List.IsChain.append (List.IsChain.tail h) (List.isChain_singleton a) ?_
    intro x hx y hy
    have hya : a = y := by simpa using hy
    subst y
    exact hcyc x (by simpa using hx) a rfl

/-- The chain relation is reflexive: a one-letter word never cancels against itself. -/
theorem hnnChainRel_refl (a : ℤˣ × G) : hnnChainRel (A := A) (B := B) a a := by
  intro _
  rfl

/-- The wrap-around link also survives one-step rotation. -/
theorem cyclicWrap_rotate_one {α : Type*} {R : α → α → Prop} (hrefl : ∀ a, R a a)
    {l : List α} (h : l.IsChain R) (hcyc : ∀ x ∈ l.getLast?, ∀ y ∈ l.head?, R x y) :
    ∀ x ∈ (l.rotate 1).getLast?, ∀ y ∈ (l.rotate 1).head?, R x y := by
  match l with
  | [] => simp
  | [a] => simpa using hrefl a
  | a :: b :: t =>
    intro x hx y hy
    rw [List.rotate_cons_succ, List.rotate_zero] at hx hy
    have hx' : x = a := by
      rw [List.getLast?_append_of_ne_nil (b :: t) (l₂ := [a]) (by simp)] at hx
      simpa [eq_comm] using hx
    have hy' : y = b := by
      have hb : ((b :: t) ++ [a]).head? = some b := by simp
      rw [hb] at hy
      simpa [eq_comm] using hy
    subst hx'
    subst hy'
    have hlink := (List.isChain_cons.mp h).1
    simpa using hlink

/-- One-step rotation of a cyclically reduced normal word with trivial head. -/
def rotateOne (w : HNNExtension.NormalWord d) (hc : CyclicChain (A := A) (B := B) w) :
    HNNExtension.NormalWord d where
  head := w.head
  toList := w.toList.rotate 1
  mem_set := by
    intro u g hg
    exact w.mem_set u g (List.mem_rotate.mp hg)
  chain := isChain_rotate_one w.chain (fun x hx y hy => hc x hx y hy)

/-- Rotation of a cyclically reduced normal word is a normal word whose product is the
rotated letter product. -/
theorem rotateOne_prod (w : HNNExtension.NormalWord d)
    (hc : CyclicChain (A := A) (B := B) w) (hhead : w.head = 1) :
    (rotateOne w hc).prod φ = letterProd (φ := φ) (w.toList.rotate 1) := by
  rw [prod_eq_head_mul_letterProd]
  simp [rotateOne, hhead]

/-- **Cyclic shift preserves conjugacy**, at the level of `NormalWord`. -/
theorem isConj_rotateOne (w : HNNExtension.NormalWord d)
    (hc : CyclicChain (A := A) (B := B) w) (hhead : w.head = 1) :
    IsConj ((rotateOne w hc).prod φ) (w.prod φ) := by
  rw [rotateOne_prod w hc hhead, prod_eq_head_mul_letterProd, hhead]
  simpa using isConj_letterProd_rotate (φ := φ) w.toList 1

/-- The stable-letter exponent list of a normal word. -/
def exponentList (w : HNNExtension.NormalWord d) : List ℤˣ :=
  w.toList.map Prod.fst

/-- The exponent list of a rotated word is the rotation of the exponent list. -/
theorem exponentList_rotateOne (w : HNNExtension.NormalWord d)
    (hc : CyclicChain (A := A) (B := B) w) :
    exponentList w ~r exponentList (rotateOne w hc) := by
  refine ⟨1, ?_⟩
  show (w.toList.map Prod.fst).rotate 1 = (rotateOne w hc).toList.map Prod.fst
  rw [show (rotateOne w hc).toList = w.toList.rotate 1 from rfl, List.map_rotate]

/-- One-step rotation preserves the cyclic-chain condition. -/
theorem cyclicChain_rotateOne (w : HNNExtension.NormalWord d)
    (hc : CyclicChain (A := A) (B := B) w) :
    CyclicChain (A := A) (B := B) (rotateOne w hc) :=
  cyclicWrap_rotate_one (hnnChainRel_refl (A := A) (B := B)) w.chain hc

/-- **The cyclic shift family.** For every `n`, a cyclically reduced normal word with trivial
head has an `n`-th cyclic shift that stays cyclically reduced with trivial head, has the `n`-th
rotation of the stable-letter exponent list, and has a conjugate product. -/
theorem exists_rotateN (w : HNNExtension.NormalWord d)
    (hc : CyclicChain (A := A) (B := B) w) (hhead : w.head = 1) (n : ℕ) :
    ∃ v : HNNExtension.NormalWord d,
      CyclicChain (A := A) (B := B) v ∧ v.head = 1 ∧
      exponentList v ~r exponentList w ∧ IsConj (v.prod φ) (w.prod φ) := by
  induction n with
  | zero => exact ⟨w, hc, hhead, List.IsRotated.refl _, IsConj.refl _⟩
  | succ n ih =>
    obtain ⟨v, hcv, hvhead, hrot, hconj⟩ := ih
    exact ⟨rotateOne v hcv, cyclicChain_rotateOne v hcv, by simpa [rotateOne] using hvhead,
      (exponentList_rotateOne v hcv).symm.trans hrot,
      (isConj_rotateOne v hcv hvhead).trans hconj⟩


/-- The cancelling branch removes the first stable letter. -/
theorem unitsSMulWithCancel_toList (u : ℤˣ) (w : HNNExtension.NormalWord d)
    (h : HNNExtension.NormalWord.Cancels (A := A) (B := B) u w) :
    (HNNExtension.NormalWord.unitsSMulWithCancel φ u w h).toList = w.toList.tail := by
  induction w using HNNExtension.NormalWord.consRecOn with
  | ofGroup g =>
      simp [HNNExtension.NormalWord.Cancels, HNNExtension.NormalWord.ofGroup] at h
  | cons g u' w h1 h2 ih =>
      rw [HNNExtension.NormalWord.unitsSMulWithCancel, HNNExtension.NormalWord.consRecOn_cons]
      simp

/-- One stable-letter action prepends its exponent or cancels the first exponent. -/
theorem unitsSMul_toList_map_fst (u : ℤˣ) (w : HNNExtension.NormalWord d) :
    (HNNExtension.NormalWord.unitsSMul φ u w).toList.map Prod.fst =
        u :: w.toList.map Prod.fst ∨
      ∃ v : List ℤˣ,
        w.toList.map Prod.fst = -u :: v ∧
          (HNNExtension.NormalWord.unitsSMul φ u w).toList.map Prod.fst = v := by
  by_cases h : HNNExtension.NormalWord.Cancels (A := A) (B := B) u w
  · right
    refine ⟨(w.toList.map Prod.fst).tail, ?_, ?_⟩
    · cases hw : w.toList with
      | nil => simp [hw, HNNExtension.NormalWord.Cancels] at h
      | cons a l =>
          have hhead := h.2
          rw [hw] at hhead
          simpa using hhead
    · rw [HNNExtension.NormalWord.unitsSMul, dite_eq_left h, unitsSMulWithCancel_toList]
      simp
  · left
    rw [HNNExtension.NormalWord.unitsSMul, dite_eq_right h]
    simp


/-- One stable-letter action changes the exponent-list length by one. -/
theorem unitsSMul_toList_length (u : ℤˣ) (w : HNNExtension.NormalWord d) :
    (HNNExtension.NormalWord.unitsSMul φ u w).toList.length = w.toList.length + 1 ∨
      (HNNExtension.NormalWord.unitsSMul φ u w).toList.length + 1 = w.toList.length := by
  rcases unitsSMul_toList_map_fst (A := A) (B := B) (φ := φ) u w with h | ⟨v, hv, hw⟩
  · left
    have := congrArg List.length h
    simpa using this
  · right
    have hlen_w : w.toList.length = v.length + 1 := by
      have := congrArg List.length hv
      simpa using this
    have hlen_u : (HNNExtension.NormalWord.unitsSMul φ u w).toList.length = v.length := by
      have := congrArg List.length hw
      simpa using this
    omega

end BS23Cyclic
end AC
