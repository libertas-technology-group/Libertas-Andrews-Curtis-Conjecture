module

/-
# Challenge — Andrews–Curtis, three universal laws

This module is the Palomar challenge module. It imports Mathlib only, so a
reader can reproduce the statements without this project's package.

Three statements, at every rank:

1. `relationSubgroup_eq_top` — for every rank and every balanced presentation
   whose presented group is one-element, the normal closure of the relators is
   the whole free group.
2. `expSpan_eq_top_of_presents` — for every such presentation, the `ℤ`-span of
   the relator exponent vectors is the whole lattice.
3. `expMatrix_det_step` — every official move changes the determinant of the
   exponent matrix by at most a sign.

Two vocabulary lemmas record that conjugation fixes the exponent data:
`expVec_conj` at word level and `expMatrix_conj` at matrix level.

Vocabulary is restated rather than imported because the registry caps the
challenge module's imports to Lean core, Mathlib, Tau Ceti and CSLib.
-/
public import Mathlib

@[expose] public section

namespace ACChallenge

/-- Words on `n` generators. -/
abbrev Word (n : ℕ) : Type := FreeGroup (Fin n)

/-- A balanced presentation: one relator per generator. -/
abbrev Relators (n : ℕ) : Type := Fin n → Word n

/-- The standard tuple: each relator is the corresponding free generator. -/
def standard (n : ℕ) : Relators n := FreeGroup.of

/-- The group presented by a tuple of relators. -/
abbrev PresentedGroup {n : ℕ} (R : Relators n) : Type :=
  Word n ⧸ Subgroup.normalClosure (Set.range R)

/-- The presentation presents the trivial group. -/
def PresentsTrivialGroup {n : ℕ} (R : Relators n) : Prop :=
  Subsingleton (PresentedGroup R)

/-- The normal closure of the relators inside the free group. -/
noncomputable def relationSubgroup {n : ℕ} (R : Relators n) : Subgroup (Word n) :=
  Subgroup.normalClosure (Set.range R)

/-- When the presented group is trivial, the relation subgroup is the whole free
group. -/
theorem relationSubgroup_eq_top {n : ℕ} {R : Relators n}
    (h : PresentsTrivialGroup R) : relationSubgroup R = ⊤ := by
  sorry

/-- A single AC move, fixing the rank and changing only one relator. -/
inductive Step {n : ℕ} : Relators n → Relators n → Prop
  | inv (R : Relators n) (i : Fin n) :
      Step R (Function.update R i (R i)⁻¹)
  | mulRight (R : Relators n) (i j : Fin n) (h : i ≠ j) :
      Step R (Function.update R i (R i * R j))
  | conj (R : Relators n) (i : Fin n) (w : Word n) :
      Step R (Function.update R i (w * R i * w⁻¹))

/-- Existence of a finite sequence of AC moves, including the empty sequence. -/
def Reachable {n : ℕ} : Relators n → Relators n → Prop :=
  Relation.ReflTransGen Step

/-- The vector with value `1` at `i` and value `0` elsewhere. -/
def genVec {n : ℕ} (i : Fin n) : Fin n → ℤ := Pi.single i 1

/-- The exponent-sum homomorphism from the free group on `n` generators to `ℤⁿ`. -/
noncomputable def expHom (n : ℕ) : Word n →* Multiplicative (Fin n → ℤ) :=
  FreeGroup.lift fun i => Multiplicative.ofAdd (genVec i)

/-- The exponent vector of a word: the vector of its letter counts. -/
noncomputable def expVec {n : ℕ} (w : Word n) : Fin n → ℤ :=
  Multiplicative.toAdd (expHom n w)

/-- Conjugation leaves the exponent vector unchanged. -/
theorem expVec_conj {n : ℕ} {r w : Word n} : expVec (w * r * w⁻¹) = expVec r := by
  sorry

/-- The `ℤ`-span of the relator exponent vectors. -/
noncomputable def expSpan {n : ℕ} (R : Relators n) : Submodule ℤ (Fin n → ℤ) :=
  Submodule.span ℤ (Set.range fun i => expVec (R i))

/-- The exponent matrix: row `i` is the exponent vector of relator `i`. -/
noncomputable def expMatrix {n : ℕ} (R : Relators n) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => expVec (R i) j

/-- The conjugation move leaves the exponent matrix untouched. -/
theorem expMatrix_conj {n : ℕ} (R : Relators n) (i : Fin n) (w : Word n) :
    expMatrix (Function.update R i (w * R i * w⁻¹)) = expMatrix R := by
  sorry

/-- The span of the relator exponent vectors is the whole lattice whenever the
presentation presents the trivial group. -/
theorem expSpan_eq_top_of_presents {n : ℕ} {R : Relators n}
    (h : PresentsTrivialGroup R) : expSpan R = ⊤ := by
  sorry

/-- One official move changes the determinant of the exponent matrix by at most
a sign. -/
theorem expMatrix_det_step {n : ℕ} {R S : Relators n} (h : Step R S) :
    (expMatrix S).det = (expMatrix R).det ∨
      (expMatrix S).det = -(expMatrix R).det := by
  sorry

/-- The power family `(x * y ^ n, y)` at rank two, with `x = FreeGroup.of 0`
and `y = FreeGroup.of 1`. -/
def powFamily (n : ℕ) : Relators 2 :=
  Function.update (standard 2) 0 (FreeGroup.of 0 * (FreeGroup.of 1) ^ n)

/-- Every member of the power family reaches the standard pair. -/
theorem reachable_powFamily (n : ℕ) : Reachable (powFamily n) (standard 2) := by
  sorry

/-- No `ℕ`-valued function decreases on every official step at positive rank. -/
theorem no_strictly_decreasing_measure {n : ℕ} (hn : 0 < n) (μ : Relators n → ℕ) :
    ¬ ∀ R S : Relators n, Step R S → μ S < μ R := by
  sorry

/-! ## 6. Stability: inserting an isolated generator–relator pair

The stable move changes the rank. A balanced presentation is carried together
with its rank, and `stabilize` inserts one fresh generator at position `g`
together with the singleton relator on it at position `i`. The inserted pair is
isolated: the new generator occurs in no old relator, and no old generator
occurs in the new relator. -/

/-- A balanced presentation together with its rank, which may change along a
stable path. -/
abbrev Presentation := (n : ℕ) × Relators n

/-- Insert a fresh generator at position `g` and its singleton relator at
position `i`. The injection `g.succAbove` relabels the old generators while
skipping the new one; `Fin.insertNth` retains all old relators, in their original
relative order. -/
def stabilize {n : ℕ} (R : Relators n) (g i : Fin (n + 1)) : Relators (n + 1) :=
  Fin.insertNth i (FreeGroup.of g) (fun j => FreeGroup.map g.succAbove (R j))

/-- A stable AC move is an ordinary AC move, insertion of an isolated
generator–relator pair, or the exact reverse of such an insertion. -/
inductive StableStep : Presentation → Presentation → Prop
  | ac {n : ℕ} {R S : Relators n} (h : Step R S) :
      StableStep ⟨n, R⟩ ⟨n, S⟩
  | stabilize {n : ℕ} (R : Relators n) (g i : Fin (n + 1)) :
      StableStep ⟨n, R⟩ ⟨n + 1, stabilize R g i⟩
  | destabilize {n : ℕ} (R : Relators n) (g i : Fin (n + 1)) :
      StableStep ⟨n + 1, stabilize R g i⟩ ⟨n, R⟩

/-- Inserting an isolated generator–relator pair preserves the property that
the exponent span is the whole lattice, in both directions. -/
theorem expSpan_stabilize_eq_top_iff {n : ℕ} (R : Relators n) (g i : Fin (n + 1)) :
    expSpan (stabilize R g i) = ⊤ ↔ expSpan R = ⊤ := by
  sorry

/-- Every stable step preserves the proposition that the exponent span is the
whole lattice, in both directions. -/
theorem stableStep_expSpan_top {P Q : Presentation} (h : StableStep P Q) :
    (expSpan P.2 = ⊤ ↔ expSpan Q.2 = ⊤) := by
  sorry

end ACChallenge
