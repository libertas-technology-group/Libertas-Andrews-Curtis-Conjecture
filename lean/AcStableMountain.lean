import AC
import BranchD

/-!
# AcStableMountain — the stable AC mountain normal-form statement

This module carries the mountain normal-form proposition of the stable
Andrews–Curtis candidate statement as a proposition-valued definition. It declares no
theorem, because the proposition is open: the statement record
`STABLE_AC_MOUNTAIN.md` fixes the definitions and claims no proof.

`StablePath` is the data-carrying counterpart of `AC.StableReachable`
(`AC.lean:103-104`), whose constructors are the empty path and extension by one
`AC.StableStep` (`AC.lean:93-99`). The rank trace reads `BranchD.rankOf`
(`BranchD.lean:96`) at every state, and `OnePeak` asks for one ascent followed
by one descent. `MountainNormalForm` states that every stable-reachable pair
has a one-peak path with the same endpoints.

The two theorem contracts of the statement record are not declared here. This
module supplies the definitions they quantify over:
`AC.StableMountain.stableReachable_mountain_normalForm` (the normal-form
declaration, whose proof is the open obligation) and
`AC.StableMountain.stablePath_nonempty_of_stableReachable` (the path bridge).
-/

set_option autoImplicit false

namespace AC
namespace StableMountain

/-- A finite stable path, as data: a starting presentation and a chain of stable steps. -/
inductive StablePath : Presentation → Presentation → Type
  | refl (P : Presentation) : StablePath P P
  | tail {P Q R : Presentation} (p : StablePath P Q) (h : StableStep Q R) : StablePath P R

namespace StablePath

/-- The target presentation of a stable step. -/
def targetOfStep {P Q : Presentation} (_ : StableStep P Q) : Presentation := Q

/-- The rank trace: the rank of every state of the path, in order. -/
def rankTrace : {P Q : Presentation} → StablePath P Q → List ℕ
  | _, _, .refl P => [BranchD.rankOf P]
  | _, _, .tail p h => rankTrace p ++ [BranchD.rankOf (targetOfStep h)]

end StablePath

/-- A list is nondecreasing at adjacent pairs. -/
def Nondecreasing : List ℕ → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => a ≤ b ∧ Nondecreasing (b :: rest)

/-- A list is nonincreasing at adjacent pairs. -/
def Nonincreasing : List ℕ → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => b ≤ a ∧ Nonincreasing (b :: rest)

/-- A path is one-peak when its rank trace rises to a peak index and then falls. -/
def OnePeak {P Q : Presentation} (p : StablePath P Q) : Prop :=
  ∃ k : ℕ, k < p.rankTrace.length ∧
    Nondecreasing (p.rankTrace.take (k + 1)) ∧
    Nonincreasing (p.rankTrace.drop k)

/-- Every stable path has a one-peak stable path with the same endpoints. -/
def MountainNormalForm : Prop :=
  ∀ {P Q : Presentation}, StableReachable P Q → ∃ q : StablePath P Q, OnePeak q

/-- The mountain normal form, named as the first lemma of the statement, stated without proof. -/
def stableReachable_mountain_normalForm_statement : Prop := MountainNormalForm

end StableMountain
end AC
