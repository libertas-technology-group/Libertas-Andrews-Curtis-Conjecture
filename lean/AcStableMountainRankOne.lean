import AcStableMountain

/-!
# AcStableMountainRankOne — the rank-one mountain subgoal

The general mountain normal form is `AC.StableMountain.MountainNormalForm`
(`AcStableMountain.lean:66-68`). This file records the rank-one specialization
as a proposition-valued definition. It does not claim a proof. The rank-one
case is separated from the general statement because the rank trace
`BranchD.rankOf` is constant on the standard rank-one presentation, while a
stable path can still leave and return to rank one.
-/

set_option autoImplicit false

namespace AC
namespace StableMountain

/-- Every stable path between rank-one presentations has a one-peak path with
the same endpoints. -/
def MountainNormalFormRankOne : Prop :=
  ∀ {P Q : Presentation}, P.1 = 1 → Q.1 = 1 → StableReachable P Q →
    ∃ q : StablePath P Q, OnePeak q

/-- The rank-one mountain subgoal, named without proof. -/
def mountainNormalFormRankOne_statement : Prop := MountainNormalFormRankOne

end StableMountain
end AC

#check @AC.StableMountain.MountainNormalFormRankOne
#check @AC.StableMountain.mountainNormalFormRankOne_statement
