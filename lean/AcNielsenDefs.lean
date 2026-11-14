/-
# Definitions for the cyclic Nielsen measure

This module supplies the three definitions the cyclic Nielsen attack imports:
the cyclic length of one word, the cyclic Nielsen length of a relator tuple,
and the abelian-terminal predicate. The bodies are those of the session source
`AcNielsen.lean:191`, `AcNielsen.lean:196`, and `AcNielsen.lean:345`; nothing is
restated in a different form. The module carries no proofs and no assumptions.
-/

import AC
import AcInvariant
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

set_option autoImplicit false

open scoped BigOperators

namespace AC
namespace Nielsen

variable {n : ℕ}

/-- The length of the cyclically reduced representative of a free-group word. -/
noncomputable def cycLen (w : Word n) : ℕ :=
  (FreeGroup.reduceCyclically w.toWord).length

/-- The cyclic Nielsen length of a relator tuple: the sum of the cyclically
reduced lengths of its entries. -/
noncomputable def cyclicNielsenLength (R : Relators n) : ℕ :=
  ∑ i : Fin n, cycLen (R i)

/-- The abelian-terminal set at rank `n`: the exponent vectors of the relators
are the signed standard basis vectors, and the assignment of basis vectors to
relator positions is a bijection. This is the body of
`AC.BranchA.IsAbelianTerminal`, expressed against `AC.Invariant` so this module
does not depend on the branch file. -/
def AbelianTerminal {n : ℕ} (R : Relators n) : Prop :=
  ∃ σ : Fin n → Fin n, Function.Bijective σ ∧ ∃ ε : Fin n → Bool,
    ∀ i : Fin n, Invariant.expVec (R i) =
      if ε i then Invariant.genVec (σ i) else -Invariant.genVec (σ i)

end Nielsen
end AC
