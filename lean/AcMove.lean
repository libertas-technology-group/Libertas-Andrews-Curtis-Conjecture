import AC

/-!
# Move grammar for the Andrews–Curtis relation

`AcMove` is the syntactic grammar of the three elementary moves in `AC.Step`.
`AcMove.toStep` interprets a grammar move as an official step. `AcMove.step_iff`
and `AcMove.toStep_surjective` state that the grammar generates exactly the
official relation: every official step parses to a grammar move, and every
grammar move interprets to an official step.
-/

namespace AC

/-- The three elementary Andrews–Curtis moves, as syntax. -/
inductive AcMove (n : ℕ) : Relators n → Relators n → Type
  | inv (R : Relators n) (i : Fin n) :
      AcMove n R (Function.update R i (R i)⁻¹)
  | mulRight (R : Relators n) (i j : Fin n) (h : i ≠ j) :
      AcMove n R (Function.update R i (R i * R j))
  | conj (R : Relators n) (i : Fin n) (w : Word n) :
      AcMove n R (Function.update R i (w * R i * w⁻¹))

/-- Interpret one grammar move as an official `AC.Step`. -/
theorem AcMove.toStep {n : ℕ} {R S : Relators n} (m : AcMove n R S) : Step R S := by
  cases m with
  | inv i => exact Step.inv R i
  | mulRight i j hij => exact Step.mulRight R i j hij
  | conj i w => exact Step.conj R i w

/-- Every official step parses to a grammar move, and every grammar move
interprets to an official step. -/
theorem AcMove.step_iff {n : ℕ} {R S : Relators n} :
    Step R S ↔ Nonempty (AcMove n R S) := by
  constructor
  · intro h
    cases h with
    | inv i => exact ⟨AcMove.inv R i⟩
    | mulRight i j hij => exact ⟨AcMove.mulRight R i j hij⟩
    | conj i w => exact ⟨AcMove.conj R i w⟩
  · intro h
    obtain ⟨m⟩ := h
    exact m.toStep

/-- Each official step is the interpretation of a grammar move. -/
theorem AcMove.toStep_surjective {n : ℕ} {R S : Relators n} (h : Step R S) :
    ∃ m : AcMove n R S, m.toStep = h := by
  cases h with
  | inv i => exact ⟨AcMove.inv R i, rfl⟩
  | mulRight i j hij => exact ⟨AcMove.mulRight R i j hij, rfl⟩
  | conj i w => exact ⟨AcMove.conj R i w, rfl⟩

end AC
