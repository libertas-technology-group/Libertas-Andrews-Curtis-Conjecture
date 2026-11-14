import AC
import AcInvariant

/-!
# Exponent-span transport across stable insertion

`AcInvariant.step_expSpan` shows that every ordinary AC move preserves the exponent
span. The stable move `AC.stabilize` inserts one generator together with the singleton
relator on it. This file proves that insertion preserves the property that the span is
the whole space, and that the implication is reversible, so a `StableStep` preserves
that property in both directions.

The transport map `tau g` embeds the old exponent vectors into the hyperplane of the
new space on which the new coordinate vanishes; the inserted relator contributes the
complementary coordinate vector `genVec g`.
-/

namespace AC
namespace StabilityTransport

variable {n : ℕ}

open Invariant

/-! ## 1. The insertion map on exponent vectors -/

/-- Insert the new coordinate `0` at position `g` and copy the old coordinates into
the remaining positions along `Fin.succAbove g`. This is the exponent-vector image of
`FreeGroup.map g.succAbove`. -/
def tau (g : Fin (n + 1)) (v : Fin n → ℤ) : Fin (n + 1) → ℤ :=
  Fin.insertNth g 0 v

@[simp] theorem tau_apply_self (g : Fin (n + 1)) (v : Fin n → ℤ) : tau g v g = 0 :=
  Fin.insertNth_apply_same (α := fun _ => ℤ) g 0 v

@[simp] theorem tau_apply_succAbove (g : Fin (n + 1)) (v : Fin n → ℤ) (y : Fin n) :
    tau g v (g.succAbove y) = v y :=
  Fin.insertNth_apply_succAbove (α := fun _ => ℤ) g 0 v y

theorem tau_zero (g : Fin (n + 1)) : tau g (0 : Fin n → ℤ) = 0 := by
  funext x
  obtain hx | ⟨y, rfl⟩ := Fin.eq_self_or_eq_succAbove g x
  · rw [hx]; simp
  · simp

theorem tau_add (g : Fin (n + 1)) (u v : Fin n → ℤ) :
    tau g (u + v) = tau g u + tau g v := by
  funext x
  obtain hx | ⟨y, rfl⟩ := Fin.eq_self_or_eq_succAbove g x
  · rw [hx]; simp
  · simp [Pi.add_apply]

theorem tau_smul (g : Fin (n + 1)) (c : ℤ) (v : Fin n → ℤ) :
    tau g (c • v) = c • tau g v := by
  funext x
  obtain hx | ⟨y, rfl⟩ := Fin.eq_self_or_eq_succAbove g x
  · rw [hx]; simp
  · simp [Pi.smul_apply]

/-- The bundled additive form of `tau g`. -/
def tauAdd (g : Fin (n + 1)) : (Fin n → ℤ) →+ (Fin (n + 1) → ℤ) where
  toFun := tau g
  map_zero' := tau_zero g
  map_add' := tau_add g

/-- The bundled `ℤ`-linear form of `tau g`. -/
def tauLin (g : Fin (n + 1)) : (Fin n → ℤ) →ₗ[ℤ] (Fin (n + 1) → ℤ) where
  toFun := tau g
  map_add' := tau_add g
  map_smul' := tau_smul g

/-- The multiplicative form used to compare with the exponent homomorphism. -/
def tauMul (g : Fin (n + 1)) :
    Multiplicative (Fin n → ℤ) →* Multiplicative (Fin (n + 1) → ℤ) where
  toFun v := Multiplicative.ofAdd (tau g v.toAdd)
  map_one' := by simp [tau_zero]
  map_mul' := by intro a b; simp [tau_add, toAdd_mul, ofAdd_add]

@[simp] theorem tauMul_ofAdd (g : Fin (n + 1)) (v : Fin n → ℤ) :
    tauMul g (Multiplicative.ofAdd v) = Multiplicative.ofAdd (tau g v) := by
  simp [tauMul]

/-- The coordinate projection that forgets the new coordinate and reads the old
coordinates along `Fin.succAbove g`. -/
def proj (g : Fin (n + 1)) : (Fin (n + 1) → ℤ) →ₗ[ℤ] (Fin n → ℤ) where
  toFun w := fun y => w (g.succAbove y)
  map_add' := by intro a b; rfl
  map_smul' := by intro c a; rfl

@[simp] theorem proj_tau (g : Fin (n + 1)) (v : Fin n → ℤ) : proj g (tau g v) = v := by
  funext y
  simp [proj]

@[simp] theorem proj_genVec (g : Fin (n + 1)) : proj g (genVec g) = 0 := by
  funext y
  simp [proj, genVec]

/-- On the old basis, `tau` is the insertion. -/
theorem genVec_succAbove (g : Fin (n + 1)) (y : Fin n) :
    genVec (g.succAbove y) = tau g (genVec y) := by
  funext x
  obtain hx | ⟨z, rfl⟩ := Fin.eq_self_or_eq_succAbove g x
  · rw [hx]
    simp [genVec]
  · simp [genVec, Pi.single_apply]

/-! ## 2. Exponent vectors of the stabilized relators -/

/-- The exponent homomorphism commutes with insertion of the new generator. -/
theorem expHom_map_succAbove (g : Fin (n + 1)) :
    (expHom (n + 1)).comp (FreeGroup.map (Fin.succAbove g)) =
      (tauMul g).comp (expHom n) := by
  apply FreeGroup.ext_hom
  intro y
  simp only [MonoidHom.comp_apply, FreeGroup.map.of, expHom, FreeGroup.lift_apply_of,
    tauMul_ofAdd]
  rw [genVec_succAbove]

/-- The exponent vector of an old relator, pushed into the new generator type. -/
theorem expVec_map_succAbove (g : Fin (n + 1)) (w : Word n) :
    expVec (FreeGroup.map (Fin.succAbove g) w) = tau g (expVec w) := by
  have h := DFunLike.congr_fun (expHom_map_succAbove g) w
  simpa [expVec, tauMul, tauAdd] using h

/-- (a) The inserted relator has exponent vector the new basis vector. -/
theorem expVec_stabilize_self (R : Relators n) (g i : Fin (n + 1)) :
    expVec ((stabilize R g i) i) = genVec g := by
  rw [show stabilize R g i i = FreeGroup.of g from Fin.insertNth_apply_same i _ _]
  simp [expVec, expHom, genVec]

/-- (b) Each old relator is carried by `tau`. -/
theorem expVec_stabilize_succAbove (R : Relators n) (g i : Fin (n + 1)) (j : Fin n) :
    expVec ((stabilize R g i) (i.succAbove j)) = tau g (expVec (R j)) := by
  rw [show stabilize R g i (i.succAbove j) = FreeGroup.map g.succAbove (R j) from
    Fin.insertNth_apply_succAbove i _ _ j]
  exact expVec_map_succAbove g (R j)

/-! ## 3. The span is transported onto the whole space -/

/-- The image under `tau` of any element of the old span lies in the new span. -/
theorem tau_mem_expSpan_stabilize (R : Relators n) (g i : Fin (n + 1))
    {u : Fin n → ℤ} (hu : u ∈ expSpan R) :
    tau g u ∈ expSpan (stabilize R g i) := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [← expVec_stabilize_succAbove R g i j]
      exact expVec_mem_expSpan _ (i.succAbove j)
  | zero =>
      rw [tau_zero]
      exact (expSpan (stabilize R g i)).zero_mem
  | add x y _ _ ihx ihy =>
      rw [tau_add]
      exact (expSpan (stabilize R g i)).add_mem ihx ihy
  | smul c x _ ih =>
      rw [tau_smul]
      exact (expSpan (stabilize R g i)).smul_mem c ih

/-- The inserted basis vector lies in the new span. -/
theorem genVec_mem_expSpan_stabilize (R : Relators n) (g i : Fin (n + 1)) :
    genVec g ∈ expSpan (stabilize R g i) := by
  rw [← expVec_stabilize_self R g i]
  exact expVec_mem_expSpan _ i

/-- (c) A top old span gives a top new span. -/
theorem expSpan_stabilize_top (R : Relators n) (g i : Fin (n + 1))
    (hR : expSpan R = ⊤) : expSpan (stabilize R g i) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro v
  have hu : (fun y : Fin n => v (g.succAbove y)) ∈ expSpan R := by
    rw [hR]; exact Submodule.mem_top
  have ht := tau_mem_expSpan_stabilize R g i hu
  have hdecomp : v = tau g (fun y : Fin n => v (g.succAbove y)) + v g • genVec g := by
    funext x
    obtain hx | ⟨y, rfl⟩ := Fin.eq_self_or_eq_succAbove g x
    · subst hx; simp [tau, genVec]
    · simp [tau, genVec]
  rw [hdecomp]
  exact (expSpan (stabilize R g i)).add_mem ht
    ((expSpan (stabilize R g i)).smul_mem (v g) (genVec_mem_expSpan_stabilize R g i))

/-- The projection of the new span is the old span. -/
theorem map_proj_expSpan_stabilize (R : Relators n) (g i : Fin (n + 1)) :
    Submodule.map (proj g) (expSpan (stabilize R g i)) = expSpan R := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    change expVec (stabilize R g i k) ∈ Submodule.comap (proj g) (expSpan R)
    rw [Submodule.mem_comap]
    rcases Fin.eq_self_or_eq_succAbove i k with hk | ⟨j, rfl⟩
    · subst hk
      rw [expVec_stabilize_self, proj_genVec]
      exact (expSpan R).zero_mem
    · rw [expVec_stabilize_succAbove, proj_tau]
      exact expVec_mem_expSpan R j
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    have hmem : expVec ((stabilize R g i) (i.succAbove j)) ∈ expSpan (stabilize R g i) :=
      expVec_mem_expSpan _ _
    have hmap := Submodule.mem_map_of_mem (f := proj g) hmem
    rwa [expVec_stabilize_succAbove, proj_tau] at hmap

/-- (d) The old span is top exactly when the new span is. -/
theorem expSpan_stabilize_eq_top_iff (R : Relators n) (g i : Fin (n + 1)) :
    expSpan (stabilize R g i) = ⊤ ↔ expSpan R = ⊤ := by
  constructor
  · intro h
    have hmap := map_proj_expSpan_stabilize R g i
    rw [h, Submodule.map_top] at hmap
    rw [← hmap]
    exact LinearMap.range_eq_top.mpr (fun u => ⟨tau g u, proj_tau g u⟩)
  · intro h
    exact expSpan_stabilize_top R g i h

/-! ## 4. A stable step preserves the top-span property in both directions -/

/-- (e) Every stable step preserves the proposition that the exponent span is top. -/
theorem stableStep_expSpan_top {P Q : Presentation} (h : StableStep P Q) :
    (expSpan P.2 = ⊤ ↔ expSpan Q.2 = ⊤) := by
  cases h with
  | ac hstep =>
      constructor
      · intro hP; rw [step_expSpan hstep]; exact hP
      · intro hQ; rw [← step_expSpan hstep]; exact hQ
  | stabilize R g i =>
      exact (expSpan_stabilize_eq_top_iff R g i).symm
  | destabilize R g i =>
      exact expSpan_stabilize_eq_top_iff R g i

end StabilityTransport
end AC
