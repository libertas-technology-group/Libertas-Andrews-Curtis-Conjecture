/-
# Solution — Andrews–Curtis, three universal laws

Same declarations and types as `Challenge.lean`, with proofs. The duplicated
vocabulary is deliberate: Comparator compares the two modules by name and type,
and the challenge module may not import this project.

Axioms used: `propext`, `Classical.choice`, `Quot.sound`. No `sorryAx`.
-/
import Mathlib

namespace ACChallenge

abbrev Word (n : ℕ) : Type := FreeGroup (Fin n)

abbrev Relators (n : ℕ) : Type := Fin n → Word n

def standard (n : ℕ) : Relators n := FreeGroup.of

abbrev PresentedGroup {n : ℕ} (R : Relators n) : Type :=
  Word n ⧸ Subgroup.normalClosure (Set.range R)

def PresentsTrivialGroup {n : ℕ} (R : Relators n) : Prop :=
  Subsingleton (PresentedGroup R)

noncomputable def relationSubgroup {n : ℕ} (R : Relators n) : Subgroup (Word n) :=
  Subgroup.normalClosure (Set.range R)

/-- When the presented group is trivial, the relation subgroup is the whole free
group. The quotient by the normal closure is one-element, so every word lies in
the normal closure. -/
theorem relationSubgroup_eq_top {n : ℕ} {R : Relators n}
    (h : PresentsTrivialGroup R) : relationSubgroup R = ⊤ := by
  haveI : (relationSubgroup R).Normal := by
    unfold relationSubgroup
    infer_instance
  rw [eq_top_iff]
  intro w _
  haveI : Subsingleton (Word n ⧸ relationSubgroup R) := h
  have h1 : (QuotientGroup.mk w : Word n ⧸ relationSubgroup R) = 1 :=
    Subsingleton.elim _ _
  exact (QuotientGroup.eq_one_iff w).mp h1

inductive Step {n : ℕ} : Relators n → Relators n → Prop
  | inv (R : Relators n) (i : Fin n) :
      Step R (Function.update R i (R i)⁻¹)
  | mulRight (R : Relators n) (i j : Fin n) (h : i ≠ j) :
      Step R (Function.update R i (R i * R j))
  | conj (R : Relators n) (i : Fin n) (w : Word n) :
      Step R (Function.update R i (w * R i * w⁻¹))

def Reachable {n : ℕ} : Relators n → Relators n → Prop :=
  Relation.ReflTransGen Step

/-! ## 1. The exponent vector and its span -/

def genVec {n : ℕ} (i : Fin n) : Fin n → ℤ := Pi.single i 1

noncomputable def expHom (n : ℕ) : Word n →* Multiplicative (Fin n → ℤ) :=
  FreeGroup.lift fun i => Multiplicative.ofAdd (genVec i)

noncomputable def expVec {n : ℕ} (w : Word n) : Fin n → ℤ :=
  Multiplicative.toAdd (expHom n w)

@[simp] theorem expVec_one {n : ℕ} : expVec (1 : Word n) = 0 := by
  simp [expVec]

theorem expVec_mul {n : ℕ} {u v : Word n} : expVec (u * v) = expVec u + expVec v := by
  simp [expVec, map_mul]

theorem expVec_inv {n : ℕ} {w : Word n} : expVec w⁻¹ = -expVec w := by
  have h : expVec w + expVec w⁻¹ = 0 := by
    rw [← expVec_mul, mul_inv_cancel, expVec_one]
  exact eq_neg_of_add_eq_zero_right h

theorem expVec_conj {n : ℕ} {r w : Word n} : expVec (w * r * w⁻¹) = expVec r := by
  rw [expVec_mul, expVec_mul, expVec_inv]
  abel

noncomputable def expSpan {n : ℕ} (R : Relators n) : Submodule ℤ (Fin n → ℤ) :=
  Submodule.span ℤ (Set.range fun i => expVec (R i))

theorem expVec_mem_expSpan {n : ℕ} (R : Relators n) (j : Fin n) :
    expVec (R j) ∈ expSpan R :=
  Submodule.subset_span ⟨j, rfl⟩

/-! ## 2. The exponent span of a trivial presentation is the whole lattice

The quotient map `ℤⁿ → ℤⁿ ⧸ expSpan R` kills every relator exponent vector, so
it composes with the exponent homomorphism to a homomorphism `ψ` out of the free
group whose kernel contains the relation subgroup. Triviality of the presented
group puts each free generator in the relation subgroup, hence each `genVec i`
lies in `expSpan R`. Those vectors are the standard basis. -/
theorem expSpan_eq_top_of_presents {n : ℕ} {R : Relators n}
    (h : PresentsTrivialGroup R) : expSpan R = ⊤ := by
  classical
  let quoHom : Multiplicative (Fin n → ℤ) →*
      Multiplicative ((Fin n → ℤ) ⧸ expSpan R) :=
    { toFun := fun v => Multiplicative.ofAdd (Submodule.Quotient.mk v.toAdd)
      map_one' := by simp
      map_mul' := by
        intro a b
        simp [toAdd_mul, ofAdd_add] }
  let ψ : Word n →* Multiplicative ((Fin n → ℤ) ⧸ expSpan R) :=
    quoHom.comp (expHom n)
  have hkill : ∀ r ∈ Set.range R, ψ r = 1 := by
    rintro r ⟨j, rfl⟩
    have hmem : expVec (R j) ∈ expSpan R := expVec_mem_expSpan R j
    have hzero : (Submodule.Quotient.mk (expVec (R j)) :
        (Fin n → ℤ) ⧸ expSpan R) = 0 := by
      rw [Submodule.Quotient.mk_eq_zero]
      exact hmem
    show Multiplicative.ofAdd (Submodule.Quotient.mk (expVec (R j))) = 1
    rw [hzero]
    simp
  have hle : relationSubgroup R ≤ ψ.ker := Subgroup.normalClosure_le_normal hkill
  have hgen : ∀ i : Fin n, genVec i ∈ expSpan R := by
    intro i
    haveI : (relationSubgroup R).Normal := by
      unfold relationSubgroup
      infer_instance
    haveI : Subsingleton (PresentedGroup R) := h
    have hq : (QuotientGroup.mk (FreeGroup.of i) : PresentedGroup R) = 1 :=
      Subsingleton.elim _ _
    have hmem : FreeGroup.of i ∈ relationSubgroup R :=
      (QuotientGroup.eq_one_iff (FreeGroup.of i)).mp hq
    have h1 : ψ (FreeGroup.of i) = 1 := by
      have := hle hmem
      simpa [MonoidHom.mem_ker] using this
    have h2 : (Submodule.Quotient.mk (genVec i) : (Fin n → ℤ) ⧸ expSpan R) = 0 := by
      simpa [ψ, quoHom, expHom, expVec, genVec] using h1
    rwa [Submodule.Quotient.mk_eq_zero] at h2
  have hbasis : Submodule.span ℤ (Set.range (fun i : Fin n => genVec i)) = ⊤ := by
    have hfun : (fun i : Fin n => genVec i) = ⇑(Pi.basisFun ℤ (Fin n)) := by
      funext i
      simp [genVec, Pi.basisFun_apply]
    rw [hfun]
    exact (Pi.basisFun ℤ (Fin n)).span_eq
  rw [eq_top_iff]
  calc ⊤ = Submodule.span ℤ (Set.range (fun i : Fin n => genVec i)) := hbasis.symm
    _ ≤ expSpan R := Submodule.span_le.mpr (Set.range_subset_iff.mpr hgen)

/-! ## 3. The exponent matrix and the determinant move law -/

noncomputable def expMatrix {n : ℕ} (R : Relators n) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => expVec (R i) j

theorem expVec_zpow_general {n : ℕ} (w : Word n) (z : ℤ) :
    expVec (w ^ z) = z • expVec w := by
  simp [expVec, map_zpow]

theorem expMatrix_update {n : ℕ} (R : Relators n) (i : Fin n) (w : Word n) :
    expMatrix (Function.update R i w) = Function.update (expMatrix R) i (expVec w) := by
  funext r s
  by_cases hr : r = i
  · rw [hr]
    simp [expMatrix]
  · simp [expMatrix, hr]

theorem expMatrix_rowAdd {n : ℕ} (R : Relators n) (i j : Fin n) (c : ℤ) :
    expMatrix (Function.update R i (R i * R j ^ c)) =
      Function.update (expMatrix R) i (expMatrix R i + c • expMatrix R j) := by
  funext r s
  by_cases hr : r = i
  · rw [hr]
    simp [expMatrix, expVec_mul, expVec_zpow_general, Pi.add_apply]
  · simp [expMatrix, hr]

theorem expMatrix_rowNeg {n : ℕ} (R : Relators n) (i : Fin n) :
    expMatrix (Function.update R i (R i)⁻¹) =
      Function.update (expMatrix R) i (-(expMatrix R i)) := by
  funext r s
  by_cases hr : r = i
  · rw [hr]
    simp [expMatrix, expVec_inv]
  · simp [expMatrix, hr]

theorem expMatrix_conj {n : ℕ} (R : Relators n) (i : Fin n) (w : Word n) :
    expMatrix (Function.update R i (w * R i * w⁻¹)) = expMatrix R := by
  rw [expMatrix_update, expVec_conj]
  rw [show expVec (R i) = (expMatrix R) i from rfl, Function.update_eq_self]

theorem expMatrix_det_rowAdd {n : ℕ} (R : Relators n) (i j : Fin n)
    (hij : i ≠ j) (c : ℤ) :
    (expMatrix (Function.update R i (R i * R j ^ c))).det = (expMatrix R).det := by
  rw [expMatrix_rowAdd]
  exact Matrix.det_updateRow_add_smul_self (expMatrix R) hij c

theorem expMatrix_det_rowNeg {n : ℕ} (R : Relators n) (i : Fin n) :
    (expMatrix (Function.update R i (R i)⁻¹)).det = -(expMatrix R).det := by
  rw [expMatrix_rowNeg]
  change (Matrix.updateRow (expMatrix R) i (-(expMatrix R i))).det = -(expMatrix R).det
  rw [show -(expMatrix R i) = (-1 : ℤ) • expMatrix R i from
    (neg_one_smul ℤ (expMatrix R i)).symm]
  rw [Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  simp

theorem expMatrix_det_step {n : ℕ} {R S : Relators n} (h : Step R S) :
    (expMatrix S).det = (expMatrix R).det ∨
      (expMatrix S).det = -(expMatrix R).det := by
  cases h with
  | inv i => exact Or.inr (expMatrix_det_rowNeg R i)
  | mulRight i j hij => exact Or.inl (by simpa using expMatrix_det_rowAdd R i j hij 1)
  | conj i w => exact Or.inl (by rw [expMatrix_conj])

/-! ## 4. The power family `(x * y ^ n, y)` reaches the standard pair

The ordered pair `(x * y ^ n, y)` on two generators can be carried to the
standard pair `(x, y)` by Andrews–Curtis moves. `powFamily_step_succ` spends
three moves per unit of the exponent: invert the second relator, right-multiply
the first relator by it, and invert the second relator back. The induction
`reachable_powFamily` iterates that step down to `powFamily 0 = standard 2`. -/

/-- The power family `(x * y ^ n, y)` at rank two, with `x = FreeGroup.of 0`
and `y = FreeGroup.of 1`. -/
def powFamily (n : ℕ) : Relators 2 :=
  Function.update (standard 2) 0 (FreeGroup.of 0 * (FreeGroup.of 1) ^ n)

/-- The first relator of `powFamily n` is `x * y ^ n`. -/
@[simp] theorem powFamily_apply_zero (n : ℕ) :
    powFamily n 0 = FreeGroup.of 0 * (FreeGroup.of 1) ^ n := by
  simp [powFamily]

/-- The second relator of `powFamily n` is the generator `y`. -/
@[simp] theorem powFamily_apply_one (n : ℕ) : powFamily n 1 = FreeGroup.of 1 := by
  simp [powFamily, standard]

/-- The family starts at the standard pair, because `y ^ 0 = 1` and updating a
function at a point with its own value changes nothing. -/
theorem powFamily_zero : powFamily 0 = standard 2 := by
  have h : FreeGroup.of 0 * (FreeGroup.of 1) ^ 0 = standard 2 0 := by
    simp [standard]
  simp only [powFamily, h, Function.update_eq_self]

/-- One unit of the exponent costs three moves. The chain inverts relator 1,
right-multiplies relator 0 by it, and inverts relator 1 back. The intermediate
tuples are named `S` and `T` so the three `Step` constructors apply to explicit
targets. -/
theorem powFamily_step_succ (n : ℕ) :
    Reachable (powFamily (n + 1)) (powFamily n) := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  set S : Relators 2 := Function.update (powFamily (n + 1)) 1 (FreeGroup.of 1)⁻¹ with hS
  have hstep1 : Step (powFamily (n + 1)) S := by
    rw [hS]
    simpa [powFamily_apply_one] using (Step.inv (powFamily (n + 1)) 1)
  have hS0 : S 0 = FreeGroup.of 0 * (FreeGroup.of 1) ^ (n + 1) := by
    rw [hS]
    simp
  have hS1 : S 1 = (FreeGroup.of 1)⁻¹ := by
    rw [hS]
    simp
  set T : Relators 2 := Function.update S 0 (S 0 * S 1) with hT
  have hstep2 : Step S T := by
    rw [hT]
    exact Step.mulRight S 0 1 h01
  have hT0 : T 0 = FreeGroup.of 0 * (FreeGroup.of 1) ^ n := by
    rw [hT, Function.update_self, hS0, hS1]
    simp [pow_succ, mul_assoc]
  have hT1 : T 1 = (FreeGroup.of 1)⁻¹ := by
    rw [hT, Function.update_of_ne h10]
    exact hS1
  have hstep3 : Step T (Function.update T 1 (FreeGroup.of 1)) := by
    simpa [hT1] using (Step.inv T 1)
  have hF : Function.update T 1 (FreeGroup.of 1) = powFamily n := by
    have h0 : Function.update T 1 (FreeGroup.of 1) 0 = powFamily n 0 := by
      rw [Function.update_of_ne h01, hT0, powFamily_apply_zero]
    have h1 : Function.update T 1 (FreeGroup.of 1) 1 = powFamily n 1 := by
      rw [Function.update_self, powFamily_apply_one]
    funext i
    exact (Fin.forall_fin_two (p := fun j =>
      Function.update T 1 (FreeGroup.of 1) j = powFamily n j)).mpr ⟨h0, h1⟩ i
  have hfirst : Reachable (powFamily (n + 1)) S := Relation.ReflTransGen.single hstep1
  have hsecond : Reachable S T := Relation.ReflTransGen.single hstep2
  have hthird : Reachable T (powFamily n) := by
    rw [← hF]
    exact Relation.ReflTransGen.single hstep3
  exact (hfirst.trans hsecond).trans hthird

/-- Every member of the power family reaches the standard pair, by induction on
the exponent using the base case and the three-move successor step. -/
theorem reachable_powFamily (n : ℕ) : Reachable (powFamily n) (standard 2) := by
  induction n with
  | zero =>
      rw [powFamily_zero]
      exact Relation.ReflTransGen.refl
  | succ n ih =>
      exact (powFamily_step_succ n).trans ih

/-! ## 5. No natural-valued measure decreases on every step

`Step` contains the two-cycle `R → update R i (R i)⁻¹ → R`. A strict decrease on
both edges of a cycle cannot exist in `ℕ`, so no `ℕ`-valued measure decreases on
every step at positive rank. -/

/-- No `ℕ`-valued function decreases on every official step at positive rank. -/
theorem no_strictly_decreasing_measure {n : ℕ} (hn : 0 < n) (μ : Relators n → ℕ) :
    ¬ ∀ R S : Relators n, Step R S → μ S < μ R := by
  intro h
  let i : Fin n := ⟨0, hn⟩
  let R : Relators n := standard n
  let S : Relators n := Function.update R i (R i)⁻¹
  have hSR : Function.update S i (S i)⁻¹ = R := by
    funext j
    by_cases hj : j = i
    · rw [hj]
      simp [S]
    · rw [Function.update_of_ne hj]
      exact Function.update_of_ne hj (R i)⁻¹ R
  have h1 : μ S < μ R := h R S (Step.inv R i)
  have h2 : μ R < μ S := h S R (by rw [← hSR]; exact Step.inv S i)
  exact not_lt_of_ge (le_of_lt h1) h2

/-! ## 6. Stability: inserting an isolated generator–relator pair

The stable move changes the rank, so a balanced presentation is carried together
with its rank. `stabilize` inserts one fresh generator at position `g` together
with the singleton relator on it at position `i`. The inserted pair is isolated:
the new generator occurs in no old relator and no old generator occurs in the
new relator.

The transport map `tau g` embeds the old exponent vectors into the hyperplane of
the new space on which the new coordinate vanishes; the inserted relator
contributes the complementary basis vector `genVec g`, and `proj g` reads the
old coordinates back. -/

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

/-! ### 6.1 The insertion map on exponent vectors -/

/-- Insert the new coordinate `0` at position `g` and copy the old coordinates
into the remaining positions along `Fin.succAbove g`. -/
def tau {n : ℕ} (g : Fin (n + 1)) (v : Fin n → ℤ) : Fin (n + 1) → ℤ :=
  Fin.insertNth g 0 v

@[simp] theorem tau_apply_self {n : ℕ} (g : Fin (n + 1)) (v : Fin n → ℤ) :
    tau g v g = 0 :=
  Fin.insertNth_apply_same (α := fun _ => ℤ) g 0 v

@[simp] theorem tau_apply_succAbove {n : ℕ} (g : Fin (n + 1)) (v : Fin n → ℤ)
    (y : Fin n) : tau g v (g.succAbove y) = v y :=
  Fin.insertNth_apply_succAbove (α := fun _ => ℤ) g 0 v y

theorem tau_zero {n : ℕ} (g : Fin (n + 1)) : tau g (0 : Fin n → ℤ) = 0 := by
  funext x
  obtain hx | ⟨y, rfl⟩ := Fin.eq_self_or_eq_succAbove g x
  · rw [hx]; simp
  · simp

theorem tau_add {n : ℕ} (g : Fin (n + 1)) (u v : Fin n → ℤ) :
    tau g (u + v) = tau g u + tau g v := by
  funext x
  obtain hx | ⟨y, rfl⟩ := Fin.eq_self_or_eq_succAbove g x
  · rw [hx]; simp
  · simp [Pi.add_apply]

theorem tau_smul {n : ℕ} (g : Fin (n + 1)) (c : ℤ) (v : Fin n → ℤ) :
    tau g (c • v) = c • tau g v := by
  funext x
  obtain hx | ⟨y, rfl⟩ := Fin.eq_self_or_eq_succAbove g x
  · rw [hx]; simp
  · simp [Pi.smul_apply]

/-- The bundled additive form of `tau g`. -/
def tauAdd {n : ℕ} (g : Fin (n + 1)) : (Fin n → ℤ) →+ (Fin (n + 1) → ℤ) where
  toFun := tau g
  map_zero' := tau_zero g
  map_add' := tau_add g

/-- The bundled `ℤ`-linear form of `tau g`. -/
def tauLin {n : ℕ} (g : Fin (n + 1)) : (Fin n → ℤ) →ₗ[ℤ] (Fin (n + 1) → ℤ) where
  toFun := tau g
  map_add' := tau_add g
  map_smul' := tau_smul g

/-- The multiplicative form used to compare with the exponent homomorphism. -/
def tauMul {n : ℕ} (g : Fin (n + 1)) :
    Multiplicative (Fin n → ℤ) →* Multiplicative (Fin (n + 1) → ℤ) where
  toFun v := Multiplicative.ofAdd (tau g v.toAdd)
  map_one' := by simp [tau_zero]
  map_mul' := by intro a b; simp [tau_add, toAdd_mul, ofAdd_add]

@[simp] theorem tauMul_ofAdd {n : ℕ} (g : Fin (n + 1)) (v : Fin n → ℤ) :
    tauMul g (Multiplicative.ofAdd v) = Multiplicative.ofAdd (tau g v) := by
  simp [tauMul]

/-- The coordinate projection that forgets the new coordinate and reads the old
coordinates along `Fin.succAbove g`. -/
def proj {n : ℕ} (g : Fin (n + 1)) : (Fin (n + 1) → ℤ) →ₗ[ℤ] (Fin n → ℤ) where
  toFun w := fun y => w (g.succAbove y)
  map_add' := by intro a b; rfl
  map_smul' := by intro c a; rfl

@[simp] theorem proj_tau {n : ℕ} (g : Fin (n + 1)) (v : Fin n → ℤ) :
    proj g (tau g v) = v := by
  funext y
  simp [proj]

@[simp] theorem proj_genVec {n : ℕ} (g : Fin (n + 1)) : proj g (genVec g) = 0 := by
  funext y
  simp [proj, genVec]

/-- On the old basis, `tau` is the insertion. -/
theorem genVec_succAbove {n : ℕ} (g : Fin (n + 1)) (y : Fin n) :
    genVec (g.succAbove y) = tau g (genVec y) := by
  funext x
  obtain hx | ⟨z, rfl⟩ := Fin.eq_self_or_eq_succAbove g x
  · rw [hx]
    simp [genVec]
  · simp [genVec, Pi.single_apply]

/-! ### 6.2 Exponent vectors of the stabilized relators -/

/-- The exponent homomorphism commutes with insertion of the new generator. -/
theorem expHom_map_succAbove {n : ℕ} (g : Fin (n + 1)) :
    (expHom (n + 1)).comp (FreeGroup.map (Fin.succAbove g)) =
      (tauMul g).comp (expHom n) := by
  apply FreeGroup.ext_hom
  intro y
  simp only [MonoidHom.comp_apply, FreeGroup.map.of, expHom, FreeGroup.lift_apply_of,
    tauMul_ofAdd]
  rw [genVec_succAbove]

/-- The exponent vector of an old relator, pushed into the new generator type. -/
theorem expVec_map_succAbove {n : ℕ} (g : Fin (n + 1)) (w : Word n) :
    expVec (FreeGroup.map (Fin.succAbove g) w) = tau g (expVec w) := by
  have h := DFunLike.congr_fun (expHom_map_succAbove g) w
  simpa [expVec, tauMul, tauAdd] using h

/-- The inserted relator has the new basis vector as exponent vector. -/
theorem expVec_stabilize_self {n : ℕ} (R : Relators n) (g i : Fin (n + 1)) :
    expVec ((stabilize R g i) i) = genVec g := by
  rw [show stabilize R g i i = FreeGroup.of g from Fin.insertNth_apply_same i _ _]
  simp [expVec, expHom, genVec]

/-- Each old relator is carried by `tau`. -/
theorem expVec_stabilize_succAbove {n : ℕ} (R : Relators n) (g i : Fin (n + 1))
    (j : Fin n) : expVec ((stabilize R g i) (i.succAbove j)) = tau g (expVec (R j)) := by
  rw [show stabilize R g i (i.succAbove j) = FreeGroup.map g.succAbove (R j) from
    Fin.insertNth_apply_succAbove i _ _ j]
  exact expVec_map_succAbove g (R j)

/-! ### 6.3 The span is transported onto the whole space -/

/-- The image under `tau` of any element of the old span lies in the new span. -/
theorem tau_mem_expSpan_stabilize {n : ℕ} (R : Relators n) (g i : Fin (n + 1))
    {u : Fin n → ℤ} (hu : u ∈ expSpan R) : tau g u ∈ expSpan (stabilize R g i) := by
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
theorem genVec_mem_expSpan_stabilize {n : ℕ} (R : Relators n) (g i : Fin (n + 1)) :
    genVec g ∈ expSpan (stabilize R g i) := by
  rw [← expVec_stabilize_self R g i]
  exact expVec_mem_expSpan _ i

/-- A top old span gives a top new span. -/
theorem expSpan_stabilize_top {n : ℕ} (R : Relators n) (g i : Fin (n + 1))
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
theorem map_proj_expSpan_stabilize {n : ℕ} (R : Relators n) (g i : Fin (n + 1)) :
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

/-- Inserting an isolated generator–relator pair preserves the property that
the exponent span is the whole lattice, in both directions. -/
theorem expSpan_stabilize_eq_top_iff {n : ℕ} (R : Relators n) (g i : Fin (n + 1)) :
    expSpan (stabilize R g i) = ⊤ ↔ expSpan R = ⊤ := by
  constructor
  · intro h
    have hmap := map_proj_expSpan_stabilize R g i
    rw [h, Submodule.map_top] at hmap
    rw [← hmap]
    exact LinearMap.range_eq_top.mpr (fun u => ⟨tau g u, proj_tau g u⟩)
  · intro h
    exact expSpan_stabilize_top R g i h

/-! ### 6.4 Ordinary moves preserve the span -/

theorem expSpan_le_of_forall {n : ℕ} {R S : Relators n}
    (h : ∀ j, expVec (S j) ∈ expSpan R) : expSpan S ≤ expSpan R :=
  Submodule.span_le.mpr (Set.range_subset_iff.mpr h)

theorem expSpan_eq_of_forall {n : ℕ} {R S : Relators n}
    (h1 : ∀ j, expVec (S j) ∈ expSpan R) (h2 : ∀ j, expVec (R j) ∈ expSpan S) :
    expSpan S = expSpan R :=
  le_antisymm (expSpan_le_of_forall h1) (expSpan_le_of_forall h2)

theorem expSpan_inv {n : ℕ} (R : Relators n) (i : Fin n) :
    expSpan (Function.update R i (R i)⁻¹) = expSpan R := by
  apply expSpan_eq_of_forall
  · intro j
    by_cases hj : j = i
    · rw [hj, Function.update_self, expVec_inv]
      exact (expSpan R).neg_mem (expVec_mem_expSpan R i)
    · rw [Function.update_of_ne hj]
      exact expVec_mem_expSpan R j
  · intro j
    by_cases hj : j = i
    · rw [hj]
      have h : expVec (R i) = -expVec ((Function.update R i (R i)⁻¹) i) := by
        rw [Function.update_self, expVec_inv, neg_neg]
      rw [h]
      exact (expSpan (Function.update R i (R i)⁻¹)).neg_mem
        (expVec_mem_expSpan (Function.update R i (R i)⁻¹) i)
    · rw [← Function.update_of_ne (f := R) (a := j) (a' := i) hj]
      exact expVec_mem_expSpan (Function.update R i (R i)⁻¹) j

theorem expSpan_mulRight {n : ℕ} (R : Relators n) (i j : Fin n) (hij : i ≠ j) :
    expSpan (Function.update R i (R i * R j)) = expSpan R := by
  apply expSpan_eq_of_forall
  · intro k
    by_cases hk : k = i
    · rw [hk, Function.update_self, expVec_mul]
      exact (expSpan R).add_mem (expVec_mem_expSpan R i) (expVec_mem_expSpan R j)
    · rw [Function.update_of_ne hk]
      exact expVec_mem_expSpan R k
  · intro k
    by_cases hk : k = i
    · rw [hk]
      have hSj : Function.update R i (R i * R j) j = R j :=
        Function.update_of_ne (Ne.symm hij) (R i * R j) R
      have h : expVec (R i) =
          expVec ((Function.update R i (R i * R j)) i) -
            expVec ((Function.update R i (R i * R j)) j) := by
        rw [Function.update_self, hSj, expVec_mul]
        abel
      rw [h]
      exact (expSpan (Function.update R i (R i * R j))).sub_mem
        (expVec_mem_expSpan (Function.update R i (R i * R j)) i)
        (expVec_mem_expSpan (Function.update R i (R i * R j)) j)
    · rw [← Function.update_of_ne (f := R) (a := k) (a' := i) hk]
      exact expVec_mem_expSpan (Function.update R i (R i * R j)) k

theorem expSpan_conj {n : ℕ} (R : Relators n) (i : Fin n) (w : Word n) :
    expSpan (Function.update R i (w * R i * w⁻¹)) = expSpan R := by
  apply expSpan_eq_of_forall
  · intro k
    by_cases hk : k = i
    · rw [hk, Function.update_self, expVec_conj]
      exact expVec_mem_expSpan R i
    · rw [Function.update_of_ne hk]
      exact expVec_mem_expSpan R k
  · intro k
    by_cases hk : k = i
    · rw [hk]
      have h : expVec (R i) = expVec ((Function.update R i (w * R i * w⁻¹)) i) := by
        rw [Function.update_self, expVec_conj]
      rw [h]
      exact expVec_mem_expSpan (Function.update R i (w * R i * w⁻¹)) i
    · rw [← Function.update_of_ne (f := R) (a := k) (a' := i) hk]
      exact expVec_mem_expSpan (Function.update R i (w * R i * w⁻¹)) k

/-- Every official step preserves the span of the relator exponent vectors. -/
theorem step_expSpan {n : ℕ} {R S : Relators n} (h : Step R S) :
    expSpan S = expSpan R := by
  cases h with
  | inv i => exact expSpan_inv _ i
  | mulRight i j hij => exact expSpan_mulRight _ i j hij
  | conj i w => exact expSpan_conj _ i w

/-- Every stable step preserves the proposition that the exponent span is the
whole lattice, in both directions. -/
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

end ACChallenge
