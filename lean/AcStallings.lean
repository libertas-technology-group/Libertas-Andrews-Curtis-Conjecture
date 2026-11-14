import AC
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Option

/-!
# AcStallings — Stallings graphs, immersions, and elementary folds

This module defines the labelled-graph objects of Stallings' folding algorithm
for the free group of rank `n`.  An edge carries a source vertex, a target
vertex, and a signed generator label.  A graph is immersed into the rank-`n`
rose when each signed label occurs on at most one outgoing edge and on at most
one incoming edge at every vertex.  An elementary fold is a quotient map that
identifies two edges with one signed label and one incidence, together with
their free endpoints, and identifies no other pair.  `FoldStep` is one such
map; `FoldsTo` is its reflexive-transitive closure.

`roseGraph R` is the graph of a relator tuple `R : Relators n`: one subdivided
loop per relator, all loops attached at one basepoint.  Stallings' process
starts at this graph and folds until the immersion condition holds.
`foldsToImmersion_statement` names that terminal property as a
proposition-valued definition.  No proof is claimed here.

The definitions follow the labelled-graph formulation of Stallings' fold: two
distinct edges with one label and one incidence at a vertex are identified, and
their other endpoints are identified with them.  See Touikan,
arXiv:0805.2348, Definition 1.1, and the Oxford notes on Stallings folding,
Definition 1.2.9.

## Boundary

The graph, immersion, and fold definitions above are the compiled objects.  No
`tailArea` is declared here, and the fold relation does not define one.

A measure that depends only on the fold result is a graph invariant of the
folded rose.  The tuples `(x, y)` and `(x, x * y)` in `Relators 2` fold to the
same one-vertex two-loop graph: the `x`-edge of the second relator folds with
the `x`-relator, its endpoint joins the basepoint, and the `y`-edge becomes a
loop.  The first tuple is a signed permutation (`AcProof.lean:61-64`); the
second is not, because `x * y` has length two.  A graph invariant takes one
value on both tuples, so it cannot be zero exactly on the terminal set.

A measure that counts folds instead is zero at every rose that is already
immersed, and `(x * y, y * x)` is an immersed non-terminal rose at rank two: at
the basepoint the outgoing labels are `x` and `y` and the incoming labels are
`y` and `x`.  A measure read from an intermediate graph depends on the fold
order, so it is not a function of the state.  No fold-derived measure of these
three kinds satisfies the terminal-characterisation obligation.

The exact missing object is a state-level measure
`tailArea : Relators n → ℕ` that is not a function of the fold class, together
with the descent step
`∀ R, ¬ IsSignedPermutation R → ∃ S, Step R S ∧ tailArea S < tailArea R`.
The descent must be stated over `Step`, not over `Reachable`: every `Step` is
undoable, so `Reachable` is symmetric, and a strictly smaller `Reachable`
successor at every non-terminal state would give an infinite descending chain
in `ℕ`.

The compiled `AC.Tail.tail` (`AcTailDefs.lean:32-33`) is the rank-two commutator
tail `w * (x ^ a * y ^ b)⁻¹`; it is not a tail area.  The plan for the measure,
`PLANNED_40_STALLINGS_FOLDING.md`, is absent from the repository tree;
`PROOF_STRATEGY.md:216` records that the Stallings tail-area route has no
session block yet.
-/

set_option autoImplicit false

namespace AC
namespace Stallings

/-- A finite directed graph over the rank-`n` rose.  An edge carries a source
vertex, a target vertex, and a signed generator label. -/
structure StallingsGraph (n : ℕ) where
  V : Type
  E : Type
  fintypeV : Fintype V
  fintypeE : Fintype E
  src : E → V
  tgt : E → V
  edgeLabel : E → Fin n × Bool

attribute [instance] StallingsGraph.fintypeV StallingsGraph.fintypeE

/-- A graph morphism that preserves source, target, and signed label. -/
structure Hom {n : ℕ} (G H : StallingsGraph n) where
  mapV : G.V → H.V
  mapE : G.E → H.E
  src_map : ∀ e : G.E, mapV (G.src e) = H.src (mapE e)
  tgt_map : ∀ e : G.E, mapV (G.tgt e) = H.tgt (mapE e)
  label_map : ∀ e : G.E, H.edgeLabel (mapE e) = G.edgeLabel e

/-- The immersed condition into the rank-`n` rose: at each vertex, each signed
generator label occurs on at most one outgoing edge and on at most one incoming
edge. -/
def IsImmersion {n : ℕ} (G : StallingsGraph n) : Prop :=
  (∀ e₁ e₂ : G.E, G.src e₁ = G.src e₂ → G.edgeLabel e₁ = G.edgeLabel e₂ →
    e₁ = e₂) ∧
  (∀ e₁ e₂ : G.E, G.tgt e₁ = G.tgt e₂ → G.edgeLabel e₁ = G.edgeLabel e₂ →
    e₁ = e₂)

/-- The quotient map of one fold at a common source.  Two distinct edges with
one signed label leave one vertex; the map identifies the two edges and their
target vertices, and identifies no other pair of edges or vertices. -/
def IsSourceFoldMap {n : ℕ} (G H : StallingsGraph n) (f : Hom G H) : Prop :=
  ∃ e₁ e₂ : G.E,
    e₁ ≠ e₂ ∧ G.src e₁ = G.src e₂ ∧ G.edgeLabel e₁ = G.edgeLabel e₂ ∧
    f.mapE e₁ = f.mapE e₂ ∧
    (∀ e e' : G.E, f.mapE e = f.mapE e' ↔
      e = e' ∨ (e = e₁ ∧ e' = e₂) ∨ (e = e₂ ∧ e' = e₁)) ∧
    (∀ v v' : G.V, f.mapV v = f.mapV v' ↔
      v = v' ∨ (v = G.tgt e₁ ∧ v' = G.tgt e₂) ∨
        (v = G.tgt e₂ ∧ v' = G.tgt e₁)) ∧
    (∀ w : H.V, ∃ v : G.V, f.mapV v = w) ∧
    (∀ d : H.E, ∃ e : G.E, f.mapE e = d)

/-- The quotient map of one fold at a common target.  Two distinct edges with
one signed label enter one vertex; the map identifies the two edges and their
source vertices, and identifies no other pair of edges or vertices. -/
def IsTargetFoldMap {n : ℕ} (G H : StallingsGraph n) (f : Hom G H) : Prop :=
  ∃ e₁ e₂ : G.E,
    e₁ ≠ e₂ ∧ G.tgt e₁ = G.tgt e₂ ∧ G.edgeLabel e₁ = G.edgeLabel e₂ ∧
    f.mapE e₁ = f.mapE e₂ ∧
    (∀ e e' : G.E, f.mapE e = f.mapE e' ↔
      e = e' ∨ (e = e₁ ∧ e' = e₂) ∨ (e = e₂ ∧ e' = e₁)) ∧
    (∀ v v' : G.V, f.mapV v = f.mapV v' ↔
      v = v' ∨ (v = G.src e₁ ∧ v' = G.src e₂) ∨
        (v = G.src e₂ ∧ v' = G.src e₁)) ∧
    (∀ w : H.V, ∃ v : G.V, f.mapV v = w) ∧
    (∀ d : H.E, ∃ e : G.E, f.mapE e = d)

/-- One elementary Stallings fold. -/
inductive FoldStep {n : ℕ} : StallingsGraph n → StallingsGraph n → Prop
  | source {G H : StallingsGraph n} (f : Hom G H) :
      IsSourceFoldMap G H f → FoldStep G H
  | target {G H : StallingsGraph n} (f : Hom G H) :
      IsTargetFoldMap G H f → FoldStep G H

/-- A finite sequence of elementary folds. -/
def FoldsTo {n : ℕ} (G H : StallingsGraph n) : Prop :=
  Relation.ReflTransGen (FoldStep (n := n)) G H

/-! ## The graph of a relator tuple -/

/-- The vertices of the rose with one subdivided loop per relator: one
basepoint, and one internal vertex for each position strictly inside a relator. -/
abbrev RoseVertex {n : ℕ} (R : Relators n) : Type :=
  Option (Σ i : Fin n, Fin ((R i).toWord.length - 1))

/-- The edges of the rose: the letter positions in the relators. -/
abbrev RoseEdge {n : ℕ} (R : Relators n) : Type :=
  Σ i : Fin n, Fin ((R i).toWord.length)

/-- The source of a letter edge.  The first letter of a relator leaves the
basepoint. -/
def roseSrc {n : ℕ} (R : Relators n) (e : RoseEdge R) : RoseVertex R :=
  if h : e.2.val = 0 then none
  else some ⟨e.1, ⟨e.2.val - 1, by
    have hlt : e.2.val < (R e.1).toWord.length := e.2.isLt
    omega⟩⟩

/-- The target of a letter edge.  The letter after the last one enters the
basepoint. -/
def roseTgt {n : ℕ} (R : Relators n) (e : RoseEdge R) : RoseVertex R :=
  if h : e.2.val + 1 = (R e.1).toWord.length then none
  else some ⟨e.1, ⟨e.2.val, by
    have hlt : e.2.val < (R e.1).toWord.length := e.2.isLt
    omega⟩⟩

/-- The signed label of a letter edge. -/
def roseLabel {n : ℕ} (R : Relators n) (e : RoseEdge R) : Fin n × Bool :=
  (R e.1).toWord.get e.2

/-- The rose of a relator tuple, before folding. -/
def roseGraph {n : ℕ} (R : Relators n) : StallingsGraph n where
  V := RoseVertex R
  E := RoseEdge R
  fintypeV := inferInstance
  fintypeE := inferInstance
  src := roseSrc R
  tgt := roseTgt R
  edgeLabel := roseLabel R

/-- The folding process reaches an immersed graph.  This is a proposition-valued
definition; no proof is supplied here. -/
def foldsToImmersion_statement {n : ℕ} : Prop :=
  ∀ G : StallingsGraph n, ∃ H : StallingsGraph n, FoldsTo G H ∧ IsImmersion H

end Stallings
end AC
