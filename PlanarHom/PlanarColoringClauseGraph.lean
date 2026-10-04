import PlanarHom.PlanarColoringPaletteTransport

/-! Literal three-input positive-exact-one color clause gadget. Three actual
palette-propagating one-way converters meet a central triangle. Three exclusive
diamonds connect neighboring palette pairs. A rim edge already supplied by a
converter is reused instead of duplicated as a parallel straight segment. -/
noncomputable section
namespace PlanarHom.PlanarColoringClause
open MultiGraph
set_option maxRecDepth 6000
set_option synthInstance.maxSize 10000

abbrev Vertex := Fin 105
abbrev Edge := (Fin 3 × PlanarColoringOneWayConverter.Edge) ⊕ ((Fin 3 × Fin 7) ⊕ Fin 5)
def copyVertex (k : Fin 3) (v : Fin 34) : Vertex := ⟨34*k.val+v.val,by omega⟩
def centerVertex (k : Fin 3) : Vertex := ⟨102+k.val,by omega⟩
def next (k : Fin 3) : Fin 3 := k+1

def gapMap (k : Fin 3) : Fin 5 → Vertex :=
  ![copyVertex k 2,copyVertex k 4,copyVertex (next k) 7,copyVertex (next k) 6,centerVertex k]
def extraSrc : Fin 5 → Vertex :=
  ![copyVertex 0 1,copyVertex 1 1,copyVertex 2 1,copyVertex 0 1,copyVertex 2 1]
def extraDst : Fin 5 → Vertex :=
  ![copyVertex 1 1,copyVertex 2 1,copyVertex 0 1,copyVertex 0 4,copyVertex 2 7]

def graph : MultiGraph Vertex Edge where
  src := Sum.elim (fun p => copyVertex p.1 (PlanarColoringOneWayConverter.graph.src p.2))
    (Sum.elim (fun p => gapMap p.1 (PlanarColoringExclusiveCrossing.graph.src p.2.succ)) extraSrc)
  dst := Sum.elim (fun p => copyVertex p.1 (PlanarColoringOneWayConverter.graph.dst p.2))
    (Sum.elim (fun p => gapMap p.1 (PlanarColoringExclusiveCrossing.graph.dst p.2.succ)) extraDst)

def Proper (col : Vertex → Fin 3) : Prop := ∀ e,col (graph.src e)≠col (graph.dst e)

/-- Every component is the literal subgraph whose counting theorem is used. -/
theorem proper_split (col : Vertex → Fin 3) : Proper col ↔
    (∀ k,PlanarColoringOneWayConverter.Proper (col ∘ copyVertex k)) ∧
    (∀ k,PlanarColoringExclusiveCrossing.Proper (col ∘ gapMap k)) ∧
    col (copyVertex 0 1)≠col (copyVertex 1 1) ∧
    col (copyVertex 1 1)≠col (copyVertex 2 1) ∧
    col (copyVertex 2 1)≠col (copyVertex 0 1) ∧
    col (copyVertex 0 1)≠col (copyVertex 0 4) ∧
    col (copyVertex 2 1)≠col (copyVertex 2 7) := by
  constructor
  · intro h
    refine ⟨fun k e => h (.inl (k,e)),?_,h (.inr (.inr 0)),h (.inr (.inr 1)),
      h (.inr (.inr 2)),h (.inr (.inr 3)),h (.inr (.inr 4))⟩
    intro k e
    refine Fin.cases ?_ (fun j => ?_) e
    · exact h (.inl (k,.inl (2,0)))
    · exact h (.inr (.inl (k,j)))
  · rintro ⟨hc,hg,h0,h1,h2,h3,h4⟩ e
    rcases e with ⟨k,e⟩ | (⟨k,e⟩ | e)
    · exact hc k e
    · exact hg k e.succ
    · fin_cases e <;> first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4

end PlanarHom.PlanarColoringClause
