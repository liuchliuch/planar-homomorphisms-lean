import PlanarHom.ColoredSeriesGadget

/-! NEW literal five-private-vertex, eight-occurrence mixed double diamond. -/
noncomputable section
namespace PlanarHom.RectangularMixedGadgets
open MultiGraph

def doubleDiamond : TwoTerminal (Fin 5) (Fin 8) where
  src := fun e=>if e.val=0 then .inl false else if e.val=1 then .inr 0 else
    if e.val=2 then .inl false else if e.val=3 then .inr 1 else
    if e.val=4 then .inr 2 else if e.val=5 then .inr 3 else
    if e.val=6 then .inr 2 else .inr 4
  dst := fun e=>if e.val=0 then .inr 0 else if e.val=1 then .inr 2 else
    if e.val=2 then .inr 1 else if e.val=3 then .inr 2 else
    if e.val=4 then .inr 3 else if e.val=5 then .inl true else
    if e.val=6 then .inr 4 else .inl true

def label (k : Fin 8) : Fin 2 := if k.val=0 ∨ k.val=2 ∨ k.val=5 ∨ k.val=7 then 0 else 1

def vertexSide : Bool⊕Fin 5→Fin 2
  | .inl _ => 0
  | .inr k => if k.val=2 then 1 else 0

def edgeMatrices {C R : Type} (K B : Matrix C C R) : Fin 8→Matrix C C R :=
  fun k=>if k.val=0 ∨ k.val=2 ∨ k.val=5 ∨ k.val=7 then K else B

end PlanarHom.RectangularMixedGadgets
