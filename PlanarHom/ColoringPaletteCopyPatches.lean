import PlanarHom.ColoringUniquePaletteAttachments

/-! Two-input, uniquely extending interfaces for the actual palette-copy
strips, including the retained middle rim used by the numeric macro emitter. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringPalettePairCopy
open MultiGraph IntegerStraightDrawing PlanarColoringExclusiveCrossing
set_option maxHeartbeats 6000000

namespace Single

def patchMap (v : Fin 5) : Bool ⊕ Fin 3 :=
  if h0 : v.val=0 then .inl false else if h1 : v.val=1 then .inl true else
    .inr ⟨v.val-2,by have := v.isLt; omega⟩

def patchGraph : MultiGraph (Bool ⊕ Fin 3) (Fin 6) where
  src e := patchMap (graph.src e)
  dst e := patchMap (graph.dst e)

def patchExtension (a b : Fin 3) : Fin 3 → Fin 3 := ![a,b,third a b]

theorem patch_spec (a b : Fin 3) (hab : a≠b) (u : Fin 3 → Fin 3) :
    (∀ e,Sum.elim (ColoringUniquePaletteAttachments.inputColor a b) u (patchGraph.src e)≠
      Sum.elim (ColoringUniquePaletteAttachments.inputColor a b) u (patchGraph.dst e)) ↔
        u=patchExtension a b := by
  let col := Sum.elim (ColoringUniquePaletteAttachments.inputColor a b) u ∘ patchMap
  change Proper col ↔ _
  have h01 : col 0≠col 1 := hab
  rw [proper_iff col h01]
  constructor
  · intro h
    funext w
    fin_cases w
    · exact congrFun h 2
    · exact congrFun h 3
    · exact congrFun h 4
  · intro h
    subst u
    funext v
    fin_cases v <;> rfl

end Single
namespace Double

def graphWithRim : MultiGraph (Fin 8) (Unit ⊕ (Bool × Fin 6)) where
  src := Sum.elim (fun _ => 4) graph.src
  dst := Sum.elim (fun _ => 5) graph.dst

def ProperWithRim (col : Fin 8 → Fin 3) : Prop :=
  ∀ e,col (graphWithRim.src e)≠col (graphWithRim.dst e)

theorem properWithRim_iff (col : Fin 8 → Fin 3) (hab : col 0≠col 1) :
    ProperWithRim col ↔ col=extension (col 0) (col 1) := by
  constructor
  · intro h
    exact (proper_iff col hab).mp (fun e => h (.inr e))
  · intro h
    have hp := (proper_iff col hab).mpr h
    rintro (_ | e)
    · rw [h]
      exact hab
    · exact hp e

def rimCertificate : IntegerStraightDrawing.Certificate graphWithRim point where
  injective := certificate.injective
  nondegenerate := by decide
  separated := by decide
  avoids := by decide

def drawingWithRim : PlaneDrawing graphWithRim := IntegerStraightDrawing.drawing rimCertificate

def patchMap (v : Fin 8) : Bool ⊕ Fin 6 :=
  if h0 : v.val=0 then .inl false else if h1 : v.val=1 then .inl true else
    .inr ⟨v.val-2,by have := v.isLt; omega⟩

def patchGraph : MultiGraph (Bool ⊕ Fin 6) (Unit ⊕ (Bool × Fin 6)) where
  src e := patchMap (graphWithRim.src e)
  dst e := patchMap (graphWithRim.dst e)

def patchExtension (a b : Fin 3) : Fin 6 → Fin 3 := ![a,b,a,b,third a b,third a b]

theorem patch_spec (a b : Fin 3) (hab : a≠b) (u : Fin 6 → Fin 3) :
    (∀ e,Sum.elim (ColoringUniquePaletteAttachments.inputColor a b) u (patchGraph.src e)≠
      Sum.elim (ColoringUniquePaletteAttachments.inputColor a b) u (patchGraph.dst e)) ↔
        u=patchExtension a b := by
  let col := Sum.elim (ColoringUniquePaletteAttachments.inputColor a b) u ∘ patchMap
  change ProperWithRim col ↔ _
  have h01 : col 0≠col 1 := hab
  rw [properWithRim_iff col h01]
  constructor
  · intro h
    funext w
    fin_cases w
    · exact congrFun h 2
    · exact congrFun h 3
    · exact congrFun h 4
    · exact congrFun h 5
    · exact congrFun h 6
    · exact congrFun h 7
  · intro h
    subst u
    funext v
    fin_cases v <;> rfl

end Double

inductive Shape | single | double deriving DecidableEq, Fintype

def Shape.Internal : Shape → Type
  | .single => Fin 3
  | .double => Fin 6

def Shape.Edge : Shape → Type
  | .single => Fin 6
  | .double => Unit ⊕ (Bool × Fin 6)

instance (s : Shape) : Fintype s.Internal := by cases s <;> dsimp [Shape.Internal] <;> infer_instance
instance (s : Shape) : Fintype s.Edge := by cases s <;> dsimp [Shape.Edge] <;> infer_instance

def Shape.graph (s : Shape) : MultiGraph (Bool ⊕ s.Internal) s.Edge :=
  match s with
  | .single => Single.patchGraph
  | .double => Double.patchGraph

def Shape.extension (s : Shape) (a b : Fin 3) : s.Internal → Fin 3 :=
  match s with
  | .single => Single.patchExtension a b
  | .double => Double.patchExtension a b

theorem Shape.spec (s : Shape) (a b : Fin 3) (hab : a≠b) (u : s.Internal → Fin 3) :
    (∀ e,Sum.elim (ColoringUniquePaletteAttachments.inputColor a b) u (s.graph.src e)≠
      Sum.elim (ColoringUniquePaletteAttachments.inputColor a b) u (s.graph.dst e)) ↔ u=s.extension a b := by
  cases s
  · exact Single.patch_spec a b hab u
  · exact Double.patch_spec a b hab u

end PlanarHom.ColoringPalettePairCopy
