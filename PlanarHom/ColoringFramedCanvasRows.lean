import PlanarHom.ColoringFramedCanvasGraph
import PlanarHom.HostRowAssembly
import PlanarHom.RotationRowEnding

/-! Canonical complete framed rows, with every exposed macro row cut just
after its hosted boundary-closing dart. Cell blocks occur in reverse canvas
order, followed by the initial seed-cycle block. -/
noncomputable section
open Classical
namespace PlanarHom
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization PositiveBlockProgram
open ParsimoniousNorOneInThree

namespace HostRowSystem

def ofRotationRows {V E : Type} {dec : DecidableEq (Dart E)} (G : MultiGraph V E) (R : @RotationRows V E G dec) : HostRowSystem V (Dart E) where
  host a := (G.dartPair a).1
  row := R.row
  nodup := R.nodup
  mem := R.mem

@[simp] theorem ofRotationRows_rotation {V E : Type} [DecidableEq (Dart E)] (G : MultiGraph V E) (R : RotationRows G) :
    (ofRotationRows G R).rotation=R.rotation := rfl

end HostRowSystem
namespace ColoringEmitter
namespace FramedMacro

def portVertex (s : CellShape) (p : LocalPatch.Port s) : Fin (vertexCount s) := oldVertex s (LocalPatch.portVertex s p)

theorem portVertex_injective (s : CellShape) : Function.Injective (portVertex s) := by
  intro p q h
  apply LocalPatch.portVertex_injective s
  exact Sum.inl.inj ((vertexParts s).injective h)

def cutRow (s : CellShape) (v : Fin (vertexCount s)) : List (Dart (Fin (edgeCount s))) :=
  if h:∃p,portVertex s p=v then
    ((rows s).row v).rotate (((rows s).row v).idxOf (portClosing s h.choose)+1)
  else (rows s).row v

theorem cutRow_port (s : CellShape) (p : LocalPatch.Port s) :
    cutRow s (portVertex s p)=((rows s).row (portVertex s p)).rotate
      (((rows s).row (portVertex s p)).idxOf (portClosing s p)+1) := by
  have h : ∃q,portVertex s q=portVertex s p := ⟨p,rfl⟩
  have hc : h.choose=p := portVertex_injective s h.choose_spec
  rw [cutRow,dif_pos h,hc]

def cutRows (s : CellShape) : RotationRows (graph s) where
  row := cutRow s
  nodup v := by
    unfold cutRow
    split_ifs
    · exact List.nodup_rotate.mpr ((rows s).nodup v)
    · exact (rows s).nodup v
  mem v a := by
    unfold cutRow
    split_ifs <;> simpa only [List.mem_rotate] using (rows s).mem v a

theorem cutRows_rotation (s : CellShape) : (cutRows s).rotation=(rows s).rotation := by
  apply Equiv.ext
  intro a
  change (cutRow s ((graph s).dartPair a).1).formPerm a=((rows s).row ((graph s).dartPair a).1).formPerm a
  unfold cutRow
  split_ifs
  · rw [List.formPerm_rotate _ ((rows s).nodup _)]
  · rfl

end FramedMacro
namespace FramedCanvas

def seedGraph (N : ℕ) : MultiGraph (Fin N) (Fin N) := ⟨id,finRotate N⟩

def seedRow (N : ℕ) (v : Fin N) : List (MultiGraph.Kasteleyn.Dart (Fin N)) := [(v,true),((finRotate N).symm v,false)]

def seedRows (N : ℕ) : RotationRows (seedGraph N) where
  row := seedRow N
  nodup v := by simp [seedRow]
  mem v a := by
    obtain ⟨e,b⟩:=a
    cases b <;> simp [seedRow,seedGraph,MultiGraph.dartPair,Equiv.eq_symm_apply]

abbrev PatchIndex (f : NumericFormula) := Option (Canvas.Index f)
def LocalVertex (f : NumericFormula) : PatchIndex f → Type
  | none => Fin (3*f.1)
  | some i => Fin (FramedMacro.vertexCount (canvasCell f i).shape)
def LocalDart (f : NumericFormula) : PatchIndex f → Type
  | none => MultiGraph.Kasteleyn.Dart (Fin (3*f.1))
  | some i => MultiGraph.Kasteleyn.Dart (PatchEdge f i)

def localSystem (f : NumericFormula) : ∀c,HostRowSystem (LocalVertex f c) (LocalDart f c)
  | none => HostRowSystem.ofRotationRows (seedGraph _) (seedRows _)
  | some i => HostRowSystem.ofRotationRows (FramedMacro.graph (canvasCell f i).shape)
      (FramedMacro.cutRows (canvasCell f i).shape)

def place (f : NumericFormula) : ∀c,LocalVertex f c→Vertex f
  | none => seedVertex f
  | some i => placeMacroVertex f i

def localVertices (f : NumericFormula) : ∀c,List (LocalVertex f c)
  | none => List.finRange (3*f.1)
  | some i => List.finRange (FramedMacro.vertexCount (canvasCell f i).shape)

def order (f : NumericFormula) : List (PatchIndex f) :=
  ((List.finRange (canvas f).length).reverse.map some)++[none]

theorem order_nodup (f : NumericFormula) : (order f).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨(List.nodup_reverse.mpr (List.nodup_finRange _)).map (Option.some_injective _),by simp,?_⟩
  simp

theorem order_mem (f : NumericFormula) (c : PatchIndex f) : c∈order f := by
  cases c <;> simp [order]

def rawSystem (f : NumericFormula) : HostRowSystem (Vertex f) (Sigma (LocalDart f)) :=
  HostRowSystem.assemble (localSystem f) (place f) (localVertices f)
    (by intro c; cases c <;> exact List.nodup_finRange _)
    (by intro c w; cases c <;> exact List.mem_finRange w)
    (order f) (order_nodup f) (order_mem f)

def dartEquiv (f : NumericFormula) : Sigma (LocalDart f)≃Dart f where
  toFun
    | ⟨none,a⟩ => seedDart f a
    | ⟨some i,a⟩ => patchDart f i a
  invFun
    | (.inl e,b) => ⟨none,(e,b)⟩
    | (.inr ⟨i,e⟩,b) => ⟨some i,(e,b)⟩
  left_inv a := by obtain ⟨c,a⟩:=a; cases c <;> rfl
  right_inv a := by obtain ⟨e,b⟩:=a; cases e <;> rfl

def system (f : NumericFormula) : HostRowSystem (Vertex f) (Dart f) := (rawSystem f).relabel (dartEquiv f)

theorem system_host (f : NumericFormula) (a : Dart f) : (system f).host a=((graph f).dartPair a).1 := by
  obtain ⟨e,b⟩:=a
  cases e with
  | inl e => cases b <;> rfl
  | inr e => obtain ⟨i,e⟩:=e; cases b <;> rfl

def fullRows (f : NumericFormula) : RotationRows (graph f) where
  row := (system f).row
  nodup := (system f).nodup
  mem v a := by rw [(system f).mem,system_host]

theorem fullRows_rotation (f : NumericFormula) : (fullRows f).rotation=(system f).rotation := by
  apply Equiv.ext
  intro a
  change ((system f).row ((graph f).dartPair a).1).formPerm a=((system f).row ((system f).host a)).formPerm a
  rw [system_host]

end FramedCanvas
end ColoringEmitter
end PlanarHom
