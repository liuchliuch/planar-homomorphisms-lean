import PlanarHom.ColoringFramedCanvasRows
import PlanarHom.PortPatchRowPreimage

noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.FramedCanvas
open MultiGraph MultiGraph.Kasteleyn PositiveBlockProgram ParsimoniousNorOneInThree
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def patchWord (f : NumericFormula) (i : Canvas.Index f) (v : Vertex f) : List (Dart f) :=
  (List.finRange (FramedMacro.vertexCount (canvasCell f i).shape)).flatMap (fun w=>
    if placeMacroVertex f i w=v then (FramedMacro.cutRow (canvasCell f i).shape w).map (patchDart f i) else [])

def seedWord (f : NumericFormula) (v : Vertex f) : List (Dart f) :=
  (List.finRange (3*f.1)).flatMap (fun w=>if seedVertex f w=v then (seedRow (3*f.1) w).map (seedDart f) else [])

theorem fullRows_word (f : NumericFormula) (v : Vertex f) :
    (fullRows f).row v=((List.finRange (canvas f).length).reverse.flatMap (fun i=>patchWord f i v))++seedWord f v := by
  simp only [fullRows,system,rawSystem,HostRowSystem.relabel,HostRowSystem.assemble,
    HostRowSystem.word,HostRowSystem.localWord,order,List.map_flatMap,List.flatMap_append,
    List.map_append,List.flatMap_map,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  simp [localVertices,localSystem,HostRowSystem.ofRotationRows,place,dartEquiv,
    patchWord,seedWord,List.map_map,Function.comp_def,FramedMacro.cutRows,seedRows,apply_ite]
  rfl

theorem placeMacroVertex_injective (f : NumericFormula) (i : Canvas.Index f) :
    Function.Injective (placeMacroVertex f i) := by
  intro v w h
  apply (FramedMacro.vertexParts (canvasCell f i).shape).symm.injective
  generalize hv : (FramedMacro.vertexParts (canvasCell f i).shape).symm v=x
  generalize hw : (FramedMacro.vertexParts (canvasCell f i).shape).symm w=y
  unfold placeMacroVertex at h
  rw [hv,hw] at h
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      apply congrArg Sum.inl
      apply (LocalPatch.localVertexParts (canvasCell f i).shape).symm.injective
      exact Canvas.placeVertex_injective f i (Sum.inl.inj h)
    | inr b => cases h
  | inr a =>
    cases y with
    | inl b => cases h
    | inr b => exact congrArg Sum.inr (congrArg Prod.snd (Sum.inr.inj h))

theorem seedVertex_injective (f : NumericFormula) : Function.Injective (seedVertex f) := by
  intro a b h
  have hh:=Sum.inl.inj (Sum.inl.inj h)
  have hd:=congrArg (fun s : Canvas.BoundaryTriple f=>s.1.val.2) hh
  have hc:=congrArg (fun s : Canvas.BoundaryTriple f=>s.2.val) hh
  change a.val/3=b.val/3 at hd
  change 2-a.val%3=2-b.val%3 at hc
  have ha:=Nat.mod_lt a.val (by omega : 0<3)
  have hb:=Nat.mod_lt b.val (by omega : 0<3)
  apply Fin.ext
  omega

theorem patchWord_preimage (f : NumericFormula) (i : Canvas.Index f)
    (v : Fin (FramedMacro.vertexCount (canvasCell f i).shape)) :
    patchWord f i (placeMacroVertex f i v)=(FramedMacro.cutRow (canvasCell f i).shape v).map (patchDart f i) := by
  unfold patchWord
  simp only [(placeMacroVertex_injective f i).eq_iff]
  exact PortPatchAssembly.selectWord_eq _ (List.nodup_finRange _) v (List.mem_finRange _) _

theorem seedWord_preimage (f : NumericFormula) (v : Fin (3*f.1)) :
    seedWord f (seedVertex f v)=(seedRow (3*f.1) v).map (seedDart f) := by
  unfold seedWord
  simp only [(seedVertex_injective f).eq_iff]
  exact PortPatchAssembly.selectWord_eq _ (List.nodup_finRange _) v (List.mem_finRange _) _

theorem patchWord_eq_nil (f : NumericFormula) (i : Canvas.Index f) (v : Vertex f)
    (h : ∀w,placeMacroVertex f i w≠v) : patchWord f i v=[] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro w _
  exact if_neg (h w)

theorem seedWord_eq_nil (f : NumericFormula) (v : Vertex f) (h : ∀w,seedVertex f w≠v) : seedWord f v=[] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro w _
  exact if_neg (h w)

end PlanarHom.ColoringEmitter.FramedCanvas
