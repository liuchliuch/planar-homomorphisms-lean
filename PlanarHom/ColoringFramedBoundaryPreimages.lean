import PlanarHom.ColoringFramedCanvasRowWords
import PlanarHom.ColoringFramedMarkerHosts
import PlanarHom.ColoringFramedPortOwners
import PlanarHom.ColoringFramedBaseRotation

/-! Exact local preimages of every canonical boundary triple in the framed
canvas. Private vertices and frame corners cannot supply an extra boundary row. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.FramedCanvas
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization PositiveBlockProgram ParsimoniousNorOneInThree

 theorem place_portVertex (f : NumericFormula) (i : Canvas.Index f)
    (p : LocalPatch.Port (canvasCell f i).shape) :
    placeMacroVertex f i (FramedMacro.portVertex (canvasCell f i).shape p)=.inl (.inl (Canvas.port f i p)) := by
  rw [FramedMacro.portVertex,place_oldVertex,←LocalPatch.localVertexParts_port,Equiv.symm_apply_apply]
  rfl

 theorem place_boundary_iff (f : NumericFormula) (i : Canvas.Index f)
    (v : Fin (FramedMacro.vertexCount (canvasCell f i).shape)) (b : Canvas.BoundaryTriple f) :
    placeMacroVertex f i v=.inl (.inl b) ↔
      ∃p : LocalPatch.Port (canvasCell f i).shape,v=FramedMacro.portVertex (canvasCell f i).shape p ∧ Canvas.port f i p=b := by
  constructor
  · intro he
    unfold placeMacroVertex at he
    cases hv : (FramedMacro.vertexParts (canvasCell f i).shape).symm v with
    | inr k => rw [hv] at he; cases he
    | inl w =>
        rw [hv] at he
        dsimp only [Sum.elim] at he
        cases hp : (LocalPatch.localVertexParts (canvasCell f i).shape).symm w with
        | inr k => rw [hp] at he; cases he
        | inl p =>
            rw [hp] at he
            refine ⟨p,?_,Sum.inl.inj (Sum.inl.inj he)⟩
            apply (FramedMacro.vertexParts (canvasCell f i).shape).symm.injective
            rw [hv,FramedMacro.portVertex,FramedMacro.oldVertex,Equiv.symm_apply_apply]
            apply congrArg Sum.inl
            apply (LocalPatch.localVertexParts (canvasCell f i).shape).symm.injective
            rw [hp,←LocalPatch.localVertexParts_port,Equiv.symm_apply_apply]
  · rintro ⟨p,rfl,hp⟩
    rw [place_portVertex,hp]

 theorem seed_boundary_iff (f : NumericFormula) (e : Fin (3*f.1)) (b : Canvas.BoundaryTriple f) :
    seedVertex f e=.inl (.inl b) ↔
      ∃i : Fin f.1,b.1=initialBoundary f i ∧ e=initialVertex f i b.2 := by
  constructor
  · intro he
    let i : Fin f.1 := ⟨e.val/3,by have h:=e.isLt; omega⟩
    let c : Fin 3 := ⟨2-e.val%3,by have h:=Nat.mod_lt e.val (by omega : 0<3); omega⟩
    have hp : (initialBoundary f i,c)=b := Sum.inl.inj (Sum.inl.inj he)
    refine ⟨i,(congrArg Prod.fst hp).symm,?_⟩
    have hc := congrArg Prod.snd hp
    rw [←hc]
    apply Fin.ext
    change e.val=3*(e.val/3)+(2-(2-e.val%3))
    have hmod := Nat.mod_lt e.val (by omega : 0<3)
    omega
  · rintro ⟨i,hi,rfl⟩
    rw [seedVertex_initialVertex,←hi]

 theorem initial_origin_signal (f : NumericFormula) (hf : NumericValid f) (b : Canvas.BoundaryTriple f)
    (i : Fin f.1) (h : (Canvas.signalEquiv f hf).symm b.1=.inl i) : b.1=initialBoundary f i := by
  have hh := congrArg (Canvas.signalEquiv f hf) h
  simpa only [Equiv.apply_symm_apply,Canvas.signalEquiv_initial] using hh

 theorem output_origin_signal (f : NumericFormula) (hf : NumericValid f) (b : Canvas.BoundaryTriple f)
    (i : Canvas.Index f) (o : Fin (canvasCell f i).shape.outputCount)
    (h : (Canvas.signalEquiv f hf).symm b.1=.inr ⟨i,o⟩) :
    b.1=boundaryPort f i ((canvasCell f i).freshPort o) := by
  have hh := congrArg (Canvas.signalEquiv f hf) h
  simpa only [Equiv.apply_symm_apply,Canvas.signalEquiv_output] using hh

 theorem seedWord_initial (f : NumericFormula) (hf : NumericValid f) (b : Canvas.BoundaryTriple f)
    (i : Fin f.1) (h : (Canvas.signalEquiv f hf).symm b.1=.inl i) :
    seedWord f (.inl (.inl b))=blockWord f none (initialVertex f i b.2) := by
  have hs := initial_origin_signal f hf b i h
  have hb : b=(initialBoundary f i,b.2) := Prod.ext hs rfl
  rw [hb,←seedVertex_initialVertex f i b.2,seedWord_preimage]
  rfl

 theorem seedWord_output (f : NumericFormula) (hf : NumericValid f) (b : Canvas.BoundaryTriple f)
    (i : Canvas.Index f) (o : Fin (canvasCell f i).shape.outputCount)
    (h : (Canvas.signalEquiv f hf).symm b.1=.inr ⟨i,o⟩) : seedWord f (.inl (.inl b))=[] := by
  apply seedWord_eq_nil
  intro e he
  obtain ⟨a,ha,_⟩ := (seed_boundary_iff f e b).mp he
  rw [ha,←Canvas.signalEquiv_initial f hf a,Equiv.symm_apply_apply] at h
  cases h

 theorem patchWord_boundary (f : NumericFormula) (i : Canvas.Index f)
    (p : LocalPatch.Port (canvasCell f i).shape) :
    patchWord f i (.inl (.inl (Canvas.port f i p)))=
      blockWord f (some i) (FramedMacro.portVertex (canvasCell f i).shape p) := by
  rw [←place_portVertex,patchWord_preimage]
  rfl

 theorem patchWord_boundary_nil (f : NumericFormula) (i : Canvas.Index f) (b : Canvas.BoundaryTriple f)
    (h : ∀p : LocalPatch.Port (canvasCell f i).shape,Canvas.port f i p≠b) :
    patchWord f i (.inl (.inl b))=[] := by
  apply patchWord_eq_nil
  intro v hv
  obtain ⟨p,_,hp⟩ := (place_boundary_iff f i v b).mp hv
  exact h p hp
end PlanarHom.ColoringEmitter.FramedCanvas
