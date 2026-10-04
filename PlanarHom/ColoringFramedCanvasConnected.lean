import PlanarHom.ColoringFramedCanvasRows
import PlanarHom.ColoringFramedFutureSupport
import PlanarHom.ColoringBoundaryCycleSeed
import PlanarHom.FisherExpansionConnected

/-! NEW connectedness of the canonical framed augmentation. Every real cell
attaches to an initial or strictly earlier output signal, proved by allocation. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.FramedCanvas
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles
open PositiveBlockProgram ParsimoniousNorOneInThree

 theorem place_port_vertex (f : NumericFormula) (i : Canvas.Index f) (p : LocalPatch.Port (canvasCell f i).shape) :
    placeMacroVertex f i (FramedMacro.portVertex (canvasCell f i).shape p)=.inl (.inl (Canvas.port f i p)) := by
  rw [FramedMacro.portVertex,place_oldVertex]
  change Sum.inl (PortPatchAssembly.placeVertex (W:=Canvas.Private f) (Canvas.port f) i
    ((LocalPatch.localVertexParts _).symm ((LocalPatch.localVertexParts _) (.inl p))))=_
  rw [Equiv.symm_apply_apply]
  rfl

 theorem seedVertex_initial (f : NumericFormula) (i : Fin f.1) (b : Fin 3) :
    seedVertex f (initialVertex f i b)=.inl (.inl (initialBoundary f i,b)) := by
  apply congrArg Sum.inl
  apply congrArg Sum.inl
  apply Prod.ext
  · apply Subtype.ext
    change (0,(3*i.val+(2-b.val))/3)=(0,i.val)
    have hb:=b.isLt
    congr 1
    omega
  · apply Fin.ext
    change 2-(3*i.val+(2-b.val))%3=b.val
    have hb:=b.isLt
    omega

 theorem patch_connected (f : NumericFormula) (i : Canvas.Index f) (a b : Fin (FramedMacro.vertexCount (canvasCell f i).shape)) :
    (graph f).componentSetoid Finset.univ (placeMacroVertex f i a) (placeMacroVertex f i b) := by
  let color : Fin (FramedMacro.vertexCount (canvasCell f i).shape)→(graph f).Components Finset.univ :=
    fun v=>Quotient.mk _ (placeMacroVertex f i v)
  apply Quotient.exact ((FramedMacro.graph (canvasCell f i).shape).edgeConstant_respects Finset.univ color ?_
    (FramedMacro.connected (canvasCell f i).shape a b))
  intro e _
  exact Quotient.sound (Relation.EqvGen.rel _ _ ⟨.inr ⟨i,e⟩,Finset.mem_univ _,rfl,rfl⟩)

 theorem seed_connected (f : NumericFormula) (hn : 0<f.1) (a b : Fin (3*f.1)) :
    (graph f).componentSetoid Finset.univ (seedVertex f a) (seedVertex f b) := by
  let color : Fin (3*f.1)→(graph f).Components Finset.univ := fun v=>Quotient.mk _ (seedVertex f v)
  apply Quotient.exact ((ColoringBoundaryCycleSeed.graph (3*f.1)).edgeConstant_respects Finset.univ color ?_
    (ColoringBoundaryCycleSeed.connected (3*f.1) (by omega) a b))
  intro e _
  exact Quotient.sound (Relation.EqvGen.rel _ _ ⟨.inl e,Finset.mem_univ _,rfl,rfl⟩)

 theorem patch_reaches_seed (f : NumericFormula) (hf : NumericValid f) (hn : 0<f.1)
    (i : Canvas.Index f) (v : Fin (FramedMacro.vertexCount (canvasCell f i).shape)) :
    (graph f).componentSetoid Finset.univ (placeMacroVertex f i v) (seedVertex f ⟨0,by omega⟩) := by
  suffices ∀k,∀i : Canvas.Index f,i.val=k→∀v,
      (graph f).componentSetoid Finset.univ (placeMacroVertex f i v) (seedVertex f ⟨0,by omega⟩) from this i.val i rfl v
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro i hik v
      let q : LocalPatch.Port (canvasCell f i).shape := FramedMacro.leftPort (canvasCell f i).shape ⟨0,FramedMacro.leftCount_pos _⟩
      have hp : q.1∈(canvasCell f i).shape.leftPorts := FramedMacro.leftPort_mem _ _
      have hstart:=patch_connected f i v (FramedMacro.portVertex (canvasCell f i).shape q)
      rw [place_port_vertex] at hstart
      rcases Canvas.input_origin f hf i q.1 hp with ⟨r,hr⟩|⟨j,o,hji,hjo⟩
      · have hb:=congrArg (Canvas.signalEquiv f hf) hr
        simp only [Equiv.apply_symm_apply,Canvas.signalEquiv_initial] at hb
        have he : Canvas.port f i q=(initialBoundary f r,q.2) := Prod.ext hb rfl
        rw [he,←seedVertex_initial f r q.2] at hstart
        exact Relation.EqvGen.trans _ _ _ hstart (seed_connected f hn _ _)
      · have hb:=congrArg (Canvas.signalEquiv f hf) hjo
        simp only [Equiv.apply_symm_apply,Canvas.signalEquiv_output] at hb
        have he : Canvas.port f i q=Canvas.port f j ((canvasCell f j).freshPort o,q.2) := Prod.ext hb rfl
        rw [he,←place_port_vertex] at hstart
        exact Relation.EqvGen.trans _ _ _ hstart (ih j.val (by omega) j rfl _)

 theorem graph_connected (f : NumericFormula) (hf : NumericValid f) (hn : 0<f.1) :
    ∀a b,(graph f).componentSetoid Finset.univ a b := by
  have hbase (v : Vertex f) : (graph f).componentSetoid Finset.univ v (seedVertex f ⟨0,by omega⟩) := by
    rcases v with ((⟨b,ch⟩|⟨i,w⟩)|⟨i,k⟩)
    · obtain ⟨r,hr⟩:=(Canvas.signalEquiv f hf).surjective b
      cases r with
      | inl r =>
          have hb : b=initialBoundary f r := hr.symm
          rw [hb,←seedVertex_initial f r ch]
          exact seed_connected f hn _ _
      | inr r =>
          rcases r with ⟨i,o⟩
          have hb : b=boundaryPort f i ((canvasCell f i).freshPort o) := hr.symm
          rw [hb]
          change (graph f).componentSetoid Finset.univ (.inl (.inl (Canvas.port f i ((canvasCell f i).freshPort o,ch)))) _
          rw [←place_port_vertex]
          exact patch_reaches_seed f hf hn i _
    · have he : placeMacroVertex f i (FramedMacro.oldVertex _ w.val)=.inl (.inr ⟨i,w⟩) := by
        rw [place_oldVertex]
        change Sum.inl (PortPatchAssembly.placeVertex (W:=Canvas.Private f) (Canvas.port f) i
          ((LocalPatch.localVertexParts _).symm ((LocalPatch.localVertexParts _) (.inr w))))=_
        rw [Equiv.symm_apply_apply]
        rfl
      rw [←he]
      exact patch_reaches_seed f hf hn i _
    · have he : placeMacroVertex f i (FramedMacro.vertexParts _ (.inr k))=.inr (i,k) := by
        simp only [placeMacroVertex,Equiv.symm_apply_apply,Sum.elim_inr]
      rw [←he]
      exact patch_reaches_seed f hf hn i _
  intro a b
  exact Relation.EqvGen.trans _ _ _ (hbase a) (Relation.EqvGen.symm _ _ (hbase b))

 theorem graph_incident (f : NumericFormula) (hf : NumericValid f) (hn : 0<f.1) :
    ∀v,∃a : Dart f,((graph f).dartPair a).1=v := by
  letI : Nonempty (Edge f) := ⟨.inl ⟨0,by omega⟩⟩
  exact Fisher.incident_of_connected (graph_connected f hf hn)

 theorem graph_componentCount (f : NumericFormula) (hf : NumericValid f) (hn : 0<f.1) :
    (graph f).componentCount Finset.univ=1 := by
  letI : Subsingleton ((graph f).Components Finset.univ) := ⟨by
    intro a b
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b => exact Quotient.sound (graph_connected f hf hn a b)⟩
  letI : Nonempty ((graph f).Components Finset.univ) := ⟨Quotient.mk _ (seedVertex f ⟨0,by omega⟩)⟩
  exact (Nat.card_eq_fintype_card (α:=(graph f).Components Finset.univ)).symm.trans Nat.card_unique

end PlanarHom.ColoringEmitter.FramedCanvas
