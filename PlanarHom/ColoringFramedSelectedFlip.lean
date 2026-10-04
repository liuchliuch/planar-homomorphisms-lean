import PlanarHom.ColoringFramedDartPartition
import PlanarHom.ColoringFramedSelectedComponents
import PlanarHom.RadialPottsBoundaryPermutation

noncomputable section
namespace PlanarHom.ColoringEmitter.FramedCanvas
open MultiGraph MultiGraph.Kasteleyn ParsimoniousNorOneInThree RadialPotts.Assembly PlanarityLRRealization

theorem keepDart_none_iff (f : NumericFormula) (d : Dart f) : keepDart f d=none ↔ keepEdge f d.1=false := by
  obtain ⟨e,b⟩:=d
  cases e with
  | inl e => simp [keepDart,keepEdge]
  | inr e =>
    obtain ⟨i,e⟩:=e
    by_cases h : e.val<(Macro.edges (PositiveBlockProgram.canvasCell f i).shape.kind).length
    all_goals simp [keepDart,keepEdge,h]

theorem selectedFlip_oldDart (f : NumericFormula) (a : MultiGraph.Kasteleyn.Dart (Canvas.Edge f)) :
    selectedFlip (keepEdge f) (oldDart f a)=oldDart f (reversePerm _ a) := by
  obtain ⟨⟨i,e⟩,b⟩:=a
  simp [selectedFlip,oldDart,oldEdge,FramedMacro.oldEdge,keepEdge,e.isLt,reversePerm]

theorem selectedFlip_fixed_of_deleted (f : NumericFormula) (d : Dart f) (h : keepDart f d=none) :
    selectedFlip (keepEdge f) d=d := by
  have hh:=(keepDart_none_iff f d).mp h
  obtain ⟨e,b⟩:=d
  simp [selectedFlip,hh]

theorem partition_selectedFlip (f : NumericFormula) :
    (dartPartition f).permCongr (selectedFlip (keepEdge f))=
      Equiv.sumCongr (reversePerm (Canvas.Edge f)) (Equiv.refl (Fin (markerCount f))) := by
  apply Equiv.ext
  intro x
  cases x with
  | inl a =>
    simp only [Equiv.permCongr_apply,partition_symm_inl,selectedFlip_oldDart,partition_oldDart]
    rfl
  | inr m =>
    have hh : keepDart f ((dartPartition f).symm (.inr m))=none := by
      rw [←partition_keep,Equiv.apply_symm_apply]
      rfl
    simp only [Equiv.permCongr_apply,selectedFlip_fixed_of_deleted f _ hh,Equiv.apply_symm_apply]
    rfl

end PlanarHom.ColoringEmitter.FramedCanvas
