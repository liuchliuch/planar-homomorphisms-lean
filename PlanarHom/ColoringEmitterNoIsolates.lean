import PlanarHom.ColoringCanvasNoIsolates
import PlanarHom.ColoringEmitterComputedRows
import PlanarHom.RotationRowsTransport

/-! No added isolate markers are needed for the literal coloring compiler.
The empty-formula branch emits no vertices; every other valid source emits only
vertices incident to genuine coloring edges. -/
noncomputable section
namespace PlanarHom.ColoringEmitter
open MultiGraph MultiGraph.Kasteleyn ParsimoniousNorOneInThree

 theorem compile_dart_host_surjective_nonempty (f : NumericFormula) (hf : NumericValid f) (hne : f.2≠[]) :
    Function.Surjective (fun a : Dart (Fin (compile f).edges.length)=>
      (((compile f).toMultiGraph (compile_valid f)).dartPair a).1) := by
  intro v
  let i:=Canvas.compile_incidenceEquiv f hf hne
  obtain ⟨a,ha⟩:=Canvas.dart_host_surjective f hf hne (i.vertex.symm v)
  refine ⟨i.darts a,?_⟩
  dsimp only at ha ⊢
  rw [i.dart_host,ha,i.vertex.apply_symm_apply]

 theorem compile_dart_host_surjective (f : NumericFormula) (hf : NumericValid f) :
    Function.Surjective (fun a : Dart (Fin (compile f).edges.length)=>
      (((compile f).toMultiGraph (compile_valid f)).dartPair a).1) := by
  by_cases h : f.2=[]
  · intro v
    have hv:=v.isLt
    simp [compile,h] at hv
  · exact compile_dart_host_surjective_nonempty f hf h

 theorem compile_incident (f : NumericFormula) (hf : NumericValid f) (v : Fin (compile f).vertices) :
    ∃e,((compile f).toMultiGraph (compile_valid f)).src e=v ∨
      ((compile f).toMultiGraph (compile_valid f)).dst e=v := by
  obtain ⟨⟨e,b⟩,he⟩:=compile_dart_host_surjective f hf v
  cases b
  · exact ⟨e,Or.inr he⟩
  · exact ⟨e,Or.inl he⟩

end PlanarHom.ColoringEmitter
