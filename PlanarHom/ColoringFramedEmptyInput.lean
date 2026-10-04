import PlanarHom.ColoringFramedBaseCount

/-! NEW empty-input branch for the literal framed face program. A valid
zero-variable exact-one instance has no clauses and hence emits no cells. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.ColoringEmitter.FramedCanvas
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles
open PositiveBlockProgram ParsimoniousNorOneInThree

 theorem valid_zero_formula (f : NumericFormula) (hf : NumericValid f) (hz : f.1=0) : f.2=[] := by
  by_contra hn
  obtain ⟨c,cs,hc⟩:=List.exists_cons_of_ne_nil hn
  have hh:=hf c (by rw [hc]; simp)
  omega

 theorem positive_inputs_of_formula_nonempty (f : NumericFormula) (hf : NumericValid f) (hn : f.2≠[]) : 0<f.1 := by
  by_contra hz
  exact hn (valid_zero_formula f hf (by omega))

 theorem canvas_nil_of_zero (f : NumericFormula) (hf : NumericValid f) (hz : f.1=0) : canvas f=[] := by
  have hh:=valid_zero_formula f hf hz
  simp only [canvas,hh,formulaCells]

 theorem edge_empty_of_zero (f : NumericFormula) (hf : NumericValid f) (hz : f.1=0) : IsEmpty (Edge f) := by
  have hc:=canvas_nil_of_zero f hf hz
  constructor
  rintro (e|⟨i,e⟩)
  · have he:=e.isLt
    omega
  · have hi:=i.isLt
    change i.val<(canvas f).length at hi
    have hlen : (canvas f).length=0 := congrArg List.length hc
    omega

 theorem finalFace_count_zero (f : NumericFormula) (hf : NumericValid f) (hz : f.1=0) : count (finalFace f hf)=0 := by
  letI:=edge_empty_of_zero f hf hz
  exact count_empty _

 theorem face_fold_zero (f : NumericFormula) (hf : NumericValid f) (hz : f.1=0) :
    count (finalFace f hf)+2*(canvas f).length=count (baseFace f)+
      ((canvas f).map (fun c=>FramedMacro.leftCount c.shape)).sum := by
  letI:=edge_empty_of_zero f hf hz
  rw [canvas_nil_of_zero f hf hz,count_empty (finalFace f hf),count_empty (baseFace f)]
  simp

end PlanarHom.ColoringEmitter.FramedCanvas
