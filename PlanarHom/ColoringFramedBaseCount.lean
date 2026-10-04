import PlanarHom.ColoringFramedSpliceProgram
import PlanarHom.ColoringBoundaryCycleSeed
import PlanarHom.FinitePermutationSigmaCount
import PlanarHom.FinitePermutationArrowSubdivision

/-! NEW exact sum of all initial seed/macro face cycles on the canonical
occurrence carrier. It includes every real local face and no virtual face. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.ColoringEmitter.FramedCanvas
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles
open PositiveBlockProgram ParsimoniousNorOneInThree

 theorem seedFace_eq (N : ℕ) : seedFace N=(ColoringBoundaryCycleSeed.rows N).facePerm := by
  apply Equiv.ext
  rintro ⟨e,b⟩
  cases b
  · exact (ColoringBoundaryCycleSeed.face_false N e).symm
  · exact (ColoringBoundaryCycleSeed.face_true N e).symm

 def baseDartEquiv (f : NumericFormula) : Dart f≃
    MultiGraph.Kasteleyn.Dart (Fin (3*f.1))⊕(Σi : Canvas.Index f,MultiGraph.Kasteleyn.Dart (PatchEdge f i)) where
  toFun
    | (.inl e,b) => .inl (e,b)
    | (.inr ⟨i,e⟩,b) => .inr ⟨i,(e,b)⟩
  invFun := Sum.elim (seedDart f) (fun p=>patchDart f p.1 p.2)
  left_inv a:=by rcases a with ⟨e|⟨i,e⟩,b⟩ <;> rfl
  right_inv a:=by rcases a with a|⟨i,a⟩ <;> rfl

 theorem baseFace_conjugacy (f : NumericFormula) (a : Dart f) :
    baseDartEquiv f (baseFace f a)=
      Equiv.sumCongr (seedFace (3*f.1)) (sigmaPerm (fun i : Canvas.Index f=>(FramedMacro.rows (canvasCell f i).shape).facePerm)) (baseDartEquiv f a) := by
  rcases a with ⟨e|⟨i,e⟩,b⟩ <;> rfl

 theorem baseFace_count (f : NumericFormula) (hn : 0<f.1) :
    count (baseFace f)=2+∑i : Canvas.Index f,count (FramedMacro.rows (canvasCell f i).shape).facePerm := by
  rw [count_semiconj _ _ (baseDartEquiv f) (baseFace_conjugacy f),count_sumCongr,count_sigmaPerm,seedFace_eq,
    ColoringBoundaryCycleSeed.face_count (3*f.1) (by omega)]

 theorem macro_euler_sum (f : NumericFormula) :
    (∑i : Canvas.Index f,FramedMacro.vertexCount (canvasCell f i).shape)+
      (∑i : Canvas.Index f,count (FramedMacro.rows (canvasCell f i).shape).facePerm)=
      (∑i : Canvas.Index f,FramedMacro.edgeCount (canvasCell f i).shape)+2*(canvas f).length := by
  have hh:=Finset.sum_congr (s₁:=Finset.univ) (s₂:=Finset.univ) rfl
    (fun i (_ : i∈(Finset.univ : Finset (Canvas.Index f)))=>FramedMacro.euler (canvasCell f i).shape)
  simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,Nat.mul_comm] using hh

end PlanarHom.ColoringEmitter.FramedCanvas
