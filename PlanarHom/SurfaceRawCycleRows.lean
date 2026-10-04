import PlanarHom.SurfaceRawHomologyRows
import PlanarHom.SurfaceBooleanRowSpanOn
import PlanarHom.SurfaceRotationHomology

/-! NEW exact primal incidence interpretation of the computed Boolean kernel. -/
namespace PlanarHom.SurfaceRawHomology
open SurfaceBooleanRows Complexity PlanarityLRRealization

def primalMatrix (g : MixedCode) : Matrix (Fin g.vertices) (Fin g.edges.length) (ZMod 2) :=
  fun v e => bitValue (decide ((g.edges.get e).1=v.val) ^^ decide ((g.edges.get e).2.1=v.val))

theorem cycleRows_span_raw (g : MixedCode) :
    rowSpanOn g.edges.length (cycleRows g)=LinearMap.ker (primalMatrix g).mulVecLin := by
  let A (n m : ℕ) : Matrix (Fin n) (Fin m) (ZMod 2) :=
    fun i j => bitValue (bitAt ((primalRows g)[i.val]?.getD []) j.val)
  have ha : inputMatrix (shape g) (primalRows g)=A (primalRows g).length (shape g).length := by
    funext i j
    simp [inputMatrix,A,finiteValue,value,List.getElem?_eq_getElem i.isLt,List.get_eq_getElem]
  have hk := kernelRows_span (shape g) (primalRows g)
  rw [←rowSpanOn_eq_finiteSpan,ha] at hk
  generalize hm : (shape g).length=m at hk
  generalize hn : (primalRows g).length=n at hk
  have hm' : m=g.edges.length := hm.symm.trans (shape_length g)
  have hn' : n=g.vertices := hn.symm.trans (primalRows_length g)
  clear hm hn
  subst m n
  have hA : A g.vertices g.edges.length=primalMatrix g := by
    funext v e
    simp [A,primalRows,bitAt,primalMatrix,v.isLt,e.isLt,List.get_eq_getElem]
  rw [hA] at hk
  exact hk

theorem primalMatrix_eq {bt ut : ℕ} (g : MixedCode) (hg : g.Valid bt ut) :
    primalMatrix g=((g.toMultiGraph hg).coboundaryMatrix (ZMod 2)).transpose := by
  funext v e
  simp only [primalMatrix,Matrix.transpose_apply,MultiGraph.coboundaryMatrix,
    MixedCode.toMultiGraph,bitValue_xor]
  have hs : (⟨(g.edges.get e).1,(hg.1 _ (List.get_mem _ _)).1⟩:Fin g.vertices)=v ↔
      (g.edges.get e).1=v.val := Fin.ext_iff
  have ht : (⟨(g.edges.get e).2.1,(hg.1 _ (List.get_mem _ _)).2.1⟩:Fin g.vertices)=v ↔
      (g.edges.get e).2.1=v.val := Fin.ext_iff
  simp only [hs,ht,bitValue,decide_eq_true_eq,ZModModule.sub_eq_add]

theorem cycleRows_span {bt ut : ℕ} (g : MixedCode) (hg : g.Valid bt ut)
    (R : RotationRows (g.toMultiGraph hg)) :
    rowSpanOn g.edges.length (cycleRows g)=R.cycleSpace := by
  rw [cycleRows_span_raw,primalMatrix_eq g hg]
  rfl

theorem cycleRows_width (g : MixedCode) (r : Row) (hr : r∈cycleRows g) : r.length=g.edges.length := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hr
  have hh := kernelRows_width (shape g) (primalRows g) i
  change ((cycleRows g).get i).length=(shape g).length at hh
  simpa only [hi,shape_length] using hh

end PlanarHom.SurfaceRawHomology
