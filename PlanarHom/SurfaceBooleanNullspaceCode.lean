import PlanarHom.SurfaceBooleanNullspace
import PlanarHom.SurfaceBooleanFiniteMachines

/-! NEW exact bridge from the encoded nullspace generator lists to their
proved matrix kernel. -/
namespace PlanarHom.SurfaceBooleanRows

@[simp] theorem kernelRows_length (shape : Row) (rs : List Row) :
    (kernelRows shape rs).length=shape.length := by simp [kernelRows,transpose]

theorem kernelRows_width (shape : Row) (rs : List Row) (i : Fin (kernelRows shape rs).length) :
    ((kernelRows shape rs).get i).length=shape.length := by
  simp [kernelRows,transpose,List.get_eq_getElem]

theorem kernelRows_bitAt (shape : Row) (rs : List Row)
    (i : Fin (kernelRows shape rs).length) (j : Fin shape.length) :
    bitAt ((kernelRows shape rs).get i) j.val=
      bitAt (reduce (basis (normalizedRows shape rs)) (unit shape j.val)) i.val := by
  have hi : i.val<shape.length := by simpa using i.isLt
  simp [kernelRows,transpose,List.get_eq_getElem,bitAt,List.getElem?_map,
    List.getElem?_zipIdx,List.getElem?_eq_getElem j.isLt,hi]

theorem kernelRows_interpret (shape : Row) (rs : List Row) :
    (kernelRows shape rs).map (finiteValue shape.length)=List.ofFn (reductionMatrix shape rs) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hi' : i<(kernelRows shape rs).length := by simpa using hi
    have hi'' : i<shape.length := by simpa using hi'
    simp only [List.getElem_map,List.getElem_ofFn]
    funext j
    have hb := kernelRows_bitAt shape rs ⟨i,hi'⟩ j
    change bitValue (bitAt ((kernelRows shape rs).get ⟨i,hi'⟩) j.val)=_
    rw [hb]
    change value (reduce (basis (normalizedRows shape rs)) (unit shape j.val)) i=_
    rw [value_reduce,unit_value]
    rfl

def finiteSpan (shape : Row) (rs : List Row) : Submodule (ZMod 2) (Fin shape.length→ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range (fun i:Fin rs.length => finiteValue shape.length (rs.get i)))

theorem finiteSpan_eq (shape : Row) (rs : List Row) :
    finiteSpan shape rs=Submodule.span (ZMod 2) {x | x∈rs.map (finiteValue shape.length)} := by
  unfold finiteSpan
  congr 1
  ext x
  simp only [Set.mem_range,Set.mem_setOf_eq,List.mem_map]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨rs.get i,List.get_mem rs i,hi⟩
  · rintro ⟨r,hr,he⟩
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hr
    exact ⟨i,by rw [hi];exact he⟩

theorem kernelRows_span (shape : Row) (rs : List Row) :
    finiteSpan shape (kernelRows shape rs)=LinearMap.ker (inputMatrix shape rs).mulVecLin := by
  rw [finiteSpan_eq,kernelRows_interpret]
  have hs : {x | x∈List.ofFn (reductionMatrix shape rs)}=Set.range (reductionMatrix shape rs) := by
    ext x
    simp
  rw [hs]
  exact reduction_rows_span_kernel shape rs

end PlanarHom.SurfaceBooleanRows
