import PlanarHom.SurfaceBooleanFiniteRows

/-! NEW nullspace generators obtained by transposing the actual reduction map.
Every vector annihilating the input rows is fixed by the transposed projection. -/
namespace PlanarHom.SurfaceBooleanRows
open scoped BigOperators

def inputMatrix (shape : Row) (rs : List Row) :
    Matrix (Fin rs.length) (Fin shape.length) (ZMod 2) :=
  fun i j => finiteValue shape.length (rs.get i) j

def reductionMatrix (shape : Row) (rs : List Row) :
    Matrix (Fin shape.length) (Fin shape.length) (ZMod 2) :=
  fun i j => reduceMap (basis (normalizedRows shape rs)) (unitVector j) i.val

theorem reductionMatrix_mulVec (shape : Row) (rs : List Row) (x : Vector)
    (hx : Bounded shape.length x) :
    (reductionMatrix shape rs).mulVec (fun j => x j.val)=
      fun i => reduceMap (basis (normalizedRows shape rs)) x i.val := by
  funext i
  conv_rhs => rw [←sum_units x hx,map_sum]
  simp only [map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
    Matrix.mulVec,dotProduct,reductionMatrix]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem pair_zero_of_input_kernel (shape : Row) (rs : List Row)
    (x : Fin shape.length→ZMod 2) (hx : (inputMatrix shape rs).mulVec x=0) :
    rowSpan (basis (normalizedRows shape rs))≤LinearMap.ker (pair shape.length x) := by
  rw [basis_span]
  apply Submodule.span_le.mpr
  rintro y ⟨r,hr,rfl⟩
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hs
  have he := congrFun hx i
  change (∑j:Fin shape.length,finiteValue shape.length (rs.get i) j*x j)=0 at he
  change pair shape.length x (value (normalize shape s))=0
  rw [pair_apply]
  have hn := normalize_finiteValue shape s
  have hh : (fun j:Fin shape.length => value (normalize shape s) j.val)=finiteValue shape.length s := hn
  simp_rw [show ∀j:Fin shape.length,value (normalize shape s) j.val=finiteValue shape.length s j from congrFun hh]
  rw [←hi]
  simpa only [mul_comm] using he

theorem reductionMatrix_row_kernel (shape : Row) (rs : List Row) (i : Fin shape.length) :
    (inputMatrix shape rs).mulVec (reductionMatrix shape rs i)=0 := by
  funext j
  have hm : value (normalize shape (rs.get j))∈rowSpan (basis (normalizedRows shape rs)) := by
    rw [basis_span]
    exact Submodule.subset_span ⟨_,List.mem_map.mpr ⟨_,List.get_mem rs j,rfl⟩,rfl⟩
  have hz := rowSpan_le_ker (basis (normalizedRows shape rs)) (echelon_basis _) hm
  have hq := congrFun (reductionMatrix_mulVec shape rs (value (normalize shape (rs.get j)))
    (value_bounded _ _ (by simp))) i
  change reduceMap (basis (normalizedRows shape rs)) (value (normalize shape (rs.get j)))=0 at hz
  rw [hz] at hq
  change (∑k:Fin shape.length,finiteValue shape.length (rs.get j) k*reductionMatrix shape rs i k)=0
  change (∑k:Fin shape.length,reductionMatrix shape rs i k*value (normalize shape (rs.get j)) k.val)=0 at hq
  have hn := normalize_finiteValue shape (rs.get j)
  change (∑k:Fin shape.length,reductionMatrix shape rs i k*finiteValue shape.length (normalize shape (rs.get j)) k)=0 at hq
  rw [hn] at hq
  simpa only [mul_comm] using hq

theorem input_kernel_fixed (shape : Row) (rs : List Row)
    (x : Fin shape.length→ZMod 2) (hx : (inputMatrix shape rs).mulVec x=0) :
    x=(reductionMatrix shape rs).transpose.mulVec x := by
  funext j
  have hd := reduction_difference_mem (basis (normalizedRows shape rs)) (unitVector j)
  have hz := pair_zero_of_input_kernel shape rs x hx hd
  change pair shape.length x (unitVector j-reduceMap (basis (normalizedRows shape rs)) (unitVector j))=0 at hz
  rw [map_sub,pair_unit,sub_eq_zero] at hz
  rw [hz,pair_apply]
  simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,reductionMatrix,mul_comm]

theorem reduction_rows_span_kernel (shape : Row) (rs : List Row) :
    Submodule.span (ZMod 2) (Set.range (reductionMatrix shape rs))=
      LinearMap.ker (inputMatrix shape rs).mulVecLin := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨i,rfl⟩
    exact reductionMatrix_row_kernel shape rs i
  · intro x hx
    have he := input_kernel_fixed shape rs x hx
    have hs : (∑i:Fin shape.length,x i • reductionMatrix shape rs i)∈
        Submodule.span (ZMod 2) (Set.range (reductionMatrix shape rs)) := by
      apply Submodule.sum_mem
      intro i _
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)
    have hh : (∑i:Fin shape.length,x i • reductionMatrix shape rs i)=x := by
      conv_rhs => rw [he]
      funext j
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Matrix.mulVec,
        dotProduct,Matrix.transpose_apply,mul_comm]
    rwa [hh] at hs

end PlanarHom.SurfaceBooleanRows
