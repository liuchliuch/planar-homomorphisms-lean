import PlanarHom.RepresentedInterpolationMatrices
import PlanarHom.RepresentedInterpolationListSystem
import PlanarHom.RepresentedPowerTableNodes

noncomputable section
open Classical
namespace PlanarHom.RepresentedInterpolationMatrices
open RepresentedBit RepresentedPowerTable RepresentedInterpolation
variable {K:Type} [Field K] (P:Presentation K) {t:ℕ} {A:Fin t→K}

theorem range_map_ofFn {B:Type} (n:ℕ) (f:ℕ→B) :
    (List.range n).map f=List.ofFn (fun i:Fin n=>f i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem matrix_values_scalar (ops:AddMulMachines P) (WA:WordProductMachine P A) (rs:List (Row P t))
    (hword:∀r∈rs,(r.2.2.val.map (RepresentedExponentWords.symbol A)).prod=source P r) :
    (matrix P ops WA rs).map (List.map P.value)=scalarRows (sourceNode P rs) (targetNode P rs) := by
  rw [matrix_values P ops WA rs hword,range_map_ofFn]
  unfold scalarRows
  congr 1
  · apply congrArg List.ofFn
    funext i
    congr 1
    exact (List.ofFn_getElem_eq_map rs (fun r=>source P r^(i.val+1))).symm
  · congr 1
    congr 1
    exact (List.ofFn_getElem_eq_map rs (fun r=> -target P r)).symm

theorem value_lookup {C:Type} (value:C→K) (z:C) (hz:value z=0) (xs:List C) (i:ℕ) :
    value (xs[i]?.getD z)=(xs.map value)[i]?.getD 0 := by
  cases h:xs[i]? <;> simp [List.getElem?_map,h,hz]

theorem value_row_lookup {C:Type} (value:C→K) (z:C) (hz:value z=0)
    (rs:List (List C)) (i j:ℕ) :
    value ((rs[i]?.getD [])[j]?.getD z)=((rs.map (List.map value))[i]?.getD [])[j]?.getD 0 := by
  cases h:rs[i]? with
  | none=>simp [List.getElem?_map,h,hz]
  | some r=>simpa [List.getElem?_map,h] using value_lookup value z hz r j

end PlanarHom.RepresentedInterpolationMatrices
