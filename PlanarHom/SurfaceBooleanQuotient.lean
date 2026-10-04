import PlanarHom.SurfaceBooleanCoordinates

/-! NEW quotient coordinates from two actual row families: reduce cycle
rows modulo face rows, then compute a basis of those literal residuals. -/
namespace PlanarHom.SurfaceBooleanRows

def quotientRows (faces cycles : List Row) : BasisRows :=
  basis (cycles.map (reduce (basis faces)))

def quotientEncode (faces cycles : List Row) :
    Vector →ₗ[ZMod 2] (Fin (quotientRows faces cycles).length → ZMod 2) :=
  (coordinateMap (quotientRows faces cycles)).comp (reduceMap (basis faces))

def quotientLift (faces cycles : List Row) :
    (Fin (quotientRows faces cycles).length → ZMod 2) →ₗ[ZMod 2] Vector :=
  reconstruct (quotientRows faces cycles)

theorem inputSpan_reduce (bs : BasisRows) (rs : List Row) :
    inputSpan (rs.map (reduce bs))=(inputSpan rs).map (reduceMap bs) := by
  rw [inputSpan,inputSpan,Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨r,hr,hx⟩
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
    exact ⟨value s,⟨s,hs,rfl⟩,(value_reduce bs s).symm.trans hx⟩
  · rintro ⟨y,⟨r,hr,rfl⟩,hx⟩
    exact ⟨reduce bs r,List.mem_map.mpr ⟨r,hr,rfl⟩,(value_reduce bs r).trans hx⟩

theorem quotientRows_span (faces cycles : List Row) :
    rowSpan (quotientRows faces cycles)=(inputSpan cycles).map (reduceMap (basis faces)) := by
  rw [quotientRows,basis_span,inputSpan_reduce]

theorem reduceMap_idempotent (bs : BasisRows) (h : Echelon bs) (x : Vector) :
    reduceMap bs (reduceMap bs x)=reduceMap bs x := by
  have hz := rowSpan_le_ker bs h (reduction_difference_mem bs x)
  change reduceMap bs (x-reduceMap bs x)=0 at hz
  rw [map_sub,sub_eq_zero] at hz
  exact hz.symm

theorem reconstruct_mem (bs : BasisRows) (x : Fin bs.length→ZMod 2) :
    reconstruct bs x∈rowSpan bs := by
  rw [reconstruct_apply]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (row_mem_span bs (bs.get i) (List.get_mem bs i))

theorem quotient_reduce_fixed (faces cycles : List Row) (x : Vector)
    (hx : x∈rowSpan (quotientRows faces cycles)) : reduceMap (basis faces) x=x := by
  rw [quotientRows_span] at hx
  obtain ⟨y,hy,rfl⟩ := hx
  exact reduceMap_idempotent _ (echelon_basis _) y

theorem quotientEncode_lift (faces cycles : List Row)
    (x : Fin (quotientRows faces cycles).length→ZMod 2) :
    quotientEncode faces cycles (quotientLift faces cycles x)=x := by
  change coordinateMap (quotientRows faces cycles)
    (reduceMap (basis faces) (reconstruct (quotientRows faces cycles) x))=x
  rw [quotient_reduce_fixed faces cycles _ (reconstruct_mem _ x)]
  exact coordinates_reconstruct _ (echelon_basis _) x

theorem quotientLift_mem (faces cycles : List Row) (h : inputSpan faces ≤ inputSpan cycles)
    (x : Fin (quotientRows faces cycles).length→ZMod 2) :
    quotientLift faces cycles x∈inputSpan cycles := by
  have hx := reconstruct_mem (quotientRows faces cycles) x
  rw [quotientRows_span] at hx
  obtain ⟨y,hy,he⟩ := hx
  have hd := reduction_difference_mem (basis faces) y
  rw [basis_span] at hd
  have hh := Submodule.sub_mem (inputSpan cycles) hy (h hd)
  rw [sub_sub_cancel,he] at hh
  exact hh

theorem quotientEncode_kernel (faces cycles : List Row) (x : Vector)
    (hx : x∈inputSpan cycles) : quotientEncode faces cycles x=0 ↔ x∈inputSpan faces := by
  have hr : reduceMap (basis faces) x∈rowSpan (quotientRows faces cycles) := by
    rw [quotientRows_span]
    exact ⟨x,hx,rfl⟩
  have hz := rowSpan_le_ker (quotientRows faces cycles) (echelon_basis _) hr
  change reduceMap (quotientRows faces cycles) (reduceMap (basis faces) x)=0 at hz
  constructor
  · intro he
    have hre := reconstruction (quotientRows faces cycles) (reduceMap (basis faces) x)
    change coordinateMap (quotientRows faces cycles) (reduceMap (basis faces) x)=0 at he
    rw [hz,he,map_zero,add_zero] at hre
    rw [←basis_span faces,←ker_reduceMap _ (echelon_basis _)]
    exact hre
  · intro he
    rw [←basis_span faces,←ker_reduceMap _ (echelon_basis _)] at he
    change reduceMap (basis faces) x=0 at he
    change coordinateMap (quotientRows faces cycles) (reduceMap (basis faces) x)=0
    rw [he,map_zero]

end PlanarHom.SurfaceBooleanRows
