import PlanarHom.ExponentVectorMachines
import PlanarHom.FixedExponentProductMachines

/-! Actual fixed-alphabet product tables, retaining a target product for every
source exponent vector before nonzero filtering and collision merging. -/
namespace PlanarHom.ExponentProductTables
open Turing PlanarHom.Complexity
open scoped BigOperators

private def asFunction {t : ℕ} (xs : List ℕ) (h : xs.length=t) : Fin t→ℕ:=
  fun i=>xs.get ⟨i.val,by simpa only [h] using i.isLt⟩

private theorem ofFn_asFunction {t : ℕ} (xs : List ℕ) (h : xs.length=t) :
    List.ofFn (asFunction xs h)=xs:=by
  subst t
  exact List.ofFn_get xs

/-- The attached membership proof changes no serialized data. -/
def vectors (t m : ℕ) : List (Fin t→ℕ):=
  (PlanarHom.ExponentVectors.weak t m).attach.map (fun xs=>
    asFunction xs.val ((PlanarHom.ExponentVectors.mem_weak t m xs.val).mp xs.property).1)

theorem vectors_encoding (t m : ℕ) :
    (BitEncoding.nat.vector t).list.encode (vectors t m)=
      BitEncoding.nat.list.list.encode (PlanarHom.ExponentVectors.weak t m):=by
  have hword {xs : List ℕ} (h : xs.length=t) :
      (BitEncoding.nat.vector t).encode (asFunction xs h)=BitEncoding.nat.list.encode xs:=by
    simp only [BitEncoding.vector,ofFn_asFunction]
  have hm : (vectors t m).map (BitEncoding.nat.vector t).encode=
      (PlanarHom.ExponentVectors.weak t m).map BitEncoding.nat.list.encode:=by
    rw [vectors,List.map_map]
    change ((PlanarHom.ExponentVectors.weak t m).attach.map (fun xs=> (BitEncoding.nat.vector t).encode (asFunction xs.val ((PlanarHom.ExponentVectors.mem_weak t m xs.val).mp xs.property).1)))=_
    simp only [hword]
    exact List.attach_map_val
  change BitEncoding.frame (BitEncoding.nat.encode (vectors t m).length)++BitEncoding.frames
    ((vectors t m).map (BitEncoding.nat.vector t).encode)=
    BitEncoding.frame (BitEncoding.nat.encode (PlanarHom.ExponentVectors.weak t m).length)++
      BitEncoding.frames ((PlanarHom.ExponentVectors.weak t m).map BitEncoding.nat.list.encode)
  rw [hm]
  have hl : (vectors t m).length=(PlanarHom.ExponentVectors.weak t m).length:=by simp [vectors]
  rw [hl]

theorem fp_vectors (t : ℕ) :
    FP BitEncoding.unaryNat (BitEncoding.nat.vector t).list (vectors t):=
  (PlanarHom.ExponentVectorMachines.fp_weak t).transportOutput (fun m=>(vectors_encoding t m).symm)

theorem length_vectors (t m : ℕ) : (vectors t m).length≤(m+1)^t:=by
  simpa [vectors] using PlanarHom.ExponentVectors.length_weak_le t m

theorem coordinate_le {t m : ℕ} {r : Fin t→ℕ} (hr : r∈vectors t m) (i : Fin t) : r i≤m:=by
  obtain ⟨xs,hxs,he⟩:=List.mem_map.mp hr
  subst r
  exact PlanarHom.ExponentVectors.coordinate_le xs.property (List.get_mem xs.val _)

theorem sum_eq {t m : ℕ} {r : Fin t→ℕ} (hr : r∈vectors t m) : (∑i,r i)=m:=by
  obtain ⟨xs,hxs,he⟩:=List.mem_map.mp hr
  subst r
  rw [←List.sum_ofFn,ofFn_asFunction]
  exact ((PlanarHom.ExponentVectors.mem_weak t m xs.val).mp xs.property).2

variable {K : Type} [Field K] [Algebra ℚ K] {dimension t : ℕ}

def products (A B : Fin t→K) (m : ℕ) : List (K × K):=
  (vectors t m).map (fun r=>(∏i,A i^(r i),∏i,B i^(r i)))

omit [Algebra ℚ K] in
theorem length_products (A B : Fin t→K) (m : ℕ) : (products A B m).length≤(m+1)^t:=by
  simpa only [products,List.length_map] using length_vectors t m

/-- The table is generated and every source/target product is computed by real
FP machines. Equality of source products will later select original table rows. -/
theorem fp_products (basis : Module.Basis (Fin dimension) ℚ K) (A B : Fin t→K) :
    FP BitEncoding.unaryNat ((numberFieldEncoding basis).prod (numberFieldEncoding basis)).list
      (products A B):=by
  have hm:=PlanarHom.ListContextMachines.fp_mapWithContext BitEncoding.unaryNat (BitEncoding.nat.vector t)
    ((numberFieldEncoding basis).prod (numberFieldEncoding basis))
    (fun p=>(∏i,A i^(min p.1 (p.2 i)),∏i,B i^(min p.1 (p.2 i))))
    (PlanarHom.FixedExponentProductMachines.fp_product_pair basis A B)
  have h:=((fp_id BitEncoding.unaryNat).pair (fp_vectors t)).comp hm
  apply h.congr
  intro m
  apply List.map_congr_left
  intro r hr
  change (∏i,A i^(min m (r i)),∏i,B i^(min m (r i)))=(∏i,A i^(r i),∏i,B i^(r i))
  rw [PlanarHom.FixedExponentProductMachines.clipped_product_eq A m r (coordinate_le hr),
    PlanarHom.FixedExponentProductMachines.clipped_product_eq B m r (coordinate_le hr)]

end PlanarHom.ExponentProductTables
