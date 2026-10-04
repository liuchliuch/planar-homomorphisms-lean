import PlanarHom.SurfaceBooleanBasis

/-! NEW executable elimination coefficients and their linear interpretation. -/
namespace PlanarHom.SurfaceBooleanRows
open scoped BigOperators

def coefficientList : BasisRows → Row → Row
  | [],_ => []
  | p::bs,r => bitAt r p.1 :: coefficientList bs (clear r p)

theorem coefficientFold (bs : BasisRows) (r z : Row) :
    bs.foldl (fun s p => (clear s.1 p,s.2++[bitAt s.1 p.1])) (r,z)=
      (reduce bs r,z++coefficientList bs r) := by
  induction bs generalizing r z with
  | nil => simp [reduce,coefficientList]
  | cons p bs ih =>
      simp only [List.foldl_cons,ih,coefficientList,reduce,List.foldl_cons]
      simp [List.append_assoc]

theorem coefficients_eq (bs : BasisRows) (r : Row) : coefficients bs r=coefficientList bs r := by
  simp [coefficients,coefficientFold]

@[simp] theorem coefficientList_length (bs : BasisRows) (r : Row) :
    (coefficientList bs r).length=bs.length := by
  induction bs generalizing r with
  | nil => rfl
  | cons p bs ih => simp [coefficientList,ih]

def coordinateMap : (bs : BasisRows) → (Vector →ₗ[ZMod 2] (Fin bs.length → ZMod 2))
  | [] => 0
  | p::bs => LinearMap.pi (Fin.cons (LinearMap.proj p.1)
      (fun i => (LinearMap.proj i).comp ((coordinateMap bs).comp (clearMap p))))

@[simp] theorem coordinateMap_cons_zero (p : PivotRow) (bs : BasisRows) (x : Vector) :
    coordinateMap (p::bs) x (0:Fin (bs.length+1))=x p.1 := rfl
@[simp] theorem coordinateMap_cons_succ (p : PivotRow) (bs : BasisRows) (x : Vector) (i : Fin bs.length) :
    coordinateMap (p::bs) x i.succ=coordinateMap bs (clearMap p x) i := rfl

theorem coefficientList_value (bs : BasisRows) (r : Row) (i : Fin bs.length) :
    value (coefficientList bs r) i.val=coordinateMap bs (value r) i := by
  induction bs generalizing r with
  | nil => exact Fin.elim0 i
  | cons p bs ih =>
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
          change value (coefficientList bs (clear r p)) i.val=coordinateMap bs (clearMap p (value r)) i
          rw [ih,value_clear]

theorem coefficients_value (bs : BasisRows) (r : Row) (i : Fin bs.length) :
    value (coefficients bs r) i.val=coordinateMap bs (value r) i := by
  rw [coefficients_eq]
  exact coefficientList_value bs r i

def reconstruct (bs : BasisRows) : (Fin bs.length → ZMod 2) →ₗ[ZMod 2] Vector :=
  ∑i, (LinearMap.proj i).smulRight (rowVectors bs i)

@[simp] theorem reconstruct_apply (bs : BasisRows) (x : Fin bs.length → ZMod 2) :
    reconstruct bs x=∑i,x i • rowVectors bs i := by simp [reconstruct]

theorem reconstruct_cons (p : PivotRow) (bs : BasisRows) (x : Fin (bs.length+1) → ZMod 2) :
    reconstruct (p::bs) x=x 0 • value p.2+reconstruct bs (fun i => x i.succ) := by
  rw [reconstruct_apply (p::bs) x,reconstruct_apply bs]
  change (∑i:Fin (bs.length+1),x i • rowVectors (p::bs) i)=_
  rw [Fin.sum_univ_succ]
  simp only [rowVectors_cons,Fin.cons_zero,Fin.cons_succ]

theorem reconstruction (bs : BasisRows) (x : Vector) :
    x=reduceMap bs x+reconstruct bs (coordinateMap bs x) := by
  induction bs generalizing x with
  | nil =>
      change x=x+reconstruct [] 0
      rw [map_zero,add_zero]
  | cons p bs ih =>
      rw [reduceMap_cons,reconstruct_cons]
      simp only [coordinateMap_cons_zero,coordinateMap_cons_succ]
      have ht := ih (clearMap p x)
      have he : clearMap p x=x+x p.1•value p.2 := rfl
      rw [he] at ht
      have hz : x p.1•value p.2+x p.1•value p.2=0 := by
        ext j
        change (x p.1*value p.2 j)+(x p.1*value p.2 j)=0
        exact ZModModule.add_self _
      calc
        x = (x+x p.1•value p.2)+x p.1•value p.2 := by rw [add_assoc,hz,add_zero]
        _ = _ := by rw [ht]; simp only [clearMap_apply]; abel

theorem reconstruct_injective (bs : BasisRows) (h : Echelon bs) : Function.Injective (reconstruct bs) := by
  have hi := echelon_independent bs h
  intro x y hxy
  apply_fun (fun z => z) at hxy
  have he : ∑i,(x i-y i)•rowVectors bs i=0 := by
    simpa only [reconstruct_apply,sub_smul,Finset.sum_sub_distrib,sub_eq_zero] using hxy
  have hz := (Fintype.linearIndependent_iff.mp hi) (fun i => x i-y i) he
  funext i
  exact sub_eq_zero.mp (hz i)

theorem coordinates_reconstruct (bs : BasisRows) (h : Echelon bs) (x : Fin bs.length → ZMod 2) :
    coordinateMap bs (reconstruct bs x)=x := by
  apply reconstruct_injective bs h
  have hr := reconstruction bs (reconstruct bs x)
  have hz : reduceMap bs (reconstruct bs x)=0 := by
    rw [reconstruct_apply,map_sum]
    simp only [map_smul]
    apply Finset.sum_eq_zero
    intro i _
    dsimp only [rowVectors]
    rw [reduceMap_row_zero bs h (bs.get i) (List.get_mem bs i),smul_zero]
  simpa only [hz,zero_add] using hr.symm

end PlanarHom.SurfaceBooleanRows
