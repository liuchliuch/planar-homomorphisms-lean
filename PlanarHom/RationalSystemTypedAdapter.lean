import PlanarHom.DenseRationalSystemCorrectness

/-! Finite-matrix views of the raw rational-function system solver. These only
change indices and use the actual literal list program. -/
noncomputable section
namespace PlanarHom.DensePolynomial
variable (n m:ℕ)

def typedSystem (a:Fin m→Fin m→FractionCode n) (b:Fin m→FractionCode n) : System n :=
  (List.ofFn (fun i=>List.ofFn (a i)),List.ofFn b)

theorem typedSystem_valid (a:Fin m→Fin m→FractionCode n) (b:Fin m→FractionCode n)
    (ha:∀i j,FractionValid n (a i j)) (hb:∀i,FractionValid n (b i)) :
    SystemValid n (typedSystem n m a b) := by
  constructor
  · intro row hr x hx
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hr
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hx
    exact ha i j
  · intro x hx
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hx
    exact hb i

theorem typedSystem_matrix (a:Fin m→Fin m→FractionCode n) (b:Fin m→FractionCode n) :
    systemMatrix n (typedSystem n m a b)=fun i j=>fractionValue n (a ⟨i.val,by simpa [typedSystem] using i.isLt⟩ ⟨j.val,by simpa [typedSystem] using j.isLt⟩) := by
  funext i j
  have hi:i.val<m:=by simpa [typedSystem] using i.isLt
  have hj:j.val<m:=by simpa [typedSystem] using j.isLt
  simp only [systemMatrix,systemEntry,typedSystem,List.getElem?_ofFn,hi,hj,dif_pos,Option.getD_some]

def typedIndex (a:Fin m→Fin m→FractionCode n) (b:Fin m→FractionCode n) :
    Fin m ≃ Fin (typedSystem n m a b).1.length := finCongr (by simp [typedSystem])

@[simp] theorem typedIndex_val (a:Fin m→Fin m→FractionCode n) (b:Fin m→FractionCode n) (i:Fin m) :
    (typedIndex n m a b i).val=i.val := rfl
@[simp] theorem typedIndex_symm_val (a:Fin m→Fin m→FractionCode n) (b:Fin m→FractionCode n)
    (i:Fin (typedSystem n m a b).1.length) : ((typedIndex n m a b).symm i).val = i.val := rfl

theorem typedSystem_reindex (a:Fin m→Fin m→FractionCode n) (b:Fin m→FractionCode n) :
    systemMatrix n (typedSystem n m a b)=Matrix.reindex (typedIndex n m a b) (typedIndex n m a b)
      (fun i j=>fractionValue n (a i j)) := by
  rw [typedSystem_matrix]
  rfl

theorem solve_typed_correct (a:Fin m→Fin m→FractionCode n) (b:Fin m→FractionCode n)
    (ha:∀i j,FractionValid n (a i j)) (hb:∀i,FractionValid n (b i))
    (h:(show Matrix (Fin m) (Fin m) (RationalFunction n) from fun i j=>fractionValue n (a i j)).det≠0) :
    (show Matrix (Fin m) (Fin m) (RationalFunction n) from fun i j=>fractionValue n (a i j)).mulVec
      (fun k=>fractionValue n ((solve n (typedSystem n m a b))[k.val]?.getD (fractionZero n)))=
      fun i=>fractionValue n (b i) := by
  have hn:(systemMatrix n (typedSystem n m a b)).det≠0 := by
    rw [typedSystem_reindex,Matrix.det_reindex_self]
    exact h
  have hs:=solve_correct n (typedSystem n m a b) (typedSystem_valid n m a b ha hb) hn
  rw [typedSystem_reindex] at hs
  funext i
  have hh:=congrFun hs (typedIndex n m a b i)
  simp only [Matrix.mulVec,dotProduct,Matrix.reindex_apply,Matrix.submatrix_apply,
    Equiv.symm_apply_apply] at hh
  rw [←(typedIndex n m a b).sum_comp] at hh
  simpa only [Equiv.symm_apply_apply,typedIndex,finCongr_apply,Fin.coe_cast,Matrix.mulVec,dotProduct,systemVector,systemRhs,typedSystem,
    List.getElem?_ofFn,i.isLt,dif_pos,Option.getD_some,Fin.eta] using hh

theorem solve_typed_valid (a:Fin m→Fin m→FractionCode n) (b:Fin m→FractionCode n)
    (ha:∀i j,FractionValid n (a i j)) (hb:∀i,FractionValid n (b i))
    (h:(show Matrix (Fin m) (Fin m) (RationalFunction n) from fun i j=>fractionValue n (a i j)).det≠0)
    (k:Fin m) : FractionValid n ((solve n (typedSystem n m a b))[k.val]?.getD (fractionZero n)) := by
  have hn:(systemMatrix n (typedSystem n m a b)).det≠0 := by
    rw [typedSystem_reindex,Matrix.det_reindex_self]
    exact h
  exact solve_output_valid n (typedSystem n m a b) (typedSystem_valid n m a b ha hb) hn
    (typedIndex n m a b k)

end PlanarHom.DensePolynomial
