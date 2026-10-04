import PlanarHom.ParallelSourceRotation
import PlanarHom.FinitePermutationCycleCertificate
import PlanarHom.FinitePermutationArrowSubdivision

/-! Parallel thickening retains the old face permutation and adds exactly one
literal two-dart face between each pair of consecutive copies of each edge. -/
noncomputable section
open Classical
namespace PlanarHom.ParallelSource
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles
variable {V E : Type} [Fintype E] [DecidableEq (Dart E)] {G : MultiGraph V E}

 def outerDart (n : ℕ) (a : Dart E) : Dart (E×Fin (n+1)) := copyDart a 0
 def innerDart (n : ℕ) (a : Dart (E×Fin n)) : Dart (E×Fin (n+1)) :=
  if a.2 then ((a.1.1,a.1.2.succ),true) else ((a.1.1,a.1.2.castSucc),false)

 theorem reverse_outer (n : ℕ) (a : Dart E) :
    reversePerm (E×Fin (n+1)) (outerDart n a)=copyDart (reversePerm E a) (Fin.last n) := by
  rcases a with ⟨e,b⟩
  cases b <;> simp [outerDart,copyDart,orientedIndex,reversePerm]

 theorem face_outer (R : RotationRows G) (n : ℕ) (a : Dart E) :
    ((rows R (n+1)).rotation*reversePerm (E×Fin (n+1))) (outerDart n a)=
      outerDart n ((R.rotation*reversePerm E) a) := by
  rw [Equiv.Perm.mul_apply,reverse_outer,rotation_last]
  rfl

 theorem face_inner (R : RotationRows G) (n : ℕ) (a : Dart (E×Fin n)) :
    ((rows R (n+1)).rotation*reversePerm (E×Fin (n+1))) (innerDart n a)=
      innerDart n (reversePerm (E×Fin n) a) := by
  rcases a with ⟨⟨e,k⟩,b⟩
  cases b
  · have h := rotation_inner R (e,true) k.castSucc (by simpa using k.isLt)
    simpa [innerDart,copyDart,orientedIndex,reversePerm,Equiv.Perm.mul_apply] using h
  · have hj : k.succ.rev.val+1<n+1 := by simp only [Fin.val_rev,Fin.val_succ]; omega
    have h := rotation_inner R (e,false) k.succ.rev hj
    have he : copyDart (e,false) (⟨k.succ.rev.val+1,hj⟩ : Fin (n+1))=
        ((e,k.castSucc),false) := by
      simp only [copyDart,orientedIndex,Bool.false_eq_true,if_false]
      apply congrArg (fun j : Fin (n+1) => ((e,j),false))
      apply Fin.ext
      simp only [Fin.val_rev,Fin.val_succ,Fin.coe_castSucc]
      omega
    rw [he] at h
    simpa [innerDart,copyDart,orientedIndex,reversePerm,Equiv.Perm.mul_apply] using h

 def faceDartEquiv (n : ℕ) : Dart (E×Fin (n+1)) ≃ Dart E ⊕ Dart (E×Fin n) where
  toFun a := if a.2 then
      Fin.cases (.inl (a.1.1,true)) (fun k => .inr ((a.1.1,k),true)) a.1.2
    else if h : a.1.2.val<n then .inr ((a.1.1,⟨a.1.2.val,h⟩),false) else .inl (a.1.1,false)
  invFun a := match a with
    | .inl a => outerDart n a
    | .inr a => innerDart n a
  left_inv a := by
    rcases a with ⟨⟨e,i⟩,b⟩
    cases b
    · by_cases hi : i.val<n
      · simp only [Bool.false_eq_true,if_false,dif_pos hi,innerDart]
        rfl
      · simp only [Bool.false_eq_true,if_false,dif_neg hi,outerDart,copyDart,orientedIndex]
        apply congrArg (fun j : Fin (n+1) => ((e,j),false))
        apply Fin.ext
        simp only [Fin.val_rev,Fin.val_zero]
        omega
    · simp only [if_true]
      refine Fin.cases ?_ (fun k => ?_) i
      · simp [outerDart,copyDart,orientedIndex]
      · simp [innerDart]
  right_inv a := by
    rcases a with ⟨e,b⟩ | ⟨⟨e,k⟩,b⟩
    · cases b <;> simp [outerDart,copyDart,orientedIndex]
    · cases b <;> simp [innerDart,k.isLt]

 theorem faceDartEquiv_outer (n : ℕ) (a : Dart E) : faceDartEquiv n (outerDart n a)=.inl a :=
  (faceDartEquiv n).apply_symm_apply (.inl a)
 theorem faceDartEquiv_inner (n : ℕ) (a : Dart (E×Fin n)) : faceDartEquiv n (innerDart n a)=.inr a :=
  (faceDartEquiv n).apply_symm_apply (.inr a)

 theorem face_conjugacy (R : RotationRows G) (n : ℕ) (a : Dart (E×Fin (n+1))) :
    faceDartEquiv n (((rows R (n+1)).rotation*reversePerm (E×Fin (n+1))) a)=
      Equiv.sumCongr (R.rotation*reversePerm E) (reversePerm (E×Fin n)) (faceDartEquiv n a) := by
  obtain ⟨x,rfl⟩ := (faceDartEquiv n).symm.surjective a
  rw [Equiv.apply_symm_apply]
  cases x with
  | inl x => change faceDartEquiv n (((rows R (n+1)).rotation*reversePerm (E×Fin (n+1))) (outerDart n x))=_; rw [face_outer,faceDartEquiv_outer]; rfl
  | inr x => change faceDartEquiv n (((rows R (n+1)).rotation*reversePerm (E×Fin (n+1))) (innerDart n x))=_; rw [face_inner,faceDartEquiv_inner]; rfl

 theorem count_reverse (A : Type) [Fintype A] : count (reversePerm A)=Fintype.card A := by
  let C : LabelCertificate (reversePerm A) A := {
    label := Prod.fst
    root := fun a => (a,false)
    rank := fun a => if a.2 then 1 else 0
    root_label := fun _ => rfl
    step_label := fun _ => rfl
    zero_root := by rintro ⟨a,b⟩ h; cases b <;> simp_all
    step_rank := by rintro ⟨a,b⟩ h; cases b <;> simp_all [reversePerm] }
  exact C.count

 theorem parallel_face_count (R : RotationRows G) (n : ℕ) :
    count ((rows R (n+1)).rotation*reversePerm (E×Fin (n+1)))=
      count (R.rotation*reversePerm E)+Fintype.card E*n := by
  rw [count_of_step _ _ (faceDartEquiv n) (face_conjugacy R n),count_sumCongr,count_reverse]
  simp
end PlanarHom.ParallelSource
