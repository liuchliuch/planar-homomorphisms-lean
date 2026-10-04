import PlanarHom.RankFourTensorClosure
import PlanarHom.RankFourBooleanFactors

noncomputable section
open Classical
namespace PlanarHom.RankFour
open Structures Boolean

theorem singleton_positive_class {C:Type} [Unique C] (a:ℝ) (ha:0<a) :
    NonnegativeClass (fun _ _ : C=>a) := by
  let e : C≃Cube 0 := Equiv.ofUnique _ _
  have h:=scaled_tensor_allowed a ha (fun i:Fin 0=>i.elim0) (fun i=>i.elim0) e
  simpa using h.nonnegativeClass

theorem swap_class (γ:ℝ) (hγ:0<γ) : NonnegativeClass (fun i j=>γ*RankFour.swap i j) := by
  let e : Bool≃Bool×Cube 0 := (Equiv.prodUnique _ _).symm
  have h:=scaled_swap_tensor_allowed γ hγ (fun i:Fin 0=>i.elim0) (fun i=>i.elim0) e
  simpa [e] using h.nonnegativeClass

theorem ising_class (γ ρ:ℝ) (hγ:0<γ) (hρ:0<ρ) : NonnegativeClass (fun i j=>γ*W ρ i j) := by
  have h:=scaled_tensor_allowed γ hγ (fun _:Fin 1=>ρ) (fun _=>hρ)
    (Equiv.funUnique (Fin 1) Bool).symm
  simpa [tensor] using h.nonnegativeClass

def boolFiber (v:Bool) : {i:Bool//i=v}≃Unit where
  toFun:=fun _=>()
  invFun:=fun _=>⟨v,rfl⟩
  left_inv:=by intro i; apply Subtype.ext; exact i.property.symm
  right_inv:=by intro i; rfl

theorem diagonal_class (a c:ℝ) (ha:0<a) (hc:0<c) :
    NonnegativeClass (fun i j:Bool=>if i=j then (if i then c else a) else 0) := by
  apply nonnegativeClass_of_partition _ id Function.surjective_id
  · intro i j he; exact if_neg he
  · intro r
    have hr : 0<(if r then c else a) := by cases r <;> assumption
    have h:=scaled_tensor_allowed (if r then c else a) hr (fun i:Fin 0=>i.elim0) (fun i=>i.elim0)
      ((boolFiber r).trans (Equiv.ofUnique _ _))
    convert h using 1
    funext i j
    have hi:i.val=r:=i.property
    have hj:j.val=r:=j.property
    simp [hi,hj]

theorem BooleanNormal.nonnegativeClass {A:Matrix Bool Bool ℝ} (h:BooleanNormal A) : NonnegativeClass A := by
  cases h with
  | diagonal a c ha hc hm =>
    have he : A=(fun i j=>if i=j then (if i then c else a) else 0) := funext (fun i=>funext (hm i))
    rw [he]; exact diagonal_class a c ha hc
  | swap γ hγ hm =>
    have he : A=(fun i j=>γ*RankFour.swap i j) := funext (fun i=>funext (hm i))
    rw [he]; exact swap_class γ hγ
  | ising γ ρ hγ hρ hm =>
    have he : A=(fun i j=>γ*W ρ i j) := funext (fun i=>funext (hm i))
    rw [he]; exact ising_class γ ρ hγ hρ

def firstFalseEquiv : {i:Bool×Bool//i.1=false}≃Bool where
  toFun:=fun i=>i.val.2
  invFun:=fun i=>⟨(false,i),rfl⟩
  left_inv:=by intro i; apply Subtype.ext; exact Prod.ext i.property.symm rfl
  right_inv:=fun _=>rfl

def firstTrueEquiv : {i:Bool×Bool//¬i.1=false}≃Bool where
  toFun:=fun i=>i.val.2
  invFun:=fun i=>⟨(true,i),by simp⟩
  left_inv:=by
    rintro ⟨⟨x,y⟩,h⟩
    cases x
    · exact (h rfl).elim
    · rfl
  right_inv:=fun _=>rfl

theorem diagonal_product_class (a c:ℝ) (ha:0<a) (hc:0<c)
    (B:Matrix Bool Bool ℝ) (hB:NonnegativeClass B) :
    NonnegativeClass (factorProduct (fun i j=>if i=j then (if i then c else a) else 0) B) := by
  apply NonnegativeClass.of_split (fun i:Bool×Bool=>i.1=false)
  · intro i j hi hj
    have he:i.1≠j.1:=fun he=>hj (he.symm.trans hi)
    simp only [factorProduct,if_neg he,zero_mul]
  · intro i j hi hj
    have he:i.1≠j.1:=fun he=>hi (he.trans hj)
    simp only [factorProduct,if_neg he,zero_mul]
  · have h:=(hB.posScalar a ha).equiv firstFalseEquiv
    convert h using 1
    funext i j
    simp [factorProduct,i.property,j.property,firstFalseEquiv]
  · have h:=(hB.posScalar c hc).equiv firstTrueEquiv
    convert h using 1
    funext i j
    have hi:i.val.1=true:=by
      cases hh:i.val.1
      · exact (i.property hh).elim
      · rfl
    have hj:j.val.1=true:=by
      cases hh:j.val.1
      · exact (j.property hh).elim
      · rfl
    simp [factorProduct,hi,hj,firstTrueEquiv]

theorem product_comm_class (A B:Matrix Bool Bool ℝ)
    (h:NonnegativeClass (factorProduct A B)) : NonnegativeClass (factorProduct B A) := by
  have h':=h.equiv (Equiv.prodComm Bool Bool)
  convert h' using 1
  funext i j
  exact mul_comm _ _

def equalBitsEquiv : {i:Bool×Bool//i.1=i.2}≃Bool where
  toFun:=fun i=>i.val.1
  invFun:=fun i=>⟨(i,i),rfl⟩
  left_inv:=by intro i; apply Subtype.ext; exact Prod.ext rfl i.property
  right_inv:=fun _=>rfl

def unequalBitsEquiv : {i:Bool×Bool//¬i.1=i.2}≃Bool where
  toFun:=fun i=>i.val.1
  invFun:=fun i=>⟨(i,!i),by cases i <;> decide⟩
  left_inv:=by
    rintro ⟨⟨x,y⟩,h⟩
    cases x <;> cases y <;> first | rfl | exact (h rfl).elim
  right_inv:=fun _=>rfl

theorem swap_swap_class (γ δ:ℝ) (hγ:0<γ) (hδ:0<δ) :
    NonnegativeClass (factorProduct (fun i j=>γ*RankFour.swap i j) (fun i j=>δ*RankFour.swap i j)) := by
  apply NonnegativeClass.of_split (fun i:Bool×Bool=>i.1=i.2)
  · rintro ⟨x,y⟩ ⟨z,w⟩ hi hj
    cases x <;> cases y <;> cases z <;> cases w <;> simp_all [factorProduct,swap]
  · rintro ⟨x,y⟩ ⟨z,w⟩ hi hj
    cases x <;> cases y <;> cases z <;> cases w <;> simp_all [factorProduct,swap]
  · have h:=(swap_class (γ*δ) (mul_pos hγ hδ)).equiv equalBitsEquiv
    convert h using 1
    funext i j
    rcases i with ⟨⟨x,y⟩,hi⟩; rcases j with ⟨⟨z,w⟩,hj⟩
    change x=y at hi
    change z=w at hj
    cases x <;> cases y <;> cases z <;> cases w <;> simp at hi hj <;> simp [factorProduct,swap,equalBitsEquiv]
  · have h:=(swap_class (γ*δ) (mul_pos hγ hδ)).equiv unequalBitsEquiv
    convert h using 1
    funext i j
    rcases i with ⟨⟨x,y⟩,hi⟩; rcases j with ⟨⟨z,w⟩,hj⟩
    change x≠y at hi
    change z≠w at hj
    cases x <;> cases y <;> cases z <;> cases w <;> simp at hi hj <;> simp [factorProduct,swap,unequalBitsEquiv]

theorem swap_ising_class (γ δ ρ:ℝ) (hγ:0<γ) (hδ:0<δ) (hρ:0<ρ) :
    NonnegativeClass (factorProduct (fun i j=>γ*RankFour.swap i j) (fun i j=>δ*W ρ i j)) := by
  apply SingleTensor.nonnegativeClass
  refine Or.inr ⟨γ*δ,ρ,Equiv.refl _,mul_pos hγ hδ,hρ,?_⟩
  intro i j; dsimp [factorProduct]; ring

theorem ising_ising_class (γ δ ρ σ:ℝ) (hγ:0<γ) (hδ:0<δ) (hρ:0<ρ) (hσ:0<σ) :
    NonnegativeClass (factorProduct (fun i j=>γ*W ρ i j) (fun i j=>δ*W σ i j)) := by
  apply SingleTensor.nonnegativeClass
  refine Or.inl ⟨γ*δ,![ρ,σ],(finTwoArrowEquiv Bool).symm,mul_pos hγ hδ,?_,?_⟩
  · intro i; fin_cases i <;> assumption
  · intro i j
    simp [factorProduct,tensor,Fin.prod_univ_two,finTwoArrowEquiv]
    ring

end PlanarHom.RankFour
