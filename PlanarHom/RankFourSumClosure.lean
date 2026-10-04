import PlanarHom.RankFourStructuralTransport

noncomputable section
open Classical
namespace PlanarHom.Structures
variable {C D B E : Type}

def sumMatrix (A : Matrix C C ℝ) (B : Matrix D D ℝ) : Matrix (C⊕D) (C⊕D) ℝ
  | .inl i,.inl j=>A i j
  | .inr i,.inr j=>B i j
  | _,_=>0

def sumFiberLeft (b:C→B) (c:D→E) (r:B) :
    {z:C⊕D//Sum.map b c z=Sum.inl r} ≃ {i//b i=r} where
  toFun := fun z=>match z with
    | ⟨.inl i,h⟩=>⟨i,Sum.inl.inj h⟩
    | ⟨.inr _,h⟩=>by cases h
  invFun := fun i=>⟨.inl i.val,congrArg Sum.inl i.property⟩
  left_inv := by
    rintro ⟨z,h⟩
    cases z with
    | inl i => cases h <;> rfl
    | inr i => cases h <;> rfl
  right_inv := by intro i; rfl

def sumFiberRight (b:C→B) (c:D→E) (r:E) :
    {z:C⊕D//Sum.map b c z=Sum.inr r} ≃ {i//c i=r} where
  toFun := fun z=>match z with
    | ⟨.inr i,h⟩=>⟨i,Sum.inr.inj h⟩
    | ⟨.inl _,h⟩=>by cases h
  invFun := fun i=>⟨.inr i.val,congrArg Sum.inr i.property⟩
  left_inv := by
    rintro ⟨z,h⟩
    cases z with
    | inl i => cases h <;> rfl
    | inr i => cases h <;> rfl
  right_inv := by intro i; rfl

theorem NonnegativeClass.sum {A : Matrix C C ℝ} {B : Matrix D D ℝ}
    (hA : NonnegativeClass A) (hB : NonnegativeClass B) : NonnegativeClass (sumMatrix A B) := by
  obtain ⟨t,b,hb,hz,ha⟩:=hA
  obtain ⟨u,c,hc,hz',ha'⟩:=hB
  apply nonnegativeClass_of_partition _ (Sum.map b c)
  · intro r; cases r with
    | inl r => obtain ⟨i,hi⟩:=hb r; exact ⟨.inl i,congrArg Sum.inl hi⟩
    | inr r => obtain ⟨i,hi⟩:=hc r; exact ⟨.inr i,congrArg Sum.inr hi⟩
  · intro i j h; cases i <;> cases j
    · exact hz _ _ (fun he=>h (congrArg Sum.inl he))
    · rfl
    · rfl
    · exact hz' _ _ (fun he=>h (congrArg Sum.inr he))
  · intro r; cases r with
    | inl r =>
      have h := (ha r).equiv (sumFiberLeft b c r)
      convert h using 1
      funext i j
      rcases i with ⟨i,hi⟩; rcases j with ⟨j,hj⟩
      cases i with
      | inl i => cases j with
        | inl j => rfl
        | inr j => cases hj
      | inr i => cases hi
    | inr r =>
      have h := (ha' r).equiv (sumFiberRight b c r)
      convert h using 1
      funext i j
      rcases i with ⟨i,hi⟩; rcases j with ⟨j,hj⟩
      cases i with
      | inr i => cases j with
        | inr j => rfl
        | inl j => cases hj
      | inl i => cases hi

theorem NonnegativeClass.of_split {M : Matrix C C ℝ} (p:C→Prop)
    (hz : ∀i j,p i→¬p j→M i j=0) (hz' : ∀i j,¬p i→p j→M i j=0)
    (ha : NonnegativeClass (fun i j:{c//p c}=>M i.val j.val))
    (hb : NonnegativeClass (fun i j:{c//¬p c}=>M i.val j.val)) : NonnegativeClass M := by
  have h:=(ha.sum hb).equiv (Equiv.sumCompl p).symm
  convert h using 1
  funext i j
  by_cases hi:p i <;> by_cases hj:p j <;>
    simp [Equiv.sumCompl_apply_symm_of_pos,Equiv.sumCompl_apply_symm_of_neg,hi,hj,sumMatrix]
  · exact hz i j hi hj
  · exact hz' i j hi hj

end PlanarHom.Structures
