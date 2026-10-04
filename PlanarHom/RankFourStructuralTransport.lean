import PlanarHom.MainStructuralSupportTransport

/-! Finite nonempty block partitions, restriction to a block complement, and
actual simultaneous direct-sum charts. -/
noncomputable section
open Classical
namespace PlanarHom.Structures
variable {C D B : Type} [Fintype B]

theorem nonnegativeClass_of_partition (M : Matrix C C ℝ) (block : C→B)
    (hs : Function.Surjective block)
    (hz : ∀i j,block i≠block j→M i j=0)
    (ha : ∀r,AllowedBlock (fun i j:{c//block c=r}=>M i.val j.val)) :
    NonnegativeClass M := by
  let e := Fintype.equivFin B
  refine ⟨Fintype.card B,e∘block,e.surjective.comp hs,?_,?_⟩
  · intro i j h
    exact hz i j (fun he=>h (congrArg e he))
  · intro r
    exact (ha (e.symm r)).equiv (Equiv.subtypeEquivRight
      (fun c=>e.apply_eq_iff_eq_symm_apply))

theorem AllowedBlock.nonnegativeClass {M : Matrix C C ℝ} (h : AllowedBlock M) :
    NonnegativeClass M := by
  refine ⟨1,fun _=>0,?_,?_,?_⟩
  · intro r
    have hn : Nonempty C := by
      cases h with
      | zero e hz => exact ⟨e.symm ()⟩
      | positive k d hk a ρ ha hρ e hm =>
        exact ⟨e.symm (⟨0,hk⟩,fun _=>false)⟩
      | bipartite k l d hk hl a b ρ ha hb hρ e hm =>
        exact ⟨e.symm (.inl ⟨0,hk⟩,fun _=>false)⟩
    exact ⟨Classical.choice hn,Subsingleton.elim _ _⟩
  · intro i j h; exact (h rfl).elim
  · intro r
    exact h.equiv {
      toFun := Subtype.val
      invFun := fun c => ⟨c,Subsingleton.elim _ _⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem NonnegativeClass.equiv {M : Matrix C C ℝ} (h : NonnegativeClass M) (e:D≃C) :
    NonnegativeClass (fun i j=>M (e i) (e j)) := by
  obtain ⟨t,b,hs,hz,ha⟩:=h
  refine ⟨t,b∘e,hs.comp e.surjective,?_,?_⟩
  · exact fun i j h=>hz _ _ h
  · intro r
    exact (ha r).equiv (e.subtypeEquiv (fun _=>Iff.rfl))

theorem complement_fiber_class (M : Matrix C C ℝ) {t:ℕ} (b:C→Fin t)
    (hs : Function.Surjective b) (hz : ∀i j,b i≠b j→M i j=0)
    (ha : ∀r,AllowedBlock (fun i j:{c//b c=r}=>M i.val j.val)) (r:Fin t) :
    NonnegativeClass (fun i j:{c//b c≠r}=>M i.val j.val) := by
  let b' : {c//b c≠r}→{s:Fin t//s≠r} := fun c=>⟨b c.val,c.property⟩
  apply nonnegativeClass_of_partition _ b'
  · intro s
    obtain ⟨c,hc⟩:=hs s.val
    exact ⟨⟨c,by simpa [hc] using s.property⟩,Subtype.ext hc⟩
  · intro i j hij
    exact hz _ _ (fun he=>hij (Subtype.ext he))
  · intro s
    let e : {i : {c//b c≠r} // b' i=s} ≃ {c//b c=s.val} := {
      toFun := fun i=>⟨i.val.val,congrArg Subtype.val i.property⟩
      invFun := fun i=>⟨⟨i.val,by simpa [i.property] using s.property⟩,Subtype.ext i.property⟩
      left_inv := fun _=>rfl
      right_inv := fun _=>rfl }
    exact (ha s.val).equiv e

end PlanarHom.Structures
