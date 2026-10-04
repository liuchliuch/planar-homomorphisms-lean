import PlanarHom.RadialPottsRedOnionComponents
import PlanarHom.RadialPottsOnionBoundaryRotation

/-! NEW reconstruction: endpoint switching along the already-present long
matching preserves actual connectivity. Thus the red/blue truth table has no
unproved internal-component or boundary-connectivity premise. -/
noncomputable section
open Classical
namespace PlanarHom.RadialPottsTile.OnionBoundary
open MultiGraph

private theorem any_long_reach {k : ℕ} (a b : HalfShort k → White k) (e : Long k) :
    (withShort a b).componentSetoid Finset.univ (.inl (longLeft e)) (longRight e) :=
  Relation.EqvGen.rel _ _ ⟨.inl e,Finset.mem_univ _,rfl,rfl⟩

/-- Every moved white vertex is joined to its switched image by its literal
long occurrence. This works with any choice of short endpoints. -/
theorem switch_long_reach {k : ℕ} (a b : HalfShort k → White k) (w : White k) :
    (withShort a b).componentSetoid Finset.univ (.inl w) (.inl (switch w)) := by
  rcases w with ⟨r,i⟩
  by_cases h0 : i.val=0 ∧ r.val+1<k
  · let e : Long k := ⟨r,(0,⟨0,by omega⟩)⟩
    have hs : longLeft e=⟨r,i⟩ := by
      apply white_ext
      · rfl
      · dsimp [longLeft,e]
        omega
    have ht : longRight e=.inl (switch (⟨r,i⟩ : White k)) := by
      rw [longRight,dif_pos h0.2,switch,dif_pos h0]
      apply congrArg Sum.inl
      apply white_ext <;> simp [e]
    have hh := any_long_reach a b e
    rw [hs,ht] at hh
    exact hh
  · by_cases h1 : i.val=1 ∧ 0<r.val
    · let r' : Fin k := ⟨r.val-1,by have := r.isLt; omega⟩
      let e : Long k := ⟨r',(0,⟨0,by omega⟩)⟩
      have hr : r'.val+1=r.val := by dsimp [r']; omega
      have hs : longLeft e=switch (⟨r,i⟩ : White k) := by
        rw [switch,dif_neg h0,dif_pos h1]
        apply white_ext <;> simp [longLeft,e,r']
      have ht : longRight e=.inl (⟨r,i⟩ : White k) := by
        rw [longRight,dif_pos (show e.1.val+1<k by change r'.val+1<k; rw [hr]; exact r.isLt)]
        apply congrArg Sum.inl
        apply white_ext
        · exact hr
        · dsimp [e]
          omega
      have hh := any_long_reach a b e
      rw [hs,ht] at hh
      exact Relation.EqvGen.symm _ _ hh
    · have hh : switch (⟨r,i⟩ : White k)=⟨r,i⟩ := by rw [switch,dif_neg h0,dif_neg h1]
      rw [hh]

private theorem switched_short_reach {k : ℕ} (e : HalfShort k) :
    (switchedRedGraph k).componentSetoid Finset.univ
      (.inl (switch (evenWhite e))) (.inl (switch (oddWhite e))) :=
  Relation.EqvGen.rel _ _ ⟨.inr e,Finset.mem_univ _,rfl,rfl⟩

private theorem red_short_reach {k : ℕ} (e : HalfShort k) :
    RedReach (.inl (evenWhite e)) (.inl (oddWhite e)) :=
  Relation.EqvGen.rel _ _ ⟨.inr e,Finset.mem_univ _,rfl,rfl⟩

/-- Both directions are witnessed by finite paths in the actual graphs. -/
theorem switched_red_reach_iff {k : ℕ} (u v : Vertex k) :
    (switchedRedGraph k).componentSetoid Finset.univ u v ↔ RedReach u v := by
  constructor
  · intro h
    induction h with
    | rel u v h =>
      obtain ⟨e,_,rfl,rfl⟩ := h
      cases e with
      | inl e => exact any_long_reach _ _ e
      | inr e =>
        exact Relation.EqvGen.trans _ _ _
          (Relation.EqvGen.symm _ _ (switch_long_reach evenWhite oddWhite (evenWhite e)))
          (Relation.EqvGen.trans _ _ _ (red_short_reach e)
            (switch_long_reach evenWhite oddWhite (oddWhite e)))
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih ij => exact Relation.EqvGen.trans _ _ _ ih ij
  · intro h
    induction h with
    | rel u v h =>
      obtain ⟨e,_,rfl,rfl⟩ := h
      cases e with
      | inl e => exact any_long_reach _ _ e
      | inr e =>
        exact Relation.EqvGen.trans _ _ _
          (switch_long_reach (switch ∘ evenWhite) (switch ∘ oddWhite) (evenWhite e))
          (Relation.EqvGen.trans _ _ _ (switched_short_reach e)
            (Relation.EqvGen.symm _ _
              (switch_long_reach (switch ∘ evenWhite) (switch ∘ oddWhite) (oddWhite e))))
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih ij => exact Relation.EqvGen.trans _ _ _ ih ij

theorem switched_red_connected_iff {k : ℕ} (u v : Vertex k) :
    (switchedRedGraph k).componentSetoid Finset.univ u v ↔ component u=component v := by
  rw [switched_red_reach_iff,red_connected_iff]

theorem blue_connected_iff {k : ℕ} (u v : Vertex k) :
    (blueGraph k).componentSetoid Finset.univ u v ↔
      component ((rotateVertex k).symm u)=component ((rotateVertex k).symm v) := by
  rw [inverse_rotation_connected_iff]
  exact red_connected_iff _ _
end PlanarHom.RadialPottsTile.OnionBoundary
