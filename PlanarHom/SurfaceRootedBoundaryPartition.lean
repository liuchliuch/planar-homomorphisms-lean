import PlanarHom.SurfaceComplementGenusBound

/-! NEW finite gluing lemma used by the actual planar compiler. One selected
boundary per ribbon component meets the outer region; every other boundary
bounds its own disk. The partition and incidence claims are proved here. -/
noncomputable section
open Classical
namespace PlanarHom.SurfaceRootedBoundaryPartition
open MultiGraph
variable {B C : Type*} [Fintype B] [Fintype C]

structure Data (component : B→C) where
  root : C→B
  root_component : ∀c,component (root c)=c
  disks : List B
  nodup : disks.Nodup
  mem_disks : ∀b,b∈disks ↔ b≠root (component b)

variable {component : B→C} (D : Data component)

 def partitionEquiv : B≃C⊕{b:B // b∈D.disks} where
  toFun b:=if h:b=D.root (component b) then .inl (component b) else .inr ⟨b,(D.mem_disks b).mpr h⟩
  invFun
    | .inl c=>D.root c
    | .inr b=>b.val
  left_inv b:=by
    by_cases h:b=D.root (component b)
    · simp only [dif_pos h]
      exact h.symm
    · simp only [dif_neg h]
  right_inv b:=by
    cases b with
    | inl c=>simp [D.root_component]
    | inr b=>simp [((D.mem_disks b.val).mp b.property)]

 theorem cardinal : Fintype.card B=Fintype.card C+D.disks.length := by
  rw [Fintype.card_congr (partitionEquiv D),Fintype.card_sum]
  congr 1
  have h:Fintype.card {b:B // b∈D.disks}=D.disks.toFinset.card := by
    rw [Fintype.card_subtype]
    congr 1
    ext b
    simp
  rw [h,List.toFinset_card_of_nodup D.nodup]

 theorem incidence_connected (q : ℕ) (hq:q=D.disks.length+1) (attach:B→Fin q)
    (hr:∀c,(attach (D.root c)).val=0)
    (hd:∀k:Fin D.disks.length,(attach (D.disks.get k)).val=k.val+1) :
    ∀u v,(MultiGraph.mk (fun b=>Sum.inl (component b)) (fun b=>Sum.inr (attach b))).componentSetoid
      Finset.univ u v := by
  let H : MultiGraph (C⊕Fin q) B:=⟨fun b=>.inl (component b),fun b=>.inr (attach b)⟩
  let outer : Fin q:=⟨0,by omega⟩
  have hc (c:C) : H.componentSetoid Finset.univ (.inl c) (.inr outer) := by
    apply Relation.EqvGen.rel
    refine ⟨D.root c,Finset.mem_univ _,?_,?_⟩
    · simp [H,D.root_component]
    · change Sum.inr (attach (D.root c))=Sum.inr outer
      congr 1
      exact Fin.ext (hr c)
  have ho (u:C⊕Fin q) : H.componentSetoid Finset.univ u (.inr outer) := by
    cases u with
    | inl c=>exact hc c
    | inr j=>
      by_cases hj:j.val=0
      · have he:j=outer:=Fin.ext hj
        rw [he]
        try exact Relation.EqvGen.refl _
      · let k:Fin D.disks.length:=⟨j.val-1,by have:=j.isLt; omega⟩
        have hkj:(attach (D.disks.get k))=j := by
          apply Fin.ext
          rw [hd]
          dsimp [k]
          omega
        have he:H.componentSetoid Finset.univ (.inl (component (D.disks.get k))) (.inr j) := by
          apply Relation.EqvGen.rel
          exact ⟨D.disks.get k,Finset.mem_univ _,rfl,by change Sum.inr _=Sum.inr _; rw [hkj]⟩
        exact Relation.EqvGen.trans _ _ _ he.symm (hc _)
  intro u v
  exact Relation.EqvGen.trans _ _ _ (ho u) (ho v).symm

end PlanarHom.SurfaceRootedBoundaryPartition
