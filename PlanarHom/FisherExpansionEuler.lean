import PlanarHom.FisherExpansionFacePaths

/-! NEW exact Euler transfer for every nonisolated source component. Added
path darts are genuine old-face markers; precisely the two fixed loop sides
per original vertex are new faces. -/
noncomputable section
open Classical
namespace PlanarHom.Fisher
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable (o : G.IncidenceOrdering) (hpos : ∀v,0<o.degree v)

 def expansionFaceProjection : Dart (ExpansionEdge o)→Dart E⊕(V×Bool)
  | (.inl e,b) => .inl (e,b)
  | (.inr ⟨v,.inl k⟩,true) => .inl (originalPortDart o v (expansionPathTarget o hpos v k))
  | (.inr ⟨v,.inl _⟩,false) => .inl (originalPortDart o v (firstPort o hpos v))
  | (.inr ⟨v,.inr b⟩,true) => .inl (originalPortDart o v (firstPort o hpos v))
  | (.inr ⟨v,.inr b⟩,false) => .inr (v,b)

 def expansionFaceLift : Dart E⊕(V×Bool)→Dart (ExpansionEdge o) :=
  Sum.elim (expansionExternalDart o) (fun q=>expansionLoopDart o q.1 q.2 false)

 def expansionFaceLabel (a : Dart (ExpansionEdge o)) : CycleClass o.rotationRows.facePerm⊕(V×Bool) :=
  Sum.map (classOf o.rotationRows.facePerm) id (expansionFaceProjection o hpos a)

 theorem expansion_projection_lift (a : Dart E⊕(V×Bool)) :
    expansionFaceProjection o hpos (expansionFaceLift o a)=a := by
  cases a with
  | inl a => rfl
  | inr a => rfl

 theorem expansion_projection_reaches (a : Dart (ExpansionEdge o)) :
    (expansionRows o).facePerm.SameCycle a (expansionFaceLift o (expansionFaceProjection o hpos a)) := by
  rcases a with ⟨e,b⟩
  cases e with
  | inl e => exact .rfl
  | inr e =>
      rcases e with ⟨v,k|side⟩
      · cases b
        · exact expansion_path_backward_reaches o hpos v k
        · exact expansion_path_forward_reaches o hpos v k
      · cases b
        · exact .rfl
        · exact expansion_loop_reaches o hpos v side

 theorem expansion_label_external_step (a : Dart E) :
    expansionFaceLabel o hpos ((expansionRows o).facePerm (expansionExternalDart o a))=
      expansionFaceLabel o hpos (expansionExternalDart o a) := by
  obtain ⟨⟨v,i⟩,rfl⟩ := o.darts.surjective a
  have hf : (expansionRows o).facePerm (expansionExternalDart o (o.darts ⟨v,i⟩))=
      expansionPathDart o v i.succ true := by
    rw [expansionExternalDart_endpoint,expansion_face_port]
  rw [hf]
  change Sum.inl (classOf o.rotationRows.facePerm (originalPortDart o v (expansionPathTarget o hpos v i.succ)))=
    Sum.inl (classOf o.rotationRows.facePerm (o.darts ⟨v,i⟩))
  rw [expansionPathTarget_succ,←original_face_endpoint]
  apply congrArg Sum.inl
  exact Quotient.sound Equiv.Perm.SameCycle.rfl.apply_left

 theorem expansion_label_step (a : Dart (ExpansionEdge o)) :
    expansionFaceLabel o hpos ((expansionRows o).facePerm a)=expansionFaceLabel o hpos a := by
  rcases a with ⟨e,b⟩
  cases e with
  | inl e => exact expansion_label_external_step o hpos (e,b)
  | inr e =>
      rcases e with ⟨v,k|side⟩
      · cases b
        · change expansionFaceLabel o hpos ((expansionRows o).facePerm (expansionPathDart o v k false))=_
          induction k using Fin.cases with
          | zero => rw [expansion_face_path_zero]; rfl
          | succ i => rw [expansion_face_path_backward]; rfl
        · change expansionFaceLabel o hpos ((expansionRows o).facePerm (expansionPathDart o v k true))=_
          by_cases hk : k.val<o.degree v
          · let i : Fin (o.degree v) := ⟨k.val,hk⟩
            have hi : i.castSucc=k := Fin.ext rfl
            rw [←hi,expansion_face_path_forward]
            simp [expansionFaceLabel,expansionFaceProjection,expansionPathDart,expansionPortDart,
              originalPortDart,expansionPathTarget,i.isLt,reversePerm]
          · have he : k=Fin.last (o.degree v) := Fin.ext (by change k.val=o.degree v; have := k.isLt; omega)
            rw [he,expansion_face_path_last]
            simp [expansionFaceLabel,expansionFaceProjection,expansionPathDart,expansionLoopDart,expansionPathTarget]
      · cases b
        · change expansionFaceLabel o hpos ((expansionRows o).facePerm (expansionLoopDart o v side false))=_
          rw [expansion_face_loop_false]
          rfl
        · cases side
          · change expansionFaceLabel o hpos ((expansionRows o).facePerm (expansionLoopDart o v false true))=_
            rw [expansion_face_loop_zero]
            simp [expansionFaceLabel,expansionFaceProjection,expansionPathDart,expansionLoopDart,expansionPathTarget,firstPort,hpos v]
          · change expansionFaceLabel o hpos ((expansionRows o).facePerm (expansionLoopDart o v true true))=_
            rw [expansion_face_loop_last]
            rfl

 theorem expansion_sameCycle_label (a b : Dart (ExpansionEdge o))
    (h : (expansionRows o).facePerm.SameCycle a b) : expansionFaceLabel o hpos a=expansionFaceLabel o hpos b := by
  obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
  have hi : ∀n,expansionFaceLabel o hpos ((expansionRows o).facePerm^[n] a)=expansionFaceLabel o hpos a := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply',expansion_label_step,ih]
  simpa only [Equiv.Perm.iterate_eq_pow,hn] using (hi n).symm

 include hpos in
 theorem expansion_lift_sameCycle (a b : Dart E⊕(V×Bool))
    (h : Sum.map (classOf o.rotationRows.facePerm) id a=Sum.map (classOf o.rotationRows.facePerm) id b) :
    (expansionRows o).facePerm.SameCycle (expansionFaceLift o a) (expansionFaceLift o b) := by
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          have hh : o.rotationRows.facePerm.SameCycle a b := Quotient.exact (Sum.inl.inj h)
          exact sameCycle_map_of_step o.rotationRows.facePerm (expansionRows o).facePerm
            (expansionExternalDart o) (expansion_old_step_lifts o hpos) hh
      | inr b => contradiction
  | inr a =>
      cases b with
      | inl b => contradiction
      | inr b => have he : a=b := Sum.inr.inj h; rw [he]

 theorem expansion_sameCycle_iff_label (a b : Dart (ExpansionEdge o)) :
    (expansionRows o).facePerm.SameCycle a b ↔ expansionFaceLabel o hpos a=expansionFaceLabel o hpos b := by
  constructor
  · exact expansion_sameCycle_label o hpos a b
  · intro h
    exact (expansion_projection_reaches o hpos a).trans
      ((expansion_lift_sameCycle o hpos _ _ h).trans (expansion_projection_reaches o hpos b).symm)

 theorem expansion_label_surjective : Function.Surjective (expansionFaceLabel o hpos) := by
  intro q
  cases q with
  | inl q =>
      induction q using Quotient.inductionOn with | h a => exact ⟨expansionExternalDart o a,rfl⟩
  | inr q => exact ⟨expansionLoopDart o q.1 q.2 false,rfl⟩

 include hpos in
 theorem expansion_face_count : count (expansionRows o).facePerm=count o.rotationRows.facePerm+2*Fintype.card V := by
  rw [count_eq_card_of_label _ (expansionFaceLabel o hpos) (expansion_label_surjective o hpos)
    (expansion_sameCycle_iff_label o hpos),Fintype.card_sum]
  simp [count,Nat.card_eq_fintype_card,CycleClass,Fintype.card_prod,Nat.mul_comm]

 include hpos in
 theorem expansion_euler
    (heuler : Fintype.card V+count o.rotationRows.facePerm=Fintype.card E+2) :
    Fintype.card (ExpansionVertex o)+count (expansionRows o).facePerm=Fintype.card (ExpansionEdge o)+2 := by
  rw [expansion_vertexCount,expansion_edgeCount,expansion_face_count o hpos]
  omega

end PlanarHom.Fisher
