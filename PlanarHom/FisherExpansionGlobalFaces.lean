import PlanarHom.FisherExpansionLocalFaces

/-! NEW literal face count of Fisher expansion with arbitrary mixtures of
isolated and nonisolated source vertices. Each isolate contributes its actual
four-dart face in addition to the two fixed loop faces. -/
noncomputable section
open Classical
namespace PlanarHom.Fisher
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable (o : G.IncidenceOrdering)

abbrev IsolatedVertex := {v : V // o.degree v=0}
abbrev GlobalFaceIndex := (Dart E ⊕ (V×Bool)) ⊕ IsolatedVertex o
abbrev GlobalFaceLabel := (CycleClass o.rotationRows.facePerm ⊕ (V×Bool)) ⊕ IsolatedVertex o

 def globalFaceProjection : Dart (ExpansionEdge o)→GlobalFaceIndex o
  | (.inl e,b) => .inl (.inl (e,b))
  | (.inr ⟨v,.inl k⟩,true) => if hv : 0<o.degree v then
      .inl (.inl (originalPortDart o v (localPathTarget o v hv k)))
      else .inr ⟨v,Nat.eq_zero_of_not_pos hv⟩
  | (.inr ⟨v,.inl _⟩,false) => if hv : 0<o.degree v then
      .inl (.inl (originalPortDart o v (localFirstPort o v hv)))
      else .inr ⟨v,Nat.eq_zero_of_not_pos hv⟩
  | (.inr ⟨v,.inr b⟩,true) => if hv : 0<o.degree v then
      .inl (.inl (originalPortDart o v (localFirstPort o v hv)))
      else .inr ⟨v,Nat.eq_zero_of_not_pos hv⟩
  | (.inr ⟨v,.inr b⟩,false) => .inl (.inr (v,b))

 def globalFaceLift : GlobalFaceIndex o→Dart (ExpansionEdge o)
  | .inl (.inl a) => expansionExternalDart o a
  | .inl (.inr q) => expansionLoopDart o q.1 q.2 false
  | .inr v => expansionPathDart o v.val 0 true

 def globalIndexLabel : GlobalFaceIndex o→GlobalFaceLabel o :=
  Sum.map (Sum.map (classOf o.rotationRows.facePerm) id) id
 def globalFaceLabel (a : Dart (ExpansionEdge o)) : GlobalFaceLabel o :=
  globalIndexLabel o (globalFaceProjection o a)

 theorem local_zero_path (v : V) (hv : o.degree v=0) (k : Fin (o.degree v+1)) : k=0 := by
  apply Fin.ext
  have := k.isLt
  change k.val=0
  omega

 theorem local_zero_backward_reaches (v : V) :
    (expansionRows o).facePerm.SameCycle (expansionPathDart o v 0 false) (expansionPathDart o v 0 true) := by
  have h₁ := expansion_face_step o (expansionPathDart o v 0 false)
  rw [expansion_face_path_zero] at h₁
  have h₂ := expansion_face_step o (expansionLoopDart o v false true)
  rw [expansion_face_loop_zero] at h₂
  exact h₁.trans h₂

 theorem global_projection_reaches (a : Dart (ExpansionEdge o)) :
    (expansionRows o).facePerm.SameCycle a (globalFaceLift o (globalFaceProjection o a)) := by
  rcases a with ⟨e,b⟩
  cases e with
  | inl e => exact .rfl
  | inr e =>
      rcases e with ⟨v,k|side⟩
      · by_cases hv : 0<o.degree v
        · cases b
          · simpa [globalFaceProjection,globalFaceLift,expansionPathDart,hv] using local_path_backward_reaches o v hv k
          · simpa [globalFaceProjection,globalFaceLift,expansionPathDart,hv] using local_path_forward_reaches o v hv k
        · have hz := Nat.eq_zero_of_not_pos hv
          have hk := local_zero_path o v hz k
          subst k
          cases b
          · simpa [globalFaceProjection,globalFaceLift,expansionPathDart,hv] using local_zero_backward_reaches o v
          · simp only [globalFaceProjection,dif_neg hv,globalFaceLift]
            exact .rfl
      · cases b
        · exact .rfl
        · by_cases hv : 0<o.degree v
          · simpa [globalFaceProjection,globalFaceLift,expansionLoopDart,hv] using local_loop_reaches o v hv side
          · have hz := Nat.eq_zero_of_not_pos hv
            simp only [globalFaceProjection,dif_neg hv,globalFaceLift]
            cases side
            · have h := expansion_face_step o (expansionLoopDart o v false true)
              rw [expansion_face_loop_zero] at h
              exact h
            · have h := expansion_face_step o (expansionLoopDart o v true true)
              rw [expansion_face_loop_last,local_zero_path o v hz (Fin.last (o.degree v))] at h
              exact h.trans (local_zero_backward_reaches o v)

 theorem global_label_external_step (a : Dart E) :
    globalFaceLabel o ((expansionRows o).facePerm (expansionExternalDart o a))=
      globalFaceLabel o (expansionExternalDart o a) := by
  obtain ⟨⟨v,i⟩,rfl⟩ := o.darts.surjective a
  have hv : 0<o.degree v := Nat.zero_lt_of_lt i.isLt
  have hf : (expansionRows o).facePerm (expansionExternalDart o (o.darts ⟨v,i⟩))=
      expansionPathDart o v i.succ true := by
    rw [expansionExternalDart_endpoint,expansion_face_port]
  rw [hf]
  simp only [globalFaceLabel,globalFaceProjection,globalIndexLabel,expansionPathDart,expansionExternalDart,
    dif_pos hv,Sum.map_inl,Sum.map_inr,id_eq]
  rw [localPathTarget_succ,←original_face_endpoint]
  apply congrArg (Sum.inl ∘ Sum.inl)
  exact Quotient.sound Equiv.Perm.SameCycle.rfl.apply_left

 theorem global_label_step (a : Dart (ExpansionEdge o)) :
    globalFaceLabel o ((expansionRows o).facePerm a)=globalFaceLabel o a := by
  rcases a with ⟨e,b⟩
  cases e with
  | inl e => exact global_label_external_step o (e,b)
  | inr e =>
      rcases e with ⟨v,k|side⟩
      · cases b
        · change globalFaceLabel o ((expansionRows o).facePerm (expansionPathDart o v k false))=_
          induction k using Fin.cases with
          | zero => rw [expansion_face_path_zero]; rfl
          | succ i => rw [expansion_face_path_backward]; rfl
        · change globalFaceLabel o ((expansionRows o).facePerm (expansionPathDart o v k true))=_
          by_cases hk : k.val<o.degree v
          · let i : Fin (o.degree v) := ⟨k.val,hk⟩
            have hv : 0<o.degree v := Nat.zero_lt_of_lt hk
            have hi : i.castSucc=k := Fin.ext rfl
            rw [←hi,expansion_face_path_forward]
            simp [globalFaceLabel,globalFaceProjection,globalIndexLabel,expansionPathDart,expansionPortDart,
              originalPortDart,localPathTarget,i.isLt,reversePerm,hv]
          · have he : k=Fin.last (o.degree v) := Fin.ext (by change k.val=o.degree v; have := k.isLt; omega)
            rw [he,expansion_face_path_last]
            simp [globalFaceLabel,globalFaceProjection,globalIndexLabel,expansionPathDart,expansionLoopDart,localPathTarget]
      · cases b
        · change globalFaceLabel o ((expansionRows o).facePerm (expansionLoopDart o v side false))=_
          rw [expansion_face_loop_false]
          rfl
        · cases side
          · change globalFaceLabel o ((expansionRows o).facePerm (expansionLoopDart o v false true))=_
            rw [expansion_face_loop_zero]
            by_cases hv : 0<o.degree v
            · simp [globalFaceLabel,globalFaceProjection,globalIndexLabel,expansionPathDart,expansionLoopDart,localPathTarget,localFirstPort,hv]
            · simp [globalFaceLabel,globalFaceProjection,globalIndexLabel,expansionPathDart,expansionLoopDart,hv]
          · change globalFaceLabel o ((expansionRows o).facePerm (expansionLoopDart o v true true))=_
            rw [expansion_face_loop_last]
            rfl

 theorem global_sameCycle_label (a b : Dart (ExpansionEdge o))
    (h : (expansionRows o).facePerm.SameCycle a b) : globalFaceLabel o a=globalFaceLabel o b := by
  obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
  have hi : ∀n,globalFaceLabel o ((expansionRows o).facePerm^[n] a)=globalFaceLabel o a := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply',global_label_step,ih]
  simpa only [Equiv.Perm.iterate_eq_pow,hn] using (hi n).symm

 theorem global_lift_sameCycle (a b : GlobalFaceIndex o)
    (h : globalIndexLabel o a=globalIndexLabel o b) :
    (expansionRows o).facePerm.SameCycle (globalFaceLift o a) (globalFaceLift o b) := by
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          cases a with
          | inl a =>
              cases b with
              | inl b =>
                  have hh : o.rotationRows.facePerm.SameCycle a b := Quotient.exact (Sum.inl.inj (Sum.inl.inj h))
                  exact sameCycle_map_of_step o.rotationRows.facePerm (expansionRows o).facePerm
                    (expansionExternalDart o) (local_old_step_lifts o) hh
              | inr b => simp [globalIndexLabel] at h
          | inr a =>
              cases b with
              | inl b => simp [globalIndexLabel] at h
              | inr b => have he : a=b := Sum.inr.inj (Sum.inl.inj h); rw [he]
      | inr b => simp [globalIndexLabel] at h
  | inr a =>
      cases b with
      | inl b => simp [globalIndexLabel] at h
      | inr b => have he : a=b := Sum.inr.inj h; rw [he]

 theorem global_sameCycle_iff_label (a b : Dart (ExpansionEdge o)) :
    (expansionRows o).facePerm.SameCycle a b ↔ globalFaceLabel o a=globalFaceLabel o b := by
  constructor
  · exact global_sameCycle_label o a b
  · intro h
    exact (global_projection_reaches o a).trans
      ((global_lift_sameCycle o _ _ h).trans (global_projection_reaches o b).symm)

 theorem global_label_surjective : Function.Surjective (globalFaceLabel o) := by
  intro q
  cases q with
  | inl q =>
      cases q with
      | inl q => induction q using Quotient.inductionOn with | h a => exact ⟨expansionExternalDart o a,rfl⟩
      | inr q => exact ⟨expansionLoopDart o q.1 q.2 false,rfl⟩
  | inr q =>
      refine ⟨expansionPathDart o q.val 0 true,?_⟩
      have hv : ¬0<o.degree q.val := by rw [q.property]; omega
      simp [globalFaceLabel,globalFaceProjection,globalIndexLabel,expansionPathDart,hv]

 theorem expansion_face_count_global : count (expansionRows o).facePerm=
    count o.rotationRows.facePerm+2*Fintype.card V+Fintype.card (IsolatedVertex o) := by
  rw [count_eq_card_of_label _ (globalFaceLabel o) (global_label_surjective o)
    (global_sameCycle_iff_label o)]
  simp [GlobalFaceLabel,count,Nat.card_eq_fintype_card,CycleClass,Fintype.card_prod,Nat.mul_comm]

end PlanarHom.Fisher
