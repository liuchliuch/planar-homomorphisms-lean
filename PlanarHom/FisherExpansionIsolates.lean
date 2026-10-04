import PlanarHom.FisherExpansionConnected

/-! NEW explicit six-dart face calculation for zero-degree source vertices.
The four non-fixed darts form one real cycle and each loop contributes its
separate fixed face. No virtual face enters the output table. -/
noncomputable section
open Classical
namespace PlanarHom.Fisher
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable (o : G.IncidenceOrdering) (hzero : ∀v,o.degree v=0)

 include hzero in
 theorem no_edge_of_degrees_zero (e : E) : False := by
  let q := o.darts.symm (e,false)
  have h := q.2.isLt
  have hz := hzero q.1
  omega

 include hzero in
 theorem only_path_of_degree_zero (v : V) (k : Fin (o.degree v+1)) : k=0 := by
  apply Fin.ext
  change k.val=0
  have h := k.isLt
  have hz := hzero v
  omega

 def expansionZeroLabel : Dart (ExpansionEdge o)→V×Fin 3
  | (.inl e,_) => False.elim (no_edge_of_degrees_zero o hzero e)
  | (.inr ⟨v,.inl _⟩,_) => (v,2)
  | (.inr ⟨v,.inr _⟩,true) => (v,2)
  | (.inr ⟨v,.inr false⟩,false) => (v,0)
  | (.inr ⟨v,.inr true⟩,false) => (v,1)

 def expansionZeroLift (q : V×Fin 3) : Dart (ExpansionEdge o) :=
  if q.2=0 then expansionLoopDart o q.1 false false
  else if q.2=1 then expansionLoopDart o q.1 true false else expansionPathDart o q.1 0 true

 include hzero in
 theorem expansion_zero_path_forward (v : V) :
    (expansionRows o).facePerm (expansionPathDart o v 0 true)=expansionLoopDart o v true true := by
  have h := expansion_face_path_last o v
  rw [only_path_of_degree_zero o hzero v (Fin.last (o.degree v))] at h
  exact h

 include hzero in
 theorem expansion_zero_backward_reaches (v : V) :
    (expansionRows o).facePerm.SameCycle (expansionPathDart o v 0 false) (expansionPathDart o v 0 true) := by
  have h₁ := expansion_face_step o (expansionPathDart o v 0 false)
  rw [expansion_face_path_zero] at h₁
  have h₂ := expansion_face_step o (expansionLoopDart o v false true)
  rw [expansion_face_loop_zero] at h₂
  exact h₁.trans h₂

 theorem expansion_zero_label_step (d : Dart (ExpansionEdge o)) :
    expansionZeroLabel o hzero ((expansionRows o).facePerm d)=expansionZeroLabel o hzero d := by
  rcases d with ⟨e,b⟩
  cases e with
  | inl e => exact False.elim (no_edge_of_degrees_zero o hzero e)
  | inr e =>
      rcases e with ⟨v,k|side⟩
      · have hk := only_path_of_degree_zero o hzero v k
        subst k
        cases b
        · rw [show (Sum.inr ⟨v,Sum.inl 0⟩,false)=expansionPathDart o v 0 false from rfl,expansion_face_path_zero]
          rfl
        · rw [show (Sum.inr ⟨v,Sum.inl 0⟩,true)=expansionPathDart o v 0 true from rfl,expansion_zero_path_forward o hzero]
          rfl
      · cases b
        · change expansionZeroLabel o hzero ((expansionRows o).facePerm (expansionLoopDart o v side false))=_
          rw [expansion_face_loop_false]
          rfl
        · cases side
          · rw [show (Sum.inr ⟨v,Sum.inr false⟩,true)=expansionLoopDart o v false true from rfl,expansion_face_loop_zero]
            rfl
          · rw [show (Sum.inr ⟨v,Sum.inr true⟩,true)=expansionLoopDart o v true true from rfl,expansion_face_loop_last]
            rfl

 theorem expansion_zero_reaches (d : Dart (ExpansionEdge o)) :
    (expansionRows o).facePerm.SameCycle d (expansionZeroLift o (expansionZeroLabel o hzero d)) := by
  rcases d with ⟨e,b⟩
  cases e with
  | inl e => exact False.elim (no_edge_of_degrees_zero o hzero e)
  | inr e =>
      rcases e with ⟨v,k|side⟩
      · have hk := only_path_of_degree_zero o hzero v k
        subst k
        cases b
        · exact expansion_zero_backward_reaches o hzero v
        · exact .rfl
      · cases b
        · cases side <;> exact .rfl
        · cases side
          · have h := expansion_face_step o (expansionLoopDart o v false true)
            rw [expansion_face_loop_zero] at h
            exact h
          · have h := expansion_face_step o (expansionLoopDart o v true true)
            rw [expansion_face_loop_last,only_path_of_degree_zero o hzero v (Fin.last (o.degree v))] at h
            exact h.trans (expansion_zero_backward_reaches o hzero v)

 theorem expansion_zero_sameCycle_iff (a b : Dart (ExpansionEdge o)) :
    (expansionRows o).facePerm.SameCycle a b ↔ expansionZeroLabel o hzero a=expansionZeroLabel o hzero b := by
  constructor
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    have hi : ∀n,expansionZeroLabel o hzero ((expansionRows o).facePerm^[n] a)=expansionZeroLabel o hzero a := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ_apply',expansion_zero_label_step,ih]
    simpa only [Equiv.Perm.iterate_eq_pow,hn] using (hi n).symm
  · intro h
    have ha := expansion_zero_reaches o hzero a
    have hb := expansion_zero_reaches o hzero b
    rw [h] at ha
    exact ha.trans hb.symm

 theorem expansion_zero_label_surjective : Function.Surjective (expansionZeroLabel o hzero) := by
  intro q
  refine ⟨expansionZeroLift o q,?_⟩
  rcases q with ⟨v,i⟩
  fin_cases i <;> rfl

 include hzero in
 theorem expansion_zero_face_count : count (expansionRows o).facePerm=3*Fintype.card V := by
  rw [count_eq_card_of_label _ (expansionZeroLabel o hzero) (expansion_zero_label_surjective o hzero)
    (expansion_zero_sameCycle_iff o hzero)]
  simp [Fintype.card_prod,Nat.mul_comm]

 include hzero in
 theorem expansion_euler_isolated (hV : Fintype.card V=1) :
    Fintype.card (ExpansionVertex o)+count (expansionRows o).facePerm=Fintype.card (ExpansionEdge o)+2 := by
  letI : IsEmpty E := ⟨no_edge_of_degrees_zero o hzero⟩
  rw [expansion_vertexCount,expansion_edgeCount,expansion_zero_face_count o hzero,Fintype.card_of_isEmpty,hV] <;> norm_num

end PlanarHom.Fisher
