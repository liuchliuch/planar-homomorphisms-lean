import PlanarHom.OccurrenceDegreeRows
import PlanarHom.FisherExpansionGraph

/-! NEW literal path-and-two-loops rotation for Fisher degree reduction.
The formulas include zero-degree vertices and retain every endpoint occurrence. -/
noncomputable section
open Classical
namespace PlanarHom.Fisher
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization
variable {V E : Type*} {G : MultiGraph V E} (o : G.IncidenceOrdering)

 def expansionPathDart (v : V) (j : Fin (o.degree v+1)) (b : Bool) : Dart (ExpansionEdge o) :=
  (.inr ⟨v,.inl j⟩,b)

 def expansionLoopDart (v : V) (side b : Bool) : Dart (ExpansionEdge o) :=
  (.inr ⟨v,.inr side⟩,b)

 def expansionPortDart (v : V) (i : Fin (o.degree v)) : Dart (ExpansionEdge o) :=
  (.inl (o.darts ⟨v,i⟩).1,!(o.darts ⟨v,i⟩).2)

 def expansionRow (q : ExpansionVertex o) : List (Dart (ExpansionEdge o)) :=
  if h0 : q.2=0 then
    [expansionPathDart o q.1 0 true,expansionLoopDart o q.1 false true,expansionLoopDart o q.1 false false]
  else if hl : q.2=Fin.last (o.degree q.1+1) then
    [expansionPathDart o q.1 (Fin.last (o.degree q.1)) false,
     expansionLoopDart o q.1 true true,expansionLoopDart o q.1 true false]
  else
    let i : Fin (o.degree q.1) := ⟨q.2.val-1,by
      have hj:=q.2.isLt
      have hz : q.2.val≠0 := fun h=>h0 (Fin.ext h)
      have hlast : q.2.val≠o.degree q.1+1 := fun h=>hl (Fin.ext h)
      omega⟩
    [expansionPathDart o q.1 i.castSucc false,expansionPortDart o q.1 i,expansionPathDart o q.1 i.succ true]

@[simp] theorem expansionRow_zero (v : V) : expansionRow o ⟨v,0⟩=
    [expansionPathDart o v 0 true,expansionLoopDart o v false true,expansionLoopDart o v false false] := by
  simp [expansionRow]

@[simp] theorem expansionRow_last (v : V) : expansionRow o ⟨v,Fin.last (o.degree v+1)⟩=
    [expansionPathDart o v (Fin.last (o.degree v)) false,
     expansionLoopDart o v true true,expansionLoopDart o v true false] := by
  have hn : (Fin.last (o.degree v+1) : Fin (o.degree v+2))≠0 := by simp [Fin.ext_iff]
  simp [expansionRow,hn]

@[simp] theorem expansionRow_port (v : V) (i : Fin (o.degree v)) :
    expansionRow o ⟨v,i.succ.castSucc⟩=
      [expansionPathDart o v i.castSucc false,expansionPortDart o v i,expansionPathDart o v i.succ true] := by
  have hz : (i.succ.castSucc : Fin (o.degree v+2))≠0 := by simp [Fin.ext_iff]
  have hl : (i.succ.castSucc : Fin (o.degree v+2))≠Fin.last (o.degree v+1) := by
    intro h
    have hh := congrArg Fin.val h
    change i.val+1=o.degree v+1 at hh
    omega
  simp [expansionRow,hz,hl]

 theorem expansionPortDart_host (v : V) (i : Fin (o.degree v)) :
    ((expansionGraph o).dartPair (expansionPortDart o v i)).1=⟨v,i.succ.castSucc⟩ := by
  obtain ⟨e,b,h⟩ : ∃e b,o.darts ⟨v,i⟩=(e,b) := ⟨_,_,rfl⟩
  have hi : o.darts.symm (e,b)=⟨v,i⟩ := by rw [←h,o.darts.symm_apply_apply]
  cases b <;> simp only [expansionPortDart,h,Bool.not_false,Bool.not_true,expansionGraph,dartPair,
    Bool.false_eq_true,if_true,if_false,Sum.elim_inl] <;> rw [hi] <;> rfl

 theorem expansionRow_nodup (q : ExpansionVertex o) : (expansionRow o q).Nodup := by
  rcases q with ⟨v,j⟩
  apply (forall_fin_endpoints (d:=o.degree v) (fun j=>(expansionRow o ⟨v,j⟩).Nodup)).mpr ?_ j
  constructor
  · simp [expansionRow_zero,expansionPathDart,expansionLoopDart]
  constructor
  · simp [expansionRow_last,expansionPathDart,expansionLoopDart]
  · intro i
    change (expansionRow o ⟨v,i.succ.castSucc⟩).Nodup
    rw [expansionRow_port]
    simp [expansionPathDart,expansionPortDart]

 theorem expansionRow_length (q : ExpansionVertex o) : (expansionRow o q).length=3 := by
  rcases q with ⟨v,j⟩
  apply (forall_fin_endpoints (d:=o.degree v) (fun j=>(expansionRow o ⟨v,j⟩).length=3)).mpr ?_ j
  refine ⟨by simp,by simp,?_⟩
  intro i
  change (expansionRow o ⟨v,i.succ.castSucc⟩).length=3
  rw [expansionRow_port]
  rfl

 theorem expansionRow_hosts (q : ExpansionVertex o) :
    ∀a∈expansionRow o q,((expansionGraph o).dartPair a).1=q := by
  rcases q with ⟨v,j⟩
  apply (forall_fin_endpoints (d:=o.degree v)
    (fun j=>∀a∈expansionRow o ⟨v,j⟩,((expansionGraph o).dartPair a).1=⟨v,j⟩)).mpr ?_ j
  constructor
  · simp [expansionRow_zero,expansionPathDart,expansionLoopDart,expansionGraph,dartPair,localExpansion,pathLoopVertex]
  constructor
  · simp [expansionRow_last,expansionPathDart,expansionLoopDart,expansionGraph,dartPair,localExpansion,pathLoopVertex]
  · intro i a ha
    rw [expansionRow_port] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl
    · rfl
    · exact expansionPortDart_host o v i
    · rfl

 def expansionRows [Fintype V] [Fintype E] : RotationRows (expansionGraph o) where
  row := expansionRow o
  nodup := expansionRow_nodup o
  mem v := (expansionGraph o).row_mem_of_degree v (expansionRow o v) (expansionRow_nodup o v)
    (expansionRow_hosts o v) (by rw [expansionRow_length,expansion_is_cubic])

end PlanarHom.Fisher
