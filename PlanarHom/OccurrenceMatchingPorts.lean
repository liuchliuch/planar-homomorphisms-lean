import PlanarHom.OccurrenceMatchingCycleIncidence

/-! NEW unique occurrence-labelled matching ports and their exact mate involutions. -/
noncomputable section
open Classical
namespace PlanarHom.MultiGraph
open Kasteleyn
variable {V E : Type*} {G : MultiGraph V E} {M N : Finset E}

theorem dart_host_unique_of_nonloop (a b : Dart E) (he : a.1=b.1)
    (hh : (G.dartPair a).1=(G.dartPair b).1) (hn : G.src a.1≠G.dst a.1) : a=b := by
  rcases a with ⟨e,x⟩
  rcases b with ⟨f,y⟩
  dsimp at he
  subst f
  cases x <;> cases y <;> simp_all [dartPair]

theorem dartPair_reverse_snd (a : Dart E) : (G.dartPair (a.1,!a.2)).2=(G.dartPair a).1 := by
  rcases a with ⟨e,b⟩
  cases b <;> rfl

namespace PerfectMatching

theorem exists_port (hM : G.PerfectMatching M) (v : V) : ∃a:Dart E,a.1∈M ∧ (G.dartPair a).1=v := by
  have hex : ∃e∈M,G.src e=v ∨ G.dst e=v := by
    by_contra h
    push_neg at h
    have hd:=hM v
    have hz : G.selectedDegree M v=0 := by
      apply Finset.sum_eq_zero
      intro e he
      simp only [if_neg (h e he).1,if_neg (h e he).2,zero_add]
    omega
  obtain ⟨e,he,hs | ht⟩:=hex
  · exact ⟨(e,true),he,hs⟩
  · exact ⟨(e,false),he,ht⟩

def port (hM : G.PerfectMatching M) (v : V) : Dart E := (hM.exists_port v).choose

theorem port_mem (hM : G.PerfectMatching M) (v : V) : (hM.port v).1∈M := (hM.exists_port v).choose_spec.1

theorem port_host (hM : G.PerfectMatching M) (v : V) : (G.dartPair (hM.port v)).1=v := (hM.exists_port v).choose_spec.2

theorem port_unique (hM : G.PerfectMatching M) (v : V) (a : Dart E)
    (ha : a.1∈M) (hh : (G.dartPair a).1=v) : a=hM.port v := by
  have hp (b : Dart E) (hb : (G.dartPair b).1=v) : 0<G.endpointCount b.1 v := by
    rw [DirectedSimpleCycle.endpointCount_dart b v,hb]
    simp
  have he:=hM.eq_of_endpointCount_pos G ha (hM.port_mem v) (hp a hh) (hp _ (hM.port_host v))
  exact dart_host_unique_of_nonloop a (hM.port v) he (hh.trans (hM.port_host v).symm) (hM.no_loop G M a.1 ha)

def mate (hM : G.PerfectMatching M) (v : V) : V := (G.dartPair (hM.port v)).2

theorem port_mate (hM : G.PerfectMatching M) (v : V) :
    hM.port (hM.mate v)=((hM.port v).1,!(hM.port v).2) := by
  symm
  apply hM.port_unique (hM.mate v) ((hM.port v).1,!(hM.port v).2) (hM.port_mem v)
  exact dartPair_reverse_fst (hM.port v)

theorem mate_mate (hM : G.PerfectMatching M) (v : V) : hM.mate (hM.mate v)=v := by
  change (G.dartPair (hM.port (hM.mate v))).2=v
  rw [hM.port_mate v,dartPair_reverse_snd,hM.port_host]

theorem mate_ne (hM : G.PerfectMatching M) (v : V) : hM.mate v≠v := by
  intro h
  have hn:=hM.no_loop G M (hM.port v).1 (hM.port_mem v)
  have he : (G.dartPair (hM.port v)).1=(G.dartPair (hM.port v)).2 := (hM.port_host v).trans h.symm
  cases hb:(hM.port v).2 <;> simp only [dartPair,hb,Bool.false_eq_true,if_false,if_true] at he
  · exact hn he.symm
  · exact hn he

def matePerm (hM : G.PerfectMatching M) : Equiv.Perm V where
  toFun := hM.mate
  invFun := hM.mate
  left_inv := hM.mate_mate
  right_inv := hM.mate_mate

def Differ (hM : G.PerfectMatching M) (hN : G.PerfectMatching N) (v : V) : Prop :=
  (hM.port v).1≠(hN.port v).1

theorem differing_port_not_mem (hM : G.PerfectMatching M) (hN : G.PerfectMatching N) (v : V)
    (hd : hM.Differ hN v) : (hM.port v).1∉N := by
  intro hm
  exact hd (congrArg Prod.fst (hN.port_unique v (hM.port v) hm (hM.port_host v)))

theorem differ_mate_left (hM : G.PerfectMatching M) (hN : G.PerfectMatching N) (v : V)
    (hd : hM.Differ hN v) : hM.Differ hN (hM.mate v) := by
  intro he
  have hm:=hN.port_mem (hM.mate v)
  rw [←he,hM.port_mate] at hm
  exact hM.differing_port_not_mem hN v hd hm

theorem differ_mate_right (hM : G.PerfectMatching M) (hN : G.PerfectMatching N) (v : V)
    (hd : hM.Differ hN v) : hM.Differ hN (hN.mate v) := by
  exact Ne.symm (hN.differ_mate_left hM v (Ne.symm hd))

theorem exists_differ (hM : G.PerfectMatching M) (hN : G.PerfectMatching N) (hne : M≠N) :
    ∃v,hM.Differ hN v := by
  by_contra hn
  have heq : ∀v,(hM.port v).1=(hN.port v).1 := by
    intro v
    by_contra h
    exact hn ⟨v,h⟩
  apply hne
  ext e
  constructor
  · intro he
    have hp: (e,true)=hM.port (G.src e) := hM.port_unique _ _ he rfl
    have hm:=hN.port_mem (G.src e)
    rw [←heq,←hp] at hm
    exact hm
  · intro he
    have hp: (e,true)=hN.port (G.src e) := hN.port_unique _ _ he rfl
    have hm:=hM.port_mem (G.src e)
    rw [heq,←hp] at hm
    exact hm

end PerfectMatching
end PlanarHom.MultiGraph
