import PlanarHom.OccurrenceKasteleynDartWords
import PlanarHom.OccurrenceMatchingPorts

/-! NEW endpoint-word distinctness from literal occurrence matching membership. -/
noncomputable section
open Classical
namespace PlanarHom.MultiGraph
open Kasteleyn
variable {V E : Type*} [LinearOrder V] {G : MultiGraph V E} {M : Finset E}

theorem mem_dartWord_iff (ds : List (Dart E)) (v : V) :
    v∈G.dartWord ds ↔ ∃a∈ds,v=(G.dartPair a).1 ∨ v=(G.dartPair a).2 := by
  simp only [dartWord,pairWord,List.flatMap_map,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false]

theorem endpointCount_pos_of_dart_endpoint (a : Dart E) (v : V)
    (hv : v=(G.dartPair a).1 ∨ v=(G.dartPair a).2) : 0<G.endpointCount a.1 v := by
  rw [DirectedSimpleCycle.endpointCount_dart]
  rcases hv with hv | hv <;> simp [←hv]

theorem dartWord_nodup_of_matching (hM : G.PerfectMatching M) (ds : List (Dart E))
    (hn : (ds.map Prod.fst).Nodup) (hmem : ∀a∈ds,a.1∈M) : (G.dartWord ds).Nodup := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
      have hd:=List.nodup_cons.mp hn
      have hdm:=hmem d (List.mem_cons_self ..)
      have htmem:∀a∈ds,a.1∈M:=fun a ha=>hmem a (List.mem_cons_of_mem _ ha)
      have hnot (v : V) (hv : v=(G.dartPair d).1 ∨ v=(G.dartPair d).2) : v∉G.dartWord ds := by
        intro hm
        obtain ⟨a,ha,hv'⟩:=(mem_dartWord_iff ds v).mp hm
        have he:=hM.eq_of_endpointCount_pos G hdm (htmem a ha)
          (endpointCount_pos_of_dart_endpoint d v hv) (endpointCount_pos_of_dart_endpoint a v hv')
        exact hd.1 (List.mem_map.mpr ⟨a,ha,he.symm⟩)
      have hne:(G.dartPair d).1≠(G.dartPair d).2:=by
        have hl:=hM.no_loop G M d.1 hdm
        cases hb:d.2
        · simpa [dartPair,hb] using hl.symm
        · simpa [dartPair,hb] using hl
      rw [dartWord_cons]
      apply List.nodup_cons.mpr
      refine ⟨?_,List.nodup_cons.mpr ⟨hnot _ (Or.inr rfl),ih hd.2 htmem⟩⟩
      intro hh
      rcases List.mem_cons.mp hh with hh | hh
      · exact hne hh
      · exact hnot _ (Or.inl rfl) hh

end PlanarHom.MultiGraph
