import PlanarHom.SurfaceNullCycleSigns

/-! NEW matching confinement and region parity for the whole symmetric
difference, requiring no assumption that its individual cycles are null. -/
noncomputable section
open Classical
namespace PlanarHom.MultiGraph
open Kasteleyn PlanarityLRRealization
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}

theorem edgeIndicator_symmDiff (M N : Finset E) :
    edgeIndicator (symmDiff M N)=edgeIndicator M+edgeIndicator N := by
  funext e
  by_cases hm:e∈M <;> by_cases hn:e∈N <;>
    simp [edgeIndicator,Finset.mem_symmDiff,hm,hn] <;> decide

theorem PerfectMatching.symmDiff_even {M N : Finset E}
    (hM : G.PerfectMatching M) (hN : G.PerfectMatching N) : G.EvenSubgraph (symmDiff M N) := by
  intro v
  apply ZMod.natCast_eq_zero_iff_even.mp
  rw [←G.boundary_edgeIndicator,edgeIndicator_symmDiff,Matrix.mulVec_add,Pi.add_apply,
    G.boundary_edgeIndicator,G.boundary_edgeIndicator,hM v,hN v]
  norm_num
  decide

theorem PerfectMatching.symmDiff_incident_closed {M N : Finset E}
    (hM : G.PerfectMatching M) (hN : G.PerfectMatching N)
    (e : E) (he : e∈M) (a : Dart E) (ha : a.1∈symmDiff M N)
    (hv : (G.dartPair a).1=G.src e ∨ (G.dartPair a).1=G.dst e) : e∈symmDiff M N := by
  have hap : 0<G.endpointCount a.1 (G.dartPair a).1 := by
    rw [DirectedSimpleCycle.endpointCount_dart]
    simp
  have hep : 0<G.endpointCount e (G.dartPair a).1 := by
    rcases hv with hv|hv <;> simp [endpointCount,hv]
  rcases Finset.mem_symmDiff.mp ha with ha|ha
  · have heq:=hM.eq_of_endpointCount_pos G he ha.1 hep hap
    exact Finset.mem_symmDiff.mpr (Or.inl ⟨he,fun hen=>ha.2 (heq ▸ hen)⟩)
  · apply Finset.mem_symmDiff.mpr
    left
    refine ⟨he,?_⟩
    intro hen
    have heq:=hN.eq_of_endpointCount_pos G hen ha.1 hep hap
    exact ha.2 (heq ▸ he)

end PlanarHom.MultiGraph
namespace PlanarHom.PlanarityLRRealization.RotationRows.FaceCut
open MultiGraph MultiGraph.Kasteleyn
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq (Dart E)]
variable {G : MultiGraph V E} {R : RotationRows G} {root : Dart E} {M N : Finset E}
variable (C : R.FaceCut (symmDiff M N) root)

theorem matching_symmDiff_inside_closed
    (hM : G.PerfectMatching M) (hN : G.PerfectMatching N) (e : E) (he : e∈M) :
    C.InsideVertex (G.src e)↔C.InsideVertex (G.dst e) := by
  by_cases hb:e∈symmDiff M N
  · have hs:¬C.InsideVertex (G.src e):=fun h=>(C.inside_excludes_boundary h (e,true) rfl) hb
    have ht:¬C.InsideVertex (G.dst e):=fun h=>(C.inside_excludes_boundary h (e,false) rfl) hb
    simp [hs,ht]
  · apply C.inside_iff_across_nonboundary e hb
    · intro a ha hm
      exact hb (hM.symmDiff_incident_closed hN e he a hm (.inl ha))
    · intro a ha hm
      exact hb (hM.symmDiff_incident_closed hN e he a hm (.inr ha))

theorem matching_symmDiff_inside_even
    (hM : G.PerfectMatching M) (hN : G.PerfectMatching N) :
    Even (Fintype.card {v : V // C.InsideVertex v}) := by
  have h:=hM.region_card_even G (Finset.univ.filter C.InsideVertex) (by
    intro e he
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact C.matching_symmDiff_inside_closed hM hN e he)
  simpa only [Fintype.card_subtype] using h

end PlanarHom.PlanarityLRRealization.RotationRows.FaceCut
