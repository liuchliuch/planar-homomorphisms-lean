import PlanarHom.OccurrenceMatchingCyclePatch

/-! NEW connectivity of actual occurrence perfect matchings by simple even cycle flips.
Progress counts differing occurrences, retaining parallel-edge two-cycles. -/
noncomputable section
open Classical
namespace PlanarHom.MultiGraph.PerfectMatching
variable {V E : Type*} [Finite V] {G : MultiGraph V E} {M N : Finset E}

theorem cycleFlip_connected (hM : G.PerfectMatching M) (hN : G.PerfectMatching N) :
    Relation.ReflTransGen (CycleFlipRel G) M N := by
  suffices ∀k,∀M:Finset E,(M\N).card=k→G.PerfectMatching M→
      Relation.ReflTransGen (CycleFlipRel G) M N from this _ M rfl hM
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro M hsize hM
      by_cases he:M=N
      · subst M
        exact .refl
      · obtain ⟨c,heven,hleft,hright⟩:=hM.exists_alternating_cycle hN he
        let P:=patchCycle (M:=M) (N:=N) c
        have hP:G.PerfectMatching P:=hM.patchCycle_perfect hN c heven hleft hright
        have hlt:(P\N).card<k:=by
          have hh:=patchCycle_difference_card_lt c hleft hright
          change (P\N).card<(M\N).card at hh
          omega
        have hpath:=ih (P\N).card hlt P rfl hP
        have hflip:CycleFlipRel G M P:=⟨hM.patchCycle_flip hN c heven hleft hright⟩
        exact (Relation.ReflTransGen.single hflip).trans hpath

end PlanarHom.MultiGraph.PerfectMatching
