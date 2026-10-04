import PlanarHom.PlanarityLRFaceRepresentatives
import PlanarHom.PlanarityLRComponents

/-! NEW exact component preservation of every raw face transition and emitted
boundary. DFS roots are computed, not supplied by a connectivity oracle. -/
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints
open PlanarityFaceCode

theorem source_target_componentRoot (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {e : ℕ} (he : e < g.edges.length) :
    componentRoot g (source g e) = componentRoot g (target g e) := by
  by_cases ht : isTree g e = true
  · exact tree_componentRoot g hg ht
  · by_cases hn : source g e = target g e
    · rw [hn]
    · have hb : isBack g e = true := by simp [isBack,he,Bool.eq_false_iff.mpr ht,hn]
      exact (componentRoot_eq_of_desc g (source_target_valid g hg he).1
        (Or.inr (back_target_ancestor g hg hb))).symm

theorem endpoints_componentRoot (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {e : ℕ} (he : e < g.edges.length) :
    componentRoot g (edge g e).1 = componentRoot g (edge g e).2.1 := by
  have h := source_target_componentRoot g hg he
  rcases PlanarityRotationCode.source_target_endpoints g e with hh | hh
  · have hs := congrArg Prod.fst hh
    have ht := congrArg Prod.snd hh
    simp only [Prod.fst,Prod.snd] at hs ht
    rw [hs,ht] at h
    exact h
  · have hs := congrArg Prod.fst hh
    have ht := congrArg Prod.snd hh
    simp only [Prod.fst,Prod.snd] at hs ht
    rw [hs,ht] at h
    exact h.symm

theorem reverse_componentRoot (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    {a : PlanarityRotationCode.Dart} (ha : a.1 < g.edges.length) :
    componentRoot g (PlanarityRotationCode.host g (PlanarityRotationCode.reverse a)) =
      componentRoot g (PlanarityRotationCode.host g a) := by
  have he := endpoints_componentRoot g hg ha
  rcases a with ⟨e,b⟩
  cases b <;> simp only [PlanarityRotationCode.reverse,PlanarityRotationCode.host,Bool.not_false,
    Bool.not_true,Bool.false_eq_true,reduceIte] <;> first | exact he | exact he.symm

theorem directRotation_host (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) :
    PlanarityRotationCode.host g (directRotation g bits (eraseDart a)) = PlanarityRotationCode.host g (eraseDart a) := by
  rw [← directRotationRows_erase g hg bits a,eraseDart_host g hg,eraseDart_host g hg]
  exact congrArg Fin.val ((directRotationRows g hg bits).rotation_host a)

theorem facePermutation_componentRoot (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) :
    componentRoot g (PlanarityRotationCode.host g (eraseDart (facePermutation g hg bits a))) =
      componentRoot g (PlanarityRotationCode.host g (eraseDart a)) := by
  rw [facePermutation_erase]
  change componentRoot g (PlanarityRotationCode.host g
    (directRotation g bits (eraseDart (reversePerm _ a)))) = _
  rw [directRotation_host g hg bits]
  exact reverse_componentRoot g hg (a := eraseDart a) a.1.isLt

theorem facePermutation_iterate_componentRoot (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) (n : ℕ) :
    componentRoot g (PlanarityRotationCode.host g (eraseDart ((facePermutation g hg bits)^[n] a))) =
      componentRoot g (PlanarityRotationCode.host g (eraseDart a)) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',facePermutation_componentRoot,ih]

theorem orbit_componentRoot (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) {b : PlanarityRotationCode.Dart}
    (hb : b ∈ orbit g bits (eraseDart a)) :
    componentRoot g (PlanarityRotationCode.host g b) = componentRoot g (PlanarityRotationCode.host g (eraseDart a)) := by
  obtain ⟨n,_,he⟩ := List.mem_map.mp hb
  rw [← facePermutation_iterate_erase g hg bits a n] at he
  rw [← he]
  exact facePermutation_iterate_componentRoot g hg bits a n

theorem boundary_componentRoot (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) {b : PlanarityRotationCode.Dart}
    (hb : b ∈ boundary g bits (eraseDart a)) :
    componentRoot g (PlanarityRotationCode.host g b) = componentRoot g (PlanarityRotationCode.host g (eraseDart a)) :=
  orbit_componentRoot g hg bits a ((mem_boundary_iff_orbit g hg bits a b).mp hb)

theorem representative_componentRoot (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) :
    componentRoot g (PlanarityRotationCode.host g (representative g bits (eraseDart a))) =
      componentRoot g (PlanarityRotationCode.host g (eraseDart a)) :=
  orbit_componentRoot g hg bits a (representative_mem_orbit g hg bits a)

end PlanarHom.PlanarityLRRealization
