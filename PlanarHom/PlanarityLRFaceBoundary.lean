import PlanarHom.PlanarityLRFacePermutation
import PlanarHom.FiniteOrbitBoundary

/-! NEW exact one-cycle semantics for the literal bounded boundary program. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph.Kasteleyn PlanarityLRDirect

/-- The emitted boundary is precisely one minimal-period traversal. -/
theorem boundary_eq_period_walk (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) :
    PlanarityFaceCode.boundary g bits (eraseDart a) =
      (List.range (Function.minimalPeriod (facePermutation g hg bits) a)).map
        (fun n => eraseDart ((facePermutation g hg bits)^[n] a)) := by
  let p := Function.minimalPeriod (facePermutation g hg bits) a
  have hp : 0 < p := Function.minimalPeriod_pos_of_mem_periodicPts
    ((facePermutation g hg bits).injective.mem_periodicPts a)
  have hb : p ≤ 2*g.edges.length := by
    simpa only [dart_card] using (Function.minimalPeriod_le_card (f := facePermutation g hg bits) (x := a))
  have hret : (faceStep g bits)^[p] (eraseDart a) = eraseDart a := by
    rw [← facePermutation_iterate_erase g hg bits a p]
    exact congrArg eraseDart (Function.iterate_minimalPeriod (f := facePermutation g hg bits) (x := a))
  have hfirst : ∀ i : ℕ, 0 < i → i < p → (faceStep g bits)^[i] (eraseDart a) ≠ eraseDart a := by
    intro i hi hip he
    have hi0 := eraseDart_injective g ((facePermutation_iterate_erase g hg bits a i).trans he)
    have hz := (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod hip hp).mp hi0
    omega
  have he := FiniteOrbitBoundary.trim_walk (fun n => (faceStep g bits)^[n] (eraseDart a)) p
    (2*g.edges.length) hp hb hret hfirst
  dsimp only [Function.iterate_zero_apply] at he
  rw [PlanarityFaceCode.boundary,PlanarityFaceCode.orbit,PlanarityFaceCode.walk,he]
  apply List.map_congr_left
  intro n _
  exact (facePermutation_iterate_erase g hg bits a n).symm

theorem boundary_nodup (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) :
    (PlanarityFaceCode.boundary g bits (eraseDart a)).Nodup := by
  rw [boundary_eq_period_walk g hg bits a]
  apply (List.nodup_map_iff_inj_on List.nodup_range).mpr
  intro i hi j hj he
  exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
    (List.mem_range.mp hi) (List.mem_range.mp hj)).mp (eraseDart_injective g he)

theorem boundary_length_pos (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) :
    0 < (PlanarityFaceCode.boundary g bits (eraseDart a)).length := by
  rw [boundary_eq_period_walk g hg bits a]
  simp only [List.length_map,List.length_range]
  exact Function.minimalPeriod_pos_of_mem_periodicPts ((facePermutation g hg bits).injective.mem_periodicPts a)

theorem mem_boundary_iff_orbit (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) (b : PlanarityRotationCode.Dart) :
    b ∈ PlanarityFaceCode.boundary g bits (eraseDart a) ↔ b ∈ PlanarityFaceCode.orbit g bits (eraseDart a) := by
  rw [boundary_eq_period_walk g hg bits a]
  simp only [List.mem_map,List.mem_range,PlanarityFaceCode.orbit,PlanarityFaceCode.walk]
  constructor
  · rintro ⟨i,hi,he⟩
    have hb : Function.minimalPeriod (facePermutation g hg bits) a ≤ 2*g.edges.length := by
      simpa only [dart_card] using (Function.minimalPeriod_le_card (f := facePermutation g hg bits) (x := a))
    exact ⟨i,lt_of_lt_of_le hi hb,(facePermutation_iterate_erase g hg bits a i).symm.trans he⟩
  · rintro ⟨i,hi,he⟩
    have hp := Function.minimalPeriod_pos_of_mem_periodicPts ((facePermutation g hg bits).injective.mem_periodicPts a)
    refine ⟨i % Function.minimalPeriod (facePermutation g hg bits) a,Nat.mod_lt _ hp,?_⟩
    rw [Function.iterate_mod_minimalPeriod_eq,facePermutation_iterate_erase]
    exact he

end PlanarHom.PlanarityLRRealization
