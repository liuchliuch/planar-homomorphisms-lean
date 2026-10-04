import PlanarHom.PlanarityRowFaceRepresentatives
import PlanarHom.PlanarityLRFaceComponents

/-! NEW actual DFS-component preservation for arbitrary realized row tables. -/
noncomputable section
namespace PlanarHom.PlanarityRowFaceCode
open Complexity MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints PlanarityLRRealization
theorem rowRotation_host (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) (a : Dart (Fin g.edges.length)) :
    PlanarityRotationCode.host g (rotation g rows (eraseDart a)) = PlanarityRotationCode.host g (eraseDart a) := by
  rw [← rotation_erase g hg rows R hrows a,eraseDart_host g hg,eraseDart_host g hg]
  exact congrArg Fin.val ((R).rotation_host a)

theorem facePermutation_componentRoot (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) (a : Dart (Fin g.edges.length)) :
    componentRoot g (PlanarityRotationCode.host g (eraseDart (R.facePerm a))) =
      componentRoot g (PlanarityRotationCode.host g (eraseDart a)) := by
  rw [facePermutation_erase g hg rows R hrows]
  change componentRoot g (PlanarityRotationCode.host g
    (rotation g rows (eraseDart (reversePerm _ a)))) = _
  rw [rowRotation_host g hg rows R hrows]
  exact reverse_componentRoot g hg (a := eraseDart a) a.1.isLt

theorem facePermutation_iterate_componentRoot (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) (a : Dart (Fin g.edges.length)) (n : ℕ) :
    componentRoot g (PlanarityRotationCode.host g (eraseDart ((R.facePerm)^[n] a))) =
      componentRoot g (PlanarityRotationCode.host g (eraseDart a)) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',facePermutation_componentRoot g hg rows R hrows,ih]

theorem orbit_componentRoot (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) (a : Dart (Fin g.edges.length)) {b : PlanarityRotationCode.Dart}
    (hb : b ∈ orbit g rows (eraseDart a)) :
    componentRoot g (PlanarityRotationCode.host g b) = componentRoot g (PlanarityRotationCode.host g (eraseDart a)) := by
  obtain ⟨n,_,he⟩ := List.mem_map.mp hb
  rw [← facePermutation_iterate_erase g hg rows R hrows a n] at he
  rw [← he]
  exact facePermutation_iterate_componentRoot g hg rows R hrows a n

theorem boundary_componentRoot (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) (a : Dart (Fin g.edges.length)) {b : PlanarityRotationCode.Dart}
    (hb : b ∈ boundary g rows (eraseDart a)) :
    componentRoot g (PlanarityRotationCode.host g b) = componentRoot g (PlanarityRotationCode.host g (eraseDart a)) :=
  orbit_componentRoot g hg rows R hrows a ((mem_boundary_iff_orbit g hg rows R hrows a b).mp hb)

theorem representative_componentRoot (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) (a : Dart (Fin g.edges.length)) :
    componentRoot g (PlanarityRotationCode.host g (representative g rows (eraseDart a))) =
      componentRoot g (PlanarityRotationCode.host g (eraseDart a)) :=
  orbit_componentRoot g hg rows R hrows a (representative_mem_orbit g hg rows R hrows a)

end PlanarHom.PlanarityRowFaceCode
