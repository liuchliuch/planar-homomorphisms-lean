import PlanarHom.PlanarityRowFaceCodeProgram
import PlanarHom.RotationFaceCycleDuality

/-! NEW arbitrary materialized-row face semantics. This adapts the verified
computed-LR orbit proofs to the exact Realizes row-table interface. -/
noncomputable section
namespace PlanarHom.PlanarityRowFaceCode
open Complexity MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRealization

 theorem rotation_erase (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R)
    (a : Dart (Fin g.edges.length)) : eraseDart (R.rotation a)=rotation g rows (eraseDart a) := by
  rw [rotation,eraseDart_host g hg]
  rw [hrows ((g.toMultiGraph hg).dartPair a).1]
  rw [rowNext_eq_formPerm _ ((R.nodup _).map (eraseDart_injective g)) _
    (List.mem_map.mpr ⟨a,(R.mem _ _).mpr rfl,rfl⟩)]
  exact (map_formPerm_apply eraseDart (eraseDart_injective g) _ (R.nodup _) ((R.mem _ _).mpr rfl)).symm

 theorem facePermutation_erase (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R)
    (a : Dart (Fin g.edges.length)) : eraseDart (R.facePerm a)=faceStep g rows (eraseDart a) :=
  rotation_erase g hg rows R hrows (reversePerm _ a)

theorem facePermutation_iterate_erase (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) (a : Dart (Fin g.edges.length)) (n : ℕ) :
    eraseDart ((R.facePerm)^[n] a) = (faceStep g rows)^[n] (eraseDart a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply',Function.iterate_succ_apply',facePermutation_erase g hg rows R hrows,ih]

theorem mem_orbit_iff_iterate (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) (a b : Dart (Fin g.edges.length)) :
    eraseDart b ∈ PlanarityRowFaceCode.orbit g rows (eraseDart a) ↔
      ∃ n, (R.facePerm)^[n] a = b := by
  simp only [PlanarityRowFaceCode.orbit,PlanarityRowFaceCode.walk,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨n,_,hn⟩
    exact ⟨n,eraseDart_injective g ((facePermutation_iterate_erase g hg rows R hrows a n).trans hn)⟩
  · rintro ⟨n,rfl⟩
    let p := Function.minimalPeriod (R.facePerm) a
    have hp : 0 < p := Function.minimalPeriod_pos_of_mem_periodicPts
      ((R.facePerm).injective.mem_periodicPts a)
    have hb : p ≤ 2*g.edges.length := by
      simpa only [dart_card] using (Function.minimalPeriod_le_card (f := R.facePerm) (x := a))
    refine ⟨n%p,lt_of_lt_of_le (Nat.mod_lt _ hp) hb,?_⟩
    rw [← facePermutation_iterate_erase g hg rows R hrows a (n%p)]
    exact congrArg eraseDart (Function.iterate_mod_minimalPeriod_eq (f := R.facePerm) (x := a) (n := n))

theorem mem_orbit_iff_sameCycle (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) (a b : Dart (Fin g.edges.length)) :
    eraseDart b ∈ PlanarityRowFaceCode.orbit g rows (eraseDart a) ↔
      (R.facePerm).SameCycle a b := by
  rw [mem_orbit_iff_iterate g hg rows R hrows]
  constructor
  · rintro ⟨n,hn⟩
    refine ⟨(n : ℤ),?_⟩
    simpa only [zpow_natCast,Equiv.Perm.iterate_eq_pow] using hn
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    exact ⟨n,by simpa only [Equiv.Perm.iterate_eq_pow] using hn⟩

theorem orbit_index_valid (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : Rows) (R : RotationRows (g.toMultiGraph hg)) (hrows : Realizes g hg rows R) (a : Dart (Fin g.edges.length)) {b : PlanarityRotationCode.Dart}
    (hb : b ∈ PlanarityRowFaceCode.orbit g rows (eraseDart a)) : b.1 < g.edges.length := by
  obtain ⟨n,_,he⟩ := List.mem_map.mp hb
  rw [← facePermutation_iterate_erase g hg rows R hrows a n] at he
  rw [← he]
  exact ((R.facePerm)^[n] a).1.isLt

end PlanarHom.PlanarityRowFaceCode
