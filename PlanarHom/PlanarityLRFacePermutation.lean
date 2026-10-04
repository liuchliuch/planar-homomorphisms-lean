import PlanarHom.PlanarityLRRealizationRotationSystem
import PlanarHom.PlanarityFaceCodeProgram
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-! NEW identification of the bounded raw face orbit with the exact cycles of
the computed typed dart permutation. This is combinatorial face semantics;
planar region realization is proved separately. -/
noncomputable section
open Classical
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph.Kasteleyn PlanarityLRDirect

/-- Dart reversal retains the literal occurrence and flips only its direction. -/
def reversePerm (E : Type*) : Equiv.Perm (Dart E) where
  toFun a := (a.1,!a.2)
  invFun a := (a.1,!a.2)
  left_inv a := by cases a; simp
  right_inv a := by cases a; simp

def facePermutation (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool) :
    Equiv.Perm (Dart (Fin g.edges.length)) :=
  (reversePerm _).trans (directRotationRows g hg bits).rotation

@[simp] theorem erase_reversePerm {g : MixedCode} (a : Dart (Fin g.edges.length)) :
    eraseDart (reversePerm _ a) = PlanarityRotationCode.reverse (eraseDart a) := rfl

theorem facePermutation_erase (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) :
    eraseDart (facePermutation g hg bits a) = faceStep g bits (eraseDart a) := by
  exact directRotationRows_erase g hg bits (reversePerm _ a)

theorem facePermutation_iterate_erase (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) (n : ℕ) :
    eraseDart ((facePermutation g hg bits)^[n] a) = (faceStep g bits)^[n] (eraseDart a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply',Function.iterate_succ_apply',facePermutation_erase,ih]

@[simp] theorem dart_card (g : MixedCode) : Fintype.card (Dart (Fin g.edges.length)) = 2*g.edges.length := by
  simp [Dart,Nat.mul_comm]

theorem mem_orbit_iff_iterate (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a b : Dart (Fin g.edges.length)) :
    eraseDart b ∈ PlanarityFaceCode.orbit g bits (eraseDart a) ↔
      ∃ n, (facePermutation g hg bits)^[n] a = b := by
  simp only [PlanarityFaceCode.orbit,PlanarityFaceCode.walk,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨n,_,hn⟩
    exact ⟨n,eraseDart_injective g ((facePermutation_iterate_erase g hg bits a n).trans hn)⟩
  · rintro ⟨n,rfl⟩
    let p := Function.minimalPeriod (facePermutation g hg bits) a
    have hp : 0 < p := Function.minimalPeriod_pos_of_mem_periodicPts
      ((facePermutation g hg bits).injective.mem_periodicPts a)
    have hb : p ≤ 2*g.edges.length := by
      simpa only [dart_card] using (Function.minimalPeriod_le_card (f := facePermutation g hg bits) (x := a))
    refine ⟨n%p,lt_of_lt_of_le (Nat.mod_lt _ hp) hb,?_⟩
    rw [← facePermutation_iterate_erase g hg bits a (n%p)]
    exact congrArg eraseDart (Function.iterate_mod_minimalPeriod_eq (f := facePermutation g hg bits) (x := a) (n := n))

theorem mem_orbit_iff_sameCycle (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a b : Dart (Fin g.edges.length)) :
    eraseDart b ∈ PlanarityFaceCode.orbit g bits (eraseDart a) ↔
      (facePermutation g hg bits).SameCycle a b := by
  rw [mem_orbit_iff_iterate]
  constructor
  · rintro ⟨n,hn⟩
    refine ⟨(n : ℤ),?_⟩
    simpa only [zpow_natCast,Equiv.Perm.iterate_eq_pow] using hn
  · intro h
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    exact ⟨n,by simpa only [Equiv.Perm.iterate_eq_pow] using hn⟩

theorem orbit_index_valid (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (a : Dart (Fin g.edges.length)) {b : PlanarityRotationCode.Dart}
    (hb : b ∈ PlanarityFaceCode.orbit g bits (eraseDart a)) : b.1 < g.edges.length := by
  obtain ⟨n,_,he⟩ := List.mem_map.mp hb
  rw [← facePermutation_iterate_erase g hg bits a n] at he
  rw [← he]
  exact ((facePermutation g hg bits)^[n] a).1.isLt

end PlanarHom.PlanarityLRRealization
