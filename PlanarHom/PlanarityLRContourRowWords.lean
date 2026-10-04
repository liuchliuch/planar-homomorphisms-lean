import PlanarHom.PlanarityLRContourExcursions
import PlanarHom.FinitePermutationReturnWords

/-! NEW actual contour words expanded along the literal host rotation row. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints
open FinitePermutationReturnWords

namespace RotationRows
variable {V E : Type*} {G : MultiGraph V E} [DecidableEq (Dart E)] [BEq (Dart E)] [LawfulBEq (Dart E)]

theorem orbitPrefix_rotation (rows : RotationRows G) (a : Dart E) :
    orbitPrefix rows.rotation (rows.row (G.dartPair a).1).length a=
      (rows.row (G.dartPair a).1).rotate ((rows.row (G.dartPair a).1).idxOf a) := by
  let xs := rows.row (G.dartPair a).1
  have ha : a∈xs := (rows.mem _ _).mpr rfl
  have hi : xs.idxOf a<xs.length := List.idxOf_lt_length_iff.mpr ha
  have hga : xs[xs.idxOf a]=a := eq_of_beq (List.findIdx_getElem (xs := xs) (p := fun b => b == a) (w := hi))
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp only [orbitPrefix,List.getElem_map,List.getElem_range]
  rw [rows.rotation_iterate_eq_formPerm,Equiv.Perm.iterate_eq_pow]
  change (xs.formPerm^i) a=(xs.rotate (xs.idxOf a))[i]
  conv_lhs => rw [←hga]
  rw [List.formPerm_pow_apply_getElem xs (rows.nodup _) i _ hi,List.getElem_rotate]
  simp only [Nat.add_comm]

theorem rotation_period [Finite (Dart E)] (rows : RotationRows G) (a : Dart E) :
    Function.minimalPeriod rows.rotation a=(rows.row (G.dartPair a).1).length := by
  let xs := rows.row (G.dartPair a).1
  have ha : a∈xs := (rows.mem _ _).mpr rfl
  have hi : xs.idxOf a<xs.length := List.idxOf_lt_length_iff.mpr ha
  have hga : xs[xs.idxOf a]=a := eq_of_beq (List.findIdx_getElem (xs := xs) (p := fun b => b == a) (w := hi))
  apply period_eq_of_prefix_nodup rows.rotation a xs.length (List.length_pos_of_mem ha)
  · rw [rows.rotation_iterate_eq_formPerm,Equiv.Perm.iterate_eq_pow]
    change (xs.formPerm^xs.length) a=a
    conv_lhs => rw [←hga]
    rw [List.formPerm_pow_apply_getElem xs (rows.nodup _) _ _ hi]
    simpa only [Nat.add_mod_right,Nat.mod_eq_of_lt hi] using hga
  · rw [rows.orbitPrefix_rotation]
    exact List.nodup_rotate.mpr (rows.nodup _)
end RotationRows

def hostExcursionLength (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (a : Dart (Fin g.edges.length)) : ℕ :=
  (contour_host_excursion g hg rows a).choose

theorem hostExcursionLength_spec (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (a : Dart (Fin g.edges.length)) :
    0 < hostExcursionLength g hg rows a ∧
    hostExcursionLength g hg rows a≤Function.minimalPeriod (dfsContourForRows g hg rows) a ∧
    (dfsContourForRows g hg rows)^[hostExcursionLength g hg rows a] a=rows.rotation a ∧
    ∀ i, 0 < i → i < hostExcursionLength g hg rows a →
      dartHost g ((dfsContourForRows g hg rows)^[i] a)≠dartHost g a :=
  (contour_host_excursion g hg rows a).choose_spec

def hostExcursionWord (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (a : Dart (Fin g.edges.length)) : List (Dart (Fin g.edges.length)) :=
  orbitPrefix (dfsContourForRows g hg rows) (hostExcursionLength g hg rows a) a

/-- The actual global contour is exactly the concatenation of its host excursions,
in the host's literal cyclic row order. -/
theorem contour_word_eq_row_expansion (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (rows : RotationRows (g.toMultiGraph hg)) (a : Dart (Fin g.edges.length)) :
    orbitPrefix (dfsContourForRows g hg rows)
        (Function.minimalPeriod (dfsContourForRows g hg rows) a) a =
      ((rows.row ((g.toMultiGraph hg).dartPair a).1).rotate
        ((rows.row ((g.toMultiGraph hg).dartPair a).1).idxOf a)).flatMap
          (hostExcursionWord g hg rows) := by
  let q := fun b => dartHost g b=dartHost g a
  have hh := cycle_return_expansion (dfsContourForRows g hg rows) rows.rotation q
    (hostExcursionLength g hg rows)
    (fun b hb => (rotationRows_dartHost g hg rows b).trans hb)
    (fun b _ => (hostExcursionLength_spec g hg rows b).1)
    (fun b _ => (hostExcursionLength_spec g hg rows b).2.1)
    (fun b _ => (hostExcursionLength_spec g hg rows b).2.2.1)
    (fun b hb i hi hj he => (hostExcursionLength_spec g hg rows b).2.2.2 i hi hj (he.trans hb.symm))
    a rfl
  rw [rows.rotation_period,rows.orbitPrefix_rotation] at hh
  exact hh.symm

end PlanarHom.PlanarityLRRealization
