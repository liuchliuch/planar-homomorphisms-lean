import Mathlib.GroupTheory.Perm.List

/-! A finite cyclic row cut at a specified closing dart is unique. This
eliminates the arbitrary initial representative chosen when rows are recovered
from a permutation certificate. -/
namespace PlanarHom
variable {D : Type} [DecidableEq D]

 theorem ending_words_eq (xs ys : List D) (a : D)
    (hx : (xs++[a]).Nodup) (hy : (ys++[a]).Nodup)
    (hm : ∀b,b∈xs++[a] ↔ b∈ys++[a])
    (hp : (xs++[a]).formPerm=(ys++[a]).formPerm) : xs++[a]=ys++[a] := by
  have hlen := ((List.perm_ext_iff_of_nodup hx hy).mpr hm).length_eq
  have hxp : (a::xs.reverse).Nodup := by simpa only [List.reverse_append,List.reverse_singleton,List.singleton_append] using List.nodup_reverse.mpr hx
  have hyp : (a::ys.reverse).Nodup := by simpa only [List.reverse_append,List.reverse_singleton,List.singleton_append] using List.nodup_reverse.mpr hy
  have hrev : (a::xs.reverse).formPerm=(a::ys.reverse).formPerm := by
    have hh := congrArg Inv.inv hp
    simpa only [←List.formPerm_reverse,List.reverse_append,List.reverse_singleton,
      List.singleton_append] using hh
  apply List.reverse_injective
  simp only [List.reverse_append,List.reverse_singleton,List.singleton_append]
  apply List.ext_getElem
  · simpa using hlen
  · intro i hi hj
    have hh := List.formPerm_pow_apply_head a xs.reverse hxp i
    have hk := List.formPerm_pow_apply_head a ys.reverse hyp i
    simp only [Nat.mod_eq_of_lt hi] at hh
    simp only [Nat.mod_eq_of_lt hj] at hk
    rw [←hh,←hk,hrev]
end PlanarHom
