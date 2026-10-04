import PlanarHom.PlanarityLRDualReachability

/-! NEW exact contour permutation interface for tree-collar geometry.
At a selected tree dart cross to its reverse before rotating; at every remaining
port rotate at its own host. Thus the order is fully specified by the rows. -/
noncomputable section
open Classical
namespace PlanarHom.PlanarityLRRealization
open MultiGraph MultiGraph.Kasteleyn

/-- Reverse exactly the selected occurrence pairs. -/
def partialReverse (E : Type*) (selected : E → Bool) : Equiv.Perm (Dart E) where
  toFun a := if selected a.1 then reversePerm E a else a
  invFun a := if selected a.1 then reversePerm E a else a
  left_inv a := by
    rcases a with ⟨e,b⟩
    cases h : selected e <;> simp [h,reversePerm]
  right_inv a := by
    rcases a with ⟨e,b⟩
    cases h : selected e <;> simp [h,reversePerm]

def contourPermutation {V E : Type*} {G : MultiGraph V E} [DecidableEq (Dart E)]
    (rows : RotationRows G) (selected : E → Bool) : Equiv.Perm (Dart E) :=
  (partialReverse E selected).trans rows.rotation

@[simp] theorem contourPermutation_selected {V E : Type*} {G : MultiGraph V E} [DecidableEq (Dart E)]
    (rows : RotationRows G) (selected : E → Bool) (a : Dart E) (ha : selected a.1=true) :
    contourPermutation rows selected a = rows.rotation (reversePerm E a) := by
  simp [contourPermutation,partialReverse,ha]

@[simp] theorem contourPermutation_port {V E : Type*} {G : MultiGraph V E} [DecidableEq (Dart E)]
    (rows : RotationRows G) (selected : E → Bool) (a : Dart E) (ha : selected a.1=false) :
    contourPermutation rows selected a = rows.rotation a := by
  simp [contourPermutation,partialReverse,ha]

/-- The exact emitted non-tree port word of one contour cycle. -/
def contourPortWord {V E : Type*} {G : MultiGraph V E} [DecidableEq (Dart E)]
    (rows : RotationRows G) (selected : E → Bool) (a : Dart E) : List (Dart E) :=
  ((List.range (Function.minimalPeriod (contourPermutation rows selected) a)).map
    (fun n => (contourPermutation rows selected)^[n] a)).filter (fun b => !(selected b.1))

theorem contourPortWord_nodup {V E : Type*} {G : MultiGraph V E} [DecidableEq (Dart E)]
    (rows : RotationRows G) (selected : E → Bool) (a : Dart E) : (contourPortWord rows selected a).Nodup := by
  apply List.Nodup.filter
  apply (List.nodup_map_iff_inj_on List.nodup_range).mpr
  intro i hi j hj he
  exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod (List.mem_range.mp hi) (List.mem_range.mp hj)).mp he

theorem mem_contourPortWord_iff {V E : Type*} {G : MultiGraph V E} [DecidableEq (Dart E)] [Finite (Dart E)]
    (rows : RotationRows G) (selected : E → Bool) (a b : Dart E) :
    b ∈ contourPortWord rows selected a ↔
      (contourPermutation rows selected).SameCycle a b ∧ selected b.1=false := by
  have hh : b ∈ ((List.range (Function.minimalPeriod (contourPermutation rows selected) a)).map
      (fun n => (contourPermutation rows selected)^[n] a)) ↔
      (contourPermutation rows selected).SameCycle a b := by
    simp only [List.mem_map,List.mem_range]
    constructor
    · rintro ⟨n,_,hn⟩
      exact ⟨(n:ℤ),by simpa only [zpow_natCast,Equiv.Perm.iterate_eq_pow] using hn⟩
    · intro h
      obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
      let f := contourPermutation rows selected
      have hp := Function.minimalPeriod_pos_of_mem_periodicPts (f.injective.mem_periodicPts a)
      refine ⟨n % Function.minimalPeriod f a,Nat.mod_lt _ hp,?_⟩
      rw [Function.iterate_mod_minimalPeriod_eq,Equiv.Perm.iterate_eq_pow]
      exact hn
  rw [contourPortWord,List.mem_filter,hh]
  cases selected b.1 <;> simp

end PlanarHom.PlanarityLRRealization
