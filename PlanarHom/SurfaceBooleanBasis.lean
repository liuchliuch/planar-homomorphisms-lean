import PlanarHom.SurfaceBooleanReduction
import Mathlib.Algebra.Field.ZMod

/-! NEW proof that the executable pivot fold computes a genuine basis of the
input row span, with no preselected basis or rank oracle. -/
namespace PlanarHom.SurfaceBooleanRows

theorem addRow_sublist (bs : BasisRows) (r : Row) : bs.Sublist (addRow bs r) := by
  dsimp only [addRow]
  split
  · exact List.sublist_append_left _ _
  · exact List.Sublist.refl _

theorem rowSpan_addRow (bs : BasisRows) (r : Row) :
    rowSpan (addRow bs r)=rowSpan bs ⊔ Submodule.span (ZMod 2) {value r} := by
  let s := reduce bs r
  have hd : value r-value s∈rowSpan bs := by
    rw [value_reduce]
    exact reduction_difference_mem bs (value r)
  have hold : rowSpan bs≤rowSpan (addRow bs r) := rowSpan_mono (addRow_sublist bs r)
  have hs : value s∈rowSpan (addRow bs r) := by
    by_cases hp : pivot s<s.length
    · apply row_mem_span _ (pivot s,s)
      simp [addRow,s,hp]
    · have hz := value_eq_zero_of_no_pivot s hp
      rw [hz]
      exact Submodule.zero_mem _
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨p,hp,rfl⟩
    dsimp only [addRow] at hp
    split at hp
    · rcases List.mem_append.mp hp with hp | hp
      · exact Submodule.mem_sup_left (row_mem_span bs p hp)
      · have he : p=(pivot s,s) := by simpa [s] using hp
        subst p
        have hr : value r∈rowSpan bs ⊔ Submodule.span (ZMod 2) {value r} :=
          Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
        have hh := Submodule.sub_mem (rowSpan bs ⊔ Submodule.span (ZMod 2) {value r}) hr (Submodule.mem_sup_left hd)
        simpa only [sub_sub_cancel] using hh
    · exact Submodule.mem_sup_left (row_mem_span bs p hp)
  · apply sup_le hold
    apply Submodule.span_le.mpr
    rintro x (rfl : x=value r)
    have hh := Submodule.add_mem (rowSpan (addRow bs r)) (hold hd) hs
    simpa only [sub_add_cancel] using hh

def inputSpan (rs : List Row) : Submodule (ZMod 2) Vector :=
  Submodule.span (ZMod 2) {x | ∃r∈rs,value r=x}

@[simp] theorem inputSpan_nil : inputSpan []=⊥ := by simp [inputSpan]
@[simp] theorem rowSpan_nil : rowSpan []=⊥ := by simp [rowSpan]

theorem inputSpan_cons (r : Row) (rs : List Row) :
    inputSpan (r::rs)=Submodule.span (ZMod 2) {value r} ⊔ inputSpan rs := by
  rw [inputSpan,inputSpan,←Submodule.span_union]
  congr 1
  ext x
  simp only [Set.mem_setOf_eq,List.mem_cons,Set.mem_union,Set.mem_singleton_iff]
  constructor
  · rintro ⟨s,hs,hx⟩
    rcases hs with rfl | hs
    · exact Or.inl hx.symm
    · exact Or.inr ⟨s,hs,hx⟩
  · rintro (rfl | ⟨s,hs,hx⟩)
    · exact ⟨r,Or.inl rfl,rfl⟩
    · exact ⟨s,Or.inr hs,hx⟩

theorem fold_rowSpan (rs : List Row) (bs : BasisRows) :
    rowSpan (rs.foldl addRow bs)=rowSpan bs ⊔ inputSpan rs := by
  induction rs generalizing bs with
  | nil => simp
  | cons r rs ih =>
      simp only [List.foldl_cons,ih,rowSpan_addRow,inputSpan_cons,sup_assoc]

theorem basis_span (rs : List Row) : rowSpan (basis rs)=inputSpan rs := by
  simpa only [basis,rowSpan_nil,bot_sup_eq] using fold_rowSpan rs []

def rowVectors (bs : BasisRows) : Fin bs.length → Vector := fun i => value (bs.get i).2

theorem rowVectors_cons (p : PivotRow) (bs : BasisRows) :
    rowVectors (p::bs)=Fin.cons (value p.2) (rowVectors bs) := by
  funext i
  cases i using Fin.cases <;> rfl

theorem echelon_independent (bs : BasisRows) (h : Echelon bs) :
    LinearIndependent (ZMod 2) (rowVectors bs) := by
  induction bs with
  | nil =>
      change LinearIndependent (ZMod 2) (rowVectors ([]:BasisRows) : Fin 0 → Vector)
      letI : IsEmpty (Fin ([]:BasisRows).length) := ⟨fun i => Fin.elim0 i⟩
      exact linearIndependent_empty_type
  | cons p bs ih =>
      rw [rowVectors_cons]
      apply linearIndependent_fin_cons.mpr
      refine ⟨ih ⟨fun q hq => h.1 q (by simp [hq]),h.2.tail⟩,?_⟩
      have hz : Submodule.span (ZMod 2) (Set.range (rowVectors bs)) ≤
          LinearMap.ker (LinearMap.proj p.1 : Vector →ₗ[ZMod 2] ZMod 2) := by
        apply Submodule.span_le.mpr
        rintro x ⟨i,rfl⟩
        have hi : bs.get i∈bs := List.get_mem bs i
        have hzero := (List.pairwise_cons.mp h.2).1 (bs.get i) hi
        change value (bs.get i).2 p.1=0
        change bitValue (bitAt (bs.get i).2 p.1)=0
        rw [hzero]
        rfl
      intro hp
      have he := hz hp
      have htrue := h.1 p (by simp)
      change value p.2 p.1=0 at he
      simpa [value,htrue] using he

theorem basis_independent (rs : List Row) :
    LinearIndependent (ZMod 2) (rowVectors (basis rs)) :=
  echelon_independent _ (echelon_basis rs)

end PlanarHom.SurfaceBooleanRows
