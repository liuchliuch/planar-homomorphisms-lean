import PlanarHom.SurfaceBooleanRows

/-! NEW pivot invariants for the literal Boolean elimination program. -/
namespace PlanarHom.SurfaceBooleanRows

def Echelon (bs : BasisRows) : Prop :=
  (∀p∈bs,bitAt p.2 p.1=true) ∧ bs.Pairwise (fun p q => bitAt q.2 p.1=false)

@[simp] theorem echelon_nil : Echelon [] := by simp [Echelon]

theorem clear_at (r : Row) (p : PivotRow) (j : ℕ) :
    bitAt (clear r p) j = if bitAt r p.1 then bitAt r j ^^ bitAt p.2 j else bitAt r j := by
  cases h : bitAt r p.1 <;> simp [clear,h,at_xorRows]

theorem clear_pivot (r : Row) (p : PivotRow) (hp : bitAt p.2 p.1=true) :
    bitAt (clear r p) p.1=false := by
  rw [clear_at,hp]
  cases bitAt r p.1 <;> rfl

theorem clear_preserves (r : Row) (p : PivotRow) (j : ℕ) (hp : bitAt p.2 j=false) :
    bitAt (clear r p) j=bitAt r j := by
  rw [clear_at,hp]
  cases bitAt r p.1 <;> simp

theorem reduce_preserves (bs : BasisRows) (r : Row) (j : ℕ)
    (h : ∀p∈bs,bitAt p.2 j=false) : bitAt (reduce bs r) j=bitAt r j := by
  induction bs generalizing r with
  | nil => rfl
  | cons p bs ih =>
      change bitAt (reduce bs (clear r p)) j=bitAt r j
      rw [ih (clear r p) (fun q hq => h q (by simp [hq]))]
      exact clear_preserves r p j (h p (by simp))

theorem reduce_pivots (bs : BasisRows) (h : Echelon bs) (r : Row) :
    ∀p∈bs,bitAt (reduce bs r) p.1=false := by
  induction bs generalizing r with
  | nil => simp
  | cons p bs ih =>
      have hp : bitAt p.2 p.1=true := h.1 p (by simp)
      have ht : Echelon bs := ⟨fun q hq => h.1 q (by simp [hq]),h.2.tail⟩
      have hzero : ∀q∈bs,bitAt q.2 p.1=false := (List.pairwise_cons.mp h.2).1
      intro q hq
      rcases List.mem_cons.mp hq with hqp | hq
      · subst q
        change bitAt (reduce bs (clear r p)) p.1=false
        rw [reduce_preserves bs (clear r p) p.1 hzero]
        exact clear_pivot r p hp
      · exact ih ht (clear r p) q hq

theorem echelon_addRow (bs : BasisRows) (h : Echelon bs) (r : Row) :
    Echelon (addRow bs r) := by
  dsimp only [addRow]
  split
  · rename_i hp
    constructor
    · intro p hp'
      rcases List.mem_append.mp hp' with hb | hn
      · exact h.1 p hb
      · have he : p=(pivot (reduce bs r),reduce bs r) := by simpa using hn
        subst p
        exact at_pivot _ hp
    · apply List.pairwise_append.mpr
      refine ⟨h.2,by simp,?_⟩
      intro p hp' q hq
      have he : q=(pivot (reduce bs r),reduce bs r) := by simpa using hq
      subst q
      exact reduce_pivots bs h r p hp'
  · exact h

theorem echelon_fold (rs : List Row) (bs : BasisRows) (h : Echelon bs) :
    Echelon (rs.foldl addRow bs) := by
  induction rs generalizing bs with
  | nil => exact h
  | cons r rs ih => exact ih (addRow bs r) (echelon_addRow bs h r)

theorem echelon_basis (rs : List Row) : Echelon (basis rs) := echelon_fold rs [] echelon_nil

end PlanarHom.SurfaceBooleanRows
