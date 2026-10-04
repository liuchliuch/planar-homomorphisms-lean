import PlanarHom.OccurrenceKasteleynTablePrimitives
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-! NEW executable zero-padded Boolean rows for the supplied-surface homology
algorithm. Malformed/ragged inputs are handled by the same total program. -/
namespace PlanarHom.SurfaceBooleanRows
abbrev Row := List Bool
abbrev PivotRow := ℕ × Row
abbrev BasisRows := List PivotRow

def bitAt (r : Row) (i : ℕ) : Bool := r[i]?.getD false

def xorRows : Row → Row → Row
  | [],s => s
  | r,[] => r
  | a::r,b::s => (a ^^ b)::xorRows r s

@[simp] theorem at_nil (i : ℕ) : bitAt [] i=false := rfl
@[simp] theorem at_cons_zero (a : Bool) (r : Row) : bitAt (a::r) 0=a := rfl
@[simp] theorem at_cons_succ (a : Bool) (r : Row) (i : ℕ) : bitAt (a::r) (i+1)=bitAt r i := rfl
@[simp] theorem xorRows_nil (r : Row) : xorRows r []=r := by cases r <;> rfl
@[simp] theorem xorRows_length (r s : Row) : (xorRows r s).length=max r.length s.length := by
  induction r generalizing s with
  | nil => simp [xorRows]
  | cons a r ih => cases s <;> simp [xorRows,ih,Nat.succ_max_succ]

theorem at_xorRows (r s : Row) (i : ℕ) : bitAt (xorRows r s) i=(bitAt r i ^^ bitAt s i) := by
  induction r generalizing s i with
  | nil => simp [xorRows]
  | cons a r ih =>
      cases s with
      | nil => simp [xorRows]
      | cons b s => cases i <;> simp [xorRows,ih]

def bitValue (b : Bool) : ZMod 2 := if b then 1 else 0

def value (r : Row) : ℕ → ZMod 2 := fun i => bitValue (bitAt r i)

@[simp] theorem bitValue_false : bitValue false=0 := rfl
@[simp] theorem bitValue_true : bitValue true=1 := rfl
@[simp] theorem bitValue_xor (a b : Bool) : bitValue (a ^^ b)=bitValue a+bitValue b := by
  cases a <;> cases b <;> decide
@[simp] theorem value_nil : value []=0 := by funext i; simp [value,bitAt,bitValue]

theorem value_xorRows (r s : Row) : value (xorRows r s)=value r+value s := by
  funext i
  exact (congrArg bitValue (at_xorRows r s i)).trans (bitValue_xor _ _)

def pivot (r : Row) : ℕ := r.idxOf true

theorem pivot_lt_iff (r : Row) : pivot r<r.length ↔ true∈r := List.idxOf_lt_length_iff

theorem at_pivot (r : Row) (h : pivot r<r.length) : bitAt r (pivot r)=true := by
  simp only [bitAt,List.getElem?_eq_getElem h,Option.getD_some]
  exact List.getElem_idxOf h

theorem value_eq_zero_of_no_pivot (r : Row) (h : ¬pivot r<r.length) : value r=0 := by
  funext i
  have hn : true∉r := mt (pivot_lt_iff r).mpr h
  cases hr : r[i]? with
  | none => simp [value,bitAt,hr]
  | some b =>
      have hb : b∈r := List.mem_of_getElem? hr
      cases b with
      | false => simp [value,bitAt,hr]
      | true => exact (hn hb).elim

def clear (r : Row) (p : PivotRow) : Row := if bitAt r p.1 then xorRows r p.2 else r

def reduce (bs : BasisRows) (r : Row) : Row := bs.foldl clear r

def addRow (bs : BasisRows) (r : Row) : BasisRows :=
  let s := reduce bs r
  if pivot s<s.length then bs++[(pivot s,s)] else bs

def basis (rs : List Row) : BasisRows := rs.foldl addRow []

def coefficients (bs : BasisRows) (r : Row) : Row :=
  (bs.foldl (fun s p => (clear s.1 p,s.2++[bitAt s.1 p.1])) (r,[])).2

end PlanarHom.SurfaceBooleanRows
