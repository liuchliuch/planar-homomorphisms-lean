import PlanarHom.RectangularNormNormalization
import Mathlib.Data.Fintype.Quotient

noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularTwinQuotient
variable {X Y : Type}

def rowSetoid (C : Matrix X Y ℝ) : Setoid X := Setoid.ker C
def columnSetoid (C : Matrix X Y ℝ) : Setoid Y := Setoid.ker C.transpose
abbrev Rows (C : Matrix X Y ℝ) := Quotient (rowSetoid C)
abbrev Columns (C : Matrix X Y ℝ) := Quotient (columnSetoid C)

def core (C : Matrix X Y ℝ) : Matrix (Rows C) (Columns C) ℝ := fun r s => C r.out s.out

theorem row_out (C : Matrix X Y ℝ) (x : X) : C (Quotient.mk (rowSetoid C) x).out=C x :=
  Quotient.exact (Quotient.out_eq (Quotient.mk (rowSetoid C) x))
theorem column_out (C : Matrix X Y ℝ) (y : Y) :
    C.transpose (Quotient.mk (columnSetoid C) y).out=C.transpose y :=
  Quotient.exact (Quotient.out_eq (Quotient.mk (columnSetoid C) y))

theorem core_mk_column (C : Matrix X Y ℝ) (r : Rows C) (y : Y) :
    core C r (Quotient.mk (columnSetoid C) y)=C r.out y := congrFun (column_out C y) r.out
theorem core_mk_row (C : Matrix X Y ℝ) (x : X) (s : Columns C) :
    core C (Quotient.mk (rowSetoid C) x) s=C x s.out := congrFun (row_out C x) s.out

theorem core_entry (C : Matrix X Y ℝ) (x : X) (y : Y) :
    core C (Quotient.mk (rowSetoid C) x) (Quotient.mk (columnSetoid C) y)=C x y := by
  rw [core_mk_column]
  exact congrFun (row_out C x) y

theorem core_rows_injective (C : Matrix X Y ℝ) : Function.Injective (core C) := by
  intro r r' he
  have hr : C r.out=C r'.out := by
    funext y
    simpa only [core_mk_column] using congrFun he (Quotient.mk (columnSetoid C) y)
  calc
    r = Quotient.mk (rowSetoid C) r.out := (Quotient.out_eq r).symm
    _ = Quotient.mk (rowSetoid C) r'.out := Quotient.sound hr
    _ = r' := Quotient.out_eq r'

theorem core_columns_injective (C : Matrix X Y ℝ) : Function.Injective (core C).transpose := by
  intro s s' he
  have hs : C.transpose s.out=C.transpose s'.out := by
    funext x
    have h := congrFun he (Quotient.mk (rowSetoid C) x)
    change core C (Quotient.mk (rowSetoid C) x) s=core C (Quotient.mk (rowSetoid C) x) s' at h
    simpa only [core_mk_row] using h
  calc
    s = Quotient.mk (columnSetoid C) s.out := (Quotient.out_eq s).symm
    _ = Quotient.mk (columnSetoid C) s'.out := Quotient.sound hs
    _ = s' := Quotient.out_eq s'

theorem core_positive (C : Matrix X Y ℝ) (hC : ∀ x y,0<C x y) :
    ∀ r s,0<core C r s := fun r s => hC r.out s.out

open RectangularNormNormalization
variable [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

theorem normalized_core_no_proportional_rows (V : Matrix X Y ℝ) (hV : ∀ x y,0<V x y)
    (r r' : Rows (normalized V)) (t : ℝ)
    (h : ∀ s,core (normalized V) r s=t*core (normalized V) r' s) : t=1 ∧ r=r' := by
  have hh : ∀ y,normalized V r.out y=t*normalized V r'.out y := by
    intro y
    simpa only [core_mk_column] using h (Quotient.mk (columnSetoid (normalized V)) y)
  have ht := (normalized_proportional_rows V hV r.out r'.out t hh).1
  refine ⟨ht,core_rows_injective _ (funext (fun s => ?_))⟩
  simpa only [ht,one_mul] using h s

theorem normalized_core_no_proportional_columns (V : Matrix X Y ℝ) (hV : ∀ x y,0<V x y)
    (s s' : Columns (normalized V)) (t : ℝ)
    (h : ∀ r,core (normalized V) r s=t*core (normalized V) r s') : t=1 ∧ s=s' := by
  have hh : ∀ x,normalized V x s.out=t*normalized V x s'.out := by
    intro x
    simpa only [core_mk_row] using h (Quotient.mk (rowSetoid (normalized V)) x)
  have ht := (normalized_proportional_columns V hV s.out s'.out t hh).1
  refine ⟨ht,core_columns_injective _ (funext (fun r => ?_))⟩
  simpa only [ht,one_mul] using h r

theorem original_entry_from_core (V : Matrix X Y ℝ) (hV : ∀ x y,0<V x y) (x : X) (y : Y) :
    V x y=rowNorm V x*columnNorm V y*
      core (normalized V) (Quotient.mk (rowSetoid (normalized V)) x) (Quotient.mk (columnSetoid (normalized V)) y) := by
  rw [core_entry]
  exact reconstruct V hV x y

def rowClassMass (V : Matrix X Y ℝ) (m : ℕ) (r : Rows (normalized V)) : ℝ :=
  ∑ x : {x // Quotient.mk (rowSetoid (normalized V)) x=r},(rowNorm V x.val)^(2*m)
def columnClassMass (V : Matrix X Y ℝ) (m : ℕ) (s : Columns (normalized V)) : ℝ :=
  ∑ y : {y // Quotient.mk (columnSetoid (normalized V)) y=s},(columnNorm V y.val)^(2*m)

theorem rowClassMass_pos (V : Matrix X Y ℝ) (hV : ∀ x y,0<V x y) (m : ℕ)
    (r : Rows (normalized V)) : 0<rowClassMass V m r := by
  letI : Nonempty {x // Quotient.mk (rowSetoid (normalized V)) x=r} := ⟨⟨r.out,Quotient.out_eq r⟩⟩
  exact Finset.sum_pos (fun x _ => pow_pos (rowNorm_pos V hV x.val) _) Finset.univ_nonempty

theorem columnClassMass_pos (V : Matrix X Y ℝ) (hV : ∀ x y,0<V x y) (m : ℕ)
    (s : Columns (normalized V)) : 0<columnClassMass V m s := by
  letI : Nonempty {y // Quotient.mk (columnSetoid (normalized V)) y=s} := ⟨⟨s.out,Quotient.out_eq s⟩⟩
  exact Finset.sum_pos (fun y _ => pow_pos (columnNorm_pos V hV y.val) _) Finset.univ_nonempty

theorem rowClassMass_zero (V : Matrix X Y ℝ) (r : Rows (normalized V)) :
    rowClassMass V 0 r=Fintype.card {x // Quotient.mk (rowSetoid (normalized V)) x=r} := by
  simp [rowClassMass]
theorem columnClassMass_zero (V : Matrix X Y ℝ) (s : Columns (normalized V)) :
    columnClassMass V 0 s=Fintype.card {y // Quotient.mk (columnSetoid (normalized V)) y=s} := by
  simp [columnClassMass]

end PlanarHom.RectangularTwinQuotient
