import PlanarHom.BooleanFieldTowerMachines
import PlanarHom.MaterializedFieldListMachines
import PlanarHom.ListMapMachines

/-! Actual dynamic list summation in the fixed-dimensional radical algebra.
The program splits the represented coordinates and invokes proved base-field
list sums, so no unproved iteration-growth premise is introduced. -/
noncomputable section
namespace PlanarHom.BooleanFieldTowerSumMachines
open Complexity PairProjectionMachines BooleanFieldTower BooleanFieldTowerMachines
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}

def sum (n : ℕ) (xs : List (Tower K n)) : Tower K n:=xs.foldr (add n) (zero n)

@[simp] theorem sum_zero (xs : List K) : sum 0 xs=xs.sum := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>simpa [sum,add,zero] using congrArg (fun a=>x+a) ih

@[simp] theorem sum_succ (n : ℕ) (xs : List (Tower K (n+1))) :
    sum (n+1) xs=(sum n (xs.map Prod.fst),sum n (xs.map Prod.snd)) := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    change add (n+1) x (sum (n+1) xs)=_
    rw [ih]
    rfl

theorem fp_sum (basis : Module.Basis (Fin dimension) ℚ K) (n : ℕ) :
    FP (encoding basis n).list (encoding basis n) (sum n) := by
  induction n with
  | zero=>
    exact (MaterializedFieldListMachines.fp_sum basis).congr (fun xs=>(sum_zero xs).symm)
  | succ n ih=>
    have hp:=ListMapMachines.fp_map ((encoding basis n).prod (encoding basis n)) (encoding basis n)
      Prod.fst (fp_fst _ _)
    have hq:=ListMapMachines.fp_map ((encoding basis n).prod (encoding basis n)) (encoding basis n)
      Prod.snd (fp_snd _ _)
    exact ((hp.comp ih).pair (hq.comp ih)).congr (fun xs=>(sum_succ n xs).symm)

theorem fp_add_sum (basis : Module.Basis (Fin dimension) ℚ K) (n : ℕ) :
    FP ((encoding basis n).prod (encoding basis n).list) (encoding basis n)
      (fun p : Tower K n×List (Tower K n)=>add n p.1 (sum n p.2)) :=
  BooleanFieldTowerMachines.fp_add basis _ n _ _ (fp_fst _ _)
    ((fp_snd _ _).comp (fp_sum basis n))

end PlanarHom.BooleanFieldTowerSumMachines
