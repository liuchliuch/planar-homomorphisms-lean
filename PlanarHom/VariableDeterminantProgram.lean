import PlanarHom.OccurrencePfaffianEvaluationMachines
import PlanarHom.BlockPfaffianCalibration
import PlanarHom.NatListSumMachines

/-! NEW: total variable-order determinant code. The order is the outer list
length; absent entries are zero. Both the block matrix and its sign calibration
are materialized by actual polynomial-time list machines. -/
noncomputable section
open Classical
namespace PlanarHom.VariableDeterminant
open Complexity PairProjectionMachines PfaffianList
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

def rows {C A : Type} (size : C → ℕ) (row : C → ℕ → A) (c : C) : List A :=
  (List.range (size c)).map (row c)

theorem fp_rows {C A : Type} (ec : BitEncoding C) (ea : BitEncoding A)
    (size : C → ℕ) (row : C → ℕ → A)
    (hn : FP ec BitEncoding.unaryNat size)
    (hr : FP (ec.prod BitEncoding.nat) ea (fun p => row p.1 p.2)) :
    FP ec ea.list (rows size row) :=
  ((fp_id ec).pair (hn.comp UnaryArithmeticMachines.fp_range)).comp
    (ListContextMachines.fp_mapWithContext ec BitEncoding.nat ea _ hr)

def zeroRow (g : Grid K) : List K := rows List.length (fun _ _ => 0) g
def upperRow (g : Grid K) (i : ℕ) : List K :=
  zeroRow g ++ rows (fun p : Grid K × ℕ => p.1.length)
    (fun p j => entry p.1 p.2 j) (g,i)
def lowerRow (g : Grid K) (j : ℕ) : List K :=
  rows (fun p : Grid K × ℕ => p.1.length)
    (fun p i => -entry p.1 i p.2) (g,j) ++ zeroRow g
def blockGrid (g : Grid K) : Grid K :=
  rows List.length upperRow g ++ rows List.length lowerRow g
def identityGrid (g : Grid K) : Grid K :=
  rows List.length (fun g i => rows (fun p : Grid K × ℕ => p.1.length)
    (fun p j => if p.2 = j then (1:K) else 0) (g,i)) g

def determinant (g : Grid K) : K :=
  evaluateGrid (blockGrid (identityGrid g)) * evaluateGrid (blockGrid g)

theorem fp_blockGrid : FP (gridEncoding basis) (gridEncoding basis) (blockGrid (K := K)) := by
  let eg := gridEncoding basis
  let ef := numberFieldEncoding basis
  let ec := eg.prod BitEncoding.nat
  have hn := ListUnaryLengthMachine.fp_length ef.list
  have hc := fp_fst ec BitEncoding.nat
  have hg := hc.comp (fp_fst eg BitEncoding.nat)
  have hi := hc.comp (fp_snd eg BitEncoding.nat)
  have hj := fp_snd ec BitEncoding.nat
  have hv := (hg.pair (hi.pair hj)).comp (fp_entry basis)
  have hw := ((hg.pair (hj.pair hi)).comp (fp_entry basis)).comp
    (FixedFieldArithmetic.fp_negation basis)
  have hn' := (fp_fst eg BitEncoding.nat).comp hn
  have hrow := fp_rows ec ef (fun p : Grid K × ℕ => p.1.length)
    (fun p j => entry p.1 p.2 j) hn' hv
  have hcol := fp_rows ec ef (fun p : Grid K × ℕ => p.1.length)
    (fun p i => -entry p.1 i p.2) hn' hw
  have hz := fp_rows eg ef List.length (fun _ _ => (0:K)) hn
    (fp_const ec ef 0)
  have hz' := (fp_fst eg BitEncoding.nat).comp hz
  have hu : FP ec ef.list (fun p : Grid K × ℕ => upperRow p.1 p.2) :=
    (hz'.pair hrow).comp (ListMutationMachines.fp_append ef)
  have hl : FP ec ef.list (fun p : Grid K × ℕ => lowerRow p.1 p.2) :=
    (hcol.pair hz').comp (ListMutationMachines.fp_append ef)
  exact ((fp_rows eg ef.list List.length upperRow hn hu).pair
    (fp_rows eg ef.list List.length lowerRow hn hl)).comp
      (ListMutationMachines.fp_append ef.list)

theorem fp_identityGrid : FP (gridEncoding basis) (gridEncoding basis) (identityGrid (K := K)) := by
  let eg := gridEncoding basis
  let ef := numberFieldEncoding basis
  let ec := eg.prod BitEncoding.nat
  have hn := ListUnaryLengthMachine.fp_length ef.list
  have hi := (fp_fst ec BitEncoding.nat).comp (fp_snd eg BitEncoding.nat)
  have hj := fp_snd ec BitEncoding.nat
  have he := (hi.pair hj).comp NatListSumMachines.fp_equal
  have hv := he.ite (fp_const (ec.prod BitEncoding.nat) ef (1:K))
    (fp_const (ec.prod BitEncoding.nat) ef (0:K))
  have hr := fp_rows ec ef (fun p : Grid K × ℕ => p.1.length)
    (fun p j => if p.2 = j then (1:K) else 0)
    ((fp_fst eg BitEncoding.nat).comp hn) hv
  exact fp_rows eg ef.list List.length _ hn hr

/-- The runtime theorem is uniform in the matrix order and total on ragged inputs. -/
theorem fp_determinant : FP (gridEncoding basis) (numberFieldEncoding basis) (determinant (K := K)) :=
  (((fp_identityGrid basis).comp (fp_blockGrid basis)).comp (fp_evaluateGrid basis) |>.pair
    ((fp_blockGrid basis).comp (fp_evaluateGrid basis))).comp
      (FixedFieldArithmetic.fp_multiplication basis)

end PlanarHom.VariableDeterminant
