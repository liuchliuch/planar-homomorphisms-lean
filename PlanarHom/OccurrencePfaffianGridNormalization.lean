import PlanarHom.OccurrencePfaffianListStep
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.List.OfFn

/-! NEW reconstruction. A real total FP adapter to square alternating grids.
It preserves all intended skew, zero-diagonal matrix inputs exactly. -/
namespace PlanarHom.PfaffianList
open Complexity PairProjectionMachines
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

def skewEntry (g : Grid K) (i j : ℕ) : K :=
  if i < j then entry g i j else if j < i then -entry g j i else 0

def normalizeGrid (g : Grid K) : Grid K :=
  (List.range g.length).map (fun i => (List.range g.length).map (fun j => skewEntry g i j))

 theorem fp_skewEntry :
    FP ((gridEncoding basis).prod (BitEncoding.nat.prod BitEncoding.nat))
      (numberFieldEncoding basis) (fun p => skewEntry p.1 p.2.1 p.2.2) := by
  let eg := gridEncoding basis
  let en := BitEncoding.nat.prod BitEncoding.nat
  let ei := eg.prod en
  have hg := fp_fst eg en
  have hij := fp_snd eg en
  have hi := hij.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hj := hij.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hf := hij.comp BinaryArithmetic.fp_comparison
  have hb := (hj.pair hi).comp BinaryArithmetic.fp_comparison
  have hvalue := fp_entry basis
  have hrev := ((hg.pair (hj.pair hi)).comp (fp_entry basis)).comp
    (FixedFieldArithmetic.fp_negation basis)
  exact hf.ite hvalue (hb.ite hrev (fp_const ei (numberFieldEncoding basis) 0))

 theorem fp_normalizeGrid : FP (gridEncoding basis) (gridEncoding basis) (normalizeGrid (K := K)) := by
  let eg := gridEncoding basis
  let ef := numberFieldEncoding basis
  let ec := eg.prod BitEncoding.nat
  have hc := fp_fst ec BitEncoding.nat
  have hj := fp_snd ec BitEncoding.nat
  have hg := hc.comp (fp_fst eg BitEncoding.nat)
  have hi := hc.comp (fp_snd eg BitEncoding.nat)
  have he := (hg.pair (hi.pair hj)).comp (fp_skewEntry basis)
  have hrange := (ListUnaryLengthMachine.fp_length ef.list).comp UnaryArithmeticMachines.fp_range
  have hrg := (fp_fst eg BitEncoding.nat).comp hrange
  have hrow := ((fp_id ec).pair hrg).comp
    (ListContextMachines.fp_mapWithContext ec BitEncoding.nat ef _ he)
  exact ((fp_id eg).pair hrange).comp
    (ListContextMachines.fp_mapWithContext eg BitEncoding.nat ef.list _ hrow)

@[simp] theorem normalizeGrid_length (g : Grid K) : (normalizeGrid g).length = g.length := by
  simp [normalizeGrid]

 theorem skewEntry_swap (g : Grid K) (i j : ℕ) : skewEntry g j i = -skewEntry g i j := by
  unfold skewEntry
  rcases lt_trichotomy i j with h | h | h
  · simp [h, not_lt_of_ge h.le]
  · subst j; simp
  · simp [h, not_lt_of_ge h.le]

@[simp] theorem skewEntry_diag (g : Grid K) (i : ℕ) : skewEntry g i i = 0 := by
  simp [skewEntry]

end PlanarHom.PfaffianList
