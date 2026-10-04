import PlanarHom.OccurrencePfaffianListPrimitives
import PlanarHom.SelectedStretchMachines
import PlanarHom.BinaryDivisionMachine
import Mathlib.Algebra.Ring.Parity

/-! NEW reconstruction. A genuine polynomial-time materialized pivot step,
including search, sign, full grid update, active-list deletion and accumulator.
The eventual iteration bound is deliberately not inferred from this one-step
result: intermediate encoded heights require their own mathematical proof. -/

namespace PlanarHom.PfaffianList
open Complexity PairProjectionMachines

 theorem fp_nat_eq : FP (BitEncoding.nat.prod BitEncoding.nat) BitEncoding.bool
    (fun p : ℕ × ℕ => decide (p.1 = p.2)) := by
  exact ((ArithmeticCircuitPrimitives.fp_nat_int.prodMap ArithmeticCircuitPrimitives.fp_nat_int).comp
    RationalCircuits.fp_integer_equality).congr (fun p => by simp)

def eraseIndex {A : Type} (xs : List A) (k : ℕ) : List A :=
  (xs.zipIdx.filter (fun q => decide (q.2 ≠ k))).map Prod.fst

theorem eraseIndex_eq {A : Type} (xs : List A) (k : ℕ) : eraseIndex xs k = xs.eraseIdx k := by
  induction xs generalizing k with
  | nil => simp [eraseIndex]
  | cons a xs ih =>
    cases k with
    | zero =>
      simp [eraseIndex, List.zipIdx_cons, List.zipIdx_succ, List.filter_map,
        List.map_map, Function.comp_def]
    | succ k =>
      simpa [eraseIndex, List.zipIdx_cons, List.zipIdx_succ, List.filter_map,
        List.map_map, Function.comp_def] using congrArg (List.cons a) (ih k)

theorem fp_eraseIndex {A : Type} (e : BitEncoding A) :
    FP (e.list.prod BitEncoding.nat) e.list (fun p => eraseIndex p.1 p.2) := by
  let ei := e.prod BitEncoding.nat
  have hl := fp_fst BitEncoding.nat ei
  have hr := (fp_snd BitEncoding.nat ei).comp (fp_snd e BitEncoding.nat)
  have heq := (hr.pair hl).comp fp_nat_eq
  have hp := heq.comp (ArithmeticCircuitPrimitives.fp_bool_unary BitEncoding.bool Bool.not)
  have hp' : FP (BitEncoding.nat.prod ei) BitEncoding.bool
      (fun p => decide (p.2.2 ≠ p.1)) := hp.congr (fun _ => by simp)
  have hx := (fp_fst e.list BitEncoding.nat).comp (ListIndexMachines.fp_zipIdx e)
  have hk := fp_snd e.list BitEncoding.nat
  have hf := (hk.pair hx).comp (fp_filterContext BitEncoding.nat ei _ hp')
  exact (hf.comp (ListMapMachines.fp_map ei e Prod.fst (fp_fst e BitEncoding.nat))).congr
    (fun p => by simp only [Function.comp_apply, filterContext_eq, eraseIndex])

variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

abbrev SearchContext (K : Type) := Grid K × ℕ
noncomputable def searchEncoding : BitEncoding (SearchContext K) :=
  (gridEncoding basis).prod BitEncoding.nat

/-- Candidates retain both the original vertex and its zero-based tail position. -/
def candidates (g : Grid K) (i : ℕ) (xs : List ℕ) : List (ℕ × ℕ) :=
  xs.zipIdx.filter (fun q => decide (entry g i q.1 ≠ 0))

theorem fp_candidates :
    FP ((searchEncoding basis).prod BitEncoding.nat.list)
      (BitEncoding.nat.prod BitEncoding.nat).list
      (fun p => candidates p.1.1 p.1.2 p.2) := by
  let ec := searchEncoding basis
  let en := BitEncoding.nat.prod BitEncoding.nat
  let ef := numberFieldEncoding basis
  have hc := fp_fst ec en
  have hq := fp_snd ec en
  have hg := hc.comp (fp_fst (gridEncoding basis) BitEncoding.nat)
  have hi := hc.comp (fp_snd (gridEncoding basis) BitEncoding.nat)
  have hj := hq.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hv := (hg.pair (hi.pair hj)).comp (fp_entry basis)
  have he := (hv.pair (fp_const (ec.prod en) ef 0)).comp (FixedFieldArithmetic.fp_equality basis)
  have hn := he.comp (ArithmeticCircuitPrimitives.fp_bool_unary BitEncoding.bool Bool.not)
  have hp : FP (ec.prod en) BitEncoding.bool
      (fun p => decide (entry p.1.1 p.1.2 p.2.1 ≠ 0)) :=
    hn.congr (fun _ => by simp)
  have hz := (fp_snd ec BitEncoding.nat.list).comp (ListIndexMachines.fp_zipIdx BitEncoding.nat)
  exact (((fp_fst ec BitEncoding.nat.list).pair hz).comp
    (fp_filterContext ec en _ hp)).congr (fun p => by
      simp only [Function.comp_apply, filterContext_eq, candidates])

/-- The sign is selected from exact binary remainder, rather than exponentiation. -/
def sign (k : ℕ) : K := if k % 2 = 0 then 1 else -1

theorem sign_eq (k : ℕ) : sign (K := K) k = (-1 : K) ^ k := by
  rw [neg_one_pow_eq_ite]
  simp only [sign, Nat.even_iff]

theorem fp_sign : FP BitEncoding.nat (numberFieldEncoding basis) (sign (K := K)) := by
  have hp := ((fp_id BitEncoding.nat).pair (fp_const BitEncoding.nat BitEncoding.nat 2)).comp
    BinaryArithmetic.fp_division
  have hr := hp.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hz := hr.comp RationalCircuits.fp_nat_isZero
  exact hz.ite (fp_const BitEncoding.nat (numberFieldEncoding basis) 1)
    (fp_const BitEncoding.nat (numberFieldEncoding basis) (-1))

/-- The state contains the whole current matrix, active ambient labels, and the
signed product of the pivots already removed. -/
abbrev State (K : Type) := Grid K × (List ℕ × K)
noncomputable def stateEncoding : BitEncoding (State K) :=
  (gridEncoding basis).prod (BitEncoding.nat.list.prod (numberFieldEncoding basis))

def headVertex (s : State K) : ℕ := s.2.1.headD 0
def tailVertices (s : State K) : List ℕ := s.2.1.tail
def pivotCandidates (s : State K) : List (ℕ × ℕ) := candidates s.1 (headVertex s) (tailVertices s)
def pivotChoice (s : State K) : ℕ × ℕ := (pivotCandidates s).headD (0,0)

def pivotStep (s : State K) : State K :=
  let q := pivotChoice s
  (updateGrid s.1 (headVertex s) q.1,
    (eraseIndex (tailVertices s) q.2,
      s.2.2 * (sign q.2 * entry s.1 (headVertex s) q.1)))

/-- Completed states are fixed; a nonempty zero row terminates with value zero. -/
def step (s : State K) : State K :=
  if s.2.1 = [] then s else
    if pivotCandidates s = [] then (s.1,([],0)) else pivotStep s

 theorem fp_pivotChoice : FP (stateEncoding basis) (BitEncoding.nat.prod BitEncoding.nat)
    (pivotChoice (K := K)) := by
  let eg := gridEncoding basis
  let et := BitEncoding.nat.list.prod (numberFieldEncoding basis)
  have hg := fp_fst eg et
  have ht := fp_snd eg et
  have hx := ht.comp (fp_fst BitEncoding.nat.list (numberFieldEncoding basis))
  have hi := hx.comp (ListDecompositionMachines.fp_headD BitEncoding.nat 0)
  have hs := hx.comp (ListDecompositionMachines.fp_tail BitEncoding.nat 0)
  exact (((hg.pair hi).pair hs).comp (fp_candidates basis)).comp
    (ListDecompositionMachines.fp_headD (BitEncoding.nat.prod BitEncoding.nat) (0,0))

 theorem fp_pivotStep : FP (stateEncoding basis) (stateEncoding basis) (pivotStep (K := K)) := by
  let ef := numberFieldEncoding basis
  let eg := gridEncoding basis
  let et := BitEncoding.nat.list.prod ef
  have hg := fp_fst eg et
  have ht := fp_snd eg et
  have hx := ht.comp (fp_fst BitEncoding.nat.list ef)
  have ha := ht.comp (fp_snd BitEncoding.nat.list ef)
  have hi := hx.comp (ListDecompositionMachines.fp_headD BitEncoding.nat 0)
  have hs := hx.comp (ListDecompositionMachines.fp_tail BitEncoding.nat 0)
  have hq := fp_pivotChoice basis
  have hj := hq.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hk := hq.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hg' := (hg.pair (hi.pair hj)).comp (fp_updateGrid basis)
  have hs' := (hs.pair hk).comp (fp_eraseIndex BitEncoding.nat)
  have hp := (hg.pair (hi.pair hj)).comp (fp_entry basis)
  have hsign := hk.comp (fp_sign basis)
  have hmul := (hsign.pair hp).comp (FixedFieldArithmetic.fp_multiplication basis)
  have ha' := (ha.pair hmul).comp (FixedFieldArithmetic.fp_multiplication basis)
  exact hg'.pair (hs'.pair ha')

 theorem fp_step : FP (stateEncoding basis) (stateEncoding basis) (step (K := K)) := by
  let ef := numberFieldEncoding basis
  let eg := gridEncoding basis
  let et := BitEncoding.nat.list.prod ef
  let es := stateEncoding basis
  let en := BitEncoding.nat.prod BitEncoding.nat
  have hg := fp_fst eg et
  have ht := fp_snd eg et
  have hx := ht.comp (fp_fst BitEncoding.nat.list ef)
  have hi := hx.comp (ListDecompositionMachines.fp_headD BitEncoding.nat 0)
  have hs := hx.comp (ListDecompositionMachines.fp_tail BitEncoding.nat 0)
  have hcs := ((hg.pair hi).pair hs).comp (fp_candidates basis)
  have hz := (hcs.comp (ListCodecMachines.fp_length en)).comp RationalCircuits.fp_nat_isZero
  have hz' : FP es BitEncoding.bool (fun s => decide (pivotCandidates s = [])) :=
    hz.congr (fun s => by simp [pivotCandidates, headVertex, tailVertices])
  have hn := (hx.comp (ListCodecMachines.fp_length BitEncoding.nat)).comp RationalCircuits.fp_nat_isZero
  have hn' : FP es BitEncoding.bool (fun s => decide (s.2.1 = [])) :=
    hn.congr (fun _ => by simp)
  have hzero := hg.pair ((fp_const es BitEncoding.nat.list []).pair (fp_const es ef 0))
  exact hn'.ite (fp_id es) (hz'.ite hzero (fp_pivotStep basis))

end PlanarHom.PfaffianList
