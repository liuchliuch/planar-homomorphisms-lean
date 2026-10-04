import PlanarHom.OccurrenceOrientationLogMachines
import PlanarHom.OccurrencePfaffianEvaluationMachines
import PlanarHom.MixedPlanarCode
import PlanarHom.MixedUnaryParallelMachines

/-! NEW reconstruction. Actual occurrence-indexed signed skew-grid construction
from an ordinary mixed graph, orientation toggle log and weight list. Parallel
occurrences are summed separately and every loop cancels. -/
open Classical
namespace PlanarHom.OccurrenceSkewCode
open Complexity PairProjectionMachines MultiGraph MultiGraph.Kasteleyn
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

abbrev Data (K : Type) := MixedCode × (List ℕ × List K)
noncomputable def dataEncoding : BitEncoding (Data K) :=
  MixedCode.encoding.prod (logCode.prod (numberFieldEncoding basis).list)

abbrev Edge := ℕ × (ℕ × ℕ)
def edgeEncoding : BitEncoding Edge := BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)

def signedWeight (p : Data K) (k : ℕ) : K :=
  if logOrientation p.2.1 k then p.2.2.getD k 0 else -p.2.2.getD k 0

 theorem fp_signedWeight : FP ((dataEncoding basis).prod BitEncoding.nat)
    (numberFieldEncoding basis) (fun p => signedWeight p.1 p.2) := by
  let ef := numberFieldEncoding basis
  let et := logCode.prod ef.list
  let ed := dataEncoding basis
  have hd := fp_fst ed BitEncoding.nat
  have hk := fp_snd ed BitEncoding.nat
  have ht := hd.comp (fp_snd MixedCode.encoding et)
  have hl := ht.comp (fp_fst logCode ef.list)
  have hw := ht.comp (fp_snd logCode ef.list)
  have hv := (hw.pair hk).comp (PfaffianList.fp_at ef 0)
  have hn := hv.comp (FixedFieldArithmetic.fp_negation basis)
  have hp := (hl.pair hk).comp fp_logOrientation
  have hp' : FP (ed.prod BitEncoding.nat) BitEncoding.bool
      (fun p => decide (logOrientation p.1.2.1 p.2 = true)) := hp.congr (fun _ => by simp)
  exact (hp'.ite hv hn).congr (fun p => by simp [signedWeight, PfaffianList.lookup, List.getD_eq_getElem?_getD])

def contribution (p : Data K) (u v : ℕ) (q : Edge × ℕ) : K :=
  (if q.1.1 = u then if q.1.2.1 = v then signedWeight p q.2 else 0 else 0) -
  (if q.1.1 = v then if q.1.2.1 = u then signedWeight p q.2 else 0 else 0)

noncomputable def contextEncoding : BitEncoding (Data K × (ℕ × ℕ)) :=
  (dataEncoding basis).prod (BitEncoding.nat.prod BitEncoding.nat)

 theorem fp_contribution :
    FP ((contextEncoding basis).prod (edgeEncoding.prod BitEncoding.nat)) (numberFieldEncoding basis)
      (fun p => contribution p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  let ed := dataEncoding basis
  let en := BitEncoding.nat.prod BitEncoding.nat
  let ei := edgeEncoding.prod BitEncoding.nat
  let ec := contextEncoding basis
  let inp := ec.prod ei
  let ef := numberFieldEncoding basis
  have hc := fp_fst ec ei
  have hq := fp_snd ec ei
  have hd := hc.comp (fp_fst ed en)
  have huv := hc.comp (fp_snd ed en)
  have hu := huv.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hv := huv.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have he := hq.comp (fp_fst edgeEncoding BitEncoding.nat)
  have hk := hq.comp (fp_snd edgeEncoding BitEncoding.nat)
  have hsrc := he.comp (fp_fst BitEncoding.nat en)
  have hdst := (he.comp (fp_snd BitEncoding.nat en)).comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hw := (hd.pair hk).comp (fp_signedWeight basis)
  have hz := fp_const inp ef 0
  have hsu := (hsrc.pair hu).comp PfaffianList.fp_nat_eq
  have hdv := (hdst.pair hv).comp PfaffianList.fp_nat_eq
  have hsv := (hsrc.pair hv).comp PfaffianList.fp_nat_eq
  have hdu := (hdst.pair hu).comp PfaffianList.fp_nat_eq
  have hf := hsu.ite (hdv.ite hw hz) hz
  have hb := hsv.ite (hdu.ite hw hz) hz
  exact (hf.pair hb).comp (FixedFieldArithmetic.fp_subtraction basis)

def gridEntry (p : Data K) (u v : ℕ) : K :=
  (p.1.edges.zipIdx.map (fun q => contribution p u v q)).sum

 theorem fp_gridEntry : FP (contextEncoding basis) (numberFieldEncoding basis)
    (fun p => gridEntry p.1 p.2.1 p.2.2) := by
  let ed := dataEncoding basis
  let en := BitEncoding.nat.prod BitEncoding.nat
  let ef := numberFieldEncoding basis
  have hd := fp_fst ed en
  have hg := hd.comp (fp_fst MixedCode.encoding (logCode.prod ef.list))
  have he := (hg.comp MixedCode.fp_edges).comp (ListIndexMachines.fp_zipIdx edgeEncoding)
  have hm := ((fp_id (contextEncoding basis)).pair he).comp
    (ListContextMachines.fp_mapWithContext (contextEncoding basis)
      (edgeEncoding.prod BitEncoding.nat) ef _ (fp_contribution basis))
  exact hm.comp (MaterializedFieldListMachines.fp_sum basis)

def grid (p : Data K) : PfaffianList.Grid K :=
  (List.range p.1.vertices).map (fun i => (List.range p.1.vertices).map (fun j => gridEntry p i j))

 theorem fp_grid : FP (dataEncoding basis) (PfaffianList.gridEncoding basis) (grid (K := K)) := by
  let ed := dataEncoding basis
  let ef := numberFieldEncoding basis
  let ec := ed.prod BitEncoding.nat
  have hc := fp_fst ec BitEncoding.nat
  have hj := fp_snd ec BitEncoding.nat
  have hd := hc.comp (fp_fst ed BitEncoding.nat)
  have hi := hc.comp (fp_snd ed BitEncoding.nat)
  have he := (hd.pair (hi.pair hj)).comp (fp_gridEntry basis)
  have hg := fp_fst MixedCode.encoding (logCode.prod ef.list)
  have hr := (hg.comp MixedCode.fp_vertices).comp UnaryArithmeticMachines.fp_range
  have hrowRange := (fp_fst ed BitEncoding.nat).comp hr
  have hrow := ((fp_id ec).pair hrowRange).comp
    (ListContextMachines.fp_mapWithContext ec BitEncoding.nat ef _ he)
  exact ((fp_id ed).pair hr).comp
    (ListContextMachines.fp_mapWithContext ed BitEncoding.nat ef.list _ hrow)

/-- Complete ordinary encoded graph-to-signed-evaluator pipeline. -/
 theorem fp_evaluate : FP (dataEncoding basis) (numberFieldEncoding basis)
    (fun p => PfaffianList.evaluateGrid (grid p)) :=
  (fp_grid basis).comp (PfaffianList.fp_evaluateGrid basis)

 theorem gridEntry_swap (p : Data K) (u v : ℕ) : gridEntry p v u = -gridEntry p u v := by
  simp only [gridEntry]
  induction p.1.edges.zipIdx with
  | nil => simp
  | cons q xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    simp only [contribution]
    ring

@[simp] theorem gridEntry_diag (p : Data K) (u : ℕ) : gridEntry p u u = 0 := by
  simp [gridEntry, contribution]


 theorem sum_zipIdx_eq_fin {A : Type} (xs : List A) (f : A × ℕ → K) :
    (xs.zipIdx.map f).sum = ∑ i : Fin xs.length, f (xs.get i,i.val) := by
  have hz := PfaffianList.zipIdx_ofFn (fun i : Fin xs.length => xs[i.val])
  rw [List.ofFn_getElem] at hz
  rw [hz, List.map_ofFn, List.sum_ofFn]
  rfl

 theorem gridEntry_eq_occurrenceSkewMatrix (p : Data K) {bt ut : ℕ}
    (hp : p.1.Valid bt ut) (u v : Fin p.1.vertices) :
    gridEntry p u.val v.val =
      (p.1.toMultiGraph hp).occurrenceSkewMatrix
        (fun e => logOrientation p.2.1 e.val) (fun e => p.2.2.getD e.val 0) u v := by
  rw [gridEntry, sum_zipIdx_eq_fin]
  unfold MultiGraph.occurrenceSkewMatrix
  apply Finset.sum_congr rfl
  intro e he
  simp only [contribution, MultiGraph.occurrenceEntry, MixedCode.toMultiGraph,
    Fin.ext_iff, signedWeight, MultiGraph.orientationSign]
  by_cases ho : logOrientation p.2.1 e.val = true <;>
    by_cases hsu : (p.1.edges.get e).1 = u.val <;>
    by_cases hsv : (p.1.edges.get e).1 = v.val <;>
    by_cases hdu : (p.1.edges.get e).2.1 = u.val <;>
    by_cases hdv : (p.1.edges.get e).2.1 = v.val <;>
    simp_all

 theorem grid_eq_matrixRows (p : Data K) {bt ut : ℕ} (hp : p.1.Valid bt ut) :
    grid p = PfaffianList.matrixRows ((p.1.toMultiGraph hp).occurrenceSkewMatrix
      (fun e => logOrientation p.2.1 e.val) (fun e => p.2.2.getD e.val 0)) := by
  simp only [grid, PfaffianList.matrixRows, List.ofFn_eq_map]
  rw [← List.map_coe_finRange p.1.vertices]
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro u hu
  apply List.map_congr_left
  intro v hv
  exact gridEntry_eq_occurrenceSkewMatrix p hp u v


include basis in
 theorem evaluate_eq_pairingPfaffian (p : Data K) {bt ut : ℕ} (hp : p.1.Valid bt ut) :
    PfaffianList.evaluateGrid (grid p) =
      MultiGraph.pairingPfaffian ((p.1.toMultiGraph hp).occurrenceSkewMatrix
        (fun e => logOrientation p.2.1 e.val) (fun e => p.2.2.getD e.val 0)) := by
  rw [grid_eq_matrixRows p hp]
  exact PfaffianList.evaluateGrid_matrixRows basis _
    ((p.1.toMultiGraph hp).occurrenceSkewMatrix_swap _ _)
    ((p.1.toMultiGraph hp).occurrenceSkewMatrix_diag _ _)

include basis in
 theorem calibrated_evaluation (p : Data K) {bt ut : ℕ} (hp : p.1.Valid bt ut)
    (ho : (p.1.toMultiGraph hp).IsPfaffianOrientation (fun e => logOrientation p.2.1 e.val))
    (M₀ : Finset (Fin p.1.edges.length)) (hM₀ : (p.1.toMultiGraph hp).PerfectMatching M₀) :
    (∑ M : {M : Finset (Fin p.1.edges.length) // (p.1.toMultiGraph hp).PerfectMatching M},
      ∏ e ∈ M.val, p.2.2.getD e.val 0) =
      (p.1.toMultiGraph hp).matchingPfaffianSign (fun e => logOrientation p.2.1 e.val) M₀ *
        PfaffianList.evaluateGrid (grid p) := by
  classical
  rw [evaluate_eq_pairingPfaffian basis p hp]
  exact (p.1.toMultiGraph hp).matchingSum_eq_referenceSign_mul_pairingPfaffian _ ho M₀ hM₀ _

end PlanarHom.OccurrenceSkewCode
