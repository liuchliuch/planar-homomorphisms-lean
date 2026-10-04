import PlanarHom.DependentMonomialMachines
import PlanarHom.SourceInterpolationWeights

/-! Fixed-source interpolation weights are embedded and aggregated in the parameter's target field. -/
noncomputable section
namespace PlanarHom.DependentTargetAggregation
open Complexity PairProjectionMachines
open scoped BigOperators
variable {L X : Type} [Field L] [Algebra ℚ L] [DecidableEq L]
variable {sourceDimension : ℕ} (sourceBasis : Module.Basis (Fin sourceDimension) ℚ L)
variable (ex : BitEncoding X) (K : X → Type) [∀ x, Field (K x)] [∀ x, Algebra ℚ (K x)]
variable (dimension : X → ℕ) (basis : ∀ x, Module.Basis (Fin (dimension x)) ℚ (K x))
variable (inclusion : ∀ x, L →+* K x) {t : ℕ} (B : ∀ x, Fin t → K x)

abbrev Input (L X : Type) := (X × ℕ) × List (L × List ℕ)

def rowValue (p : (X × ℕ) × (L × List ℕ)) : Σ x, K x :=
  ⟨p.1.1,inclusion p.1.1 p.2.1 * ∏ i, B p.1.1 i ^ min p.1.2 (p.2.2.getD i.val 0)⟩

def aggregate (p : Input L X) : Σ x, K x :=
  ⟨p.1.1,(p.2.map (fun row => inclusion p.1.1 row.1 *
    ∏ i, B p.1.1 i ^ min p.1.2 (row.2.getD i.val 0))).sum⟩

variable (c : ℕ) (hc : ∀ x, dimension x ≤ c)
variable (hpresentation : FP ex BitEncoding.rat.list
  (fun x => UniformFieldPresentationHeights.presentationList (basis x)))
variable (hmul : FP (DependentFieldCodecs.pair ex (DependentFieldListMachines.fieldEncoding K dimension basis)) (DependentFieldCodecs.sigma ex (DependentFieldListMachines.fieldEncoding K dimension basis)) (fun s : Σ x, K x × K x => ⟨s.1,s.2.1*s.2.2⟩))
variable (hadd : FP (DependentFieldCodecs.pair ex (DependentFieldListMachines.fieldEncoding K dimension basis)) (DependentFieldCodecs.sigma ex (DependentFieldListMachines.fieldEncoding K dimension basis)) (fun s : Σ x, K x × K x => ⟨s.1,s.2.1+s.2.2⟩))
variable (hinclusion : FP (ex.prod (numberFieldEncoding sourceBasis)) (DependentFieldCodecs.sigma ex (DependentFieldListMachines.fieldEncoding K dimension basis))
  (fun p => ⟨p.1,inclusion p.1 p.2⟩))
variable (hB : FP ex (DependentFieldCodecs.sigma ex (fun x => ((DependentFieldListMachines.fieldEncoding K dimension basis) x).vector t)) (fun x => ⟨x,B x⟩))

include hinclusion in
theorem fp_one : FP ex (DependentFieldCodecs.sigma ex (DependentFieldListMachines.fieldEncoding K dimension basis)) (fun x => ⟨x,1⟩) :=
  (((fp_id ex).pair (fp_const ex (numberFieldEncoding sourceBasis) 1)).comp hinclusion).congr
    (fun x => by simp)

include hinclusion in
theorem fp_zero : FP ex (DependentFieldCodecs.sigma ex (DependentFieldListMachines.fieldEncoding K dimension basis)) (fun x => ⟨x,0⟩) :=
  (((fp_id ex).pair (fp_const ex (numberFieldEncoding sourceBasis) 0)).comp hinclusion).congr
    (fun x => by simp)

include hc hpresentation hmul hinclusion hB in
theorem fp_rowValue : FP ((ex.prod BitEncoding.unaryNat).prod (SourceExponentRepresentatives.rowEncoding sourceBasis)) (DependentFieldCodecs.sigma ex (DependentFieldListMachines.fieldEncoding K dimension basis)) (rowValue K inclusion B) := by
  have hp := fp_fst (ex.prod BitEncoding.unaryNat) (SourceExponentRepresentatives.rowEncoding sourceBasis)
  have hx := hp.comp (fp_fst ex BitEncoding.unaryNat)
  have hm := hp.comp (fp_snd ex BitEncoding.unaryNat)
  have hr := fp_snd (ex.prod BitEncoding.unaryNat) (SourceExponentRepresentatives.rowEncoding sourceBasis)
  have hw := hr.comp (fp_fst (numberFieldEncoding sourceBasis) BitEncoding.nat.list)
  have hv := hr.comp (fp_snd (numberFieldEncoding sourceBasis) BitEncoding.nat.list)
  have hη := DependentMonomialMachines.fp_monomial ex K dimension basis ((ex.prod BitEncoding.unaryNat).prod (SourceExponentRepresentatives.rowEncoding sourceBasis))
    (fun p => p.1.1) c hc hpresentation hmul (fp_one sourceBasis ex K dimension basis inclusion hinclusion)
    (fun p => B p.1.1) (fun p => p.1.2) (fun p => p.2.2) (hx.comp hB) hm hv
  exact (DependentEncodingMachines.fp_pair ex (DependentFieldListMachines.fieldEncoding K dimension basis) (DependentFieldListMachines.fieldEncoding K dimension basis) ((hx.pair hw).comp hinclusion) hη).comp hmul

/- Actual context map, same-parameter collection, and a uniform dependent sum.
The input rows may be arbitrary; weak-vector validity appears only in semantics. -/
include hc hpresentation hmul hadd hinclusion hB in
theorem fp_aggregate : FP ((ex.prod BitEncoding.unaryNat).prod (SourceExponentRepresentatives.rowEncoding sourceBasis).list) (DependentFieldCodecs.sigma ex (DependentFieldListMachines.fieldEncoding K dimension basis)) (aggregate K inclusion B) := by
  have hp := fp_fst (ex.prod BitEncoding.unaryNat) (SourceExponentRepresentatives.rowEncoding sourceBasis).list
  have hx := hp.comp (fp_fst ex BitEncoding.unaryNat)
  have hrows := ListContextMachines.fp_mapWithContext (ex.prod BitEncoding.unaryNat) (SourceExponentRepresentatives.rowEncoding sourceBasis) (DependentFieldCodecs.sigma ex (DependentFieldListMachines.fieldEncoding K dimension basis)) (rowValue K inclusion B)
    (fp_rowValue sourceBasis ex K dimension basis inclusion B c hc hpresentation hmul hinclusion hB)
  let terms (p : Input L X) : List (K p.1.1) := p.2.map (fun row => inclusion p.1.1 row.1 *
    ∏ i, B p.1.1 i ^ min p.1.2 (row.2.getD i.val 0))
  have hrows' : FP ((ex.prod BitEncoding.unaryNat).prod (SourceExponentRepresentatives.rowEncoding sourceBasis).list)
      (DependentFieldCodecs.sigma ex (DependentFieldListMachines.fieldEncoding K dimension basis)).list
      (fun p => (terms p).map (fun a => (⟨p.1.1,a⟩ : Σ x, K x))) :=
    hrows.congr (fun p => by simp [terms, rowValue, List.map_map])
  have hcollect := DependentEncodingMachines.fp_collect ex (DependentFieldListMachines.fieldEncoding K dimension basis) hx hrows' 
  have hzero := hx.comp (fp_zero sourceBasis ex K dimension basis inclusion hinclusion)
  have hinput := DependentEncodingMachines.fp_pair ex (DependentFieldListMachines.fieldEncoding K dimension basis) (fun x => ((DependentFieldListMachines.fieldEncoding K dimension basis) x).list) hzero hcollect
  exact (hinput.comp (DependentFieldListMachines.fp_fold_sum ex K dimension basis c hc hpresentation hadd)).congr
    (fun p => by simp [aggregate, rowValue, terms])

/- Recovery keeps all interpolation arithmetic and all source answer words in L. -/
def recover (p : (X × ℕ) × (List (L × List ℕ) × List L)) : Σ x, K x :=
  aggregate K inclusion B (p.1, SourceInterpolationWeights.weightedRows p.2.1 p.2.2)

include hc hpresentation hmul hadd hinclusion hB in
theorem fp_recover : FP ((ex.prod BitEncoding.unaryNat).prod (SourceInterpolationWeights.inputEncoding sourceBasis)) (DependentFieldCodecs.sigma ex (DependentFieldListMachines.fieldEncoding K dimension basis))
    (recover K inclusion B) := by
  have hp := fp_fst (ex.prod BitEncoding.unaryNat) (SourceInterpolationWeights.inputEncoding sourceBasis)
  have hw := (fp_snd (ex.prod BitEncoding.unaryNat) (SourceInterpolationWeights.inputEncoding sourceBasis)).comp
    (SourceInterpolationWeights.fp_weightedRows sourceBasis)
  exact (hp.pair hw).comp (fp_aggregate sourceBasis ex K dimension basis inclusion B c hc hpresentation hmul hadd hinclusion hB)

/- Dropping the parameter frame is an explicit actual output conversion. -/
include hc hpresentation hmul hadd hinclusion hB in
theorem fp_recover_payload : FP ((ex.prod BitEncoding.unaryNat).prod (SourceInterpolationWeights.inputEncoding sourceBasis)) BitEncoding.bits
    (fun p => ((DependentFieldListMachines.fieldEncoding K dimension basis) p.1.1).encode ((recover K inclusion B p).2)) :=
  (fp_recover sourceBasis ex K dimension basis inclusion B c hc hpresentation hmul hadd hinclusion hB).comp
    (DependentEncodingMachines.fp_payload ex (DependentFieldListMachines.fieldEncoding K dimension basis))

theorem aggregate_eq (x : X) (m : ℕ) (rows : List (L × List ℕ))
    (hrows : ∀ row ∈ rows, row.2 ∈ ExponentVectors.weak t m) :
    aggregate K inclusion B ((x,m),rows) =
      ⟨x,(rows.map (fun row => inclusion x row.1 * ExponentProductSemantics.value (B x) row.2)).sum⟩ := by
  unfold aggregate
  congr 1
  congr 1
  apply List.map_congr_left
  intro row hr
  rw [DependentMonomialMachines.clipped_eq (B x) m row.2 (hrows row hr)]

end PlanarHom.DependentTargetAggregation
