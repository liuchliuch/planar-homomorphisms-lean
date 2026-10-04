import PlanarHom.CoefficientConvolutionAlgebra
import PlanarHom.SyntheticDivisionMachines
import PlanarHom.SelectedStretchMachines

/-! Actual dynamic coefficient convolution. The generic compiler needs only
actual multiplication and sum machines; every loop is a bounded list map, and
no separate output-height premise is assumed. -/
noncomputable section
namespace PlanarHom.CoefficientConvolutionMachines
open Complexity PairProjectionMachines
variable {A C : Type}

/-- Runtime context may contain the radicands of a non-domain radical algebra. -/
def term (zero : A) (mul : C → A → A → A)
    (p : (C × (List A × ℕ)) × (A × ℕ)) : A :=
  if p.1.2.2 < p.2.2 then zero else mul p.1.1 p.2.1 (p.1.2.1[p.1.2.2-p.2.2]?.getD zero)

theorem fp_term (ea : BitEncoding A) (ec : BitEncoding C) (zero : A)
    (mul : C → A → A → A)
    (hmul : FP (ec.prod (ea.prod ea)) ea (fun p => mul p.1 p.2.1 p.2.2)) :
    FP ((ec.prod (ea.list.prod BitEncoding.nat)).prod (ea.prod BitEncoding.nat)) ea
      (term zero mul) := by
  let ei := ea.prod BitEncoding.nat
  let ect := ec.prod (ea.list.prod BitEncoding.nat)
  let ein := ect.prod ei
  have hl := fp_fst ect ei
  have hr := fp_snd ect ei
  have hc := hl.comp (fp_fst ec (ea.list.prod BitEncoding.nat))
  have ht := hl.comp (fp_snd ec (ea.list.prod BitEncoding.nat))
  have hys := ht.comp (fp_fst ea.list BitEncoding.nat)
  have hk := ht.comp (fp_snd ea.list BitEncoding.nat)
  have ha := hr.comp (fp_fst ea BitEncoding.nat)
  have hi := hr.comp (fp_snd ea BitEncoding.nat)
  have hj := (hk.pair hi).comp BinaryArithmetic.fp_subtraction
  have hd := (hj.pair hys).comp (ListDropMachines.fp_drop ea zero)
  have hv := hd.comp (ListDecompositionMachines.fp_headD ea zero)
  have hm := (hc.pair (ha.pair hv)).comp hmul
  have hp := (hk.pair hi).comp BinaryArithmetic.fp_comparison
  apply (hp.ite (fp_const ein ea zero) hm).congr
  intro p
  simp only [term, Function.comp_apply, List.headD_eq_head?_getD, List.head?_drop]

/-- Sum of the products contributing to one selected coefficient. -/
def coefficient (zero : A) (mul : C → A → A → A) (sum : C → List A → A)
    (p : C × ((List A × List A) × ℕ)) : A :=
  sum p.1 (p.2.1.1.zipIdx.map (fun q => term zero mul ((p.1,(p.2.1.2,p.2.2)),q)))

theorem fp_coefficient (ea : BitEncoding A) (ec : BitEncoding C) (zero : A)
    (mul : C → A → A → A) (sum : C → List A → A)
    (hmul : FP (ec.prod (ea.prod ea)) ea (fun p => mul p.1 p.2.1 p.2.2))
    (hsum : FP (ec.prod ea.list) ea (fun p => sum p.1 p.2)) :
    FP (ec.prod ((ea.list.prod ea.list).prod BitEncoding.nat)) ea
      (coefficient zero mul sum) := by
  let els := ea.list.prod ea.list
  let ei := els.prod BitEncoding.nat
  have hc := fp_fst ec ei
  have hr := fp_snd ec ei
  have hls := hr.comp (fp_fst els BitEncoding.nat)
  have hk := hr.comp (fp_snd els BitEncoding.nat)
  have hxs := hls.comp (fp_fst ea.list ea.list)
  have hys := hls.comp (fp_snd ea.list ea.list)
  have hidx := hxs.comp (ListIndexMachines.fp_zipIdx ea)
  have hm := ((hc.pair (hys.pair hk)).pair hidx).comp
    (ListContextMachines.fp_mapWithContext (ec.prod (ea.list.prod BitEncoding.nat))
      (ea.prod BitEncoding.nat) ea (term zero mul) (fp_term ea ec zero mul hmul))
  exact (hc.pair hm).comp hsum

/-- Materialize every coefficient, with one harmless trailing position. -/
def convolution (zero : A) (mul : C → A → A → A) (sum : C → List A → A)
    (p : C × (List A × List A)) : List A :=
  (List.range (p.2.1.length+p.2.2.length+1)).map
    (fun k => coefficient zero mul sum (p.1,(p.2,k)))

theorem fp_convolution (ea : BitEncoding A) (ec : BitEncoding C) (zero : A)
    (mul : C → A → A → A) (sum : C → List A → A)
    (hmul : FP (ec.prod (ea.prod ea)) ea (fun p => mul p.1 p.2.1 p.2.2))
    (hsum : FP (ec.prod ea.list) ea (fun p => sum p.1 p.2)) :
    FP (ec.prod (ea.list.prod ea.list)) ea.list (convolution zero mul sum) := by
  let els := ea.list.prod ea.list
  let ein := ec.prod els
  have hr := fp_snd ec els
  have hx := hr.comp (fp_fst ea.list ea.list)
  have hy := hr.comp (fp_snd ea.list ea.list)
  have hn := ((hx.comp (ListUnaryLengthMachine.fp_length ea)).pair
    (hy.comp (ListUnaryLengthMachine.fp_length ea))).comp UnaryArithmeticMachines.fp_add
  have hrange := (hn.comp UnaryArithmeticMachines.fp_succ).comp UnaryArithmeticMachines.fp_range
  have hctx := fp_fst ein BitEncoding.nat
  have hk := fp_snd ein BitEncoding.nat
  have hc := hctx.comp (fp_fst ec els)
  have hls := hctx.comp (fp_snd ec els)
  have hb := (hc.pair (hls.pair hk)).comp (fp_coefficient ea ec zero mul sum hmul hsum)
  exact ((fp_id ein).pair hrange).comp (ListContextMachines.fp_mapWithContext ein
    BitEncoding.nat ea _ hb)

variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

/-- Complete actual FP coefficient-list multiplication in a fixed number field. -/
theorem fp_fieldConvolution : FP
    ((numberFieldEncoding basis).list.prod (numberFieldEncoding basis).list)
    (numberFieldEncoding basis).list
    (fun p : List K × List K => CoefficientListAlgebra.convolution p.1 p.2) := by
  let e := numberFieldEncoding basis
  let ec := BitEncoding.bool
  have hm : FP (ec.prod (e.prod e)) e
      (fun p : Bool × (K × K) => p.2.1 * p.2.2) :=
    (fp_snd ec (e.prod e)).comp (FixedFieldArithmetic.fp_multiplication basis)
  have hs : FP (ec.prod e.list) e (fun p : Bool × List K => p.2.sum) :=
    (fp_snd ec e.list).comp (MaterializedFieldListMachines.fp_sum basis)
  have hp := (fp_const (e.list.prod e.list) ec false).pair (fp_id (e.list.prod e.list))
  exact (hp.comp (fp_convolution e ec 0 (fun _ a b => a*b) (fun _ xs => xs.sum) hm hs)).congr
    (fun _ => rfl)

end PlanarHom.CoefficientConvolutionMachines
