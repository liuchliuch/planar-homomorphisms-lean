import PlanarHom.RuntimePolynomialEvaluationMachines
import PlanarHom.LinearProductDividedDifference

/-! Actual division-free evaluation of grouped interpolation projectors.
Only a polynomial number of materialized list maps, sums, and products is used.
Runtime algebra operations are supplied as actual FP machines. -/
noncomputable section
namespace PlanarHom.GroupedProjectorValueMachines
open Complexity PairProjectionMachines
variable {A C : Type}

structure Operations (C A : Type) where
  one : A
  sub : A → A → A
  neg : A → A
  mul : C → A → A → A
  inverse : C → A → A
  sum : List A → A
  product : C → A → List A → A

structure Programs (ea : BitEncoding A) (ec : BitEncoding C) (o : Operations C A) : Prop where
  sub : FP (ea.prod ea) ea (fun p => o.sub p.1 p.2)
  neg : FP ea ea o.neg
  mul : FP (ec.prod (ea.prod ea)) ea (fun p => o.mul p.1 p.2.1 p.2.2)
  inverse : FP (ec.prod ea) ea (fun p => o.inverse p.1 p.2)
  sum : FP ea.list ea o.sum
  product : FP (ec.prod (ea.prod ea.list)) ea (fun p => o.product p.1 p.2.1 p.2.2)

variable (ea : BitEncoding A) (ec : BitEncoding C) (o : Operations C A) (h : Programs ea ec o)
include h

def listProduct (p : C × List A) : A := o.product p.1 o.one p.2

theorem fp_listProduct : FP (ec.prod ea.list) ea (listProduct o) := by
  have hc := fp_fst ec ea.list
  have hl := fp_snd ec ea.list
  exact (hc.pair ((fp_const (ec.prod ea.list) ea o.one).pair hl)).comp h.product

def factor (p : (A × (A × ℕ)) × (A × ℕ)) : A :=
  if p.2.2 < p.1.2.2 then o.sub p.1.2.1 p.2.1
  else if p.1.2.2 < p.2.2 then o.sub p.1.1 p.2.1 else o.one

theorem fp_factor : FP ((ea.prod (ea.prod BitEncoding.nat)).prod (ea.prod BitEncoding.nat)) ea
    (factor o) := by
  let ct := ea.prod (ea.prod BitEncoding.nat)
  let it := ea.prod BitEncoding.nat
  let ein := ct.prod it
  have hc := fp_fst ct it
  have hr := fp_snd ct it
  have hz := hc.comp (fp_fst ea (ea.prod BitEncoding.nat))
  have hbj := hc.comp (fp_snd ea (ea.prod BitEncoding.nat))
  have hb := hbj.comp (fp_fst ea BitEncoding.nat)
  have hj := hbj.comp (fp_snd ea BitEncoding.nat)
  have ha := hr.comp (fp_fst ea BitEncoding.nat)
  have hi := hr.comp (fp_snd ea BitEncoding.nat)
  have hl := (hi.pair hj).comp BinaryArithmetic.fp_comparison
  have hg := (hj.pair hi).comp BinaryArithmetic.fp_comparison
  exact hl.ite ((hb.pair ha).comp h.sub)
    (hg.ite ((hz.pair ha).comp h.sub) (fp_const ein ea o.one))

def term (p : C × ((A × A) × (List A × ℕ))) : A :=
  listProduct o (p.1, p.2.2.1.zipIdx.map (fun q => factor o ((p.2.1.1,(p.2.1.2,p.2.2.2)),q)))

theorem fp_term : FP (ec.prod ((ea.prod ea).prod (ea.list.prod BitEncoding.nat))) ea (term o) := by
  let ep := (ea.prod ea).prod (ea.list.prod BitEncoding.nat)
  have hc := fp_fst ec ep
  have ht := fp_snd ec ep
  have hzb := ht.comp (fp_fst (ea.prod ea) (ea.list.prod BitEncoding.nat))
  have hnj := ht.comp (fp_snd (ea.prod ea) (ea.list.prod BitEncoding.nat))
  have hz := hzb.comp (fp_fst ea ea)
  have hb := hzb.comp (fp_snd ea ea)
  have hj := hnj.comp (fp_snd ea.list BitEncoding.nat)
  have hn := (hnj.comp (fp_fst ea.list BitEncoding.nat)).comp (ListIndexMachines.fp_zipIdx ea)
  have hm := ((hz.pair (hb.pair hj)).pair hn).comp
    (ListContextMachines.fp_mapWithContext (ea.prod (ea.prod BitEncoding.nat))
      (ea.prod BitEncoding.nat) ea (factor o) (fp_factor ea ec o h))
  exact (hc.pair hm).comp (fp_listProduct ea ec o h)

def dividedValue (p : C × ((A × A) × List A)) : A :=
  o.sum (p.2.2.zipIdx.map (fun q => term o (p.1,(p.2.1,(p.2.2,q.2)))))

theorem fp_dividedValue : FP (ec.prod ((ea.prod ea).prod ea.list)) ea (dividedValue o) := by
  let ect := ec.prod ((ea.prod ea).prod ea.list)
  let ei := ea.prod BitEncoding.nat
  have hp := fp_fst ect ei
  have hi := (fp_snd ect ei).comp (fp_snd ea BitEncoding.nat)
  have hc := hp.comp (fp_fst ec ((ea.prod ea).prod ea.list))
  have ht := hp.comp (fp_snd ec ((ea.prod ea).prod ea.list))
  have hzb := ht.comp (fp_fst (ea.prod ea) ea.list)
  have hnodes := ht.comp (fp_snd (ea.prod ea) ea.list)
  have hb := (hc.pair (hzb.pair (hnodes.pair hi))).comp (fp_term ea ec o h)
  have hn := ((fp_snd ec ((ea.prod ea).prod ea.list)).comp
    (fp_snd (ea.prod ea) ea.list)).comp (ListIndexMachines.fp_zipIdx ea)
  exact (((fp_id ect).pair hn).comp
    (ListContextMachines.fp_mapWithContext ect ei ea _ hb)).comp h.sum

def rootValue (p : C × (A × List A)) : A :=
  listProduct o (p.1,p.2.2.map (fun a => o.sub p.2.1 a))

theorem fp_rootValue : FP (ec.prod (ea.prod ea.list)) ea (rootValue o) := by
  have hc := fp_fst ec (ea.prod ea.list)
  have hr := fp_snd ec (ea.prod ea.list)
  have hm := hr.comp (ListContextMachines.fp_mapWithContext ea ea ea
    (fun p => o.sub p.1 p.2) h.sub)
  exact (hc.pair hm).comp (fp_listProduct ea ec o h)

def reciprocalValue (p : C × (A × (List A × A))) : A :=
  o.mul p.1 (o.neg (o.inverse p.1 (rootValue o (p.1,(p.2.2.2,p.2.2.1)))))
    (dividedValue o (p.1,((p.2.1,p.2.2.2),p.2.2.1)))

theorem fp_reciprocalValue : FP (ec.prod (ea.prod (ea.list.prod ea))) ea (reciprocalValue o) := by
  let er := ea.prod (ea.list.prod ea)
  have hc := fp_fst ec er
  have ht := fp_snd ec er
  have hz := ht.comp (fp_fst ea (ea.list.prod ea))
  have hnb := ht.comp (fp_snd ea (ea.list.prod ea))
  have hn := hnb.comp (fp_fst ea.list ea)
  have hb := hnb.comp (fp_snd ea.list ea)
  have hroot := (hc.pair (hb.pair hn)).comp (fp_rootValue ea ec o h)
  have hi := ((hc.pair hroot).comp h.inverse).comp h.neg
  have hv := (hc.pair ((hz.pair hb).pair hn)).comp (fp_dividedValue ea ec o h)
  exact (hc.pair (hi.pair hv)).comp h.mul

/-- The two lists are group members and outsiders. No within-group difference
is ever inverted, so repeated nodes remain legal. -/
def projectorValue (p : C × (A × (List A × List A))) : A :=
  o.mul p.1 (rootValue o (p.1,(p.2.1,p.2.2.2)))
    (listProduct o (p.1,p.2.2.2.map (fun b => reciprocalValue o (p.1,(p.2.1,(p.2.2.1,b))))))

theorem fp_projectorValue : FP (ec.prod (ea.prod (ea.list.prod ea.list))) ea (projectorValue o) := by
  let ect := ec.prod (ea.prod ea.list)
  have hp := fp_fst ect ea
  have hb := fp_snd ect ea
  have hc := hp.comp (fp_fst ec (ea.prod ea.list))
  have ht := hp.comp (fp_snd ec (ea.prod ea.list))
  have hz := ht.comp (fp_fst ea ea.list)
  have hn := ht.comp (fp_snd ea ea.list)
  have hf := (hc.pair (hz.pair (hn.pair hb))).comp (fp_reciprocalValue ea ec o h)
  let er := ea.prod (ea.list.prod ea.list)
  have hc' := fp_fst ec er
  have ht' := fp_snd ec er
  have hz' := ht'.comp (fp_fst ea (ea.list.prod ea.list))
  have hls := ht'.comp (fp_snd ea (ea.list.prod ea.list))
  have hin := hls.comp (fp_fst ea.list ea.list)
  have hout := hls.comp (fp_snd ea.list ea.list)
  have hm := ((hc'.pair (hz'.pair hin)).pair hout).comp
    (ListContextMachines.fp_mapWithContext ect ea ea _ hf)
  have hprod := (hc'.pair hm).comp (fp_listProduct ea ec o h)
  have hroot := (hc'.pair (hz'.pair hout)).comp (fp_rootValue ea ec o h)
  exact (hc'.pair (hroot.pair hprod)).comp h.mul

end PlanarHom.GroupedProjectorValueMachines
