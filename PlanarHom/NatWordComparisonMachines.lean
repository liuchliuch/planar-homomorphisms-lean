import PlanarHom.PlanarityLRConstraintMachines

/-! NEW reconstruction. Exact dynamically sized natural-word zip, equality and
lexicographic comparison via actual indexed list maps and finite Boolean folds. -/
namespace PlanarHom.NatWordComparisonMachines
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives
abbrev pairCode := BitEncoding.nat.prod BitEncoding.nat
abbrev inputCode := BitEncoding.nat.list.prod BitEncoding.nat.list

 def indexedZip (xs ys : List ℕ) : List (ℕ×ℕ) :=
   (xs.zipIdx.filter (fun q=>decide (q.2<ys.length))).map (fun q=>(q.1,ys.getD q.2 0))

 theorem indexedZip_eq (xs ys : List ℕ) : indexedZip xs ys=xs.zip ys := by
  induction xs generalizing ys with
  | nil => simp [indexedZip]
  | cons a xs ih =>
    cases ys with
    | nil => simp [indexedZip]
    | cons b ys =>
      simpa [indexedZip,List.zipIdx_cons,List.zipIdx_succ,List.filter_map,List.map_map,
        Function.comp_def,List.getD_eq_getElem?_getD] using congrArg (List.cons (a,b)) (ih ys)

 theorem fp_zip : FP inputCode pairCode.list (fun p=>p.1.zip p.2) := by
  let ec:=BitEncoding.nat.list
  have hy:=fp_fst ec pairCode
  have hi:=(fp_snd ec pairCode).comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have ha:=(fp_snd ec pairCode).comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hlen:=hy.comp (ListCodecMachines.fp_length BitEncoding.nat)
  have hvalid:=(hi.pair hlen).comp BinaryArithmetic.fp_comparison
  have hv:=(hy.pair hi).comp (PfaffianList.fp_at BitEncoding.nat 0)
  have hvalue:=ha.pair hv
  have hx:=(fp_fst ec ec).comp (ListIndexMachines.fp_zipIdx BitEncoding.nat)
  have hy₀:=fp_snd ec ec
  have hfiltered:=(hy₀.pair hx).comp
    (ListContextFilterMachines.fp_filterWithContext ec pairCode _ hvalid)
  have hm:=(hy₀.pair hfiltered).comp (ListContextMachines.fp_mapWithContext ec pairCode pairCode _ hvalue)
  exact hm.congr (fun p=>by
    simpa only [Function.comp_apply,PfaffianList.lookup,List.getD_eq_getElem?_getD] using indexedZip_eq p.1 p.2)

 def lexCombine (p : ℕ×ℕ) (rest : Bool) : Bool := decide (p.1<p.2) || ((p.1==p.2) && rest)

 theorem lex_foldr (xs ys : List ℕ) :
    (xs.zip ys).foldr lexCombine (decide (xs.length<ys.length)) = xs.lex ys (fun x y=>decide (x<y)) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [List.lex]
  | cons a xs ih =>
    cases ys with
    | nil => simp [List.lex]
    | cons b ys => simpa [List.lex,lexCombine] using congrArg (lexCombine (a,b)) (ih ys)

 theorem fp_lex : FP inputCode BitEncoding.bool (fun p=>p.1.lex p.2 (fun x y=>decide (x<y))) := by
  have hacc:=fp_fst BitEncoding.bool pairCode
  have hp:=fp_snd BitEncoding.bool pairCode
  have hlt:=hp.comp BinaryArithmetic.fp_comparison
  have heq:=hp.comp PfaffianList.fp_nat_eq
  have heq':=heq.congr (fun p=>show decide (p.2.1=p.2.2)=(p.2.1==p.2.2) from by simp [Bool.beq_eq_decide_eq])
  have hand:=(heq'.pair hacc).comp (fp_bool_gate (fun p=>p.1 && p.2))
  have hbody:=(hlt.pair hand).comp (fp_bool_gate (fun p=>p.1 || p.2))
  have hfold:=ListFoldMachines.fp_foldl pairCode BitEncoding.bool (fun b p=>lexCombine p b) hbody 1
    (fun b xs i hi=>by simp [BitEncoding.bool])
  have hl:=(fp_fst BitEncoding.nat.list BitEncoding.nat.list).comp (ListCodecMachines.fp_length BitEncoding.nat)
  have hr:=(fp_snd BitEncoding.nat.list BitEncoding.nat.list).comp (ListCodecMachines.fp_length BitEncoding.nat)
  have hseed:=(hl.pair hr).comp BinaryArithmetic.fp_comparison
  have hrev:=fp_zip.comp (ListReverseMachines.fp_reverse pairCode)
  exact ((hseed.pair hrev).comp hfold).congr (fun p=>by
    simp only [Function.comp_apply,List.foldl_reverse]
    exact lex_foldr p.1 p.2)

 theorem zip_all_eq (xs ys : List ℕ) :
    ((xs.zip ys).all (fun p=>p.1==p.2) && decide (xs.length=ys.length))=decide (xs=ys) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp
  | cons a xs ih =>
    cases ys with
    | nil => simp
    | cons b ys =>
      simpa [Bool.beq_eq_decide_eq,Bool.and_assoc] using (congrArg (fun z:Bool=>decide (a=b) && z) (ih ys))

 theorem fp_equal : FP inputCode BitEncoding.bool (fun p=>decide (p.1=p.2)) := by
  have hcmp : FP pairCode BitEncoding.bool (fun p=>p.1==p.2) :=
    PfaffianList.fp_nat_eq.congr (fun _=>by simp [Bool.beq_eq_decide_eq])
  have hm:=fp_zip.comp (ListMapMachines.fp_map pairCode BitEncoding.bool _ hcmp)
  have hall:=hm.comp MultiGraph.Kasteleyn.fp_allBool
  have hl:=(fp_fst BitEncoding.nat.list BitEncoding.nat.list).comp (ListCodecMachines.fp_length BitEncoding.nat)
  have hr:=(fp_snd BitEncoding.nat.list BitEncoding.nat.list).comp (ListCodecMachines.fp_length BitEncoding.nat)
  have hlen:=(hl.pair hr).comp PfaffianList.fp_nat_eq
  exact ((hall.pair hlen).comp (fp_bool_gate (fun p=>p.1 && p.2))).congr (fun p=>by
    simpa only [Function.comp_apply,List.all_map,id_eq] using zip_all_eq p.1 p.2)

end PlanarHom.NatWordComparisonMachines
