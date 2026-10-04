import PlanarHom.PlanarityLRDirectMachines

/-! NEW reconstruction. Exact dynamically bounded prefixes and takeWhile by
an indexed filter and the first failed test, with concrete encoded programs. -/
namespace PlanarHom.ListPrefixMachines
open Complexity PairProjectionMachines
variable {A C : Type}

 def indexedTake (xs : List A) (k : ℕ) :=
   (xs.zipIdx.filter (fun q=>decide (q.2<k))).map Prod.fst

 theorem indexedTake_eq (xs : List A) (k : ℕ) : indexedTake xs k=xs.take k := by
  induction xs generalizing k with
  | nil => simp [indexedTake]
  | cons a xs ih =>
    cases k with
    | zero => simp [indexedTake]
    | succ k =>
      simpa [indexedTake,List.zipIdx_cons,List.zipIdx_succ,List.filter_map,List.map_map,
        Function.comp_def] using congrArg (List.cons a) (ih k)

 theorem fp_take (ea : BitEncoding A) :
    FP (ea.list.prod BitEncoding.nat) ea.list (fun p=>p.1.take p.2) := by
  let ep:=ea.prod BitEncoding.nat
  have hk:=fp_fst BitEncoding.nat ep
  have hi:=(fp_snd BitEncoding.nat ep).comp (fp_snd ea BitEncoding.nat)
  have hp:=(hi.pair hk).comp BinaryArithmetic.fp_comparison
  have hx:=(fp_fst ea.list BitEncoding.nat).comp (ListIndexMachines.fp_zipIdx ea)
  have hk₀:=fp_snd ea.list BitEncoding.nat
  have hf:=(hk₀.pair hx).comp (ListContextFilterMachines.fp_filterWithContext BitEncoding.nat ep _ hp)
  exact (hf.comp (ListMapMachines.fp_map ep ea Prod.fst (fp_fst ea BitEncoding.nat))).congr
    (fun p=>indexedTake_eq p.1 p.2)

 theorem take_first_false (xs : List A) (p : A→Bool) :
    xs.take ((xs.map p).idxOf false)=xs.takeWhile p := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    cases hp:p a <;> simp [hp,List.idxOf_cons,ih]

 theorem fp_takeWhileWithContext (ec : BitEncoding C) (ea : BitEncoding A) (p : C→A→Bool)
    (hp : FP (ec.prod ea) BitEncoding.bool (fun q=>p q.1 q.2)) :
    FP (ec.prod ea.list) ea.list (fun q=>q.2.takeWhile (p q.1)) := by
  have hm:=ListContextMachines.fp_mapWithContext ec ea BitEncoding.bool (fun q=>p q.1 q.2) hp
  have heq:=ArithmeticCircuitPrimitives.fp_bool_gate (fun q:Bool×Bool=>decide (q.1=q.2))
  have hk:=((fp_const (ec.prod ea.list) BitEncoding.bool false).pair hm).comp
    (DynamicListIndexMachines.fp_index BitEncoding.bool heq)
  exact (((fp_snd ec ea.list).pair hk).comp (fp_take ea)).congr
    (fun q=>take_first_false q.2 (p q.1))

end PlanarHom.ListPrefixMachines
