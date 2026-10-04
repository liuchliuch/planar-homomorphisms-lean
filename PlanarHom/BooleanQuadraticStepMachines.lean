import PlanarHom.BooleanQuadraticMachinePrimitives

/-! NEW actual coefficient-update and pivot-search TM2 compositions. -/
namespace PlanarHom.BooleanQuadratic
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives

 theorem fp_xor {C : Type} {ec : BitEncoding C} {a b : C→Bool}
    (ha : FP ec BitEncoding.bool a) (hb : FP ec BitEncoding.bool b) :
    FP ec BitEncoding.bool (fun c=>xor (a c) (b c)) :=
  (ha.pair hb).comp (fp_bool_gate (fun p=>xor p.1 p.2))
 theorem fp_and {C : Type} {ec : BitEncoding C} {a b : C→Bool}
    (ha : FP ec BitEncoding.bool a) (hb : FP ec BitEncoding.bool b) :
    FP ec BitEncoding.bool (fun c=>a c && b c) :=
  (ha.pair hb).comp (fp_bool_gate (fun p=>p.1 && p.2))

 theorem fp_pivot {C : Type} (ec : BitEncoding C) (q : C→Data) (i j : C→ℕ)
    (hq : FP ec dataCode q) (hi : FP ec BitEncoding.nat i) (hj : FP ec BitEncoding.nat j) :
    FP ec dataCode (fun c=>pivot (q c) (i c) (j c)) := by
  have hn:=hq.comp fp_dimension
  have hconstant:=fp_xor (hq.comp fp_constant)
    (fp_and (fp_linear ec q i hq hi) (fp_linear ec q j hq hj))
  let ek:=ec.prod BitEncoding.nat
  have hc:=fp_fst ec BitEncoding.nat
  have hk:=fp_snd ec BitEncoding.nat
  have hqk:=hc.comp hq
  have hik:=hc.comp hi
  have hjk:=hc.comp hj
  have hkeep:=fp_keep ek _ _ _ hik hjk hk
  have hl:=fp_and hkeep (fp_xor (fp_rawLinear ek _ _ hqk hk)
    (fp_xor (fp_and (fp_linear ek _ _ hqk hik) (fp_cross ek _ _ _ hqk hjk hk))
      (fp_and (fp_linear ek _ _ hqk hjk) (fp_cross ek _ _ _ hqk hik hk))))
  have hline:=fp_mapRange ec BitEncoding.bool _ _ hn hl
  let el:=ek.prod BitEncoding.nat
  have hp:=fp_fst ek BitEncoding.nat
  have hll:=fp_snd ek BitEncoding.nat
  have hql:=hp.comp hqk
  have hil:=hp.comp hik
  have hjl:=hp.comp hjk
  have hkl:=hp.comp hk
  have hentry:=fp_and (fp_and (hp.comp hkeep) (fp_keep el _ _ _ hil hjl hll))
    (fp_xor (fp_entry el _ _ _ hql hkl hll)
      (fp_and (fp_cross el _ _ _ hql hil hkl) (fp_cross el _ _ _ hql hjl hll)))
  have hrow:=fp_mapRange ek BitEncoding.bool _ _ (hc.comp hn) hentry
  have hgrid:=fp_mapRange ec BitEncoding.bool.list _ _ hn hrow
  exact hconstant.pair (hline.pair hgrid)

 theorem fp_remove {C : Type} (ec : BitEncoding C) (q : C→Data) (i : C→ℕ)
    (hq : FP ec dataCode q) (hi : FP ec BitEncoding.nat i) :
    FP ec dataCode (fun c=>remove (q c) (i c)) := by
  have hn:=hq.comp fp_dimension
  let ek:=ec.prod BitEncoding.nat
  have hc:=fp_fst ec BitEncoding.nat
  have hk:=fp_snd ec BitEncoding.nat
  have hqk:=hc.comp hq
  have hik:=hc.comp hi
  have hkeep:=fp_keep ek _ _ _ hik hik hk
  have hl:=fp_and hkeep (fp_rawLinear ek _ _ hqk hk)
  have hline:=fp_mapRange ec BitEncoding.bool _ _ hn hl
  let el:=ek.prod BitEncoding.nat
  have hp:=fp_fst ek BitEncoding.nat
  have hll:=fp_snd ek BitEncoding.nat
  have hil:=hp.comp hik
  have hkkeep:=hp.comp hkeep
  have hlkeep:=fp_keep el _ _ _ hil hil hll
  have hentry:=fp_and (fp_and hkkeep hlkeep) (fp_entry el _ _ _ (hp.comp hqk) (hp.comp hk) hll)
  have hrow:=fp_mapRange ek BitEncoding.bool _ _ (hc.comp hn) hentry
  have hgrid:=fp_mapRange ec BitEncoding.bool.list _ _ hn hrow
  exact ((hq.comp fp_constant).pair (hline.pair hgrid)).congr (fun c=>by
    simp only [remove,keep]
    congr 2 <;> apply List.map_congr_left <;> intro k hk
    · simp
    · apply List.map_congr_left
      intro l hl
      cases hki:(k==i c) <;> cases hli:(l==i c) <;> simp [hki,hli])

 theorem fp_candidates : FP (dataCode.prod BitEncoding.nat) BitEncoding.nat.list
    (fun p=>(List.range (dimension p.1)).filter (fun j=>decide (p.2<j) && cross p.1 p.2 j)) := by
  let ec:=dataCode.prod BitEncoding.nat
  have hq:=fp_fst dataCode BitEncoding.nat
  have hi:=fp_snd dataCode BitEncoding.nat
  have hc:=fp_fst ec BitEncoding.nat
  have hj:=fp_snd ec BitEncoding.nat
  have hlt:=((hc.comp hi).pair hj).comp BinaryArithmetic.fp_comparison
  have ht:=fp_and hlt (fp_cross (ec.prod BitEncoding.nat) _ _ _ (hc.comp hq) (hc.comp hi) hj)
  exact (((fp_id ec).pair ((hq.comp fp_dimension).comp ZeroOneSharpPMembership.fp_range)).comp
    (ListContextFilterMachines.fp_filterWithContext ec BitEncoding.nat _ ht)).congr (fun _=>rfl)

 theorem find_eq_filter_head {A : Type} (p : A→Bool) (xs : List A) :
    xs.find? p=(xs.filter p).head? := by
  induction xs with
  | nil=>rfl
  | cons a xs ih=>cases h:p a <;> simp only [List.find?,List.filter,h,Bool.false_eq_true,if_false,if_true,List.head?_cons,ih]

 theorem fp_step : FP (stateCode.prod BitEncoding.nat) stateCode (fun p=>step p.1 p.2) := by
  let ec:=stateCode.prod BitEncoding.nat
  have hs:=fp_fst stateCode BitEncoding.nat
  have hi:=fp_snd stateCode BitEncoding.nat
  have hq:=hs.comp (fp_fst dataCode (BitEncoding.unaryNat.prod BitEncoding.bool))
  have hm:=hs.comp (fp_snd dataCode (BitEncoding.unaryNat.prod BitEncoding.bool))
  have hn:=hm.comp (fp_fst BitEncoding.unaryNat BitEncoding.bool)
  have hz:=hm.comp (fp_snd BitEncoding.unaryNat BitEncoding.bool)
  have hc:=(hq.pair hi).comp fp_candidates
  have hj:=hc.comp (ListDecompositionMachines.fp_headD BitEncoding.nat 0)
  have hnonempty:=((fp_const ec BitEncoding.nat 0).pair
    (hc.comp (ListCodecMachines.fp_length BitEncoding.nat))).comp BinaryArithmetic.fp_comparison
  have hp:=(fp_pivot ec _ _ _ hq hi hj).pair ((hn.comp UnaryArithmeticMachines.fp_succ).pair hz)
  have hb:=(hz.pair (fp_linear ec _ _ hq hi)).comp (fp_bool_gate (fun p=>p.1 || p.2))
  have hr:=(fp_remove ec _ _ hq hi).pair (hn.pair hb)
  exact ((hnonempty.pair (hp.pair hr)).comp (ConditionalMachines.fp_select stateCode)).congr (fun p=>by
    simp only [Function.comp_apply,step,partner,find_eq_filter_head]
    cases h:((List.range (dimension p.1.1)).filter (fun j=>decide (p.2<j) && cross p.1.1 p.2 j)) with
    | nil=>simp only [h,List.length_nil,lt_self_iff_false,decide_false,Bool.false_eq_true,ite_false,List.head?_nil]
    | cons j js=>simp only [h,List.length_cons,Nat.zero_lt_succ,decide_true,ite_true,List.headD_cons,List.head?_cons])

 theorem fp_xorList : FP BitEncoding.bool.list BitEncoding.bool xorList := by
  have hf:=ListFoldMachines.fp_foldl BitEncoding.bool BitEncoding.bool xor
    (fp_bool_gate (fun p=>xor p.1 p.2)) (Polynomial.C 1) (by
      intro z xs i hi
      simp [BitEncoding.bool])
  exact (((fp_const BitEncoding.bool.list BitEncoding.bool false).pair
    (fp_id BitEncoding.bool.list)).comp hf).congr (fun _=>rfl)

end PlanarHom.BooleanQuadratic
