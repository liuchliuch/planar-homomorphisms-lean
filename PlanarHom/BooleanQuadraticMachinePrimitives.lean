import PlanarHom.BooleanQuadraticProgram
import PlanarHom.ListContextFilterMachines
import PlanarHom.ListUnaryLengthMachine
import PlanarHom.ConditionalMachines
import PlanarHom.SelectedStretchMachines

/-! NEW actual typed TM2 primitives for the Boolean coefficient program. -/
namespace PlanarHom.BooleanQuadratic
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives

 theorem fp_getD {A : Type} (ea : BitEncoding A) (d : A) :
    FP (ea.list.prod BitEncoding.nat) ea (fun p=>p.1[p.2]?.getD d) := by
  have hd:=((fp_snd ea.list BitEncoding.nat).pair (fp_fst ea.list BitEncoding.nat)).comp
    (ListDropMachines.fp_drop ea d)
  exact (hd.comp (ListDecompositionMachines.fp_headD ea d)).congr (fun p=>by
    simp only [Function.comp_apply,List.headD_eq_head?_getD,List.head?_drop])

 theorem fp_mapRange {C A : Type} (ec : BitEncoding C) (ea : BitEncoding A)
    (n : C→ℕ) (f : C×ℕ→A)
    (hn : FP ec BitEncoding.unaryNat n)
    (hf : FP (ec.prod BitEncoding.nat) ea f) :
    FP ec ea.list (fun c=>(List.range (n c)).map (fun i=>f (c,i))) := by
  exact (((fp_id ec).pair (hn.comp ZeroOneSharpPMembership.fp_range)).comp
    (ListContextMachines.fp_mapWithContext ec BitEncoding.nat ea _ hf)).congr (fun _=>rfl)

 theorem fp_linearList : FP dataCode BitEncoding.bool.list (fun q=>q.2.1) :=
  (fp_snd BitEncoding.bool (BitEncoding.bool.list.prod BitEncoding.bool.list.list)).comp
    (fp_fst BitEncoding.bool.list BitEncoding.bool.list.list)
 theorem fp_grid : FP dataCode BitEncoding.bool.list.list (fun q=>q.2.2) :=
  (fp_snd BitEncoding.bool (BitEncoding.bool.list.prod BitEncoding.bool.list.list)).comp
    (fp_snd BitEncoding.bool.list BitEncoding.bool.list.list)
 theorem fp_constant : FP dataCode BitEncoding.bool Prod.fst :=
  fp_fst BitEncoding.bool (BitEncoding.bool.list.prod BitEncoding.bool.list.list)
 theorem fp_dimension : FP dataCode BitEncoding.unaryNat dimension :=
  fp_linearList.comp (ListUnaryLengthMachine.fp_length BitEncoding.bool)

 theorem fp_entry {C : Type} (ec : BitEncoding C) (q : C→Data) (i j : C→ℕ)
    (hq : FP ec dataCode q) (hi : FP ec BitEncoding.nat i) (hj : FP ec BitEncoding.nat j) :
    FP ec BitEncoding.bool (fun c=>entry (q c) (i c) (j c)) := by
  have hr:=((hq.comp fp_grid).pair hi).comp (fp_getD BitEncoding.bool.list [])
  exact (hr.pair hj).comp (fp_getD BitEncoding.bool false)

 theorem fp_rawLinear {C : Type} (ec : BitEncoding C) (q : C→Data) (i : C→ℕ)
    (hq : FP ec dataCode q) (hi : FP ec BitEncoding.nat i) :
    FP ec BitEncoding.bool (fun c=>(q c).2.1[i c]?.getD false) :=
  ((hq.comp fp_linearList).pair hi).comp (fp_getD BitEncoding.bool false)

 theorem fp_linear {C : Type} (ec : BitEncoding C) (q : C→Data) (i : C→ℕ)
    (hq : FP ec dataCode q) (hi : FP ec BitEncoding.nat i) :
    FP ec BitEncoding.bool (fun c=>linear (q c) (i c)) :=
  ((fp_rawLinear ec q i hq hi).pair (fp_entry ec q i i hq hi hi)).comp (fp_bool_gate (fun p=>xor p.1 p.2))

 theorem fp_cross {C : Type} (ec : BitEncoding C) (q : C→Data) (i j : C→ℕ)
    (hq : FP ec dataCode q) (hi : FP ec BitEncoding.nat i) (hj : FP ec BitEncoding.nat j) :
    FP ec BitEncoding.bool (fun c=>cross (q c) (i c) (j c)) :=
  ((fp_entry ec q i j hq hi hj).pair (fp_entry ec q j i hq hj hi)).comp (fp_bool_gate (fun p=>xor p.1 p.2))

 theorem fp_keep {C : Type} (ec : BitEncoding C) (i j k : C→ℕ)
    (hi : FP ec BitEncoding.nat i) (hj : FP ec BitEncoding.nat j) (hk : FP ec BitEncoding.nat k) :
    FP ec BitEncoding.bool (fun c=>keep (i c) (j c) (k c)) := by
  have hki:=(hk.pair hi).comp NatListSumMachines.fp_equal
  have hkj:=(hk.pair hj).comp NatListSumMachines.fp_equal
  exact ((hki.pair hkj).comp (fp_bool_gate (fun p=> !(p.1 || p.2)))).congr (fun c=>by
    by_cases hki:k c=i c <;> by_cases hkj:k c=j c <;> simp [keep,hki,hkj])

end PlanarHom.BooleanQuadratic
