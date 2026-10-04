import PlanarHom.ZeroOneHomCertificates
import PlanarHom.FiniteRationalCircuits
import PlanarHom.ListDropMachines
import PlanarHom.ListContextMachines
import PlanarHom.UnaryRangeMachines

/-! Fixed finite Boolean circuits and actual dynamic bit lookup for the
homomorphism verifier. The target relation is fixed program data. -/
namespace PlanarHom.ZeroOneSharpPMembership
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives

theorem fp_range : FP BitEncoding.unaryNat BitEncoding.nat.list List.range :=
  (UnaryRangeMachines.fp_range.comp (ListReverseMachines.fp_reverse BitEncoding.nat)).congr (fun n=>by simp)

theorem fp_anyFixed {A I:Type} (ea:BitEncoding A) (s:Finset I) (f:A→I→Bool)
    (hf:∀i,FP ea BitEncoding.bool (fun a=>f a i)) :
    FP ea BitEncoding.bool (fun a=>decide (∃i∈s,f a i=true)) := by
  classical
  induction s using Finset.induction_on with
  | empty=>simpa using fp_const ea BitEncoding.bool false
  | @insert i s hi ih=>
    exact (((hf i).pair ih).comp (fp_bool_gate (fun p=>p.1 || p.2))).congr (fun a=>by simp)

theorem fp_allContext {C A:Type} (ec:BitEncoding C) (ea:BitEncoding A) (f:C×A→Bool)
    (hf:FP (ec.prod ea) BitEncoding.bool f) :
    FP (ec.prod ea.list) BitEncoding.bool (fun p=>p.2.all (fun a=>f (p.1,a))) := by
  exact ((ListContextMachines.fp_mapWithContext ec ea BitEncoding.bool f hf).comp
    MultiGraph.Kasteleyn.fp_allBool).congr (fun p=>by simp [List.all_map,Function.comp_def])

theorem fp_getBit : FP (BitEncoding.bits.prod BitEncoding.nat) BitEncoding.bool (fun p=>getBit p.1 p.2) := by
  have hw:=(fp_fst BitEncoding.bits BitEncoding.nat).comp RawBooleanListMachine.fp_boolList
  have hi:=fp_snd BitEncoding.bits BitEncoding.nat
  have hd:=(hi.pair hw).comp (ListDropMachines.fp_drop BitEncoding.bool false)
  exact (hd.comp (ListDecompositionMachines.fp_headD BitEncoding.bool false)).congr (fun p=>by
    simp only [Function.comp_apply,id_eq,getBit,List.headD_eq_head?_getD,List.head?_drop])

theorem fp_rowMatch (q:ℕ) (c:Fin q) : FP (BitEncoding.bits.prod BitEncoding.nat) BitEncoding.bool
    (fun p=>rowMatch q p.1 p.2 c) := by
  classical
  let ec:=BitEncoding.bits.prod BitEncoding.nat
  have hv:=(fp_const ec BitEncoding.nat q).pair (fp_snd BitEncoding.bits BitEncoding.nat) |>.comp BinaryArithmetic.fp_multiplication
  have hbit (j:Fin q):FP ec BitEncoding.bool (fun p=>getBit p.1 (q*p.2+j.val)) :=
    ((fp_fst BitEncoding.bits BitEncoding.nat).pair
      ((hv.pair (fp_const ec BitEncoding.nat j.val)).comp BinaryArithmetic.fp_addition)).comp fp_getBit
  have hbody (j:Fin q):= ((hbit j).pair (fp_const ec BitEncoding.bool (decide (c=j)))).comp
    (fp_bool_gate (fun p=>p.1==p.2))
  exact (FiniteRationalCircuits.fp_all ec Finset.univ _ hbody).congr (fun p=>by
    simp [rowMatch,Matches,Function.comp_def])

theorem fp_vertexCheck (q:ℕ) : FP (BitEncoding.bits.prod BitEncoding.nat) BitEncoding.bool
    (fun p=>vertexCheck q p.1 p.2) := by
  exact (fp_anyFixed _ Finset.univ (fun p c=>rowMatch q p.1 p.2 c) (fp_rowMatch q)).congr
    (fun p=>by simp [vertexCheck,rowMatch])

theorem fp_edgeCheck (q:ℕ) (R:Relation q) :
    FP (BitEncoding.bits.prod (BitEncoding.nat.prod BitEncoding.nat)) BitEncoding.bool
      (fun p=>edgeCheck q R p.1 p.2) := by
  let ec:=BitEncoding.bits.prod (BitEncoding.nat.prod BitEncoding.nat)
  have hw:=fp_fst BitEncoding.bits (BitEncoding.nat.prod BitEncoding.nat)
  have he:=fp_snd BitEncoding.bits (BitEncoding.nat.prod BitEncoding.nat)
  have hu:=he.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hv:=he.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hpair (c d:Fin q):FP ec BitEncoding.bool
      (fun p=>rowMatch q p.1 p.2.1 c && rowMatch q p.1 p.2.2 d && R c d) := by
    have hm:=(((hw.pair hu).comp (fp_rowMatch q c)).pair ((hw.pair hv).comp (fp_rowMatch q d))).comp
      (fp_bool_gate (fun p=>p.1 && p.2))
    exact (hm.pair (fp_const ec BitEncoding.bool (R c d))).comp (fp_bool_gate (fun p=>p.1 && p.2))
  have hd (c:Fin q):=fp_anyFixed ec Finset.univ _ (hpair c)
  exact (fp_anyFixed ec Finset.univ _ hd).congr (fun p=>by
    simp [edgeCheck,rowMatch,Function.comp_def,Bool.and_eq_true,and_assoc])
end PlanarHom.ZeroOneSharpPMembership
