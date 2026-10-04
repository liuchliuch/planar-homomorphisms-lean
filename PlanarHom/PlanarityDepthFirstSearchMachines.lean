import PlanarHom.PlanarityDepthFirstSearchStepMachines
import PlanarHom.PlanarityDepthFirstSearchRuntimeBounds
import PlanarHom.RestrictedIterationMachine

/-! NEW reconstruction. The complete occurrence-preserving DFS and its dynamic
metadata accessors are genuine polynomial-time TM2 programs on ordinary graph
codes. All loops use proved full-state encoded bounds. -/
noncomputable section
namespace PlanarHom.PlanarityDepthFirstSearch
open Complexity PairProjectionMachines MachineComposition Polynomial

def loopStep (p : MixedCode × State) : MixedCode × State := (p.1,step p.1 p.2)
def loopCode := MixedCode.encoding.prod stateCode

 theorem loopStep_iterate (g : MixedCode) (s : State) (n : ℕ) :
    loopStep^[n] (g,s)=(g,(step g)^[n] s) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply',ih,loopStep]

 theorem fp_loopStep : FP loopCode loopCode loopStep :=
  (fp_fst MixedCode.encoding stateCode).pair fp_step

 def preparedCode : BitEncoding MixedCode :=
  (BitEncoding.unaryNat.prod loopCode).retract
    (fun g=>(fuel g,(g,initial g))) (fun p=>p.2.1) (fun _=>rfl)

 theorem fp_prepare : FP MixedCode.encoding preparedCode id :=
  (fp_fuel.pair ((fp_id MixedCode.encoding).pair fp_initial)).transportOutput (fun _=>rfl)

/-- Total ordinary-input encoded DFS, not an assumed spanning forest oracle. -/
 theorem fp_run : FP MixedCode.encoding stateCode run := by
  obtain ⟨body⟩:=fp_loopStep
  let p : Polynomial ℕ:=C 2*X+statePolynomial+1
  have hb (g : MixedCode) (n : ℕ) (hn : n≤fuel g) :
      (loopCode.encode (loopStep^[n] (g,initial g))).length ≤ p.eval (preparedCode.encode g).length := by
    rw [loopStep_iterate]
    have hh:=iterate_state_word g n hn
    have hs : (loopCode.encode (g,(step g)^[n] (initial g))).length ≤ p.eval (inputLength g) := by
      simp only [loopCode,BitEncoding.prod_length,p,eval_add,eval_mul,eval_C,eval_X,eval_one]
      change 2*inputLength g+_+1 ≤ _
      omega
    exact hs.trans (natPolynomial_monotone p (by
      simp only [preparedCode,BitEncoding.retract,loopCode,BitEncoding.prod_length,inputLength]
      omega))
  have hlo : FP preparedCode loopCode (fun g=>loopStep^[fuel g] (g,initial g)) :=
    ⟨BoundedIterationMachine.computerOn preparedCode loopCode loopStep fuel
      (fun g=>(g,initial g)) (fun _=>rfl) body p hb⟩
  exact ((fp_prepare.comp hlo).comp (fp_snd MixedCode.encoding stateCode)).congr
    (fun g=>by simp only [Function.comp_apply,id_eq,loopStep_iterate,run])

 theorem fp_discoveryOrder : FP MixedCode.encoding BitEncoding.nat.list discoveryOrder :=
  (((fp_run.comp fp_discovered).comp (ListReverseMachines.fp_reverse discoveryCode)).comp
    (ListMapMachines.fp_map discoveryCode BitEncoding.nat Discovery.vertex fp_discoveredVertex))

 theorem fp_finishOrder : FP MixedCode.encoding BitEncoding.nat.list finishOrder :=
  (fp_run.comp fp_finished).comp (ListReverseMachines.fp_reverse BitEncoding.nat)

 theorem fp_headWithDefault {A : Type} (ea : BitEncoding A) (fixed : A) :
    FP (ea.list.prod ea) ea (fun p=>p.1.headD p.2) := by
  classical
  have hx:=fp_fst ea.list ea
  have hd:=fp_snd ea.list ea
  have hh:=hx.comp (ListDecompositionMachines.fp_headD ea fixed)
  have hz:=(hx.comp (ListCodecMachines.fp_length ea)).comp RationalCircuits.fp_nat_isZero
  have hz' : FP (ea.list.prod ea) BitEncoding.bool (fun p=>decide (p.1=[])):=hz.congr (fun _=>by simp)
  exact (hz'.ite hd hh).congr (fun p=>by cases h : p.1 <;> simp [h])

 theorem fp_discoveryAt : FP (MixedCode.encoding.prod BitEncoding.nat) discoveryCode
    (fun p=>discoveryAt p.1 p.2) := by
  let ei:=MixedCode.encoding.prod BitEncoding.nat
  have hg:=fp_fst MixedCode.encoding BitEncoding.nat
  have hv:=fp_snd MixedCode.encoding BitEncoding.nat
  have hr:=(hg.comp fp_run).comp fp_discovered
  have hm:=(hg.comp MixedCode.fp_edges).comp (ListCodecMachines.fp_length edgeCode)
  have hdefault:=fp_mkDiscovery ei _ _ _ hv hm (fp_const ei BitEncoding.nat.list [])
  have hk:=fp_fst BitEncoding.nat discoveryCode
  have hd:=(fp_snd BitEncoding.nat discoveryCode).comp fp_discoveredVertex
  have heq:=(hd.pair hk).comp PfaffianList.fp_nat_eq
  have hpred : FP (BitEncoding.nat.prod discoveryCode) BitEncoding.bool
      (fun p=>p.2.vertex==p.1):=heq.congr (fun _=>by simp [Bool.beq_eq_decide_eq])
  have hf:=(hv.pair hr).comp
    (ListContextFilterMachines.fp_filterWithContext BitEncoding.nat discoveryCode _ hpred)
  exact ((hf.pair hdefault).comp (fp_headWithDefault discoveryCode ⟨0,0,[]⟩)).congr (fun p=>by
    simp only [Function.comp_apply,List.headD_eq_head?_getD,discoveryAt]
    rw [MultiGraph.Kasteleyn.head_filter_eq_find])

 theorem fp_ancestorList : FP (MixedCode.encoding.prod BitEncoding.nat) BitEncoding.nat.list
    (fun p=>ancestors p.1 p.2) := fp_discoveryAt.comp fp_ancestors

 theorem fp_parentEdge : FP (MixedCode.encoding.prod BitEncoding.nat) BitEncoding.nat
    (fun p=>parentEdge p.1 p.2) := fp_discoveryAt.comp fp_treeEdge

 theorem fp_height : FP (MixedCode.encoding.prod BitEncoding.nat) BitEncoding.nat
    (fun p=>height p.1 p.2) := fp_ancestorList.comp (ListCodecMachines.fp_length BitEncoding.nat)


 theorem fp_parentVertex : FP (MixedCode.encoding.prod BitEncoding.nat) BitEncoding.nat
    (fun p=>parentVertex p.1 p.2) := by
  have hg:=fp_fst MixedCode.encoding BitEncoding.nat
  have hn:=(hg.comp MixedCode.fp_vertices).comp UnaryNatConversionMachine.fp_conversion
  exact (fp_ancestorList.pair hn).comp (fp_headWithDefault BitEncoding.nat 0)

 theorem fp_isAncestor : FP (MixedCode.encoding.prod (BitEncoding.nat.prod BitEncoding.nat)) BitEncoding.bool
    (fun p=>decide (p.2.1∈ancestors p.1 p.2.2)) := by
  have hg:=fp_fst MixedCode.encoding (BitEncoding.nat.prod BitEncoding.nat)
  have ht:=fp_snd MixedCode.encoding (BitEncoding.nat.prod BitEncoding.nat)
  have hu:=ht.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hv:=ht.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hp:=(hg.pair hv).comp fp_ancestorList
  exact (hu.pair hp).comp GraphComponentMachines.fp_mem

end PlanarHom.PlanarityDepthFirstSearch
